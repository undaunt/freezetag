#!/usr/bin/env python3

import gc
import os
import platform
import sys
import time
from collections import OrderedDict
from errno import ENOENT
from pathlib import Path
from stat import S_IFDIR
from threading import Lock, Timer

from appdirs import user_cache_dir
from watchdog.events import FileSystemEventHandler
from watchdog.observers import Observer

from .base import FuseFile, MusicMetadata, ParsedFile
from .core import ChecksumDB, Freezetag

try:
    from fuse import FUSE, FuseOSError, Operations
except ImportError:
    fuse_urls = {
        'Darwin': 'Install it via Homebrew by running "brew install macfuse", or manually from https://osxfuse.github.io/',
        'Linux': 'Install FUSE from your package manager, or manually from https://github.com/libfuse/libfuse/releases/latest.',
        'Windows': 'Download and install it from https://github.com/billziss-gh/winfsp/releases/latest.',
    }
    print('Could not load FUSE.', file=sys.stderr)
    print(fuse_urls.get(platform.system(), 'Please install FUSE for your operating system.'), file=sys.stderr)
    sys.exit(1)

FREEZETAG_CACHE_LIMIT = 10
FREEZETAG_KEEPALIVE_TIME = 10
CACHE_DIR = Path(user_cache_dir('freezetag', 'x1ppy'))

ST_ITEMS = ['st_atime', 'st_ctime', 'st_gid', 'st_mode', 'st_mtime', 'st_nlink', 'st_size', 'st_uid']
if platform.system() == 'Darwin':
    ST_ITEMS.append('st_birthtime')


# An LRU cache with polite eviction
class PoliteLRUCache(OrderedDict):
    def __init__(self, getter, can_purge, maxsize=128, *args, **kwds):
        self.maxsize = maxsize
        self.getter = getter
        self.can_purge = can_purge
        super().__init__(*args, **kwds)

    def __getitem__(self, key):
        if key not in self:
            self.__setitem__(key, self.getter(key))
        value = super().__getitem__(key)
        self.move_to_end(key)
        return value

    def __setitem__(self, key, value):
        super().__setitem__(key, value)
        if len(self) > self.maxsize:
            for _ in range(len(self) - self.maxsize):
                oldest = next(iter(self))
                if self.can_purge(oldest):
                    del self[oldest]
                    break
                self.move_to_end(oldest)


class FrozenItemFreezetagEntry:
    def __init__(self, freezetag_path, path, metadata_len):
        self.freezetag_path = freezetag_path
        self.path = path
        self.metadata_len = metadata_len


class FrozenItemFileEntry:
    def __init__(self, path, metadata_info, metadata_len):
        self.path = path
        self.metadata_info = metadata_info
        self.metadata_len = metadata_len


class FrozenItem:
    def __init__(self, checksum):
        self.checksum = checksum
        self.freezetags = []
        self.files = []


class FreezeFS(Operations, FileSystemEventHandler):
    def __init__(self, verbose=False, db_path=None, uid=None, gid=None):
        self.uid = uid if uid is not None else os.getuid()
        self.gid = gid if gid is not None else os.getgid()

        self.path_map = {Path('/').root: {}}
        self.checksum_map = {}
        self.abs_path_map = {}
        self.freezetag_map = {}
        self.inactive_freezetags = []
        self.freezetag_ref_lock = Lock()
        self.fh_map = {}
        self.verbose = verbose

        # Determine the path for the database
        if db_path:
            db_path = Path(db_path)
            if db_path.is_dir():
                # If db_path is a directory, append the default database filename
                self.db_path = db_path / 'freezefs.db'
            else:
                # If db_path is a file, use it directly
                self.db_path = db_path
        else:
            # Use the default path if no db_path is provided
            self.db_path = CACHE_DIR / 'freezefs.db'

        # Ensure the directory for the database exists
        self.db_path.parent.mkdir(parents=True, exist_ok=True)
        self.checksum_db = ChecksumDB(self.db_path)

        # self.freezetag_ref_lock must be acquired before accessing.
        self.freezetag_cache = PoliteLRUCache(Freezetag.from_path, self._can_purge_ftag, FREEZETAG_CACHE_LIMIT)

        # self.freezetag_ref_lock must be acquired before accessing.
        self.freezetag_refs = {}

        now = time.time()

        dir_stat_items = {
            'st_atime': now,
            'st_ctime': now,
            'st_mtime': now,
            'st_mode': S_IFDIR | 0o755,
            'st_nlink': 2,
            'st_gid': self.gid,
            'st_uid': self.uid,
        }

        if platform.system() == 'Darwin':
            dir_stat_items['st_birthtime'] = now

        self.dir_stat = dir_stat_items

    def mount(self, directory, mount_point):
        observer = Observer()
        observer.schedule(self, directory, recursive=True)
        observer.start()

        print(f"Scanning {directory} for files and freezetags...")
        for path in walk_dir(directory):
            if path.suffix.lower() == '.ftag':
                self._add_ftag(path)
            else:
                self._add_file(path)
        self.checksum_db.flush()

        print(f'Mounting {mount_point}')

        fuse_args = {
            'nothreads': True,
            'foreground': True,
            'fsname': 'freezefs',
            'volname': Path(mount_point).name,
        }

        # Only macOS supports FUSE volume names; remove it for other OSes
        if platform.system() != 'Darwin':
            fuse_args.pop('volname', None)

        self._log_verbose(f'Mounting FUSE with these args: {fuse_args}')
        FUSE(self, mount_point, **fuse_args)

    # Helpers
    # =======

    def _log_verbose(self, msg):
        if self.verbose:
            print(msg)

    def _add_freezetag_entry(self, checksum, entry):
        if checksum not in self.checksum_map:
            item = FrozenItem(checksum)
            self.checksum_map[checksum] = item
        else:
            item = self.checksum_map[checksum]

        item.freezetags.append(entry)

        assert not self._get_item(entry.path)

        map = self.path_map
        parts = Path(entry.path).parts
        for part in parts[0:-1]:
            if part not in map:
                map[part] = {}
            map = map[part]
        map[parts[-1]] = item

    def _add_path_entry(self, checksum, entry):
        if checksum not in self.checksum_map:
            item = FrozenItem(checksum)
            self.checksum_map[checksum] = item
        else:
            item = self.checksum_map[checksum]

        item.files.append(entry)
        self.abs_path_map[entry.path] = item

    def _get_item(self, path):
        item = self.path_map
        for part in Path(path).parts:
            if part not in item:
                return None
            item = item[part]
        return item

    def _add_ftag(self, path):
        self.freezetag_ref_lock.acquire()
        try:
            freezetag = self.freezetag_cache[path]
            self._schedule_purge_ftag(path)
        except KeyboardInterrupt:
            raise
        except Exception as e:
            print(f'Cannot parse freezetag: {path}, error: {e}')
            return
        finally:
            self.freezetag_ref_lock.release()

        self._log_verbose(f'Adding freezetag: {path}')

        root = Path('/') / freezetag.data.frozen.root
        item = self._get_item(root)
        if item:
            print(f'Cannot mount {path} to {root}: path already mounted by another freezetag')
            self.inactive_freezetags.append([root, path])
            return

        self.freezetag_map[path] = freezetag_map = (root, [])

        for state in freezetag.data.frozen.files:
            fuse_path = Path('/') / freezetag.data.frozen.root / state.path
            metadata = MusicMetadata.from_state(state)
            metadata_len = sum(m[1] for m in metadata) if metadata else 0
            entry = FrozenItemFreezetagEntry(path, fuse_path, metadata_len)
            self._add_freezetag_entry(state.checksum, entry)
            freezetag_map[1].append(state.checksum)

    def _add_file(self, src):
        try:
            st = src.stat()
        except Exception as e:
            print(f'Cannot stat file: {src}, error: {e}')
            return

        cached = self.checksum_db.get(st.st_dev, st.st_ino, st.st_mtime)
        if cached:
            self._log_verbose(f'Adding cached file: {src}')
            checksum, metadata_info, metadata_len, mtime = cached
            entry = FrozenItemFileEntry(src, metadata_info, metadata_len)
            self._add_path_entry(checksum, entry)
            return

        file = ParsedFile.from_path(src)
        try:
            file.parse()
        except KeyboardInterrupt:
            raise
        except Exception as e:
            print(f'Cannot parse file: {src}, error: {e}')
            return

        self._log_verbose(f'Adding new file: {src}')

        try:
            metadata = file.strip()
        except Exception as e:
            print(f'Cannot strip metadata from file: {src}, error: {e}')
            metadata = None

        metadata_info = list(metadata) if metadata else []
        metadata_len = sum(m[1] for m in metadata_info) if metadata else 0
        checksum = file.checksum()
        entry = FrozenItemFileEntry(src, metadata_info, metadata_len)
        self.checksum_db.add(st.st_dev, st.st_ino, st.st_mtime, checksum, metadata_info, metadata_len)
        self._add_path_entry(checksum, entry)

    def _delete_if_dangling(self, item, fuse_path, file_path):
        if not len(item.freezetags) and not len(item.files):
            del self.checksum_map[item.checksum]

        if fuse_path and not any(entry.path == fuse_path for entry in item.freezetags):
            map = self.path_map
            parents = []
            for part in Path(fuse_path).parts:
                parents.append((part, map))
                map = map[part]
            while len(parents):
                part, parent = parents.pop()
                del parent[part]
                if len(parent):
                    break

        if file_path and not len(item.files):
            del self.abs_path_map[file_path]

    def _can_purge_ftag(self, path):
        assert self.freezetag_ref_lock.locked()

        if path not in self.freezetag_refs:
            return True
        return self.freezetag_refs[path][1] <= 0

    def _purge_ftag(self, path, force):
        self.freezetag_ref_lock.acquire()
        try:
            no_refs = path in self.freezetag_refs and self.freezetag_refs[path][1] <= 0
            if (force or no_refs) and path in self.freezetag_cache:
                del self.freezetag_cache[path]
                gc.collect()
            if no_refs and path in self.freezetag_refs:
                del self.freezetag_refs[path]
        finally:
            self.freezetag_ref_lock.release()

    def _schedule_purge_ftag(self, path):
        assert self.freezetag_ref_lock.locked()

        t = Timer(FREEZETAG_KEEPALIVE_TIME, lambda: self._purge_ftag(path, force=False))
        t.start()

        if path not in self.freezetag_refs:
            self.freezetag_refs[path] = [t, 0]
        else:
            timer = self.freezetag_refs[path][0]
            if timer:
                timer.cancel()
            self.freezetag_refs[path][0] = t

    # Filesystem methods
    # ==================

    def getattr(self, path, fh=None):
        path = Path(path)

        item = self._get_item(path)
        if item is None:
            raise FuseOSError(ENOENT)

        if isinstance(item, FrozenItem):
            if not len(item.freezetags) or not len(item.files):
                raise FuseOSError(ENOENT)

            file_entry = item.files[0]
            frozen_entry = None
            for entry in item.freezetags:
                if entry.path == path:
                    frozen_entry = entry
                    break

            if not frozen_entry:
                raise FuseOSError(ENOENT)

            st = file_entry.path.stat()
            d = {key: getattr(st, key) for key in ST_ITEMS if hasattr(st, key)}
            d['st_size'] += frozen_entry.metadata_len - file_entry.metadata_len
            d['st_uid'] = self.uid
            d['st_gid'] = self.gid
            return d

        # For directories
        d = self.dir_stat.copy()
        d['st_uid'] = self.uid
        d['st_gid'] = self.gid
        return d

    def readdir(self, path, fh):
        yield '.'
        yield '..'
        for name, item in self._get_item(path).items():
            if isinstance(item, FrozenItem) and (not len(item.freezetags) or not len(item.files)):
                continue
            yield name

    # File methods
    # ============

    def open(self, path, flags):
        path = Path(path)
        item = self._get_item(path)
        if not item:
            raise FuseOSError(ENOENT)

        # As long as the raw checksum matches, any file should work, so just use the first one we have.
        file_entry = item.files[0]

        frozen_entry = None
        for entry in item.freezetags:
            if entry.path == path:
                frozen_entry = entry
                break

        if not frozen_entry:
            raise FuseOSError(ENOENT)

        # This is the path, relative to the freezetag file's root, that we are trying to open.
        # Knowing this is essential to providing the correct metadata.
        #
        # TODO: validate that this is correct on all operating systems.
        target_path = "/".join(frozen_entry.path.parts[2:])

        freezetag_path = None
        metadata = None
        if frozen_entry.metadata_len:
            freezetag_path = frozen_entry.freezetag_path

            self.freezetag_ref_lock.acquire()
            try:
                if freezetag_path not in self.freezetag_refs:
                    self.freezetag_refs[freezetag_path] = [None, 0]
                self.freezetag_refs[freezetag_path][1] += 1
                freezetag = self.freezetag_cache[freezetag_path]
            finally:
                self.freezetag_ref_lock.release()

            for f in freezetag.data.frozen.files:
                if f.checksum == item.checksum:
                    if f.path == target_path:
                        self._log_verbose(f'opened {f.path} as {path} (target: {target_path})')
                        metadata = f.metadata
                        break
                    self._log_verbose(f'ignoring {f.path} despite matching checksum (target: {target_path})')

        file = FuseFile.from_info(
            file_entry.path,
            flags,
            metadata,
            file_entry.metadata_info,
            file_entry.metadata_len,
            frozen_entry.metadata_len,
        )
        self.fh_map[file.fh] = (file, freezetag_path)
        return file.fh

    def read(self, path, length, offset, fh):
        return self.fh_map[fh][0].read(length, offset)

    def release(self, path, fh):
        f, freezetag_path = self.fh_map[fh]

        if freezetag_path:
            self.freezetag_ref_lock.acquire()
            try:
                self.freezetag_refs[freezetag_path][1] -= 1
                self._schedule_purge_ftag(freezetag_path)
            finally:
                self.freezetag_ref_lock.release()

        del self.fh_map[fh]
        return f.close()

    # watchdog observers
    # ==================

    def on_moved(self, event):
        src = Path(event.src_path)
        dst = Path(event.dest_path)
        if dst.is_dir():
            return

        self._log_verbose(f'Moved: {src} to {dst}')

        if src.suffix.lower() == '.ftag':
            self._purge_ftag(src, force=True)

            freezetag_map = self.freezetag_map.get(src)
            if not freezetag_map:
                for tag in self.inactive_freezetags:
                    if tag[1] == src:
                        tag[1] = dst
                        break
                return

            del self.freezetag_map[src]
            self.freezetag_map[dst] = freezetag_map

            for checksum in freezetag_map[1]:
                item = self.checksum_map[checksum]
                for entry in item.freezetags:
                    if entry.freezetag_path == src:
                        entry.freezetag_path = dst
                        break
            return

        item = self.abs_path_map[src]
        del self.abs_path_map[src]
        self.abs_path_map[dst] = item

        for entry in item.files:
            if entry.path == src:
                entry.path = dst

    def on_created(self, event):
        path = Path(event.src_path)
        if path.is_dir():
            return

        if path.suffix.lower() == '.ftag':
            self._add_ftag(path)
            return

        self._add_file(path)

    def on_deleted(self, event):
        path = Path(event.src_path)

        if path.suffix.lower() != '.ftag':
            self._log_verbose(f'Deleting file {path}')

            item = self.abs_path_map.get(path)
            if not item:
                return

            for entry in item.files:
                if entry.path == path:
                    item.files.remove(entry)
                    self._delete_if_dangling(item, fuse_path=None, file_path=path)
                    break
            return

        self._log_verbose(f'Deleting freezetag {path}')

        self._purge_ftag(path, force=True)

        freezetag_map = self.freezetag_map.get(path)
        if not freezetag_map:
            for tag in self.inactive_freezetags:
                if tag[1] == path:
                    self.inactive_freezetags.remove(tag)
                    break
            return

        for checksum in freezetag_map[1]:
            item = self.checksum_map[checksum]
            for entry in item.freezetags:
                if entry.freezetag_path == path:
                    item.freezetags.remove(entry)
                    self._delete_if_dangling(item, fuse_path=entry.path, file_path=None)
                    break
        del self.freezetag_map[path]

        root = freezetag_map[0]
        for tag in self.inactive_freezetags:
            if tag[0] == root:
                self.inactive_freezetags.remove(tag)
                self._add_ftag(tag[1])
                break

    def on_modified(self, event):
        self.on_deleted(event)
        self.on_created(event)


def walk_dir(path):
    for dirpath, dirnames, filenames in os.walk(path):
        dirnames.sort()
        for filename in sorted(filenames):
            yield Path(dirpath) / filename
