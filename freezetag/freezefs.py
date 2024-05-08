#!/usr/bin/env python3

import gc
import os
import platform
import sys
import time
import errno
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
except:
    fuse_urls = {
        'Darwin': 'Install it via homebrew by running "brew cask install osxfuse", or manually from https://github.com/osxfuse/osxfuse/releases/latest.',
        'Linux': 'Install fuse2 from your package manager, or manually from https://github.com/libfuse/libfuse/releases/tag/fuse-2.9.9.',
        'Windows': 'Download and install it from https://github.com/billziss-gh/winfsp/releases/latest.',
    }
    print('Could not load FUSE.', file=sys.stderr)
    print(fuse_urls[platform.system()], file=sys.stderr)
    sys.exit(1)

FREEZETAG_CACHE_LIMIT = 10
FREEZETAG_KEEPALIVE_TIME = 10
CACHE_DIR = Path(user_cache_dir('freezetag', 'x1ppy'))

ST_ITEMS = ['st_atime', 'st_ctime', 'st_gid', 'st_mode', 'st_mtime', 'st_nlink', 'st_size', 'st_uid']
if platform.system() == 'Darwin':
    ST_ITEMS.append('st_birthtime')


# An LRU cache with mostly standard behavior besides one thing: it asks whether
# an item can be purged before doing so. This prevents the cache from purging
# freezetags that are still be in use by open files; that way, they won't be
# needlessly recreated in memory if another file with the same freezetag is
# opened. This also means the cache could technically expand past its maxsize
# if all items cannot be purged.
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
            for i in range(len(self) - 1):
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
    def __init__(self, verbose=False, db_path=None, transparent=False):
        self.path_map = {Path('/').root: {}}
        self.checksum_map = {}
        self.abs_path_map = {}
        self.freezetag_map = {}
        self.inactive_freezetags = []
        self.freezetag_ref_lock = Lock()
        self.fh_map = {}
        self.verbose = verbose
        self.directory = None
        self.transparent = transparent  # New attribute to handle transparent mode

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

        try:
            self.gid = os.getgid()
            self.uid = os.getuid()
        except:
            # Windows.
            self.gid = 0
            self.uid = 0

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

        print(f"Initial dir_stat: {self.dir_stat}")

    def mount(self, directory, mount_point):
        if not directory:
            raise ValueError("Directory path must be provided")
        self.directory = directory
        db_path = Path(self.db_path)  # Ensure db_path is a Path object
        db_dir = db_path.parent
        db_dir.mkdir(parents=True, exist_ok=True)  # Ensure the directory exists

        # Other initialization and setup...
        CACHE_DIR.mkdir(parents=True, exist_ok=True)
        observer = Observer()
        observer.schedule(self, directory, recursive=True)
        observer.start()

        print(f'scanning {directory} for files and freezetags...')
        for path in walk_dir(directory):
            if path.suffix.lower() == '.ftag':
                self._add_ftag(path)
            else:
                self._add_file(path)
        self.checksum_db.flush()

        print(f'mounting {mount_point}')

        fuse_args = {
            'nothreads': True,
            'foreground': True,
            'fsname': 'freezefs',
            'volname': Path(mount_point).name  # Keep this if on Darwin
        }

        # Add uid and gid to the fuse arguments
        fuse_args['uid'] = self.uid
        fuse_args['gid'] = self.gid

        # macOS specific option, remove 'volname' if not on Darwin
        if platform.system() != 'Darwin':
            del fuse_args['volname']
    
        self._log_verbose(f'mounting FUSE with these args: {fuse_args}')
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

        assert (not self._get_item(entry.path))

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
        except:
            print(f'cannot parse freezetag: {path}')
            return
        finally:
            self.freezetag_ref_lock.release()

        self._log_verbose(f'adding freezetag: {path}')

        root = Path('/') / freezetag.data.frozen.root
        item = self._get_item(root)
        if item:
            print(f'cannot mount {path} to {root}: path already mounted by another freezetag')
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
        if self.transparent:
            ftag_path = src.with_suffix('.ftag')
            if ftag_path.exists():
                # Handle as frozen file if .ftag exists
                self._handle_frozen_file(src, ftag_path)
                return

        # Existing code for handling regular files
        try:
            st = src.stat()
        except:
            print(f'cannot stat file: {src}')
            return

        cached = self.checksum_db.get(st.st_dev, st.st_ino, st.st_mtime)
        if cached:
            self._log_verbose(f'adding cached file: {src}')
            checksum, metadata_info, metadata_len, mtime = cached
            entry = FrozenItemFileEntry(src, metadata_info, metadata_len)
            self._add_path_entry(checksum, entry)
            return

        file = ParsedFile.from_path(src)
        try:
            file.parse()
        except KeyboardInterrupt:
            raise
        except:
            print(f'cannot parse file: {src}')
            return

        self._log_verbose(f'adding new file: {src}')

        metadata = file.strip()
        metadata_info = list(metadata) if metadata else []
        metadata_len = sum(m[1] for m in metadata_info) if metadata else 0
        checksum = file.checksum()
        entry = FrozenItemFileEntry(src, metadata_info, metadata_len)
        self.checksum_db.add(st.st_dev, st.st_ino, st.st_mtime, checksum, metadata_info, metadata_len)
        self._add_path_entry(checksum, entry)

    def _find_ftag(self, path):
        """
        Recursively search for an .ftag file starting from the given path and moving upwards.
        Returns the path to the .ftag file if found, otherwise None.
        """
        current_path = Path(path)
        while current_path != current_path.parent:  # Stop when reaching the root directory
            ftag_files = list(current_path.glob('*.ftag'))
            if ftag_files:
                return ftag_files[0]  # Return the first .ftag file found
            current_path = current_path.parent
        return None

    def _handle_frozen_file(self, src, ftag_path):
        print(f'Handling frozen file: {src} with .ftag: {ftag_path}')
        
        # Assuming parse_ftag is a function that parses the .ftag file and returns a dictionary of settings
        try:
            with open(ftag_path, 'r') as file:
                ftag_data = parse_ftag(file)
            
            # Example of using parsed data - adjust visibility or access based on .ftag settings
            if 'root' in ftag_data:
                # Implement logic based on the root or other settings
                print(f"Root directory specified in .ftag: {ftag_data['root']}")
                # Additional logic to handle files according to .ftag specifications
        except Exception as e:
            print(f"Failed to handle .ftag file {ftag_path}: {str(e)}")

    def _delete_if_dangling(self, item, fuse_path, file_path):
        if self.transparent and any(Path(fuse_path).with_suffix('.ftag').exists() for entry in item.freezetags if entry.path == fuse_path):
            return  # Skip deletion if any related .ftag files exist

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
        assert (self.freezetag_ref_lock.locked())

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
        assert (self.freezetag_ref_lock.locked())

        t = Timer(FREEZETAG_KEEPALIVE_TIME, lambda: self._purge_ftag(path, force=False))
        t.start()

        if not path in self.freezetag_refs:
            self.freezetag_refs[path] = [t, 0]
        else:
            timer = self.freezetag_refs[path][0]
            timer and timer.cancel()
            self.freezetag_refs[path][0] = t

    # Filesystem methods
    # ==================

    def create(self, path, mode, fi=None):
        if not self.transparent:
            raise FuseOSError(errno.EROFS)  # Read-only file system error

        actual_path = os.path.join(self.directory, path.lstrip('/'))
        fh = os.open(actual_path, os.O_CREAT | os.O_WRONLY, mode)
        
        # Convert the file descriptor to a file object for further operations
        file_obj = os.fdopen(fh, 'w+')  # 'w+' mode opens the file for both reading and writing
        self.fh_map[fh] = (file_obj, None)  # Store the file object and path in fh_map
        return fh

    def write(self, path, data, offset, fh):
        if not self.transparent:
            raise FuseOSError(errno.EROFS)  # Read-only file system error

        file_obj, _ = self.fh_map.get(fh, (None, None))
        if file_obj is None:
            actual_path = os.path.join(self.directory, path.lstrip('/'))
            try:
                file_obj = open(actual_path, 'r+b')
                self.fh_map[fh] = (file_obj, None)
            except IOError:
                raise FuseOSError(errno.EBADF)  # Handle file open errors

            # Update the modification time
            self.dir_stat['st_mtime'] = time.time()
            return bytes_written

    def rename(self, old, new):
        if not self.transparent:
            raise FuseOSError(errno.EROFS)

        old_path = os.path.join(self.directory, old.lstrip('/'))
        new_path = os.path.join(self.directory, new.lstrip('/'))

        # Check if the old file is frozen by looking for a corresponding .ftag file
        ftag_path = Path(old_path + '.ftag')
        if ftag_path.exists():
            raise FuseOSError(errno.EACCES)  # Access denied error for trying to rename a frozen file

        os.rename(old_path, new_path)

    def unlink(self, path):
        if not self.transparent:
            self._log_verbose(f"Attempt to delete file {path} blocked in non-transparent mode")
            raise FuseOSError(errno.EROFS)  # Prevent deletion in non-transparent mode

        actual_path = os.path.join(self.directory, path.lstrip('/'))
        os.unlink(actual_path)
        self._log_verbose(f"File {path} deleted")

    def getattr(self, path, fh=None):
        self._log_verbose(f"Getting attributes for: {path}")

        # Handle the root path separately
        if path == Path('/'):
            attrs = {
                'st_mode': (S_IFDIR | 0o755),
                'st_ctime': time.time(),
                'st_mtime': time.time(),
                'st_atime': time.time(),
                'st_nlink': 2
            }
            return attrs

        # Attempt to find and handle .ftag file
        ftag_path = self._find_ftag(path)
        if ftag_path:
            self._log_verbose(f"Found .ftag for {path}, handling as frozen file")
            try:
                # Simulate adding .ftag to leverage its parsing and handling logic
                self._add_ftag(ftag_path)
                # Fetch the item after it has been processed
                item = self._get_item(path)
                if item:
                    return {
                        'st_mode': item.mode,
                        'st_ctime': item.ctime,
                        'st_mtime': item.mtime,
                        'st_atime': item.atime,
                        'st_nlink': item.nlink,
                        'st_uid': item.uid,
                        'st_gid': item.gid,
                        'st_size': item.size,
                    }
            except Exception as e:
                self._log_verbose(f"Failed to handle .ftag file {ftag_path}: {str(e)}")
                raise FuseOSError(ENOENT)  # No entry error if handling fails

        # Handle as regular file if no .ftag file is associated or not in transparent mode
        try:
            attrs = os.lstat(os.path.join(self.directory, str(path).lstrip('/')))
            return {
                'st_mode': attrs.st_mode,
                'st_ctime': attrs.st_ctime,
                'st_mtime': attrs.st_mtime,
                'st_atime': attrs.st_atime,
                'st_nlink': attrs.st_nlink,
                'st_size': attrs.st_size,
                'st_uid': attrs.st_uid,
                'st_gid': attrs.st_gid
            }
        except FileNotFoundError:
            self._log_verbose(f"No file found for path: {path}")
            raise FuseOSError(ENOENT)

    def readdir(self, path, fh):
        path = Path(path)
        self._log_verbose(f"Listing directory: {path}")
        yield '.'
        yield '..'

        if self.transparent:
            # In transparent mode, list both regular and frozen files
            try:
                # List all files in the directory
                all_files = os.listdir(os.path.join(self.directory, str(path).lstrip('/')))
                # Filter out files that have a corresponding .ftag file
                frozen_files = {f[:-5] for f in all_files if f.endswith('.ftag')}
                regular_files = {f for f in all_files if not f.endswith('.ftag')}

                # Yield all regular files and files with .ftag as frozen versions
                for file in regular_files.union(frozen_files):
                    self._log_verbose(f"Yielding file: {file}")
                    yield file
            except FileNotFoundError:
                self._log_verbose(f"Directory not found: {path}")
                raise FuseOSError(ENOENT)
        else:
            # Non-transparent mode: use existing logic
            item = self._get_item(path)
            if item is None:
                self._log_verbose(f"No item found for path: {path}")
                raise FuseOSError(ENOENT)
            for name, sub_item in item.items():
                if isinstance(sub_item, FrozenItem) and (not len(sub_item.freezetags) or not len(sub_item.files)):
                    continue
                self._log_verbose(f"Yielding sub-item: {name}")
                yield name

    # File methods
    # ============

    def open(self, path, flags):
        path = Path(path)

        if self.transparent:
            ftag_path = path.with_suffix('.ftag')
            if ftag_path.exists():
                # Handle as frozen file if .ftag exists
                return self._open_frozen_file(path, flags, ftag_path)
            else:
                # Handle as regular file if no .ftag file is associated
                return self._open_regular_file(path, flags)

        item = self._get_item(path)
        if not item:
            raise FuseOSError(ENOENT)

        file_entry = item.files[0]

        frozen_entry = None
        for entry in item.freezetags:
            if entry.path == path:
                frozen_entry = entry
                break

        if not frozen_entry:
            raise FuseOSError(ENOENT)

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
                    metadata = f.metadata
                    break

        # Determine the mode based on flags
        mode = 'rb'  # Default to binary read mode
        if flags & os.O_WRONLY:
            mode = 'wb'  # Binary write mode
        elif flags & os.O_RDWR:
            mode = 'r+b'  # Binary read/write mode

        # Open the file and get a file descriptor
        os_fh = os.open(file_entry.path, flags)
        # Convert file descriptor to a file object
        file_obj = os.fdopen(os_fh, mode)
        self.fh_map[os_fh] = (file_obj, freezetag_path)
        return os_fh

    def _open_frozen_file(self, path, flags, ftag_path):
        # Logic to open a frozen file based on .ftag
        print(f'Opening frozen file: {path} with .ftag: {ftag_path}')
        # Implement the logic to open and handle frozen files
        # Placeholder: Implement this method based on your handling of frozen files

    def _open_regular_file(self, path, flags):
        # Logic to open a regular file
        os_fh = os.open(os.path.join(self.directory, path.lstrip('/')), flags)
        mode = 'rb' if flags & os.O_RDONLY else 'wb' if flags & os.O_WRONLY else 'r+b'
        file_obj = os.fdopen(os_fh, mode)
        self.fh_map[os_fh] = (file_obj, None)
        return os_fh

    def read(self, path, length, offset, fh):
        file_obj = self.fh_map[fh][0]
        file_obj.seek(offset)  # Move to the correct offset
        return file_obj.read(length)  # Read the specified number of bytes

    def release(self, path, fh):
        try:
            if fh not in self.fh_map:
                self._log_verbose(f"File handle {fh} not found for release")
                raise FuseOSError(errno.EINVAL)  # Handle not found

            file_obj, freezetag_path = self.fh_map.pop(fh, (None, None))
            if file_obj is None:
                self._log_verbose(f"No file object found for file handle {fh}")
                raise FuseOSError(errno.EINVAL)  # Handle not found

            # Close the file object if it's valid
            if hasattr(file_obj, 'close'):
                file_obj.close()
            else:
                self._log_verbose(f"Object associated with file handle {fh} is not closable. Type: {type(file_obj)}")

            # Handle freezetag path reference counting
            if freezetag_path:
                self.freezetag_ref_lock.acquire()
                try:
                    if freezetag_path in self.freezetag_refs:
                        self.freezetag_refs[freezetag_path][1] -= 1
                        if self.freezetag_refs[freezetag_path][1] <= 0:
                            self._schedule_purge_ftag(freezetag_path)
                finally:
                    self.freezetag_ref_lock.release()

        except Exception as e:
            self._log_verbose(f"Error releasing file handle {fh}: {str(e)}")
            raise FuseOSError(errno.EIO)  # General I/O error for any exceptions


    # watchdog observers
    # ==================

    def on_moved(self, event):
        src = Path(event.src_path)
        dst = Path(event.dest_path)
        if dst.is_dir():
            return

        self._log_verbose(f'moved: {src} to {dst}')

        if self.transparent:
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

        if self.transparent:
            if path.suffix.lower() == '.ftag':
                self._add_ftag(path)
                return

        self._add_file(path)

    def on_deleted(self, event):
        path = Path(event.src_path)

        if self.transparent:
            if path.suffix.lower() == '.ftag':
                self._log_verbose(f'Deleting freezetag {path}')
                self._purge_ftag(path, force=True)

                freezetag_map = self.freezetag_map.get(path)
                if freezetag_map:
                    # Remove the freezetag from the map and update the checksum map
                    for checksum in freezetag_map[1]:
                        item = self.checksum_map[checksum]
                        for entry in item.freezetags:
                            if entry.freezetag_path == path:
                                item.freezetags.remove(entry)
                                self._delete_if_dangling(item, fuse_path=entry.path, file_path=None)
                                break
                    del self.freezetag_map[path]
                else:
                    # Handle cases where the freezetag map does not exist
                    for tag in self.inactive_freezetags:
                        if tag[1] == path:
                            self.inactive_freezetags.remove(tag)
                            break
                return

            # Check if the path is a frozen file
            if any(ftag.path == path for ftag in self.freezetag_map.values()):
                self._log_verbose(f'Attempt to delete frozen file {path} blocked')
                return  # Block deletion of frozen files

        if path.suffix.lower() != '.ftag':
            self._log_verbose(f'deleting file {path}')

            item = self.abs_path_map.get(path)
            if not item:
                return

            for entry in item.files:
                if entry.path == path:
                    item.files.remove(entry)
                    self._delete_if_dangling(item, fuse_path=None, file_path=path)
                    break

def on_modified(self, event):
    src = Path(event.src_path)

    # Check if the file has a corresponding .ftag file
    ftag_path = src.with_suffix('.ftag')
    has_ftag = ftag_path.exists()

    # Handle based on the mode
    if self.transparent:
        if has_ftag:
            # In transparent mode, frozen files should not be modified
            self._log_verbose(f'Attempt to modify frozen file {src} blocked in transparent mode')
        else:
            # Apply changes to non-frozen files
            self.on_deleted(event)
            self.on_created(event)
    else:
        # In original freezetag mode, modifications to frozen files are not allowed
        if has_ftag:
            self._log_verbose(f'Attempt to modify frozen file {src} blocked in original freezetag mode')
        else:
            # Non-frozen files are not typically handled in original mode, but let's log if this happens
            self._log_verbose(f'Non-frozen file {src} modified in original freezetag mode')


def walk_dir(path):
    for dirpath, dirnames, filenames in os.walk(path):
        dirnames.sort()
        for filename in sorted(filenames):
            yield Path(dirpath) / filename

