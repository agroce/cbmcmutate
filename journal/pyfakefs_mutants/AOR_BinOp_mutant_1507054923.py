# line: 91
'A fake filesystem implementation for unit testing.\n\n:Includes:\n  * FakeFile:  Provides the appearance of a real file.\n  * FakeDirectory: Provides the appearance of a real directory.\n  * FakeFilesystem:  Provides the appearance of a real directory hierarchy.\n  * FakeOsModule:  Uses FakeFilesystem to provide a fake os module replacement.\n  * FakePathModule:  Faked os.path module replacement.\n  * FakeFileOpen:  Faked file() and open() function replacements.\n\n:Usage:\n\n>>> from pyfakefs import fake_filesystem\n>>> filesystem = fake_filesystem.FakeFilesystem()\n>>> os_module = fake_filesystem.FakeOsModule(filesystem)\n>>> pathname = \'/a/new/dir/new-file\'\n\nCreate a new file object, creating parent directory objects as needed:\n\n>>> os_module.path.exists(pathname)\nFalse\n>>> new_file = filesystem.CreateFile(pathname)\n\nFile objects can\'t be overwritten:\n\n>>> os_module.path.exists(pathname)\nTrue\n>>> try:\n...   filesystem.CreateFile(pathname)\n... except IOError as e:\n...   assert e.errno == errno.EEXIST, \'unexpected errno: %d\' % e.errno\n...   assert e.strerror == \'File already exists in fake filesystem\'\n\nRemove a file object:\n\n>>> filesystem.RemoveObject(pathname)\n>>> os_module.path.exists(pathname)\nFalse\n\nCreate a new file object at the previous path:\n\n>>> beatles_file = filesystem.CreateFile(pathname,\n...     contents=\'Dear Prudence\\nWon\\\'t you come out to play?\\n\')\n>>> os_module.path.exists(pathname)\nTrue\n\nUse the FakeFileOpen class to read fake file objects:\n\n>>> file_module = fake_filesystem.FakeFileOpen(filesystem)\n>>> for line in file_module(pathname):\n...     print(line.rstrip())\n...\nDear Prudence\nWon\'t you come out to play?\n\nFile objects cannot be treated like directory objects:\n\n>>> os_module.listdir(pathname)  #doctest: +NORMALIZE_WHITESPACE\nTraceback (most recent call last):\n  File "fake_filesystem.py", line 291, in listdir\n    raise OSError(errno.ENOTDIR,\nOSError: [Errno 20] Fake os module: not a directory: \'/a/new/dir/new-file\'\n\nThe FakeOsModule can list fake directory objects:\n\n>>> os_module.listdir(os_module.path.dirname(pathname))\n[\'new-file\']\n\nThe FakeOsModule also supports stat operations:\n\n>>> import stat\n>>> stat.S_ISREG(os_module.stat(pathname).st_mode)\nTrue\n>>> stat.S_ISDIR(os_module.stat(os_module.path.dirname(pathname)).st_mode)\nTrue\n'
# line: 92
import codecs
# line: 93
import errno
# line: 94
import heapq
# line: 95
import io
# line: 96
import locale
# line: 97
import platform
# line: 98
import os
# line: 99
import sys
# line: 100
import time
# line: 101
import warnings
# line: 103
from collections import namedtuple
# line: 105
import stat
# line: 106
from copy import copy
# line: 108
__pychecker__ = 'no-reimportself'
# line: 110
__version__ = '3.3'
# line: 112
PERM_READ = 256
# line: 113
PERM_WRITE = 128
# line: 114
PERM_EXE = 64
# line: 115
PERM_DEF = 511
# line: 116
PERM_DEF_FILE = 438
# line: 117
PERM_ALL = 4095
# line: 119
_OpenModes = namedtuple('open_modes', 'must_exist can_read can_write truncate append must_not_exist')
# line: 125
_OPEN_MODE_MAP = {'r': (True, True, False, False, False, False), 'w': (False, False, True, True, False, False), 'a': (False, False, True, False, True, False), 'r+': (True, True, True, False, False, False), 'w+': (False, True, True, True, False, False), 'a+': (False, True, True, False, True, False), }
# line: 136
if ((sys.version_info[0] < 3) and (sys.platform != 'win32')):
    # line: 137
    _OPEN_MODE_MAP['rw'] = (True, True, True, False, False, False)
# line: 139
if (sys.version_info >= (3, 3)):
    # line: 140
    _OPEN_MODE_MAP['x'] = (False, False, True, False, False, True)
    # line: 141
    _OPEN_MODE_MAP['x+'] = (False, True, True, False, False, True)
# line: 143
if sys.platform.startswith('linux'):
    # line: 146
    _MAX_LINK_DEPTH = 40
else:
    # line: 149
    _MAX_LINK_DEPTH = 32
# line: 151
FAKE_PATH_MODULE_DEPRECATION = 'Do not instantiate a FakePathModule directly; let FakeOsModule instantiate it.  See the FakeOsModule docstring for details.'
# line: 155
if (sys.platform == 'win32'):
    # line: 157
    OSError = WindowsError


# line: 160
class FakeLargeFileIoException(Exception):
    # line: 163
    'Exception thrown on unsupported operations for fake large files.\n    Fake large files have a size with no real content.\n    '

    # line: 165
    def __init__(self, file_path):
        # line: 166
        super(FakeLargeFileIoException, self).__init__(('Read and write operations not supported for fake large file: %s' % file_path))

# line: 171
def CopyModule(old):
    # line: 172
    'Recompiles and creates new module object.'
    # line: 173
    saved = sys.modules.pop(old.__name__, None)
    # line: 174
    new = __import__(old.__name__)
    # line: 175
    sys.modules[old.__name__] = saved
    # line: 176
    return new


# line: 179
class _FakeStatResult(object):
    # line: 183
    'Mimics os.stat_result for use as return type of `stat()` and similar.\n    This is needed as `os.stat_result` has no possibility to set\n    nanosecond times directly.\n    '
    # line: 184
    long_type = (long if (sys.version_info < (3,)) else int)

    # line: 186
    def __init__(self, initial_time=None):
        # line: 187
        self.use_float = FakeOsModule.stat_float_times
        # line: 188
        self.st_mode = None
        # line: 189
        self.st_ino = None
        # line: 190
        self.st_dev = None
        # line: 191
        self.st_nlink = 0
        # line: 192
        self.st_uid = None
        # line: 193
        self.st_gid = None
        # line: 194
        self.st_size = None
        # line: 195
        if (initial_time is not None):
            # line: 196
            self._st_atime_ns = self.long_type((initial_time * 1000000000.0))
        else:
            # line: 198
            self._st_atime_ns = None
        # line: 199
        self._st_mtime_ns = self._st_atime_ns
        # line: 200
        self._st_ctime_ns = self._st_atime_ns

    # line: 202
    def __eq__(self, other):
        # line: 203
        return (isinstance(other, _FakeStatResult) and (self._st_atime_ns == other._st_atime_ns) and (self._st_ctime_ns == other._st_ctime_ns) and (self._st_mtime_ns == other._st_mtime_ns) and (self.st_size == other.st_size) and (self.st_gid == other.st_gid) and (self.st_uid == other.st_uid) and (self.st_nlink == other.st_nlink) and (self.st_dev == other.st_dev) and (self.st_ino == other.st_ino) and (self.st_mode == other.st_mode))

    # line: 217
    def __ne__(self, other):
        # line: 218
        return (not (self == other))

    # line: 220
    def copy(self):
        # line: 223
        'Return a copy where the float usage is hard-coded to mimic the behavior\n        of the real os.stat_result.\n        '
        # line: 224
        use_float = self.use_float()
        # line: 225
        stat_result = copy(self)
        # line: 226
        stat_result.use_float = (lambda : use_float)
        # line: 227
        return stat_result

    # line: 229
    def set_from_stat_result(self, stat_result):
        # line: 233
        'Set values from a real os.stat_result.\n        Note: values that are controlled by the fake filesystem are not set.\n        This includes st_ino, st_dev and st_nlink.\n        '
        # line: 234
        self.st_mode = stat_result.st_mode
        # line: 235
        self.st_uid = stat_result.st_uid
        # line: 236
        self.st_gid = stat_result.st_gid
        # line: 237
        self.st_size = stat_result.st_size
        # line: 238
        if (sys.version_info < (3, 3)):
            # line: 239
            self._st_atime_ns = self.long_type((stat_result.st_atime * 1000000000.0))
            # line: 240
            self._st_mtime_ns = self.long_type((stat_result.st_mtime * 1000000000.0))
            # line: 241
            self._st_ctime_ns = self.long_type((stat_result.st_ctime * 1000000000.0))
        else:
            # line: 243
            self._st_atime_ns = stat_result.st_atime_ns
            # line: 244
            self._st_mtime_ns = stat_result.st_mtime_ns
            # line: 245
            self._st_ctime_ns = stat_result.st_ctime_ns

    # line: 247
    @property
    # line: 247
    def st_ctime(self):
        # line: 249
        'Return the creation time in seconds.'
        # line: 250
        ctime = (self._st_ctime_ns / 1000000000.0)
        # line: 251
        return (ctime if self.use_float() else int(ctime))

    # line: 253
    @property
    # line: 253
    def st_atime(self):
        # line: 255
        'Return the access time in seconds.'
        # line: 256
        atime = (self._st_atime_ns / 1000000000.0)
        # line: 257
        return (atime if self.use_float() else int(atime))

    # line: 259
    @property
    # line: 259
    def st_mtime(self):
        # line: 261
        'Return the modification time in seconds.'
        # line: 262
        mtime = (self._st_mtime_ns / 1000000000.0)
        # line: 263
        return (mtime if self.use_float() else int(mtime))

    # line: 265
    @st_ctime.setter
    # line: 265
    def st_ctime(self, val):
        # line: 267
        'Set the creation time in seconds.'
        # line: 268
        self._st_ctime_ns = self.long_type((val * 1000000000.0))

    # line: 270
    @st_atime.setter
    # line: 270
    def st_atime(self, val):
        # line: 272
        'Set the access time in seconds.'
        # line: 273
        self._st_atime_ns = self.long_type((val * 1000000000.0))

    # line: 275
    @st_mtime.setter
    # line: 275
    def st_mtime(self, val):
        # line: 277
        'Set the modification time in seconds.'
        # line: 278
        self._st_mtime_ns = self.long_type((val * 1000000000.0))

    # line: 280
    def __getitem__(self, item):
        # line: 281
        'Implement item access to mimic `os.stat_result` behavior.'
        # line: 282
        if (item == stat.ST_MODE):
            # line: 283
            return self.st_mode
        # line: 284
        if (item == stat.ST_INO):
            # line: 285
            return self.st_ino
        # line: 286
        if (item == stat.ST_DEV):
            # line: 287
            return self.st_dev
        # line: 288
        if (item == stat.ST_NLINK):
            # line: 289
            return self.st_nlink
        # line: 290
        if (item == stat.ST_UID):
            # line: 291
            return self.st_uid
        # line: 292
        if (item == stat.ST_GID):
            # line: 293
            return self.st_gid
        # line: 294
        if (item == stat.ST_SIZE):
            # line: 295
            return self.st_size
        # line: 296
        if (item == stat.ST_ATIME):
            # line: 298
            return int(self.st_atime)
        # line: 299
        if (item == stat.ST_MTIME):
            # line: 300
            return int(self.st_mtime)
        # line: 301
        if (item == stat.ST_CTIME):
            # line: 302
            return int(self.st_ctime)
    # line: 304
    if (sys.version_info >= (3, 3)):

        # line: 306
        @property
        # line: 306
        def st_atime_ns(self):
            # line: 308
            'Return the access time in nanoseconds.'
            # line: 309
            return self._st_atime_ns

        # line: 311
        @property
        # line: 311
        def st_mtime_ns(self):
            # line: 313
            'Return the modification time in nanoseconds.'
            # line: 314
            return self._st_mtime_ns

        # line: 316
        @property
        # line: 316
        def st_ctime_ns(self):
            # line: 318
            'Return the creation time in nanoseconds.'
            # line: 319
            return self._st_ctime_ns

        # line: 321
        @st_atime_ns.setter
        # line: 321
        def st_atime_ns(self, val):
            # line: 323
            'Set the access time in nanoseconds.'
            # line: 324
            self._st_atime_ns = val

        # line: 326
        @st_mtime_ns.setter
        # line: 326
        def st_mtime_ns(self, val):
            # line: 328
            'Set the modification time of the fake file in nanoseconds.'
            # line: 329
            self._st_mtime_ns = val

        # line: 331
        @st_ctime_ns.setter
        # line: 331
        def st_ctime_ns(self, val):
            # line: 333
            'Set the creation time of the fake file in nanoseconds.'
            # line: 334
            self._st_ctime_ns = val


# line: 337
class FakeFile(object):
    # line: 353
    "Provides the appearance of a real file.\n\n    Attributes currently faked out:\n        st_mode: user-specified, otherwise S_IFREG\n        st_ctime: the time.time() timestamp of the file change time (updated\n        each time a file's attributes is modified).\n        st_atime: the time.time() timestamp when the file was last accessed.\n        st_mtime: the time.time() timestamp when the file was last modified.\n        st_size: the size of the file\n        st_nlink: the number of hard links to the file\n        st_ino: the inode number - a unique number identifying the file\n        st_dev: a unique number identifying the (fake) file system device the file belongs to\n\n    Other attributes needed by os.stat are assigned default value of None\n    these include: st_uid, st_gid\n    "

    # line: 355
    def __init__(self, name, st_mode=(stat.S_IFREG | PERM_DEF_FILE), contents=None, filesystem=None, encoding=None, errors=None):
        # line: 371
        'init.\n\n        Args:\n          name:  name of the file/directory, without parent path information\n          st_mode:  the stat.S_IF* constant representing the file type (i.e.\n            stat.S_IFREG, stat.S_IFDIR)\n          contents:  the contents of the filesystem object; should be a string or byte object for\n            regular files, and a list of other FakeFile or FakeDirectory objects\n            for FakeDirectory objects\n          filesystem: the fake filesystem where the file is created.\n            New in pyfakefs 2.9.\n          encoding: if contents is a unicode string, the encoding used for serialization\n          errors: the error mode used for encoding/decoding errors\n            New in pyfakefs 3.2.\n        '
        # line: 372
        self.name = name
        # line: 373
        self.stat_result = _FakeStatResult(time.time())
        # line: 374
        self.stat_result.st_mode = st_mode
        # line: 375
        self.encoding = encoding
        # line: 376
        self.errors = (errors or 'strict')
        # line: 377
        self._byte_contents = self._encode_contents(contents)
        # line: 378
        self.stat_result.st_size = (len(self._byte_contents) if (self._byte_contents is not None) else 0)
        # line: 381
        if (filesystem is None):
            # line: 382
            raise ValueError('filesystem shall not be None')
        # line: 383
        self.filesystem = filesystem
        # line: 384
        self.epoch = 0
        # line: 385
        self.parent_dir = None

    # line: 387
    @property
    # line: 387
    def byte_contents(self):
        # line: 389
        return self._byte_contents

    # line: 391
    @property
    # line: 391
    def contents(self):
        # line: 393
        'Return the contents as string with the original encoding.'
        # line: 394
        if ((sys.version_info >= (3, 0)) and isinstance(self.byte_contents, bytes)):
            # line: 395
            return self.byte_contents.decode((self.encoding or locale.getpreferredencoding(False)), errors=self.errors)
        # line: 398
        return self.byte_contents

    # line: 400
    def SetLargeFileSize(self, st_size):
        # line: 413
        "Sets the self.st_size attribute and replaces self.content with None.\n\n        Provided specifically to simulate very large files without regards\n        to their content (which wouldn't fit in memory).\n        Note that read/write operations with such a file raise FakeLargeFileIoException.\n\n        Args:\n          st_size: (int) The desired file size\n\n        Raises:\n          IOError: if the st_size is not a non-negative integer,\n                   or if st_size exceeds the available file system space\n        "
        # line: 414
        self._check_positive_int(st_size)
        # line: 415
        if self.st_size:
            # line: 416
            self.SetSize(0)
        # line: 417
        self.filesystem.ChangeDiskUsage(st_size, self.name, self.st_dev)
        # line: 418
        self.st_size = st_size
        # line: 419
        self._byte_contents = None

    # line: 421
    def _check_positive_int(self, size):
        # line: 423
        int_types = ((int, long) if (sys.version_info < (3, 0)) else int)
        # line: 424
        if ((not isinstance(size, int_types)) or (size < 0)):
            # line: 425
            raise IOError(errno.ENOSPC, ('Fake file object: size must be a non-negative integer, but is %s' % size), self.name)

    # line: 429
    def IsLargeFile(self):
        # line: 430
        'Return True if this file was initialized with size but no contents.'
        # line: 431
        return (self._byte_contents is None)

    # line: 433
    def _encode_contents(self, contents):
        # line: 435
        if ((sys.version_info >= (3, 0)) and isinstance(contents, str)):
            # line: 436
            contents = bytes(contents, (self.encoding or locale.getpreferredencoding(False)), self.errors)
        elif ((sys.version_info < (3, 0)) and isinstance(contents, unicode)):
            # line: 438
            contents = contents.encode((self.encoding or locale.getpreferredencoding(False)), self.errors)
        # line: 439
        return contents

    # line: 441
    def _set_initial_contents(self, contents):
        # line: 450
        'Sets the file contents and size.\n           Called internally after initial file creation.\n\n        Args:\n          contents: string, new content of file.\n        Raises:\n          IOError: if the st_size is not a non-negative integer,\n                   or if st_size exceeds the available file system space\n        '
        # line: 451
        contents = self._encode_contents(contents)
        # line: 452
        st_size = len(contents)
        # line: 454
        if self._byte_contents:
            # line: 455
            self.SetSize(0)
        # line: 456
        current_size = (self.st_size or 0)
        # line: 457
        self.filesystem.ChangeDiskUsage((st_size - current_size), self.name, self.st_dev)
        # line: 458
        self._byte_contents = contents
        # line: 459
        self.st_size = st_size
        # line: 460
        self.epoch += 1

    # line: 462
    def SetContents(self, contents, encoding=None):
        # line: 475
        'Sets the file contents and size and increases the modification time.\n\n        Args:\n          contents: (str, bytes, unicode) new content of file.\n          encoding: (str) the encoding to be used for writing the contents\n                    if they are a unicode string.\n                    If not given, the locale preferred encoding is used.\n                    New in pyfakefs 2.9.\n\n        Raises:\n          IOError: if the st_size is not a non-negative integer,\n                   or if st_size exceeds the available file system space.\n        '
        # line: 476
        self.encoding = encoding
        # line: 477
        self._set_initial_contents(contents)
        # line: 478
        current_time = time.time()
        # line: 479
        self.st_ctime = current_time
        # line: 480
        self.st_mtime = current_time

    # line: 482
    def GetSize(self):
        # line: 485
        'Returns the size in bytes of the file contents.\n        New in pyfakefs 2.9.\n        '
        # line: 486
        return self.st_size

    # line: 488
    def GetPath(self):
        # line: 489
        'Return the full path of the current object.'
        # line: 490
        names = []
        # line: 491
        obj = self
        # line: 492
        while obj:
            # line: 493
            names.insert(0, obj.name)
            # line: 494
            obj = obj.parent_dir
        # line: 495
        sep = self.filesystem._path_separator(self.name)
        # line: 496
        return self.filesystem.NormalizePath(sep.join(names[1:]))

    # line: 498
    def SetSize(self, st_size):
        # line: 507
        'Resizes file content, padding with nulls if new size exceeds the old.\n\n        Args:\n          st_size: The desired size for the file.\n\n        Raises:\n          IOError: if the st_size arg is not a non-negative integer\n                   or if st_size exceeds the available file system space\n        '
        # line: 509
        self._check_positive_int(st_size)
        # line: 510
        current_size = (self.st_size or 0)
        # line: 511
        self.filesystem.ChangeDiskUsage((st_size - current_size), self.name, self.st_dev)
        # line: 512
        if self._byte_contents:
            # line: 513
            if (st_size < current_size):
                # line: 514
                self._byte_contents = self._byte_contents[:st_size]
            elif (sys.version_info < (3, 0)):
                # line: 517
                self._byte_contents = ('%s%s' % (self._byte_contents, ('\x00' * (st_size - current_size))))
            else:
                # line: 520
                self._byte_contents += ('\x00' * (st_size - current_size))
        # line: 521
        self.st_size = st_size
        # line: 522
        self.epoch += 1

    # line: 524
    def SetATime(self, st_atime):
        # line: 529
        'Set the self.st_atime attribute.\n\n        Args:\n          st_atime: The desired access time.\n        '
        # line: 530
        self.st_atime = st_atime

    # line: 532
    def SetMTime(self, st_mtime):
        # line: 537
        'Set the self.st_mtime attribute.\n\n        Args:\n          st_mtime: The desired modification time.\n        '
        # line: 538
        self.st_mtime = st_mtime

    # line: 540
    def SetCTime(self, st_ctime):
        # line: 546
        'Set the self.st_ctime attribute.\n        New in pyfakefs 3.0.\n\n        Args:\n          st_ctime: The desired creation time.\n        '
        # line: 547
        self.st_ctime = st_ctime

    # line: 549
    def __getattr__(self, item):
        # line: 550
        'Forward some properties to stat_result.'
        # line: 551
        return getattr(self.stat_result, item)

    # line: 553
    def __setattr__(self, key, value):
        # line: 554
        'Forward some properties to stat_result.'
        # line: 555
        if (key in ('st_mode', 'st_ino', 'st_dev', 'st_nlink', 'st_uid', 'st_gid', 'st_size', 'st_atime', 'st_mtime', 'st_ctime', 'st_atime_ns', 'st_mtime_ns', 'st_ctime_ns')):
            # line: 558
            return setattr(self.stat_result, key, value)
        # line: 559
        return super(FakeFile, self).__setattr__(key, value)

    # line: 561
    def __str__(self):
        # line: 562
        return ('%s(%o)' % (self.name, self.st_mode))

    # line: 564
    def SetIno(self, st_ino):
        # line: 571
        'Set the self.st_ino attribute.\n        Note that a unique inode is assigned automatically to a new fake file.\n        Using this function does not guarantee uniqueness and should used with caution.\n\n        Args:\n          st_ino: (int) The desired inode.\n        '
        # line: 572
        self.st_ino = st_ino


# line: 575
class FakeFileFromRealFile(FakeFile):
    # line: 580
    'Represents a fake file copied from the real file system.\n    \n    The contents of the file are read on demand only.\n    New in pyfakefs 3.2.\n    '

    # line: 582
    def __init__(self, file_path, filesystem, read_only=True):
        # line: 593
        'init.\n\n        Args:\n            file_path: path to the existing file.\n            filesystem: the fake filesystem where the file is created.\n            read_only: if set, the file is treated as read-only, e.g. a write access raises an exception;\n                otherwise, writing to the file changes the fake file only as usually.\n\n        Raises:\n            OSError: if the file does not exist in the real file system.\n        '
        # line: 594
        real_stat = os.stat(file_path)
        # line: 596
        super(FakeFileFromRealFile, self).__init__(name=os.path.basename(file_path), filesystem=filesystem)
        # line: 598
        self.stat_result.set_from_stat_result(real_stat)
        # line: 599
        if read_only:
            # line: 600
            self.st_mode &= 261924
        # line: 601
        self.file_path = file_path
        # line: 602
        self.contents_read = False

    # line: 604
    @property
    # line: 604
    def byte_contents(self):
        # line: 606
        if (not self.contents_read):
            # line: 607
            self.contents_read = True
            # line: 608
            with io.open(self.file_path, 'rb') as f:
                # line: 609
                self._byte_contents = f.read()
        # line: 611
        self.st_atime = os.stat(self.file_path).st_atime
        # line: 612
        return self._byte_contents

    # line: 614
    def IsLargeFile(self):
        # line: 615
        'The contents are never faked.'
        # line: 616
        return False


# line: 619
class FakeDirectory(FakeFile):
    # line: 620
    'Provides the appearance of a real directory.'

    # line: 622
    def __init__(self, name, perm_bits=PERM_DEF, filesystem=None):
        # line: 629
        'init.\n\n        Args:\n          name:  name of the file/directory, without parent path information\n          perm_bits: permission bits. defaults to 0o777.\n          filesystem: if set, the fake filesystem where the directory is created\n        '
        # line: 630
        FakeFile.__init__(self, name, (stat.S_IFDIR | perm_bits), {}, filesystem=filesystem)
        # line: 632
        self.st_nlink += 1

    # line: 634
    def SetContents(self, contents, encoding=None):
        # line: 635
        error_class = (OSError if self.filesystem.is_windows_fs else IOError)
        # line: 636
        raise error_class(errno.EISDIR, 'Trying to write to directory')

    # line: 638
    @property
    # line: 638
    def contents(self):
        # line: 640
        'Return the list of contained directory entries.'
        # line: 641
        return self.byte_contents

    # line: 643
    @property
    # line: 643
    def ordered_dirs(self):
        # line: 645
        'Return the list of contained directory entry names ordered by creation order.'
        # line: 646
        return [item[0] for item in sorted(self.byte_contents.items(), key=(lambda entry: entry[1].st_ino))]

    # line: 649
    def AddEntry(self, path_object):
        # line: 658
        'Adds a child FakeFile to this directory.\n\n        Args:\n            path_object:  FakeFile instance to add as a child of this directory.\n\n        Raises:\n            OSError: if the directory has no write permission (Posix only)\n            OSError: if the file or directory to be added already exists\n        '
        # line: 659
        if ((not (self.st_mode & PERM_WRITE)) and (not self.filesystem.is_windows_fs)):
            # line: 660
            raise OSError(errno.EACCES, 'Permission Denied', self.GetPath())
        # line: 662
        if (path_object.name in self.contents):
            # line: 663
            raise OSError(errno.EEXIST, 'Object already exists in fake filesystem', self.GetPath())
        # line: 667
        self.contents[path_object.name] = path_object
        # line: 668
        path_object.parent_dir = self
        # line: 669
        self.st_nlink += 1
        # line: 670
        path_object.st_nlink += 1
        # line: 671
        path_object.st_dev = self.st_dev
        # line: 672
        if (path_object.st_nlink == 1):
            # line: 673
            self.filesystem.ChangeDiskUsage(path_object.GetSize(), path_object.name, self.st_dev)

    # line: 675
    def GetEntry(self, pathname_name):
        # line: 686
        'Retrieves the specified child file or directory entry.\n\n        Args:\n          pathname_name: basename of the child object to retrieve.\n\n        Returns:\n          fake file or directory object.\n\n        Raises:\n          KeyError: if no child exists by the specified name.\n        '
        # line: 687
        return self.contents[pathname_name]

    # line: 689
    def RemoveEntry(self, pathname_name, recursive=True):
        # line: 701
        'Removes the specified child file or directory.\n\n        Args:\n          pathname_name: basename of the child object to remove.\n          recursive: if True (default), the entries in contained directories are deleted first.\n            Needed to propagate removal errors (e.g. permission problems) from contained entries.\n            New in pyfakefs 2.9.\n\n        Raises:\n          KeyError: if no child exists by the specified name.\n          OSError: if user lacks permission to delete the file, or (Windows only) the file is open.\n        '
        # line: 702
        entry = self.contents[pathname_name]
        # line: 703
        if ((entry.st_mode & PERM_WRITE) == 0):
            # line: 704
            raise OSError(errno.EACCES, 'Trying to remove object without write permission', pathname_name)
        # line: 706
        if (self.filesystem.is_windows_fs and self.filesystem.HasOpenFile(entry)):
            # line: 707
            raise OSError(errno.EACCES, 'Trying to remove an open file', pathname_name)
        # line: 708
        if (recursive and isinstance(entry, FakeDirectory)):
            # line: 709
            while entry.contents:
                # line: 710
                entry.RemoveEntry(list(entry.contents)[0])
        elif (entry.st_nlink == 1):
            # line: 712
            self.filesystem.ChangeDiskUsage((- entry.GetSize()), pathname_name, entry.st_dev)
        # line: 714
        self.st_nlink -= 1
        # line: 715
        entry.st_nlink -= 1
        # line: 716
        assert (entry.st_nlink >= 0)
        # line: 718
        del self.contents[pathname_name]

    # line: 720
    def GetSize(self):
        # line: 723
        'Return the total size of all files contained in this directory tree.\n        New in pyfakefs 2.9.\n        '
        # line: 724
        return sum([item[1].GetSize() for item in self.contents.items()])

    # line: 726
    def HasParentObject(self, dir_object):
        # line: 728
        'Return `True` if dir_object is a direct or indirect parent directory,\n        or if both are the same object.'
        # line: 729
        obj = self
        # line: 730
        while obj:
            # line: 731
            if (obj == dir_object):
                # line: 732
                return True
            # line: 733
            obj = obj.parent_dir
        # line: 734
        return False

    # line: 736
    def __str__(self):
        # line: 737
        description = (super(FakeDirectory, self).__str__() + ':\n')
        # line: 738
        for item in self.contents:
            # line: 739
            item_desc = self.contents[item].__str__()
            # line: 740
            for line in item_desc.split('\n'):
                # line: 741
                if line:
                    # line: 742
                    description = (((description + '  ') + line) + '\n')
        # line: 743
        return description


# line: 746
class FakeDirectoryFromRealDirectory(FakeDirectory):
    # line: 751
    'Represents a fake directory copied from the real file system.\n    \n    The contents of the directory are read on demand only.\n    New in pyfakefs 3.2.\n    '

    # line: 753
    def __init__(self, dir_path, filesystem, read_only):
        # line: 765
        'init.\n\n        Args:\n            dir_path:  full directory path\n            filesystem: the fake filesystem where the directory is created\n            read_only: if set, all files under the directory are treated as read-only,\n                e.g. a write access raises an exception;\n                otherwise, writing to the files changes the fake files only as usually.\n                \n        Raises:\n            OSError if the directory does not exist in the real file system\n        '
        # line: 766
        real_stat = os.stat(dir_path)
        # line: 767
        super(FakeDirectoryFromRealDirectory, self).__init__(name=os.path.split(dir_path)[1], perm_bits=real_stat.st_mode, filesystem=filesystem)
        # line: 772
        self.st_ctime = real_stat.st_ctime
        # line: 773
        self.st_atime = real_stat.st_atime
        # line: 774
        self.st_mtime = real_stat.st_mtime
        # line: 775
        self.st_gid = real_stat.st_gid
        # line: 776
        self.st_uid = real_stat.st_uid
        # line: 777
        self.dir_path = dir_path
        # line: 778
        self.read_only = read_only
        # line: 779
        self.contents_read = False

    # line: 781
    @property
    # line: 781
    def contents(self):
        # line: 783
        'Return the list of contained directory entries, loading them if not already loaded.'
        # line: 784
        if (not self.contents_read):
            # line: 785
            self.contents_read = True
            # line: 786
            self.filesystem.add_real_paths([os.path.join(self.dir_path, entry) for entry in os.listdir(self.dir_path)], read_only=self.read_only)
        # line: 789
        return self.byte_contents

    # line: 791
    def GetSize(self):
        # line: 793
        if (not self.contents_read):
            # line: 794
            return 0
        # line: 795
        return super(FakeDirectoryFromRealDirectory, self).GetSize()


# line: 798
class FakeFilesystem(object):
    # line: 809
    'Provides the appearance of a real directory tree for unit testing.\n\n    Attributes:\n        path_separator: The path separator, corresponds to `os.path.sep`.\n        alternative_path_separator: Corresponds to `os.path.altsep`.\n        is_windows_fs: `True` in a Windows file system, `False` otherwise.\n        is_case_sensitive: `True` if a case-sensitive file system is assumed.\n        root: The root `FakeDirectory` entry of the file system.\n        cwd: The current working directory path.\n        umask: The umask used for newly created files, see `os.umask`.\n    '

    # line: 811
    def __init__(self, path_separator=os.path.sep, total_size=None):
        # line: 823
        "init.\n\n        Args:\n            path_separator:  optional substitute for os.path.sep\n            total_size: if not None, the total size in bytes of the root filesystem.\n                New in pyfakefs 2.9.\n\n        Example usage to emulate real file systems:\n            filesystem = FakeFilesystem(\n                alt_path_separator='/' if _is_windows else None)\n\n        "
        # line: 824
        self.path_separator = path_separator
        # line: 825
        self.alternative_path_separator = os.path.altsep
        # line: 826
        if (path_separator != os.sep):
            # line: 827
            self.alternative_path_separator = None
        # line: 832
        self.is_windows_fs = (sys.platform == 'win32')
        # line: 836
        self.is_case_sensitive = (sys.platform not in ['win32', 'cygwin', 'darwin'])
        # line: 838
        self.root = FakeDirectory(self.path_separator, filesystem=self)
        # line: 839
        self.cwd = self.root.name
        # line: 841
        self.umask = os.umask(18)
        # line: 842
        os.umask(self.umask)
        # line: 845
        self.open_files = []
        # line: 847
        self._free_fd_heap = []
        # line: 849
        self._last_ino = 0
        # line: 850
        self._last_dev = 0
        # line: 851
        self.mount_points = {}
        # line: 852
        self.AddMountPoint(self.root.name, total_size)

    # line: 854
    @staticmethod
    # line: 854
    def _matching_string(matched, string):
        # line: 858
        'Return the string as byte or unicode depending \n        on the type of matched, assuming string is an ASCII string.\n        '
        # line: 859
        if (string is None):
            # line: 860
            return string
        # line: 861
        if (sys.version_info < (3,)):
            # line: 862
            if isinstance(matched, unicode):
                # line: 863
                return unicode(string)
            else:
                # line: 865
                return string
        elif isinstance(matched, bytes):
            # line: 868
            return bytes(string, 'ascii')
        else:
            # line: 870
            return string

    # line: 872
    def _path_separator(self, path):
        # line: 873
        'Return the path separator as the same type as path'
        # line: 874
        return self._matching_string(path, self.path_separator)

    # line: 876
    def _alternative_path_separator(self, path):
        # line: 877
        'Return the alternative path separator as the same type as path'
        # line: 878
        return self._matching_string(path, self.alternative_path_separator)

    # line: 880
    def _IsLinkSupported(self):
        # line: 882
        return ((not self.is_windows_fs) or (sys.version_info >= (3, 2)))

    # line: 884
    def AddMountPoint(self, path, total_size=None):
        # line: 900
        'Add a new mount point for a filesystem device.\n        The mount point gets a new unique device number.\n        New in pyfakefs 2.9.\n\n        Args:\n            path: The root path for the new mount path.\n\n            total_size: The new total size of the added filesystem device\n                in bytes. Defaults to infinite size.\n\n        Returns:\n            The newly created mount point dict.\n\n        Raises:\n            OSError: if trying to mount an existing mount point again.\n        '
        # line: 901
        path = self.NormalizePath(path)
        # line: 902
        if (path in self.mount_points):
            # line: 903
            raise OSError(errno.EEXIST, 'Mount point cannot be added twice', path)
        # line: 904
        self._last_dev += 1
        # line: 905
        self.mount_points[path] = {'idev': self._last_dev, 'total_size': total_size, 'used_size': 0, }
        # line: 909
        root_dir = (self.root if (path == self.root.name) else self.CreateDirectory(path))
        # line: 910
        root_dir.st_dev = self._last_dev
        # line: 911
        return self.mount_points[path]

    # line: 913
    def _AutoMountDriveIfNeeded(self, path, force=False):
        # line: 914
        if (self.is_windows_fs and (force or (not self._MountPointForPath(path)))):
            # line: 915
            drive = self.SplitDrive(path)[0]
            # line: 916
            if drive:
                # line: 917
                return self.AddMountPoint(path=drive)

    # line: 919
    def _MountPointForPath(self, path):

        # line: 920
        def to_str(string):
            # line: 921
            'Convert the str, unicode or byte object to a str using the default encoding.'
            # line: 922
            if ((string is None) or isinstance(string, str)):
                # line: 923
                return string
            # line: 924
            if (sys.version_info < (3, 0)):
                # line: 925
                return string.encode(locale.getpreferredencoding(False))
            else:
                # line: 927
                return string.decode(locale.getpreferredencoding(False))
        # line: 929
        path = self.NormalizePath(self.NormalizeCase(path))
        # line: 930
        if (path in self.mount_points):
            # line: 931
            return self.mount_points[path]
        # line: 932
        mount_path = self._matching_string(path, '')
        # line: 933
        drive = self.SplitDrive(path)[:1]
        # line: 934
        for root_path in self.mount_points:
            # line: 935
            root_path = self._matching_string(path, root_path)
            # line: 936
            if (drive and (not root_path.startswith(drive))):
                # line: 937
                continue
            # line: 938
            if (path.startswith(root_path) and (len(root_path) > len(mount_path))):
                # line: 939
                mount_path = root_path
        # line: 940
        if mount_path:
            # line: 941
            return self.mount_points[to_str(mount_path)]
        # line: 942
        mount_point = self._AutoMountDriveIfNeeded(path, force=True)
        # line: 943
        assert mount_point
        # line: 944
        return mount_point

    # line: 946
    def _MountPointForDevice(self, idev):
        # line: 947
        for mount_point in self.mount_points.values():
            # line: 948
            if (mount_point['idev'] == idev):
                # line: 949
                return mount_point

    # line: 951
    def GetDiskUsage(self, path=None):
        # line: 961
        "Return the total, used and free disk space in bytes as named tuple,\n        or placeholder values simulating unlimited space if not set.\n        Note: This matches the return value of shutil.disk_usage().\n        New in pyfakefs 2.9.\n\n        Args:\n            path: The disk space is returned for the file system device where\n                path resides.\n                Defaults to the root path (e.g. '/' on Unix systems).\n        "
        # line: 962
        DiskUsage = namedtuple('usage', 'total, used, free')
        # line: 963
        if (path is None):
            # line: 964
            mount_point = self.mount_points[self.root.name]
        else:
            # line: 966
            mount_point = self._MountPointForPath(path)
        # line: 967
        if (mount_point and (mount_point['total_size'] is not None)):
            # line: 968
            return DiskUsage(mount_point['total_size'], mount_point['used_size'], (mount_point['total_size'] - mount_point['used_size']))
        # line: 970
        return DiskUsage((((1024 + 1024) * 1024) * 1024), 0, (((1024 * 1024) * 1024) * 1024))

    # line: 972
    def SetDiskUsage(self, total_size, path=None):
        # line: 986
        "Changes the total size of the file system, preserving the used space.\n        Example usage: set the size of an auto-mounted Windows drive.\n        New in pyfakefs 2.9.\n\n        Args:\n            total_size: The new total size of the filesystem in bytes.\n\n            path: The disk space is changed for the file system device where\n                path resides.\n                Defaults to the root path (e.g. '/' on Unix systems).\n\n        Raises:\n            IOError: if the new space is smaller than the used size.\n        "
        # line: 987
        if (path is None):
            # line: 988
            path = self.root.name
        # line: 989
        mount_point = self._MountPointForPath(path)
        # line: 990
        if ((mount_point['total_size'] is not None) and (mount_point['used_size'] > total_size)):
            # line: 991
            raise IOError(errno.ENOSPC, ('Fake file system: cannot change size to %r bytes - used space is larger' % total_size), path)
        # line: 994
        mount_point['total_size'] = total_size

    # line: 996
    def ChangeDiskUsage(self, usage_change, file_path, st_dev):
        # line: 1010
        'Change the used disk space by the given amount.\n        New in pyfakefs 2.9.\n\n        Args:\n            usage_change: Number of bytes added to the used space.\n                If negative, the used space will be decreased.\n\n          file_path: The path of the object needing the disk space.\n\n          st_dev: The device ID for the respective file system.\n\n        Raises:\n            IOError: if usage_change exceeds the free file system space\n        '
        # line: 1011
        mount_point = self._MountPointForDevice(st_dev)
        # line: 1012
        if mount_point:
            # line: 1013
            if (mount_point['total_size'] is not None):
                # line: 1014
                if ((mount_point['total_size'] - mount_point['used_size']) < usage_change):
                    # line: 1015
                    raise IOError(errno.ENOSPC, ('Fake file system: disk is full, failed to add %r bytes' % usage_change), file_path)
            # line: 1018
            mount_point['used_size'] += usage_change

    # line: 1020
    def GetStat(self, entry_path, follow_symlinks=True):
        # line: 1034
        "Return the os.stat-like tuple for the FakeFile object of entry_path.\n        New in pyfakefs 3.0.\n\n        Args:\n          entry_path:  path to filesystem object to retrieve.\n          follow_symlinks: if False and entry_path points to a symlink, the link itself is inspected\n              instead of the linked object.\n\n        Returns:\n          the FakeStatResult object corresponding to entry_path.\n\n        Raises:\n          OSError: if the filesystem object doesn't exist.\n        "
        # line: 1036
        try:
            # line: 1037
            file_object = self.ResolveObject(entry_path, follow_symlinks, allow_fd=True)
            # line: 1038
            return file_object.stat_result.copy()
        # line: 1039
        except IOError as io_error:
            # line: 1040
            raise OSError(io_error.errno, io_error.strerror, entry_path)

    # line: 1042
    def ChangeMode(self, path, mode, follow_symlinks=True):
        # line: 1051
        'Change the permissions of a file as encoded in integer mode.\n        New in pyfakefs 3.0.\n\n        Args:\n          path: (str) Path to the file.\n          mode: (int) Permissions.\n          follow_symlinks: if False and entry_path points to a symlink, the link itself is affected\n              instead of the linked object.\n        '
        # line: 1052
        try:
            # line: 1053
            file_object = self.ResolveObject(path, follow_symlinks, allow_fd=True)
        # line: 1054
        except IOError as io_error:
            # line: 1055
            if (io_error.errno == errno.ENOENT):
                # line: 1056
                raise OSError(errno.ENOENT, 'No such file or directory in fake filesystem', path)
            # line: 1059
            raise
        # line: 1060
        file_object.st_mode = ((file_object.st_mode & (~ PERM_ALL)) | (mode & PERM_ALL))
        # line: 1062
        file_object.st_ctime = time.time()

    # line: 1064
    def UpdateTime(self, path, times=None, ns=None, follow_symlinks=True):
        # line: 1086
        'Change the access and modified times of a file.\n        New in pyfakefs 3.0.\n\n        Args:\n            path: (str) Path to the file.\n            times: 2-tuple of int or float numbers, of the form (atime, mtime) \n                which is used to set the access and modified times in seconds. \n                If None, both times are set to the current time.\n            ns: 2-tuple of int numbers, of the form (atime, mtime)  which is \n                used to set the access and modified times in nanoseconds. \n                If None, both times are set to the current time.\n                New in Python 3.3. New in pyfakefs 3.3.\n            follow_symlinks: If `False` and entry_path points to a symlink, \n                the link itself is queried instead of the linked object. \n                New in Python 3.3. New in pyfakefs 3.0.\n    \n            Raises:\n                TypeError: If anything other than the expected types is \n                    specified in the passed `times` or `ns` tuple, \n                    or if the tuple length is not equal to 2.\n                ValueError: If both times and ns are specified.\n        '
        # line: 1087
        if ((times is not None) and (ns is not None)):
            # line: 1088
            raise ValueError("utime: you may specify either 'times' or 'ns' but not both")
        # line: 1089
        if ((times is not None) and (len(times) != 2)):
            # line: 1090
            raise TypeError("utime: 'times' must be either a tuple of two ints or None")
        # line: 1091
        if ((ns is not None) and (len(ns) != 2)):
            # line: 1092
            raise TypeError("utime: 'ns' must be a tuple of two ints")
        # line: 1094
        try:
            # line: 1095
            file_object = self.ResolveObject(path, follow_symlinks, allow_fd=True)
        # line: 1096
        except IOError as io_error:
            # line: 1097
            if (io_error.errno == errno.ENOENT):
                # line: 1098
                raise OSError(errno.ENOENT, 'No such file or directory in fake filesystem', path)
            # line: 1101
            raise
        # line: 1102
        if (times is not None):
            # line: 1103
            for file_time in times:
                # line: 1104
                if (not isinstance(file_time, (int, float))):
                    # line: 1105
                    raise TypeError('atime and mtime must be numbers')
            # line: 1107
            file_object.st_atime = times[0]
            # line: 1108
            file_object.st_mtime = times[1]
        elif (ns is not None):
            # line: 1110
            for file_time in ns:
                # line: 1111
                if (not isinstance(file_time, int)):
                    # line: 1112
                    raise TypeError('atime and mtime must be ints')
            # line: 1114
            file_object.st_atime_ns = ns[0]
            # line: 1115
            file_object.st_mtime_ns = ns[1]
        else:
            # line: 1117
            current_time = time.time()
            # line: 1118
            file_object.st_atime = current_time
            # line: 1119
            file_object.st_mtime = current_time

    # line: 1121
    def SetIno(self, path, st_ino):
        # line: 1129
        "Set the self.st_ino attribute of file at 'path'.\n        Note that a unique inode is assigned automatically to a new fake file.\n        Using this function does not guarantee uniqueness and should used with caution.\n\n        Args:\n          path: Path to file.\n          st_ino: The desired inode.\n        "
        # line: 1130
        self.GetObject(path).SetIno(st_ino)

    # line: 1132
    def AddOpenFile(self, file_obj):
        # line: 1142
        'Add file_obj to the list of open files on the filesystem.\n\n        The position in the self.open_files array is the file descriptor number.\n\n        Args:\n          file_obj:  file object to be added to open files list.\n\n        Returns:\n          File descriptor number for the file object.\n        '
        # line: 1143
        if self._free_fd_heap:
            # line: 1144
            open_fd = heapq.heappop(self._free_fd_heap)
            # line: 1145
            self.open_files[open_fd] = file_obj
            # line: 1146
            return open_fd
        # line: 1148
        self.open_files.append(file_obj)
        # line: 1149
        return (len(self.open_files) - 1)

    # line: 1151
    def CloseOpenFile(self, file_des):
        # line: 1158
        'Remove file object with given descriptor from the list of open files.\n\n        Sets the entry in open_files to None.\n\n        Args:\n          file_des:  descriptor of file object to be removed from open files list.\n        '
        # line: 1159
        self.open_files[file_des] = None
        # line: 1160
        heapq.heappush(self._free_fd_heap, file_des)

    # line: 1162
    def GetOpenFile(self, file_des):
        # line: 1174
        'Return an open file.\n\n        Args:\n          file_des:  file descriptor of the open file.\n\n        Raises:\n          OSError: an invalid file descriptor.\n          TypeError: filedes is not an integer.\n\n        Returns:\n          Open file object.\n        '
        # line: 1175
        if (not isinstance(file_des, int)):
            # line: 1176
            raise TypeError('an integer is required')
        # line: 1177
        if ((file_des >= len(self.open_files)) or (self.open_files[file_des] is None)):
            # line: 1179
            raise OSError(errno.EBADF, 'Bad file descriptor', file_des)
        # line: 1180
        return self.open_files[file_des]

    # line: 1182
    def HasOpenFile(self, file_object):
        # line: 1191
        'Return True if the given file object is in the list of open files.\n        New in pyfakefs 2.9.\n\n        Args:\n          file_object: The FakeFile object to be checked.\n\n        Returns:\n          True if the file is open.\n        '
        # line: 1192
        return (file_object in [wrapper.GetObject() for wrapper in self.open_files if wrapper])

    # line: 1194
    def NormalizePathSeparator(self, path):
        # line: 1204
        'Replace all appearances of alternative path separator with path separator.\n        Do nothing if no alternative separator is set.\n        New in pyfakefs 2.9.\n\n        Args:\n          path: the path to be normalized.\n\n        Returns:\n          The normalized path that will be used internally.\n        '
        # line: 1205
        if (sys.version_info >= (3, 6)):
            # line: 1206
            path = os.fspath(path)
        # line: 1207
        if ((self.alternative_path_separator is None) or (not path)):
            # line: 1208
            return path
        # line: 1209
        return path.replace(self._alternative_path_separator(path), self._path_separator(path))

    # line: 1211
    def CollapsePath(self, path):
        # line: 1230
        "Mimic os.path.normpath using the specified path_separator.\n\n        Mimics os.path.normpath using the path_separator that was specified\n        for this FakeFilesystem. Normalizes the path, but unlike the method\n        NormalizePath, does not make it absolute.  Eliminates dot components\n        (. and ..) and combines repeated path separators (//).  Initial ..\n        components are left in place for relative paths.  If the result is an empty\n        path, '.' is returned instead.\n\n        This also replaces alternative path separator with path separator.  That is,\n        it behaves like the real os.path.normpath on Windows if initialized with\n        '\\' as path separator and  '/' as alternative separator.\n\n        Args:\n          path:  (str) The path to normalize.\n\n        Returns:\n          (str) A copy of path with empty components and dot components removed.\n        "
        # line: 1231
        path = self.NormalizePathSeparator(path)
        # line: 1232
        (drive, path) = self.SplitDrive(path)
        # line: 1233
        sep = self._path_separator(path)
        # line: 1234
        is_absolute_path = path.startswith(sep)
        # line: 1235
        path_components = path.split(sep)
        # line: 1236
        collapsed_path_components = []
        # line: 1237
        dot = self._matching_string(path, '.')
        # line: 1238
        dotdot = self._matching_string(path, '..')
        # line: 1239
        for component in path_components:
            # line: 1240
            if ((not component) or (component == dot)):
                # line: 1241
                continue
            # line: 1242
            if (component == dotdot):
                # line: 1243
                if (collapsed_path_components and (collapsed_path_components[(-1)] != dotdot)):
                    # line: 1246
                    collapsed_path_components.pop()
                    # line: 1247
                    continue
                elif is_absolute_path:
                    # line: 1250
                    continue
            # line: 1251
            collapsed_path_components.append(component)
        # line: 1252
        collapsed_path = sep.join(collapsed_path_components)
        # line: 1253
        if is_absolute_path:
            # line: 1254
            collapsed_path = (sep + collapsed_path)
        # line: 1255
        return ((drive + collapsed_path) or dot)

    # line: 1257
    def NormalizeCase(self, path):
        # line: 1267
        'Return a normalized case version of the given path for case-insensitive\n        file systems. For case-sensitive file systems, return path unchanged.\n        New in pyfakefs 2.9.\n\n        Args:\n            path: the file path to be transformed\n\n        Returns:\n            A version of path matching the case of existing path elements.\n        '

        # line: 1268
        def components_to_path():
            # line: 1269
            if (len(path_components) > len(normalized_components)):
                # line: 1270
                normalized_components.extend(path_components[len(normalized_components):])
            # line: 1271
            sep = self._path_separator(path)
            # line: 1272
            normalized_path = sep.join(normalized_components)
            # line: 1273
            if (path.startswith(sep) and (not normalized_path.startswith(sep))):
                # line: 1274
                normalized_path = (sep + normalized_path)
            # line: 1275
            return normalized_path
        # line: 1277
        if (self.is_case_sensitive or (not path)):
            # line: 1278
            return path
        # line: 1279
        path_components = self.GetPathComponents(path)
        # line: 1280
        normalized_components = []
        # line: 1281
        current_dir = self.root
        # line: 1282
        for component in path_components:
            # line: 1283
            if (not isinstance(current_dir, FakeDirectory)):
                # line: 1284
                return components_to_path()
            # line: 1285
            (dir_name, current_dir) = self._DirectoryContent(current_dir, component)
            # line: 1286
            if ((current_dir is None) or (isinstance(current_dir, FakeDirectory) and (current_dir._byte_contents is None) and (current_dir.st_size == 0))):
                # line: 1290
                return components_to_path()
            # line: 1291
            normalized_components.append(dir_name)
        # line: 1292
        return components_to_path()

    # line: 1294
    def NormalizePath(self, path):
        # line: 1306
        'Absolutize and minimalize the given path.\n\n        Forces all relative paths to be absolute, and normalizes the path to\n        eliminate dot and empty components.\n\n        Args:\n          path:  path to normalize\n\n        Returns:\n          The normalized path relative to the current working directory, or the root\n            directory if path is empty.\n        '
        # line: 1307
        path = self.NormalizePathSeparator(path)
        # line: 1308
        if (not path):
            # line: 1309
            path = self.path_separator
        elif (not self._StartsWithRootPath(path)):
            # line: 1312
            root_name = self._matching_string(path, self.root.name)
            # line: 1313
            empty = self._matching_string(path, '')
            # line: 1314
            path = self._path_separator(path).join(((((self.cwd != root_name) and self.cwd) or empty), path))
        # line: 1316
        if (path == self._matching_string(path, '.')):
            # line: 1317
            path = self.cwd
        # line: 1318
        return self.CollapsePath(path)

    # line: 1320
    def SplitPath(self, path):
        # line: 1332
        'Mimic os.path.split using the specified path_separator.\n\n        Mimics os.path.split using the path_separator that was specified\n        for this FakeFilesystem.\n\n        Args:\n          path:  (str) The path to split.\n\n        Returns:\n          (str) A duple (pathname, basename) for which pathname does not\n              end with a slash, and basename does not contain a slash.\n        '
        # line: 1333
        (drive, path) = self.SplitDrive(path)
        # line: 1334
        path = self.NormalizePathSeparator(path)
        # line: 1335
        sep = self._path_separator(path)
        # line: 1336
        path_components = path.split(sep)
        # line: 1337
        if (not path_components):
            # line: 1338
            return ('', '')
        # line: 1339
        basename = path_components.pop()
        # line: 1340
        if (not path_components):
            # line: 1341
            return ('', basename)
        # line: 1342
        for component in path_components:
            # line: 1343
            if component:
                # line: 1346
                while (not path_components[(-1)]):
                    # line: 1347
                    path_components.pop()
                # line: 1348
                return ((drive + sep.join(path_components)), basename)
        # line: 1350
        return ((drive or sep), basename)

    # line: 1352
    def SplitDrive(self, path):
        # line: 1363
        'Splits the path into the drive part and the rest of the path.\n        New in pyfakefs 2.9.\n\n        Taken from Windows specific implementation in Python 3.5 and slightly adapted.\n\n        Args:\n            path: the full path to be split.\n\n        Returns: a tuple of the drive part and the rest of the path, or of an empty string\n            and the full path if drive letters are not supported or no drive is present.\n        '
        # line: 1364
        if (sys.version_info >= (3, 6)):
            # line: 1365
            path = os.fspath(path)
        # line: 1366
        if self.is_windows_fs:
            # line: 1367
            if (len(path) >= 2):
                # line: 1368
                path = self.NormalizePathSeparator(path)
                # line: 1369
                sep = self._path_separator(path)
                # line: 1371
                if (sys.version_info >= (2, 7, 8)):
                    # line: 1372
                    if ((path[0:2] == (sep * 2)) and (path[2:3] != sep)):
                        # line: 1375
                        sep_index = path.find(sep, 2)
                        # line: 1376
                        if (sep_index == (-1)):
                            # line: 1377
                            return (path[:0], path)
                        # line: 1378
                        sep_index2 = path.find(sep, (sep_index + 1))
                        # line: 1379
                        if (sep_index2 == (sep_index + 1)):
                            # line: 1380
                            return (path[:0], path)
                        # line: 1381
                        if (sep_index2 == (-1)):
                            # line: 1382
                            sep_index2 = len(path)
                        # line: 1383
                        return (path[:sep_index2], path[sep_index2:])
                # line: 1384
                if (path[1:2] == self._matching_string(path, ':')):
                    # line: 1385
                    return (path[:2], path[2:])
        # line: 1386
        return (path[:0], path)

    # line: 1388
    def _JoinPathsWithDriveSupport(self, *all_paths):
        # line: 1389
        'Taken from Python 3.5 os.path.join() code in ntpath.py and slightly adapted'
        # line: 1390
        base_path = all_paths[0]
        # line: 1391
        paths_to_add = all_paths[1:]
        # line: 1392
        sep = self._path_separator(base_path)
        # line: 1393
        seps = [sep, self._alternative_path_separator(base_path)]
        # line: 1394
        (result_drive, result_path) = self.SplitDrive(base_path)
        # line: 1395
        for path in paths_to_add:
            # line: 1396
            (drive_part, path_part) = self.SplitDrive(path)
            # line: 1397
            if (path_part and (path_part[:1] in seps)):
                # line: 1399
                if (drive_part or (not result_drive)):
                    # line: 1400
                    result_drive = drive_part
                # line: 1401
                result_path = path_part
                # line: 1402
                continue
            elif (drive_part and (drive_part != result_drive)):
                # line: 1404
                if (self.is_case_sensitive or (drive_part.lower() != result_drive.lower())):
                    # line: 1406
                    result_drive = drive_part
                    # line: 1407
                    result_path = path_part
                    # line: 1408
                    continue
                # line: 1410
                result_drive = drive_part
            # line: 1412
            if (result_path and (result_path[(-1):] not in seps)):
                # line: 1413
                result_path = (result_path + sep)
            # line: 1414
            result_path = (result_path + path_part)
        # line: 1416
        colon = self._matching_string(base_path, ':')
        # line: 1417
        if (result_path and (result_path[:1] not in seps) and result_drive and (result_drive[(-1):] != colon)):
            # line: 1419
            return ((result_drive + sep) + result_path)
        # line: 1420
        return (result_drive + result_path)

    # line: 1422
    def JoinPaths(self, *paths):
        # line: 1431
        'Mimic os.path.join using the specified path_separator.\n\n        Args:\n          *paths:  (str) Zero or more paths to join.\n\n        Returns:\n          (str) The paths joined by the path separator, starting with the last\n              absolute path in paths.\n        '
        # line: 1432
        if (sys.version_info >= (3, 6)):
            # line: 1433
            paths = [os.fspath(path) for path in paths]
        # line: 1434
        if (len(paths) == 1):
            # line: 1435
            return paths[0]
        # line: 1436
        if self.is_windows_fs:
            # line: 1437
            return self._JoinPathsWithDriveSupport(*paths)
        # line: 1438
        joined_path_segments = []
        # line: 1439
        sep = self._path_separator(paths[0])
        # line: 1440
        for path_segment in paths:
            # line: 1441
            if self._StartsWithRootPath(path_segment):
                # line: 1443
                joined_path_segments = [path_segment]
            else:
                # line: 1445
                if (joined_path_segments and (not joined_path_segments[(-1)].endswith(sep))):
                    # line: 1447
                    joined_path_segments.append(sep)
                # line: 1448
                if path_segment:
                    # line: 1449
                    joined_path_segments.append(path_segment)
        # line: 1450
        return self._matching_string(paths[0], '').join(joined_path_segments)

    # line: 1452
    def GetPathComponents(self, path):
        # line: 1473
        'Breaks the path into a list of component names.\n\n        Does not include the root directory as a component, as all paths\n        are considered relative to the root directory for the FakeFilesystem.\n        Callers should basically follow this pattern:\n\n        >>> file_path = self.NormalizePath(file_path)\n        >>> path_components = self.GetPathComponents(file_path)\n        >>> current_dir = self.root\n        >>> for component in path_components:\n        >>>     if component not in current_dir.contents:\n        >>>         raise IOError\n        >>>     DoStuffWithComponent(current_dir, component)\n        >>>     current_dir = current_dir.GetEntry(component)\n\n        Args:\n            path:  path to tokenize\n\n        Returns:\n            The list of names split from path\n        '
        # line: 1474
        if ((not path) or (path == self._path_separator(path))):
            # line: 1475
            return []
        # line: 1476
        (drive, path) = self.SplitDrive(path)
        # line: 1477
        path_components = path.split(self._path_separator(path))
        # line: 1478
        assert (drive or path_components)
        # line: 1479
        if (not path_components[0]):
            # line: 1481
            path_components = path_components[1:]
        # line: 1482
        if drive:
            # line: 1483
            path_components.insert(0, drive)
        # line: 1484
        return path_components

    # line: 1486
    def StartsWithDriveLetter(self, file_path):
        # line: 1496
        'Return True if file_path starts with a drive letter.\n        New in pyfakefs 2.9.\n\n        Args:\n            file_path: the full path to be examined.\n\n        Returns:\n            True if drive letter support is enabled in the filesystem and\n            the path starts with a drive letter.\n        '
        # line: 1497
        colon = self._matching_string(file_path, ':')
        # line: 1498
        return (self.is_windows_fs and (len(file_path) >= 2) and file_path[:1].isalpha and (file_path[1:2] == colon))

    # line: 1501
    def _StartsWithRootPath(self, file_path):
        # line: 1502
        root_name = self._matching_string(file_path, self.root.name)
        # line: 1503
        return (file_path.startswith(root_name) or ((not self.is_case_sensitive) and file_path.lower().startswith(root_name.lower())) or self.StartsWithDriveLetter(file_path))

    # line: 1508
    def _IsRootPath(self, file_path):
        # line: 1509
        root_name = self._matching_string(file_path, self.root.name)
        # line: 1510
        return ((file_path == root_name) or ((not self.is_case_sensitive) and (file_path.lower() == root_name.lower())) or ((len(file_path) == 2) and self.StartsWithDriveLetter(file_path)))

    # line: 1514
    def _EndsWithPathSeparator(self, file_path):
        # line: 1515
        return (file_path and (file_path.endswith(self._path_separator(file_path)) or ((self.alternative_path_separator is not None) and file_path.endswith(self._alternative_path_separator(file_path)))))

    # line: 1519
    def _DirectoryContent(self, directory, component):
        # line: 1520
        if (not isinstance(directory, FakeDirectory)):
            # line: 1521
            return (None, None)
        # line: 1522
        if (component in directory.contents):
            # line: 1523
            return (component, directory.contents[component])
        # line: 1524
        if (not self.is_case_sensitive):
            # line: 1525
            matching_content = [(subdir, directory.contents[subdir]) for subdir in directory.contents if (subdir.lower() == component.lower())]
            # line: 1528
            if matching_content:
                # line: 1529
                return matching_content[0]
        # line: 1531
        return (None, None)

    # line: 1533
    def Exists(self, file_path):
        # line: 1544
        'Return true if a path points to an existing file system object.\n\n        Args:\n          file_path:  path to examine.\n\n        Returns:\n          (bool) True if the corresponding object exists.\n\n        Raises:\n          TypeError: if file_path is None.\n        '
        # line: 1545
        if (sys.version_info >= (3, 6)):
            # line: 1546
            file_path = os.fspath(file_path)
        # line: 1547
        if (file_path is None):
            # line: 1548
            raise TypeError
        # line: 1549
        if (not file_path):
            # line: 1550
            return False
        # line: 1551
        try:
            # line: 1552
            file_path = self.ResolvePath(file_path)
        # line: 1553
        except (IOError, OSError):
            # line: 1554
            return False
        # line: 1555
        if (file_path == self.root.name):
            # line: 1556
            return True
        # line: 1557
        path_components = self.GetPathComponents(file_path)
        # line: 1558
        current_dir = self.root
        # line: 1559
        for component in path_components:
            # line: 1560
            current_dir = self._DirectoryContent(current_dir, component)[1]
            # line: 1561
            if (not current_dir):
                # line: 1562
                return False
        # line: 1563
        return True

    # line: 1565
    def ResolvePath(self, file_path, allow_fd=False, raw_io=True):
        # line: 1601
        "Follow a path, resolving symlinks.\n\n        ResolvePath traverses the filesystem along the specified file path,\n        resolving file names and symbolic links until all elements of the path are\n        exhausted, or we reach a file which does not exist.  If all the elements\n        are not consumed, they just get appended to the path resolved so far.\n        This gives us the path which is as resolved as it can be, even if the file\n        does not exist.\n\n        This behavior mimics Unix semantics, and is best shown by example.  Given a\n        file system that looks like this:\n\n              /a/b/\n              /a/b/c -> /a/b2          c is a symlink to /a/b2\n              /a/b2/x\n              /a/c   -> ../d\n              /a/x   -> y\n\n         Then:\n              /a/b/x      =>  /a/b/x\n              /a/c        =>  /a/d\n              /a/x        =>  /a/y\n              /a/b/c/d/e  =>  /a/b2/d/e\n\n        Args:\n            file_path:  path to examine.\n            allow_fd: If `True`, `file_path` may be open file descriptor\n            raw_io: `True` if called from low-level I/O functions\n\n        Returns:\n            resolved_path (string) or None.\n\n        Raises:\n            TypeError: if file_path is None.\n            IOError: if file_path is '' or a part of the path doesn't exist.\n        "

        # line: 1603
        def _ComponentsToPath(component_folders):
            # line: 1604
            sep = (self._path_separator(component_folders[0]) if component_folders else self.path_separator)
            # line: 1606
            path = sep.join(component_folders)
            # line: 1607
            if (not self._StartsWithRootPath(path)):
                # line: 1608
                path = (sep + path)
            # line: 1609
            return path

        # line: 1611
        def _ValidRelativePath(file_path):
            # line: 1612
            slash_dotdot = self._matching_string(file_path, '/..')
            # line: 1613
            while (file_path and (slash_dotdot in file_path)):
                # line: 1614
                file_path = file_path[:file_path.rfind(slash_dotdot)]
                # line: 1615
                if (not self.Exists(self.NormalizePath(file_path))):
                    # line: 1616
                    return False
            # line: 1617
            return True

        # line: 1619
        def _FollowLink(link_path_components, link):
            # line: 1639
            'Follow a link w.r.t. a path resolved so far.\n\n            The component is either a real file, which is a no-op, or a symlink.\n            In the case of a symlink, we have to modify the path as built up so far\n              /a/b => ../c   should yield /a/../c (which will normalize to /a/c)\n              /a/b => x      should yield /a/x\n              /a/b => /x/y/z should yield /x/y/z\n            The modified path may land us in a new spot which is itself a\n            link, so we may repeat the process.\n\n            Args:\n              link_path_components: The resolved path built up to the link so far.\n              link: The link object itself.\n\n            Returns:\n              (string) the updated path resolved after following the link.\n\n            Raises:\n              IOError: if there are too many levels of symbolic link\n            '
            # line: 1640
            link_path = link.contents
            # line: 1641
            sep = self._path_separator(link_path)
            # line: 1642
            alt_sep = self._alternative_path_separator(link_path)
            # line: 1646
            if ((not link_path.startswith(sep)) and ((alt_sep is None) or (not link_path.startswith(alt_sep)))):
                # line: 1652
                components = link_path_components[:(-1)]
                # line: 1653
                components.append(link_path)
                # line: 1654
                link_path = sep.join(components)
            # line: 1656
            return self.CollapsePath(link_path)
        # line: 1658
        if (allow_fd and (sys.version_info >= (3, 3)) and isinstance(file_path, int)):
            # line: 1659
            return self.GetOpenFile(file_path).GetObject().GetPath()
        # line: 1661
        if (sys.version_info >= (3, 6)):
            # line: 1662
            file_path = os.fspath(file_path)
        # line: 1663
        if (file_path is None):
            # line: 1665
            raise TypeError('Expected file system path string, received None')
        # line: 1666
        if ((not file_path) or (not _ValidRelativePath(file_path))):
            # line: 1669
            raise IOError(errno.ENOENT, ("No such file or directory: '%s'" % file_path))
        # line: 1671
        file_path = self.NormalizePath(self.NormalizeCase(file_path))
        # line: 1672
        if self._IsRootPath(file_path):
            # line: 1673
            return file_path
        # line: 1675
        current_dir = self.root
        # line: 1676
        path_components = self.GetPathComponents(file_path)
        # line: 1678
        resolved_components = []
        # line: 1679
        link_depth = 0
        # line: 1680
        while path_components:
            # line: 1681
            component = path_components.pop(0)
            # line: 1682
            resolved_components.append(component)
            # line: 1683
            current_dir = self._DirectoryContent(current_dir, component)[1]
            # line: 1684
            if (current_dir is None):
                # line: 1690
                resolved_components.extend(path_components)
                # line: 1691
                break
            # line: 1694
            if stat.S_ISLNK(current_dir.st_mode):
                # line: 1698
                if (link_depth > _MAX_LINK_DEPTH):
                    # line: 1699
                    error_class = (OSError if raw_io else IOError)
                    # line: 1700
                    raise error_class(errno.ELOOP, ("Too many levels of symbolic links: '%s'" % _ComponentsToPath(resolved_components)))
                # line: 1704
                link_path = _FollowLink(resolved_components, current_dir)
                # line: 1708
                target_components = self.GetPathComponents(link_path)
                # line: 1709
                path_components = (target_components + path_components)
                # line: 1710
                resolved_components = []
                # line: 1711
                current_dir = self.root
                # line: 1712
                link_depth += 1
        # line: 1713
        return _ComponentsToPath(resolved_components)

    # line: 1715
    def GetObjectFromNormalizedPath(self, file_path):
        # line: 1727
        'Search for the specified filesystem object within the fake filesystem.\n\n        Args:\n          file_path: specifies target FakeFile object to retrieve, with a\n              path that has already been normalized/resolved.\n\n        Returns:\n          the FakeFile object corresponding to file_path.\n\n        Raises:\n          IOError: if the object is not found.\n        '
        # line: 1728
        if (sys.version_info >= (3, 6)):
            # line: 1729
            file_path = os.fspath(file_path)
        # line: 1730
        if (file_path == self.root.name):
            # line: 1731
            return self.root
        # line: 1732
        path_components = self.GetPathComponents(file_path)
        # line: 1733
        target_object = self.root
        # line: 1734
        try:
            # line: 1735
            for component in path_components:
                # line: 1736
                if stat.S_ISLNK(target_object.st_mode):
                    # line: 1737
                    target_object = self.ResolveObject(target_object.contents)
                # line: 1738
                if (not stat.S_ISDIR(target_object.st_mode)):
                    # line: 1739
                    if (not self.is_windows_fs):
                        # line: 1740
                        raise IOError(errno.ENOTDIR, 'Not a directory in fake filesystem', file_path)
                    # line: 1743
                    raise IOError(errno.ENOENT, 'No such file or directory in fake filesystem', file_path)
                # line: 1746
                target_object = target_object.GetEntry(component)
        # line: 1747
        except KeyError:
            # line: 1748
            raise IOError(errno.ENOENT, 'No such file or directory in fake filesystem', file_path)
        # line: 1751
        return target_object

    # line: 1753
    def GetObject(self, file_path):
        # line: 1764
        'Search for the specified filesystem object within the fake filesystem.\n\n        Args:\n          file_path: specifies target FakeFile object to retrieve.\n\n        Returns:\n          the FakeFile object corresponding to file_path.\n\n        Raises:\n          IOError: if the object is not found.\n        '
        # line: 1765
        if (sys.version_info >= (3, 6)):
            # line: 1766
            file_path = os.fspath(file_path)
        # line: 1767
        file_path = self.NormalizePath(self.NormalizeCase(file_path))
        # line: 1768
        return self.GetObjectFromNormalizedPath(file_path)

    # line: 1770
    def ResolveObject(self, file_path, follow_symlinks=True, allow_fd=False):
        # line: 1784
        'Search for the specified filesystem object, resolving all links.\n\n        Args:\n            file_path: Specifies target FakeFile object to retrieve.\n            follow_symlinks: If `False`, the link itself is resolved,\n                otherwise the object linked to.\n            allow_fd: If `True`, `file_path` may be open file descriptor\n\n        Returns:\n          the FakeFile object corresponding to file_path.\n\n        Raises:\n          IOError: if the object is not found.\n        '
        # line: 1785
        if (allow_fd and (sys.version_info >= (3, 3)) and isinstance(file_path, int)):
            # line: 1786
            return self.GetOpenFile(file_path).GetObject()
        # line: 1788
        if follow_symlinks:
            # line: 1789
            if (sys.version_info >= (3, 6)):
                # line: 1790
                file_path = os.fspath(file_path)
            # line: 1791
            return self.GetObjectFromNormalizedPath(self.ResolvePath(file_path))
        # line: 1792
        return self.LResolveObject(file_path)

    # line: 1794
    def LResolveObject(self, path):
        # line: 1808
        'Search for the specified object, resolving only parent links.\n\n        This is analogous to the stat/lstat difference.  This resolves links *to*\n        the object but not of the final object itself.\n\n        Args:\n          path: specifies target FakeFile object to retrieve.\n\n        Returns:\n          the FakeFile object corresponding to path.\n\n        Raises:\n          IOError: if the object is not found.\n        '
        # line: 1809
        if (sys.version_info >= (3, 6)):
            # line: 1810
            path = os.fspath(path)
        # line: 1811
        if (path == self.root.name):
            # line: 1813
            return self.root
        # line: 1816
        sep = self._path_separator(path)
        # line: 1817
        alt_sep = self._alternative_path_separator(path)
        # line: 1818
        if (path.endswith(sep) or (alt_sep and path.endswith(alt_sep))):
            # line: 1819
            path = path[:(-1)]
        # line: 1821
        (parent_directory, child_name) = self.SplitPath(path)
        # line: 1822
        if (not parent_directory):
            # line: 1823
            parent_directory = self.cwd
        # line: 1824
        try:
            # line: 1825
            parent_obj = self.ResolveObject(parent_directory)
            # line: 1826
            assert parent_obj
            # line: 1827
            if (not isinstance(parent_obj, FakeDirectory)):
                # line: 1828
                if ((not self.is_windows_fs) and isinstance(parent_obj, FakeFile)):
                    # line: 1829
                    raise IOError(errno.ENOTDIR, 'The parent object is not a directory', path)
                # line: 1831
                raise IOError(errno.ENOENT, 'No such file or directory in fake filesystem', path)
            # line: 1834
            return parent_obj.GetEntry(child_name)
        # line: 1835
        except KeyError:
            # line: 1836
            raise IOError(errno.ENOENT, 'No such file or directory in the fake filesystem', path)

    # line: 1840
    def AddObject(self, file_path, file_object, error_class=OSError):
        # line: 1851
        'Add a fake file or directory into the filesystem at file_path.\n\n        Args:\n          file_path: the path to the file to be added relative to self.\n          file_object: file or directory to add.\n          error_class: the error class to be thrown if file_path does\n            not correspond to a directory (used internally(\n\n        Raises:\n          IOError or OSError: if file_path does not correspond to a directory.\n        '
        # line: 1852
        if (not file_path):
            # line: 1853
            target_directory = self.root
        else:
            # line: 1855
            target_directory = self.ResolveObject(file_path)
            # line: 1856
            if (not stat.S_ISDIR(target_directory.st_mode)):
                # line: 1857
                raise error_class(errno.ENOTDIR, 'Not a directory in the fake filesystem', file_path)
        # line: 1860
        target_directory.AddEntry(file_object)

    # line: 1862
    def RenameObject(self, old_file_path, new_file_path, force_replace=False):
        # line: 1883
        'Renames a FakeFile object at old_file_path to new_file_path, preserving all properties.\n\n        Args:\n            old_file_path: Path to filesystem object to rename.\n            new_file_path: Path to where the filesystem object will live after this call.\n            force_replace: If set and destination is an existing file, it will be replaced\n                     even under Windows if the user has permissions, otherwise replacement\n                     happens under Unix only.\n\n        Raises:\n            OSError: if old_file_path does not exist.\n            OSError: if new_file_path is an existing directory\n                (Windows, or Posix if old_file_path points to a regular file)\n            OSError: if old_file_path is a directory and new_file_path a file\n            OSError: if new_file_path is an existing file and force_replace not set\n                (Windows only).\n            OSError: if new_file_path is an existing file and could not be removed\n                (Posix, or Windows with force_replace set).\n            OSError: if dirname(new_file_path) does not exist.\n            OSError: if the file would be moved to another filesystem (e.g. mount point).\n        '
        # line: 1884
        old_file_path = self.NormalizePath(old_file_path)
        # line: 1885
        new_file_path = self.NormalizePath(new_file_path)
        # line: 1886
        if ((not self.Exists(old_file_path)) and (not self.IsLink(old_file_path))):
            # line: 1887
            raise OSError(errno.ENOENT, 'Fake filesystem object: can not rename nonexistent file', old_file_path)
        # line: 1891
        old_object = self.LResolveObject(old_file_path)
        # line: 1892
        if (not self.is_windows_fs):
            # line: 1893
            if (self.IsDir(old_file_path, follow_symlinks=False) and self.IsLink(new_file_path)):
                # line: 1895
                raise OSError(errno.ENOTDIR, 'Cannot rename directory to symlink', new_file_path)
            # line: 1898
            if (self.IsDir(new_file_path, follow_symlinks=False) and self.IsLink(old_file_path)):
                # line: 1900
                raise OSError(errno.EISDIR, 'Cannot rename symlink to directory', new_file_path)
        # line: 1904
        if (self.Exists(new_file_path) or self.IsLink(new_file_path)):
            # line: 1905
            if (old_file_path == new_file_path):
                # line: 1906
                return
            # line: 1908
            new_object = self.GetObject(new_file_path)
            # line: 1909
            if (old_object == new_object):
                # line: 1910
                if (old_file_path.lower() == new_file_path.lower()):
                    # line: 1912
                    pass
                else:
                    # line: 1915
                    return
            elif (stat.S_ISDIR(new_object.st_mode) or stat.S_ISLNK(new_object.st_mode)):
                # line: 1918
                if self.is_windows_fs:
                    # line: 1919
                    if force_replace:
                        # line: 1920
                        raise OSError(errno.EACCES, 'Fake filesystem object: can not replace existing directory', new_file_path)
                    else:
                        # line: 1924
                        raise OSError(errno.EEXIST, 'Fake filesystem object: can not rename to existing directory', new_file_path)
                # line: 1927
                if (not stat.S_ISLNK(new_object.st_mode)):
                    # line: 1928
                    if new_object.contents:
                        # line: 1929
                        raise OSError(errno.EEXIST, 'Fake filesystem object: can not rename to non-empty directory', new_file_path)
                    # line: 1932
                    if stat.S_ISREG(old_object.st_mode):
                        # line: 1933
                        raise OSError(errno.EISDIR, 'Fake filesystem object: cannot rename file to directory', new_file_path)
            elif stat.S_ISDIR(old_object.st_mode):
                # line: 1937
                raise OSError(errno.ENOTDIR, 'Fake filesystem object: cannot rename directory to file', new_file_path)
            elif (self.is_windows_fs and (not force_replace)):
                # line: 1941
                raise OSError(errno.EEXIST, 'Fake filesystem object: can not rename to existing file', new_file_path)
            else:
                # line: 1945
                try:
                    # line: 1946
                    self.RemoveObject(new_file_path)
                # line: 1947
                except IOError as exc:
                    # line: 1948
                    raise OSError(exc.errno, exc.strerror, exc.filename)
        # line: 1950
        (old_dir, old_name) = self.SplitPath(old_file_path)
        # line: 1951
        (new_dir, new_name) = self.SplitPath(new_file_path)
        # line: 1952
        if (not self.Exists(new_dir)):
            # line: 1953
            raise OSError(errno.ENOENT, 'No such fake directory', new_dir)
        # line: 1954
        old_dir_object = self.ResolveObject(old_dir)
        # line: 1955
        new_dir_object = self.ResolveObject(new_dir)
        # line: 1956
        if (old_dir_object.st_dev != new_dir_object.st_dev):
            # line: 1957
            raise OSError(errno.EXDEV, 'Fake filesystem object: cannot rename across file systems', old_file_path)
        # line: 1960
        if (not stat.S_ISDIR(new_dir_object.st_mode)):
            # line: 1961
            raise OSError((errno.EACCES if self.is_windows_fs else errno.ENOTDIR), 'Fake filesystem object: target parent is not a directory', new_file_path)
        # line: 1964
        if new_dir_object.HasParentObject(old_object):
            # line: 1965
            raise OSError(errno.EINVAL, 'Fake filesystem object: invalid target for rename', new_file_path)
        # line: 1969
        object_to_rename = old_dir_object.GetEntry(old_name)
        # line: 1970
        old_dir_object.RemoveEntry(old_name, recursive=False)
        # line: 1971
        object_to_rename.name = new_name
        # line: 1972
        if (new_name in new_dir_object.contents):
            # line: 1974
            new_dir_object.RemoveEntry(new_name)
        # line: 1975
        new_dir_object.AddEntry(object_to_rename)

    # line: 1977
    def RemoveObject(self, file_path):
        # line: 1987
        "Remove an existing file or directory.\n\n        Args:\n          file_path: the path to the file relative to self.\n\n        Raises:\n          IOError: if file_path does not correspond to an existing file, or if part\n            of the path refers to something other than a directory.\n          OSError: if the directory is in use (eg, if it is '/').\n        "
        # line: 1988
        file_path = self.NormalizePath(self.NormalizeCase(file_path))
        # line: 1989
        if self._IsRootPath(file_path):
            # line: 1990
            raise OSError(errno.EBUSY, 'Fake device or resource busy', file_path)
        # line: 1992
        try:
            # line: 1993
            (dirname, basename) = self.SplitPath(file_path)
            # line: 1994
            target_directory = self.ResolveObject(dirname)
            # line: 1995
            target_directory.RemoveEntry(basename)
        # line: 1996
        except KeyError:
            # line: 1997
            raise IOError(errno.ENOENT, 'No such file or directory in the fake filesystem', file_path)
        # line: 2000
        except AttributeError:
            # line: 2001
            raise IOError(errno.ENOTDIR, 'Not a directory in the fake filesystem', file_path)

    # line: 2005
    def CreateDirectory(self, directory_path, perm_bits=PERM_DEF):
        # line: 2019
        'Create directory_path, and all the parent directories.\n\n        Helper method to set up your test faster.\n\n        Args:\n            directory_path:  The full directory path to create.\n            perm_bits: The permission bits as set by `chmod`.\n\n        Returns:\n            the newly created FakeDirectory object.\n\n        Raises:\n            OSError:  if the directory already exists.\n        '
        # line: 2020
        directory_path = self.NormalizePath(directory_path)
        # line: 2021
        self._AutoMountDriveIfNeeded(directory_path)
        # line: 2022
        if self.Exists(directory_path):
            # line: 2023
            raise OSError(errno.EEXIST, 'Directory exists in fake filesystem', directory_path)
        # line: 2026
        path_components = self.GetPathComponents(directory_path)
        # line: 2027
        current_dir = self.root
        # line: 2029
        new_dirs = []
        # line: 2030
        for component in path_components:
            # line: 2031
            directory = self._DirectoryContent(current_dir, component)[1]
            # line: 2032
            if (not directory):
                # line: 2033
                new_dir = FakeDirectory(component, filesystem=self)
                # line: 2034
                new_dirs.append(new_dir)
                # line: 2035
                current_dir.AddEntry(new_dir)
                # line: 2036
                current_dir = new_dir
            else:
                # line: 2038
                if stat.S_ISLNK(directory.st_mode):
                    # line: 2039
                    directory = self.ResolveObject(directory.contents)
                # line: 2040
                current_dir = directory
                # line: 2041
                if ((directory.st_mode & stat.S_IFDIR) != stat.S_IFDIR):
                    # line: 2042
                    raise OSError(errno.ENOTDIR, 'Not a directory', current_dir.GetPath())
        # line: 2046
        for new_dir in new_dirs:
            # line: 2047
            new_dir.st_mode = (stat.S_IFDIR | perm_bits)
        # line: 2049
        self._last_ino += 1
        # line: 2050
        current_dir.SetIno(self._last_ino)
        # line: 2051
        return current_dir

    # line: 2053
    def CreateFile(self, file_path, st_mode=(stat.S_IFREG | PERM_DEF_FILE), contents='', st_size=None, create_missing_dirs=True, apply_umask=False, encoding=None, errors=None):
        # line: 2079
        'Create file_path, including all the parent directories along the way.\n\n        This helper method can be used to set up tests more easily.\n\n        Args:\n            file_path: The path to the file to create.\n            st_mode: The stat constant representing the file type.\n            contents: The contents of the file.\n            st_size: The file size; only valid if contents not given.\n            create_missing_dirs: If `True`, auto create missing directories.\n            apply_umask: `True` if the current umask must be applied on st_mode.\n            encoding: Ff contents is a unicode string, the encoding used\n                for serialization.\n                New in pyfakefs 2.9.\n            errors: The error mode used for encoding/decoding errors.\n                New in pyfakefs 3.2.\n\n        Returns:\n            the newly created FakeFile object.\n\n        Raises:\n            IOError: if the file already exists.\n            IOError: if the containing directory is required and missing.\n        '
        # line: 2080
        return self.CreateFileInternally(file_path, st_mode, contents, st_size, create_missing_dirs, apply_umask, encoding, errors)

    # line: 2084
    def add_real_file(self, file_path, read_only=True):
        # line: 2109
        "Create file_path, including all the parent directories along the way, for an existing\n        real file.  The contents of the real file are read only on demand.\n        New in pyfakefs 3.2.\n\n        Args:\n            file_path: Path to an existing file in the real file system\n            read_only: If `True` (the default), writing to the fake file\n                raises an exception.  Otherwise, writing to the file changes\n                the fake file only.\n\n        Returns:\n            the newly created FakeFile object.\n\n        Raises:\n            OSError: if the file does not exist in the real file system.\n            IOError: if the file already exists in the fake file system.\n\n        .. note:: On MacOS and BSD, accessing the fake file's contents will update                   both the real and fake files' `atime.` (access time).  In this                   particular case, `add_real_file()` violates the rule that `pyfakefs`                   must not modify the real file system.                                     Further, Windows offers the option to enable atime, and older                   versions of Linux may also modify atime.\n        "
        # line: 2110
        return self.CreateFileInternally(file_path, read_from_real_fs=True, read_only=read_only)

    # line: 2114
    def add_real_directory(self, dir_path, read_only=True, lazy_read=True):
        # line: 2139
        'Create a fake directory corresponding to the real directory at the specified\n        path.  Add entries in the fake directory corresponding to the entries in the\n        real directory.\n        New in pyfakefs 3.2.\n\n        Args:\n            dir_path: The path to the existing directory.\n            read_only: If set, all files under the directory are treated as\n                read-only, e.g. a write access raises an exception;\n                otherwise, writing to the files changes the fake files only\n                as usually.\n            lazy_read: If set (default), directory contents are only read when\n                accessed, and only until the needed subdirectory level.\n                *Note:* this means that the file system size is only updated\n                at the time the directory contents are read; set this to\n                `False` only if you are dependent on accurate file system\n                size in your test\n\n        Returns:\n            the newly created FakeDirectory object.\n\n        Raises:\n            OSError: if the directory does not exist in the real file system.\n            IOError: if the directory already exists in the fake file system.\n        '
        # line: 2140
        if (not os.path.exists(dir_path)):
            # line: 2141
            raise IOError(errno.ENOENT, 'No such directory', dir_path)
        # line: 2142
        if lazy_read:
            # line: 2143
            parent_path = os.path.split(dir_path)[0]
            # line: 2144
            if self.Exists(parent_path):
                # line: 2145
                parent_dir = self.GetObject(parent_path)
            else:
                # line: 2147
                parent_dir = self.CreateDirectory(parent_path)
            # line: 2148
            new_dir = FakeDirectoryFromRealDirectory(dir_path, filesystem=self, read_only=read_only)
            # line: 2149
            parent_dir.AddEntry(new_dir)
            # line: 2150
            self._last_ino += 1
            # line: 2151
            new_dir.SetIno(self._last_ino)
        else:
            # line: 2153
            new_dir = self.CreateDirectory(dir_path)
            # line: 2154
            for (base, _, files) in os.walk(dir_path):
                # line: 2155
                for fileEntry in files:
                    # line: 2156
                    self.add_real_file(os.path.join(base, fileEntry), read_only)
        # line: 2157
        return new_dir

    # line: 2159
    def add_real_paths(self, path_list, read_only=True, lazy_dir_read=True):
        # line: 2176
        'This convenience method adds multiple files and/or directories from the\n        real file system to the fake file system. See `add_real_file()` and\n        `add_real_directory()`.\n        New in pyfakefs 3.2.\n\n        Args:\n            path_list: List of file and directory paths in the real file system.\n            read_only: If set, all files and files under under the directories are treated as read-only,\n                e.g. a write access raises an exception;\n                otherwise, writing to the files changes the fake files only as usually.\n            lazy_dir_read: Uses lazy reading of directory contents if set\n                (see `add_real_directory`)\n\n        Raises:\n            OSError: if any of the files and directories in the list does not exist in the real file system.\n            OSError: if any of the files and directories in the list already exists in the fake file system.\n        '
        # line: 2177
        for path in path_list:
            # line: 2178
            if os.path.isdir(path):
                # line: 2179
                self.add_real_directory(path, read_only, lazy_dir_read)
            else:
                # line: 2181
                self.add_real_file(path, read_only)

    # line: 2183
    def CreateFileInternally(self, file_path, st_mode=(stat.S_IFREG | PERM_DEF_FILE), contents='', st_size=None, create_missing_dirs=True, apply_umask=False, encoding=None, errors=None, read_from_real_fs=False, read_only=True, raw_io=False):
        # line: 2203
        'Internal fake file creator that supports both normal fake files and fake\n        files based on real files.\n\n        Args:\n            file_path: path to the file to create.\n            st_mode: the stat.S_IF constant representing the file type.\n            contents: the contents of the file.\n            st_size: file size; only valid if contents not given.\n            create_missing_dirs: if True, auto create missing directories.\n            apply_umask: whether or not the current umask must be applied on st_mode.\n            encoding: if contents is a unicode string, the encoding used for serialization.\n            errors: the error mode used for encoding/decoding errors\n            read_from_real_fs: if True, the contents are reaf from the real file system on demand.\n            read_only: if set, the file is treated as read-only, e.g. a write access raises an exception;\n                otherwise, writing to the file changes the fake file only as usually.\n            raw_io: `True` if called from low-level API (`os.open`)\n        '
        # line: 2204
        error_class = (OSError if raw_io else IOError)
        # line: 2205
        file_path = self.NormalizePath(file_path)
        # line: 2208
        if (self.Exists(file_path) or self.IsLink(file_path)):
            # line: 2209
            raise OSError(errno.EEXIST, 'File already exists in fake filesystem', file_path)
        # line: 2212
        (parent_directory, new_file) = self.SplitPath(file_path)
        # line: 2213
        if (not parent_directory):
            # line: 2214
            parent_directory = self.cwd
        # line: 2215
        self._AutoMountDriveIfNeeded(parent_directory)
        # line: 2216
        if (not self.Exists(parent_directory)):
            # line: 2217
            if (not create_missing_dirs):
                # line: 2218
                raise error_class(errno.ENOENT, 'No such fake directory', parent_directory)
            # line: 2219
            self.CreateDirectory(parent_directory)
        else:
            # line: 2221
            parent_directory = self.NormalizeCase(parent_directory)
        # line: 2222
        if apply_umask:
            # line: 2223
            st_mode &= (~ self.umask)
        # line: 2224
        if read_from_real_fs:
            # line: 2225
            file_object = FakeFileFromRealFile(file_path, filesystem=self, read_only=read_only)
        else:
            # line: 2227
            file_object = FakeFile(new_file, st_mode, filesystem=self, encoding=encoding, errors=errors)
        # line: 2229
        self._last_ino += 1
        # line: 2230
        file_object.SetIno(self._last_ino)
        # line: 2231
        self.AddObject(parent_directory, file_object, error_class)
        # line: 2233
        if ((not read_from_real_fs) and ((contents is not None) or (st_size is not None))):
            # line: 2234
            try:
                # line: 2235
                if (st_size is not None):
                    # line: 2236
                    file_object.SetLargeFileSize(st_size)
                else:
                    # line: 2238
                    file_object._set_initial_contents(contents)
            # line: 2239
            except IOError:
                # line: 2240
                self.RemoveObject(file_path)
                # line: 2241
                raise
        # line: 2243
        return file_object

    # line: 2246
    def CreateLink(self, file_path, link_target, create_missing_dirs=True):
        # line: 2261
        'Create the specified symlink, pointed at the specified link target.\n\n        Args:\n            file_path:  path to the symlink to create\n            link_target:  the target of the symlink\n            create_missing_dirs: If `True`, any missing parent directories of\n                file_path will be created\n\n        Returns:\n          the newly created FakeFile object.\n\n        Raises:\n          OSError:  if the symlink could not be created (see `CreateFile`).\n          OSError:  if on Windows before Python 3.2.\n        '
        # line: 2262
        if (not self._IsLinkSupported()):
            # line: 2263
            raise OSError('Symbolic links are not supported on Windows before Python 3.2')
        # line: 2265
        if (not self.IsLink(file_path)):
            # line: 2266
            file_path = self.ResolvePath(file_path)
        # line: 2267
        if (sys.version_info >= (3, 6)):
            # line: 2268
            link_target = os.fspath(link_target)
        # line: 2269
        return self.CreateFileInternally(file_path, st_mode=(stat.S_IFLNK | PERM_DEF), contents=link_target, create_missing_dirs=create_missing_dirs, raw_io=True)

    # line: 2273
    def CreateHardLink(self, old_path, new_path):
        # line: 2289
        "Create a hard link at new_path, pointing at old_path.\n        New in pyfakefs 2.9.\n\n        Args:\n          old_path: an existing link to the target file.\n          new_path: the destination path to create a new link at.\n\n        Returns:\n          the FakeFile object referred to by old_path.\n\n        Raises:\n          OSError:  if something already exists at new_path.\n          OSError:  if old_path is a directory.\n          OSError:  if the parent directory doesn't exist.\n          OSError:  if on Windows before Python 3.2.\n        "
        # line: 2290
        if (not self._IsLinkSupported()):
            # line: 2291
            raise OSError('Links are not supported on Windows before Python 3.2')
        # line: 2292
        new_path_normalized = self.NormalizePath(new_path)
        # line: 2293
        if self.Exists(new_path_normalized):
            # line: 2294
            raise OSError(errno.EEXIST, 'File already exists in fake filesystem', new_path)
        # line: 2298
        (new_parent_directory, new_basename) = self.SplitPath(new_path_normalized)
        # line: 2299
        if (not new_parent_directory):
            # line: 2300
            new_parent_directory = self.cwd
        # line: 2302
        if (not self.Exists(new_parent_directory)):
            # line: 2303
            raise OSError(errno.ENOENT, 'No such fake directory', new_parent_directory)
        # line: 2307
        try:
            # line: 2308
            old_file = self.ResolveObject(old_path)
        # line: 2309
        except:
            # line: 2310
            raise OSError(errno.ENOENT, 'No such file or directory in fake filesystem', old_path)
        # line: 2314
        if (old_file.st_mode & stat.S_IFDIR):
            # line: 2315
            raise OSError((errno.EACCES if self.is_windows_fs else errno.EPERM), 'Cannot create hard link to directory', old_path)
        # line: 2320
        old_file.name = new_basename
        # line: 2321
        self.AddObject(new_parent_directory, old_file)
        # line: 2322
        return old_file

    # line: 2324
    def ReadLink(self, path):
        # line: 2338
        'Read the target of a symlink.\n        New in pyfakefs 3.0.\n\n        Args:\n          path:  symlink to read the target of.\n\n        Returns:\n          the string representing the path to which the symbolic link points.\n\n        Raises:\n          TypeError: if path is None\n          OSError: (with errno=ENOENT) if path is not a valid path, or\n                   (with errno=EINVAL) if path is valid, but is not a symlink.\n        '
        # line: 2339
        if (path is None):
            # line: 2340
            raise TypeError
        # line: 2341
        try:
            # line: 2342
            link_obj = self.LResolveObject(path)
        # line: 2343
        except IOError as exc:
            # line: 2344
            raise OSError(exc.errno, 'Fake path does not exist', path)
        # line: 2345
        if (stat.S_IFMT(link_obj.st_mode) != stat.S_IFLNK):
            # line: 2346
            raise OSError(errno.EINVAL, 'Fake filesystem: not a symlink', path)
        # line: 2347
        return link_obj.contents

    # line: 2349
    def MakeDirectory(self, dir_name, mode=PERM_DEF):
        # line: 2362
        "Create a leaf Fake directory.\n        New in pyfakefs 3.0.\n\n        Args:\n          dir_name: (str) Name of directory to create.  Relative paths are assumed\n            to be relative to '/'.\n          mode: (int) Mode to create directory with.  This argument defaults to\n            0o777.  The umask is applied to this mode.\n\n        Raises:\n          OSError: if the directory name is invalid or parent directory is read only\n          or as per `FakeFilesystem.AddObject()`.\n        "
        # line: 2363
        if (sys.version_info >= (3, 6)):
            # line: 2364
            dir_name = os.fspath(dir_name)
        # line: 2365
        if self._EndsWithPathSeparator(dir_name):
            # line: 2366
            dir_name = dir_name[:(-1)]
        # line: 2367
        if (not dir_name):
            # line: 2368
            raise OSError(errno.ENOENT, 'Empty directory name')
        # line: 2370
        (parent_dir, _) = self.SplitPath(dir_name)
        # line: 2371
        if parent_dir:
            # line: 2372
            base_dir = self.CollapsePath(parent_dir)
            # line: 2373
            ellipsis = self._matching_string(parent_dir, (self.path_separator + '..'))
            # line: 2374
            if parent_dir.endswith(ellipsis):
                # line: 2375
                (base_dir, dummy_dotdot, _) = parent_dir.partition(ellipsis)
            # line: 2376
            if (not self.Exists(base_dir)):
                # line: 2377
                raise OSError(errno.ENOENT, 'No such fake directory', base_dir)
        # line: 2379
        dir_name = self.NormalizePath(dir_name)
        # line: 2380
        if self.Exists(dir_name):
            # line: 2381
            raise OSError(errno.EEXIST, 'Fake object already exists', dir_name)
        # line: 2382
        (head, tail) = self.SplitPath(dir_name)
        # line: 2384
        self.AddObject(head, FakeDirectory(tail, (mode & (~ self.umask)), filesystem=self))

    # line: 2387
    def MakeDirectories(self, dir_name, mode=PERM_DEF, exist_ok=False):
        # line: 2402
        'Create a leaf Fake directory and create any non-existent parent dirs.\n        New in pyfakefs 3.0.\n\n        Args:\n          dir_name: (str) Name of directory to create.\n          mode: (int) Mode to create directory (and any necessary parent\n            directories) with. This argument defaults to 0o777.  The umask is\n            applied to this mode.\n          exist_ok: (boolean) If exist_ok is False (the default), an OSError is\n            raised if the target directory already exists.  New in Python 3.2.\n\n        Raises:\n          OSError: if the directory already exists and exist_ok=False, or as per\n          `FakeFilesystem.CreateDirectory()`.\n        '
        # line: 2403
        dir_name = self.NormalizePath(dir_name)
        # line: 2404
        path_components = self.GetPathComponents(dir_name)
        # line: 2408
        current_dir = self.root
        # line: 2409
        for component in path_components:
            # line: 2410
            if ((component not in current_dir.contents) or (not isinstance(current_dir.contents, dict))):
                # line: 2412
                break
            else:
                # line: 2414
                current_dir = current_dir.contents[component]
        # line: 2415
        try:
            # line: 2416
            self.CreateDirectory(dir_name, (mode & (~ self.umask)))
        # line: 2417
        except (IOError, OSError) as e:
            # line: 2418
            if ((not exist_ok) or (not isinstance(self.ResolveObject(dir_name), FakeDirectory))):
                # line: 2420
                if isinstance(e, OSError):
                    # line: 2421
                    raise
                # line: 2422
                raise OSError(e.errno, e.strerror, e.filename)

    # line: 2424
    def _IsType(self, path, st_flag, follow_symlinks=True):
        # line: 2438
        "Helper function to implement isdir(), islink(), etc.\n\n        See the stat(2) man page for valid stat.S_I* flag values\n\n        Args:\n          path:  path to file to stat and test\n          st_flag:  the stat.S_I* flag checked for the file's st_mode\n\n        Returns:\n          boolean (the st_flag is set in path's st_mode)\n\n        Raises:\n          TypeError: if path is None\n        "
        # line: 2439
        if (sys.version_info >= (3, 6)):
            # line: 2440
            path = os.fspath(path)
        # line: 2441
        if (path is None):
            # line: 2442
            raise TypeError
        # line: 2443
        try:
            # line: 2444
            obj = self.ResolveObject(path, follow_symlinks)
            # line: 2445
            if obj:
                # line: 2446
                return (stat.S_IFMT(obj.st_mode) == st_flag)
        # line: 2447
        except (IOError, OSError):
            # line: 2448
            return False
        # line: 2449
        return False

    # line: 2451
    def IsDir(self, path, follow_symlinks=True):
        # line: 2463
        'Determine if path identifies a directory.\n        New in pyfakefs 3.0.\n\n        Args:\n          path: path to filesystem object.\n\n        Returns:\n          True if path points to a directory (following symlinks).\n\n        Raises:\n          TypeError: if path is None.\n        '
        # line: 2464
        return self._IsType(path, stat.S_IFDIR, follow_symlinks)

    # line: 2466
    def IsFile(self, path, follow_symlinks=True):
        # line: 2478
        'Determine if path identifies a regular file.\n        New in pyfakefs 3.0.\n\n        Args:\n          path: path to filesystem object.\n\n        Returns:\n          True if path points to a regular file (following symlinks).\n\n        Raises:\n          TypeError: if path is None.\n        '
        # line: 2479
        return self._IsType(path, stat.S_IFREG, follow_symlinks)

    # line: 2481
    def IsLink(self, path):
        # line: 2493
        'Determine if path identifies a symbolic link.\n        New in pyfakefs 3.0.\n\n        Args:\n          path: path to filesystem object.\n\n        Returns:\n          True if path points to a symlink (S_IFLNK set in st_mode)\n\n        Raises:\n          TypeError: if path is None.\n        '
        # line: 2494
        return self._IsType(path, stat.S_IFLNK, follow_symlinks=False)

    # line: 2496
    def ConfirmDir(self, target_directory):
        # line: 2508
        'Test that the target is actually a directory, raising OSError if not.\n        New in pyfakefs 3.0.\n\n        Args:\n          target_directory:  path to the target directory within the fake filesystem.\n\n        Returns:\n          the FakeDirectory object corresponding to target_directory.\n\n        Raises:\n          OSError:  if the target is not a directory.\n        '
        # line: 2509
        try:
            # line: 2510
            directory = self.ResolveObject(target_directory)
        # line: 2511
        except IOError as exc:
            # line: 2512
            raise OSError(exc.errno, exc.strerror, target_directory)
        # line: 2513
        if (not (directory.st_mode & stat.S_IFDIR)):
            # line: 2514
            raise OSError(errno.ENOTDIR, 'Fake os module: not a directory', target_directory)
        # line: 2517
        return directory

    # line: 2519
    def RemoveFile(self, path):
        # line: 2530
        'Remove the FakeFile object at the specified file path.\n        New in pyfakefs 3.0.\n\n        Args:\n          path:  path to file to be removed.\n\n        Raises:\n          OSError: if path points to a directory.\n          OSError: if path does not exist.\n          OSError: if removal failed.\n        '
        # line: 2531
        path = self.NormalizePath(path)
        # line: 2532
        if self.Exists(path):
            # line: 2533
            obj = self.ResolveObject(path)
            # line: 2534
            if (stat.S_IFMT(obj.st_mode) == stat.S_IFDIR):
                # line: 2535
                link_obj = self.LResolveObject(path)
                # line: 2536
                if (stat.S_IFMT(link_obj.st_mode) != stat.S_IFLNK):
                    # line: 2537
                    raise OSError(errno.EISDIR, ("Is a directory: '%s'" % path))
        # line: 2539
        try:
            # line: 2540
            self.RemoveObject(path)
        # line: 2541
        except IOError as exc:
            # line: 2542
            raise OSError(exc.errno, exc.strerror, exc.filename)

    # line: 2544
    def RemoveDirectory(self, target_directory, allow_symlink=False):
        # line: 2557
        "Remove a leaf Fake directory.\n        New in pyfakefs 3.0.\n\n        Args:\n            target_directory: (str) Name of directory to remove.\n            allow_symlink: (bool) if `target_directory` is a symlink,\n                the function just returns, otherwise it raises (Posix only)\n\n        Raises:\n          OSError: if target_directory does not exist.\n          OSError: if target_directory does not point to a directory.\n          OSError: if removal failed per FakeFilesystem.RemoveObject. Cannot remove '.'.\n        "
        # line: 2558
        if (target_directory in ('.', u'.')):
            # line: 2559
            raise OSError(errno.EINVAL, "Invalid argument: '.'")
        # line: 2560
        target_directory = self.NormalizePath(target_directory)
        # line: 2561
        if self.ConfirmDir(target_directory):
            # line: 2562
            if ((not self.is_windows_fs) and self.IsLink(target_directory)):
                # line: 2563
                if allow_symlink:
                    # line: 2564
                    return
                # line: 2565
                raise OSError(errno.ENOTDIR, 'Cannot remove symlink', target_directory)
            # line: 2567
            dir_object = self.ResolveObject(target_directory)
            # line: 2568
            if dir_object.contents:
                # line: 2569
                raise OSError(errno.ENOTEMPTY, 'Fake Directory not empty', target_directory)
            # line: 2571
            try:
                # line: 2572
                self.RemoveObject(target_directory)
            # line: 2573
            except IOError as exc:
                # line: 2574
                raise OSError(exc.errno, exc.strerror, exc.filename)

    # line: 2576
    def ListDir(self, target_directory):
        # line: 2588
        'Return a list of file names in target_directory.\n        New in pyfakefs 3.0.\n\n        Args:\n          target_directory:  path to the target directory within the fake filesystem.\n\n        Returns:\n          a list of file names within the target directory in arbitrary order.\n\n        Raises:\n          OSError:  if the target is not a directory.\n        '
        # line: 2589
        target_directory = self.ResolvePath(target_directory, allow_fd=True)
        # line: 2590
        directory = self.ConfirmDir(target_directory)
        # line: 2591
        directory_contents = directory.contents
        # line: 2592
        return list(directory_contents.keys())
    # line: 2594
    if (sys.version_info >= (3, 5)):


        # line: 2595
        class DirEntry:
            # line: 2596
            'Emulates os.DirEntry. Note that we did not enforce keyword only arguments.'

            # line: 2598
            def __init__(self, filesystem):
                # line: 2603
                'Initialize the dir entry with unset values.\n\n                Args:\n                    filesystem: the fake filesystem used for implementation.\n                '
                # line: 2604
                self._filesystem = filesystem
                # line: 2605
                self.name = ''
                # line: 2606
                self.path = ''
                # line: 2607
                self._inode = None
                # line: 2608
                self._islink = False
                # line: 2609
                self._isdir = False
                # line: 2610
                self._statresult = None
                # line: 2611
                self._statresult_symlink = None

            # line: 2613
            def inode(self):
                # line: 2614
                'Return the inode number of the entry.'
                # line: 2615
                if (self._inode is None):
                    # line: 2616
                    self.stat(follow_symlinks=False)
                # line: 2617
                return self._inode

            # line: 2619
            def is_dir(self, follow_symlinks=True):
                # line: 2629
                'Return True if this entry is a directory entry.\n\n                Args:\n                    follow_symlinks: If True, also return True if this entry is a symlink\n                                    pointing to a directory.\n\n                Returns:\n                    True if this entry is an existing directory entry, or if\n                    follow_symlinks is set, and this entry points to an existing directory entry.\n                '
                # line: 2630
                return (self._isdir and (follow_symlinks or (not self._islink)))

            # line: 2632
            def is_file(self, follow_symlinks=True):
                # line: 2642
                'Return True if this entry is a regular file entry.\n\n                Args:\n                    follow_symlinks: If True, also return True if this entry is a symlink\n                                    pointing to a regular file.\n\n                Returns:\n                    True if this entry is an existing file entry, or if\n                    follow_symlinks is set, and this entry points to an existing file entry.\n                '
                # line: 2643
                return ((not self._isdir) and (follow_symlinks or (not self._islink)))

            # line: 2645
            def is_symlink(self):
                # line: 2646
                'Return True if this entry is a symbolic link (even if broken).'
                # line: 2647
                return self._islink

            # line: 2649
            def stat(self, follow_symlinks=True):
                # line: 2655
                'Return a stat_result object for this entry.\n\n                Args:\n                    follow_symlinks: If False and the entry is a symlink, return the\n                        result for the symlink, otherwise for the object it points to.\n                '
                # line: 2656
                if follow_symlinks:
                    # line: 2657
                    if (self._statresult_symlink is None):
                        # line: 2658
                        file_object = self._filesystem.ResolveObject(self.path)
                        # line: 2659
                        if self._filesystem.is_windows_fs:
                            # line: 2662
                            file_object.st_ino = 0
                            # line: 2663
                            file_object.st_dev = 0
                            # line: 2664
                            file_object.st_nlink = 0
                        # line: 2665
                        self._statresult_symlink = file_object.stat_result.copy()
                    # line: 2666
                    return self._statresult_symlink
                # line: 2668
                if (self._statresult is None):
                    # line: 2669
                    file_object = self._filesystem.LResolveObject(self.path)
                    # line: 2670
                    self._inode = file_object.st_ino
                    # line: 2671
                    if self._filesystem.is_windows_fs:
                        # line: 2672
                        file_object.st_ino = 0
                        # line: 2673
                        file_object.st_dev = 0
                        # line: 2674
                        file_object.st_nlink = 0
                    # line: 2675
                    self._statresult = file_object.stat_result.copy()
                # line: 2676
                return self._statresult


        # line: 2678
        class ScanDirIter:
            # line: 2681
            'Iterator for DirEntry objects returned from `scandir()` function.\n            New in pyfakefs 3.0.\n            '

            # line: 2683
            def __init__(self, filesystem, path):
                # line: 2684
                self.filesystem = filesystem
                # line: 2685
                self.path = self.filesystem.ResolvePath(path)
                # line: 2686
                contents = {}
                # line: 2687
                try:
                    # line: 2688
                    contents = self.filesystem.ConfirmDir(path).contents
                # line: 2689
                except OSError:
                    # line: 2690
                    pass
                # line: 2691
                self.contents_iter = iter(contents)

            # line: 2693
            def __iter__(self):
                # line: 2694
                return self

            # line: 2696
            def __next__(self):
                # line: 2697
                entry = self.contents_iter.__next__()
                # line: 2698
                dir_entry = self.filesystem.DirEntry(self.filesystem)
                # line: 2699
                dir_entry.name = entry
                # line: 2700
                dir_entry.path = self.filesystem.JoinPaths(self.path, dir_entry.name)
                # line: 2701
                dir_entry._isdir = self.filesystem.IsDir(dir_entry.path)
                # line: 2702
                dir_entry._islink = self.filesystem.IsLink(dir_entry.path)
                # line: 2703
                return dir_entry
            # line: 2705
            if (sys.version_info >= (3, 6)):

                # line: 2706
                def __enter__(self):
                    # line: 2707
                    return self

                # line: 2709
                def __exit__(self, exc_type, exc_val, exc_tb):
                    # line: 2710
                    self.close()

                # line: 2712
                def close(self):
                    # line: 2713
                    pass

        # line: 2715
        def ScanDir(self, path=''):
            # line: 2728
            'Return an iterator of DirEntry objects corresponding to the entries\n            in the directory given by path.\n            New in pyfakefs 3.0.\n\n            Args:\n              path: path to the target directory within the fake filesystem.\n\n            Returns:\n              an iterator to an unsorted list of os.DirEntry objects for each entry in path.\n\n            Raises:\n              OSError: if the target is not a directory.\n            '
            # line: 2729
            return self.ScanDirIter(self, path)

    # line: 2731
    def __str__(self):
        # line: 2732
        return str(self.root)


# line: 2735
class FakePathModule(object):
    # line: 2740
    'Faked os.path module replacement.\n\n    FakePathModule should *only* be instantiated by FakeOsModule.  See the\n    FakeOsModule docstring for details.\n    '
    # line: 2741
    _OS_PATH_COPY = CopyModule(os.path)

    # line: 2743
    def __init__(self, filesystem, os_module=None):
        # line: 2749
        'Init.\n\n        Args:\n          filesystem:  FakeFilesystem used to provide file system information\n          os_module: (deprecated) FakeOsModule to assign to self.os\n        '
        # line: 2750
        self.filesystem = filesystem
        # line: 2751
        self._os_path = self._OS_PATH_COPY
        # line: 2752
        if (os_module is None):
            # line: 2753
            warnings.warn(FAKE_PATH_MODULE_DEPRECATION, DeprecationWarning, stacklevel=2)
        # line: 2755
        self._os_path.os = self.os = os_module
        # line: 2756
        self.sep = self.filesystem.path_separator
        # line: 2757
        self.altsep = self.filesystem.alternative_path_separator

    # line: 2759
    def exists(self, path):
        # line: 2767
        'Determine whether the file object exists within the fake filesystem.\n\n        Args:\n          path:  path to the file object.\n\n        Returns:\n          bool (if file exists).\n        '
        # line: 2768
        return self.filesystem.Exists(path)

    # line: 2770
    def lexists(self, path):
        # line: 2778
        'Test whether a path exists.  Returns True for broken symbolic links.\n\n        Args:\n          path:  path to the symlink object.\n\n        Returns:\n          bool (if file exists).\n        '
        # line: 2779
        return (self.exists(path) or self.islink(path))

    # line: 2781
    def getsize(self, path):
        # line: 2789
        'Return the file object size in bytes.\n\n        Args:\n          path:  path to the file object.\n\n        Returns:\n          file size in bytes.\n        '
        # line: 2790
        try:
            # line: 2791
            file_obj = self.filesystem.ResolveObject(path)
            # line: 2792
            return file_obj.st_size
        # line: 2793
        except IOError as exc:
            # line: 2794
            raise os.error(exc.errno, exc.strerror)

    # line: 2796
    def isabs(self, path):
        # line: 2797
        'Return True if path is an absolute pathname.'
        # line: 2798
        if self.filesystem.is_windows_fs:
            # line: 2799
            path = self.splitdrive(path)[1]
        # line: 2800
        if (sys.version_info >= (3, 6)):
            # line: 2801
            path = os.fspath(path)
        # line: 2802
        sep = self.filesystem._path_separator(path)
        # line: 2803
        altsep = self.filesystem._alternative_path_separator(path)
        # line: 2804
        if self.filesystem.is_windows_fs:
            # line: 2805
            return ((len(path) > 0) and (path[:1] in (sep, altsep)))
        else:
            # line: 2807
            return (path.startswith(sep) or ((altsep is not None) and path.startswith(altsep)))

    # line: 2809
    def isdir(self, path):
        # line: 2810
        'Determine if path identifies a directory.'
        # line: 2811
        return self.filesystem.IsDir(path)

    # line: 2813
    def isfile(self, path):
        # line: 2814
        'Determine if path identifies a regular file.'
        # line: 2815
        return self.filesystem.IsFile(path)

    # line: 2817
    def islink(self, path):
        # line: 2828
        'Determine if path identifies a symbolic link.\n\n        Args:\n          path: path to filesystem object.\n\n        Returns:\n          True if path points to a symbolic link.\n\n        Raises:\n          TypeError: if path is None.\n        '
        # line: 2829
        return self.filesystem.IsLink(path)

    # line: 2831
    def getmtime(self, path):
        # line: 2843
        'Returns the modification time of the fake file.\n\n        Args:\n            path: the path to fake file.\n\n        Returns:\n            (int, float) the modification time of the fake file\n                         in number of seconds since the epoch.\n\n        Raises:\n            OSError: if the file does not exist.\n        '
        # line: 2844
        try:
            # line: 2845
            file_obj = self.filesystem.ResolveObject(path)
        # line: 2846
        except IOError as exc:
            # line: 2847
            raise OSError(errno.ENOENT, str(exc))
        # line: 2848
        return file_obj.st_mtime

    # line: 2850
    def getatime(self, path):
        # line: 2863
        'Returns the last access time of the fake file.\n\n        Note: Access time is not set automatically in fake filesystem on access.\n\n        Args:\n            path: the path to fake file.\n\n        Returns:\n            (int, float) the access time of the fake file in number of seconds since the epoch.\n\n        Raises:\n            OSError: if the file does not exist.\n        '
        # line: 2864
        try:
            # line: 2865
            file_obj = self.filesystem.ResolveObject(path)
        # line: 2866
        except IOError as exc:
            # line: 2867
            raise OSError(errno.ENOENT, str(exc))
        # line: 2868
        return file_obj.st_atime

    # line: 2870
    def getctime(self, path):
        # line: 2881
        'Returns the creation time of the fake file.\n\n        Args:\n            path: the path to fake file.\n\n        Returns:\n            (int, float) the creation time of the fake file in number of seconds since the epoch.\n\n        Raises:\n            OSError: if the file does not exist.\n        '
        # line: 2882
        try:
            # line: 2883
            file_obj = self.filesystem.ResolveObject(path)
        # line: 2884
        except IOError as exc:
            # line: 2885
            raise OSError(errno.ENOENT, str(exc))
        # line: 2886
        return file_obj.st_ctime

    # line: 2888
    def abspath(self, path):
        # line: 2889
        'Return the absolute version of a path.'

        # line: 2891
        def getcwd():
            # line: 2892
            'Return the current working directory.'
            # line: 2894
            if ((sys.version_info < (3,)) and isinstance(path, unicode)):
                # line: 2895
                return self.os.getcwdu()
            elif ((sys.version_info >= (3,)) and isinstance(path, bytes)):
                # line: 2897
                return self.os.getcwdb()
            else:
                # line: 2899
                return self.os.getcwd()
        # line: 2901
        if (sys.version_info >= (3, 6)):
            # line: 2902
            path = os.fspath(path)
        # line: 2904
        sep = self.filesystem._path_separator(path)
        # line: 2905
        altsep = self.filesystem._alternative_path_separator(path)
        # line: 2906
        if (not self.isabs(path)):
            # line: 2907
            path = self.join(getcwd(), path)
        elif ((self.filesystem.is_windows_fs and path.startswith(sep)) or ((altsep is not None) and path.startswith(altsep))):
            # line: 2911
            cwd = getcwd()
            # line: 2912
            if self.filesystem.StartsWithDriveLetter(cwd):
                # line: 2913
                path = self.join(cwd[:2], path)
        # line: 2914
        return self.normpath(path)

    # line: 2916
    def join(self, *p):
        # line: 2917
        'Return the completed path with a separator of the parts.'
        # line: 2918
        return self.filesystem.JoinPaths(*p)

    # line: 2920
    def split(self, path):
        # line: 2923
        'Split the path into the directory and the filename of the path.\n        New in pyfakefs 3.0.\n        '
        # line: 2924
        return self.filesystem.SplitPath(path)

    # line: 2926
    def splitdrive(self, path):
        # line: 2929
        'Split the path into the drive part and the rest of the path, if supported.\n        New in pyfakefs 2.9.\n        '
        # line: 2930
        return self.filesystem.SplitDrive(path)

    # line: 2932
    def normpath(self, path):
        # line: 2933
        'Normalize path, eliminating double slashes, etc.'
        # line: 2934
        return self.filesystem.CollapsePath(path)

    # line: 2936
    def normcase(self, path):
        # line: 2939
        'Convert to lower case under windows, replaces additional path separator.\n        New in pyfakefs 2.9.\n        '
        # line: 2940
        path = self.filesystem.NormalizePathSeparator(path)
        # line: 2941
        if self.filesystem.is_windows_fs:
            # line: 2942
            path = path.lower()
        # line: 2943
        return path

    # line: 2945
    def relpath(self, path, start=None):
        # line: 2946
        'We mostly rely on the native implementation and adapt the path separator.'
        # line: 2947
        if (not path):
            # line: 2948
            raise ValueError('no path specified')
        # line: 2949
        if (sys.version_info >= (3, 6)):
            # line: 2950
            path = os.fspath(path)
            # line: 2951
            if (start is not None):
                # line: 2952
                start = os.fspath(start)
        # line: 2953
        if (start is None):
            # line: 2954
            start = self.filesystem.cwd
        # line: 2955
        if (self.filesystem.alternative_path_separator is not None):
            # line: 2956
            path = path.replace(self.filesystem.alternative_path_separator, self._os_path.sep)
            # line: 2957
            start = start.replace(self.filesystem.alternative_path_separator, self._os_path.sep)
        # line: 2958
        path = path.replace(self.filesystem.path_separator, self._os_path.sep)
        # line: 2959
        start = start.replace(self.filesystem.path_separator, self._os_path.sep)
        # line: 2960
        path = self._os_path.relpath(path, start)
        # line: 2961
        return path.replace(self._os_path.sep, self.filesystem.path_separator)

    # line: 2963
    def realpath(self, filename):
        # line: 2967
        'Return the canonical path of the specified filename, eliminating any\n        symbolic links encountered in the path.\n        New in pyfakefs 3.0.\n        '
        # line: 2968
        if self.filesystem.is_windows_fs:
            # line: 2969
            return self.abspath(filename)
        # line: 2970
        if (sys.version_info >= (3, 6)):
            # line: 2971
            filename = os.fspath(filename)
        # line: 2972
        (path, ok) = self._joinrealpath(filename[:0], filename, {})
        # line: 2973
        return self.abspath(path)
    # line: 2975
    if ((sys.platform != 'win32') or (sys.version_info >= (3, 2))):

        # line: 2976
        def samefile(self, path1, path2):
            # line: 2987
            'Return whether path1 and path2 point to the same file.\n            Windows support new in Python 3.2.\n            New in pyfakefs 3.3.\n\n            Args:\n                path1: first file path or path object (Python >=3.6)\n                path2: second file path or path object (Python >=3.6)\n\n            Raises:\n              OSError: if one of the paths does not point to an existing file system object.\n            '
            # line: 2988
            stat1 = self.filesystem.GetStat(path1)
            # line: 2989
            stat2 = self.filesystem.GetStat(path2)
            # line: 2990
            return ((stat1.st_ino == stat2.st_ino) and (stat1.st_dev == stat2.st_dev))

    # line: 2992
    def _joinrealpath(self, path, rest, seen):
        # line: 2996
        'Join two paths, normalizing and eliminating any symbolic links\n        encountered in the second path.\n        Taken from Python source and adapted.\n        '
        # line: 2997
        curdir = self.filesystem._matching_string(path, '.')
        # line: 2998
        pardir = self.filesystem._matching_string(path, '..')
        # line: 3000
        sep = self.filesystem._path_separator(path)
        # line: 3001
        if self.isabs(rest):
            # line: 3002
            rest = rest[1:]
            # line: 3003
            path = sep
        # line: 3005
        while rest:
            # line: 3006
            (name, _, rest) = rest.partition(sep)
            # line: 3007
            if ((not name) or (name == curdir)):
                # line: 3009
                continue
            # line: 3010
            if (name == pardir):
                # line: 3012
                if path:
                    # line: 3013
                    (path, name) = self.filesystem.SplitPath(path)
                    # line: 3014
                    if (name == pardir):
                        # line: 3015
                        path = self.filesystem.JoinPaths(path, pardir, pardir)
                else:
                    # line: 3017
                    path = pardir
                # line: 3018
                continue
            # line: 3019
            newpath = self.filesystem.JoinPaths(path, name)
            # line: 3020
            if (not self.filesystem.IsLink(newpath)):
                # line: 3021
                path = newpath
                # line: 3022
                continue
            # line: 3024
            if (newpath in seen):
                # line: 3026
                path = seen[newpath]
                # line: 3027
                if (path is not None):
                    # line: 3029
                    continue
                # line: 3032
                return (self.filesystem.JoinPaths(newpath, rest), False)
            # line: 3033
            seen[newpath] = None
            # line: 3034
            (path, ok) = self._joinrealpath(path, self.filesystem.ReadLink(newpath), seen)
            # line: 3035
            if (not ok):
                # line: 3036
                return (self.filesystem.JoinPaths(path, rest), False)
            # line: 3037
            seen[newpath] = path
        # line: 3038
        return (path, True)

    # line: 3040
    def dirname(self, path):
        # line: 3043
        'Returns the first part of the result of `split()`.\n        New in pyfakefs 3.0.\n        '
        # line: 3044
        return self.split(path)[0]

    # line: 3046
    def expanduser(self, path):
        # line: 3049
        "Return the argument with an initial component of ~ or ~user\n        replaced by that user's home directory.\n        "
        # line: 3050
        return self._os_path.expanduser(path).replace(self._os_path.sep, self.sep)

    # line: 3052
    def ismount(self, path):
        # line: 3062
        'Return true if the given path is a mount point.\n        New in pyfakefs 2.9.\n\n        Args:\n          path:  path to filesystem object to be checked\n\n        Returns:\n          True if path is a mount point added to the fake file system.\n          Under Windows also returns True for drive and UNC roots (independent of their existence).\n        '
        # line: 3063
        if (sys.version_info >= (3, 6)):
            # line: 3064
            path = os.fspath(path)
        # line: 3065
        if (not path):
            # line: 3066
            return False
        # line: 3067
        normed_path = self.filesystem.NormalizePath(path)
        # line: 3068
        sep = self.filesystem._path_separator(path)
        # line: 3069
        if self.filesystem.is_windows_fs:
            # line: 3070
            if (self.filesystem.alternative_path_separator is not None):
                # line: 3071
                path_seps = (sep, self.filesystem._alternative_path_separator(path))
            else:
                # line: 3075
                path_seps = (sep,)
            # line: 3076
            (drive, rest) = self.filesystem.SplitDrive(normed_path)
            # line: 3077
            if (drive and (drive[:1] in path_seps)):
                # line: 3078
                return ((not rest) or (rest in path_seps))
            # line: 3079
            if (rest in path_seps):
                # line: 3080
                return True
        # line: 3081
        for mount_point in self.filesystem.mount_points:
            # line: 3082
            if (normed_path.rstrip(sep) == mount_point.rstrip(sep)):
                # line: 3083
                return True
        # line: 3084
        return False
    # line: 3086
    if (sys.version_info < (3, 0)):

        # line: 3087
        def walk(self, top, func, arg):
            # line: 3095
            'Directory tree walk with callback function.\n            New in pyfakefs 3.0.\n\n            Args:\n                top: root path to traverse. The root itself is not included in the called elements.\n                func: function to be called for each visited path node.\n                arg: first argument to be called with func (apart from dirname and filenames).\n            '
            # line: 3096
            try:
                # line: 3097
                names = self.filesystem.ListDir(top)
            # line: 3098
            except os.error:
                # line: 3099
                return
            # line: 3100
            func(arg, top, names)
            # line: 3101
            for name in names:
                # line: 3102
                name = self.filesystem.JoinPaths(top, name)
                # line: 3103
                if self.filesystem.is_windows_fs:
                    # line: 3104
                    if self.filesystem.IsDir(name):
                        # line: 3105
                        self.walk(name, func, arg)
                else:
                    # line: 3107
                    try:
                        # line: 3108
                        st = self.filesystem.GetStat(name, follow_symlinks=False)
                    # line: 3109
                    except os.error:
                        # line: 3110
                        continue
                    # line: 3111
                    if stat.S_ISDIR(st.st_mode):
                        # line: 3112
                        self.walk(name, func, arg)

    # line: 3114
    def __getattr__(self, name):
        # line: 3115
        'Forwards any non-faked calls to the real os.path.'
        # line: 3116
        return getattr(self._os_path, name)


# line: 3119
class FakeOsModule(object):
    # line: 3130
    'Uses FakeFilesystem to provide a fake os module replacement.\n\n    Do not create os.path separately from os, as there is a necessary circular\n    dependency between os and os.path to replicate the behavior of the standard\n    Python modules.  What you want to do is to just let FakeOsModule take care of\n    os.path setup itself.\n\n    # You always want to do this.\n    filesystem = fake_filesystem.FakeFilesystem()\n    my_os_module = fake_filesystem.FakeOsModule(filesystem)\n    '
    # line: 3132
    _stat_float_times = (sys.version_info >= (2, 5))

    # line: 3134
    def __init__(self, filesystem, os_path_module=None):
        # line: 3140
        'Also exposes self.path (to fake os.path).\n\n        Args:\n          filesystem:  FakeFilesystem used to provide file system information\n          os_path_module: (deprecated) optional FakePathModule instance\n        '
        # line: 3141
        self.filesystem = filesystem
        # line: 3142
        self.sep = filesystem.path_separator
        # line: 3143
        self.altsep = filesystem.alternative_path_separator
        # line: 3144
        self._os_module = os
        # line: 3145
        if (os_path_module is None):
            # line: 3146
            self.path = FakePathModule(self.filesystem, self)
        else:
            # line: 3148
            warnings.warn(FAKE_PATH_MODULE_DEPRECATION, DeprecationWarning, stacklevel=2)
            # line: 3150
            self.path = os_path_module
        # line: 3151
        if (sys.version_info < (3, 0)):
            # line: 3152
            self.fdopen = self._fdopen_ver2
        else:
            # line: 3154
            self.fdopen = self._fdopen

    # line: 3156
    def _fdopen(self, *args, **kwargs):
        # line: 3168
        'Redirector to open() builtin function.\n\n        Args:\n          *args: pass through args\n          **kwargs: pass through kwargs\n\n        Returns:\n          File object corresponding to file_des.\n\n        Raises:\n          TypeError: if file descriptor is not an integer.\n        '
        # line: 3169
        if (not isinstance(args[0], int)):
            # line: 3170
            raise TypeError('an integer is required')
        # line: 3171
        return FakeFileOpen(self.filesystem)(*args, **kwargs)

    # line: 3173
    def _fdopen_ver2(self, file_des, mode='r', bufsize=None):
        # line: 3188
        'Returns an open file object connected to the file descriptor file_des.\n\n        Args:\n          file_des: An integer file descriptor for the file object requested.\n          mode: additional file flags. Currently checks to see if the mode matches\n            the mode of the requested file object.\n          bufsize: ignored. (Used for signature compliance with __builtin__.fdopen)\n\n        Returns:\n          File object corresponding to file_des.\n\n        Raises:\n          OSError: if bad file descriptor or incompatible mode is given.\n          TypeError: if file descriptor is not an integer.\n        '
        # line: 3189
        if (not isinstance(file_des, int)):
            # line: 3190
            raise TypeError('an integer is required')
        # line: 3192
        try:
            # line: 3193
            return FakeFileOpen(self.filesystem).Call(file_des, mode=mode)
        # line: 3194
        except IOError as exc:
            # line: 3195
            raise OSError(exc)

    # line: 3197
    def _umask(self):
        # line: 3198
        'Return the current umask.'
        # line: 3199
        if self.filesystem.is_windows_fs:
            # line: 3201
            return 0
        # line: 3202
        if (sys.platform == 'win32'):
            # line: 3204
            return 2
        else:
            # line: 3209
            mask = os.umask(0)
            # line: 3210
            os.umask(mask)
            # line: 3211
            return mask

    # line: 3214
    def open(self, file_path, flags, mode=None, dir_fd=None):
        # line: 3233
        'Return the file descriptor for a FakeFile.\n\n        Args:\n            file_path: the path to the file\n            flags: low-level bits to indicate io operation\n            mode: bits to define default permissions\n                Note: only basic modes are supported, OS-specific modes are ignored\n            dir_fd: If not `None`, the file descriptor of a directory,\n                with `file_path` being relative to this directory.\n                New in Python 3.3. New in pyfakefs 3.3.\n\n        Returns:\n            A file descriptor.\n\n        Raises:\n            IOError: if the path cannot be found\n            ValueError: if invalid mode is given\n            NotImplementedError: if `os.O_EXCL` is used without `os.O_CREAT`\n        '
        # line: 3234
        file_path = self._path_with_dir_fd(file_path, self.open, dir_fd)
        # line: 3235
        if (mode is None):
            # line: 3236
            if self.filesystem.is_windows_fs:
                # line: 3237
                mode = 438
            else:
                # line: 3239
                mode = (511 & (~ self._umask()))
        # line: 3241
        open_modes = _OpenModes(must_exist=(not (flags & os.O_CREAT)), can_read=(not (flags & os.O_WRONLY)), can_write=(flags & (os.O_RDWR | os.O_WRONLY)), truncate=(flags & os.O_TRUNC), append=(flags & os.O_APPEND), must_not_exist=(flags & os.O_EXCL))
        # line: 3249
        if (open_modes.must_not_exist and open_modes.must_exist):
            # line: 3250
            raise NotImplementedError('O_EXCL without O_CREAT mode is not supported')
        # line: 3252
        if ((not self.filesystem.is_windows_fs) and (not open_modes.can_write) and self.filesystem.Exists(file_path)):
            # line: 3256
            obj = self.filesystem.ResolveObject(file_path)
            # line: 3257
            if isinstance(obj, FakeDirectory):
                # line: 3258
                dir_wrapper = FakeDirWrapper(obj, file_path, self.filesystem)
                # line: 3259
                file_des = self.filesystem.AddOpenFile(dir_wrapper)
                # line: 3260
                dir_wrapper.filedes = file_des
                # line: 3261
                return file_des
        # line: 3264
        str_flags = 'b'
        # line: 3265
        delete_on_close = False
        # line: 3266
        if hasattr(os, 'O_TEMPORARY'):
            # line: 3267
            delete_on_close = ((flags & os.O_TEMPORARY) == os.O_TEMPORARY)
        # line: 3268
        fake_file = FakeFileOpen(self.filesystem, delete_on_close=delete_on_close, raw_io=True)(file_path, str_flags, open_modes=open_modes)
        # line: 3271
        self.chmod(file_path, mode)
        # line: 3272
        return fake_file.fileno()

    # line: 3274
    def close(self, file_des):
        # line: 3283
        'Close a file descriptor.\n\n        Args:\n          file_des: An integer file descriptor for the file object requested.\n\n        Raises:\n          OSError: bad file descriptor.\n          TypeError: if file descriptor is not an integer.\n        '
        # line: 3284
        file_handle = self.filesystem.GetOpenFile(file_des)
        # line: 3285
        file_handle.close()

    # line: 3287
    def read(self, file_des, num_bytes):
        # line: 3300
        'Read number of bytes from a file descriptor, returns bytes read.\n\n        Args:\n          file_des: An integer file descriptor for the file object requested.\n          num_bytes: Number of bytes to read from file.\n\n        Returns:\n          Bytes read from file.\n\n        Raises:\n          OSError: bad file descriptor.\n          TypeError: if file descriptor is not an integer.\n        '
        # line: 3301
        file_handle = self.filesystem.GetOpenFile(file_des)
        # line: 3302
        file_handle.raw_io = True
        # line: 3303
        return file_handle.read(num_bytes)

    # line: 3305
    def write(self, file_des, contents):
        # line: 3318
        'Write string to file descriptor, returns number of bytes written.\n\n        Args:\n          file_des: An integer file descriptor for the file object requested.\n          contents: String of bytes to write to file.\n\n        Returns:\n          Number of bytes written.\n\n        Raises:\n          OSError: bad file descriptor.\n          TypeError: if file descriptor is not an integer.\n        '
        # line: 3319
        file_handle = self.filesystem.GetOpenFile(file_des)
        # line: 3320
        file_handle.raw_io = True
        # line: 3321
        file_handle._sync_io()
        # line: 3322
        file_handle.write(contents)
        # line: 3323
        file_handle.flush()
        # line: 3324
        return len(contents)

    # line: 3326
    @classmethod
    # line: 3326
    def stat_float_times(cls, newvalue=None):
        # line: 3337
        "Determine whether a file's time stamps are reported as floats or ints.\n        New in pyfakefs 2.9.\n\n        Calling without arguments returns the current value. The value is shared\n        by all instances of FakeOsModule.\n\n        Args:\n          newvalue: if True, mtime, ctime, atime are reported as floats.\n            Else, as ints (rounding down).\n        "
        # line: 3338
        if (newvalue is not None):
            # line: 3339
            cls._stat_float_times = bool(newvalue)
        # line: 3340
        return cls._stat_float_times

    # line: 3342
    def fstat(self, file_des):
        # line: 3353
        "Return the os.stat-like tuple for the FakeFile object of file_des.\n\n        Args:\n          file_des:  file descriptor of filesystem object to retrieve.\n\n        Returns:\n          the FakeStatResult object corresponding to entry_path.\n\n        Raises:\n          OSError: if the filesystem object doesn't exist.\n        "
        # line: 3355
        file_object = self.filesystem.GetOpenFile(file_des).GetObject()
        # line: 3356
        return file_object.stat_result.copy()

    # line: 3358
    def umask(self, new_mask):
        # line: 3369
        'Change the current umask.\n\n        Args:\n          new_mask: An integer.\n\n        Returns:\n          The old mask.\n\n        Raises:\n          TypeError: new_mask is of an invalid type.\n        '
        # line: 3370
        if (not isinstance(new_mask, int)):
            # line: 3371
            raise TypeError('an integer is required')
        # line: 3372
        old_umask = self.filesystem.umask
        # line: 3373
        self.filesystem.umask = new_mask
        # line: 3374
        return old_umask

    # line: 3376
    def chdir(self, target_directory):
        # line: 3385
        'Change current working directory to target directory.\n\n        Args:\n          target_directory:  path to new current working directory.\n\n        Raises:\n          OSError: if user lacks permission to enter the argument directory or if\n                   the target is not a directory\n        '
        # line: 3386
        target_directory = self.filesystem.ResolvePath(target_directory, allow_fd=True)
        # line: 3387
        self.filesystem.ConfirmDir(target_directory)
        # line: 3388
        directory = self.filesystem.ResolveObject(target_directory)
        # line: 3390
        if (not (directory.st_mode | PERM_EXE)):
            # line: 3391
            raise OSError(errno.EACCES, 'Fake os module: permission denied', directory)
        # line: 3393
        self.filesystem.cwd = target_directory

    # line: 3395
    def getcwd(self):
        # line: 3396
        'Return current working directory.'
        # line: 3397
        return self.filesystem.cwd
    # line: 3399
    if (sys.version_info < (3,)):

        # line: 3400
        def getcwdu(self):
            # line: 3401
            'Return current working directory as unicode. Python 2 only.'
            # line: 3402
            return unicode(self.filesystem.cwd)
    else:

        # line: 3405
        def getcwdb(self):
            # line: 3406
            'Return current working directory as bytes. Python 3 only.'
            # line: 3407
            return bytes(self.filesystem.cwd, locale.getpreferredencoding(False))

    # line: 3409
    def listdir(self, target_directory):
        # line: 3421
        'Return a list of file names in target_directory.\n\n        Args:\n          target_directory:  path to the target directory within the fake\n            filesystem.\n\n        Returns:\n          a list of file names within the target directory in arbitrary order.\n\n        Raises:\n          OSError:  if the target is not a directory.\n        '
        # line: 3422
        return self.filesystem.ListDir(target_directory)
    # line: 3424
    if (sys.platform.startswith('linux') and (sys.version_info >= (3, 3))):

        # line: 3425
        def listxattr(self, path=None, follow_symlinks=True):
            # line: 3426
            'Dummy implementation that returns an empty list - used by shutil.'
            # line: 3427
            return []
    # line: 3429
    if (sys.version_info >= (3, 5)):

        # line: 3430
        def scandir(self, path=''):
            # line: 3442
            'Return an iterator of DirEntry objects corresponding to the entries\n            in the directory given by path.\n\n            Args:\n              path: path to the target directory within the fake filesystem.\n\n            Returns:\n              an iterator to an unsorted list of os.DirEntry objects for each entry in path.\n\n            Raises:\n              OSError: if the target is not a directory.\n            '
            # line: 3443
            return self.filesystem.ScanDir(path)

    # line: 3445
    def _ClassifyDirectoryContents(self, root):
        # line: 3460
        'Classify contents of a directory as files/directories.\n\n        Args:\n          root: (str) Directory to examine.\n\n        Returns:\n          (tuple) A tuple consisting of three values: the directory examined, a\n          list containing all of the directory entries, and a list containing all\n          of the non-directory entries.  (This is the same format as returned by\n          the os.walk generator.)\n\n        Raises:\n          Nothing on its own, but be ready to catch exceptions generated by\n          underlying mechanisms like os.listdir.\n        '
        # line: 3461
        dirs = []
        # line: 3462
        files = []
        # line: 3463
        for entry in self.listdir(root):
            # line: 3464
            if self.path.isdir(self.path.join(root, entry)):
                # line: 3465
                dirs.append(entry)
            else:
                # line: 3467
                files.append(entry)
        # line: 3468
        return (root, dirs, files)

    # line: 3470
    def walk(self, top, topdown=True, onerror=None, followlinks=False):
        # line: 3486
        'Perform an os.walk operation over the fake filesystem.\n\n        Args:\n          top:  root directory from which to begin walk.\n          topdown:  determines whether to return the tuples with the root as the\n            first entry (True) or as the last, after all the child directory\n            tuples (False).\n          onerror:  if not None, function which will be called to handle the\n            os.error instance provided when os.listdir() fails.\n          followlinks: if True, symbolic links are followed. New in pyfakefs 2.9.\n\n        Yields:\n          (path, directories, nondirectories) for top and each of its\n          subdirectories.  See the documentation for the builtin os module for\n          further details.\n        '

        # line: 3487
        def do_walk(top, topMost=False):
            # line: 3488
            top = self.path.normpath(top)
            # line: 3489
            if ((not topMost) and (not followlinks) and self.path.islink(top)):
                # line: 3490
                return
            # line: 3491
            try:
                # line: 3492
                top_contents = self._ClassifyDirectoryContents(top)
            # line: 3493
            except OSError as exc:
                # line: 3494
                top_contents = None
                # line: 3495
                if (onerror is not None):
                    # line: 3496
                    onerror(exc)
            # line: 3498
            if (top_contents is not None):
                # line: 3499
                if topdown:
                    # line: 3500
                    yield top_contents
                # line: 3502
                for directory in top_contents[1]:
                    # line: 3503
                    if ((not followlinks) and self.path.islink(directory)):
                        # line: 3504
                        continue
                    # line: 3505
                    for contents in do_walk(self.path.join(top, directory)):
                        # line: 3506
                        yield contents
                # line: 3508
                if (not topdown):
                    # line: 3509
                    yield top_contents
        # line: 3511
        return do_walk(top, topMost=True)

    # line: 3514
    def readlink(self, path, dir_fd=None):
        # line: 3530
        'Read the target of a symlink.\n\n        Args:\n            path:  Symlink to read the target of.\n            dir_fd: If not `None`, the file descriptor of a directory,\n                with `path` being relative to this directory.\n                New in Python 3.3. New in pyfakefs 3.3.\n\n        Returns:\n            the string representing the path to which the symbolic link points.\n\n        Raises:\n            TypeError: if `path` is None\n            OSError: (with errno=ENOENT) if path is not a valid path, or\n                     (with errno=EINVAL) if path is valid, but is not a symlink.\n        '
        # line: 3531
        path = self._path_with_dir_fd(path, self.readlink, dir_fd)
        # line: 3532
        return self.filesystem.ReadLink(path)

    # line: 3534
    def stat(self, entry_path, dir_fd=None, follow_symlinks=None):
        # line: 3551
        "Return the os.stat-like tuple for the FakeFile object of entry_path.\n\n        Args:\n            entry_path:  path to filesystem object to retrieve.\n            dir_fd: (int) If not `None`, the file descriptor of a directory,\n                with `entry_path` being relative to this directory.\n                New in Python 3.3. New in pyfakefs 3.3.\n            follow_symlinks: (bool) If `False` and `entry_path` points to a symlink,\n                the link itself is changed instead of the linked object.\n                New in Python 3.3. New in pyfakefs 3.0.\n\n        Returns:\n          the FakeStatResult object corresponding to entry_path.\n\n        Raises:\n          OSError: if the filesystem object doesn't exist.\n        "
        # line: 3552
        if (follow_symlinks is None):
            # line: 3553
            follow_symlinks = True
        elif (sys.version_info < (3, 3)):
            # line: 3555
            raise TypeError("stat() got an unexpected keyword argument 'follow_symlinks'")
        # line: 3556
        entry_path = self._path_with_dir_fd(entry_path, self.stat, dir_fd)
        # line: 3557
        return self.filesystem.GetStat(entry_path, follow_symlinks)

    # line: 3559
    def lstat(self, entry_path, dir_fd=None):
        # line: 3573
        "Return the os.stat-like tuple for entry_path, not following symlinks.\n\n        Args:\n            entry_path:  path to filesystem object to retrieve.\n            dir_fd: If not `None`, the file descriptor of a directory, with `entry_path`\n                being relative to this directory.\n                New in Python 3.3. New in pyfakefs 3.3.\n\n        Returns:\n            the FakeStatResult object corresponding to `entry_path`.\n\n        Raises:\n            OSError: if the filesystem object doesn't exist.\n        "
        # line: 3575
        entry_path = self._path_with_dir_fd(entry_path, self.lstat, dir_fd)
        # line: 3576
        return self.filesystem.GetStat(entry_path, follow_symlinks=False)

    # line: 3578
    def remove(self, path, dir_fd=None):
        # line: 3591
        'Remove the FakeFile object at the specified file path.\n\n        Args:\n            path: Path to file to be removed.\n            dir_fd: If not `None`, the file descriptor of a directory,\n                with `path` being relative to this directory.\n                New in Python 3.3. New in pyfakefs 3.3.\n\n        Raises:\n            OSError: if path points to a directory.\n            OSError: if path does not exist.\n            OSError: if removal failed.\n        '
        # line: 3592
        path = self._path_with_dir_fd(path, self.remove, dir_fd)
        # line: 3593
        self.filesystem.RemoveFile(path)

    # line: 3595
    def unlink(self, path, dir_fd=None):
        # line: 3608
        'Remove the FakeFile object at the specified file path.\n\n        Args:\n            path: Path to file to be removed.\n            dir_fd: If not `None`, the file descriptor of a directory,\n                with `path` being relative to this directory.\n                New in Python 3.3. New in pyfakefs 3.3.\n\n        Raises:\n            OSError: if path points to a directory.\n            OSError: if path does not exist.\n            OSError: if removal failed.\n        '
        # line: 3609
        path = self._path_with_dir_fd(path, self.unlink, dir_fd)
        # line: 3610
        self.filesystem.RemoveFile(path)

    # line: 3612
    def rename(self, old_file_path, new_file_path, dir_fd=None):
        # line: 3631
        'Rename a FakeFile object at old_file_path to new_file_path,\n        preserving all properties.\n        Also replaces existing new_file_path object, if one existed (Unix only).\n\n        Args:\n            old_file_path:  Path to filesystem object to rename.\n            new_file_path:  Path to where the filesystem object will live after this call.\n            dir_fd: If not `None`, the file descriptor of a directory,\n                with `old_file_path` being relative to this directory.\n                New in Python 3.3. New in pyfakefs 3.3.\n\n        Raises:\n            OSError: if old_file_path does not exist.\n            OSError: if new_file_path is an existing directory.\n            OSError: if new_file_path is an existing file (Windows only)\n            OSError: if new_file_path is an existing file and could not be removed (Unix)\n            OSError: if `dirname(new_file)` does not exist\n            OSError: if the file would be moved to another filesystem (e.g. mount point)\n        '
        # line: 3632
        old_file_path = self._path_with_dir_fd(old_file_path, self.rename, dir_fd)
        # line: 3633
        self.filesystem.RenameObject(old_file_path, new_file_path)
    # line: 3635
    if (sys.version_info >= (3, 3)):

        # line: 3636
        def replace(self, old_file_path, new_file_path):
            # line: 3652
            'Renames a FakeFile object at old_file_path to new_file_path,\n            preserving all properties.\n            Also replaces existing new_file_path object, if one existed.\n            New in pyfakefs 3.0.\n\n            Args:\n              old_file_path:  path to filesystem object to rename\n              new_file_path:  path to where the filesystem object will live after this call\n\n            Raises:\n              OSError: if old_file_path does not exist.\n              OSError: if new_file_path is an existing directory.\n              OSError: if new_file_path is an existing file and could not be removed\n              OSError: if `dirname(new_file)` does not exist\n              OSError: if the file would be moved to another filesystem (e.g. mount point)\n            '
            # line: 3653
            self.filesystem.RenameObject(old_file_path, new_file_path, force_replace=True)

    # line: 3655
    def rmdir(self, target_directory, dir_fd=None):
        # line: 3667
        "Remove a leaf Fake directory.\n\n        Args:\n            target_directory: (str) Name of directory to remove.\n            dir_fd: If not `None`, the file descriptor of a directory,\n                with `target_directory` being relative to this directory.\n                New in Python 3.3. New in pyfakefs 3.3.\n\n        Raises:\n            OSError: if target_directory does not exist or is not a directory,\n            or as per FakeFilesystem.RemoveObject. Cannot remove '.'.\n        "
        # line: 3668
        target_directory = self._path_with_dir_fd(target_directory, self.rmdir, dir_fd)
        # line: 3669
        self.filesystem.RemoveDirectory(target_directory)

    # line: 3671
    def removedirs(self, target_directory):
        # line: 3680
        'Remove a leaf fake directory and all empty intermediate ones.\n\n        Args:\n            target_directory: the directory to be removed.\n\n        Raises:\n            OSError: if target_directory does not exist or is not a directory.\n            OSError: if target_directory is not empty.\n        '
        # line: 3681
        target_directory = self.filesystem.NormalizePath(target_directory)
        # line: 3682
        directory = self.filesystem.ConfirmDir(target_directory)
        # line: 3683
        if directory.contents:
            # line: 3684
            raise OSError(errno.ENOTEMPTY, 'Fake Directory not empty', self.path.basename(target_directory))
        else:
            # line: 3687
            self.rmdir(target_directory)
        # line: 3688
        (head, tail) = self.path.split(target_directory)
        # line: 3689
        if (not tail):
            # line: 3690
            (head, tail) = self.path.split(head)
        # line: 3691
        while (head and tail):
            # line: 3692
            head_dir = self.filesystem.ConfirmDir(head)
            # line: 3693
            if head_dir.contents:
                # line: 3694
                break
            # line: 3696
            self.filesystem.RemoveDirectory(head, allow_symlink=True)
            # line: 3697
            (head, tail) = self.path.split(head)

    # line: 3699
    def mkdir(self, dir_name, mode=PERM_DEF, dir_fd=None):
        # line: 3714
        "Create a leaf Fake directory.\n\n        Args:\n            dir_name: (str) Name of directory to create.\n                Relative paths are assumed to be relative to '/'.\n            mode: (int) Mode to create directory with.  This argument defaults to\n                0o777.  The umask is applied to this mode.\n            dir_fd: If not `None`, the file descriptor of a directory,\n                with `dir_name` being relative to this directory.\n                New in Python 3.3. New in pyfakefs 3.3.\n\n        Raises:\n            OSError: if the directory name is invalid or parent directory is read only\n                or as per FakeFilesystem.AddObject.\n        "
        # line: 3715
        dir_name = self._path_with_dir_fd(dir_name, self.mkdir, dir_fd)
        # line: 3716
        self.filesystem.MakeDirectory(dir_name, mode)

    # line: 3718
    def makedirs(self, dir_name, mode=PERM_DEF, exist_ok=None):
        # line: 3733
        'Create a leaf Fake directory + create any non-existent parent dirs.\n\n        Args:\n          dir_name: (str) Name of directory to create.\n          mode: (int) Mode to create directory (and any necessary parent\n            directories) with. This argument defaults to 0o777.  The umask is\n            applied to this mode.\n          exist_ok: (boolean) If exist_ok is False (the default), an OSError is\n            raised if the target directory already exists.  New in Python 3.2.\n            New in pyfakefs 2.9.\n\n        Raises:\n          OSError: if the directory already exists and exist_ok=False, or as per\n          `FakeFilesystem.CreateDirectory()`.\n        '
        # line: 3734
        if (exist_ok is None):
            # line: 3735
            exist_ok = False
        elif (sys.version_info < (3, 2)):
            # line: 3737
            raise TypeError("makedir() got an unexpected keyword argument 'exist_ok'")
        # line: 3738
        self.filesystem.MakeDirectories(dir_name, mode, exist_ok)

    # line: 3740
    def _path_with_dir_fd(self, path, fct, dir_fd):
        # line: 3741
        'Return the path considering dir_fd. Raise on nmvalid parameters.'
        # line: 3742
        if (dir_fd is not None):
            # line: 3743
            if (sys.version_info < (3, 3)):
                # line: 3744
                raise TypeError(("%s() got an unexpected keyword argument 'dir_fd'" % fct.__name__))
            # line: 3747
            real_fct = getattr(os, fct.__name__)
            # line: 3748
            if (real_fct not in self.supports_dir_fd):
                # line: 3749
                raise NotImplementedError('dir_fd unavailable on this platform')
            # line: 3750
            if isinstance(path, int):
                # line: 3751
                raise ValueError(("%s: Can't specify dir_fd without matching path" % fct.__name__))
            # line: 3753
            if (not self.path.isabs(path)):
                # line: 3754
                return self.path.join(self.filesystem.GetOpenFile(dir_fd).GetObject().GetPath(), path)
        # line: 3756
        return path

    # line: 3758
    def access(self, path, mode, dir_fd=None, follow_symlinks=None):
        # line: 3774
        'Check if a file exists and has the specified permissions.\n\n        Args:\n            path: (str) Path to the file.\n            mode: (int) Permissions represented as a bitwise-OR combination of\n                os.F_OK, os.R_OK, os.W_OK, and os.X_OK.\n            dir_fd: If not `None`, the file descriptor of a directory, with `path`\n                being relative to this directory.\n                New in Python 3.3. New in pyfakefs 3.3.\n            follow_symlinks: (bool) If `False` and `path` points to a symlink,\n                the link itself is queried instead of the linked object.\n                New in Python 3.3. New in pyfakefs 3.0.\n\n        Returns:\n            bool, `True` if file is accessible, `False` otherwise.\n        '
        # line: 3775
        if ((follow_symlinks is not None) and (sys.version_info < (3, 3))):
            # line: 3776
            raise TypeError("access() got an unexpected keyword argument 'follow_symlinks'")
        # line: 3777
        path = self._path_with_dir_fd(path, self.access, dir_fd)
        # line: 3778
        try:
            # line: 3779
            stat_result = self.stat(path, follow_symlinks=follow_symlinks)
        # line: 3780
        except OSError as os_error:
            # line: 3781
            if (os_error.errno == errno.ENOENT):
                # line: 3782
                return False
            # line: 3783
            raise
        # line: 3784
        return ((mode & ((stat_result.st_mode >> 6) & 7)) == mode)

    # line: 3786
    def chmod(self, path, mode, dir_fd=None, follow_symlinks=None):
        # line: 3798
        'Change the permissions of a file as encoded in integer mode.\n\n        Args:\n            path: (str) Path to the file.\n            mode: (int) Permissions.\n            dir_fd: If not `None`, the file descriptor of a directory, with `path`\n                being relative to this directory.\n                New in Python 3.3. New in pyfakefs 3.3.\n            follow_symlinks: (bool) If `False` and `path` points to a symlink,\n                the link itself is queried instead of the linked object.\n                New in Python 3.3. New in pyfakefs 3.0.\n        '
        # line: 3799
        if (follow_symlinks is None):
            # line: 3800
            follow_symlinks = True
        elif (sys.version_info < (3, 3)):
            # line: 3802
            raise TypeError("chmod() got an unexpected keyword argument 'follow_symlinks'")
        # line: 3803
        path = self._path_with_dir_fd(path, self.chmod, dir_fd)
        # line: 3804
        self.filesystem.ChangeMode(path, mode, follow_symlinks)

    # line: 3806
    def lchmod(self, path, mode):
        # line: 3813
        'Change the permissions of a file as encoded in integer mode.\n        If the file is a link, the permissions of the link are changed.\n\n        Args:\n          path: (str) Path to the file.\n          mode: (int) Permissions.\n        '
        # line: 3814
        if self.filesystem.is_windows_fs:
            # line: 3815
            raise (NameError, "name 'lchmod' is not defined")
        # line: 3816
        self.filesystem.ChangeMode(path, mode, follow_symlinks=False)

    # line: 3818
    def utime(self, path, times=None, ns=None, dir_fd=None, follow_symlinks=None):
        # line: 3842
        'Change the access and modified times of a file.\n\n        Args:\n            path: (str) Path to the file.\n            times: 2-tuple of int or float numbers, of the form (atime, mtime) \n                which is used to set the access and modified times in seconds. \n                If None, both times are set to the current time.\n            ns: 2-tuple of int numbers, of the form (atime, mtime)  which is \n                used to set the access and modified times in nanoseconds. \n                If None, both times are set to the current time.\n                New in Python 3.3. New in pyfakefs 3.3.\n            dir_fd: If not `None`, the file descriptor of a directory, with `path`\n                being relative to this directory.\n                New in Python 3.3. New in pyfakefs 3.3.\n            follow_symlinks: (bool) If `False` and `path` points to a symlink,\n                the link itself is queried instead of the linked object.\n                New in Python 3.3. New in pyfakefs 3.0.\n    \n            Raises:\n                TypeError: If anything other than the expected types is \n                    specified in the passed `times` or `ns` tuple, \n                    or if the tuple length is not equal to 2.\n                ValueError: If both times and ns are specified.\n        '
        # line: 3843
        if (follow_symlinks is None):
            # line: 3844
            follow_symlinks = True
        elif (sys.version_info < (3, 3)):
            # line: 3846
            raise TypeError("utime() got an unexpected keyword argument 'follow_symlinks'")
        # line: 3847
        path = self._path_with_dir_fd(path, self.utime, dir_fd)
        # line: 3848
        if ((ns is not None) and (sys.version_info < (3, 3))):
            # line: 3849
            raise TypeError("utime() got an unexpected keyword argument 'ns'")
        # line: 3851
        self.filesystem.UpdateTime(path, times, ns, follow_symlinks)

    # line: 3853
    def chown(self, path, uid, gid, dir_fd=None, follow_symlinks=None):
        # line: 3872
        'Set ownership of a faked file.\n\n        Args:\n            path: (str) Path to the file or directory.\n            uid: (int) Numeric uid to set the file or directory to.\n            gid: (int) Numeric gid to set the file or directory to.\n            dir_fd: (int) If not `None`, the file descriptor of a directory,\n                with `path` being relative to this directory.\n                New in Python 3.3. New in pyfakefs 3.3.\n            follow_symlinks: (bool) If `False` and path points to a symlink,\n                the link itself is changed instead of the linked object.\n                New in Python 3.3. New in pyfakefs 3.0.\n\n        Raises:\n          OSError: if path does not exist.\n\n        `None` is also allowed for `uid` and `gid`.  This permits `os.rename` to\n        use `os.chown` even when the source file `uid` and `gid` are `None` (unset).\n        '
        # line: 3873
        if (follow_symlinks is None):
            # line: 3874
            follow_symlinks = True
        elif (sys.version_info < (3, 3)):
            # line: 3876
            raise TypeError("chown() got an unexpected keyword argument 'follow_symlinks'")
        # line: 3877
        path = self._path_with_dir_fd(path, self.chown, dir_fd)
        # line: 3878
        try:
            # line: 3879
            file_object = self.filesystem.ResolveObject(path, follow_symlinks, allow_fd=True)
        # line: 3880
        except IOError as io_error:
            # line: 3881
            if (io_error.errno == errno.ENOENT):
                # line: 3882
                raise OSError(errno.ENOENT, 'No such file or directory in fake filesystem', path)
            # line: 3885
            raise
        # line: 3886
        if (not ((isinstance(uid, int) or (uid is None)) and (isinstance(gid, int) or (gid is None)))):
            # line: 3888
            raise TypeError('An integer is required')
        # line: 3889
        if (uid != (-1)):
            # line: 3890
            file_object.st_uid = uid
        # line: 3891
        if (gid != (-1)):
            # line: 3892
            file_object.st_gid = gid

    # line: 3894
    def mknod(self, filename, mode=None, device=None, dir_fd=None):
        # line: 3914
        "Create a filesystem node named 'filename'.\n\n        Does not support device special files or named pipes as the real os\n        module does.\n\n        Args:\n            filename: (str) Name of the file to create\n            mode: (int) Permissions to use and type of file to be created.\n                Default permissions are 0o666.  Only the stat.S_IFREG file type\n                is supported by the fake implementation.  The umask is applied\n                to this mode.\n            device: not supported in fake implementation\n            dir_fd: If not `None`, the file descriptor of a directory,\n                with `filename` being relative to this directory.\n                New in Python 3.3. New in pyfakefs 3.3.\n\n        Raises:\n          OSError: if called with unsupported options or the file can not be\n          created.\n        "
        # line: 3915
        if self.filesystem.is_windows_fs:
            # line: 3916
            raise (AttributeError, "module 'os' has no attribute 'mknode'")
        # line: 3917
        if (mode is None):
            # line: 3918
            mode = (stat.S_IFREG | PERM_DEF_FILE)
        # line: 3919
        if (device or (not (mode & stat.S_IFREG))):
            # line: 3920
            raise OSError(errno.ENOENT, 'Fake os mknod implementation only supports regular files.')
        # line: 3924
        filename = self._path_with_dir_fd(filename, self.mknod, dir_fd)
        # line: 3925
        (head, tail) = self.path.split(filename)
        # line: 3926
        if (not tail):
            # line: 3927
            if self.filesystem.Exists(head):
                # line: 3928
                raise OSError(errno.EEXIST, ('Fake filesystem: %s: %s' % (os.strerror(errno.EEXIST), filename)))
            # line: 3930
            raise OSError(errno.ENOENT, ('Fake filesystem: %s: %s' % (os.strerror(errno.ENOENT), filename)))
        # line: 3932
        if (tail in ('.', u'.', '..', u'..')):
            # line: 3933
            raise OSError(errno.ENOENT, ('Fake fileystem: %s: %s' % (os.strerror(errno.ENOENT), filename)))
        # line: 3935
        if self.filesystem.Exists(filename):
            # line: 3936
            raise OSError(errno.EEXIST, ('Fake fileystem: %s: %s' % (os.strerror(errno.EEXIST), filename)))
        # line: 3938
        try:
            # line: 3939
            self.filesystem.AddObject(head, FakeFile(tail, (mode & (~ self.filesystem.umask)), filesystem=self.filesystem))
        # line: 3942
        except IOError as e:
            # line: 3943
            raise OSError(e.errno, ('Fake filesystem: %s: %s' % (os.strerror(e.errno), filename)))

    # line: 3946
    def symlink(self, link_target, path, dir_fd=None):
        # line: 3958
        'Creates the specified symlink, pointed at the specified link target.\n\n        Args:\n            link_target: The target of the symlink.\n            path: Path to the symlink to create.\n            dir_fd: If not `None`, the file descriptor of a directory,\n                with `link_target` being relative to this directory.\n                New in Python 3.3. New in pyfakefs 3.3.\n\n        Raises:\n            OSError:  if the file already exists.\n        '
        # line: 3959
        link_target = self._path_with_dir_fd(link_target, self.symlink, dir_fd)
        # line: 3960
        self.filesystem.CreateLink(path, link_target, create_missing_dirs=False)

    # line: 3962
    def link(self, oldpath, newpath, dir_fd=None):
        # line: 3980
        "Create a hard link at new_path, pointing at old_path.\n        New in pyfakefs 2.9.\n\n        Args:\n            old_path: An existing link to the target file.\n            new_path: The destination path to create a new link at.\n            dir_fd: If not `None`, the file descriptor of a directory, with `oldpath`\n                being relative to this directory.\n                New in Python 3.3. New in pyfakefs 3.3.\n\n        Returns:\n            the FakeFile object referred to by `oldpath`.\n\n        Raises:\n            OSError:  if something already exists at new_path.\n            OSError:  if the parent directory doesn't exist.\n            OSError:  if on Windows before Python 3.2.\n        "
        # line: 3981
        oldpath = self._path_with_dir_fd(oldpath, self.link, dir_fd)
        # line: 3982
        self.filesystem.CreateHardLink(oldpath, newpath)

    # line: 3984
    def fsync(self, file_des):
        # line: 3994
        'Perform fsync for a fake file (in other words, do nothing).\n        New in pyfakefs 2.9.\n\n        Args:\n          file_des:  file descriptor of the open file.\n\n        Raises:\n          OSError: file_des is an invalid file descriptor.\n          TypeError: file_des is not an integer.\n        '
        # line: 3996
        self.filesystem.GetOpenFile(file_des)

    # line: 3998
    def fdatasync(self, file_des):
        # line: 4008
        'Perform fdatasync for a fake file (in other words, do nothing).\n        New in pyfakefs 2.9.\n\n        Args:\n          file_des:  file descriptor of the open file.\n\n        Raises:\n          OSError: file_des is an invalid file descriptor.\n          TypeError: file_des is not an integer.\n        '
        # line: 4010
        self.filesystem.GetOpenFile(file_des)

    # line: 4012
    def __getattr__(self, name):
        # line: 4013
        'Forwards any unfaked calls to the standard os module.'
        # line: 4014
        return getattr(self._os_module, name)


# line: 4017
class FakeIoModule(object):
    # line: 4026
    'Uses FakeFilesystem to provide a fake io module replacement.\n    New in pyfakefs 2.9.\n\n    Currently only used to wrap `io.open()` which is an alias to `open()`.\n\n    You need a fake_filesystem to use this:\n    filesystem = fake_filesystem.FakeFilesystem()\n    my_io_module = fake_filesystem.FakeIoModule(filesystem)\n    '

    # line: 4028
    def __init__(self, filesystem):
        # line: 4032
        '\n        Args:\n          filesystem:  FakeFilesystem used to provide file system information\n        '
        # line: 4033
        self.filesystem = filesystem
        # line: 4034
        self._io_module = io

    # line: 4036
    def open(self, file_path, mode='r', buffering=(-1), encoding=None, errors=None, newline=None, closefd=True, opener=None):
        # line: 4040
        'Redirect the call to FakeFileOpen.\n        See FakeFileOpen.Call() for description.\n        '
        # line: 4041
        if ((opener is not None) and (sys.version_info < (3, 3))):
            # line: 4042
            raise TypeError("open() got an unexpected keyword argument 'opener'")
        # line: 4043
        fake_open = FakeFileOpen(self.filesystem, use_io=True)
        # line: 4044
        return fake_open(file_path, mode, buffering, encoding, errors, newline, closefd, opener)

    # line: 4046
    def __getattr__(self, name):
        # line: 4047
        'Forwards any unfaked calls to the standard io module.'
        # line: 4048
        return getattr(self._io_module, name)


# line: 4051
class FakeFileWrapper(object):
    # line: 4056
    'Wrapper for a stream object for use by a FakeFile object.\n\n    If the wrapper has any data written to it, it will propagate to\n    the FakeFile object on close() or flush().\n    '

    # line: 4057
    def __init__(self, file_object, file_path, update=False, read=False, append=False, delete_on_close=False, filesystem=None, newline=None, binary=True, closefd=True, encoding=None, errors=None, raw_io=False, is_stream=False, use_io=True):
        # line: 4061
        self._file_object = file_object
        # line: 4062
        self._file_path = file_path
        # line: 4063
        self._append = append
        # line: 4064
        self._read = read
        # line: 4065
        self.allow_update = update
        # line: 4066
        self._closefd = closefd
        # line: 4067
        self._file_epoch = file_object.epoch
        # line: 4068
        self.raw_io = raw_io
        # line: 4069
        self._binary = binary
        # line: 4070
        self.is_stream = is_stream
        # line: 4071
        contents = file_object.byte_contents
        # line: 4072
        self._encoding = encoding
        # line: 4073
        errors = (errors or 'strict')
        # line: 4074
        if encoding:
            # line: 4075
            file_wrapper = FakeFileWrapper(file_object, file_path, update, read, append, delete_on_close=False, filesystem=filesystem, newline=None, binary=True, closefd=closefd, is_stream=True)
            # line: 4079
            codec_info = codecs.lookup(encoding)
            # line: 4080
            self._io = codecs.StreamReaderWriter(file_wrapper, codec_info.streamreader, codec_info.streamwriter, errors)
        else:
            # line: 4083
            if ((not binary) and (sys.version_info >= (3, 0))):
                # line: 4084
                io_class = io.StringIO
            else:
                # line: 4086
                io_class = io.BytesIO
            # line: 4087
            io_args = ({} if binary else {'newline': newline, })
            # line: 4088
            if (contents and (not binary)):
                # line: 4089
                contents = contents.decode((encoding or locale.getpreferredencoding(False)), errors=errors)
            # line: 4091
            if (contents and (not update)):
                # line: 4092
                self._io = io_class(contents, **io_args)
            else:
                # line: 4094
                self._io = io_class(**io_args)
        # line: 4096
        if contents:
            # line: 4097
            if update:
                # line: 4098
                if (not encoding):
                    # line: 4099
                    self._io.write(contents)
                # line: 4100
                if (not append):
                    # line: 4101
                    self._io.seek(0)
                else:
                    # line: 4103
                    self._read_whence = 0
                    # line: 4104
                    if (read and (not use_io)):
                        # line: 4105
                        self._read_seek = 0
                    else:
                        # line: 4107
                        self._read_seek = self._io.tell()
        else:
            # line: 4109
            self._read_whence = 0
            # line: 4110
            self._read_seek = 0
        # line: 4112
        if delete_on_close:
            # line: 4113
            assert filesystem, 'delete_on_close=True requires filesystem'
        # line: 4114
        self._filesystem = filesystem
        # line: 4115
        self.delete_on_close = delete_on_close
        # line: 4118
        self.name = file_object.opened_as
        # line: 4119
        self.filedes = None

    # line: 4121
    def __enter__(self):
        # line: 4122
        "To support usage of this fake file with the 'with' statement."
        # line: 4123
        return self

    # line: 4125
    def __exit__(self, type, value, traceback):
        # line: 4126
        "To support usage of this fake file with the 'with' statement."
        # line: 4127
        self.close()

    # line: 4129
    def _raise(self, message):
        # line: 4130
        if self.raw_io:
            # line: 4131
            raise OSError(errno.EBADF, message)
        # line: 4132
        if (sys.version_info < (3, 0)):
            # line: 4133
            raise IOError(message)
        # line: 4134
        raise io.UnsupportedOperation(message)

    # line: 4136
    def GetObject(self):
        # line: 4137
        'Return the FakeFile object that is wrapped by the current instance.'
        # line: 4138
        return self._file_object

    # line: 4140
    def fileno(self):
        # line: 4141
        'Return the file descriptor of the file object.'
        # line: 4142
        return self.filedes

    # line: 4144
    def close(self):
        # line: 4145
        'Close the file.'
        # line: 4147
        if (self not in self._filesystem.open_files):
            # line: 4148
            return
        # line: 4150
        if (self.allow_update and (not self.raw_io)):
            # line: 4151
            self._file_object.SetContents(self._io.getvalue(), self._encoding)
        # line: 4152
        if self._closefd:
            # line: 4153
            self._filesystem.CloseOpenFile(self.filedes)
        # line: 4154
        if self.delete_on_close:
            # line: 4155
            self._filesystem.RemoveObject(self.GetObject().GetPath())

    # line: 4157
    def flush(self):
        # line: 4158
        "Flush file contents to 'disk'."
        # line: 4159
        self._check_open_file()
        # line: 4160
        if self.allow_update:
            # line: 4161
            self._io.flush()
            # line: 4162
            self._file_object.SetContents(self._io.getvalue(), self._encoding)
            # line: 4163
            self._file_epoch = self._file_object.epoch

    # line: 4165
    def seek(self, offset, whence=0):
        # line: 4166
        "Move read/write pointer in 'file'."
        # line: 4167
        self._check_open_file()
        # line: 4168
        if (not self._append):
            # line: 4169
            self._io.seek(offset, whence)
        else:
            # line: 4171
            self._read_seek = offset
            # line: 4172
            self._read_whence = whence
        # line: 4173
        if (not self.is_stream):
            # line: 4174
            self.flush()

    # line: 4176
    def tell(self):
        # line: 4181
        "Return the file's current position.\n\n        Returns:\n          int, file's current position in bytes.\n        "
        # line: 4182
        self._check_open_file()
        # line: 4183
        self._flush_for_read()
        # line: 4184
        if (not self._append):
            # line: 4185
            return self._io.tell()
        # line: 4186
        if self._read_whence:
            # line: 4187
            write_seek = self._io.tell()
            # line: 4188
            self._io.seek(self._read_seek, self._read_whence)
            # line: 4189
            self._read_seek = self._io.tell()
            # line: 4190
            self._read_whence = 0
            # line: 4191
            self._io.seek(write_seek)
        # line: 4192
        return self._read_seek

    # line: 4194
    def _flush_for_read(self):
        # line: 4196
        if self._flushes_after_read():
            # line: 4197
            self.flush()

    # line: 4199
    def _flushes_after_read(self):
        # line: 4200
        return ((not self.is_stream) and ((not self._filesystem.is_windows_fs) or (sys.version_info[0] > 2)))

    # line: 4204
    def _sync_io(self):
        # line: 4205
        'Update the stream with changes to the file object contents.'
        # line: 4206
        if (self._file_epoch == self._file_object.epoch):
            # line: 4207
            return
        # line: 4209
        if isinstance(self._io, io.BytesIO):
            # line: 4210
            contents = self._file_object.byte_contents
        else:
            # line: 4212
            contents = self._file_object.contents
        # line: 4214
        is_stream_reader_writer = isinstance(self._io, codecs.StreamReaderWriter)
        # line: 4215
        if is_stream_reader_writer:
            # line: 4216
            self._io.stream.allow_update = True
        # line: 4217
        whence = self._io.tell()
        # line: 4218
        self._io.seek(0)
        # line: 4219
        self._io.truncate()
        # line: 4220
        self._io.write(contents)
        # line: 4221
        if self._append:
            # line: 4222
            self._io.seek(0, os.SEEK_END)
        else:
            # line: 4224
            self._io.seek(whence)
        # line: 4226
        if is_stream_reader_writer:
            # line: 4227
            self._io.stream.allow_update = False
        # line: 4228
        self._file_epoch = self._file_object.epoch

    # line: 4230
    def _ReadWrapper(self, name):
        # line: 4241
        'Wrap a stream attribute in a read wrapper.\n\n        Returns a read_wrapper which tracks our own read pointer since the\n        stream object has no concept of a different read and write pointer.\n\n        Args:\n          name: the name of the attribute to wrap.  Should be a read call.\n\n        Returns:\n          either a read_error or read_wrapper function.\n        '
        # line: 4242
        io_attr = getattr(self._io, name)

        # line: 4244
        def read_wrapper(*args, **kwargs):
            # line: 4256
            "Wrap all read calls to the stream object.\n\n            We do this to track the read pointer separate from the write\n            pointer.  Anything that wants to read from the stream object\n            while we're in append mode goes through this.\n\n            Args:\n              *args: pass through args\n              **kwargs: pass through kwargs\n            Returns:\n              Wrapped stream object method\n            "
            # line: 4257
            self._io.seek(self._read_seek, self._read_whence)
            # line: 4258
            ret_value = io_attr(*args, **kwargs)
            # line: 4259
            self._read_seek = self._io.tell()
            # line: 4260
            self._read_whence = 0
            # line: 4261
            self._io.seek(0, 2)
            # line: 4262
            return ret_value
        # line: 4264
        return read_wrapper

    # line: 4266
    def _OtherWrapper(self, name, writing):
        # line: 4274
        'Wrap a stream attribute in an other_wrapper.\n\n        Args:\n          name: the name of the stream attribute to wrap.\n\n        Returns:\n          other_wrapper which is described below.\n        '
        # line: 4275
        io_attr = getattr(self._io, name)

        # line: 4277
        def other_wrapper(*args, **kwargs):
            # line: 4289
            'Wrap all other calls to the stream Object.\n\n            We do this to track changes to the write pointer.  Anything that\n            moves the write pointer in a file open for appending should move\n            the read pointer as well.\n\n            Args:\n              *args: pass through args\n              **kwargs: pass through kwargs\n            Returns:\n              Wrapped stream object method\n            '
            # line: 4290
            write_seek = self._io.tell()
            # line: 4291
            ret_value = io_attr(*args, **kwargs)
            # line: 4292
            if (write_seek != self._io.tell()):
                # line: 4293
                self._read_seek = self._io.tell()
                # line: 4294
                self._read_whence = 0
            # line: 4295
            if ((not writing) or (sys.version_info >= (3,))):
                # line: 4296
                return ret_value
        # line: 4298
        return other_wrapper

    # line: 4300
    def _TruncateWrapper(self):
        # line: 4305
        'Wrap truncate() to allow flush after truncate.\n\n        Returns:\n          wrapper which is described below.\n        '
        # line: 4306
        io_attr = getattr(self._io, 'truncate')

        # line: 4308
        def truncate_wrapper(*args, **kwargs):
            # line: 4309
            'Wrap truncate call to call flush after truncate.'
            # line: 4310
            if self._append:
                # line: 4311
                self._io.seek(self._read_seek, self._read_whence)
            # line: 4312
            size = io_attr(*args, **kwargs)
            # line: 4313
            self.flush()
            # line: 4314
            if (not self.is_stream):
                # line: 4315
                self._file_object.SetSize(size)
                # line: 4316
                buffer_size = len(self._io.getvalue())
                # line: 4317
                if (buffer_size < size):
                    # line: 4318
                    self._io.seek(buffer_size)
                    # line: 4319
                    self._io.write(('\x00' * (size - buffer_size)))
                    # line: 4320
                    self._file_object.SetContents(self._io.getvalue(), self._encoding)
            # line: 4321
            if (sys.version_info >= (3,)):
                # line: 4322
                return size
        # line: 4324
        return truncate_wrapper

    # line: 4326
    def _WriteWrapper(self, name):
        # line: 4331
        'Wrap write() to adapt return value for Python 2.\n\n        Returns:\n          wrapper which is described below.\n        '
        # line: 4332
        io_attr = getattr(self._io, name)

        # line: 4334
        def write_wrapper(*args, **kwargs):
            # line: 4335
            'Wrap trunctae call to call flush after truncate.'
            # line: 4336
            ret_value = io_attr(*args, **kwargs)
            # line: 4337
            if (sys.version_info >= (3,)):
                # line: 4338
                return ret_value
        # line: 4340
        return write_wrapper

    # line: 4342
    def Size(self):
        # line: 4343
        'Return the content size in bytes of the wrapped file.'
        # line: 4344
        return self._file_object.st_size

    # line: 4346
    def __getattr__(self, name):
        # line: 4347
        if self._file_object.IsLargeFile():
            # line: 4348
            raise FakeLargeFileIoException(self._file_path)
        # line: 4350
        reading = (name.startswith('read') or (name == 'next'))
        # line: 4351
        truncate = (name == 'truncate')
        # line: 4352
        writing = (name.startswith('write') or truncate)
        # line: 4353
        if (reading or writing):
            # line: 4354
            self._check_open_file()
        # line: 4355
        if ((not self._read) and reading):

            # line: 4356
            def read_error(*args, **kwargs):
                # line: 4357
                'Throw an error unless the argument is zero.'
                # line: 4358
                if (args and (args[0] == 0)):
                    # line: 4359
                    if (self._filesystem.is_windows_fs and self.raw_io):
                        # line: 4360
                        return ('' if self._binary else u'')
                # line: 4361
                self._raise('File is not open for reading.')
            # line: 4363
            return read_error
        # line: 4365
        if ((not self.allow_update) and writing):

            # line: 4366
            def write_error(*args, **kwargs):
                # line: 4367
                'Throw an error.'
                # line: 4368
                if self.raw_io:
                    # line: 4369
                    if (self._filesystem.is_windows_fs and args and (len(args[0]) == 0)):
                        # line: 4370
                        return 0
                # line: 4371
                self._raise('File is not open for writing.')
            # line: 4373
            return write_error
        # line: 4375
        if reading:
            # line: 4376
            self._sync_io()
            # line: 4377
            self._flush_for_read()
        # line: 4378
        if truncate:
            # line: 4379
            return self._TruncateWrapper()
        # line: 4380
        if self._append:
            # line: 4381
            if reading:
                # line: 4382
                return self._ReadWrapper(name)
            else:
                # line: 4384
                return self._OtherWrapper(name, writing)
        # line: 4385
        if writing:
            # line: 4386
            return self._WriteWrapper(name)
        # line: 4388
        return getattr(self._io, name)

    # line: 4390
    def _check_open_file(self):
        # line: 4391
        if ((not self.is_stream) and (not (self in self._filesystem.open_files))):
            # line: 4392
            raise ValueError('I/O operation on closed file')

    # line: 4394
    def __iter__(self):
        # line: 4395
        if (not self._read):
            # line: 4396
            self._raise('File is not open for reading')
        # line: 4397
        return self._io.__iter__()


# line: 4400
class FakeDirWrapper(object):
    # line: 4402
    'Wrapper for a FakeDirectory object to be used in open files list.\n    '

    # line: 4403
    def __init__(self, file_object, file_path, filesystem):
        # line: 4404
        self._file_object = file_object
        # line: 4405
        self._file_path = file_path
        # line: 4406
        self._filesystem = filesystem
        # line: 4407
        self.filedes = None

    # line: 4409
    def GetObject(self):
        # line: 4410
        'Return the FakeFile object that is wrapped by the current instance.'
        # line: 4411
        return self._file_object

    # line: 4413
    def fileno(self):
        # line: 4414
        'Return the file descriptor of the file object.'
        # line: 4415
        return self.filedes

    # line: 4417
    def close(self):
        # line: 4418
        'Close the directory.'
        # line: 4419
        self._filesystem.CloseOpenFile(self.filedes)


# line: 4422
class FakeFileOpen(object):
    # line: 4427
    'Faked `file()` and `open()` function replacements.\n\n    Returns FakeFile objects in a FakeFilesystem in place of the `file()`\n    or `open()` function.\n    '
    # line: 4428
    __name__ = 'FakeFileOpen'

    # line: 4430
    def __init__(self, filesystem, delete_on_close=False, use_io=False, raw_io=False):
        # line: 4438
        'init.\n\n        Args:\n          filesystem:  FakeFilesystem used to provide file system information\n          delete_on_close:  optional boolean, deletes file on close()\n          use_io: if True, the io.open() version is used (ignored for Python 3,\n                  where io.open() is an alias to open() )\n        '
        # line: 4439
        self.filesystem = filesystem
        # line: 4440
        self._delete_on_close = delete_on_close
        # line: 4441
        self._use_io = (use_io or (sys.version_info >= (3, 0)) or (platform.python_implementation() == 'PyPy'))
        # line: 4443
        self.raw_io = raw_io

    # line: 4445
    def __call__(self, *args, **kwargs):
        # line: 4446
        'Redirects calls to file() or open() to appropriate method.'
        # line: 4447
        if self._use_io:
            # line: 4448
            return self.Call(*args, **kwargs)
        else:
            # line: 4450
            return self._call_ver2(*args, **kwargs)

    # line: 4452
    def _call_ver2(self, file_path, mode='r', buffering=(-1), flags=None, open_modes=None):
        # line: 4453
        'Limits args of open() or file() for Python 2.x versions.'
        # line: 4455
        mode = (flags or mode)
        # line: 4456
        return self.Call(file_path, mode, buffering, open_modes=open_modes)

    # line: 4458
    def Call(self, file_, mode='r', buffering=(-1), encoding=None, errors=None, newline=None, closefd=True, opener=None, open_modes=None):
        # line: 4484
        "Return a file-like object with the contents of the target file object.\n\n        Args:\n          file_: path to target file or a file descriptor.\n          mode: additional file modes. All r/w/a/x r+/w+/a+ modes are supported.\n            't', and 'U' are ignored, e.g., 'wU' is treated as 'w'. 'b' sets\n            binary mode, no end of line translations in StringIO.\n          buffering: ignored. (Used for signature compliance with __builtin__.open)\n          encoding: the encoding used to encode unicode strings / decode bytes.\n          New in pyfakefs 2.9.\n          errors: ignored, this relates to encoding.\n          newline: controls universal newlines, passed to stream object.\n          closefd: if a file descriptor rather than file name is passed, and set\n            to false, then the file descriptor is kept open when file is closed.\n          opener: not supported.\n          open_modes: Modes for opening files if called from low-level API\n\n        Returns:\n          a file-like object containing the contents of the target file.\n\n        Raises:\n          IOError: if the target object is a directory, the path is invalid or\n            permission is denied.\n        "
        # line: 4485
        orig_modes = mode
        # line: 4487
        binary = ((sys.version_info < (3, 0)) or ('b' in mode))
        # line: 4489
        mode = mode.replace('t', '').replace('b', '')
        # line: 4490
        mode = mode.replace('rU', 'r').replace('U', 'r')
        # line: 4492
        if (not self.raw_io):
            # line: 4493
            if (mode not in _OPEN_MODE_MAP):
                # line: 4494
                raise ValueError(('Invalid mode: %r' % orig_modes))
            # line: 4495
            open_modes = _OpenModes(*_OPEN_MODE_MAP[mode])
        # line: 4497
        file_object = None
        # line: 4498
        filedes = None
        # line: 4500
        if isinstance(file_, int):
            # line: 4501
            filedes = file_
            # line: 4502
            wrapper = self.filesystem.GetOpenFile(filedes)
            # line: 4503
            self._delete_on_close = wrapper.delete_on_close
            # line: 4504
            file_object = self.filesystem.GetOpenFile(filedes).GetObject()
            # line: 4505
            file_path = file_object.name
        else:
            # line: 4507
            file_path = file_
            # line: 4508
            real_path = self.filesystem.ResolvePath(file_path, raw_io=self.raw_io)
            # line: 4509
            if self.filesystem.Exists(file_path):
                # line: 4510
                file_object = self.filesystem.GetObjectFromNormalizedPath(real_path)
            # line: 4511
            closefd = True
        # line: 4513
        error_class = (OSError if self.raw_io else IOError)
        # line: 4514
        if (open_modes.must_not_exist and (file_object or self.filesystem.IsLink(file_path))):
            # line: 4515
            raise error_class(errno.EEXIST, 'File exists', file_path)
        # line: 4516
        if file_object:
            # line: 4517
            if ((open_modes.can_read and (not (file_object.st_mode & PERM_READ))) or (open_modes.can_write and (not (file_object.st_mode & PERM_WRITE)))):
                # line: 4519
                raise error_class(errno.EACCES, 'Permission denied', file_path)
            # line: 4520
            if open_modes.can_write:
                # line: 4521
                if open_modes.truncate:
                    # line: 4522
                    file_object.SetContents('')
        else:
            # line: 4524
            if open_modes.must_exist:
                # line: 4525
                raise error_class(errno.ENOENT, 'No such file or directory', file_path)
            # line: 4526
            file_object = self.filesystem.CreateFileInternally(real_path, create_missing_dirs=False, apply_umask=True, raw_io=self.raw_io)
        # line: 4529
        if stat.S_ISDIR(file_object.st_mode):
            # line: 4530
            if self.filesystem.is_windows_fs:
                # line: 4531
                raise OSError(errno.EPERM, 'Fake file object: is a directory', file_path)
            else:
                # line: 4533
                raise error_class(errno.EISDIR, 'Fake file object: is a directory', file_path)
        # line: 4537
        file_object.opened_as = file_path
        # line: 4539
        fakefile = FakeFileWrapper(file_object, file_path, update=open_modes.can_write, read=open_modes.can_read, append=open_modes.append, delete_on_close=self._delete_on_close, filesystem=self.filesystem, newline=newline, binary=binary, closefd=closefd, encoding=encoding, errors=errors, raw_io=self.raw_io, use_io=self._use_io)
        # line: 4553
        if (filedes is not None):
            # line: 4554
            fakefile.filedes = filedes
            # line: 4556
            self.filesystem.open_files[filedes] = fakefile
        else:
            # line: 4558
            fakefile.filedes = self.filesystem.AddOpenFile(fakefile)
        # line: 4559
        return fakefile

# line: 4562
def _RunDoctest():
    # line: 4563
    import doctest
    # line: 4564
    from pyfakefs import fake_filesystem
    # line: 4565
    return doctest.testmod(fake_filesystem)
# line: 4568
if (__name__ == '__main__'):
    # line: 4569
    _RunDoctest()