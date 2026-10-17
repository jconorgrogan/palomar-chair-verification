"""Local-only frozen native loader. No transport object or executable authority.

The original graph is read, never copied over or modified. The parent supplies a
canonical clean read-only checkout root once; the same exact38-file pins apply.
"""
from __future__ import annotations
import hashlib
import importlib.util
import inspect
import json
import os
from collections.abc import Mapping
from pathlib import Path
import stat
import sys
import threading
import types

DEFAULT_ROOT = Path('/tmp/modern_c_active_consumer_20261016T2033/pipeline')
ROOT = None
GRAPH = None
PINS_FILE = Path(__file__).resolve().parents[1] / 'inputs/FROZEN_GRAPH.json'
PINS_SHA256 = '348c13eccdf26627a8afbad190ceff9e2a56436d38cc8568cf72cecce8de4697'
LOAD_ORDER = ('fresh_stage', 'three_context_policy', 'three_context_local',
              'checked_transfer', 'three_context_final', 'three_context_execution_policy',
              'three_context_current_transport', 'three_context_runner')

class Rejected(ValueError):
    pass

def need(ok, message):
    if not ok:
        raise Rejected(message)

def digest(raw):
    return hashlib.sha256(raw).hexdigest()

def regular(path):
    need(path.is_absolute() and '..' not in path.parts, 'canonical absolute path required')
    for part in (path, *path.parents):
        need(not part.is_symlink(), 'symlink frozen path')
    st = path.lstat()
    need(stat.S_ISREG(st.st_mode) and st.st_nlink == 1, 'single-link frozen regular file required')
    return st

def read_verified(path, pin):
    before = regular(path)
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
    try:
        opened = os.fstat(fd)
        need((before.st_dev,before.st_ino,before.st_size) == (opened.st_dev,opened.st_ino,opened.st_size),
             'frozen source replaced before open')
        with os.fdopen(fd, 'rb', closefd=False) as stream:
            raw = stream.read(pin['bytes']+1)
        after = os.fstat(fd)
        need((opened.st_dev,opened.st_ino,opened.st_size,opened.st_mtime_ns,opened.st_ctime_ns,opened.st_nlink) ==
             (after.st_dev,after.st_ino,after.st_size,after.st_mtime_ns,after.st_ctime_ns,after.st_nlink),
             'frozen source changed during read')
        need(len(raw) == pin['bytes'] and digest(raw) == pin['sha256'], 'frozen compile buffer pin mismatch')
        return raw
    finally:
        os.close(fd)


def reject_bytecode(event, args):
    # Permanent and fail-closed. SourceFileLoader treats this as a cache miss;
    # it may execute only the separately hash-checked source bytes thereafter.
    if event == 'open' and args and isinstance(args[0], (str, bytes, os.PathLike)):
        if os.fsdecode(args[0]).endswith(('.pyc', '.pyo')):
            raise FileNotFoundError('bytecode execution forbidden in native admission')


def freeze_value(value):
    if isinstance(value, Mapping):
        return ('map', tuple(sorted((repr(k), freeze_value(v)) for k, v in value.items())))
    if type(value) in (list, tuple):
        return (type(value).__name__, tuple(freeze_value(v) for v in value))
    if type(value) in (set, frozenset):
        return (type(value).__name__, tuple(sorted(repr(freeze_value(v)) for v in value)))
    if type(value) in (str, bytes, int, float, bool, type(None)):
        return (type(value).__name__, value)
    return ('reference', id(value))


class FrozenGraph:
    def __init__(self, root):
        self.root = root
        self._root_text = str(root)
        need(threading.current_thread() is threading.main_thread() and threading.active_count() == 1,
             'single exclusive main thread required')
        regular(PINS_FILE)
        raw = PINS_FILE.read_bytes()
        need(digest(raw) == PINS_SHA256, 'frozen graph manifest changed')
        self.pins_raw = raw
        self.pins = json.loads(raw)
        self.loaded = {}
        self.functions = []
        self.bindings = []
        self.constants = []
        self.verify_files()
        need(not any(name in sys.modules for name in LOAD_ORDER), 'native aliases already populated')
        sys.addaudithook(reject_bytecode)
        old_bytecode = sys.dont_write_bytecode
        sys.dont_write_bytecode = True
        try:
            for name in LOAD_ORDER:
                path = self.root / 'ci' / (name + '.py')
                spec = importlib.util.spec_from_file_location(name, path)
                module = importlib.util.module_from_spec(spec)
                sys.modules[name] = module
                raw_source = read_verified(path, self.pins['files']['ci/'+name+'.py'])
                exec(compile(raw_source, str(path), 'exec', dont_inherit=True), module.__dict__)
                need(Path(module.__file__) == path, 'wrong native loaded path')
                self.loaded[name] = module
        except BaseException:
            for name, module in self.loaded.items():
                if sys.modules.get(name) is module:
                    sys.modules.pop(name, None)
            raise
        finally:
            sys.dont_write_bytecode = old_bytecode
        self.f = self.loaded['fresh_stage']
        self.p = self.loaded['three_context_policy']
        self.local = self.loaded['three_context_local']
        self.transfer = self.loaded['checked_transfer']
        self.ep = self.loaded['three_context_execution_policy']
        self.runner = self.loaded['three_context_runner']
        current = self.loaded['three_context_current_transport']
        all_modules = [*self.loaded.values(), *current._loaded.values()]
        seen = set()
        for module in all_modules:
            if id(module) in seen:
                continue
            seen.add(id(module))
            path = Path(module.__file__)
            need(path.parent == self.root/'ci' and path.relative_to(self.root).as_posix() in self.pins['files'],
                 'unexpected nested module path')
            self.bindings.append((module, '__file__', module.__file__))
            for key, value in vars(module).copy().items():
                if key != '__builtins__' and not (module is self.transfer and key in {'_ADMISSIONS','_TARGETS','_TRANSFERS'}):
                    self.constants.append((module, key, freeze_value(value)))
                if isinstance(value, (types.ModuleType, types.FunctionType, type)):
                    self.bindings.append((module, key, value))
                if inspect.isfunction(value) and value.__module__ == module.__name__:
                    self.capture_function(value, path)
                if isinstance(value, type) and value.__module__ == module.__name__:
                    for member_name, member in vars(value).copy().items():
                        if isinstance(member, (types.FunctionType, staticmethod, classmethod, property)):
                            self.bindings.append((value, member_name, inspect.getattr_static(value, member_name)))
                        if isinstance(member, (staticmethod, classmethod)):
                            member = member.__func__
                        if inspect.isfunction(member):
                            self.capture_function(member, path)
        self.verify()

    def capture_function(self, fn, path):
        original = inspect.unwrap(fn)
        need(Path(original.__code__.co_filename) == path or original.__code__.co_filename == '<string>' or
             Path(original.__code__.co_filename).name == 'dataclasses.py', 'native function code loaded from wrong path: '+fn.__qualname__)
        if original is not fn:
            self.functions.append((original, original.__code__, digest(original.__code__.co_code), original.__defaults__, original.__kwdefaults__, freeze_value(original.__defaults__), freeze_value(original.__kwdefaults__)))
        self.functions.append((fn, fn.__code__, digest(fn.__code__.co_code), fn.__defaults__, fn.__kwdefaults__, freeze_value(fn.__defaults__), freeze_value(fn.__kwdefaults__)))

    def verify_files(self):
        need(str(self.root) == self._root_text, 'loaded root binding changed')
        need(digest(self.pins_raw) == PINS_SHA256 and self.pins == json.loads(self.pins_raw), 'in-memory graph pins changed')
        regular(PINS_FILE)
        need(digest(PINS_FILE.read_bytes()) == PINS_SHA256, 'frozen manifest replaced')
        actual = set()
        for path in self.root.rglob('*'):
            relative = path.relative_to(self.root).as_posix()
            if relative == '.git' or relative.startswith('.git/'):
                continue  # Parent authenticates clean checkout identity separately.
            need(not path.is_symlink(), 'symlink in frozen source graph')
            if path.is_file():
                if self.root == DEFAULT_ROOT and relative == 'ci/__pycache__/fresh_stage.cpython-312.pyc':
                    continue  # Preserved existing local evidence; never opened.
                actual.add(relative)
        need(actual == set(self.pins['files']), 'frozen complete38-file source graph changed')
        for name, pin in self.pins['files'].items():
            path = self.root / name
            need(regular(path).st_size == pin['bytes'] and digest(path.read_bytes()) == pin['sha256'],
                 'frozen implementation bytes changed: ' + name)

    def verify(self):
        self.verify_files()
        for name, module in self.loaded.items():
            need(sys.modules.get(name) is module, 'native import alias changed: ' + name)
        for obj, key, value in self.bindings:
            actual = inspect.getattr_static(obj, key) if isinstance(obj, type) else getattr(obj, key)
            need(actual == value if key == '__file__' else actual is value, 'native global binding changed: '+key)
        for module, key, frozen in self.constants:
            need(freeze_value(getattr(module, key)) == frozen, 'native constant/mapping changed: '+key)
        for fn, code, sha, defaults, kwdefaults, frozen_defaults, frozen_kwdefaults in self.functions:
            need(fn.__code__ is code and digest(fn.__code__.co_code) == sha and
                 fn.__defaults__ is defaults and fn.__kwdefaults__ is kwdefaults and
                 freeze_value(fn.__defaults__) == frozen_defaults and freeze_value(fn.__kwdefaults__) == frozen_kwdefaults,
                 'native method implementation changed: ' + fn.__qualname__)
        r = self.runner
        need(r.f is self.f and r.p is self.p and r.ep is self.ep and r.local is self.local and
             r.transfer is self.transfer and self.ep.f is self.f and self.ep.p is self.p,
             'native reference graph changed')
        for name in ('_native_inputs', '_current_envelope', '_restore_scope', 'check_run_age', '_for_runner', '__init__'):
            fn = getattr(r.ThreeContextRunner, name)
            key = 'ci/three_context_runner.py:' + name
            need(digest(inspect.getsource(fn).encode()) == self.pins['methods'][key]['sha256'],
                 'native exact method source changed: '+name)

def load_frozen_graph(canonical_root):
    """Explicit one-time parent bootstrap. No environment fallback or root switch."""
    global GRAPH, ROOT
    need(type(canonical_root) is str and canonical_root.startswith('/') and
         str(Path(canonical_root)) == canonical_root and '..' not in Path(canonical_root).parts,
         'explicit canonical absolute native root required')
    root = Path(canonical_root)
    for part in (root, *root.parents):
        need(not part.is_symlink(), 'symlink native root')
    need(root.is_dir(), 'native checkout directory required')
    if GRAPH is not None:
        need(GRAPH.root == root, 'native graph root cannot be changed')
        GRAPH.verify()
        return GRAPH
    ROOT = root
    GRAPH = FrozenGraph(root)
    return GRAPH
