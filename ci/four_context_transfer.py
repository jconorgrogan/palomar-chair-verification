"""Inactive local-only historical transfer. No CLI, network, build, or activation.

Trusted caller contract: the future adapter authenticates the request hash and its
four-context selection, and exclusively controls this single-threaded process and
owned workspaces. This is an accidental-misuse boundary, not a Python sandbox.
There is deliberately no API accepting an admission result, validator callback,
success JSON, or deserialized capability. The fixed native path is always called.
"""
from __future__ import annotations
from contextlib import contextmanager
from dataclasses import dataclass
from datetime import datetime, timezone
import copy
import ctypes
import hashlib
import importlib.util
import json
import math
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import stat
import sys
import time
import threading
from types import MappingProxyType

FIXED_PINS = MappingProxyType({
    'code/three_context_admit.py': '22bfd7948df693307e9e5b094705f102e24b9c286d48c2c02a5fb6b95fc2bb2b',
    'code/three_context_local.py': '0ea2d6be51208e03248f5dd062b57c85bbc6b5768d156b27032891c15d10a06a',
    'code/three_context_policy.py': 'edc4852bcfe3cd8ca980733229859c98ca20fb7120edddaa61f0c55ed19f53d4',
    'inputs/PRIOR_FILES.json': '9618bc2900517a9234254ddf2a2ea6fb3c78f643bd12f11967f986f49e7dde1d',
})
SUFFIXES = ('.olean', '.olean.private', '.olean.server', '.ilean', '.ir', '.ir.sig')
SCAFFOLD = frozenset({'objects', 'scratch', 'scratch/home', 'scratch/tmp', 'logs', 'module-quarantine'})
MARKER = 'historical-transfer-state.json'
CERTIFICATE = 'historical-transfer-certificate.json'
_ADMISSIONS = {}
_TARGETS = {}
_TRANSFERS = {}

class Rejected(ValueError): pass

def need(ok, message):
    if not ok: raise Rejected(message)

def raw_json(value):
    return (json.dumps(value, sort_keys=True, indent=2, allow_nan=False) + '\n').encode()

def parse(raw):
    need(type(raw) is bytes and len(raw) <= 64 * 1024**2, 'bounded immutable JSON bytes required')
    def pairs(items):
        out = {}
        for key, value in items:
            need(key not in out, 'duplicate JSON key'); out[key] = value
        return out
    return json.loads(raw, object_pairs_hook=pairs, parse_constant=lambda _: (_ for _ in ()).throw(Rejected('nonfinite JSON')))

def digest(raw): return hashlib.sha256(raw).hexdigest()

def canonical(value):
    need(type(value) is str and value.startswith('/') and str(Path(value)) == value and '..' not in Path(value).parts, 'canonical absolute root required')
    path = Path(value)
    for part in (path, *path.parents): need(not part.is_symlink(), 'symlink path forbidden')
    return path

def relative(value):
    need(type(value) is str and value and '\\' not in value and '\x00' not in value, 'invalid relative name')
    p = PurePosixPath(value)
    need(not p.is_absolute() and str(p) == value and all(x not in ('', '.', '..') for x in p.parts), 'noncanonical relative name')
    return value

def single_thread():
    need(threading.current_thread() is threading.main_thread() and threading.active_count() == 1, 'exclusive single main thread required')

def owned_dir(path):
    canonical(str(path)); s = path.lstat()
    need(stat.S_ISDIR(s.st_mode) and s.st_uid == os.geteuid() and s.st_mode & 0o022 == 0, 'owned non-shared directory required')
    return s.st_dev, s.st_ino

def _open_directory(path):
    """Walk every component with O_NOFOLLOW, retaining a directory FD."""
    canonical(str(path)); fd = os.open('/', os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    try:
        for part in path.parts[1:]:
            child = os.open(part, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=fd)
            os.close(fd); fd = child
        return fd
    except BaseException:
        os.close(fd); raise


def _mkdir_owned_under(root, relative_parent):
    fd = _open_directory(root)
    try:
        for part in PurePosixPath(relative_parent).parts:
            if part == '.': continue
            relative(part)
            try: os.mkdir(part, 0o700, dir_fd=fd)
            except FileExistsError: pass
            child = os.open(part, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=fd)
            st = os.fstat(child)
            if not (st.st_uid == os.geteuid() and st.st_mode & 0o022 == 0):
                os.close(child); raise Rejected('shared/unowned destination directory')
            os.close(fd); fd = child
    finally: os.close(fd)


def info(path):
    canonical(str(path)); before = path.lstat()
    need(stat.S_ISREG(before.st_mode) and before.st_nlink == 1 and before.st_uid == os.geteuid(), 'owned regular single-link file required')
    parent_fd = _open_directory(path.parent)
    try: fd = os.open(path.name, os.O_RDONLY | os.O_NOFOLLOW, dir_fd=parent_fd)
    finally: os.close(parent_fd)
    try:
        opened = os.fstat(fd)
        need((opened.st_dev, opened.st_ino) == (before.st_dev, before.st_ino), 'file replaced before open')
        h = hashlib.sha256()
        while True:
            block = os.read(fd, 1024**2)
            if not block: break
            h.update(block)
        after = os.fstat(fd)
        need((before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns, before.st_ctime_ns, before.st_nlink) ==
             (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns, after.st_ctime_ns, after.st_nlink), 'file changed during hash')
        now = path.lstat()
        need((now.st_dev, now.st_ino, now.st_nlink) == (after.st_dev, after.st_ino, 1), 'file replaced/shared after hash')
        return {'bytes': after.st_size, 'sha256': h.hexdigest()}
    finally: os.close(fd)

def tree(root, *, empty_dirs=frozenset()):
    owned_dir(root); files = {}; dirs = set()
    for parent, names, leafs in os.walk(root, followlinks=False):
        for name in names:
            p = Path(parent) / name; owned_dir(p); dirs.add(p.relative_to(root).as_posix())
        for name in leafs:
            p = Path(parent) / name; rel = relative(p.relative_to(root).as_posix()); files[rel] = info(p)
    allowed = {str(p) for name in files for p in PurePosixPath(name).parents if str(p) != '.'} | set(empty_dirs)
    need(dirs == allowed, 'unexpected/missing directory')
    return files

def disjoint(a, b):
    need(a != b and a not in b.parents and b not in a.parents, 'overlapping roots')

def check_fixed_files(admission_root=Path('/tmp/modern_c_three_context_adapter_20261016T1809'), historical_root=Path('/tmp/modern_c_metadata_retry_release_20261016T1432/pipeline')):
    admission_root = canonical(str(admission_root)); historical_root = canonical(str(historical_root))
    for name, pin in FIXED_PINS.items(): need(info(admission_root / name)['sha256'] == pin, 'fixed admission implementation pin changed')
    expected = parse((admission_root / 'inputs/PRIOR_FILES.json').read_bytes())
    need(tree(historical_root / 'ci') == {n[3:]: i for n, i in expected.items() if n.startswith('ci/')}, 'fixed historical implementation tree changed')
    for name, pin in expected.items(): need(info(historical_root / name) == pin, 'fixed historical source changed')

@contextmanager
def _fixed_native(admission_root=Path('/tmp/modern_c_three_context_adapter_20261016T1809'), historical_root=Path('/tmp/modern_c_metadata_retry_release_20261016T1432/pipeline')):
    """Fresh, fixed path/hash imports; no caller-supplied callables or module maps."""
    single_thread(); admission_root = canonical(str(admission_root)); historical_root = canonical(str(historical_root)); check_fixed_files(admission_root, historical_root)
    names = ('three_context_admit', 'three_context_local', 'three_context_policy')
    prior = {name: sys.modules.get(name) for name in names}
    old_bytecode = sys.dont_write_bytecode; sys.dont_write_bytecode = True
    try:
        for name in names: sys.modules.pop(name, None)
        path = admission_root / 'code/three_context_admit.py'
        spec = importlib.util.spec_from_file_location('three_context_admit', path)
        module = importlib.util.module_from_spec(spec); sys.modules['three_context_admit'] = module
        spec.loader.exec_module(module)
        files = parse((admission_root / 'inputs/PRIOR_FILES.json').read_bytes())
        with module.l.frozen_prior(historical_root, files) as native:
            yield module, native
        check_fixed_files(admission_root, historical_root)
    finally:
        sys.dont_write_bytecode = old_bytecode
        for name in names:
            if prior[name] is None: sys.modules.pop(name, None)
            else: sys.modules[name] = prior[name]

@dataclass(frozen=True, slots=True, init=False, eq=False)
class CheckedAdmission:
    """Process-local, immutable, one-shot; cannot be reconstructed from JSON."""
    binding_sha256: str
    def __init__(self, *args, **kwargs): raise Rejected('capabilities can only follow actual native admission')
    def __reduce__(self): raise Rejected('capability serialization forbidden')

@dataclass(frozen=True, slots=True, init=False, eq=False)
class EmptyTarget:
    """Arm immediately before unchanged StageRunner.run creates its scaffold."""
    def __init__(self, *args, **kwargs): raise Rejected('use arm_empty_target')
    def __reduce__(self): raise Rejected('capability serialization forbidden')

@dataclass(frozen=True, slots=True)
class HistoricalTransfer:
    certificate_sha256: str
    certificate_bytes: bytes
    historical_stage_ids: tuple[str, ...]
    remaining_native_stage_ids: tuple[str, ...]
    complete_target_closure: bool = False
    activation_allowed: bool = False


def _scope(request):
    args = request['native']; scope = request['scope']; plan = args['plan']
    stages = {s['stage_id']: s for s in plan['stages']}
    need(len(stages) == len(plan['stages']), 'duplicate stage')
    target = scope['target_stage']; final_role = scope.get('final_role')
    if final_role is None:
        need(target in stages, 'unknown target stage')
    else:
        need(final_role in {'export_target', 'fresh_kernel'} and target is None, 'invalid final role or synthetic target stage')
    origins = scope['origin_by_stage']; need(set(origins) == set(stages), 'origin map must cover exact plan')
    need(all(v in {'OldOrigin', 'PriorSuccessorOrigin', 'LatestSuccessorOrigin', 'ProductionSuccessOrigin', 'CurrentOrigin'} for v in origins.values()), 'unknown origin')
    if final_role is None: need(origins[target] == 'CurrentOrigin', 'target must be current')
    required = list(stages) if final_role is not None else stages[target]['required_predecessors']
    need(required == [s for s in stages if s in set(required)], 'unordered/duplicate target closure')
    historical = [s for s in required if origins[s] in {'OldOrigin','PriorSuccessorOrigin'}]
    current = [s for s in required if origins[s] in {'LatestSuccessorOrigin','ProductionSuccessOrigin','CurrentOrigin'}]
    for sid in historical:
        need(set(stages[sid]['required_predecessors']) <= set(historical), 'historical subset not dependency closed')
    full = scope['expected_full_native_descriptors']
    need([d['stage_id'] for d in full] == required, 'full descriptor expectation differs from exact required_predecessors')
    need([d for d in full if origins[d['stage_id']] in {'OldOrigin','PriorSuccessorOrigin'}] == scope['expected_native_descriptors'], 'full/historical descriptor expectations differ')
    need(all(d['identity'] == scope['current_identity'] for d in full if origins[d['stage_id']] == 'CurrentOrigin'), 'current descriptor identity differs')
    need(all(d['identity'] == scope['latest_identity'] for d in full if origins[d['stage_id']] == 'LatestSuccessorOrigin'), 'latest descriptor identity differs')
    need(all(d['identity']==scope['production_identity'] for d in full if origins[d['stage_id']]=='ProductionSuccessOrigin'),'production descriptor identity differs')
    need(len({json.dumps(scope[k],sort_keys=True) for k in ('latest_identity','production_identity','current_identity')})==3,'production/latest/current identities must be distinct')
    descriptors = scope['expected_native_descriptors']; objects = scope['expected_objects']
    need([d['stage_id'] for d in descriptors] == historical, 'historical descriptors differ from filtered required_predecessors')
    need([w['native_descriptor'] for w in args['wrappers']] == descriptors, 'native invocation differs from exact expected descriptors')
    expected_modules = [m for sid in historical for m in stages[sid]['modules']]
    need(set(objects) == set(expected_modules) and len(expected_modules) == len(set(expected_modules)), 'historical module set differs')
    for module, outputs in objects.items():
        prefix = 'objects/' + module.replace('.', '/')
        need(set(outputs) == {prefix + suffix for suffix in SUFFIXES}, 'full six-companion set required')
        for name, pin in outputs.items():
            relative(name); need(type(pin) is str and re.fullmatch('[0-9a-f]{64}', pin), 'invalid object digest')
    for w in args['wrappers']:
        sid = w['native_descriptor']['stage_id']
        need(w['origin'] == ('OldOrigin' if origins[sid] == 'OldOrigin' else 'CurrentOrigin'), 'native prior origin view differs')
        expected_identity = args['old_context']['identity'] if origins[sid] == 'OldOrigin' else args['identity']
        need(w['native_descriptor']['identity'] == expected_identity, 'native identity rewrite forbidden')
    return historical, current


def _check_ages(request):
    pairs = [(request['native']['old_context']['identity'], request['native']['old_context']['contract']),
             (request['native']['identity'], request['native']['contract']),
             (request['scope']['current_identity'], request['scope']['current_contract']),
             (request['scope']['latest_identity'], request['scope']['current_contract']),
             (request['scope']['production_identity'], request['scope']['current_contract'])]
    now = datetime.now(timezone.utc)
    for identity, contract in pairs:
        started = datetime.fromisoformat(identity['run_started_at'].replace('Z', '+00:00'))
        need(started.tzinfo is not None and 0 <= (now - started).total_seconds() <= contract['max_run_age_seconds'], 'expired/future native or current identity')


def _archive_pins(request):
    pins = {}
    for w in request['native']['wrappers']:
        path = canonical(w['archive_path']); d = w['native_descriptor']
        need(str(path) not in pins, 'duplicate archive path')
        pins[str(path)] = {'bytes': d['archive_bytes'], 'sha256': d['archive_sha256']}
        need(info(path) == pins[str(path)], 'archive payload pin mismatch')
    return pins


def _check_sources(root, manifest):
    expected = {row['path']: {'bytes': row['bytes'], 'sha256': row['sha256']} for row in manifest['files']}
    need(len(expected) == len(manifest['files']) and tree(root) == expected, 'pinned source tree changed')
    return expected


def admit_historical(*, request_bytes, request_sha256, source_root, workspace,
                     admission_root='/tmp/modern_c_three_context_adapter_20261016T1809',
                     historical_root='/tmp/modern_c_metadata_retry_release_20261016T1432/pipeline', deadline_monotonic=None):
    """Only issuer. Always invokes freshly loaded unchanged admit_native.

    request_bytes are trusted adapter output authenticated by request_sha256.
    They bind native inputs, raw native selection bytes/hash, exact expected
    maps and frozen current selection/identity/manifest. A digest is a pin, not
    independent provenance. No completed JSON receipt is accepted here.
    """
    single_thread(); need(digest(request_bytes) == request_sha256, 'request pin mismatch')
    request = parse(request_bytes)
    need(set(request) == {'schema', 'native', 'native_selection_utf8', 'native_selection_sha256', 'scope'}, 'request fields differ')
    need(request['schema'] == 'fixed-four-context-transfer-request-v1', 'request schema')
    native_args = request['native']
    need(set(native_args) == {'old_context', 'source_delta', 'contract', 'manifest', 'plan', 'profiles', 'identity', 'inventory', 'wrappers'}, 'native invocation fields differ')
    scope = request['scope']
    scope_keys = {'target_stage', 'origin_by_stage', 'expected_native_descriptors', 'expected_objects', 'current_identity', 'latest_identity', 'production_identity', 'current_manifest', 'current_contract', 'expected_full_native_descriptors'}
    need(set(scope) == scope_keys or set(scope) == scope_keys | {'final_role'}, 'scope fields differ')
    if 'final_role' in scope: need(scope['final_role'] in {'export_target', 'fresh_kernel'} and scope['target_stage'] is None, 'explicit final-closure role required')
    historical, current = _scope(request)
    now_monotonic = time.monotonic(); deadline = now_monotonic + 19800
    if deadline_monotonic is not None:
        need(type(deadline_monotonic) in (int, float), 'absolute deadline must be a real number, not Boolean')
        try: supplied_deadline = float(deadline_monotonic)
        except (ValueError, OverflowError) as error: raise Rejected('malformed absolute deadline') from error
        need(math.isfinite(supplied_deadline) and supplied_deadline > now_monotonic, 'nonfinite or expired absolute deadline')
        deadline = min(deadline, supplied_deadline)
    def budget():
        _check_budget(deadline, request)
    budget()
    need(historical, 'empty historical admission has no transfer capability')
    source = canonical(source_root); work = canonical(workspace)
    admission_root = canonical(admission_root); historical_root = canonical(historical_root)
    disjoint(source, work); disjoint(work, admission_root); disjoint(work, historical_root)
    need(not work.exists(), 'native workspace must be new'); owned_dir(work.parent)
    sources = _check_sources(source, native_args['manifest']); archives = _archive_pins(request)
    for name in archives: disjoint(work, Path(name))
    with _fixed_native(admission_root, historical_root) as (admission, native):
        selection_raw = request['native_selection_utf8'].encode()
        need(digest(selection_raw) == request['native_selection_sha256'], 'native selection pin mismatch')
        selection = native.p.parse_selection(selection_raw, request['native_selection_sha256'], native_args['plan'])
        result = admission.admit_native(native, selection=selection, source_root=source, workspace=work,
                                       check_budget=budget, **copy.deepcopy(native_args))
        need(result['objects'] == scope['expected_objects'], 'live native object map differs')
        need(result['native_descriptors'] == scope['expected_native_descriptors'], 'live native descriptor map differs')
        need(result['runtime_installed'] is False and result['runtime_opened'] is False and result['executor_calls'] == 0, 'unexpected native execution')
        native.f.verify_sources(source, native_args['manifest'])
        evidence = tree(work / 'validation/restore-evidence')
        need(evidence == result['restore_evidence'], 'live native evidence map differs')
        objects = tree(work / 'validation/objects')
        expected = {name.removeprefix('objects/'): pin for outputs in scope['expected_objects'].values() for name, pin in outputs.items()}
        need({name: row['sha256'] for name, row in objects.items()} == expected, 'live full companion tree differs')
        for d in scope['expected_native_descriptors']:
            need(evidence[d['stage_id'] + '/receipt.json']['sha256'] == d['receipt_sha256'], 'raw native receipt not preserved')
    _check_sources(source, native_args['manifest']); _archive_pins(request)
    skeleton = {'empty-runtime', 'validation', *{'validation/' + s for s in SCAFFOLD}, 'validation/quarantine'}
    # Native prior may leave an empty quarantine parent; with only old stages it does not exist.
    if not (work / 'validation/quarantine').exists(): skeleton.remove('validation/quarantine')
    workspace_tree = tree(work, empty_dirs=skeleton)
    state = {'request': request_bytes, 'source': source, 'sources': sources, 'work': work,
        'work_inode': owned_dir(work), 'deadline': deadline, 'admission_root': admission_root, 'historical_root': historical_root, 'objects': objects, 'evidence': evidence, 'archives': archives,
        'workspace_tree': workspace_tree, 'native_result': result, 'native_result_bytes': raw_json(result), 'skeleton': skeleton, 'historical': historical, 'current': current, 'used': False}
    # No hashing, disk access or input serialization after this terminal check.
    budget()
    token = object.__new__(CheckedAdmission); object.__setattr__(token, 'binding_sha256', request_sha256)
    _ADMISSIONS[token] = state
    return token


def arm_empty_target(runner, *, target_stage):
    """Called by trusted future run adapter immediately before super().run(...).

    This witnesses absence, binds the exact runner/plan/source/identity, and does
    not create or adopt a directory. Only the same live runner may consume it
    after the unchanged StageRunner has created its exact empty scaffold.
    """
    return _arm_target(runner, target_stage=target_stage, final_role=None)


def arm_final_target(runner, *, final_role):
    """Explicit final full-plan provider closure; no synthetic plan stage."""
    need(final_role in {'export_target', 'fresh_kernel'}, 'unsupported final role')
    return _arm_target(runner, target_stage=None, final_role=final_role)


def _arm_target(runner, *, target_stage, final_role):
    single_thread(); path = canonical(str(runner.workspace)); need(not path.exists(), 'current workspace must be new')
    need((final_role is None and target_stage in runner.stages) or (final_role in {'export_target', 'fresh_kernel'} and target_stage is None), 'invalid target scope')
    need(not runner.objects and not runner.records and not runner.predecessor_descriptors and not runner.restore_evidence_hashes, 'current runner already has state')
    need(not getattr(runner, '_historical_transfer_poisoned', False), 'poisoned runner')
    token = object.__new__(EmptyTarget)
    _TARGETS[token] = {'runner': runner, 'workspace': path, 'parent_inode': owned_dir(path.parent), 'target': target_stage, 'final_role': final_role,
        'source_root': canonical(str(runner.source_root)), 'plan': raw_json(runner.plan), 'identity': raw_json(runner.identity), 'manifest': raw_json(runner.manifest), 'used': False}
    return token


def _durable_new(path, raw):
    canonical(str(path)); parent_fd = _open_directory(path.parent)
    try: fd = os.open(path.name, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o444, dir_fd=parent_fd)
    finally: os.close(parent_fd)
    try:
        with os.fdopen(fd, 'wb', closefd=False) as out: out.write(raw); out.flush(); os.fsync(fd)
    finally: os.close(fd)
    need(info(path) == {'bytes': len(raw), 'sha256': digest(raw)}, 'exclusive durable write readback differs')


def _readonly_file(path):
    parent_fd = _open_directory(path.parent)
    try: fd = os.open(path.name, os.O_RDONLY | os.O_NOFOLLOW, dir_fd=parent_fd)
    finally: os.close(parent_fd)
    try:
        st = os.fstat(fd)
        need(stat.S_ISREG(st.st_mode) and st.st_nlink == 1 and st.st_uid == os.geteuid(), 'readonly target is not an owned regular single-link file')
        os.fchmod(fd, 0o444)
    finally: os.close(fd)


def _read_pinned_evidence(path, expected):
    parent_fd = _open_directory(path.parent)
    try: fd = os.open(path.name, os.O_RDONLY | os.O_NOFOLLOW, dir_fd=parent_fd)
    finally: os.close(parent_fd)
    try:
        st = os.fstat(fd)
        need(stat.S_ISREG(st.st_mode) and st.st_nlink == 1 and st.st_uid == os.geteuid() and st.st_size == expected['bytes'], 'evidence read is not the pinned regular single-link file')
        with os.fdopen(fd, 'rb', closefd=False) as stream: raw = stream.read(expected['bytes'] + 1)
        need({'bytes': len(raw), 'sha256': digest(raw)} == expected, 'evidence changed during read')
        return raw
    finally: os.close(fd)


def _sync_dir(path):
    fd = _open_directory(path)
    try: os.fsync(fd)
    finally: os.close(fd)


def _rename_noreplace(source, destination):
    # Linux renameat2 with RENAME_NOREPLACE. No overwrite-capable fallback.
    libc = ctypes.CDLL(None, use_errno=True)
    function = getattr(libc, 'renameat2', None); need(function is not None, 'atomic no-clobber rename unavailable')
    function.argtypes = [ctypes.c_int, ctypes.c_char_p, ctypes.c_int, ctypes.c_char_p, ctypes.c_uint]
    function.restype = ctypes.c_int
    source_fd = _open_directory(source.parent)
    try:
        destination_fd = _open_directory(destination.parent)
        try:
            result = function(source_fd, os.fsencode(source.name), destination_fd, os.fsencode(destination.name), 1)
            if result:
                error = ctypes.get_errno()
                raise OSError(error, os.strerror(error), str(destination))
        finally: os.close(destination_fd)
    finally: os.close(source_fd)


def _check_budget(deadline, request):
    # Reuse the same clipped absolute deadline, including after expensive work.
    _check_ages(request)
    need(time.monotonic() < deadline, 'admission/transfer deadline elapsed')


def _check_pin_set(state):
    request = parse(state['request'])
    _check_budget(state['deadline'], request)
    need(raw_json(state['native_result']) == state['native_result_bytes'], 'live native admission result changed')
    need(owned_dir(state['work']) == state['work_inode'], 'admission root replaced')
    _check_sources(state['source'], request['native']['manifest']); _archive_pins(request); check_fixed_files(state['admission_root'], state['historical_root'])
    return request


def allocation_rounded_copy_budget(*, evidence, object_names, certificate_bytes_bound, marker_bytes, allocation_unit):
    """Sizing only: no admission authority. Object payload bytes are never copied."""
    need(type(allocation_unit) is int and allocation_unit > 0, 'invalid allocation unit')
    need(type(certificate_bytes_bound) is int and certificate_bytes_bound > 0 and type(marker_bytes) is int and marker_bytes > 0, 'invalid metadata byte bounds')
    unit = max(4096, allocation_unit); rounded = lambda n: ((n + unit - 1) // unit) * unit
    paths = ['restore-evidence/' + relative(n) for n in evidence] + ['objects/' + relative(n) for n in object_names]
    directories = {str(p) for name in paths for p in PurePosixPath(name).parents if str(p) != '.'} - set(SCAFFOLD)
    sizes = [row['bytes'] for row in evidence.values()]
    need(all(type(size) is int and size >= 0 for size in sizes), 'invalid evidence size')
    files = len(evidence) + 2  # New evidence, certificate and permanent attempt marker.
    payload = sum(rounded(size) for size in sizes) + rounded(certificate_bytes_bound) + rounded(marker_bytes)
    # Per-file/inode and per-directory allowances, plus conservative moved-entry
    # metadata and four journal/directory allocation units; zero deletion credit.
    overhead = unit * (files + len(directories) + len(object_names) + 4)
    return {'allocation_unit': unit, 'required_additional_free_bytes': payload + overhead,
        'required_free_inodes': files + len(directories), 'evidence_copy_bytes': sum(sizes),
        'certificate_bytes_bound': certificate_bytes_bound, 'marker_bytes': marker_bytes,
        'new_directories': len(directories), 'new_regular_files': files,
        'object_payload_copy_bytes': 0, 'deletion_credit_bytes': 0}


def transfer_checked(admission, target):
    """Transfer historical subset only. This NEVER grants complete-target authority.

    The future adapter must subsequently admit remaining CurrentOrigin payloads
    using unchanged current read_artifacts and enforce the full, exact original
    required_predecessors order before any fresh compile or receipt emission.
    """
    single_thread(); need(type(admission) is CheckedAdmission and admission in _ADMISSIONS, 'unknown admission capability')
    need(type(target) is EmptyTarget and target in _TARGETS, 'unknown empty-target capability')
    state = _ADMISSIONS[admission]; dst = _TARGETS[target]
    need(not state['used'] and not dst['used'], 'one-shot capability already consumed')
    state['used'] = True; dst['used'] = True
    runner = dst['runner']; work = dst['workspace']; runner._historical_transfer_poisoned = True
    try:
        request = _check_pin_set(state); scope = request['scope']
        need(dst['target'] == scope['target_stage'] and dst['final_role'] == scope.get('final_role'), 'wrong target stage/final role')
        need(canonical(str(runner.workspace)) == work and owned_dir(work.parent) == dst['parent_inode'], 'destination binding changed')
        for root in (state['work'], state['source'], state['admission_root'], state['historical_root']): disjoint(work, root)
        for name in state['archives']: disjoint(work, Path(name))
        need(raw_json(runner.plan) == dst['plan'] == raw_json(request['native']['plan']), 'current plan changed')
        need(raw_json(runner.identity) == dst['identity'] == raw_json(scope['current_identity']), 'current identity changed')
        need(raw_json(runner.manifest) == dst['manifest'] == raw_json(scope['current_manifest']), 'current source manifest changed')
        need(runner.contract == scope['current_contract'], 'current contract changed')
        current_source = canonical(str(runner.source_root)); need(current_source == dst['source_root'], 'current source-root binding changed'); disjoint(work, current_source)
        _check_sources(current_source, scope['current_manifest'])
        old_entries = {r['module']: r for r in request['native']['manifest']['files']}
        new_entries = {r['module']: r for r in scope['current_manifest']['files']}
        need(all(old_entries[m] == new_entries[m] for m in scope['expected_objects']), 'historical source record differs in current context')
        need(not runner.objects and not runner.records and not runner.predecessor_descriptors and not runner.restore_evidence_hashes, 'target is not empty')
        need(tree(work, empty_dirs=SCAFFOLD) == {}, 'target must have exact empty native scaffold')
        need(tree(state['work'], empty_dirs=state['skeleton']) == state['workspace_tree'], 'native workspace changed before transfer')
        inode = owned_dir(work); dst['workspace_inode'] = inode
        marker = {'schema': 'historical-transfer-attempt-v2', 'status': 'incomplete_until_live_capability_return',
                  'request_sha256': admission.binding_sha256, 'target_stage': dst['target'], 'final_role': dst['final_role'], 'activation_allowed': False}
        certificate = {'schema': 'checked-legacy-four-context-transfer-v1', 'request_sha256': admission.binding_sha256,
            'target_stage': dst['target'], 'final_role': dst['final_role'], 'historical_stage_ids': state['historical'], 'remaining_native_stage_ids': state['current'],
            'required_providers': _target_providers(runner, dst),
            'source_workspace': str(state['work']), 'destination_workspace': str(work),
            'source_workspace_inode': list(state['work_inode']), 'destination_workspace_inode': list(inode),
            'native_source_root': str(state['source']), 'current_source_root': str(current_source),
            'admission_implementation_root': str(state['admission_root']), 'historical_implementation_root': str(state['historical_root']),
            'native_descriptors': scope['expected_native_descriptors'], 'objects': state['objects'], 'preserved_native_evidence': state['evidence'],
            'native_source_manifest_sha256': digest(raw_json(request['native']['manifest'])),
            'current_identity': runner.identity, 'complete_target_closure': False, 'activation_allowed': False,
            'proof_pass_claimed': False, 'claim': 'Historical subset only; unchanged native validators admitted payloads; raw receipts preserved.'}
        filesystem = os.statvfs(work)
        # Reserve 2 KiB for the budget fields themselves; enforce that exact
        # final certificate fits before writing anything. No circular estimate.
        certificate_bound = len(raw_json(certificate)) + 2048
        budget = allocation_rounded_copy_budget(evidence=state['evidence'], object_names=tuple(state['objects']),
            certificate_bytes_bound=certificate_bound, marker_bytes=len(raw_json(marker)), allocation_unit=filesystem.f_frsize)
        certificate['additional_transfer_copy_budget'] = budget
        cert_bytes = raw_json(certificate); need(len(cert_bytes) <= certificate_bound, 'certificate exceeded reserved metadata bound')
        need(shutil.disk_usage(work).free >= budget['required_additional_free_bytes'], 'insufficient measured transfer-only copy space')
        need(filesystem.f_favail >= budget['required_free_inodes'], 'insufficient measured transfer-only copy inodes')
        _durable_new(work / MARKER, raw_json(marker)); _sync_dir(work)
        source_objects = state['work'] / 'validation/objects'; source_evidence = state['work'] / 'validation/restore-evidence'
        need(source_objects.stat().st_dev == work.stat().st_dev, 'cross-device move forbidden')
        # Copy all native evidence with exclusive creation. Originals never change.
        for name, expected in sorted(state['evidence'].items()):
            src = source_evidence / name; need(info(src) == expected, 'native evidence changed before copy')
            out = work / 'restore-evidence' / name
            _mkdir_owned_under(work, out.parent.relative_to(work).as_posix()); canonical(str(out)); owned_dir(out.parent)
            _durable_new(out, _read_pinned_evidence(src, expected)); need(info(out) == expected and info(src) == expected, 'native evidence copy differs')
        for name, expected in sorted(state['objects'].items()):
            src = source_objects / name; need(info(src) == expected, 'native object changed/shared before move')
            out = work / 'objects' / name; _mkdir_owned_under(work, out.parent.relative_to(work).as_posix())
            canonical(str(out)); owned_dir(out.parent); need(not out.exists(), 'object shadows destination')
            _rename_noreplace(src, out); _readonly_file(out)
            need(info(out) == expected, 'moved object differs/shared'); _sync_dir(out.parent); _sync_dir(src.parent)
        object_dirs = {str(p) for name in state['objects'] for p in PurePosixPath(name).parents if str(p) != '.'}
        need(tree(source_objects, empty_dirs=object_dirs) == {}, 'unexpected source object remains')
        need(tree(work / 'objects') == state['objects'], 'transferred object tree differs')
        need(tree(source_evidence) == tree(work / 'restore-evidence') == state['evidence'], 'preserved raw evidence differs')
        _check_pin_set(state); _check_sources(current_source, scope['current_manifest'])
        after_source = dict(state['workspace_tree'])
        for name in state['objects']: del after_source['validation/objects/' + name]
        source_empty = state['skeleton'] | {'validation/objects/' + d for d in object_dirs}
        need(tree(state['work'], empty_dirs=source_empty) == after_source, 'native workspace after-map differs')
        _durable_new(work / CERTIFICATE, cert_bytes)
        expected_destination = {'objects/' + n: i for n, i in state['objects'].items()}
        expected_destination.update({'restore-evidence/' + n: i for n, i in state['evidence'].items()})
        expected_destination[MARKER] = {'bytes': len(raw_json(marker)), 'sha256': digest(raw_json(marker))}
        expected_destination[CERTIFICATE] = {'bytes': len(cert_bytes), 'sha256': digest(cert_bytes)}
        need(owned_dir(work) == inode and tree(work, empty_dirs=SCAFFOLD) == expected_destination, 'destination after-map differs')
        for directory in sorted({work, *{p.parent for p in work.rglob('*')}}, key=lambda p: len(p.parts), reverse=True): _sync_dir(directory)
        # Publish no state until all checks, durable copies and certificate finish.
        runner.objects = copy.deepcopy(scope['expected_objects'])
        runner.predecessor_descriptors = copy.deepcopy(scope['expected_native_descriptors'])
        runner.restore_evidence_hashes = {sid: {name[len(sid) + 1:]: row['sha256'] for name, row in state['evidence'].items() if name.startswith(sid + '/')}
                                         for sid in state['historical']}
        runner.verify_checked_objects(); _check_pin_set(state); _check_sources(current_source, scope['current_manifest'])
        need(tree(work, empty_dirs=SCAFFOLD) == expected_destination, 'destination changed before capability return')
        need(canonical(str(runner.workspace)) == work and canonical(str(runner.source_root)) == current_source, 'current roots changed during transfer')
        need(raw_json(runner.identity) == dst['identity'] and raw_json(runner.plan) == dst['plan'] and raw_json(runner.manifest) == dst['manifest'] and runner.contract == scope['current_contract'], 'current binding changed during transfer')
        certificate_sha256 = digest(cert_bytes)
        historical_ids, current_ids = tuple(state['historical']), tuple(state['current'])
        # A late full-tree hash/fsync must never renew or outrun this deadline.
        _check_budget(state['deadline'], request)
        result = HistoricalTransfer(certificate_sha256, cert_bytes, historical_ids, current_ids)
        runner._historical_transfer_poisoned = False
        _TRANSFERS[id(result)] = (result, state, dst)
        return result
    except BaseException:
        # Preserve every byte for inspection; no rollback, deletion, or retry.
        runner._historical_transfer_poisoned = True
        runner.objects = {}; runner.predecessor_descriptors = []; runner.restore_evidence_hashes = {}
        raise


def _target_providers(runner, destination):
    return list(runner.stages) if destination['final_role'] is not None else runner.stages[destination['target']]['required_predecessors']


def finalize_predecessors(transfer, target):
    return _finalize_chain(transfer, target, require_final_role=False)


def finalize_final_closure(transfer, target):
    """Check all original ordered plan stages for one of two explicit final roles."""
    return _finalize_chain(transfer, target, require_final_role=True)


def _finalize_chain(transfer, target, *, require_final_role):
    """Consistency gate after the future adapter's actual current native calls.

    This is deliberately a check, not an admission/capability issuer. The trusted
    future adapter MUST first invoke unchanged current StageRunner.read_artifacts
    for every remaining current stage. Manually seeding current runner maps is
    outside the contract; this checker alone is not a semantic admission path.
    """
    saved = _TRANSFERS.get(id(transfer))
    need(saved is not None and saved[0] is transfer, 'unknown live transfer result')
    _, state, dst = saved
    runner = dst['runner']
    try:
        single_thread()
        need(type(target) is EmptyTarget and _TARGETS.get(target) is dst, 'wrong target capability')
        need(not dst.get('finalization_failed', False) and not runner._historical_transfer_poisoned, 'poisoned finalization cannot resume')
        need((dst['final_role'] in {'export_target', 'fresh_kernel'}) is require_final_role, 'wrong stage/final-closure finalizer')
        request = _check_pin_set(state); scope = request['scope']
        need(canonical(str(runner.workspace)) == dst['workspace'] and owned_dir(dst['workspace']) == dst['workspace_inode'], 'destination runner/root binding changed')
        need(canonical(str(runner.source_root)) == dst['source_root'], 'current source-root binding changed')
        need(raw_json(runner.manifest) == dst['manifest'] and runner.contract == scope['current_contract'], 'current source/contract binding changed')
        need(not runner._historical_transfer_poisoned, 'poisoned runner')
        need(raw_json(runner.plan) == dst['plan'] and runner.identity == scope['current_identity'], 'current binding changed')
        expected = scope['expected_full_native_descriptors']
        need(runner.predecessor_descriptors == expected, 'full native chain not exact canonical required_predecessors')
        required = _target_providers(runner, dst)
        need([d['stage_id'] for d in expected] == required, 'required_predecessors changed')
        modules = [m for sid in required for m in runner.stages[sid]['modules']]
        need(set(runner.objects) == set(modules) and len(modules) == len(set(modules)), 'full predecessor module closure differs')
        for module, outputs in runner.objects.items():
            need(set(outputs) == {'objects/' + module.replace('.', '/') + suffix for suffix in SUFFIXES}, 'full companion set differs')
        need(all(runner.objects[m] == values for m, values in scope['expected_objects'].items()), 'historical object map changed')
        need(set(runner.restore_evidence_hashes) == set(required), 'full evidence stage map differs')
        runner.verify_checked_objects()
        expected_evidence = {sid + '/' + name: pin for sid, files in runner.restore_evidence_hashes.items() for name, pin in files.items()}
        need({n: i['sha256'] for n, i in tree(runner.workspace / 'restore-evidence').items()} == expected_evidence, 'full evidence tree differs')
        need(tree(state['work'] / 'validation/restore-evidence') == state['evidence'], 'preserved original evidence changed after transfer')
        object_dirs = {str(p) for name in state['objects'] for p in PurePosixPath(name).parents if str(p) != '.'}
        after_source = dict(state['workspace_tree'])
        for name in state['objects']: del after_source['validation/objects/' + name]
        source_empty = state['skeleton'] | {'validation/objects/' + d for d in object_dirs}
        need(tree(state['work'], empty_dirs=source_empty) == after_source, 'retained native workspace changed after transfer')
        expected_outputs = {name.removeprefix('objects/'): pin for outputs in runner.objects.values() for name, pin in outputs.items()}
        need({n: i['sha256'] for n, i in tree(runner.workspace / 'objects').items()} == expected_outputs, 'full object tree differs')
        for descriptor in expected:
            evidence = runner.workspace / 'restore-evidence' / descriptor['stage_id']
            need(info(evidence / 'receipt.json')['sha256'] == descriptor['receipt_sha256'], 'full raw receipt pin differs')
        certificate_pin = {'bytes': len(transfer.certificate_bytes), 'sha256': transfer.certificate_sha256}
        need(_read_pinned_evidence(runner.workspace / CERTIFICATE, certificate_pin) == transfer.certificate_bytes, 'transfer certificate changed')
        _check_sources(canonical(str(runner.source_root)), scope['current_manifest'])
        _check_budget(state['deadline'], request)
        return None
    except BaseException:
        dst['finalization_failed'] = True
        runner._historical_transfer_poisoned = True
        raise
