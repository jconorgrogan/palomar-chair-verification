#!/usr/bin/env python3
"""Inactive-by-default, source-only fresh Lean stage runner. No proof-pass verdict.

Only a separately reviewed contract enables CLI execution. See README.md for the
trusted workflow boundary and pending final theorem/independent-kernel checks.
"""
from __future__ import annotations
import argparse
import ctypes
import hashlib
import io
import json
import os
from pathlib import Path, PurePosixPath
import re
import resource
import signal
import shutil
import stat
import subprocess
import tarfile
import time
from datetime import datetime, timezone
from typing import Callable

TOOLCHAIN_SHA256 = 'b67d0e0ba959fc74e186f1b44aebca32d6ecb6a28f8e9a029fc4e9f73398a049'
MODULE = re.compile(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*\Z")
SHA256 = re.compile(r'[0-9a-f]{64}\Z')
COMMIT = re.compile(r'[0-9a-f]{40}\Z')
SUFFIXES = {'.olean', '.olean.private', '.olean.server', '.ilean'}

class Rejected(ValueError):
    pass

def need(condition, message):
    if not condition:
        raise Rejected(message)

def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def file_sha(path: Path) -> str:
    no_symlink_path(path)
    h = hashlib.sha256()
    with path.open('rb') as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()

def json_bytes(value) -> bytes:
    return (json.dumps(value, sort_keys=True, indent=2, allow_nan=False) + '\n').encode()

def _pairs(pairs):
    result = {}
    for key, value in pairs:
        need(key not in result, f'duplicate JSON key: {key}')
        result[key] = value
    return result

def parse_json(data: bytes):
    return json.loads(data, object_pairs_hook=_pairs,
                      parse_constant=lambda x: (_ for _ in ()).throw(Rejected(f'invalid JSON: {x}')))

def load_json(path: Path):
    return parse_json(path.read_bytes())

def safe_rel(value: str) -> str:
    need(isinstance(value, str) and value and '\\' not in value and '\x00' not in value,
         'invalid relative path')
    p = PurePosixPath(value)
    need(not p.is_absolute() and str(p) == value and all(x not in ('', '.', '..') for x in p.parts),
         f'non-canonical/escaping path: {value}')
    return value

def no_symlink_path(path: Path):
    path = path.absolute()
    for p in [path, *path.parents]:
        need(not p.is_symlink(), f'symlink forbidden: {p}')

def regular_tree(root: Path) -> dict[str, Path]:
    no_symlink_path(root)
    need(root.is_dir(), f'missing directory: {root}')
    result = {}
    for parent, dirs, files in os.walk(root, followlinks=False):
        for name in dirs + files:
            p = Path(parent) / name
            mode = p.lstat().st_mode
            need(not stat.S_ISLNK(mode), f'symlink forbidden: {p}')
            need(stat.S_ISDIR(mode) or stat.S_ISREG(mode), f'non-regular entry: {p}')
            if stat.S_ISREG(mode):
                rel = safe_rel(p.relative_to(root).as_posix())
                need(rel not in result, 'duplicate filesystem entry')
                result[rel] = p
    return result

def exact_tree(root: Path, expected: set[str]):
    files = regular_tree(root)
    need(set(files) == expected,
         f'unexpected/missing files: extra={sorted(set(files)-expected)[:5]}, missing={sorted(expected-set(files))[:5]}')
    allowed_dirs = {str(p) for f in expected for p in PurePosixPath(f).parents if str(p) != '.'}
    for parent, dirs, _ in os.walk(root):
        for name in dirs:
            need((Path(parent) / name).relative_to(root).as_posix() in allowed_dirs,
                 'unexpected directory')
    return files

def import_header(data: bytes) -> tuple[list[str], bool]:
    """Strict supported Lean header subset; unusual syntax fails closed."""
    imports, prelude, depth = [], False, 0
    for line in data.decode('utf-8').splitlines():
        clean, i = [], 0
        while i < len(line):
            if depth:
                if line.startswith('/-', i): depth, i = depth + 1, i + 2
                elif line.startswith('-/', i): depth, i = depth - 1, i + 2
                else: i += 1
            elif line.startswith('/-', i): depth, i = 1, i + 2; clean.append(' ')
            elif line.startswith('--', i): break
            else: clean.append(line[i]); i += 1
        value = ''.join(clean).strip()
        if not value: continue
        if value == 'prelude':
            need(not prelude and not imports, 'misplaced prelude'); prelude = True; continue
        if value == 'module': continue
        match = re.match(r'^(?:(?:public|private|meta)\s+)*import\b', value)
        if match:
            rest = value[match.end():].strip()
            if rest.startswith('all '): rest = rest[4:]
            tokens = rest.split()
            need(tokens and all(MODULE.fullmatch(x) for x in tokens), 'unsupported import header')
            imports.extend(tokens)
        else:
            need(depth == 0, 'unterminated header comment')
            break
    need(depth == 0, 'unterminated header comment')
    return imports, not prelude

def manifest_index(manifest: dict) -> dict[str, dict]:
    entries, paths = {}, set()
    external = manifest['external_imports']
    need(external == ['Init', 'Init.Data.List.Nat.TakeDrop', 'Init.Data.List.OfFn'] or
         (len(external) == len(set(external)) and set(external) <= {'Init', 'Init.Data.List.OfFn', 'Init.Data.List.Nat.TakeDrop'}),
         'unexpected external imports')
    for entry in manifest['files']:
        module, path = entry['module'], safe_rel(entry['path'])
        need(MODULE.fullmatch(module), 'invalid module')
        need(path == module.replace('.', '/') + '.lean', 'module/path mismatch')
        need(module not in entries and path not in paths, 'duplicate module or path')
        need(SHA256.fullmatch(entry['sha256']), 'invalid source hash')
        need(type(entry['bytes']) is int and entry['bytes'] >= 0, 'invalid source size')
        need(type(entry['implicit_Init']) is bool, 'missing implicit Init flag')
        need(isinstance(entry['ordered_imports'], list) and
             all(isinstance(x, str) and MODULE.fullmatch(x) for x in entry['ordered_imports']), 'invalid imports')
        entries[module] = entry; paths.add(path)
    need(manifest['source_count'] == len(entries), 'source count mismatch')
    need(manifest['source_bytes'] == sum(x['bytes'] for x in entries.values()), 'source size mismatch')
    seen = set(external)
    for module, entry in entries.items():
        need(set(entry['ordered_imports']) <= seen, f'unresolved import/cycle/non-topological manifest: {module}')
        need(not entry['implicit_Init'] or 'Init' in external, 'implicit Init unaccounted for')
        seen.add(module)
    return entries

def verify_sources(root: Path, manifest: dict) -> dict[str, dict]:
    entries = manifest_index(manifest)
    files = exact_tree(root, {x['path'] for x in entries.values()})
    for entry in entries.values():
        data = files[entry['path']].read_bytes()
        need(len(data) == entry['bytes'] and sha(data) == entry['sha256'], 'source hash/size mismatch')
        imports, implicit = import_header(data)
        need(imports == entry['ordered_imports'] and implicit == entry['implicit_Init'],
             f'import order/implicit Init mismatch: {entry["module"]}')
    return entries

def extract_sources(archive_path: Path, destination: Path, manifest: dict):
    entries = manifest_index(manifest)
    no_symlink_path(archive_path); no_symlink_path(destination)
    need(not destination.exists(), 'source extraction directory must be new')
    need(archive_path.stat().st_size == manifest['archive']['bytes'] and
         file_sha(archive_path) == manifest['archive']['sha256'], 'selected source archive identity mismatch')
    expected = {entry['path']: entry for entry in entries.values()}
    destination.mkdir(parents=True)
    seen, total = set(), 0
    with tarfile.open(archive_path, 'r:gz') as archive:
        for member in archive:
            name = safe_rel(member.name)
            need(name not in seen and name in expected and member.isreg() and not member.pax_headers,
                 'duplicate/unlisted/non-regular source archive member')
            seen.add(name); total += member.size
            need(member.size == expected[name]['bytes'] and total <= manifest['source_bytes'], 'source archive size mismatch')
            reader = archive.extractfile(member); need(reader is not None, 'missing source bytes')
            data = reader.read(member.size + 1)
            need(len(data) == member.size and sha(data) == expected[name]['sha256'], 'source archive member hash mismatch')
            out = destination / name; out.parent.mkdir(parents=True, exist_ok=True)
            with out.open('xb') as handle: handle.write(data)
    need(seen == set(expected), 'source archive missing selected file')
    verify_sources(destination, manifest)


def stage_dependencies(plan: dict, entries: dict) -> tuple[dict, dict]:
    stages, owner, position = {}, {}, {}
    for index, stage in enumerate(plan['stages']):
        sid = stage['stage_id']
        need(re.fullmatch(r'[a-z][a-z0-9_]*', sid) and sid not in stages, 'invalid/duplicate stage')
        need(stage['modules'] and len(stage['modules']) == len(set(stage['modules'])), 'empty/duplicate stage modules')
        stages[sid] = stage
        for offset, module in enumerate(stage['modules']):
            need(module in entries and module not in owner, 'unexpected/duplicate planned module')
            owner[module], position[module] = sid, (index, offset)
    need(set(owner) == set(entries), 'plan does not cover exact source manifest')
    direct = {sid: set() for sid in stages}
    for module, entry in entries.items():
        for dependency in entry['ordered_imports']:
            if dependency not in entries: continue
            need(position[dependency] < position[module], 'plan is not topological')
            if owner[dependency] != owner[module]: direct[owner[module]].add(owner[dependency])
    ancestors = {}
    for sid in stages:
        ancestors[sid] = direct[sid] | set().union(*(ancestors[x] for x in direct[sid]))
        need(stages[sid]['required_predecessors'] == [x for x in stages if x in ancestors[sid]],
             f'incomplete/unordered predecessor artifact closure: {sid}')
    return stages, owner

def positive_int(value, label, maximum):
    need(type(value) is int and 0 < value <= maximum, f'invalid bounded {label}')

def validate_profile(profile: dict):
    need(profile.get('review_status') == 'reviewed', 'unresolved/unreviewed module profile')
    for name in ('compile_timeout_seconds', 'check_timeout_seconds'):
        positive_int(profile[name], name, 19800)
    for name in ('compile_flags', 'check_flags'):
        need(isinstance(profile[name], list) and all(isinstance(x, str) and x.startswith('-') and
             not any(c in x for c in '\n\r\x00') for x in profile[name]), 'flags must be reviewed single tokens')
        need(not any(x in ('--run', '--stdin', '-o', '-i', '--root') or
                     x.startswith(('-o=', '-i=', '--root=')) for x in profile[name]), 'runner-owned arguments overridden')
    need([x for x in profile['compile_flags'] if x.startswith('-j')] == ['-j1'], 'compile must explicitly use one thread')
    for name in ('address_space_bytes', 'rss_tree_bytes'):
        positive_int(profile[name], name, 12 * 1024**3)
    positive_int(profile['max_created_file_bytes'], 'created file bytes', 4 * 1024**3)
    need(set(profile['check_flags']) <= {'--silent', '-v', '--verbose'}, 'unsupported per-module checker flag')
    # Lean memory/heartbeat flags are reviewed strings, never inferred from historical receipts.
    need(any(re.fullmatch(r'-M[1-9][0-9]*', x) for x in profile['compile_flags']), 'finite Lean memory limit required')

def validate_contract(contract, manifest, plan, profiles):
    need(contract.get('review_status') == 'reviewed_for_execution', 'INACTIVE: pipeline review is pending')
    need(COMMIT.fullmatch(contract.get('source_commit', '')), 'exact immutable source commit required')
    need(contract['lean_release'] == 'v4.35.0-rc2' and contract['lean_archive_sha256'] == TOOLCHAIN_SHA256,
         'wrong toolchain release/archive')
    need(contract['runner'] == 'ubuntu-22.04' and type(contract['maximum_parallel_jobs']) is int and 1 <= contract['maximum_parallel_jobs'] <= 4,
         'unsupported runner/parallelism')
    need(contract['retention_days'] == 7, 'artifact retention must be seven days')
    positive_int(contract['job_timeout_seconds'], 'job timeout', 21000)
    positive_int(contract['max_artifact_bytes'], 'artifact size', 4 * 1024**3)
    positive_int(contract['max_log_bytes'], 'command logs', 1024**3)
    positive_int(contract['max_restored_bytes'], 'restored dependency bytes', 100 * 1024**3)
    positive_int(contract['max_stage_output_bytes'], 'stage output bytes', 4 * 1024**3)
    positive_int(contract['max_run_age_seconds'], 'run age', 6 * 24 * 3600)
    positive_int(contract['minimum_free_disk_bytes'], 'free disk', 100 * 1024**3)
    need(isinstance(contract['output_suffixes'], list) and '.olean' in contract['output_suffixes'] and
         len(contract['output_suffixes']) == len(set(contract['output_suffixes'])) and
         set(contract['output_suffixes']) <= SUFFIXES, 'unreviewed output layout')
    entries = manifest_index(manifest)
    stages, owner = stage_dependencies(plan, entries)
    positive_int(contract['reserved_final_jobs'], 'reserved final jobs', 256)
    need(len(stages) + contract['reserved_final_jobs'] <= 256, 'workflow job/matrix count exceeds reviewed limit')
    need(set(profiles['module_profiles']) == set(entries), 'profile map must cover exact closure')
    for name in profiles['module_profiles'].values():
        need(name in profiles['profiles'], 'missing profile')
        validate_profile(profiles['profiles'][name])
    need(contract.get('transport_review_status') == 'reviewed', 'same-run artifact transport adapter pending review')
    need(contract.get('process_containment_review_status') == 'reviewed', 'process containment requires review')
    need(contract.get('compiler_adapter_review_status') == 'reviewed', 'compiler/output adapter pending review')
    return entries, stages, owner

def verify_toolchain(root: Path, archive: Path, inventory_path: Path, contract: dict, *, derived_inventory_sha256=None):
    no_symlink_path(archive); no_symlink_path(inventory_path)
    need(file_sha(archive) == TOOLCHAIN_SHA256, 'toolchain archive hash mismatch')
    expected_inventory = contract.get('toolchain_inventory_sha256')
    if expected_inventory is None:
        need(contract.get('toolchain_inventory_mode') == 'derive_from_pinned_archive_v1', 'unreviewed inventory derivation')
        expected_inventory = derived_inventory_sha256
    need(SHA256.fullmatch(expected_inventory or ''), 'authenticated toolchain inventory digest required')
    need(file_sha(inventory_path) == expected_inventory, 'toolchain inventory hash mismatch')
    inventory = load_json(inventory_path)
    need(inventory['archive_sha256'] == TOOLCHAIN_SHA256, 'inventory/archive identity mismatch')
    expected, symlinks = inventory['files'], inventory['symlinks']
    need(not (set(expected) & set(symlinks)), 'duplicate toolchain inventory path')
    no_symlink_path(root)
    files, links = {}, {}
    for parent, dirs, names in os.walk(root, followlinks=False):
        for name in dirs + names:
            path = Path(parent) / name; rel = safe_rel(path.relative_to(root).as_posix())
            if path.is_symlink():
                links[rel] = os.readlink(path)
                need(rel in symlinks and links[rel] == symlinks[rel], 'unlisted/changed toolchain symlink')
                need(not Path(links[rel]).is_absolute(), 'absolute toolchain symlink')
                need(path.resolve(strict=True).is_relative_to(root.resolve()), 'toolchain symlink escapes installation')
            elif path.is_file(): files[rel] = path
            else: need(path.is_dir(), 'non-regular toolchain entry')
    need(set(files) == set(expected) and links == symlinks, 'toolchain inventory membership mismatch')
    for rel, info in expected.items():
        safe_rel(rel)
        need(files[rel].stat().st_size == info['bytes'] and file_sha(files[rel]) == info['sha256'], 'installed toolchain hash mismatch')
    for executable in ('bin/lean', 'bin/leanchecker'):
        need(executable in files and os.access(files[executable], os.X_OK), f'missing tool: {executable}')
    return inventory

def proc_snapshot():
    """Linux process identities; disappearing processes are the only ignored race."""
    rows = {}; pagesize = os.sysconf('SC_PAGE_SIZE')
    for path in Path('/proc').glob('[0-9]*/stat'):
        try:
            fields = path.read_text().rsplit(')', 1)[1].split()
            rows[int(path.parent.name)] = {'state': fields[0], 'parent': int(fields[1]),
                'group': int(fields[2]), 'start_ticks': int(fields[19]),
                'rss_bytes': int(fields[21]) * pagesize}
        except (FileNotFoundError, ProcessLookupError):
            continue
    return rows

def owned_processes(group, baseline_children):
    """This single-threaded runner exclusively owns newly adopted child processes.

    A Linux subreaper adopts orphaned descendants, including children that escape
    their initial process group. Pre-existing direct children are never owned.
    """
    rows = proc_snapshot(); own_pid = os.getpid()
    owned = {pid for pid, row in rows.items() if row['group'] == group or
             (row['parent'] == own_pid and (pid, row['start_ticks']) not in baseline_children)}
    while True:
        expanded = owned | {pid for pid, row in rows.items() if row['parent'] in owned}
        if expanded == owned: break
        owned = expanded
    return {pid: rows[pid] for pid in owned}

def set_child_subreaper(value=None):
    """No privilege change: confine/reap this runner's own orphaned descendants."""
    libc = ctypes.CDLL(None, use_errno=True); current = ctypes.c_int()
    need(libc.prctl(37, ctypes.byref(current), 0, 0, 0) == 0,
         'Linux PR_GET_CHILD_SUBREAPER unavailable')
    if value is not None:
        need(libc.prctl(36, int(value), 0, 0, 0) == 0,
             'Linux PR_SET_CHILD_SUBREAPER unavailable')
    return current.value

def signal_same_process(pid, identity, sig):
    """Avoid targeting a reused PID after the inspected process exits."""
    current = proc_snapshot().get(pid)
    if current and current['start_ticks'] == identity['start_ticks']:
        try: os.kill(pid, sig)
        except ProcessLookupError: pass

def terminate_owned_processes(process, baseline_children, cleanup_timeout=3.0):
    """Kill, reap, and positively observe no owned descendants within a bound.

    Raises on missing cleanup evidence. A zombie is already stopped but still
    has to be reaped before a successful command can produce an artifact.
    """
    started = time.monotonic(); deadline = started + cleanup_timeout
    try: os.killpg(process.pid, signal.SIGKILL)
    except ProcessLookupError: pass
    while True:
        process.poll()  # Popen must reap its own direct child and retain its status.
        owned = owned_processes(process.pid, baseline_children)
        for pid, row in owned.items():
            if row['state'] != 'Z': signal_same_process(pid, row, signal.SIGKILL)
            if pid != process.pid:
                try: os.waitpid(pid, os.WNOHANG)
                except ChildProcessError: pass  # Still parented by another dying descendant.
        remaining = owned_processes(process.pid, baseline_children)
        if process.poll() is not None and not remaining:
            return {'process_group_empty': True, 'descendants_empty': True,
                    'cleanup_bound_seconds': cleanup_timeout,
                    'cleanup_elapsed_seconds': round(time.monotonic() - started, 6)}
        need(time.monotonic() < deadline,
             'bounded child cleanup failed; remaining PIDs: ' + ','.join(map(str, sorted(remaining))))
        time.sleep(0.01)

def run_process(argv, *, cwd, env, timeout, stdout, stderr, max_log_bytes, limits, allow_new_sessions=False):
    """Bounded Linux process-tree execution; never returns before clean reaping."""
    started = time.monotonic(); timed_out = overflow = memory_exceeded = False
    peak_rss = 0; surviving_children = escaped_descendants = False
    def apply_limits():
        resource.setrlimit(resource.RLIMIT_AS, (limits['address_space_bytes'],) * 2)
        resource.setrlimit(resource.RLIMIT_FSIZE, (limits['max_created_file_bytes'],) * 2)
        resource.setrlimit(resource.RLIMIT_CPU, (timeout + 1,) * 2)
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    old_subreaper = set_child_subreaper(True)
    baseline = {(pid, row['start_ticks']) for pid, row in proc_snapshot().items()
                if row['parent'] == os.getpid()}
    try:
        with stdout.open('xb') as out, stderr.open('xb') as err:
            process = subprocess.Popen(argv, cwd=cwd, env=env, stdout=out, stderr=err,
                                       stdin=subprocess.DEVNULL, start_new_session=True, preexec_fn=apply_limits)
            try:
                while process.poll() is None:
                    timed_out = time.monotonic() - started > timeout
                    overflow = stdout.stat().st_size + stderr.stat().st_size > max_log_bytes
                    owned = owned_processes(process.pid, baseline)
                    peak_rss = max(peak_rss, sum(r['rss_bytes'] for r in owned.values()))
                    escaped_descendants = escaped_descendants or any(r['group'] != process.pid for r in owned.values())
                    memory_exceeded = peak_rss > limits['rss_tree_bytes']
                    if timed_out or overflow or memory_exceeded or (escaped_descendants and not allow_new_sessions): break
                    time.sleep(0.05)
                owned = owned_processes(process.pid, baseline)
                escaped_descendants = escaped_descendants or any(r['group'] != process.pid for r in owned.values())
                if process.poll() is not None:
                    surviving_children = any(pid != process.pid and row['state'] != 'Z'
                                             for pid, row in owned.items())
            finally:
                # This also runs on monitoring errors. Failure to prove cleanup raises.
                cleanup = terminate_owned_processes(process, baseline)
    finally:
        set_child_subreaper(old_subreaper)
    overflow = overflow or stdout.stat().st_size + stderr.stat().st_size > max_log_bytes
    return {'exit_code': process.returncode, 'timed_out': timed_out, 'log_overflow': overflow,
            'memory_exceeded': memory_exceeded, 'surviving_children': surviving_children,
            'escaped_descendants': escaped_descendants, 'new_sessions_explicitly_allowed': allow_new_sessions, **cleanup,
            'peak_sampled_tree_rss_bytes': peak_rss,
            'elapsed_seconds': round(time.monotonic() - started, 6)}

def object_paths(module, suffixes):
    return ['objects/' + module.replace('.', '/') + suffix for suffix in suffixes]

def log_paths(module):
    base = 'logs/' + module.replace('.', '/')
    return [base + '.' + phase + '.' + stream for phase in ('compile', 'check') for stream in ('stdout', 'stderr')]

def write_tar(path: Path, files: dict[str, Path], receipt: dict, maximum: int):
    data = json_bytes(receipt)
    need(sum(x.stat().st_size for x in files.values()) + len(data) < maximum, 'artifact payload budget exceeded')
    with tarfile.open(path, 'x', format=tarfile.USTAR_FORMAT) as archive:
        for name, source in [('receipt.json', None), *sorted(files.items())]:
            safe_rel(name)
            info = tarfile.TarInfo(name); info.mode = 0o644
            if source is None:
                info.size = len(data); archive.addfile(info, io.BytesIO(data))
            else:
                info.size = source.stat().st_size
                with source.open('rb') as handle: archive.addfile(info, handle)
    need(path.stat().st_size <= maximum, 'artifact archive budget exceeded')
    return sha(data)

def extract_verified_archive(archive_path: Path, descriptor: dict, destination: Path, maximum: int):
    no_symlink_path(archive_path)
    need(archive_path.is_file() and archive_path.stat().st_size <= maximum, 'missing/oversized artifact')
    need(SHA256.fullmatch(descriptor.get('archive_sha256', '')) and
         file_sha(archive_path) == descriptor['archive_sha256'], 'artifact digest mismatch')
    no_symlink_path(destination)
    need(not destination.exists(), 'artifact quarantine must be new')
    destination.mkdir(parents=True)
    names, total = set(), 0
    with tarfile.open(archive_path, 'r:') as archive:
        for member in archive:
            name = safe_rel(member.name)
            need(name not in names and member.isreg() and not member.pax_headers,
                 'duplicate/non-regular/pax archive member')
            names.add(name); total += member.size
            need(len(names) <= 100000 and total <= maximum, 'artifact member budget exceeded')
            out = destination / name; out.parent.mkdir(parents=True, exist_ok=True)
            reader = archive.extractfile(member)
            need(reader is not None, 'missing archive member content')
            with out.open('xb') as handle:
                for block in iter(lambda: reader.read(1024 * 1024), b''): handle.write(block)
            need(out.stat().st_size == member.size, 'truncated archive member')
    need('receipt.json' in names, 'missing receipt')
    receipt_path = destination / 'receipt.json'
    need(file_sha(receipt_path) == descriptor['receipt_sha256'], 'receipt digest mismatch')
    receipt = load_json(receipt_path)
    need(set(receipt['files']) | {'receipt.json'} == names, 'unlisted/missing artifact entry')
    for name, info in receipt['files'].items():
        safe_rel(name); path = destination / name
        need(path.stat().st_size == info['bytes'] and file_sha(path) == info['sha256'], 'artifact member hash mismatch')
    return receipt

class StageRunner:
    def __init__(self, *, contract, manifest, plan, profiles, identity, source_root, toolchain_root,
                 toolchain_inventory, workspace, executor: Callable = run_process):
        self.contract, self.manifest, self.plan, self.profiles = contract, manifest, plan, profiles
        self.entries, self.stages, self.owner = validate_contract(contract, manifest, plan, profiles)
        self.identity, self.source_root, self.toolchain_root = identity, Path(source_root), Path(toolchain_root)
        self.inventory, self.workspace, self.executor = toolchain_inventory, Path(workspace), executor
        need(identity['source_commit'] == contract['source_commit'], 'run/source commit mismatch')
        for name in ('run_id', 'run_attempt'):
            need(re.fullmatch(r'[1-9][0-9]*', identity[name]), f'invalid {name}')
        need(identity.get('run_started_at') is not None, 'trusted initial run timestamp required')
        self.objects = {}
        self.records = {}
        self.predecessor_descriptors = []

    def check_run_age(self):
        try:
            started = datetime.fromisoformat(self.identity['run_started_at'].replace('Z', '+00:00'))
            need(started.tzinfo is not None, 'run timestamp must include timezone')
            age = (datetime.now(timezone.utc) - started).total_seconds()
        except (TypeError, ValueError) as error:
            raise Rejected('invalid run timestamp') from error
        need(0 <= age <= self.contract['max_run_age_seconds'], 'run expired/incomplete; artifacts must not be renewed')

    def expected_argv(self, module, profile, phase):
        if phase == 'compile':
            return [str(self.toolchain_root / 'bin/lean'), *profile['compile_flags'], '-o',
                    str(self.workspace / object_paths(module, ['.olean'])[0]), self.entries[module]['path']]
        return [str(self.toolchain_root / 'bin/leanchecker'), *profile['check_flags'], module]

    def imported(self, module):
        entry = self.entries[module]
        imports = ([('implicit', 'Init')] if entry['implicit_Init'] else []) + [('explicit', x) for x in entry['ordered_imports']]
        result = []
        for kind, dependency in imports:
            if dependency in self.entries:
                need(dependency in self.objects, f'missing checked predecessor: {dependency}')
                outputs = self.objects[dependency]
            else:
                prefix = 'lib/lean/' + dependency.replace('.', '/')
                outputs = {name: info['sha256'] for name, info in self.inventory['files'].items()
                           if name in {prefix + suffix for suffix in SUFFIXES}}
                need(prefix + '.olean' in outputs, f'missing pinned external object: {dependency}')
            result.append({'kind': kind, 'module': dependency, 'outputs': outputs})
        return result

    def read_predecessors(self, sid, descriptors):
        return self.read_artifacts(self.stages[sid]['required_predecessors'], descriptors)

    def read_artifacts(self, expected, descriptors):
        need(expected == [sid for sid in self.stages if sid in set(expected)], 'artifact restore order/duplicates')
        need([x['stage_id'] for x in descriptors] == expected, 'wrong/missing/duplicate/unordered predecessor set')
        restored = 0
        for descriptor in descriptors:
            self.check_run_age()
            archive_path = Path(descriptor['archive_path'])
            no_symlink_path(archive_path)
            restored += archive_path.stat().st_size
            need(restored <= self.contract['max_restored_bytes'], 'aggregate restored artifact budget exceeded')
            need(descriptor.get('producer_conclusion') == 'success', 'predecessor producer was not successful')
            producer = descriptor['stage_id']
            need(descriptor['identity'] == self.identity, 'cross-run/source/toolchain artifact rejected')
            need(descriptor['producer_job'] == self.stages[producer]['producer_job'], 'wrong producer job')
            need(type(descriptor['artifact_id']) is int and descriptor['artifact_id'] > 0 and
                 type(descriptor['producer_job_id']) is int and descriptor['producer_job_id'] > 0,
                 'verified same-run artifact and producer job IDs required')
            quarantine = self.workspace / 'quarantine' / producer
            receipt = extract_verified_archive(Path(descriptor['archive_path']), descriptor, quarantine,
                                               self.contract['max_artifact_bytes'])
            need(receipt['status'] == 'fresh_compile_check_pairs_only' and receipt['identity'] == self.identity and
                 receipt['stage_id'] == producer and receipt['producer_job'] == descriptor['producer_job'],
                 'receipt provenance mismatch')
            need([x['module'] for x in receipt['modules']] == self.stages[producer]['modules'], 'wrong receipt module set/order')
            expected_chain = [x for x in self.predecessor_descriptors if x['stage_id'] in self.stages[producer]['required_predecessors']]
            need(receipt['predecessors'] == expected_chain, 'predecessor receipt chain mismatch')
            expected_files = set()
            for record in receipt['modules']:
                module = record['module']; profile_id = self.profiles['module_profiles'][module]
                need(record['source_sha256'] == self.entries[module]['sha256'] and record['profile'] == profile_id,
                     'receipt source/profile mismatch')
                need(record['ordered_imports'] == self.imported(module), 'predecessor import/object hash mismatch')
                outputs = object_paths(module, self.contract['output_suffixes'])
                need(set(record['outputs']) == set(outputs), 'wrong output set')
                for phase in ('compile', 'check'):
                    command = record[phase]
                    need(command['exit_code'] == 0 and command['timed_out'] is False and command['log_overflow'] is False and command.get('memory_exceeded') is False and command.get('surviving_children') is False and command.get('escaped_descendants') is False and command.get('process_group_empty') is True and command.get('descendants_empty') is True,
                         'unsuccessful predecessor command')
                    # Paths differ between fresh VMs; compare canonical command specification, not old absolute paths.
                    need(command['spec'] == {'tool': 'lean' if phase == 'compile' else 'leanchecker',
                         'flags': self.profiles['profiles'][profile_id][phase + '_flags'], 'module': module,
                         'source': self.entries[module]['path'] if phase == 'compile' else None}, 'command spec mismatch')
                    paths = receipt['execution_paths']
                    need(all(Path(v).is_absolute() for v in paths.values()), 'invalid execution paths')
                    flags = self.profiles['profiles'][profile_id][phase + '_flags']
                    expected_argv = ([paths['toolchain_root'] + '/bin/lean', *flags, '-o',
                                     paths['workspace'] + '/' + object_paths(module, ['.olean'])[0], self.entries[module]['path']]
                                    if phase == 'compile' else [paths['toolchain_root'] + '/bin/leanchecker', *flags, module])
                    need(command['argv'] == expected_argv, 'actual command argv mismatch')
                    need(command['resource_limits'] == {k: self.profiles['profiles'][profile_id][k]
                         for k in ('address_space_bytes', 'rss_tree_bytes', 'max_created_file_bytes')}, 'resource limits mismatch')
                    for stream in ('stdout', 'stderr'):
                        name = 'logs/' + module.replace('.', '/') + '.' + phase + '.' + stream
                        need(command[stream] == receipt['files'][name], 'command log hash mismatch')
                for name in outputs:
                    need(record['outputs'][name] == receipt['files'][name]['sha256'], 'output hash mismatch')
                    destination = self.workspace / 'deps' / name.removeprefix('objects/')
                    need(not destination.exists(), 'duplicate/shadowed predecessor object')
                    destination.parent.mkdir(parents=True, exist_ok=True)
                    destination.write_bytes((quarantine / name).read_bytes())
                need(module not in self.objects, 'duplicate predecessor module')
                self.objects[module] = record['outputs']; expected_files.update(outputs + log_paths(module))
            need(set(receipt['files']) == expected_files, 'unexpected artifact files')
            self.predecessor_descriptors.append({k: v for k, v in descriptor.items() if k != 'archive_path'})
            shutil.rmtree(quarantine)  # Only this run's newly created, fully verified quarantine.

    def command(self, module, phase, profile, environment, deadline):
        self.check_run_age()
        logs = [self.workspace / ('logs/' + module.replace('.', '/') + '.' + phase + '.' + x)
                for x in ('stdout', 'stderr')]
        logs[0].parent.mkdir(parents=True, exist_ok=True)
        timeout = min(profile[phase + '_timeout_seconds'], int(deadline - time.monotonic()))
        need(timeout > 0, 'stage time budget exhausted')
        argv = self.expected_argv(module, profile, phase)
        result = self.executor(argv, cwd=self.source_root, env=environment, timeout=timeout,
                               stdout=logs[0], stderr=logs[1], max_log_bytes=self.contract['max_log_bytes'],
                               limits={k: profile[k] for k in ('address_space_bytes', 'rss_tree_bytes', 'max_created_file_bytes')})
        need(type(result.get('exit_code')) is int, 'missing true process exit')
        result = dict(result, argv=argv, timeout_seconds=timeout,
                      resource_limits={k: profile[k] for k in ('address_space_bytes', 'rss_tree_bytes', 'max_created_file_bytes')},
                      spec={'tool': 'lean' if phase == 'compile' else 'leanchecker',
                            'flags': profile[phase + '_flags'], 'module': module,
                            'source': self.entries[module]['path'] if phase == 'compile' else None})
        for stream, path in zip(('stdout', 'stderr'), logs):
            no_symlink_path(path)
            need(path.is_file(), 'missing command log')
            result[stream] = {'bytes': path.stat().st_size, 'sha256': file_sha(path)}
        need(sum(result[x]['bytes'] for x in ('stdout', 'stderr')) <= self.contract['max_log_bytes'], 'log budget exceeded')
        # Save failure diagnostics, but never emit an accepted receipt or artifact on failure.
        (self.workspace / 'last_command.json').write_bytes(json_bytes(result))
        need(result['exit_code'] == 0 and result['timed_out'] is False and result['log_overflow'] is False and result.get('memory_exceeded') is False and result.get('surviving_children') is False and result.get('escaped_descendants') is False and result.get('process_group_empty') is True and result.get('descendants_empty') is True,
             f'{phase} failed for {module}: {result["exit_code"]}')
        return result

    def run(self, sid, descriptors, producer_job):
        deadline = time.monotonic() + self.contract['job_timeout_seconds']
        need(sid in self.stages and producer_job == self.stages[sid]['producer_job'], 'wrong current stage/job')
        no_symlink_path(self.workspace)
        need(not self.workspace.exists(), 'workspace must be new; old outputs/locks/receipts are never reused')
        self.check_run_age()
        self.workspace.mkdir(parents=True)
        for name in ('objects', 'deps', 'scratch', 'logs'): (self.workspace / name).mkdir()
        verify_sources(self.source_root, self.manifest)
        archive_total = sum(Path(x['archive_path']).stat().st_size for x in descriptors)
        required_free = 3 * archive_total + 2 * self.contract['max_stage_output_bytes'] + self.contract['minimum_free_disk_bytes']
        need(shutil.disk_usage(self.workspace).free >= required_free, 'insufficient measured space for dependency/output copies')
        self.read_predecessors(sid, descriptors)
        original_deps = {name: file_sha(path) for name, path in regular_tree(self.workspace / 'deps').items()}
        # Lean resolves a module namespace from its first search root, so separate
        # own/dependency roots can shadow one another. Build in one complete
        # namespace tree; retain the separately verified predecessor copy for
        # immutable comparison. Only own_files are ever packed for upload.
        for name, path in regular_tree(self.workspace / 'deps').items():
            destination = self.workspace / 'objects' / name
            need(not destination.exists(), 'predecessor shadows a fresh output')
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(path, destination)
        def verify_predecessor_copies():
            # Check the fixed pinned predecessor list, not a broad filesystem scan.
            need(original_deps == {name: file_sha(self.workspace / 'deps' / name) for name in original_deps},
                 'predecessor objects changed')
            checked = {name.removeprefix('objects/'): digest for outputs in self.objects.values() for name, digest in outputs.items()}
            need(checked == {name: file_sha(self.workspace / 'objects' / name) for name in checked},
                 'unified-search predecessor objects changed')
        environment = {'PATH': str(self.toolchain_root / 'bin') + ':/usr/bin:/bin',
                       'HOME': str(self.workspace / 'scratch'), 'TMPDIR': str(self.workspace / 'scratch'),
                       'LANG': 'C.UTF-8', 'LC_ALL': 'C.UTF-8', 'LEAN_NUM_THREADS': '1',
                       'LEAN_PATH': os.pathsep.join(str(x) for x in [self.workspace / 'objects', self.toolchain_root / 'lib/lean'])}
        records, own_files = [], set()
        for module in self.stages[sid]['modules']:
            profile_id = self.profiles['module_profiles'][module]
            profile = self.profiles['profiles'][profile_id]
            imported = self.imported(module)
            output_names = object_paths(module, self.contract['output_suffixes'])
            (self.workspace / output_names[0]).parent.mkdir(parents=True, exist_ok=True)
            verify_predecessor_copies()
            compile_result = self.command(module, 'compile', profile, environment, deadline)
            verify_predecessor_copies()
            expected_outputs = set(original_deps) | {x.removeprefix('objects/') for x in own_files if x.startswith('objects/')}
            expected_outputs.update(x.removeprefix('objects/') for x in output_names)
            exact_tree(self.workspace / 'objects', expected_outputs)
            before_check = {x: file_sha(self.workspace / x) for x in output_names}
            verify_predecessor_copies()
            check_result = self.command(module, 'check', profile, environment, deadline)
            verify_predecessor_copies()
            need(before_check == {x: file_sha(self.workspace / x) for x in output_names}, 'checker changed output')
            need(module not in self.objects, 'duplicate new module')
            self.objects[module] = before_check
            records.append({'module': module, 'source_sha256': self.entries[module]['sha256'], 'profile': profile_id,
                            'ordered_imports': imported, 'outputs': before_check,
                            'compile': compile_result, 'check': check_result})
            own_files.update(output_names + log_paths(module))
            need(sum((self.workspace / name).stat().st_size for name in own_files) <= self.contract['max_stage_output_bytes'],
                 'aggregate stage output/log budget exceeded')
        verify_sources(self.source_root, self.manifest)
        need(original_deps == {name: file_sha(path) for name, path in regular_tree(self.workspace / 'deps').items()},
             'predecessor objects changed')
        need(original_deps == {name: file_sha(self.workspace / 'objects' / name) for name in original_deps},
             'unified-search predecessor objects changed')
        exact_tree(self.workspace / 'objects', set(original_deps) | {x.removeprefix('objects/') for x in own_files if x.startswith('objects/')})
        exact_tree(self.workspace / 'logs', {x.removeprefix('logs/') for x in own_files if x.startswith('logs/')})
        files = {name: self.workspace / name for name in sorted(own_files)}
        info = {name: {'sha256': file_sha(path), 'bytes': path.stat().st_size} for name, path in files.items()}
        for record in records:
            need(all(info[name]['sha256'] == value for name, value in record['outputs'].items()), 'earlier output changed')
        self.check_run_age()
        receipt = {'schema': 'fresh-stage-receipt-v1', 'status': 'fresh_compile_check_pairs_only',
                   'proof_pass_claimed': False, 'identity': self.identity, 'stage_id': sid, 'producer_job': producer_job,
                   'execution_paths': {'source_root': str(self.source_root), 'toolchain_root': str(self.toolchain_root),
                                       'workspace': str(self.workspace)},
                   'predecessors': self.predecessor_descriptors, 'modules': records, 'files': info}
        archive = self.workspace / 'delta.tar'
        receipt_sha = write_tar(archive, files, receipt, self.contract['max_artifact_bytes'])
        descriptor = {'schema': 'fresh-stage-upload-candidate-v1', 'stage_id': sid, 'producer_job': producer_job,
                      'identity': self.identity, 'archive_sha256': file_sha(archive), 'receipt_sha256': receipt_sha,
                      'archive_path': str(archive), 'archive_bytes': archive.stat().st_size,
                      'artifact_id': None, 'producer_job_id': None, 'producer_conclusion': None, 'retention_days': 7}
        (self.workspace / 'upload-candidate.json').write_bytes(json_bytes(descriptor))
        return descriptor

def pinned_load(path, expected):
    no_symlink_path(path)
    need(SHA256.fullmatch(expected or '') and file_sha(path) == expected, f'pinned file hash mismatch: {path}')
    return load_json(path)

def cli():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('contract', 'manifest', 'plan', 'profiles', 'source-root', 'source-archive', 'checkout', 'pipeline-checkout', 'toolchain-root',
                 'toolchain-archive', 'toolchain-inventory', 'predecessors', 'workspace', 'stage'):
        parser.add_argument('--' + name, required=True)
    parser.add_argument('--contract-sha256', required=True)
    args = parser.parse_args()
    contract = pinned_load(Path(args.contract), args.contract_sha256)
    need(contract.get('review_status') == 'reviewed_for_execution', 'INACTIVE: contract requires review')
    manifest = pinned_load(Path(args.manifest), contract['source_manifest_sha256'])
    plan = pinned_load(Path(args.plan), contract['plan_sha256'])
    profiles = pinned_load(Path(args.profiles), contract['profiles_sha256'])
    need(file_sha(Path(__file__)) == contract['runner_sha256'], 'runner implementation hash mismatch')
    validate_contract(contract, manifest, plan, profiles)
    checkout, source_root = Path(args.checkout).absolute(), Path(args.source_root).absolute()
    pipeline_checkout = Path(args.pipeline_checkout).absolute()
    no_symlink_path(pipeline_checkout)
    no_symlink_path(checkout); no_symlink_path(source_root)
    need(not source_root.is_relative_to(checkout), 'source extraction must be outside immutable checkout')
    def git(root, *argv):
        return subprocess.run(['/usr/bin/git', '-C', str(root), *argv], check=True,
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True).stdout.strip()
    need(git(checkout, 'rev-parse', 'HEAD') == contract['source_commit'], 'checkout commit mismatch')
    need(git(checkout, 'status', '--porcelain=v1', '--untracked-files=all', '--ignored') == '', 'checkout must be entirely clean')
    pipeline_commit = git(pipeline_checkout, 'rev-parse', 'HEAD')
    need(COMMIT.fullmatch(pipeline_commit) and os.environ.get('GITHUB_ACTIONS') == 'true' and
         os.environ.get('GITHUB_SHA') == pipeline_commit, 'pipeline checkout must match trusted GitHub event commit')
    need(git(pipeline_checkout, 'status', '--porcelain=v1', '--untracked-files=all', '--ignored') == '',
         'pipeline checkout must be entirely clean')
    for value in (args.manifest, args.source_archive):
        need(Path(value).absolute().is_relative_to(checkout), 'source package input must be in source commit checkout')
    for value in (args.contract, args.plan, args.profiles, __file__):
        need(Path(value).absolute().is_relative_to(pipeline_checkout), 'verifier input must be in pipeline commit checkout')
    workspace = Path(args.workspace).absolute()
    need(not workspace.is_relative_to(checkout) and not workspace.is_relative_to(pipeline_checkout) and
         not source_root.is_relative_to(pipeline_checkout), 'outputs/extracted source must be outside clean checkouts')
    need(shutil.disk_usage(checkout).free >= contract['minimum_free_disk_bytes'], 'insufficient measured free disk')
    extract_sources(Path(args.source_archive), source_root, manifest)
    inventory = verify_toolchain(Path(args.toolchain_root), Path(args.toolchain_archive), Path(args.toolchain_inventory), contract)
    identity = {'pipeline_commit': pipeline_commit, 'source_commit': contract['source_commit'], 'source_manifest_sha256': contract['source_manifest_sha256'],
                'plan_sha256': contract['plan_sha256'], 'profiles_sha256': contract['profiles_sha256'],
                'contract_sha256': args.contract_sha256, 'runner_sha256': contract['runner_sha256'],
                'lean_archive_sha256': TOOLCHAIN_SHA256, 'toolchain_inventory_sha256': contract['toolchain_inventory_sha256'],
                'run_started_at': os.environ.get('FRESH_CI_RUN_STARTED_AT', ''),
                'run_id': os.environ.get('GITHUB_RUN_ID', ''), 'run_attempt': os.environ.get('GITHUB_RUN_ATTEMPT', '')}
    runner = StageRunner(contract=contract, manifest=manifest, plan=plan, profiles=profiles, identity=identity,
                         source_root=source_root, toolchain_root=Path(args.toolchain_root), toolchain_inventory=inventory,
                         workspace=workspace)
    descriptor = runner.run(args.stage, load_json(Path(args.predecessors)), os.environ.get('GITHUB_JOB', ''))
    print(json.dumps(descriptor, sort_keys=True))

if __name__ == '__main__':
    try: cli()
    except (Rejected, KeyError, TypeError, ValueError, OSError, subprocess.SubprocessError, tarfile.TarError) as error:
        raise SystemExit(f'FAIL CLOSED: {error}')
