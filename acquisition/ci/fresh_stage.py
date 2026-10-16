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
MODERN_SUFFIXES = ['.olean', '.olean.private', '.olean.server', '.ilean', '.ir', '.ir.sig']
SUFFIXES = set(MODERN_SUFFIXES)

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

def require_modern_header(data: bytes):
    """Require the first genuine token to be the modern module header."""
    depth = 0
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
        if value:
            need(value == 'module' and depth == 0, 'legacy/noncanonical source forbidden in modern stage')
            return
    raise Rejected('missing modern module header')

def verify_sources(root: Path, manifest: dict) -> dict[str, dict]:
    entries = manifest_index(manifest)
    files = exact_tree(root, {x['path'] for x in entries.values()})
    for entry in entries.values():
        data = files[entry['path']].read_bytes()
        need(len(data) == entry['bytes'] and sha(data) == entry['sha256'], 'source hash/size mismatch')
        require_modern_header(data)
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
    need([x for x in profile['compile_flags'] if x.startswith('-Dcompiler.postponeCompile=')] == ['-Dcompiler.postponeCompile=false'],
         'modern stage must explicitly emit IR; postponed compilation is forbidden')
    for name in ('address_space_bytes', 'rss_tree_bytes'):
        positive_int(profile[name], name, 12 * 1024**3)
    positive_int(profile['max_created_file_bytes'], 'created file bytes', 4 * 1024**3)
    need(set(profile['check_flags']) <= {'--silent', '-v', '--verbose'}, 'unsupported per-module checker flag')
    # Lean memory/heartbeat flags are reviewed strings, never inferred from historical receipts.
    need(any(re.fullmatch(r'-M[1-9][0-9]*', x) for x in profile['compile_flags']), 'finite Lean memory limit required')

def validate_contract(contract, manifest, plan, profiles):
    need(contract.get('review_status') == 'reviewed_for_execution', 'INACTIVE: pipeline review is pending')
    need(contract.get('storage_adapter_review_status') == 'reviewed', 'INACTIVE: storage adapter review is pending')
    need(contract.get('readonly_commit_review_status') == 'reviewed', 'INACTIVE: readonly committed-root review is pending')
    need(contract.get('receipt_protocol') == 'readonly_committed_v1', 'unsupported readonly receipt protocol')
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
    need(contract.get('module_interface') == 'modern_exposed_v1', 'modern interface contract required')
    need(contract['output_suffixes'] == MODERN_SUFFIXES, 'modern stage requires all six exact companions')
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
    # USTAR is uncompressed: headers/padding/end records are known before write.
    sizes = [len(data)] + [source.stat().st_size for source in files.values()]
    tar_bytes = sum(512 + ((n + 511) // 512) * 512 for n in sizes) + 1024
    tar_bytes = ((tar_bytes + tarfile.RECORDSIZE - 1) // tarfile.RECORDSIZE) * tarfile.RECORDSIZE
    need(tar_bytes <= maximum, 'artifact archive budget exceeded before packing')
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
    need(file_sha(archive_path) == descriptor['archive_sha256'], 'artifact changed during extraction')
    return receipt

class OwnedStageDownloads:
    """Authority to release ONLY files created beneath this fresh current-run root.

    This object stays in trusted process memory, never in artifact descriptors.
    External descriptors therefore cannot request deletion. No hardlinks allowed.
    """
    def __init__(self, root):
        self.root = Path(root).absolute()
        no_symlink_path(self.root)
        need(not self.root.exists(), 'download ownership root must be new')
        self.root.mkdir(parents=True, mode=0o700)
        self.root_identity = self._identity(self.root)
        self.claimed = {}

    @staticmethod
    def _identity(path):
        st = path.lstat()
        return (st.st_dev, st.st_ino, st.st_uid)

    def claim(self, descriptor):
        # Only the trusted downloader calls this after creating a new stage dir.
        path = Path(descriptor['archive_path']).absolute()
        safe_rel(descriptor['stage_id'])
        need('/' not in descriptor['stage_id'], 'invalid owned stage name')
        need(path == self.root / descriptor['stage_id'] / 'delta.tar', 'archive outside owned download root')
        need(str(path) not in self.claimed, 'archive already claimed')
        no_symlink_path(path)
        st = path.lstat()
        need(stat.S_ISREG(st.st_mode) and st.st_nlink == 1 and st.st_uid == os.geteuid(), 'archive ownership or hardlink mismatch')
        need(self._identity(self.root) == self.root_identity, 'download root changed')
        need(st.st_size == descriptor['archive_bytes'] and file_sha(path) == descriptor['archive_sha256'], 'owned download hash/size mismatch')
        self.claimed[str(path)] = {'identity': self._identity(path), 'parent': self._identity(path.parent),
            'size': st.st_size, 'mtime_ns': st.st_mtime_ns, 'ctime_ns': st.st_ctime_ns,
            'sha256': descriptor['archive_sha256']}

    def release_after_validation(self, descriptor, evidence):
        path = Path(descriptor['archive_path']).absolute()
        registered = self.claimed.get(str(path))
        if registered is None:
            return False  # Supplied/external originals are never deleted.
        no_symlink_path(path)
        st = path.lstat()
        need(self._identity(self.root) == self.root_identity and self._identity(path.parent) == registered['parent'], 'owned download directory changed')
        need(self._identity(path) == registered['identity'] and st.st_nlink == 1 and
             st.st_size == registered['size'] and st.st_mtime_ns == registered['mtime_ns'] and
             st.st_ctime_ns == registered['ctime_ns'], 'owned archive replaced or changed')
        need(file_sha(path) == registered['sha256'] == descriptor['archive_sha256'], 'owned archive changed before release')
        # Durable evidence is committed before deletion. All payload files remain
        # either in unified objects or in this retained receipt/log directory.
        record = {'schema': 'owned-stage-archive-release-v1', 'status': 'validated_ready_to_release',
            'descriptor': {k:v for k,v in descriptor.items() if k != 'archive_path'},
            'released_archive_bytes': st.st_size, 'payload_retained': True,
            'proof_pass_claimed': False}
        target = evidence / 'archive-release.json'
        with target.open('xb') as handle:
            handle.write(json_bytes(record)); handle.flush(); os.fsync(handle.fileno())
        fd = os.open(evidence, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
        try: os.fsync(fd)
        finally: os.close(fd)
        path.unlink()
        del self.claimed[str(path)]
        record['status'] = 'released'
        # Preserve the durable pre-unlink record until the updated record is
        # fully written. Interrupted writes leave the initial status readable.
        updated = evidence / 'archive-release.updated.json'
        with updated.open('xb') as handle:
            handle.write(json_bytes(record)); handle.flush(); os.fsync(handle.fileno())
        updated.replace(target)
        fd = os.open(evidence, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
        try: os.fsync(fd)
        finally: os.close(fd)
        fd = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
        try: os.fsync(fd)
        finally: os.close(fd)
        return True

def storage_restore_budget(descriptors, contract, *, build=True, stages=None, allocation_unit=4096):
    """Bound peak additional storage of the accepted layout, without delete credit.

    Preflight headers bound physical payload allocation (rounded per file),
    directory/inode allowance, and exact generated restore journals. Own output
    allowance and bounded tar packing remain separate. Child arbitrary scratch
    writes remain governed by the unchanged process controls, not a disk quota.
    """
    need(type(allocation_unit) is int and allocation_unit > 0, 'invalid filesystem allocation unit')
    unit = max(4096, allocation_unit)
    rounded = lambda n: ((n + unit - 1) // unit) * unit
    archive_total = payload_peak = metadata_peak = 0
    for descriptor in descriptors:
        path = Path(descriptor['archive_path']); no_symlink_path(path)
        size = path.stat().st_size
        need(size == descriptor['archive_bytes'] and 0 < size <= contract['max_artifact_bytes'], 'missing/oversized/misreported artifact')
        archive_total += size
        need(archive_total <= contract['max_restored_bytes'], 'aggregate restored artifact budget exceeded')
        names, directories, unpacked = set(), set(), 0
        with tarfile.open(path, 'r:') as archive:
            for member in archive:
                name = safe_rel(member.name)
                need(name not in names and member.isreg() and not member.pax_headers,
                     'duplicate/non-regular/pax archive member in storage preflight')
                names.add(name); unpacked += member.size
                need(len(names) <= 100000 and 0 <= member.size and unpacked <= contract['max_artifact_bytes'],
                     'artifact member budget exceeded in storage preflight')
                payload_peak += rounded(member.size) + unit  # file + inode/metadata allowance
                directories.update(str(p) for p in PurePosixPath(name).parents if str(p) != '.')
        need(unpacked <= size, 'uncompressed artifact payload exceeds archive')
        payload_peak += unit * (len(directories) + 4)  # quarantine/evidence/object roots
        need(stages is not None and descriptor['stage_id'] in stages, 'storage preflight stage map required')
        outputs = [name for module in stages[descriptor['stage_id']]['modules'] for name in object_paths(module, contract['output_suffixes'])]
        public_descriptor = {k:v for k,v in descriptor.items() if k != 'archive_path'}
        state = {'status': 'validated_move_pending', 'descriptor': public_descriptor,
                 'objects': {name:'0'*64 for name in outputs}, 'moved': outputs, 'proof_pass_claimed': False}
        release = {'schema': 'owned-stage-archive-release-v1', 'status': 'validated_ready_to_release',
                   'descriptor': public_descriptor, 'released_archive_bytes': size,
                   'payload_retained': True, 'proof_pass_claimed': False}
        metadata_peak += rounded(len(json_bytes(state))) + 2*rounded(len(json_bytes(release))) + 3*unit
    own_peak = 0
    if build:
        # Conservative output-file/directory overhead for the entire selected
        # closure, even though a build emits only its own stage. No cap increase.
        modules = [m for stage in (stages or {}).values() for m in stage['modules']]
        own_names = [name for module in modules for name in object_paths(module, contract['output_suffixes']) + log_paths(module)]
        own_dirs = {str(p) for name in own_names for p in PurePosixPath(name).parents if str(p) != '.'}
        own_peak = rounded(contract['max_stage_output_bytes']) + rounded(contract['max_artifact_bytes'])
        own_peak += unit * (2 * len(own_names) + len(own_dirs) + 8)
    # Existing reserve remains untouched. Bounded local runner metadata is
    # budgeted separately (last-command/descriptor and restore accounting).
    return payload_peak + metadata_peak + own_peak + 1024**2 + contract['minimum_free_disk_bytes']

READONLY_PROTOCOL = 'readonly_committed_v1'

def readonly_command_layout(paths, module, source, flags, phase):
    """Exact no-network sandbox boundary; no fallback and no inherited env."""
    need(phase in ('compile', 'check'), 'invalid readonly phase')
    need(re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.]*', module), 'invalid module path')
    need(all(Path(paths[k]).is_absolute() for k in ('source_root', 'toolchain_root', 'workspace')), 'readonly paths must be absolute')
    root, runtime, source_root = (Path(paths[k]) for k in ('workspace', 'toolchain_root', 'source_root'))
    committed = root / 'objects'; quarantine = root / 'module-quarantine' / module
    home, temp = root / 'scratch/home', root / 'scratch/tmp'
    environment = {'PATH':str(runtime / 'bin') + ':/usr/bin:/bin', 'HOME':str(home), 'TMPDIR':str(temp),
                   'LANG':'C.UTF-8', 'LC_ALL':'C.UTF-8', 'LEAN_NUM_THREADS':'1',
                   'LEAN_SYSROOT':str(runtime), 'LEAN_PATH':str(committed) + ':' + str(runtime / 'lib/lean')}
    relative = module.replace('.', '/')
    inner = ([str(runtime / 'bin/lean'), *flags, '-o', str(quarantine / ('objects/' + relative + '.olean')),
              '-i', str(quarantine / ('objects/' + relative + '.ilean')), source]
             if phase == 'compile' else [str(runtime / 'bin/leanchecker'), *flags, module])
    readonly = [runtime, source_root, committed]
    writable = [home, temp] + ([quarantine] if phase == 'compile' else [])
    for write in writable:
        for read in readonly:
            need(not write.is_relative_to(read) and not read.is_relative_to(write), 'overlapping readonly/writable mount')
    argv = ['/usr/bin/bwrap', '--unshare-all', '--die-with-parent', '--clearenv', '--proc', '/proc', '--dev', '/dev', '--tmpfs', '/tmp']
    # run_process starts one isolated session itself. No nested --new-session or
    # general escape allowance is introduced; existing escape rejection stays.
    for path in ['/usr', '/bin', '/lib', '/lib64']:
        argv += ['--ro-bind', path, path]
    for path in readonly: argv += ['--ro-bind', str(path), str(path)]
    for path in writable: argv += ['--bind', str(path), str(path)]
    for key,value in sorted(environment.items()): argv += ['--setenv', key, value]
    argv += ['--chdir', str(source_root), '--', *inner]
    layout = {'protocol':READONLY_PROTOCOL, 'readonly_roots':[str(p) for p in readonly],
              'writable_roots':[str(p) for p in writable], 'environment':environment, 'cwd':str(source_root)}
    return argv, inner, layout

class StageRunner:
    def __init__(self, *, contract, manifest, plan, profiles, identity, source_root, toolchain_root,
                 toolchain_inventory, workspace, executor: Callable = run_process, owned_downloads=None):
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
        self.owned_downloads = owned_downloads
        self.restore_evidence_hashes = {}

    def check_run_age(self):
        try:
            started = datetime.fromisoformat(self.identity['run_started_at'].replace('Z', '+00:00'))
            need(started.tzinfo is not None, 'run timestamp must include timezone')
            age = (datetime.now(timezone.utc) - started).total_seconds()
        except (TypeError, ValueError) as error:
            raise Rejected('invalid run timestamp') from error
        need(0 <= age <= self.contract['max_run_age_seconds'], 'run expired/incomplete; artifacts must not be renewed')

    def execution_paths(self):
        return {'source_root':str(self.source_root), 'toolchain_root':str(self.toolchain_root), 'workspace':str(self.workspace)}

    def expected_argv(self, module, profile, phase):
        return readonly_command_layout(self.execution_paths(), module, self.entries[module]['path'],
                                       profile[phase + '_flags'], phase)[0]

    def promote_quarantine(self, module, remaining_bytes):
        quarantine = self.workspace / 'module-quarantine' / module
        names = object_paths(module, self.contract['output_suffixes'])
        files = exact_tree(quarantine, set(names))
        info = {}
        total = 0
        for name in names:
            path=files[name]; st=path.stat()
            need(st.st_nlink == 1 and st.st_size > 0, 'quarantine output empty/shared')
            total += st.st_size
            need(total <= remaining_bytes, 'quarantine exceeds remaining stage output budget')
            info[name]={'bytes':st.st_size,'sha256':file_sha(path)}
            destination=self.workspace/name; no_symlink_path(destination)
            need(not destination.exists(), 'provisional output overwrite forbidden')
        journal=self.workspace/'promotion-state.json'
        state={'protocol':READONLY_PROTOCOL,'module':module,'status':'validated_provisional_move_pending',
               'outputs':info,'moved':[],'checker_passed':False,'proof_pass_claimed':False}
        journal.write_bytes(json_bytes(state))
        for name in names:
            fresh=files[name]; destination=self.workspace/name
            destination.parent.mkdir(parents=True,exist_ok=True);no_symlink_path(destination)
            need(not destination.exists(), 'provisional output destination appeared')
            fresh.rename(destination);destination.chmod(0o444)
            need(destination.stat().st_nlink == 1 and file_sha(destination)==info[name]['sha256'], 'provisional move changed output')
            state['moved'].append(name);journal.write_bytes(json_bytes(state))
        # Only this fresh quarantine's empty directories remain. A failed move
        # retains its journal and remaining bytes; no continuation is admitted.
        for path in sorted(quarantine.rglob('*'),key=lambda p:len(p.parts),reverse=True):
            need(path.is_dir(), 'unexpected file left in quarantine');path.rmdir()
        quarantine.rmdir()
        state['status']='provisional_awaiting_checker';journal.write_bytes(json_bytes(state))
        return {name:row['sha256'] for name,row in info.items()}, total

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
            need(archive_path.stat().st_size == descriptor['archive_bytes'], 'archive size does not match descriptor')
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
            need(receipt.get('receipt_protocol') == READONLY_PROTOCOL, 'old/non-readonly receipt protocol rejected')
            need(receipt['status'] == 'fresh_compile_check_pairs_only' and receipt['identity'] == self.identity and
                 receipt['stage_id'] == producer and receipt['producer_job'] == descriptor['producer_job'],
                 'receipt provenance mismatch')
            need([x['module'] for x in receipt['modules']] == self.stages[producer]['modules'], 'wrong receipt module set/order')
            expected_chain = [x for x in self.predecessor_descriptors if x['stage_id'] in self.stages[producer]['required_predecessors']]
            need(receipt['predecessors'] == expected_chain, 'predecessor receipt chain mismatch')
            expected_files, pending_moves = set(), []
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
                    expected_argv, inner, layout = readonly_command_layout(paths, module, self.entries[module]['path'], flags, phase)
                    need(command['argv'] == expected_argv and command.get('inner_argv') == inner, 'actual sandbox/inner command argv mismatch')
                    need(command.get('sandbox') == layout and command.get('new_sessions_explicitly_allowed') is False,
                         'readonly sandbox policy or session allowance mismatch')
                    need(command['resource_limits'] == {k: self.profiles['profiles'][profile_id][k]
                         for k in ('address_space_bytes', 'rss_tree_bytes', 'max_created_file_bytes')}, 'resource limits mismatch')
                    for stream in ('stdout', 'stderr'):
                        name = 'logs/' + module.replace('.', '/') + '.' + phase + '.' + stream
                        need(command[stream] == receipt['files'][name], 'command log hash mismatch')
                for name in outputs:
                    need(record['outputs'][name] == receipt['files'][name]['sha256'], 'output hash mismatch')
                    destination = self.workspace / name
                    need(not destination.exists(), 'duplicate/shadowed predecessor object')
                    pending_moves.append((name, destination, record['outputs'][name]))
                need(module not in self.objects, 'duplicate predecessor module')
                self.objects[module] = record['outputs']; expected_files.update(outputs + log_paths(module))
            need(set(receipt['files']) == expected_files, 'unexpected artifact files')
            # No acceptance/move/release until the entire receipt and file set
            # validate. Failed/interrupted restores keep archives and quarantine.
            journal = quarantine / 'restore-state.json'
            state = {'status': 'validated_move_pending', 'descriptor': {k:v for k,v in descriptor.items() if k != 'archive_path'},
                     'objects': {name:digest for name,_,digest in pending_moves}, 'moved': [], 'proof_pass_claimed': False}
            journal.write_bytes(json_bytes(state))
            for name, destination, digest in pending_moves:
                fresh = quarantine / name; no_symlink_path(fresh)
                need(fresh.stat().st_nlink == 1 and file_sha(fresh) == digest, 'fresh quarantine object changed/shared')
                no_symlink_path(destination)
                destination.parent.mkdir(parents=True, exist_ok=True)
                no_symlink_path(destination)
                fresh.chmod(0o444)
                fresh.rename(destination)  # Same-workspace rename, no copy/link.
                need(destination.stat().st_nlink == 1 and file_sha(destination) == digest, 'restored object changed/shared')
                state['moved'].append(name); journal.write_bytes(json_bytes(state))
            # Keep receipt and complete predecessor command logs as evidence.
            # Remove only empty object directories left by the moves.
            for directory in sorted((quarantine / 'objects').rglob('*'), key=lambda p:len(p.parts), reverse=True):
                if directory.is_dir(): directory.rmdir()
            (quarantine / 'objects').rmdir()
            state['status'] = 'restored_verified'; journal.write_bytes(json_bytes(state))
            evidence = self.workspace / 'restore-evidence' / producer
            evidence.parent.mkdir(exist_ok=True)
            need(not evidence.exists(), 'restore evidence must be new')
            quarantine.rename(evidence)
            self.verify_checked_objects()
            self.predecessor_descriptors.append({k: v for k, v in descriptor.items() if k != 'archive_path'})
            if self.owned_downloads is not None:
                # Preserve complete accepted bytes before releasing their tar.
                # These fsyncs are outside commands and only touch fresh copies.
                retained = [self.workspace / name for name,_,_ in pending_moves] + list(regular_tree(evidence).values())
                directories = {self.workspace, evidence, evidence.parent}
                for path in retained:
                    with path.open('rb') as handle: os.fsync(handle.fileno())
                    for parent in path.parents:
                        directories.add(parent)
                        if parent == self.workspace: break
                for directory in sorted(directories, key=lambda p:len(p.parts), reverse=True):
                    fd = os.open(directory, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
                    try: os.fsync(fd)
                    finally: os.close(fd)
                self.owned_downloads.release_after_validation(descriptor, evidence)
            self.restore_evidence_hashes[producer] = {name:file_sha(path) for name,path in regular_tree(evidence).items()}
        exact_tree(self.workspace / 'objects', {name.removeprefix('objects/') for outputs in self.objects.values() for name in outputs})

    def verify_checked_objects(self):
        checked = {name: digest for outputs in self.objects.values() for name, digest in outputs.items()}
        for name, digest in checked.items():
            path = self.workspace / name; no_symlink_path(path)
            need(path.is_file() and path.stat().st_nlink == 1 and file_sha(path) == digest,
                 'pinned unified-search object changed/shared: ' + name)
        for producer, expected in self.restore_evidence_hashes.items():
            evidence = self.workspace / 'restore-evidence' / producer
            files = exact_tree(evidence, set(expected))
            need(all(path.stat().st_nlink == 1 and file_sha(path) == expected[name] for name,path in files.items()),
                 'accepted restore evidence changed/shared: ' + producer)

    def command(self, module, phase, profile, environment, deadline):
        self.check_run_age()
        logs = [self.workspace / ('logs/' + module.replace('.', '/') + '.' + phase + '.' + x)
                for x in ('stdout', 'stderr')]
        logs[0].parent.mkdir(parents=True, exist_ok=True)
        timeout = min(profile[phase + '_timeout_seconds'], int(deadline - time.monotonic()))
        need(timeout > 0, 'stage time budget exhausted')
        argv, inner, layout = readonly_command_layout(self.execution_paths(), module, self.entries[module]['path'], profile[phase + '_flags'], phase)
        need(environment == layout['environment'], 'readonly command environment mismatch')
        for path in layout['readonly_roots'] + layout['writable_roots']:
            no_symlink_path(Path(path)); need(Path(path).is_dir(), 'sandbox mount is missing')
        result = self.executor(argv, cwd=self.source_root, env=environment, timeout=timeout,
                               stdout=logs[0], stderr=logs[1], max_log_bytes=self.contract['max_log_bytes'],
                               limits={k: profile[k] for k in ('address_space_bytes', 'rss_tree_bytes', 'max_created_file_bytes')})
        need(type(result.get('exit_code')) is int, 'missing true process exit')
        result = dict(result, argv=argv, inner_argv=inner, sandbox=layout, timeout_seconds=timeout,
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
        for name in ('objects', 'scratch', 'logs', 'module-quarantine'): (self.workspace / name).mkdir()
        for name in ('home','tmp'): (self.workspace / 'scratch' / name).mkdir()
        verify_sources(self.source_root, self.manifest)
        required_free = storage_restore_budget(descriptors, self.contract, stages=self.stages, allocation_unit=os.statvfs(self.workspace).f_frsize)
        need(shutil.disk_usage(self.workspace).free >= required_free, 'insufficient measured space for unified restore/output peak')
        self.read_predecessors(sid, descriptors)
        original_deps = {name.removeprefix('objects/'): digest for outputs in self.objects.values() for name, digest in outputs.items()}
        # Single namespace, independently extracted inodes, receipt-pinned hashes.
        # Already checked outputs from this stage join the same immutable list.
        first_module=self.stages[sid]['modules'][0]
        environment=readonly_command_layout(self.execution_paths(), first_module, self.entries[first_module]['path'], [], 'check')[2]['environment']
        records, own_files, own_bytes = [], set(), 0
        for module in self.stages[sid]['modules']:
            profile_id = self.profiles['module_profiles'][module]
            profile = self.profiles['profiles'][profile_id]
            imported = self.imported(module)
            output_names = object_paths(module, self.contract['output_suffixes'])
            quarantine=self.workspace/'module-quarantine'/module
            need(not quarantine.exists(), 'module quarantine must be new')
            (quarantine/output_names[0]).parent.mkdir(parents=True)
            compile_result = self.command(module, 'compile', profile, environment, deadline)
            before_check, current_bytes = self.promote_quarantine(module, self.contract['max_stage_output_bytes']-own_bytes)
            check_result = self.command(module, 'check', profile, environment, deadline)
            need(before_check == {x: file_sha(self.workspace / x) for x in output_names}, 'checker changed output')
            need(module not in self.objects, 'duplicate new module')
            self.objects[module] = before_check
            promotion=load_json(self.workspace/'promotion-state.json');promotion['status']='checker_passed';promotion['checker_passed']=True
            (self.workspace/'promotion-state.json').write_bytes(json_bytes(promotion))
            records.append({'module': module, 'source_sha256': self.entries[module]['sha256'], 'profile': profile_id,
                            'ordered_imports': imported, 'outputs': before_check,
                            'compile': compile_result, 'check': check_result})
            own_files.update(output_names + log_paths(module))
            own_bytes += current_bytes + sum((self.workspace/name).stat().st_size for name in log_paths(module))
            need(own_bytes <= self.contract['max_stage_output_bytes'],
                 'aggregate stage output/log budget exceeded')
        verify_sources(self.source_root, self.manifest)
        self.verify_checked_objects()
        exact_tree(self.workspace / 'objects', set(original_deps) | {x.removeprefix('objects/') for x in own_files if x.startswith('objects/')})
        exact_tree(self.workspace / 'logs', {x.removeprefix('logs/') for x in own_files if x.startswith('logs/')})
        files = {name: self.workspace / name for name in sorted(own_files)}
        info = {name: {'sha256': file_sha(path), 'bytes': path.stat().st_size} for name, path in files.items()}
        for record in records:
            need(all(info[name]['sha256'] == value for name, value in record['outputs'].items()), 'earlier output changed')
        self.check_run_age()
        receipt = {'schema': 'fresh-stage-receipt-v1', 'receipt_protocol':READONLY_PROTOCOL, 'status': 'fresh_compile_check_pairs_only',
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
