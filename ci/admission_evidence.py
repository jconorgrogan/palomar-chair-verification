"""Load a fixed historical admission witness, never proof payloads or executables.

The reviewed driver supplies its authenticated CurrentOriginTransport and an
original-budget check_deadline() returning remaining seconds. This module does
not construct a transport, reset a budget, import validators, or execute code
from evidence. The frozen input pin must itself be hash-pinned by that driver.
An independently reviewed strict projection and unchanged raw review are required
as sibling ADMISSION_RECONCILIATION.json and ADMISSION_INDEPENDENT_REVIEW.json.
Runtime checks are additional to those distinct witnesses.
"""
from __future__ import annotations

import base64
import contextlib
import copy
import hashlib
import json
import math
import os
from pathlib import Path, PurePosixPath
import re
import stat
import time
import urllib.error
import urllib.parse
import zipfile
from datetime import datetime, timezone

FIXED_PIN_SHA256 = '71cadf57e76113755dce36610124c87444d61b121e3d6ecdd4c44e2d539872fe'
RECONCILIATION_SHA256 = 'd259eea653bf446a90607ded5add7176cfb50388e261327cf5e136b03e7da190'
INDEPENDENT_REVIEW_SHA256 = '2003b7484bdb5b0fa2961f7ea77a78c8edcec6c754e96a5db12d149b760aef26'
REPO = 'jconorgrogan/palomar-chair-verification'
PREFIX = '/repos/' + REPO
MAX_EVIDENCE = 64 * 1024**2
MAX_LOG = 1024**2
MAX_RECONCILIATION = 1024**2
RESERVE_BYTES = 128 * 1024**2
RESERVE_INODES = 1024
CHUNK = 64 * 1024
MARKER = 'HIERARCHY_NATIVE_ADMISSION_UPLOAD='
COMPLETION = 'semantic-write/output/COMPLETION.json'
SELECTION = 'semantic-write/output/SELECTED_CANDIDATE.json'
NATIVE = 'semantic-write/output/NATIVE_VALIDATION.json'


class AdmissionRejected(RuntimeError):
    """Sanitized, terminal fail-closed rejection."""


# Diagnostics are fixed local labels only. They cannot authorize continuation.
_DIAGNOSTIC_PHASES = frozenset({
    'pin_validation', 'deadline', 'destination', 'reconciliation_read', 'review_read',
    'capacity', 'snapshot_deadline', 'run_metadata', 'job_metadata', 'workflow_metadata',
    'commit_metadata', 'workflow_source', 'artifact_listing', 'artifact_metadata',
    'log_request', 'log_guard', 'log_open', 'log_redirect', 'log_read', 'log_decode',
    'log_marker', 'projection_binding', 'create_destination', 'copy_witnesses',
    'zip_guard', 'zip_open', 'zip_read', 'zip_hash', 'evidence_guard', 'evidence_extract',
    'evidence_validate', 'identity_comparison', 'rehash_evidence', 'rehash_zip',
    'rehash_witnesses', 'final_identity', 'complete'})
_DIAGNOSTIC_CLASSES = frozenset({
    'Rejected', 'Expired', 'HTTPError', 'URLError', 'TimeoutError', '_MetadataWallTimeout',
    '_MetadataHardTimeout', 'FileNotFoundError', 'PermissionError', 'FileExistsError',
    'OSError', 'InterruptedError', 'ConnectionError', 'ConnectionResetError',
    'ConnectionAbortedError', 'BrokenPipeError', 'BadZipFile', 'LargeZipFile',
    'ValueError', 'TypeError', 'KeyError', 'AttributeError', 'RuntimeError',
    'UnicodeDecodeError', 'UnicodeEncodeError', 'OverflowError', 'MemoryError',
    'RecursionError', 'KeyboardInterrupt', 'SystemExit'})


def _phase(diagnostic, value):
    if diagnostic is not None:
        diagnostic['phase'] = value if value in _DIAGNOSTIC_PHASES else 'unknown'


_LOCAL_REJECTION_REASONS = {
    'invalid shared metadata budget': 'shared_metadata_budget_invalid',
    'invalid metadata monotonic clock': 'metadata_clock_invalid',
    'metadata aggregate/origin deadline exceeded': 'metadata_deadline_exceeded',
    'metadata request hard deadline exceeded': 'metadata_hard_deadline_exceeded',
    'metadata wall guard refuses an existing timer': 'metadata_alarm_already_active',
    'metadata wall guard requires the main thread': 'metadata_main_thread_required',
    'invalid absolute metadata deadline': 'metadata_absolute_deadline_invalid',
    'metadata absolute deadline exceeded': 'metadata_absolute_deadline_exceeded',
    'invalid metadata wall limit': 'metadata_wall_limit_invalid',
    'origin deadline exceeded; no age renewal': 'origin_deadline_exceeded',
    'trusted aware clock required': 'aware_clock_required',
    'current clock moved backward': 'current_clock_backward',
    'GitHub metadata status is not 200': 'metadata_non_success_status',
    'GitHub metadata object required': 'metadata_object_required',
    'invalid GitHub metadata JSON': 'metadata_json_invalid',
    'oversized GitHub metadata': 'metadata_size_exceeded',
    'metadata response cleanup failed': 'metadata_cleanup_failed',
    'metadata error-response cleanup failed': 'metadata_error_cleanup_failed',
    'authenticated GitHub metadata read or cleanup failed': 'metadata_read_or_cleanup_failed',
    'authenticated GitHub metadata read failed': 'metadata_read_failed',
    'metadata backoff deadline exceeded': 'metadata_backoff_deadline_exceeded',
    'metadata backoff would exceed aggregate/origin deadline': 'metadata_backoff_budget_exceeded',
    'metadata retry bound exceeded': 'metadata_retry_bound_exceeded',
}


def _trusted_rejection_type(transport):
    # Caller already requires the exact hash-authenticated CurrentOriginTransport.
    # Missing or replaced test seams cannot make arbitrary error classes trusted.
    try:
        candidate = transport._json.__func__.__globals__['f'].Rejected
        return candidate if type(candidate) is type and issubclass(candidate, BaseException) else None
    except BaseException:
        return None


def _safe_rejection_reason(error, rejection_type):
    # Never stringify or return arguments. Only the exact reviewed local class,
    # exact tuple shape and exact builtin string can match a fixed local label.
    if rejection_type is None or type(error) is not rejection_type:
        return 'unknown'
    arguments = BaseException.args.__get__(error, type(error))
    if (type(arguments) is not tuple or len(arguments) != 1 or type(arguments[0]) is not str or
            len(arguments[0]) > 160):
        return 'unknown'
    return _LOCAL_REJECTION_REASONS.get(arguments[0], 'unknown')


def _safe_failure_diagnostic(error, diagnostic, rejection_type=None):
    """Bounded labels; never stringify an exception or copy external data.

    Only the standard HTTPError integer status and allowlisted class names may
    cross the failure boundary. Exception-chain traversal is capped at eight,
    cycle-safe, and cannot modify retries, deadlines, or acceptance decisions.
    """
    try:
        phase = diagnostic.get('phase')
        phase = phase if phase in _DIAGNOSTIC_PHASES else 'unknown'
        round_ = diagnostic.get('round')
        round_ = round_ if round_ in ('initial', 'before', 'body', 'after', 'final') else 'unknown'
        name = type(error).__name__
        name = name if name in _DIAGNOSTIC_CLASSES else 'OtherError'
        timeout, http, reason, seen, current = False, 'none', 'unknown', set(), error
        for _ in range(8):
            if not isinstance(current, BaseException) or id(current) in seen:
                break
            seen.add(id(current))
            if reason == 'unknown':
                reason = _safe_rejection_reason(current, rejection_type)
            current_name = type(current).__name__
            if current_name in ('TimeoutError', '_MetadataWallTimeout', '_MetadataHardTimeout'):
                timeout = True
            if http == 'none' and isinstance(current, urllib.error.HTTPError):
                code = current.code
                if type(code) is int:
                    if code in (401, 403, 404, 408, 429):
                        http = 'http_' + str(code)
                    elif 300 <= code <= 399:
                        http = 'http_redirect'
                    elif 400 <= code <= 499:
                        http = 'http_other_4xx'
                    elif 500 <= code <= 599:
                        http = 'http_5xx'
                    else:
                        http = 'http_other'
                else:
                    http = 'http_invalid'
            current = current.__cause__ if current.__cause__ is not None else current.__context__
        return 'phase=' + round_ + '.' + phase + '; exception=' + name + '; http=' + http + '; timeout=' + ('true' if timeout else 'false') + '; reason=' + reason
    except BaseException:
        return 'phase=unknown.unknown; exception=OtherError; http=none; timeout=false; reason=unknown'


def need(value, message):
    if not value:
        raise AdmissionRejected(message)


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False).encode('utf-8')


def sha(data):
    return hashlib.sha256(data).hexdigest()


def _pairs(items):
    result = {}
    for key, value in items:
        need(key not in result, 'duplicate JSON key')
        result[key] = value
    return result


def parse(raw):
    try:
        return json.loads(raw, object_pairs_hook=_pairs,
                          parse_constant=lambda _: (_ for _ in ()).throw(AdmissionRejected('nonfinite JSON')))
    except (ValueError, TypeError, UnicodeError):
        raise AdmissionRejected('invalid admission JSON') from None


def utc(value):
    need(type(value) is str and re.fullmatch(r'\d{4}-\d\d-\d\dT\d\d:\d\d:\d\dZ', value),
         'invalid admission UTC timestamp')
    try:
        return datetime.strptime(value, '%Y-%m-%dT%H:%M:%SZ').replace(tzinfo=timezone.utc)
    except ValueError:
        raise AdmissionRejected('invalid admission UTC timestamp') from None


def _remaining(check):
    value = check()
    need(type(value) in (int, float) and math.isfinite(value) and value > 0,
         'admission shared deadline exhausted')
    return value


def _tick(transport, pin, check):
    remaining = _remaining(check)
    transport._check_age()
    now = transport.now()
    need(isinstance(now, datetime) and now.tzinfo is not None,
         'admission requires an aware trusted clock')
    need(utc(pin['run_updated_at']) <= now < min(utc(pin['original_deadline_utc']), utc(pin['expires_at'])),
         'admission original deadline or expiry exceeded')
    _remaining(check)
    return remaining


@contextlib.contextmanager
def _guard(transport, check, cap=60):
    # Reuse the actual inherited reviewed wall guard; no copied downloader or
    # parallel transport. The driver's outer SIGTERM watchdog is independent.
    seconds = min(cap, _remaining(check))
    globals_ = transport._json.__func__.__globals__
    guard = globals_.get('_metadata_wall_limit')
    need(callable(guard), 'reviewed metadata wall guard unavailable')
    deadline = time.monotonic() + seconds
    with guard(seconds, deadline=deadline):
        yield
    _remaining(check)


def _metadata_budget(started, remaining):
    """Build a representably positive deadline strictly inside the original cap.

    Addition/subtraction roundoff must never broaden the unchanged transport's
    strict 180-second validation. Unrepresentably tiny slack is rejected.
    """
    try:
        valid_start = type(started) in (int, float) and math.isfinite(started) and started >= 0
        valid_slack = type(remaining) in (int, float) and math.isfinite(remaining) and remaining > 0
    except (OverflowError, TypeError):
        valid_start = valid_slack = False
    need(valid_start and valid_slack, 'invalid admission metadata clock or slack')
    limit = min(180, remaining)
    ceiling = started + limit
    deadline = math.nextafter(ceiling, -math.inf)
    need(math.isfinite(deadline) and started < deadline <= ceiling and
         0 < deadline - started <= limit, 'admission metadata slack is not representably positive')
    return {'started': started, 'deadline': deadline}


def _json(transport, path, check):
    started = time.monotonic()
    budget = _metadata_budget(started, _remaining(check))
    value = transport._json(path, budget=budget)
    _remaining(check)
    need(type(value) is dict, 'authenticated admission metadata object required')
    return value


def _collection(transport, path, key, check):
    # Same reviewed bounded _json pagination, with the caller's shared deadline
    # propagated on every page rather than the inherited budget-less wrapper.
    result = []
    for page in range(1, 7):
        obj = _json(transport, path + '?per_page=100&page=' + str(page), check)
        rows = obj.get(key)
        need(type(rows) is list and len(rows) <= 100 and all(type(x) is dict for x in rows),
             'invalid bounded admission collection')
        result.extend(rows)
        if len(rows) < 100:
            need(type(obj.get('total_count')) is int and obj['total_count'] == len(result),
                 'incomplete admission collection')
            return result
    raise AdmissionRejected('admission collection bound exceeded')


def _validate_pin(pin):
    need(type(pin) is dict, 'admission pin object required')
    fixed = {k: v for k, v in pin.items() if k not in ('active', 'reconciliation_sha256')}
    need(sha(canonical(fixed)) == FIXED_PIN_SHA256, 'fixed admission pin changed')
    need(pin.get('active') is True and type(pin.get('reconciliation_sha256')) is str and
         pin['reconciliation_sha256'] == RECONCILIATION_SHA256,
         'independent admission reconciliation is inactive or missing')
    return copy.deepcopy(pin)


def _snapshot(transport, pin, check, diagnostic=None):
    _phase(diagnostic, 'snapshot_deadline')
    _tick(transport, pin, check)
    rid, jid, wid, aid = (pin[k] for k in ('run_id', 'producer_job_id', 'workflow_id', 'artifact_id'))
    _phase(diagnostic, 'run_metadata')
    run = _json(transport, f'{PREFIX}/actions/runs/{rid}', check)
    for name in ('repository', 'head_repository'):
        repo = run.get(name)
        need(type(repo) is dict and type(repo.get('id')) is int and repo['id'] == pin['repository_id'] and
             repo.get('full_name') == REPO, 'admission repository binding mismatch')
    expected = {'id': rid, 'run_attempt': 1, 'head_sha': pin['pipeline_commit'],
                'head_branch': pin['head_branch'], 'workflow_id': wid, 'path': pin['workflow_path'],
                'name': pin['workflow_name'], 'event': 'push', 'status': 'completed',
                'conclusion': 'success', 'created_at': pin['run_created_at'],
                'updated_at': pin['run_updated_at'], 'run_started_at': pin['run_created_at']}
    need(all(type(run.get(k)) is type(v) and run.get(k) == v for k, v in expected.items()),
         'admission run failed or identity changed')
    _phase(diagnostic, 'job_metadata')
    jobs = _collection(transport, f'{PREFIX}/actions/runs/{rid}/attempts/1/jobs', 'jobs', check)
    need(len(jobs) == 1, 'admission producer job missing or duplicated')
    job = jobs[0]
    expected_job = {'id': jid, 'name': pin['producer_job_name'], 'run_id': rid, 'run_attempt': 1,
                    'head_sha': pin['pipeline_commit'], 'head_branch': pin['head_branch'],
                    'workflow_name': pin['workflow_name'], 'status': 'completed', 'conclusion': 'success',
                    'started_at': pin['job_started_at'], 'completed_at': pin['job_completed_at'],
                    'url': f'https://api.github.com{PREFIX}/actions/jobs/{jid}',
                    'run_url': f'https://api.github.com{PREFIX}/actions/runs/{rid}'}
    need(all(type(job.get(k)) is type(v) and job.get(k) == v for k, v in expected_job.items()),
         'admission producer identity or status changed')
    steps = job.get('steps')
    need(type(steps) is list and len(steps) <= 100 and all(type(s) is dict for s in steps),
         'invalid admission producer steps')
    numbers = [s.get('number') for s in steps]
    need(all(type(n) is int and n > 0 for n in numbers) and len(numbers) == len(set(numbers)),
         'ambiguous admission producer steps')
    for expected_step in pin['steps']:
        selected = [s for s in steps if s.get('number') == expected_step['number'] or
                    s.get('name') == expected_step['name']]
        need(len(selected) == 1 and all(selected[0].get(k) == v for k, v in expected_step.items()) and
             selected[0].get('status') == 'completed' and selected[0].get('conclusion') == 'success',
             'admission controller collector upload or marker step failed')
    _phase(diagnostic, 'workflow_metadata')
    workflow = _json(transport, f'{PREFIX}/actions/workflows/{wid}', check)
    need(type(workflow.get('id')) is int and workflow['id'] == wid and
         workflow.get('name') == pin['workflow_name'] and workflow.get('path') == pin['workflow_path'],
         'admission workflow metadata mismatch')
    _phase(diagnostic, 'commit_metadata')
    commit = _json(transport, f'{PREFIX}/git/commits/{pin["pipeline_commit"]}', check)
    need(commit.get('sha') == pin['pipeline_commit'] and type(commit.get('tree')) is dict and
         commit['tree'].get('sha') == pin['source_tree'], 'admission source tree mismatch')
    _phase(diagnostic, 'workflow_source')
    source = _json(transport, f'{PREFIX}/contents/{pin["workflow_path"]}?ref={pin["pipeline_commit"]}', check)
    need(source.get('type') == 'file' and source.get('path') == pin['workflow_path'] and
         source.get('encoding') == 'base64' and type(source.get('size')) is int and
         source['size'] == pin['workflow_source_bytes'] and source.get('sha') == pin['workflow_blob_sha1'] and
         type(source.get('content')) is str and len(source['content']) < 1024**2,
         'admission workflow source metadata mismatch')
    _remaining(check)
    try:
        raw = base64.b64decode(''.join(source['content'].splitlines()), validate=True)
    except (ValueError, TypeError):
        raise AdmissionRejected('invalid admission workflow encoding') from None
    need(len(raw) == pin['workflow_source_bytes'] and sha(raw) == pin['workflow_source_sha256'],
         'admission workflow source hash mismatch')
    _phase(diagnostic, 'artifact_listing')
    artifacts = _collection(transport, f'{PREFIX}/actions/runs/{rid}/artifacts', 'artifacts', check)
    need(len(artifacts) == 1, 'admission artifact missing or duplicated')
    _phase(diagnostic, 'artifact_metadata')
    artifact = _json(transport, f'{PREFIX}/actions/artifacts/{aid}', check)
    expected_artifact = {'id': aid, 'name': pin['artifact_name'], 'size_in_bytes': pin['artifact_zip_bytes'],
                         'digest': 'sha256:' + pin['artifact_zip_sha256'], 'expired': False,
                         'expires_at': pin['expires_at'], 'created_at': pin['artifact_created_at'],
                         'updated_at': pin['artifact_updated_at']}
    for item in (artifacts[0], artifact):
        need(all(type(item.get(k)) is type(v) and item.get(k) == v for k, v in expected_artifact.items()),
             'admission artifact identity digest or expiry changed')
        expected_wr = {'id': rid, 'head_sha': pin['pipeline_commit'], 'head_branch': pin['head_branch'],
                       'repository_id': pin['repository_id'], 'head_repository_id': pin['repository_id']}
        wr = item.get('workflow_run')
        need(type(wr) is dict and all(type(wr.get(k)) is type(v) and wr.get(k) == v
                                     for k, v in expected_wr.items()), 'admission artifact repository binding changed')
    marker = _read_marker(transport, pin, check, diagnostic)
    _phase(diagnostic, 'snapshot_deadline')
    _tick(transport, pin, check)
    bound_run = dict(expected)
    for key in ('repository', 'head_repository'):
        bound_run[key] = {'id': pin['repository_id'], 'full_name': REPO}
    bound_job = dict(expected_job)
    bound_job['steps'] = [dict(step, status='completed', conclusion='success') for step in pin['steps']]
    bound_artifact = dict(expected_artifact, workflow_run=expected_wr)
    return {'run': bound_run, 'job': bound_job, 'artifact': bound_artifact,
            'source_tree': pin['source_tree'], 'workflow_source_sha256': pin['workflow_source_sha256'],
            'upload_marker': marker}


def _read_marker(transport, pin, check, diagnostic=None):
    # The connector's decoded log file hash is not a raw remote-byte identity.
    # Bind the unique emitted marker to the exact authenticated successful job.
    _phase(diagnostic, 'log_request')
    request = transport._request(f'{PREFIX}/actions/jobs/{pin["producer_job_id"]}/logs')
    raw = bytearray()
    _phase(diagnostic, 'log_guard')
    with _guard(transport, check):
        for redirects in range(6):
            _remaining(check)
            try:
                _phase(diagnostic, 'log_open')
                response = transport.opener.open(request, timeout=min(60, _remaining(check)))
            except urllib.error.HTTPError as error:
                _phase(diagnostic, 'log_redirect')
                code = error.code
                location = error.headers.get('Location', '') if error.headers else ''
                error.close()
                need(code in (301, 302, 303, 307, 308) and redirects < 5,
                     'authenticated admission log request failed')
                url = urllib.parse.urljoin(request.full_url, location)
                transport._safe_redirect(url)
                request = transport._request(url, authenticated=False)
                continue
            with response:
                need(response.getcode() == 200, 'authenticated admission log response failed')
                while True:
                    _remaining(check)
                    _phase(diagnostic, 'log_read')
                    chunk = response.read(min(CHUNK, MAX_LOG + 1 - len(raw)))
                    _remaining(check)
                    need(type(chunk) is bytes, 'invalid admission log response bytes')
                    raw.extend(chunk)
                    need(len(raw) <= MAX_LOG, 'admission job log exceeds bound')
                    if not chunk:
                        break
            break
        else:
            raise AdmissionRejected('admission log redirect bound exceeded')
    _phase(diagnostic, 'log_decode')
    try:
        encoding = 'utf-16' if raw[:2] in (b'\xff\xfe', b'\xfe\xff') else 'utf-8-sig'
        text = raw.decode(encoding, errors='strict')
    except UnicodeError:
        raise AdmissionRejected('unsupported admission log encoding') from None
    _phase(diagnostic, 'log_marker')
    emitted = []
    pattern = re.compile(r'^(\d{4}-\d\d-\d\dT\d\d:\d\d:\d\d(?:\.\d{1,9})?Z) ' + MARKER + r'(.+)$', flags=re.ASCII)
    for line in text.splitlines():
        _remaining(check)
        match = pattern.fullmatch(line)
        if match:
            emitted.append(match)
        elif line.startswith(MARKER):
            raise AdmissionRejected('admission marker lacks authenticated log timestamp')
    need(len(emitted) == 1, 'admission emitted upload marker missing or duplicated')
    expected = {'artifact_id': pin['artifact_id'], 'artifact_sha256': pin['artifact_zip_sha256'],
                'pipeline_commit': pin['pipeline_commit'], 'proof_pass_claimed': False,
                'run_attempt': '1', 'run_id': str(pin['run_id']), 'spec_sha256': pin['job_spec_sha256']}
    marker = parse(emitted[0].group(2))
    need(type(marker) is dict and canonical(marker) == canonical(expected), 'admission upload marker mismatch')
    # API steps have whole-second resolution while logs contain subsecond times.
    # The full timestamp grammar matched above. Parse only the whole-second
    # UTC prefix, avoiding version-dependent fractional fromisoformat support.
    marker_second = utc(emitted[0].group(1)[:19] + 'Z')
    step = pin['steps'][-1]
    need(utc(step['started_at']) <= marker_second <= utc(step['completed_at']),
         'admission marker outside successful marker step')
    return marker


def _safe_name(name):
    need(type(name) is str and bool(name) and len(name) <= 300 and
         re.fullmatch(r'[A-Za-z0-9_.\-/]+', name) and not name.startswith('/') and
         all(part not in ('', '.', '..') for part in name.split('/')) and
         str(PurePosixPath(name)) == name, 'unsafe admission member path')
    return name


def _no_links(path):
    path = Path(path).absolute()
    for item in [path, *path.parents]:
        need(not item.is_symlink(), 'admission destination or witness contains a link')
    need(path == path.resolve(strict=False), 'admission destination or witness is not canonical')
    return path


def _stamp(fd):
    s = os.fstat(fd)
    need(stat.S_ISREG(s.st_mode) and s.st_nlink == 1, 'admission file is not single-link regular data')
    return (s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns)


def _read_file(path, limit, check):
    path = _no_links(path)
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
    try:
        before = _stamp(fd)
        need(before[2] <= limit, 'admission local file exceeds bound')
        data = bytearray()
        while True:
            _remaining(check)
            chunk = os.read(fd, min(CHUNK, limit + 1 - len(data)))
            _remaining(check)
            data.extend(chunk)
            need(len(data) <= limit, 'admission local file exceeds bound')
            if not chunk:
                break
        need(_stamp(fd) == before and len(data) == before[2], 'admission local file mutated during read')
        current = path.lstat()
        need((current.st_dev, current.st_ino) == before[:2], 'admission local file path changed')
        return bytes(data)
    finally:
        os.close(fd)


def _preflight(parent, pin, witness_bytes):
    v = os.statvfs(parent)
    need(v.f_bavail * v.f_frsize >= pin['artifact_zip_bytes'] + MAX_EVIDENCE + witness_bytes + RESERVE_BYTES,
         'admission disk preflight failed')
    dirs = {str(p) for name in pin['files'] for p in PurePosixPath(name).parents if str(p) != '.'}
    need(v.f_favail >= len(pin['files']) + len(dirs) + 5 + RESERVE_INODES,
         'admission inode preflight failed')


def _make_file(rootfd, name):
    parts = _safe_name(name).split('/')
    fd = os.dup(rootfd)
    try:
        for part in parts[:-1]:
            try:
                os.mkdir(part, 0o700, dir_fd=fd)
            except FileExistsError:
                pass
            nextfd = os.open(part, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=fd)
            os.close(fd)
            fd = nextfd
        return os.open(parts[-1], os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600, dir_fd=fd)
    finally:
        os.close(fd)


def _write(fd, chunk):
    view = memoryview(chunk)
    while view:
        count = os.write(fd, view)
        need(count > 0, 'admission short write')
        view = view[count:]


def _download(transport, pin, rootfd, check, diagnostic=None):
    _phase(diagnostic, 'zip_open')
    fd = _make_file(rootfd, 'evidence.zip')
    h, count = hashlib.sha256(), 0
    try:
        _phase(diagnostic, 'zip_guard')
        with _guard(transport, check):
            _phase(diagnostic, 'zip_open')
            with transport._open_zip(pin['artifact_id']) as response:
                need(response.getcode() == 200, 'admission ZIP response failed')
                while True:
                    _remaining(check)
                    _phase(diagnostic, 'zip_read')
                    chunk = response.read(min(CHUNK, pin['artifact_zip_bytes'] + 1 - count))
                    _remaining(check)
                    need(type(chunk) is bytes, 'invalid admission ZIP response bytes')
                    count += len(chunk)
                    need(count <= pin['artifact_zip_bytes'], 'admission ZIP exceeds exact bound')
                    h.update(chunk)
                    _write(fd, chunk)
                    if not chunk:
                        break
            _phase(diagnostic, 'zip_hash')
            need(count == pin['artifact_zip_bytes'] and h.hexdigest() == pin['artifact_zip_sha256'],
                 'admission ZIP exact size or digest mismatch')
    finally:
        os.close(fd)


def _extract(archive, evidence, inventory, check):
    need(type(inventory) is dict and len(inventory) == 112, 'admission requires exactly 112 files')
    total = sum(row['bytes'] for row in inventory.values())
    need(total <= MAX_EVIDENCE, 'admission expanded evidence bound exceeded')
    archive = _no_links(archive)
    with archive.open('rb') as handle:
        before = _stamp(handle.fileno())
        with zipfile.ZipFile(handle) as bundle:
            members = bundle.infolist()
            need(len(members) == 112 and len({m.filename for m in members}) == 112 and
                 {m.filename for m in members} == set(inventory), 'admission ZIP member coverage changed')
            for member in members:
                _remaining(check)
                _safe_name(member.filename)
                mode = (member.external_attr >> 16) & 0xffff
                need(member.orig_filename == member.filename and not member.is_dir() and
                     not member.flag_bits & (1 | 64) and
                     stat.S_IFMT(mode) in (0, stat.S_IFREG) and member.compress_type in (0, 8) and
                     member.file_size == inventory[member.filename]['bytes'],
                     'unsafe or oversized admission ZIP member')
            evidence.mkdir(mode=0o700)
            rootfd = os.open(evidence, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
            try:
                for member in members:
                    _remaining(check)
                    fd = _make_file(rootfd, member.filename)
                    count, h = 0, hashlib.sha256()
                    try:
                        with bundle.open(member) as source:
                            while True:
                                _remaining(check)
                                chunk = source.read(min(CHUNK, member.file_size + 1 - count))
                                _remaining(check)
                                count += len(chunk)
                                need(count <= member.file_size, 'admission member exceeds exact bound')
                                h.update(chunk)
                                _write(fd, chunk)
                                if not chunk:
                                    break
                        need(count == member.file_size and h.hexdigest() == inventory[member.filename]['sha256'],
                             'admission member digest mismatch')
                    finally:
                        os.close(fd)
            finally:
                os.close(rootfd)
        need(_stamp(handle.fileno()) == before, 'admission ZIP mutated during extraction')
    _remaining(check)


def _semantic_sanity(evidence, pin, check):
    def obj(name):
        raw = _read_file(evidence / name, pin['files'][name]['bytes'], check)
        need(sha(raw) == pin['files'][name]['sha256'], 'admission evidence changed after extraction')
        return parse(raw)
    manifest = obj('EVIDENCE.json')
    need(manifest.get('schema') == 'historical-admission-evidence-bundle-v1' and
         manifest.get('status') == 'complete_candidate_evidence' and manifest.get('truncated') is False and
         manifest.get('proof_pass_claimed') is False and manifest.get('activation_allowed') is False and
         manifest.get('terminal_job_success_and_controller_exit_zero_required') is True and
         manifest.get('original_selected_bytes') == 54035590 and
         manifest.get('files') == {k: v for k, v in pin['files'].items() if k != 'EVIDENCE.json'},
         'admission evidence manifest is partial or inconsistent')
    result, complete, native = (obj(n) for n in ('RESULT.json', COMPLETION, NATIVE))
    need(result.get('status') == 'admission_only_complete' and result.get('proof_pass_claimed') is False and
         result.get('activation_allowed') is False and result.get('job_spec_sha256') == pin['job_spec_sha256'] and
         result.get('original_deadline_utc') == pin['original_deadline_utc'] and
         result.get('semantic_completion_sha256') == pin['files'][COMPLETION]['sha256'],
         'admission controller result mismatch')
    need(complete.get('status') == 'historical_payloads_native_validated_only' and
         complete.get('proof_pass_claimed') is False and complete.get('activation_allowed') is False and
         complete.get('kernel_executed') is False and complete.get('runtime_installed') is False and
         complete.get('future_current_execution_adapter_reviewed') is False and
         complete.get('spec_sha256') == pin['semantic_spec_sha256'] and
         complete.get('selection_sha256') == pin['files'][SELECTION]['sha256'] and
         complete.get('native_validation_sha256') == pin['files'][NATIVE]['sha256'] and
         complete.get('stage_count') == 48 and complete.get('module_count') == 3153 and
         complete.get('companion_count') == 18918 and complete.get('raw_archive_bytes') == 3009576960 and
         complete.get('raw_archive_cap') == 4294967296 and native.get('executor_calls') == 0 and
         native.get('runtime_installed') is False and native.get('runtime_opened') is False,
         'admission evidence scope or receipt binding mismatch')
    obj(SELECTION)


def _rehash_tree(evidence, inventory, check):
    seen = set()
    for parent, dirs, files in os.walk(evidence, followlinks=False):
        _remaining(check)
        for name in dirs:
            need(not (Path(parent) / name).is_symlink(), 'link in admission output')
        for name in files:
            path = Path(parent) / name
            relative = str(path.relative_to(evidence))
            need(relative in inventory, 'unexpected admission output file')
            row = inventory[relative]
            need(sha(_read_file(path, row['bytes'], check)) == row['sha256'], 'admission output mutated')
            seen.add(relative)
    need(seen == set(inventory), 'admission output missing members')


def load_verified_admission(transport, pin, destination, check_deadline):
    """Return token-free verified evidence paths/pins, never native objects.

    The caller must independently re-run its reviewed final component validators
    on raw completion, selection and reconciliation bytes before acquisition.
    Failure preserves this new owned destination for diagnosis; never deletes or
    overwrites an older snapshot. All external errors are sanitized.
    """
    diagnostic = {'phase': 'pin_validation', 'round': 'initial'}
    try:
        pin = _validate_pin(pin)
        _phase(diagnostic, 'deadline')
        _tick(transport, pin, check_deadline)
        _phase(diagnostic, 'destination')
        destination = _no_links(destination)
        need(not destination.exists() and destination.parent.is_dir(), 'admission destination must be new')
        _phase(diagnostic, 'reconciliation_read')
        witness_path = Path(__file__).absolute().parent / 'ADMISSION_RECONCILIATION.json'
        witness = _read_file(witness_path, MAX_RECONCILIATION, check_deadline)
        need(sha(witness) == pin['reconciliation_sha256'] and type(parse(witness)) is dict,
             'static admission reconciliation witness mismatch')
        _phase(diagnostic, 'review_read')
        review_path = Path(__file__).absolute().parent / 'ADMISSION_INDEPENDENT_REVIEW.json'
        review = _read_file(review_path, MAX_RECONCILIATION, check_deadline)
        need(sha(review) == pin['independent_review_sha256'] == INDEPENDENT_REVIEW_SHA256,
             'independent admission review witness mismatch')
        _phase(diagnostic, 'capacity')
        _preflight(destination.parent, pin, len(witness) + len(review))
        diagnostic['round'] = 'before'
        before = _snapshot(transport, pin, check_deadline, diagnostic)
        diagnostic['round'] = 'body'
        _phase(diagnostic, 'projection_binding')
        projection = parse(witness)
        need(projection.get('schema') == 'fixed-three-context-admission-reconciliation-v1' and
             projection.get('independent_review_sha256') == sha(review) and
             projection.get('authenticated_metadata') == {k: before[k] for k in ('run', 'job', 'artifact')} and
             projection.get('upload_marker') == {'artifact_id': pin['artifact_id'],
                 'artifact_zip_sha256': pin['artifact_zip_sha256'], 'occurrences': 1},
             'static admission projection does not match runtime authentication')
        _phase(diagnostic, 'create_destination')
        destination.mkdir(mode=0o700)
        rootfd = os.open(destination, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
        root_identity = os.fstat(rootfd)
        try:
            _phase(diagnostic, 'copy_witnesses')
            fd = _make_file(rootfd, 'ADMISSION_RECONCILIATION.json')
            try:
                _write(fd, witness)
            finally:
                os.close(fd)
            fd = _make_file(rootfd, 'ADMISSION_INDEPENDENT_REVIEW.json')
            try:
                _write(fd, review)
            finally:
                os.close(fd)
            _download(transport, pin, rootfd, check_deadline, diagnostic)
            _phase(diagnostic, 'evidence_guard')
            with _guard(transport, check_deadline):
                _phase(diagnostic, 'evidence_extract')
                _extract(destination / 'evidence.zip', destination / 'evidence', pin['files'], check_deadline)
                _phase(diagnostic, 'evidence_validate')
                _semantic_sanity(destination / 'evidence', pin, check_deadline)
            diagnostic['round'] = 'after'
            after = _snapshot(transport, pin, check_deadline, diagnostic)
            diagnostic['round'] = 'final'
            _phase(diagnostic, 'identity_comparison')
            need(before == after, 'admission authenticated identity mutated')
            _phase(diagnostic, 'rehash_evidence')
            _rehash_tree(destination / 'evidence', pin['files'], check_deadline)
            _phase(diagnostic, 'rehash_zip')
            need(sha(_read_file(destination / 'evidence.zip', pin['artifact_zip_bytes'], check_deadline)) ==
                 pin['artifact_zip_sha256'], 'admission ZIP changed after extraction')
            _phase(diagnostic, 'rehash_witnesses')
            need(_read_file(destination / 'ADMISSION_RECONCILIATION.json', len(witness), check_deadline) == witness,
                 'admission reconciliation changed after copy')
            need(_read_file(destination / 'ADMISSION_INDEPENDENT_REVIEW.json', len(review), check_deadline) == review,
                 'admission independent review changed after copy')
            _phase(diagnostic, 'final_identity')
            current = destination.lstat()
            need((current.st_dev, current.st_ino) == (root_identity.st_dev, root_identity.st_ino),
                 'admission destination identity changed')
            _phase(diagnostic, 'deadline')
            _tick(transport, pin, check_deadline)
        finally:
            os.close(rootfd)
        _phase(diagnostic, 'complete')
        evidence = destination / 'evidence'
        return {'schema': 'verified-admission-evidence-paths-v1', 'evidence_root': str(evidence),
                'completion_path': str(evidence / COMPLETION), 'selection_path': str(evidence / SELECTION),
                'reconciliation_path': str(destination / 'ADMISSION_RECONCILIATION.json'),
                'independent_review_path': str(destination / 'ADMISSION_INDEPENDENT_REVIEW.json'),
                'verified': {'runtime_authenticated_before_and_after': True,
                             'static_reconciliation_sha256': pin['reconciliation_sha256'],
                             'independent_review_sha256': pin['independent_review_sha256'],
                             'pin_sha256': sha(canonical(pin)), 'artifact_id': pin['artifact_id'],
                             'artifact_zip_sha256': pin['artifact_zip_sha256'], 'file_count': 112,
                             'expanded_bytes': sum(x['bytes'] for x in pin['files'].values()),
                             'metadata': after, 'proof_pass_claimed': False,
                             'native_objects_created': False, 'final_component_rechecks_required': True}}
    except AdmissionRejected:
        raise
    except BaseException as error:
        # Never expose bearer material, signed URLs, remote error bodies, or
        # original exceptions through chained traceback output.
        raise AdmissionRejected('admission loading failed (' +
                                _safe_failure_diagnostic(error, diagnostic, _trusted_rejection_type(transport)) +
                                '); external details suppressed') from None
