"""Inactive, read-only adapter for one frozen old origin and one trusted successor.

No CLI or workflow is installed. The caller must freeze/review the workflow role
map together with its exact source hash in the selection/contract. The role map
is a reviewed trust input, NOT a claim that GitHub artifact metadata names a job.
The four authoritative native-descriptor enrichments match ci_transport exactly.
"""
from __future__ import annotations

import base64
import copy
import contextlib
import errno
import math
import signal
import socket
import ssl
import threading
import hashlib
import http.client
import re
import stat
import time
import urllib.error
import urllib.parse
import urllib.request
import zipfile
from datetime import datetime, timedelta, timezone
from pathlib import Path

import fresh_stage as f
import continuation_policy as cp
from ci_transport import API, REPOSITORY, NoRedirect, Transport

REPOSITORY_ID = 1407290933
OLD_RUN_ID = 38860226136
OLD_ATTEMPT = 1
OLD_PIPELINE = 'f8c7028dd80232ac522b7cf223052921fca396fa'
OLD_BRANCH = 'verify/hierarchy-c-modern-20261016'
OLD_FACTS = {
    'pipeline_commit': OLD_PIPELINE,
    'source_commit': '4a0cbd71ba9cd318620e11694037d956d2393d06',
    'source_manifest_sha256': '401320e96ea5a511678892c359af43131fae75494a55d8ea1df0e1dc606a326f',
    'contract_sha256': 'a0ad861b7f8b9eb857d8a44ce811dcae7149ffc1f81bd9cdd7a788536ce15555',
    'plan_sha256': 'c25336bffaf3ada115c7642840675f445cc3cef145fa1d70e9eec8988567a7ed',
    'profiles_sha256': '0af17b85b2b469be445bdcb68acbc07bb38507382fc818ffc4bd2bac5e3ce1ee',
    'runner_sha256': 'a8cbd69f9904b6f2645177de722f3466cb762045a7cd8c3e6230f1ceaa9c9c1d',
    'lean_archive_sha256': 'b67d0e0ba959fc74e186f1b44aebca32d6ecb6a28f8e9a029fc4e9f73398a049',
    'toolchain_inventory_sha256': '42bd268b1ca3e9bf89f4149ac427d6c0e76f735233b092a6df4ca27a2c2db7ea',
    'run_id': str(OLD_RUN_ID), 'run_attempt': '1',
}
OLD_ORIGIN = 'OldOrigin'
CURRENT_ORIGIN = 'CurrentOrigin'
MAX_ARTIFACT_BYTES = 1024**3
MAX_FINAL_BYTES = 3 * 1024**3
FINAL_ROLES = {'export_target', 'fresh_kernel', 'lean_export', 'nanoda', 'conron'}
MAX_METADATA_BYTES = 8 * 1024**2
MAX_DESCRIPTOR_BYTES = 1024**2
MAX_WORKFLOW_BYTES = 1024**2
MAX_REDIRECTS = 5
MAX_RUN_AGE_SECONDS = 518400
MAX_METADATA_ATTEMPTS = 4
METADATA_BACKOFF_SECONDS = (1, 2, 4)
MAX_METADATA_ATTEMPT_SECONDS = 60
MAX_METADATA_TOTAL_SECONDS = 180
RETRYABLE_METADATA_STATUSES = frozenset({408, 500, 502, 503, 504})


class _MetadataWallTimeout(TimeoutError):
    """Soft transport interruption with cleanup time reserved inside the cap."""


class _MetadataHardTimeout(BaseException):
    """Terminal budget exhaustion; cleanup Exception handlers cannot swallow it."""


@contextlib.contextmanager
def _metadata_wall_limit(seconds, *, deadline=None):
    """Linux CI main-thread wall guard, including blocked or slow response reads.

    Never overwrite a caller's active alarm. Restore the inactive timer and the
    exact previous handler on every exit. No background thread/request survives.
    """
    f.need(type(seconds) in (int, float) and math.isfinite(seconds) and seconds > 0,
           'invalid metadata wall limit')
    f.need(threading.current_thread() is threading.main_thread(),
           'metadata wall guard requires the main thread')
    previous_timer = signal.getitimer(signal.ITIMER_REAL)
    f.need(previous_timer == (0.0, 0.0), 'metadata wall guard refuses an existing timer')
    previous_handler = signal.getsignal(signal.SIGALRM)
    monotonic_now = time.monotonic()
    hard_deadline = monotonic_now + seconds
    if deadline is not None:
        f.need(type(deadline) in (int, float) and math.isfinite(deadline),
               'invalid absolute metadata deadline')
        hard_deadline = min(hard_deadline, deadline)
    seconds = hard_deadline - monotonic_now
    f.need(seconds > 0, 'metadata absolute deadline exceeded')
    cleanup_reserve = min(1.0, seconds / 4)
    interrupted = False
    def expired(signum, frame):
        nonlocal interrupted
        remaining = hard_deadline - time.monotonic()
        if interrupted or remaining <= 0:
            raise _MetadataHardTimeout('metadata request hard deadline exceeded')
        interrupted = True
        signal.setitimer(signal.ITIMER_REAL, remaining)
        raise _MetadataWallTimeout('metadata transport deadline exceeded')
    signal.signal(signal.SIGALRM, expired)
    try:
        signal.setitimer(signal.ITIMER_REAL, seconds - cleanup_reserve)
        yield
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        signal.signal(signal.SIGALRM, previous_handler)


def _retryable_metadata_error(error):
    """Only explicit transient transport failures, never TLS/auth/parse errors."""
    if isinstance(error, ssl.SSLError):
        return False
    reason = error.reason if isinstance(error, urllib.error.URLError) else error
    if isinstance(reason, ssl.SSLError):
        return False
    if type(reason) in (_MetadataWallTimeout, TimeoutError, ConnectionResetError,
                        ConnectionAbortedError, ConnectionRefusedError, BrokenPipeError):
        return True
    if isinstance(reason, socket.gaierror):
        return reason.errno == socket.EAI_AGAIN
    return type(reason) is OSError and reason.errno in {
        errno.ETIMEDOUT, errno.ECONNRESET, errno.ECONNABORTED,
        errno.ECONNREFUSED, errno.EPIPE,
    }


def _metadata_backoff(attempt, retry_after):
    """Server waits can only fit within the fixed, already bounded schedule.

    Unsupported/date-valued or longer Retry-After is a terminal rejection, not
    permission to ignore the server wait or expand this request's budget.
    """
    delay = METADATA_BACKOFF_SECONDS[attempt - 1]
    if retry_after is not None:
        f.need(type(retry_after) is str and re.fullmatch(r'[0-9]{1,3}', retry_after),
               'unsupported metadata Retry-After')
        f.need(int(retry_after) <= delay, 'metadata Retry-After exceeds fixed backoff')
    return delay
STAGE_PIN_KEYS = {'artifact_id', 'producer_job_id', 'artifact_name',
                  'artifact_zip_sha256', 'artifact_zip_bytes', 'archive_sha256',
                  'archive_bytes', 'receipt_sha256', 'raw_descriptor_sha256',
                  'expires_at', 'identity_sha256'}
PREPARE_PIN_KEYS = {'artifact_id', 'producer_job_id', 'artifact_name',
                    'artifact_zip_sha256', 'artifact_zip_bytes', 'identity_sha256',
                    'inventory_sha256', 'expires_at'}


def positive(value, label):
    f.need(type(value) is int and value > 0, 'invalid positive integer: ' + label)
    return value


def digest(value, label):
    f.need(isinstance(value, str) and f.SHA256.fullmatch(value), 'invalid digest: ' + label)
    return value


def timestamp(value):
    f.need(isinstance(value, str) and re.fullmatch(r'\d{4}-\d\d-\d\dT\d\d:\d\d:\d\dZ', value),
           'timestamp must be an exact UTC API timestamp')
    try:
        return datetime.strptime(value, '%Y-%m-%dT%H:%M:%SZ').replace(tzinfo=timezone.utc)
    except ValueError as error:
        raise f.Rejected('invalid timestamp') from error


def exact_keys(value, keys, label):
    f.need(type(value) is dict and set(value) == set(keys), 'unknown/missing ' + label + ' fields')


def validate_workflow(mapping):
    """Validate a source-hash-pinned, independently reviewed role manifest.

    Exactly one upload location per role is an explicit review assertion bound
    in the frozen selection. This does not parse YAML or infer producer identity
    from self-reported artifact contents. Source/role review remains a release
    blocker until the actual original workflow has been independently checked.
    """
    exact_keys(mapping, {'workflow_id', 'path', 'name', 'head_branch', 'source_sha256', 'roles'}, 'workflow')
    positive(mapping['workflow_id'], 'workflow_id')
    digest(mapping['source_sha256'], 'workflow source')
    path = f.safe_rel(mapping['path'])
    f.need(re.fullmatch(r'\.github/workflows/[A-Za-z0-9_.-]+\.ya?ml', path), 'unreviewed workflow path')
    f.need(all(isinstance(mapping[k], str) and mapping[k] for k in ('name', 'head_branch')), 'invalid workflow label')
    f.need(type(mapping['roles']) is dict and 'prepare' in mapping['roles'], 'missing workflow roles')
    names = set()
    for role, binding in mapping['roles'].items():
        f.need(role == 'prepare' or role in FINAL_ROLES or re.fullmatch(r'build_\d{3}', role), 'unreviewed stage role')
        exact_keys(binding, {'producer_job', 'job_name', 'verifier_step', 'upload_step', 'upload_locations'}, 'role')
        f.need(type(binding['upload_locations']) is int and binding['upload_locations'] == 1,
               'role must have exactly one reviewed upload location')
        f.need(isinstance(binding['producer_job'], str) and re.fullmatch(r'[a-z][a-z0-9_]*', binding['producer_job']),
               'invalid workflow producer')
        f.need(binding['job_name'] == (role if role == 'prepare' or role in FINAL_ROLES else 'stage ' + role), 'job role/name mismatch')
        f.need(binding['job_name'] not in names, 'duplicate reviewed job role')
        names.add(binding['job_name'])
        for key in ('verifier_step', 'upload_step'):
            exact_keys(binding[key], {'number', 'name'}, 'step')
            positive(binding[key]['number'], key)
            f.need(isinstance(binding[key]['name'], str) and binding[key]['name'], 'missing reviewed step name')
        f.need(binding['verifier_step']['number'] < binding['upload_step']['number'], 'upload must follow verifier')
        f.need(binding['verifier_step']['name'] != binding['upload_step']['name'], 'ambiguous step roles')
    return mapping


class OriginTransport:
    """Resolve native stage descriptors without changing either origin's bytes.

    current_transport must be the existing authenticated Transport instance.
    old_context is the frozen old_origin selection object. current_context is
    {'identity': prepared successor identity, 'workflow': reviewed role manifest}.
    Both prepares must be independently authenticated before stage restoration.
    A custom NoRedirect-compatible opener/clock is provided only for offline tests.
    """
    def __init__(self, current_transport, old_context, current_context, *, opener=None, now=None):
        f.need(isinstance(current_transport, Transport), 'authenticated current Transport required')
        f.need(isinstance(current_transport.token, str) and current_transport.token, 'read-only workflow token missing')
        self.current = current_transport
        self.opener = opener if opener is not None else urllib.request.build_opener(NoRedirect())
        self.now = now or (lambda: datetime.now(timezone.utc))
        self.contexts = {OLD_ORIGIN: copy.deepcopy(old_context), CURRENT_ORIGIN: copy.deepcopy(current_context)}
        exact_keys(old_context, {'repository', 'repository_id', 'run_id', 'run_attempt', 'pipeline_commit',
                                 'identity', 'identity_sha256', 'prepare', 'workflow'}, 'old origin')
        exact_keys(current_context, {'identity', 'workflow'}, 'current context')
        f.need(old_context['repository'] == REPOSITORY and
               positive(old_context['repository_id'], 'repository_id') == REPOSITORY_ID and
               positive(old_context['run_id'], 'run_id') == OLD_RUN_ID and
               positive(old_context['run_attempt'], 'run_attempt') == OLD_ATTEMPT and
               old_context['pipeline_commit'] == OLD_PIPELINE, 'old origin is not fixed T0/R0/A0')
        identity = old_context['identity']
        f.need(type(identity) is dict and set(identity) == set(OLD_FACTS) | {'run_started_at'} and
               all(identity[k] == v for k, v in OLD_FACTS.items()), 'old prepare identity facts changed')
        f.need(digest(old_context['identity_sha256'], 'old identity') == f.sha(f.json_bytes(identity)),
               'old canonical identity hash mismatch')
        for origin in self.contexts:
            context = self.contexts[origin]
            validate_workflow(context['workflow'])
            timestamp(context['identity']['run_started_at'])
        f.need(old_context['workflow']['head_branch'] == OLD_BRANCH, 'old push branch changed')
        cur = current_context['identity']
        f.need(type(cur) is dict and cur.get('evidence_mode') == 'verified_continuation', 'current continuation identity required')
        f.need(cur.get('run_id') == current_transport.run_id and
               cur.get('run_attempt') == current_transport.attempt and
               cur.get('pipeline_commit') == current_transport.commit and
               re.fullmatch(r'[1-9][0-9]*', cur['run_id']) and
               re.fullmatch(r'[1-9][0-9]*', cur['run_attempt']) and
               f.COMMIT.fullmatch(cur['pipeline_commit']), 'current trusted event/identity mismatch')
        f.need(cur['run_id'] != str(OLD_RUN_ID) and cur['pipeline_commit'] != OLD_PIPELINE, 'successor must be distinct')
        cp.validate_identity_pair(identity,cur)
        self._validate_pin(old_context['prepare'], prepare=True, identity=identity)
        self._prepared = {}
        self._source_verified = set()
        self._check_age()

    def _check_age(self):
        now = self.now()
        f.need(isinstance(now, datetime) and now.tzinfo is not None, 'trusted aware clock required')
        for context in self.contexts.values():
            age = (now - timestamp(context['identity']['run_started_at'])).total_seconds()
            f.need(0 <= age <= MAX_RUN_AGE_SECONDS, 'origin deadline exceeded; no age renewal')

    def _validate_pin(self, pin, *, prepare, identity):
        exact_keys(pin, PREPARE_PIN_KEYS if prepare else STAGE_PIN_KEYS, 'prepare pin' if prepare else 'stage pin')
        for key in ('artifact_id', 'producer_job_id', 'artifact_zip_bytes'):
            positive(pin[key], key)
        for key in ('artifact_zip_sha256', 'identity_sha256'):
            digest(pin[key], key)
        f.need(isinstance(pin['artifact_name'], str) and pin['artifact_name'], 'artifact name required')
        timestamp(pin['expires_at'])
        f.need(pin['artifact_zip_bytes'] <= (32 * 1024**2 if prepare else MAX_ARTIFACT_BYTES + 1024**2), 'pinned ZIP bound')
        if prepare:
            digest(pin['inventory_sha256'], 'inventory_sha256')
            f.need(pin['inventory_sha256'] == identity['toolchain_inventory_sha256'], 'prepare inventory pin mismatch')
        else:
            for key in ('archive_sha256', 'receipt_sha256', 'raw_descriptor_sha256'):
                digest(pin[key], key)
            f.need(positive(pin['archive_bytes'], 'archive_bytes') <= MAX_ARTIFACT_BYTES, 'pinned archive bound')
            f.need(pin['identity_sha256'] == f.sha(f.json_bytes(identity)), 'stage old identity pin mismatch')

    def _context(self, origin):
        f.need(origin in self.contexts, 'origin must be exactly OldOrigin or CurrentOrigin')
        return self.contexts[origin]

    def _request(self, path, *, authenticated=True):
        if authenticated:
            f.need(path.startswith('/repos/' + REPOSITORY + '/'), 'unapproved API repository')
            url = API + path
            headers = {'Authorization': 'Bearer ' + self.current.token,
                       'Accept': 'application/vnd.github+json', 'X-GitHub-Api-Version': '2022-11-28'}
        else:
            url = path
            self._safe_redirect(url)
            headers = {}
        headers['User-Agent'] = 'hierarchy-c-verified-continuation'
        return urllib.request.Request(url, headers=headers, method='GET')

    def _metadata_remaining(self, budget):
        self._check_age()
        monotonic_now = time.monotonic()
        elapsed = monotonic_now - budget['started']
        f.need(math.isfinite(elapsed) and elapsed >= 0, 'invalid metadata monotonic clock')
        now = self.now()
        f.need(isinstance(now, datetime) and now.tzinfo is not None, 'trusted aware clock required')
        origin_remaining = min(
            (timestamp(context['identity']['run_started_at']) +
             timedelta(seconds=MAX_RUN_AGE_SECONDS) - now).total_seconds()
            for context in self.contexts.values())
        # Fix the origin slack to monotonic time on first use and only tighten.
        # A later backward wall-clock jump cannot renew either origin's budget.
        budget['deadline'] = min(budget['deadline'], monotonic_now + origin_remaining)
        remaining = budget['deadline'] - monotonic_now
        f.need(remaining > 0, 'metadata aggregate/origin deadline exceeded')
        return remaining

    def _json(self, path):
        # Only this authenticated metadata GET is retried. Each attempt starts
        # from a new response; no bytes or failed parse result are reused.
        self._check_age()
        started = time.monotonic()
        budget = {'started': started, 'deadline': started + MAX_METADATA_TOTAL_SECONDS}
        for attempt in range(1, MAX_METADATA_ATTEMPTS + 1):
            seconds = min(MAX_METADATA_ATTEMPT_SECONDS, self._metadata_remaining(budget))
            retry_after = None
            phase = 'transport'
            try:
                with _metadata_wall_limit(seconds, deadline=budget['deadline']):
                    try:
                        response = self.opener.open(self._request(path), timeout=seconds)
                        try:
                            f.need(response.getcode() == 200, 'GitHub metadata status is not 200')
                            data = response.read(MAX_METADATA_BYTES + 1)
                        except _MetadataHardTimeout:
                            phase = 'hard_timeout'
                            raise
                        finally:
                            # Never start further cleanup after terminal hard expiry.
                            # Failed soft-timeout reads retry only after successful close.
                            if phase != 'hard_timeout':
                                phase = 'cleanup'
                                try:
                                    response.close()
                                except Exception:
                                    raise f.Rejected('metadata response cleanup failed') from None
                                phase = 'transport'
                    except urllib.error.HTTPError as error:
                        phase = 'cleanup'
                        code = error.code
                        retry_after = error.headers.get('Retry-After') if error.headers is not None else None
                        try:
                            error.close()
                        except Exception:
                            raise f.Rejected('metadata error-response cleanup failed') from None
                        phase = 'http_status'
                        if type(code) is not int or code not in RETRYABLE_METADATA_STATUSES or attempt == MAX_METADATA_ATTEMPTS:
                            label = str(code) if type(code) is int else 'invalid'
                            raise f.Rejected('authenticated GitHub metadata failed with status ' + label) from None
                    else:
                        phase = 'parse'
                        f.need(len(data) <= MAX_METADATA_BYTES, 'oversized GitHub metadata')
                        try:
                            result = f.parse_json(data)
                        except (TypeError, ValueError):
                            raise f.Rejected('invalid GitHub metadata JSON') from None
                        f.need(type(result) is dict, 'GitHub metadata object required')
                        self._metadata_remaining(budget)
                        return result
            except _MetadataHardTimeout:
                raise f.Rejected('metadata request hard deadline exceeded') from None
            except (urllib.error.URLError, OSError) as error:
                if phase != 'transport' or not _retryable_metadata_error(error) or attempt == MAX_METADATA_ATTEMPTS:
                    raise f.Rejected('authenticated GitHub metadata read or cleanup failed') from None
            except f.Rejected:
                raise
            except (ValueError, http.client.HTTPException):
                raise f.Rejected('authenticated GitHub metadata read failed') from None
            delay = _metadata_backoff(attempt, retry_after)
            remaining = self._metadata_remaining(budget)
            f.need(delay < remaining, 'metadata backoff would exceed aggregate/origin deadline')
            try:
                with _metadata_wall_limit(remaining, deadline=budget['deadline']):
                    time.sleep(delay)
            except (_MetadataWallTimeout, _MetadataHardTimeout):
                raise f.Rejected('metadata backoff deadline exceeded') from None
            self._metadata_remaining(budget)
        raise f.Rejected('metadata retry bound exceeded')

    def _collection(self, path, key):
        result = []
        for page in range(1, 7):
            obj = self._json(path + '?per_page=100&page=' + str(page))
            rows = obj.get(key)
            f.need(type(rows) is list and len(rows) <= 100 and all(type(x) is dict for x in rows), 'invalid bounded API list')
            result.extend(rows)
            if len(rows) < 100:
                return result
        raise f.Rejected('GitHub metadata pagination bound exceeded')

    def _run(self, origin):
        context = self._context(origin)
        identity, workflow = context['identity'], context['workflow']
        run = self._json(f'/repos/{REPOSITORY}/actions/runs/{identity["run_id"]}')
        for key in ('repository', 'head_repository'):
            repo = run.get(key)
            f.need(type(repo) is dict and type(repo.get('id')) is int and repo['id'] == REPOSITORY_ID and
                   repo.get('full_name') == REPOSITORY, 'run repository/head-repository mismatch')
        f.need(type(run.get('id')) is int and str(run['id']) == identity['run_id'] and
               type(run.get('run_attempt')) is int and str(run['run_attempt']) == identity['run_attempt'] and
               run.get('head_sha') == identity['pipeline_commit'] and run.get('event') == 'push' and
               run.get('head_branch') == workflow['head_branch'] and
               type(run.get('workflow_id')) is int and run['workflow_id'] == workflow['workflow_id'] and
               run.get('path') == workflow['path'] and run.get('name') == workflow['name'], 'run/workflow identity mismatch or rerun')
        f.need(run.get('created_at') == identity['run_started_at'], 'trusted run start mismatch')
        created, updated = timestamp(run['created_at']), timestamp(run.get('updated_at'))
        f.need(created <= updated <= self.now(), 'inconsistent run timestamps')
        if origin == OLD_ORIGIN:
            f.need(run.get('status') == 'completed' and run.get('conclusion') == 'failure', 'old run is not terminal failure')
        else:
            f.need((run.get('status') == 'in_progress' and run.get('conclusion') is None) or
                   (run.get('status') == 'completed' and run.get('conclusion') == 'success'), 'current run is not active/successful')
        return run

    def _verify_workflow_source(self, origin):
        if origin in self._source_verified:
            return
        context = self._context(origin)
        wf = context['workflow']
        meta = self._json(f'/repos/{REPOSITORY}/actions/workflows/{wf["workflow_id"]}')
        f.need(type(meta.get('id')) is int and meta['id'] == wf['workflow_id'] and
               meta.get('path') == wf['path'] and meta.get('name') == wf['name'], 'workflow metadata mismatch')
        path = urllib.parse.quote(wf['path'], safe='/')
        obj = self._json(f'/repos/{REPOSITORY}/contents/{path}?ref={context["identity"]["pipeline_commit"]}')
        f.need(obj.get('type') == 'file' and obj.get('path') == wf['path'] and obj.get('encoding') == 'base64' and
               type(obj.get('size')) is int and 0 < obj['size'] <= MAX_WORKFLOW_BYTES and
               isinstance(obj.get('content'), str), 'invalid pinned workflow source metadata')
        try:
            raw = base64.b64decode(''.join(obj['content'].splitlines()), validate=True)
        except (ValueError, TypeError) as error:
            raise f.Rejected('invalid workflow source encoding') from error
        f.need(len(raw) == obj['size'] and f.sha(raw) == wf['source_sha256'], 'pinned workflow source hash mismatch')
        self._source_verified.add(origin)

    def _producer(self, origin, role, run, pin):
        context = self._context(origin)
        mapping = context['workflow']['roles']
        f.need(role in mapping, 'role absent from reviewed workflow')
        binding = mapping[role]
        ident = context['identity']
        jobs = self._collection(f'/repos/{REPOSITORY}/actions/runs/{ident["run_id"]}/attempts/{ident["run_attempt"]}/jobs', 'jobs')
        ids = [positive(job.get('id'), 'job id') for job in jobs]
        f.need(len(ids) == len(set(ids)), 'duplicate job IDs')
        matches = [job for job in jobs if job.get('name') == binding['job_name']]
        f.need(len(matches) == 1, 'producer missing or duplicated')
        job = matches[0]
        f.need(pin is None or job['id'] == pin['producer_job_id'], 'pinned producer job mismatch')
        f.need(type(job.get('run_id')) is int and str(job['run_id']) == ident['run_id'] and
               type(job.get('run_attempt')) is int and str(job['run_attempt']) == ident['run_attempt'] and
               job.get('head_sha') == ident['pipeline_commit'] and
               job.get('status') == 'completed' and job.get('conclusion') == 'success', 'producer context/status mismatch')
        started, completed = timestamp(job.get('started_at')), timestamp(job.get('completed_at'))
        f.need(timestamp(run['created_at']) <= started <= completed <= self.now(), 'inconsistent producer timestamps')
        if run['status'] == 'completed':
            f.need(completed <= timestamp(run['updated_at']), 'producer completed after terminal run')
        steps = job.get('steps')
        f.need(type(steps) is list and all(type(s) is dict for s in steps), 'producer steps missing')
        numbers = [positive(s.get('number'), 'step number') for s in steps]
        f.need(len(numbers) == len(set(numbers)), 'duplicate producer step numbers')
        for name in ('verifier_step', 'upload_step'):
            expected = binding[name]
            selected = [step for step in steps if step.get('number') == expected['number'] or step.get('name') == expected['name']]
            f.need(len(selected) == 1 and selected[0].get('number') == expected['number'] and
                   selected[0].get('name') == expected['name'] and selected[0].get('status') == 'completed' and
                   selected[0].get('conclusion') == 'success', 'reviewed verifier/upload step failed or ambiguous')
            begin, end = timestamp(selected[0].get('started_at')), timestamp(selected[0].get('completed_at'))
            f.need(started <= begin <= end <= completed, 'inconsistent step timestamps')
        return job, binding

    def _artifact(self, origin, role, run, job, pin, max_bytes):
        ident = self._context(origin)['identity']
        name = f'hierarchy-c-{ident["run_id"]}-{ident["run_attempt"]}-{role}'
        if pin is not None:
            f.need(pin['artifact_name'] == name, 'pinned artifact role name mismatch')
            aid = pin['artifact_id']
        else:
            artifacts = self._collection(f'/repos/{REPOSITORY}/actions/runs/{ident["run_id"]}/artifacts', 'artifacts')
            ids = [positive(a.get('id'), 'artifact id') for a in artifacts]
            f.need(len(ids) == len(set(ids)), 'duplicate artifact IDs')
            matches = [a for a in artifacts if a.get('name') == name]
            f.need(len(matches) == 1, 'current artifact missing or duplicated')
            aid = matches[0]['id']
        artifact = self._json(f'/repos/{REPOSITORY}/actions/artifacts/{aid}')
        f.need(type(artifact.get('id')) is int and artifact['id'] == aid and artifact.get('name') == name and
               artifact.get('expired') is False, 'artifact ID/name/expiry mismatch')
        size = positive(artifact.get('size_in_bytes'), 'artifact bytes')
        f.need(size <= max_bytes, 'artifact transfer bound')
        expected_digest = artifact.get('digest')
        f.need(isinstance(expected_digest, str) and re.fullmatch(r'sha256:[0-9a-f]{64}', expected_digest), 'authoritative ZIP digest missing')
        wr = artifact.get('workflow_run')
        f.need(type(wr) is dict and type(wr.get('id')) is int and str(wr['id']) == ident['run_id'] and
               wr.get('head_sha') == ident['pipeline_commit'] and wr.get('head_branch') == run['head_branch'] and
               type(wr.get('repository_id')) is int and wr['repository_id'] == REPOSITORY_ID and
               type(wr.get('head_repository_id')) is int and wr['head_repository_id'] == REPOSITORY_ID,
               'artifact run/head/repository mismatch')
        created, updated, expires = (timestamp(artifact.get(key)) for key in ('created_at', 'updated_at', 'expires_at'))
        f.need(timestamp(job['started_at']) <= created <= timestamp(job['completed_at']) and
               created <= updated <= self.now() < expires and updated < expires, 'inconsistent/expired artifact timestamps')
        if pin is not None:
            f.need(size == pin['artifact_zip_bytes'] and expected_digest[7:] == pin['artifact_zip_sha256'] and
                   artifact['expires_at'] == pin['expires_at'], 'artifact authoritative frozen pin mismatch')
        return artifact

    @staticmethod
    def _safe_redirect(url):
        f.need(isinstance(url, str) and url and not any(ord(c) < 33 for c in url), 'unsafe signed storage redirect')
        try:
            parsed = urllib.parse.urlsplit(url)
            good = (parsed.scheme == 'https' and parsed.hostname and not parsed.username and
                    not parsed.password and not parsed.fragment and parsed.port in (None, 443))
        except ValueError:
            good = False
        f.need(good, 'unsafe signed storage redirect')

    def _open_zip(self, aid):
        request = self._request(f'/repos/{REPOSITORY}/actions/artifacts/{aid}/zip')
        for redirects in range(MAX_REDIRECTS + 1):
            try:
                response = self.opener.open(request, timeout=60)
                f.need(response.getcode() == 200, 'artifact response must be 200')
                return response
            except urllib.error.HTTPError as error:
                f.need(error.code in (301, 302, 303, 307, 308), 'authenticated artifact download failed')
                f.need(redirects < MAX_REDIRECTS, 'artifact redirect bound exceeded')
                location = error.headers.get('Location', '')
                url = urllib.parse.urljoin(request.full_url, location)
                self._safe_redirect(url)
                # Every hop uses this NoRedirect opener and an entirely new,
                # credential-free request, including subsequent redirects.
                request = self._request(url, authenticated=False)
            except (OSError, ValueError):
                raise f.Rejected('artifact storage request failed; URL suppressed') from None
        raise f.Rejected('artifact redirect bound exceeded')

    def _extract(self, artifact, destination, members, max_bytes):
        destination = Path(destination)
        f.no_symlink_path(destination)
        f.need(not destination.exists(), 'artifact destination must be new')
        self._check_age()
        response = self._open_zip(artifact['id'])
        destination.mkdir(parents=True)
        archive = destination / 'download.zip'
        count, h, started = 0, hashlib.sha256(), time.monotonic()
        with response, archive.open('xb') as handle:
            while True:
                self._check_age()
                f.need(time.monotonic() - started <= 900, 'artifact transfer time bound')
                block = response.read(1024**2)
                if not block:
                    break
                count += len(block)
                f.need(count <= max_bytes and count <= artifact['size_in_bytes'], 'artifact ZIP transfer bound')
                h.update(block)
                handle.write(block)
        f.need(count == artifact['size_in_bytes'] and h.hexdigest() == artifact['digest'][7:], 'artifact ZIP digest/size mismatch')
        try:
            with zipfile.ZipFile(archive) as zipped:
                infos = zipped.infolist()
                f.need(len(infos) == len(members) and {i.filename for i in infos} == set(members), 'artifact ZIP member mismatch')
                total = 0
                for info in infos:
                    f.safe_rel(info.filename)
                    mode = info.external_attr >> 16
                    f.need(not info.is_dir() and stat.S_IFMT(mode) in (0, stat.S_IFREG) and not info.flag_bits & 1, 'unsafe ZIP member')
                    total += info.file_size
                    f.need(0 <= info.file_size and total <= max_bytes, 'ZIP expansion bound')
                    if info.filename == 'upload-candidate.json':
                        f.need(info.file_size <= MAX_DESCRIPTOR_BYTES, 'descriptor expansion bound')
                    out = destination / info.filename
                    f.no_symlink_path(out)
                    with zipped.open(info) as src, out.open('xb') as dst:
                        copied = 0
                        while True:
                            block = src.read(1024**2)
                            if not block:
                                break
                            copied += len(block)
                            f.need(copied <= info.file_size, 'overlong ZIP member')
                            dst.write(block)
                        f.need(copied == info.file_size, 'truncated ZIP member')
        except (zipfile.BadZipFile, RuntimeError, NotImplementedError, OSError) as error:
            raise f.Rejected('invalid artifact ZIP') from error
        archive.unlink()  # Only this newly downloaded, verified temporary ZIP.
        self._check_age()
        return destination

    def _download(self, origin, role, destination, members, max_bytes, pin):
        positive(max_bytes, 'download bound')
        f.need(max_bytes <= (MAX_FINAL_BYTES if role in FINAL_ROLES else MAX_ARTIFACT_BYTES) + 1024**2, 'download bound exceeds fixed cap')
        run = self._run(origin)
        self._verify_workflow_source(origin)
        job, binding = self._producer(origin, role, run, pin)
        artifact = self._artifact(origin, role, run, job, pin, max_bytes)
        destination = self._extract(artifact, destination, members, max_bytes)
        # Detect a rerun/changed terminal state during transfer, not only at start.
        self._run(origin)
        other = CURRENT_ORIGIN if origin == OLD_ORIGIN else OLD_ORIGIN
        self._run(other)
        return destination, self._metadata(origin, run, job, artifact, binding)

    @staticmethod
    def _metadata(origin, run, job, artifact, binding):
        # Avoid changing run status/updated_at and API URLs in a provenance map
        # independently derived by concurrently executing final jobs.
        run_keys = ('id', 'run_attempt', 'head_sha', 'event', 'created_at',
                    'workflow_id', 'path', 'head_branch')
        projected_run = {key: run[key] for key in run_keys}
        for key in ('repository', 'head_repository'):
            projected_run[key] = {field: run[key][field] for field in ('id', 'full_name')}
        if origin == OLD_ORIGIN:
            projected_run.update(status=run['status'], conclusion=run['conclusion'])
        projected_job = {key: job[key] for key in ('id', 'name', 'run_id', 'run_attempt', 'head_sha',
                                                  'status', 'conclusion', 'started_at', 'completed_at')}
        numbers = {binding[key]['number'] for key in ('verifier_step', 'upload_step')}
        projected_job['steps'] = [{key: step[key] for key in ('number', 'name', 'status', 'conclusion',
                                                              'started_at', 'completed_at')}
                                  for step in sorted(job['steps'], key=lambda step: step['number'])
                                  if step['number'] in numbers]
        projected_artifact = {key: artifact[key] for key in ('id', 'name', 'size_in_bytes', 'digest',
                                                           'expired', 'created_at', 'expires_at')}
        projected_artifact['workflow_run'] = {key: artifact['workflow_run'][key]
                                              for key in ('id', 'head_sha', 'head_branch',
                                                          'repository_id', 'head_repository_id')}
        return {'run': projected_run, 'job': projected_job, 'artifact': projected_artifact,
                'role': copy.deepcopy(binding)}

    def authenticate_prepare(self, origin, destination, max_bytes=32 * 1024**2):
        context = self._context(origin)
        f.need(origin not in self._prepared, 'prepare already authenticated')
        f.need(type(max_bytes) is int and 0 < max_bytes <= 32 * 1024**2, 'prepare transfer bound')
        pin = context['prepare'] if origin == OLD_ORIGIN else None
        path, metadata = self._download(origin, 'prepare', destination, ['identity.json', 'inventory.json'], max_bytes, pin)
        raw = (path / 'identity.json').read_bytes()
        f.need(len(raw) <= MAX_DESCRIPTOR_BYTES, 'prepare identity bound')
        if pin is not None:
            f.need(f.sha(raw) == pin['identity_sha256'], 'raw old prepare identity hash mismatch')
        identity = f.parse_json(raw)
        f.need(identity == context['identity'], 'authenticated prepare identity mismatch')
        f.need(f.file_sha(path / 'inventory.json') == identity['toolchain_inventory_sha256'], 'authenticated prepare inventory mismatch')
        result = {'origin': origin, 'identity': identity, 'identity_sha256': f.sha(raw),
                  'inventory_path': str(path / 'inventory.json'), 'authenticated_metadata': metadata}
        self._prepared[origin] = copy.deepcopy(result)
        return result

    def download_stage(self, origin, stage_id, destination, max_bytes, pin=None):
        context = self._context(origin)
        f.need(set(self._prepared) == {OLD_ORIGIN, CURRENT_ORIGIN}, 'both authenticated prepares required')
        f.need(isinstance(stage_id, str) and re.fullmatch(r'build_\d{3}', stage_id), 'invalid stage role')
        if origin == OLD_ORIGIN:
            f.need(pin is not None, 'frozen old stage pin required')
            self._validate_pin(pin, prepare=False, identity=context['identity'])
        else:
            f.need(pin is None, 'current origin cannot contain old pins/fallbacks')
        path, metadata = self._download(origin, stage_id, destination, ['delta.tar', 'upload-candidate.json'], max_bytes, pin)
        raw = (path / 'upload-candidate.json').read_bytes()
        raw_sha = f.sha(raw)
        if pin is not None:
            # Check exact bytes BEFORE parsing; do not normalize JSON to its pin.
            f.need(raw_sha == pin['raw_descriptor_sha256'], 'raw descriptor hash mismatch')
        descriptor = f.parse_json(raw)
        f.need(type(descriptor) is dict and descriptor.get('schema') == 'fresh-stage-upload-candidate-v1' and
               descriptor.get('stage_id') == stage_id and descriptor.get('identity') == context['identity'] and
               descriptor.get('producer_job') == metadata['role']['producer_job'] and
               type(descriptor.get('retention_days')) is int and descriptor['retention_days'] == 7, 'native descriptor identity/role mismatch')
        for field in ('archive_sha256', 'receipt_sha256'):
            digest(descriptor.get(field), field)
        archive_bytes = positive(descriptor.get('archive_bytes'), 'archive_bytes')
        f.need(archive_bytes <= MAX_ARTIFACT_BYTES and archive_bytes == (path / 'delta.tar').stat().st_size and
               descriptor['archive_sha256'] == f.file_sha(path / 'delta.tar'), 'native archive digest/size mismatch')
        if pin is not None:
            f.need(all(descriptor[key] == pin[key] for key in ('archive_sha256', 'archive_bytes', 'receipt_sha256')), 'native archive/receipt frozen pin mismatch')
        descriptor.update(artifact_id=metadata['artifact']['id'], producer_job_id=metadata['job']['id'],
                          producer_conclusion='success', artifact_zip_sha256=metadata['artifact']['digest'][7:])
        descriptor.pop('archive_path', None)
        # No origin, path, source normalization or extra transport fields in D(s).
        return {'origin': origin, 'native_descriptor': descriptor, 'archive_path': str(path / 'delta.tar'),
                'authenticated_metadata': metadata, 'raw_descriptor_sha256': raw_sha}

    def download_final(self, role, destination, max_bytes):
        """Download newly produced successor final evidence only; never old final evidence."""
        f.need(role in FINAL_ROLES and CURRENT_ORIGIN in self._prepared, 'current authenticated final role required')
        context = self._context(CURRENT_ORIGIN)
        path, metadata = self._download(CURRENT_ORIGIN, role, destination,
                                        ['payload.tar', 'upload-candidate.json'], max_bytes, None)
        raw = (path / 'upload-candidate.json').read_bytes()
        descriptor = f.parse_json(raw)
        f.need(type(descriptor) is dict and descriptor.get('schema') == 'fresh-final-upload-v1' and
               descriptor.get('role') == role and descriptor.get('identity') == context['identity'] and
               type(descriptor.get('retention_days')) is int and descriptor['retention_days'] == 7,
               'final native identity/role mismatch')
        for field in ('archive_sha256', 'receipt_sha256'):
            digest(descriptor.get(field), field)
        size = positive(descriptor.get('archive_bytes'), 'final archive bytes')
        f.need(size <= MAX_FINAL_BYTES and size == (path / 'payload.tar').stat().st_size and
               descriptor['archive_sha256'] == f.file_sha(path / 'payload.tar'), 'final archive digest/size mismatch')
        descriptor.update(artifact_id=metadata['artifact']['id'], producer_job_id=metadata['job']['id'],
                          producer_conclusion='success', artifact_zip_sha256=metadata['artifact']['digest'][7:])
        descriptor.pop('archive_path', None)
        return {'origin': CURRENT_ORIGIN, 'native_descriptor': descriptor, 'archive_path': str(path / 'payload.tar'),
                'authenticated_metadata': metadata, 'raw_descriptor_sha256': f.sha(raw)}

    def reauthenticate_wrapper(self, wrapper, pin=None):
        """Recheck current API facts without transferring the large payload again.

        The old selection pin remains mandatory. Current native artifact/job IDs
        are frozen to those in the already independently resolved map; the API
        must still resolve the same unique current role and those exact IDs.
        """
        fields = {'origin', 'native_descriptor', 'authenticated_metadata', 'raw_descriptor_sha256'}
        f.need(type(wrapper) is dict and (set(wrapper) == fields or set(wrapper) == fields | {'archive_path'}),
               'unknown/missing resolved wrapper fields')
        origin = wrapper['origin']
        context = self._context(origin)
        f.need(set(self._prepared) == {OLD_ORIGIN, CURRENT_ORIGIN}, 'both authenticated prepares required')
        descriptor = wrapper['native_descriptor']
        f.need(type(descriptor) is dict and descriptor.get('identity') == context['identity'], 'wrapper identity mismatch')
        stage = descriptor.get('stage_id')
        role = stage if stage is not None else descriptor.get('role')
        f.need(isinstance(role, str) and (re.fullmatch(r'build_\d{3}', role) or role in FINAL_ROLES), 'wrapper role invalid')
        f.need(stage is not None or origin == CURRENT_ORIGIN, 'old final artifacts forbidden')
        if origin == OLD_ORIGIN:
            self._validate_pin(pin, prepare=False, identity=context['identity'])
            f.need(wrapper['raw_descriptor_sha256'] == pin['raw_descriptor_sha256'] and
                   all(descriptor.get(key) == pin[key] for key in ('archive_bytes', 'archive_sha256',
                       'receipt_sha256', 'artifact_id', 'producer_job_id', 'artifact_zip_sha256')),
                   'wrapper differs from frozen old pin')
        else:
            f.need(pin is None, 'current wrapper cannot use old pins')
        run = self._run(origin)
        self._verify_workflow_source(origin)
        job, binding = self._producer(origin, role, run, pin)
        maximum = (MAX_ARTIFACT_BYTES if stage is not None else MAX_FINAL_BYTES) + 1024**2
        artifact = self._artifact(origin, role, run, job, pin, maximum)
        f.need(descriptor.get('artifact_id') == artifact['id'] and descriptor.get('producer_job_id') == job['id'] and
               descriptor.get('producer_conclusion') == 'success' and
               descriptor.get('artifact_zip_sha256') == artifact['digest'][7:], 'resolved wrapper authoritative identity changed')
        f.need(stage is None or descriptor.get('producer_job') == binding['producer_job'], 'resolved wrapper producer role changed')
        metadata = self._metadata(origin, run, job, artifact, binding)
        f.need(metadata == wrapper['authenticated_metadata'], 'resolved authenticated metadata changed')
        self._run(CURRENT_ORIGIN if origin == OLD_ORIGIN else OLD_ORIGIN)
        self._check_age()
        return metadata
