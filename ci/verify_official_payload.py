#!/usr/bin/env python3
"""Inactive review candidate: official Actions API -> frozen byte-only verifier.

Run only in a reviewed, read-only, GitHub-hosted Actions workflow under an external
wall-clock supervisor. No URL input, retries, archive files, object admission,
imports, proof build, or continuation activation. The single final receipt is
published atomically only after every selected stream and cleanup succeeds.
"""
from __future__ import annotations
import argparse
import contextlib
import datetime as dt
import hashlib
import json
import math
import os
from pathlib import Path, PurePosixPath
import re
import resource
import signal
import ssl
import stat
import sys
import tempfile
import time
import types
import urllib.error
import urllib.parse
import urllib.request

REPOSITORY = 'jconorgrogan/palomar-chair-verification'
REPOSITORY_ID = 1407290933
API = 'https://api.github.com'
CONSUMER_WORKFLOW = '.github/workflows/conditional-payload-verification.yml'
PRODUCER_WORKFLOW = '.github/workflows/conditional-geometry.yml'
CORE_SHA256 = '7fffe6644346845193ee2e8d4213590816f00858fb1948862de2f50e5b198bdc'
STORAGE_HOST_PATTERN = r'productionresultssa[0-9]+\.blob\.core\.windows\.net'
STAGES = ('F1_curved_existence', 'F2_period_hierarchy')
CHUNK = 64 * 1024
MAX_METADATA = 8 * 1024**2
MAX_LOG = 16 * 1024**2
MAX_PLAN = 128 * 1024
MAX_REVIEW = 8 * 1024**2
MAX_CORE = 128 * 1024
MAX_RECEIPT = 256 * 1024
MAX_SECONDS = 1800
MAX_AS = 1024**3
MAX_CPU_SECONDS = 600
SHA = re.compile(r'[0-9a-f]{64}')
COMMIT = re.compile(r'[0-9a-f]{40}')
ID = re.compile(r'[1-9][0-9]*')
TIMESTAMP = re.compile(r'\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}(?:\.\d{1,6})?Z')

_PHASE, _STAGE = 'startup', 'all'
PHASES = {'startup', 'arguments', 'hardening', 'input_pins', 'consumer_provenance',
          'producer_provenance', 'stage_provenance', 'api_request', 'redirect_policy',
          'storage_request', 'response_framing', 'metadata_or_log', 'payload_stream',
          'connection_cleanup', 'receipt_publication'}
SAFE_REJECTION_LABELS = {
    'absolute job deadline exceeded', 'plan is inactive pending independent review',
    'unapproved signed redirect', 'malformed signed redirect', 'missing/duplicate redirect location',
    'only official API 302 redirect accepted', 'unexpected API metadata redirect',
    'HTTP response is not 200', 'encoded response rejected', 'partial response rejected',
    'invalid content length', 'unsupported transfer encoding', 'ambiguous response framing',
    'exact artifact content length required', 'HTTP resource cleanup failed',
    'authenticated run identity differs', 'current consumer run is not active matching push',
    'artifact identity/size/hash/expiry differs', 'producer job identity/status differs',
    'entire producer log hash differs', 'unique timestamp-anchored producer marker differs',
    'artifact expires before absolute job deadline', 'exact checkout distribution differs',
    'distribution input hash differs', 'plan hash differs', 'frozen core hash differs',
    'producer must be an earlier distinct run', 'producer run status is not approved',
}


def mark(phase, stage=None):
    global _PHASE, _STAGE
    _PHASE = phase if phase in PHASES else 'startup'
    if stage is not None:
        _STAGE = stage if stage in STAGES else 'all'


def failure_label(error):
    # Never format arbitrary exception text, including errors from the frozen
    # core, HTTP/TLS, parsing, system libraries, or test doubles.
    label = error.args[0] if type(error) is Rejected and len(error.args) == 1 else None
    return label if type(label) is str and label in SAFE_REJECTION_LABELS else 'verification rejected'


class SafeArgumentParser(argparse.ArgumentParser):
    def error(self, message):
        self.exit(2, 'REJECTED_OFFICIAL_PAYLOAD phase=arguments stage=all reason=invalid arguments; no acceptance receipt\n')


class Rejected(Exception):
    """Messages are fixed labels only, never remote bodies, credentials, or URLs."""


def need(value, label):
    if not value:
        raise Rejected(label)


def digest(value):
    return type(value) is str and SHA.fullmatch(value) is not None


def sha(data):
    return hashlib.sha256(data).hexdigest()


def canonical(value):
    return (json.dumps(value, sort_keys=True, indent=2, allow_nan=False) + '\n').encode()


def parse_json(data):
    def pairs(rows):
        out = {}
        for key, value in rows:
            need(key not in out, 'duplicate JSON key')
            out[key] = value
        return out
    try:
        return json.loads(data, object_pairs_hook=pairs,
                          parse_constant=lambda _: (_ for _ in ()).throw(Rejected('nonfinite JSON')))
    except (ValueError, UnicodeError, RecursionError):
        raise Rejected('invalid JSON') from None


def remaining(deadline):
    need(type(deadline) in (int, float) and math.isfinite(deadline), 'invalid deadline')
    value = deadline - time.monotonic()
    need(value > 0, 'absolute job deadline exceeded')
    return min(30.0, value)


def timestamp(value):
    need(type(value) is str and TIMESTAMP.fullmatch(value) is not None, 'invalid UTC timestamp')
    try:
        return dt.datetime.fromisoformat(value[:-1] + '+00:00')
    except ValueError:
        raise Rejected('invalid UTC timestamp') from None


def identity(value):
    need(type(value) is dict and set(value) == {'repository', 'run_id', 'run_attempt', 'workflow_commit'},
         'identity keys differ')
    need(value['repository'] == REPOSITORY and all(type(value[k]) is str and ID.fullmatch(value[k])
         for k in ('run_id', 'run_attempt')) and type(value['workflow_commit']) is str
         and COMMIT.fullmatch(value['workflow_commit']), 'identity values differ')


def read_local(path, maximum, deadline):
    remaining(deadline)
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    try:
        info = os.fstat(fd)
        need(stat.S_ISREG(info.st_mode) and info.st_nlink == 1 and info.st_size <= maximum,
             'input is not a bounded regular single-link file')
        with os.fdopen(fd, 'rb') as handle:
            fd = None
            blocks, count = [], 0
            while True:
                remaining(deadline)
                block = handle.read(min(CHUNK, maximum + 1 - count))
                remaining(deadline)
                if not block:
                    break
                count += len(block)
                need(count <= maximum, 'local input byte cap exceeded')
                blocks.append(block)
        remaining(deadline)
        return b''.join(blocks)
    finally:
        if fd is not None:
            os.close(fd)


def relative_file(root, value):
    need(type(value) is str and value and '\\' not in value and '\x00' not in value,
         'invalid plan input path')
    rel = PurePosixPath(value)
    need(not rel.is_absolute() and str(rel) == value and len(rel.parts) <= 8
         and all(part not in ('', '.', '..') for part in rel.parts), 'noncanonical plan input path')
    current = Path(root)
    for part in rel.parts:
        current /= part
        need(not current.is_symlink(), 'symlink in plan input path')
    return current


def validate_plan(plan):
    need(type(plan) is dict and set(plan) == {'schema', 'consumer_workflow_path', 'producer',
         'storage_host_pattern', 'review_status', 'helper_sha256', 'core_sha256', 'input_files', 'stages'}, 'plan keys differ')
    need(plan['schema'] == 'conditional-official-payload-plan-v1'
         and plan['consumer_workflow_path'] == CONSUMER_WORKFLOW
         and plan['storage_host_pattern'] == STORAGE_HOST_PATTERN, 'plan policy differs')
    need(plan['review_status'] == 'independently_reviewed_for_activation', 'plan is inactive pending independent review')
    need(digest(plan['helper_sha256']) and plan['core_sha256'] == CORE_SHA256, 'helper/core pin differs')
    files = plan['input_files']
    need(type(files) is list and 1 <= len(files) <= 100, 'input file list bound')
    paths = []
    for row in files:
        need(type(row) is dict and set(row) == {'path', 'sha256'} and type(row['path']) is str
             and row['path'] not in paths and digest(row['sha256']), 'input file list invalid/duplicate')
        paths.append(row['path'])
    producer = plan['producer']
    need(type(producer) is dict and set(producer) == {'identity', 'workflow_path', 'workflow_id',
         'status_policy'}, 'producer pin keys differ')
    identity(producer['identity'])
    need(producer['workflow_path'] == PRODUCER_WORKFLOW and type(producer['workflow_id']) is int
         and producer['workflow_id'] > 0 and producer['status_policy'] in
         ('completed_only', 'allow_in_progress_byte_verification_only'), 'producer policy differs')
    rows = plan['stages']
    need(type(rows) is list and 1 <= len(rows) <= 2, 'stage list size differs')
    selected = [row.get('stage_id') if type(row) is dict else None for row in rows]
    need(selected in ([STAGES[0]], [STAGES[1]], list(STAGES)),
         'stage list must be exact F1, F2, or ordered F1 then F2')
    paths = []
    for row in rows:
        need(set(row) == {'stage_id', 'expectation_file', 'expectation_sha256', 'certificate_file',
             'certificate_sha256', 'independent_review_sha256', 'artifact_expires_at'}, 'stage pin keys differ')
        need(digest(row['expectation_sha256']) and digest(row['certificate_sha256']) and digest(row['independent_review_sha256']), 'invalid input digest')
        timestamp(row['artifact_expires_at'])
        for key in ('expectation_file', 'certificate_file'):
            value = row[key]
            need(type(value) is str and value not in paths, 'duplicate/invalid input path')
            paths.append(value)


def validate_distribution(root, plan_path, plan):
    expected = {row['path'] for row in plan['input_files']}
    plan_name = Path(plan_path).name
    need(plan_name not in expected and CONSUMER_WORKFLOW not in expected,
         'plan and consumer workflow must not self-pin')
    expected |= {plan_name, CONSUMER_WORKFLOW}
    expected_dirs = set()
    for name in expected:
        relative_file(root, name)
        need(PurePosixPath(name).parts[0] != '.git', 'git internals cannot be inputs')
        expected_dirs.update(str(p) for p in PurePosixPath(name).parents if str(p) != '.')
    actual_files, actual_dirs = set(), set()
    for base, directories, files in os.walk(root, followlinks=False):
        if Path(base) == root and '.git' in directories:
            directories.remove('.git')
        if Path(base) == root and '.git' in files:
            files.remove('.git')
        need(len(actual_dirs) + len(actual_files) + len(directories) + len(files) <= 300,
             'checkout distribution entry cap exceeded')
        for name in directories:
            path = Path(base) / name
            need(not path.is_symlink(), 'symlink directory in checkout')
            actual_dirs.add(path.relative_to(root).as_posix())
        for name in files:
            path = Path(base) / name
            info = path.lstat()
            need(stat.S_ISREG(info.st_mode) and info.st_nlink == 1, 'nonregular/hardlinked checkout input')
            actual_files.add(path.relative_to(root).as_posix())
    need(actual_files == expected and actual_dirs == expected_dirs, 'exact checkout distribution differs')


def load_inputs(plan_path, plan_sha256, core_path, deadline):
    need(digest(plan_sha256), 'invalid plan hash')
    plan_bytes = read_local(plan_path, MAX_PLAN, deadline)
    need(sha(plan_bytes) == plan_sha256, 'plan hash differs')
    plan = parse_json(plan_bytes)
    validate_plan(plan)
    root = Path(plan_path).resolve().parent
    validate_distribution(root, plan_path, plan)
    declared = {}
    for row in plan['input_files']:
        path = relative_file(root, row['path'])
        need(path.resolve() != Path(plan_path).resolve(), 'plan cannot pin itself')
        data = read_local(path, MAX_METADATA, deadline)
        need(sha(data) == row['sha256'], 'distribution input hash differs')
        declared[path.resolve()] = row['sha256']
    need(declared.get(Path(__file__).resolve()) == plan['helper_sha256'], 'executed helper is not plan-pinned')
    need(declared.get(Path(core_path).resolve()) == CORE_SHA256, 'core path is not plan-pinned')
    code = read_local(core_path, MAX_CORE, deadline)
    need(sha(code) == CORE_SHA256, 'frozen core hash differs')
    core = types.ModuleType('frozen_stream_verify')
    exec(compile(code, '<frozen-stream-verifier>', 'exec'), core.__dict__)
    inputs = []
    for row in plan['stages']:
        expected_bytes = read_local(relative_file(Path(plan_path).parent, row['expectation_file']),
                                    core.MAX_EXPECTATION, deadline)
        certificate_bytes = read_local(relative_file(root, row['certificate_file']), MAX_REVIEW, deadline)
        need(declared.get(relative_file(root, row['expectation_file']).resolve()) == row['expectation_sha256']
             and declared.get(relative_file(root, row['certificate_file']).resolve()) == row['certificate_sha256'],
             'stage files are absent/mismatched in input list')
        need(sha(expected_bytes) == row['expectation_sha256'] and sha(certificate_bytes) == row['certificate_sha256'],
             'expectation/certificate input hash differs')
        expected = core.parse_json(expected_bytes)
        core.validate_expected(expected)
        origin = expected['origin']
        need(origin['stage_id'] == row['stage_id'] and origin['identity'] == plan['producer']['identity']
             and origin['workflow_id'] == plan['producer']['workflow_id']
             and origin['workflow_path'] == plan['producer']['workflow_path'], 'expectation origin differs from plan')
        # This is a host-provided certificate pinned by the plan, not a freshly
        # authenticated reviewer. The independent review SHA is a declared pin.
        need(type(parse_json(certificate_bytes)) is dict, 'certificate must be JSON object')
        inputs.append({'pin': row, 'expected': expected})
    remaining(deadline)
    return plan, inputs, core


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *args, **kwargs):
        return None


def make_opener():
    # Default ProxyHandler preserves the configured proxy environment, including
    # no_proxy. No direct/proxy fallback is attempted after any request fails.
    context = ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
    context.load_default_certs(ssl.Purpose.SERVER_AUTH)
    need(context.check_hostname and context.verify_mode == ssl.CERT_REQUIRED, 'TLS verification unavailable')
    # No HTTPCookieProcessor, password manager, or SSLKEYLOGFILE side effect.
    return urllib.request.build_opener(NoRedirect(), urllib.request.HTTPSHandler(context=context))


def header_values(response):
    result = {}
    entries = list(response.headers.items())
    need(len(entries) <= 100 and sum(len(str(k)) + len(str(v)) for k, v in entries) <= 64 * 1024,
         'HTTP header cap exceeded')
    for key, value in entries:
        need(type(key) is str and type(value) is str and '\r' not in value and '\n' not in value,
             'invalid HTTP header')
        result.setdefault(key.lower(), []).append(value.strip())
    return result


def validate_response(response, maximum, exact_bytes=None):
    need(response.status == 200, 'HTTP response is not 200')
    headers = header_values(response)
    encoding = headers.get('content-encoding', [])
    need(not encoding or encoding == ['identity'], 'encoded response rejected')
    need('content-range' not in headers, 'partial response rejected')
    length, transfer = headers.get('content-length', []), headers.get('transfer-encoding', [])
    need(not length or (len(length) == 1 and re.fullmatch(r'[0-9]+', length[0])
         and int(length[0]) <= maximum), 'invalid content length')
    need(not transfer or transfer == ['chunked'], 'unsupported transfer encoding')
    need(not (length and transfer), 'ambiguous response framing')
    if exact_bytes is not None:
        need(length == [str(exact_bytes)] and not transfer, 'exact artifact content length required')
    return int(length[0]) if length else None


def redirect_url(response):
    need(response.status == 302, 'only official API 302 redirect accepted')
    headers = header_values(response)
    values = headers.get('location', [])
    need(len(values) == 1, 'missing/duplicate redirect location')
    url = values[0]
    need(0 < len(url) <= 16 * 1024 and all(33 <= ord(c) <= 126 for c in url)
         and '\\' not in url, 'malformed signed redirect')
    try:
        parsed = urllib.parse.urlsplit(url)
        need(parsed.scheme == 'https' and parsed.username is None and parsed.password is None
             and parsed.fragment == '' and parsed.port in (None, 443)
             and type(parsed.hostname) is str and re.fullmatch(STORAGE_HOST_PATTERN, parsed.hostname)
             and parsed.netloc in (parsed.hostname, parsed.hostname + ':443')
             and parsed.path.startswith('/') and bool(parsed.query), 'unapproved signed redirect')
    except ValueError:
        raise Rejected('malformed signed redirect') from None
    return url


def resources_of(response):
    # HTTPError wraps HTTPResponse in .fp, which itself wraps the buffered
    # socket. Retain the entire small chain before EOF can clear any .fp.
    pending, resources, seen = [response], [], set()
    while pending:
        current = pending.pop(0)
        if id(current) in seen:
            continue
        seen.add(id(current))
        resources.append(current)
        need(len(resources) <= 12, 'unexpected HTTP resource nesting')
        for name in ('fp', 'raw', '_sock'):
            nested = getattr(current, name, None)
            if nested is not None and callable(getattr(nested, 'close', None)):
                pending.append(nested)
    return resources


def close_all(resources):
    failed = False
    for item in resources:
        try:
            item.close()
        except BaseException:
            failed = True
    need(not failed, 'HTTP resource cleanup failed')


class BoundedResponse:
    def __init__(self, response, maximum, deadline, exact_bytes=None):
        self.response, self.maximum, self.deadline = response, maximum, deadline
        self.length = validate_response(response, maximum, exact_bytes)
        self.count, self.eof = 0, False

    def read(self, count):
        need(type(count) is int and 0 < count <= CHUNK, 'read request exceeds 64 KiB')
        remaining(self.deadline)
        data = getattr(self.response, 'read1', self.response.read)(count)
        remaining(self.deadline)
        need(type(data) is bytes and len(data) <= count, 'invalid response read')
        self.count += len(data)
        need(self.count <= self.maximum, 'remote body byte cap exceeded')
        if not data:
            need(self.length is None or self.count == self.length, 'truncated HTTP response')
            self.eof = True
        return data

    def all(self):
        blocks = []
        while True:
            block = self.read(min(CHUNK, self.maximum + 1 - self.count))
            if not block:
                return b''.join(blocks)
            blocks.append(block)


class OfficialAPI:
    def __init__(self, token, deadline, opener_factory=None):
        need(type(token) is str and token and len(token) <= 4096 and all(33 <= ord(c) <= 126 for c in token),
             'ephemeral workflow token unavailable/invalid')
        self.token, self.deadline = token, deadline
        self.factory = opener_factory or make_opener
        self.metadata, self.log_metadata = {}, {}
        self.requests, self.redirects = 0, 0

    @contextlib.contextmanager
    def response(self, path, maximum, *, signed_redirect=False, exact_bytes=None):
        need(type(path) is str and re.fullmatch(r'/repos/jconorgrogan/palomar-chair-verification/actions/'
             r'[A-Za-z0-9_./?=&-]+', path) and '..' not in path and len(path) <= 512,
             'unapproved API path')
        remaining(self.deadline)
        api_opener = storage_opener = None
        api_resources, storage_resources = [], []
        try:
            api_opener = self.factory()
            request = urllib.request.Request(API + path, headers={
                'Authorization': 'Bearer ' + self.token, 'Accept': 'application/vnd.github+json',
                'X-GitHub-Api-Version': '2022-11-28', 'User-Agent': 'conditional-byte-verification/1',
                'Accept-Encoding': 'identity', 'Connection': 'close'})
            self.requests += 1
            mark('api_request')
            try:
                response = api_opener.open(request, timeout=remaining(self.deadline))
            except urllib.error.HTTPError as error:
                response = error
            api_resources = resources_of(response)
            remaining(self.deadline)
            if response.status == 302:
                need(signed_redirect, 'unexpected API metadata redirect')
                mark('redirect_policy')
                url = redirect_url(response)
                # Close the authenticated API response before using its signed URL.
                close_all(api_resources)
                api_resources = []
                remaining(self.deadline)
                storage_opener = self.factory()
                clean_request = urllib.request.Request(url, headers={
                    'User-Agent': 'conditional-byte-verification/1', 'Accept-Encoding': 'identity',
                    'Connection': 'close'})
                self.redirects += 1
                mark('storage_request')
                try:
                    response = storage_opener.open(clean_request, timeout=remaining(self.deadline))
                except urllib.error.HTTPError as error:
                    response = error
                storage_resources = resources_of(response)
                remaining(self.deadline)
                # Any second redirect, auth challenge, partial/other status fails.
            mark('response_framing')
            stream = BoundedResponse(response, maximum, self.deadline, exact_bytes=exact_bytes)
            mark('payload_stream' if exact_bytes is not None else 'metadata_or_log')
            yield stream
            need(stream.eof, 'response EOF was not verified')
        finally:
            if sys.exc_info()[0] is None:
                mark('connection_cleanup')
            # Every nested resource is attempted even when an earlier close fails.
            try:
                close_all(storage_resources)
            finally:
                try:
                    close_all(api_resources)
                finally:
                    try:
                        if storage_opener is not None:
                            storage_opener.close()
                    finally:
                        if api_opener is not None:
                            api_opener.close()
            remaining(self.deadline)

    def get(self, path):
        need(path not in self.metadata, 'metadata endpoint repeated')
        with self.response(path, MAX_METADATA) as stream:
            data = stream.all()
        obj = parse_json(data)
        need(type(obj) is dict, 'API metadata must be JSON object')
        self.metadata[path] = {'bytes': len(data), 'sha256': sha(data)}
        return obj

    def collection(self, path, key):
        result, total = [], None
        for page in range(1, 7):
            obj = self.get(path + f'?per_page=100&page={page}')
            rows, count = obj.get(key), obj.get('total_count')
            need(type(rows) is list and len(rows) <= 100 and all(type(row) is dict for row in rows)
                 and type(count) is int and 0 <= count <= 600, 'invalid API collection')
            need(total is None or total == count, 'API collection count changed')
            total = count
            result.extend(rows)
            if len(rows) < 100:
                need(len(result) == total, 'API collection count differs')
                return result
        raise Rejected('API pagination cap exceeded')

    def producer_log(self, origin):
        path = f'/repos/{REPOSITORY}/actions/jobs/{origin["producer_job_id"]}/logs'
        with self.response(path, MAX_LOG, signed_redirect=True) as stream:
            data = stream.all()
        need(sha(data) == origin['producer_job_log_sha256'], 'entire producer log hash differs')
        markers = re.findall(rb'^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}(?:\.\d+)?Z '
                             rb'CONDITIONAL_STAGE_ARTIFACT_V1 (\{[^\r\n]*\})\r?$', data, re.M)
        need(len(markers) == 1 and parse_json(markers[0]) == origin['producer_marker'],
             'unique timestamp-anchored producer marker differs')
        self.log_metadata[path] = {'bytes': len(data), 'sha256': sha(data)}


def workflow(api, path, expected_id=None):
    result = api.get(f'/repos/{REPOSITORY}/actions/workflows/{PurePosixPath(path).name}')
    need(result.get('path') == path and type(result.get('id')) is int and result['id'] > 0,
         'authenticated workflow path/id differs')
    need(expected_id is None or result['id'] == expected_id, 'pinned workflow id differs')
    return result['id']


def authenticated_run(api, ident, workflow_path, workflow_id, *, current=False, branch=None, policy=None):
    run = api.get(f'/repos/{REPOSITORY}/actions/runs/{ident["run_id"]}')
    need(type(run.get('id')) is int and str(run['id']) == ident['run_id']
         and type(run.get('run_attempt')) is int and str(run['run_attempt']) == ident['run_attempt']
         and run.get('head_sha') == ident['workflow_commit'] and run.get('event') == 'push'
         and type(run.get('repository')) is dict and run['repository'].get('full_name') == REPOSITORY
         and type(run['repository'].get('id')) is int and run['repository']['id'] == REPOSITORY_ID
         and type(run.get('head_repository')) is dict and run['head_repository'].get('full_name') == REPOSITORY
         and type(run['head_repository'].get('id')) is int and run['head_repository']['id'] == REPOSITORY_ID
         and run.get('path') == workflow_path and run.get('workflow_id') == workflow_id,
         'authenticated run identity differs')
    if current:
        need(run.get('status') == 'in_progress' and run.get('conclusion') is None
             and run.get('head_branch') == branch, 'current consumer run is not active matching push')
    else:
        statuses = ('completed',) if policy == 'completed_only' else ('in_progress', 'completed')
        need(run.get('status') in statuses, 'producer run status is not approved')
    return run


def authenticate(api, plan, inputs, environ):
    mark('consumer_provenance', 'all')
    need(environ.get('GITHUB_ACTIONS') == 'true' and environ.get('RUNNER_ENVIRONMENT') == 'github-hosted'
         and environ.get('RUNNER_OS') == 'Linux' and environ.get('GITHUB_REPOSITORY') == REPOSITORY
         and environ.get('GITHUB_EVENT_NAME') == 'push' and environ.get('GITHUB_API_URL') == API
         and environ.get('GITHUB_SERVER_URL') == 'https://github.com', 'not approved official Actions context')
    current = {'repository': REPOSITORY, 'run_id': environ.get('GITHUB_RUN_ID'),
               'run_attempt': environ.get('GITHUB_RUN_ATTEMPT'), 'workflow_commit': environ.get('GITHUB_SHA')}
    identity(current)
    ref = environ.get('GITHUB_REF', '')
    need(ref.startswith('refs/heads/') and len(ref) > len('refs/heads/') and '\n' not in ref
         and environ.get('GITHUB_WORKFLOW_REF') == REPOSITORY + '/' + CONSUMER_WORKFLOW + '@' + ref
         and environ.get('GITHUB_WORKFLOW_SHA') == current['workflow_commit'], 'consumer workflow ref/SHA differs')
    producer = plan['producer']
    need(int(producer['identity']['run_id']) < int(current['run_id']), 'producer must be an earlier distinct run')
    current_workflow_id = workflow(api, CONSUMER_WORKFLOW)
    current_run = authenticated_run(api, current, CONSUMER_WORKFLOW, current_workflow_id,
                                    current=True, branch=ref[len('refs/heads/'):])
    mark('producer_provenance')
    producer_workflow_id = workflow(api, PRODUCER_WORKFLOW, producer['workflow_id'])
    producer_run = authenticated_run(api, producer['identity'], PRODUCER_WORKFLOW, producer_workflow_id,
                                     policy=producer['status_policy'])
    old = producer['identity']
    jobs = api.collection(f'/repos/{REPOSITORY}/actions/runs/{old["run_id"]}/attempts/{old["run_attempt"]}/jobs', 'jobs')
    artifacts = api.collection(f'/repos/{REPOSITORY}/actions/runs/{old["run_id"]}/artifacts', 'artifacts')
    bound = []
    for item in inputs:
        origin, pin = item['expected']['origin'], item['pin']
        mark('stage_provenance', pin['stage_id'])
        candidates = [j for j in jobs if j.get('name') == origin['producer_job_name']]
        need(len(candidates) == 1, 'producer job name missing/duplicated')
        job = candidates[0]
        need(type(job.get('id')) is int and job['id'] == origin['producer_job_id']
             and sum(j.get('id') == job['id'] for j in jobs) == 1 and job.get('status') == 'completed'
             and job.get('conclusion') == 'success' and str(job.get('run_id')) == old['run_id']
             and str(job.get('run_attempt')) == old['run_attempt'] and job.get('head_sha') == old['workflow_commit'],
             'producer job identity/status differs')
        matches = [a for a in artifacts if a.get('name') == origin['artifact_name']]
        need(len(matches) == 1, 'artifact name missing/duplicated')
        artifact = matches[0]
        need(type(artifact.get('id')) is int and artifact['id'] == origin['artifact_id']
             and sum(a.get('id') == artifact['id'] for a in artifacts) == 1 and artifact.get('expired') is False
             and type(artifact.get('size_in_bytes')) is int and artifact['size_in_bytes'] == origin['artifact_zip_bytes']
             and artifact.get('digest') == 'sha256:' + origin['artifact_zip_sha256']
             and artifact.get('expires_at') == pin['artifact_expires_at'], 'artifact identity/size/hash/expiry differs')
        run = artifact.get('workflow_run')
        need(type(run) is dict and str(run.get('id')) == old['run_id']
             and run.get('head_sha') == old['workflow_commit']
             and type(run.get('repository_id')) is int and run['repository_id'] == REPOSITORY_ID
             and type(run.get('head_repository_id')) is int and run['head_repository_id'] == REPOSITORY_ID,
             'artifact producer run/commit/repository id differs')
        expiry = timestamp(artifact['expires_at'])
        need(expiry > dt.datetime.now(dt.timezone.utc) + dt.timedelta(seconds=remaining_full(api.deadline)),
             'artifact expires before absolute job deadline')
        api.producer_log(origin)
        bound.append({'stage_id': pin['stage_id'], 'producer_job': job, 'artifact': artifact})
    remaining(api.deadline)
    return current, current_workflow_id, producer_run['status'], bound


def remaining_full(deadline):
    remaining(deadline)
    return max(0, deadline - time.monotonic())


def verify_all(plan, inputs, core, *, plan_sha256, deadline, environ, opener_factory=None):
    api = OfficialAPI(environ.get('GH_TOKEN'), deadline, opener_factory=opener_factory)
    current, current_workflow_id, producer_status, bound = authenticate(api, plan, inputs, environ)
    results = []
    for item, authenticated in zip(inputs, bound):
        origin = item['expected']['origin']
        mark('payload_stream', origin['stage_id'])
        path = f'/repos/{REPOSITORY}/actions/artifacts/{origin["artifact_id"]}/zip'
        with api.response(path, core.MAX_ZIP, signed_redirect=True,
                          exact_bytes=origin['artifact_zip_bytes']) as source:
            result = core.verify_stream(source, item['expected'], deadline=deadline)
        # response, nested file/socket handles, and both openers have closed here.
        remaining(deadline)
        results.append({'stage_id': origin['stage_id'], 'expectation_sha256': item['pin']['expectation_sha256'],
                        'host_certificate_sha256': item['pin']['certificate_sha256'],
                        'declared_independent_review_sha256': item['pin']['independent_review_sha256'],
                        'artifact_expires_at': item['pin']['artifact_expires_at'],
                        'authenticated_job_metadata_sha256': sha(canonical(authenticated['producer_job'])),
                        'authenticated_artifact_metadata_sha256': sha(canonical(authenticated['artifact'])),
                        'byte_verification': result})
    remaining(deadline)
    return {'schema': 'conditional-official-payload-verification-v1', 'status': 'BYTE_VERIFIED_ONLY',
            'plan_sha256': plan_sha256, 'helper_sha256': plan['helper_sha256'], 'stream_core_sha256': CORE_SHA256,
            'pinned_input_files': plan['input_files'], 'independent_reviewer_freshly_authenticated': False,
            'consumer_identity': current, 'consumer_workflow_path': CONSUMER_WORKFLOW,
            'consumer_workflow_id': current_workflow_id, 'producer_status_observed': producer_status,
            'producer_status_policy': plan['producer']['status_policy'],
            'selected_stages': [item['pin']['stage_id'] for item in inputs], 'stages': results,
            'api_metadata': api.metadata, 'producer_logs': api.log_metadata,
            'acquisition': {'api_origin': API, 'storage_host_pattern': STORAGE_HOST_PATTERN,
                            'storage_host_policy_previously_exercised': False,
                            'authenticated_api_requests': api.requests, 'signed_redirects_followed': api.redirects,
                            'redirects_per_response_maximum': 1, 'bearer_sent_only_to_api_github_com': True,
                            'storage_cookies_or_authorization_sent': False, 'configured_proxy_environment_preserved': True,
                            'TLS_certificate_and_hostname_verification': True, 'read_chunk_max_bytes': CHUNK,
                            'retries': 0, 'range_requests': 0, 'resume_performed': False,
                            'all_response_EOF_and_connection_cleanup_completed': True},
            'limits': {'address_space_bytes': MAX_AS, 'logical_cpus': 1, 'cpu_seconds_max': MAX_CPU_SECONDS, 'absolute_deadline_max_seconds': MAX_SECONDS,
                       'external_supervisor_required': True, 'zip_bytes_max': core.MAX_ZIP,
                       'metadata_bytes_max': MAX_METADATA, 'job_log_bytes_max': MAX_LOG},
            'archive_admission_performed': False, 'objects_executed_or_imported': False,
            'object_payload_bytes_written': 0, 'producer_commands_or_semantics_validated': False,
            'final_proof_claim': False, 'continuation_activation_performed': False}


def write_receipt(path, result, deadline, publication=None):
    """One bounded atomic file, no clobber; failure removes any newly linked result."""
    remaining(deadline)
    path = Path(path)
    need(not path.exists() and not path.is_symlink() and path.parent.is_dir(), 'receipt destination unavailable')
    data = canonical(result)
    need(len(data) <= MAX_RECEIPT, 'receipt byte cap exceeded')
    fd, temporary = tempfile.mkstemp(prefix='.byte-verification-', suffix='.tmp', dir=path.parent)
    published = False
    try:
        with os.fdopen(fd, 'wb') as output:
            fd = None
            for offset in range(0, len(data), CHUNK):
                remaining(deadline)
                output.write(data[offset:offset + CHUNK])
            output.flush()
            os.fsync(output.fileno())
        remaining(deadline)
        own_inode = os.stat(temporary).st_ino
        if publication is not None:
            publication.update(path=str(path), inode=own_inode)
        os.link(temporary, path, follow_symlinks=False)
        published = True
        os.unlink(temporary)
        temporary = None
        remaining(deadline)
        directory_fd = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
        try:
            os.fsync(directory_fd)
        finally:
            os.close(directory_fd)
        remaining(deadline)
    except BaseException:
        if published:
            try:
                os.unlink(path)
            except FileNotFoundError:
                pass
        raise
    finally:
        try:
            if fd is not None:
                os.close(fd)
        finally:
            if temporary is not None:
                os.unlink(temporary)


def harden_process(seconds):
    need(type(seconds) is int and 0 < seconds <= MAX_SECONDS, 'invalid job duration')
    started = time.monotonic()
    deadline = started + seconds
    resource.setrlimit(resource.RLIMIT_AS, (MAX_AS, MAX_AS))
    resource.setrlimit(resource.RLIMIT_CPU, (MAX_CPU_SECONDS, MAX_CPU_SECONDS))
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    resource.setrlimit(resource.RLIMIT_FSIZE, (MAX_RECEIPT, MAX_RECEIPT))
    cpus = os.sched_getaffinity(0)
    need(bool(cpus), 'CPU affinity unavailable')
    os.sched_setaffinity(0, {min(cpus)})
    need(len(os.sched_getaffinity(0)) == 1, 'one CPU affinity failed')
    def expired(_signal, _frame):
        raise Rejected('absolute job deadline exceeded')
    signal.signal(signal.SIGALRM, expired)
    signal.setitimer(signal.ITIMER_REAL, remaining_full(deadline))
    return deadline


def main(argv=None):
    parser = SafeArgumentParser(description=__doc__)
    parser.add_argument('--plan', required=True)
    parser.add_argument('--plan-sha256', required=True)
    parser.add_argument('--core', required=True)
    parser.add_argument('--receipt', required=True)
    parser.add_argument('--seconds', type=int, default=1800)
    args = parser.parse_args(argv)
    publication = {}
    try:
        sys.dont_write_bytecode = True
        mark('hardening', 'all')
        deadline = harden_process(args.seconds)
        need(not Path(args.receipt).exists() and not Path(args.receipt).is_symlink(), 'receipt already exists')
        mark('input_pins')
        plan, inputs, core = load_inputs(args.plan, args.plan_sha256, args.core, deadline)
        result = verify_all(plan, inputs, core, plan_sha256=args.plan_sha256, deadline=deadline, environ=os.environ)
        mark('receipt_publication', 'all')
        write_receipt(args.receipt, result, deadline, publication)
        signal.setitimer(signal.ITIMER_REAL, 0)
        # The final artifact is the only success marker; stdout carries no secret.
        return 0
    except BaseException as error:
        if publication:
            try:
                if os.lstat(publication['path']).st_ino == publication['inode']:
                    os.unlink(publication['path'])
            except FileNotFoundError:
                pass
        # Network and parser exceptions can contain signed URLs/token-bearing data.
        # Never stringify any exception, request, response, or headers.
        print('REJECTED_OFFICIAL_PAYLOAD phase=' + _PHASE + ' stage=' + _STAGE
              + ' reason=' + failure_label(error) + '; no acceptance receipt', file=sys.stderr)
        return 1
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)


if __name__ == '__main__':
    raise SystemExit(main())
