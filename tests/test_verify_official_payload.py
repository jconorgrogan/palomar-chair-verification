"""Offline-only fake HTTP tests; no network, producer objects, or proof imports."""
import copy
import datetime as dt
from email.message import Message
import importlib.util
import io
import json
import os
from pathlib import Path
import signal
import socket
import ssl
import tarfile
import tempfile
import time
import unittest
from unittest import mock
import urllib.error
import urllib.request

import verify_official_payload as h
import stream_verify as v
from test_stream_verify import fixture, seal

PREFIX = '/repos/' + h.REPOSITORY + '/actions/'
SECRET_URL = 'https://productionresultssa2.blob.core.windows.net/fixture?sig=DO_NOT_PRINT'
SECRET_TOKEN = 'ghs_DO_NOT_PRINT'


def stage_fixture(stage='F1_curved_existence', artifact_id=2, job_id=3):
    expected, _, _, old_tar = fixture()
    expected['receipt']['stage_id'] = stage
    expected['descriptor']['stage_id'] = stage
    origin = expected['origin']
    origin.update(stage_id=stage, artifact_id=artifact_id, producer_job_id=job_id,
                  artifact_name=f'conditional-geometry-123-1-{stage}-objects',
                  producer_job_name='conditional ' + stage)
    origin['producer_marker'].update(stage_id=stage, artifact_id=str(artifact_id),
                                    artifact_name=origin['artifact_name'])
    rb = v.canonical_json(expected['receipt'])
    expected['descriptor']['receipt_sha256'] = v.sha(rb)
    source = tarfile.open(fileobj=io.BytesIO(old_tar))
    out = io.BytesIO()
    with tarfile.open(fileobj=out, mode='w', format=tarfile.USTAR_FORMAT) as archive:
        for member in source:
            data = rb if member.name == 'receipt.json' else source.extractfile(member).read()
            info = tarfile.TarInfo(member.name)
            info.mode, info.size = 0o644, len(data)
            archive.addfile(info, io.BytesIO(data))
    source.close()
    expected, data, _ = seal(expected, out.getvalue())
    marker = json.dumps(expected['origin']['producer_marker'], sort_keys=True).encode()
    log = b'2026-10-16T16:01:02.123Z CONDITIONAL_STAGE_ARTIFACT_V1 ' + marker + b'\n'
    expected['origin']['producer_job_log_sha256'] = h.sha(log)
    return expected, data, log


def environment():
    return {'GITHUB_ACTIONS': 'true', 'RUNNER_ENVIRONMENT': 'github-hosted', 'RUNNER_OS': 'Linux',
            'GITHUB_REPOSITORY': h.REPOSITORY, 'GITHUB_EVENT_NAME': 'push', 'GITHUB_API_URL': h.API,
            'GITHUB_SERVER_URL': 'https://github.com', 'GITHUB_RUN_ID': '456', 'GITHUB_RUN_ATTEMPT': '1',
            'GITHUB_SHA': 'b' * 40, 'GITHUB_REF': 'refs/heads/review',
            'GITHUB_WORKFLOW_REF': h.REPOSITORY + '/' + h.CONSUMER_WORKFLOW + '@refs/heads/review',
            'GITHUB_WORKFLOW_SHA': 'b' * 40, 'GH_TOKEN': SECRET_TOKEN}


def plan_and_inputs(count=1):
    rows, inputs, bodies = [], [], {}
    for index in range(count):
        stage = h.STAGES[index]
        exp, data, log = stage_fixture(stage, 2 + index * 10, 3 + index * 10)
        row = {'stage_id': stage, 'expectation_file': f'expectations/{stage}.json',
               'expectation_sha256': h.sha(v.canonical_json(exp)), 'certificate_file': f'certificates/{stage}.json',
               'certificate_sha256': h.sha(b'{}\n'), 'independent_review_sha256': 'c' * 64,
               'artifact_expires_at': '2030-10-23T16:37:58Z'}
        rows.append(row)
        inputs.append({'pin': row, 'expected': exp})
        bodies[stage] = (data, log)
    plan = {'schema': 'conditional-official-payload-plan-v1', 'review_status': 'independently_reviewed_for_activation',
            'consumer_workflow_path': h.CONSUMER_WORKFLOW, 'producer': {
                'identity': inputs[0]['expected']['origin']['identity'], 'workflow_path': h.PRODUCER_WORKFLOW,
                'workflow_id': 1, 'status_policy': 'allow_in_progress_byte_verification_only'},
            'storage_host_pattern': h.STORAGE_HOST_PATTERN, 'helper_sha256': 'd' * 64,
            'core_sha256': h.CORE_SHA256, 'input_files': [{'path': 'placeholder', 'sha256': 'e' * 64}],
            'stages': rows}
    return plan, inputs, bodies


class Closeable:
    def __init__(self, label, seen, fail=False):
        self.label, self.seen, self.fail = label, seen, fail
        self.closed = False
    def close(self):
        self.closed = True
        self.seen.append(self.label)
        if self.fail:
            raise RuntimeError('DO_NOT_PRINT signed secret')


class Response(Closeable):
    def __init__(self, data=b'', status=200, headers=None, label='response', seen=None):
        self.seen = [] if seen is None else seen
        super().__init__(label, self.seen)
        self.status, self.body = status, io.BytesIO(data)
        self.headers = Message()
        for key, value in (headers if headers is not None else [('Content-Length', str(len(data)))]):
            self.headers[key] = value
        self.fp = Closeable(label + '/fp', self.seen)
        self.fp.raw = Closeable(label + '/raw', self.seen)
        self.fp.raw._sock = Closeable(label + '/socket', self.seen)
        self.read_sizes = []
        self.read_hook = None
    def read(self, count):
        assert 0 < count <= h.CHUNK
        self.read_sizes.append(count)
        if self.read_hook:
            self.read_hook()
        return self.body.read(min(count, 113))
    read1 = read


class FakeHTTP:
    def __init__(self, plan, inputs, bodies):
        self.plan, self.inputs, self.bodies = plan, inputs, bodies
        self.opens, self.closes, self.responses, self.openers = [], [], [], []
        self.routes = {}
        self.counter = 0
        self.fail_open = None
        self.configure()
    def add_json(self, path, value):
        self.routes[h.API + path] = lambda: Response(h.canonical(value), seen=self.closes, label=path)
    def configure(self):
        old = self.plan['producer']['identity']
        repository = {'full_name': h.REPOSITORY, 'id': h.REPOSITORY_ID}
        def run(run_id, commit, workflow_id, path, status):
            return {'id': run_id, 'run_attempt': 1, 'head_sha': commit, 'event': 'push',
                    'repository': repository.copy(), 'head_repository': repository.copy(),
                    'path': path, 'workflow_id': workflow_id, 'status': status, 'conclusion': None,
                    'head_branch': 'review'}
        self.add_json(PREFIX + 'workflows/conditional-payload-verification.yml', {'id': 2, 'path': h.CONSUMER_WORKFLOW})
        self.add_json(PREFIX + 'workflows/conditional-geometry.yml', {'id': 1, 'path': h.PRODUCER_WORKFLOW})
        self.add_json(PREFIX + 'runs/456', run(456, 'b' * 40, 2, h.CONSUMER_WORKFLOW, 'in_progress'))
        self.add_json(PREFIX + 'runs/123', run(123, 'a' * 40, 1, h.PRODUCER_WORKFLOW, 'in_progress'))
        jobs, artifacts = [], []
        for item in self.inputs:
            origin, pin = item['expected']['origin'], item['pin']
            data, log = self.bodies[pin['stage_id']]
            jobs.append({'id': origin['producer_job_id'], 'name': origin['producer_job_name'], 'status': 'completed',
                         'conclusion': 'success', 'run_id': 123, 'run_attempt': 1, 'head_sha': 'a' * 40})
            artifacts.append({'id': origin['artifact_id'], 'name': origin['artifact_name'], 'expired': False,
                              'size_in_bytes': len(data), 'digest': 'sha256:' + h.sha(data),
                              'expires_at': pin['artifact_expires_at'], 'workflow_run': {'id': 123, 'head_sha': 'a' * 40,
                              'repository_id': h.REPOSITORY_ID, 'head_repository_id': h.REPOSITORY_ID}})
            for path, body in [(PREFIX + f'jobs/{origin["producer_job_id"]}/logs', log),
                               (PREFIX + f'artifacts/{origin["artifact_id"]}/zip', data)]:
                target = SECRET_URL + '&kind=' + path.split('/')[-2]
                self.routes[h.API + path] = lambda target=target: Response(status=302, headers=[('Location', target)], seen=self.closes)
                self.routes[target] = lambda body=body: Response(body, seen=self.closes)
        self.add_json(PREFIX + 'runs/123/attempts/1/jobs?per_page=100&page=1', {'total_count': len(jobs), 'jobs': jobs})
        self.add_json(PREFIX + 'runs/123/artifacts?per_page=100&page=1', {'total_count': len(artifacts), 'artifacts': artifacts})
    def mutate_json(self, path, operation):
        response = self.routes[h.API + path]()
        value = json.loads(response.body.getvalue())
        operation(value)
        self.add_json(path, value)
    def factory(self):
        outer = self
        class Opener(Closeable):
            def open(self, request, timeout):
                outer.opens.append((request.full_url, dict(request.header_items()), timeout))
                if outer.fail_open:
                    raise outer.fail_open
                response = outer.routes[request.full_url]()
                outer.responses.append(response)
                return response
        opener = Opener('opener' + str(len(self.openers)), self.closes)
        self.openers.append(opener)
        return opener


class Tests(unittest.TestCase):
    def setUp(self):
        patcher = mock.patch.object(socket, 'create_connection', side_effect=AssertionError('offline test network forbidden'))
        patcher.start(); self.addCleanup(patcher.stop)
        self.plan, self.inputs, self.bodies = plan_and_inputs()
        self.http = FakeHTTP(self.plan, self.inputs, self.bodies)
        self.env = environment()
        self.deadline = time.monotonic() + 100
    def run_verify(self):
        return h.verify_all(self.plan, self.inputs, v, plan_sha256='f' * 64, deadline=self.deadline,
                            environ=self.env, opener_factory=self.http.factory)
    def reject(self):
        with self.assertRaises(Exception):
            self.run_verify()
        self.assertTrue(all(opener.closed for opener in self.http.openers))
        self.assertTrue(all(response.closed for response in self.http.responses))
    def test_valid_two_stages_share_deadline_and_no_objects_written(self):
        self.plan, self.inputs, self.bodies = plan_and_inputs(2)
        self.http = FakeHTTP(self.plan, self.inputs, self.bodies)
        with mock.patch('builtins.open', side_effect=AssertionError('filesystem write/read during network verification')):
            result = self.run_verify()
        self.assertEqual(result['selected_stages'], list(h.STAGES))
        self.assertEqual(result['status'], 'BYTE_VERIFIED_ONLY')
        self.assertEqual(result['producer_status_observed'], 'in_progress')
        self.assertFalse(result['final_proof_claim'])
        self.assertEqual(result['object_payload_bytes_written'], 0)
        self.assertEqual(len(result['stages']), 2)
        self.assertTrue(all(response.closed for response in self.http.responses))
        for _, _, timeout in self.http.opens:
            self.assertLessEqual(timeout, 30)
        encoded = h.canonical(result)
        self.assertNotIn(b'DO_NOT_PRINT', encoded)
        self.assertNotIn(b'sig=', encoded)
    def test_token_only_exact_api_no_cookie_range_or_storage_auth(self):
        self.run_verify()
        for url, headers, _ in self.http.opens:
            lower = {key.lower(): value for key, value in headers.items()}
            self.assertNotIn('cookie', lower)
            self.assertNotIn('range', lower)
            if url.startswith(h.API + '/'):
                self.assertEqual(lower['authorization'], 'Bearer ' + SECRET_TOKEN)
            else:
                self.assertNotIn('authorization', lower)
                self.assertNotIn('x-github-api-version', lower)
                self.assertEqual(set(lower), {'user-agent', 'accept-encoding', 'connection'})
    def test_current_run_controls(self):
        for field, value in [('GITHUB_ACTIONS', 'false'), ('RUNNER_ENVIRONMENT', 'self-hosted'),
                             ('RUNNER_OS', 'Windows'), ('GITHUB_REPOSITORY', 'elsewhere/repo'),
                             ('GITHUB_EVENT_NAME', 'workflow_dispatch'), ('GITHUB_API_URL', 'https://evil.example'),
                             ('GITHUB_SERVER_URL', 'https://evil.example'), ('GITHUB_RUN_ID', '123'),
                             ('GITHUB_RUN_ATTEMPT', '2'), ('GITHUB_SHA', 'c' * 40),
                             ('GITHUB_WORKFLOW_REF', 'wrong'), ('GITHUB_WORKFLOW_SHA', 'a' * 40),
                             ('GITHUB_REF', 'refs/tags/test')]:
            with self.subTest(field=field):
                self.setUp(); self.env[field] = value; self.reject()
    def test_authenticated_run_wrong_provenance(self):
        for target in ('runs/456', 'runs/123'):
            for field, value in [('id', 111), ('run_attempt', 9), ('head_sha', 'c' * 40),
                                 ('event', 'pull_request'), ('path', 'wrong'), ('workflow_id', 99),
                                 ('repository', {'full_name': 'evil/repo'}), ('head_repository', {'full_name': 'evil/repo'})]:
                with self.subTest(target=target, field=field):
                    self.setUp(); self.http.mutate_json(PREFIX + target, lambda obj: obj.update({field: value})); self.reject()
    def test_current_run_must_be_running_and_producer_policy_explicit(self):
        for field, value in [('status', 'completed'), ('conclusion', 'success'), ('head_branch', 'main')]:
            with self.subTest(field=field):
                self.setUp(); self.http.mutate_json(PREFIX + 'runs/456', lambda obj: obj.update({field: value})); self.reject()
        self.setUp(); self.plan['producer']['status_policy'] = 'completed_only'; self.reject()
        self.setUp(); self.http.mutate_json(PREFIX + 'runs/123', lambda obj: obj.update(status='queued')); self.reject()
    def test_stage_job_controls(self):
        for field, value in [('id', 9), ('name', 'wrong'), ('status', 'in_progress'), ('conclusion', 'failure'),
                             ('run_id', 99), ('run_attempt', 2), ('head_sha', 'b' * 40)]:
            with self.subTest(field=field):
                self.setUp()
                self.http.mutate_json(PREFIX + 'runs/123/attempts/1/jobs?per_page=100&page=1',
                                      lambda obj: obj['jobs'][0].update({field: value}))
                self.reject()
    def test_artifact_controls_and_expiry(self):
        for field, value in [('id', 9), ('name', 'wrong'), ('expired', True), ('size_in_bytes', 1),
                             ('digest', 'sha256:' + '0' * 64), ('expires_at', '2031-01-01T00:00:00Z'),
                             ('workflow_run', {'id': 456, 'head_sha': 'a' * 40})]:
            with self.subTest(field=field):
                self.setUp()
                self.http.mutate_json(PREFIX + 'runs/123/artifacts?per_page=100&page=1',
                                      lambda obj: obj['artifacts'][0].update({field: value}))
                self.reject()
        self.setUp()
        self.inputs[0]['pin']['artifact_expires_at'] = '2020-01-01T00:00:00Z'
        self.http.mutate_json(PREFIX + 'runs/123/artifacts?per_page=100&page=1',
                              lambda obj: obj['artifacts'][0].update(expires_at='2020-01-01T00:00:00Z'))
        self.reject()
    def test_duplicate_collections_and_changed_total(self):
        for key, path in [('jobs', 'runs/123/attempts/1/jobs'), ('artifacts', 'runs/123/artifacts')]:
            with self.subTest(key=key):
                self.setUp()
                self.http.mutate_json(PREFIX + path + '?per_page=100&page=1',
                                      lambda obj: (obj[key].append(copy.deepcopy(obj[key][0])), obj.update(total_count=2)))
                self.reject()
        self.setUp()
        self.http.mutate_json(PREFIX + 'runs/123/artifacts?per_page=100&page=1', lambda obj: obj.update(total_count=2))
        self.reject()
    def test_log_whole_hash_and_timestamp_marker(self):
        origin = self.inputs[0]['expected']['origin']
        original = self.bodies[h.STAGES[0]][1]
        variations = [original + b'extra', original + original, original.split(b' ', 1)[1],
                      original.replace(b'"artifact_id": "2"', b'"artifact_id": "99"')]
        for index, log in enumerate(variations):
            with self.subTest(index=index):
                self.setUp()
                if index:
                    self.inputs[0]['expected']['origin']['producer_job_log_sha256'] = h.sha(log)
                target = SECRET_URL + '&kind=3'
                self.http.routes[target] = lambda log=log: Response(log, seen=self.http.closes)
                self.reject()
    def test_bad_storage_urls_and_double_redirect(self):
        urls = ['http://productionresultssa2.blob.core.windows.net/a?x=1', 'https://evil.example/a?x=1',
                'https://productionresultssa2.blob.core.windows.net.evil.example/a?x=1',
                'https://productionresultssa2.blob.core.windows.net:444/a?x=1',
                'https://x@productionresultssa2.blob.core.windows.net/a?x=1',
                'https://productionresultssa2.blob.core.windows.net/a?x=1#frag',
                'https://productionresultssa2.blob.core.windows.net/a',
                'https://PRODUCTIONRESULTSSA2.blob.core.windows.net/a?x=1',
                'https://productionresultssa2.blob.core.windows.net\\@evil.example/a?x=1']
        for url in urls:
            with self.subTest(url=url):
                self.setUp()
                self.http.routes[h.API + PREFIX + 'jobs/3/logs'] = lambda url=url: Response(status=302, headers=[('Location', url)], seen=self.http.closes)
                self.reject()
                self.assertTrue(all(url.startswith(h.API + '/') for url, _, _ in self.http.opens))
        self.setUp()
        self.http.routes[SECRET_URL + '&kind=3'] = lambda: Response(status=302, headers=[('Location', SECRET_URL)], seen=self.http.closes)
        self.reject()
        self.assertEqual(sum(not url.startswith(h.API + '/') for url, _, _ in self.http.opens), 1)
    def test_metadata_redirect_and_api_status_rejected(self):
        for status in (206, 301, 302, 303, 307, 308, 401, 404, 500):
            with self.subTest(status=status):
                self.setUp()
                path = h.API + PREFIX + 'workflows/conditional-payload-verification.yml'
                self.http.routes[path] = lambda status=status: Response(status=status, headers=[('Location', SECRET_URL)], seen=self.http.closes)
                self.reject()
                self.assertEqual(len(self.http.opens), 1)
    def test_storage_framing_negative_cases(self):
        data = self.bodies[h.STAGES[0]][0]
        cases = [([], 200), ([('Content-Length', str(len(data) - 1))], 200),
                 ([('Content-Length', str(len(data))), ('Content-Length', str(len(data)))], 200),
                 ([('Content-Length', str(len(data))), ('Transfer-Encoding', 'chunked')], 200),
                 ([('Content-Length', str(len(data))), ('Content-Encoding', 'gzip')], 200),
                 ([('Content-Length', str(len(data))), ('Content-Range', 'bytes 0-1/2')], 200),
                 ([('Content-Length', str(len(data)))], 206), ([('Transfer-Encoding', 'chunked')], 200)]
        for headers, status in cases:
            with self.subTest(headers=headers, status=status):
                self.setUp()
                self.http.routes[SECRET_URL + '&kind=2'] = lambda headers=headers, status=status: Response(data, status=status, headers=headers, seen=self.http.closes)
                self.reject()
    def test_truncated_trailing_corrupt_payload_no_result(self):
        original = self.bodies[h.STAGES[0]][0]
        for data in (original[:-1], original + b'x', b'X' + original[1:]):
            with self.subTest(size=len(data)):
                self.setUp()
                self.http.routes[SECRET_URL + '&kind=2'] = lambda data=data: Response(data, headers=[('Content-Length', str(len(original)))], seen=self.http.closes)
                self.reject()
    def test_response_failure_closes_every_nested_handle_and_both_openers(self):
        def broken():
            response = Response(self.bodies[h.STAGES[0]][0], seen=self.http.closes)
            response.fail = True
            response.fp.fail = True
            response.fp.raw.fail = True
            return response
        self.http.routes[SECRET_URL + '&kind=2'] = broken
        self.reject()
        response = self.http.responses[-1]
        self.assertTrue(response.fp.raw._sock.closed)
        self.assertTrue(response.fp.closed)
    def test_timeout_and_cleanup_deadline_no_receipt(self):
        self.deadline = time.monotonic() - 1
        self.reject()
        self.assertEqual(self.http.opens, [])
        self.setUp()
        self.http.fail_open = TimeoutError(SECRET_URL)
        self.reject()
        self.assertEqual(len(self.http.opens), 1)
        self.setUp()
        def slow():
            response = Response(self.bodies[h.STAGES[0]][0], seen=self.http.closes)
            def expire():
                self.deadline = 0
                raise TimeoutError(SECRET_URL)
            response.read_hook = expire
            return response
        self.http.routes[SECRET_URL + '&kind=2'] = slow
        self.reject()
    def test_metadata_caps_duplicate_json_and_log_cap(self):
        response = Response(b'12345', headers=[])
        stream = h.BoundedResponse(response, 4, self.deadline)
        with self.assertRaises(h.Rejected): stream.all()
        with self.assertRaises(h.Rejected): h.parse_json(b'{"a":1,"a":2}')
        with self.assertRaises(h.Rejected): h.parse_json(b'{"a":NaN}')
        with self.assertRaises(h.Rejected): h.BoundedResponse(Response(headers=[('Content-Length', str(h.MAX_LOG + 1))]), h.MAX_LOG, self.deadline)
    def test_no_redirect_handler_and_tls_proxy_defaults(self):
        self.assertIsNone(h.NoRedirect().redirect_request(None, None, None, None, None, None))
        opener = h.make_opener()
        try:
            self.assertFalse(any(isinstance(x, urllib.request.HTTPCookieProcessor) for x in opener.handlers))
            tls = next(x for x in opener.handlers if isinstance(x, urllib.request.HTTPSHandler))
            self.assertTrue(tls._context.check_hostname)
            self.assertEqual(tls._context.verify_mode, ssl.CERT_REQUIRED)
        finally: opener.close()
        with mock.patch.dict(os.environ, {'HTTPS_PROXY': 'http://proxy.example:8123', 'NO_PROXY': 'internal.example'}, clear=True):
            opener = h.make_opener()
            proxy = next(x for x in opener.handlers if isinstance(x, urllib.request.ProxyHandler))
            self.assertEqual(proxy.proxies['https'], 'http://proxy.example:8123')
            self.assertEqual(os.environ['NO_PROXY'], 'internal.example')
            opener.close()
    def test_pending_plan_and_wrong_stage_list_rejected_before_network(self):
        for key, value in [('review_status', 'pending_independent_review'), ('storage_host_pattern', '.*'),
                           ('core_sha256', '0' * 64), ('stages', []), ('stages', self.plan['stages'] * 2)]:
            with self.subTest(key=key):
                changed = copy.deepcopy(self.plan); changed[key] = value
                with self.assertRaises(h.Rejected): h.validate_plan(changed)
        self.assertEqual(self.http.opens, [])
    def test_bounded_reads_and_http_eof(self):
        result = self.run_verify()
        self.assertTrue(all(n <= h.CHUNK for response in self.http.responses for n in response.read_sizes))
        response = Response(b'abc', headers=[('Content-Length', '5')])
        with self.assertRaises(h.Rejected): h.BoundedResponse(response, 10, self.deadline).all()
        with self.assertRaises(h.Rejected): h.BoundedResponse(Response(), 10, self.deadline).read(h.CHUNK + 1)
    def test_atomic_receipt_no_clobber_and_failed_fsync_leaves_no_marker(self):
        with tempfile.TemporaryDirectory() as directory:
            target = Path(directory) / 'result.json'
            h.write_receipt(target, {'status': 'BYTE_VERIFIED_ONLY'}, self.deadline)
            self.assertEqual(json.loads(target.read_text())['status'], 'BYTE_VERIFIED_ONLY')
            with self.assertRaises(h.Rejected): h.write_receipt(target, {}, self.deadline)
            target.unlink()
            with mock.patch.object(os, 'fsync', side_effect=OSError('failure')):
                with self.assertRaises(OSError): h.write_receipt(target, {}, self.deadline)
            self.assertEqual(list(Path(directory).iterdir()), [])
            calls = [None, OSError('directory fsync failure')]
            with mock.patch.object(os, 'fsync', side_effect=calls):
                with self.assertRaises(OSError): h.write_receipt(target, {}, self.deadline)
            self.assertEqual(list(Path(directory).iterdir()), [])
            with self.assertRaises(h.Rejected): h.write_receipt(target, {}, time.monotonic() - 1)
            self.assertFalse(target.exists())
    def test_hardening_exact_limits_and_single_absolute_timer(self):
        with mock.patch.object(h.resource, 'setrlimit') as limit, mock.patch.object(os, 'sched_getaffinity', side_effect=[{2, 3}, {2}]), \
             mock.patch.object(os, 'sched_setaffinity') as affinity, mock.patch.object(signal, 'signal'), \
             mock.patch.object(signal, 'setitimer') as timer:
            deadline = h.harden_process(1740)
        self.assertIn(mock.call(h.resource.RLIMIT_AS, (1024**3, 1024**3)), limit.call_args_list)
        self.assertIn(mock.call(h.resource.RLIMIT_CPU, (600, 600)), limit.call_args_list)
        affinity.assert_called_once_with(0, {2})
        timer.assert_called_once()
        self.assertLessEqual(timer.call_args.args[1], 1740)
        self.assertGreater(deadline, time.monotonic())
    def test_timeout_during_cleanup_rejected(self):
        api = h.OfficialAPI(SECRET_TOKEN, self.deadline, opener_factory=self.http.factory)
        original = h.remaining
        closed = {'value': False}
        path = PREFIX + 'jobs/3/logs'
        response = Response(b'', seen=self.http.closes)
        def finish():
            response.closed = True; closed['value'] = True
        response.close = finish
        self.http.routes[h.API + path] = lambda: response
        def time_check(deadline):
            if closed['value']:
                raise h.Rejected('expired during cleanup')
            return original(deadline)
        with mock.patch.object(h, 'remaining', side_effect=time_check):
            with self.assertRaises(h.Rejected):
                with api.response(path, 100) as source:
                    source.all()
        self.assertTrue(all(opener.closed for opener in self.http.openers))
        self.assertTrue(response.fp.raw._sock.closed)

    def test_http_error_wrapper_redirect_has_complete_nested_cleanup(self):
        api = h.OfficialAPI(SECRET_TOKEN, self.deadline, opener_factory=self.http.factory)
        inner = Response(status=302, headers=[('Location', SECRET_URL)], seen=self.http.closes)
        wrapped = urllib.error.HTTPError(h.API + PREFIX + 'jobs/3/logs', 302, 'Found', inner.headers, inner)
        handles = h.resources_of(wrapped)
        self.assertIn(inner.fp.raw._sock, handles)
        h.close_all(handles)
        self.assertTrue(inner.fp.raw._sock.closed)
        self.assertTrue(inner.fp.raw.closed)
        self.assertTrue(inner.fp.closed)

    def test_storage_open_failure_still_closes_api_and_both_openers(self):
        def fail():
            raise TimeoutError(SECRET_URL)
        self.http.routes[SECRET_URL + '&kind=3'] = fail
        self.reject()
        self.assertTrue(all(response.fp.raw._sock.closed for response in self.http.responses))

    def test_main_atomic_success_and_second_stage_failure_no_success_file(self):
        for fail_second in (False, True):
            with self.subTest(fail_second=fail_second), tempfile.TemporaryDirectory() as directory:
                self.plan, self.inputs, self.bodies = plan_and_inputs(2)
                self.http = FakeHTTP(self.plan, self.inputs, self.bodies)
                if fail_second:
                    self.http.routes[SECRET_URL + '&kind=12'] = lambda: Response(b'bad', seen=self.http.closes)
                target = Path(directory) / 'receipt.json'
                stdout, stderr = io.StringIO(), io.StringIO()
                with mock.patch.object(h, 'harden_process', return_value=self.deadline), \
                     mock.patch.object(h, 'load_inputs', return_value=(self.plan, self.inputs, v)), \
                     mock.patch.object(h, 'make_opener', side_effect=self.http.factory), \
                     mock.patch.dict(os.environ, self.env, clear=True), \
                     mock.patch.object(signal, 'setitimer'), \
                     mock.patch.object(h.sys, 'stdout', stdout), mock.patch.object(h.sys, 'stderr', stderr):
                    status = h.main(['--plan', 'unused', '--plan-sha256', 'f' * 64, '--core', 'unused',
                                     '--receipt', str(target), '--seconds', '1740'])
                self.assertEqual(status, 1 if fail_second else 0)
                self.assertEqual(target.exists(), not fail_second)
                self.assertNotIn('DO_NOT_PRINT', stdout.getvalue() + stderr.getvalue())
                self.assertNotIn('sig=', stdout.getvalue() + stderr.getvalue())
                self.assertEqual(stdout.getvalue(), '')
                self.assertTrue(all(response.fp.raw._sock.closed for response in self.http.responses))
                if fail_second:
                    self.assertEqual(list(Path(directory).iterdir()), [])
                else:
                    self.assertEqual(json.loads(target.read_text())['selected_stages'], list(h.STAGES))

    def test_errors_after_receipt_publication_remove_own_marker(self):
        with tempfile.TemporaryDirectory() as directory:
            target = Path(directory) / 'receipt.json'
            original = h.write_receipt
            def write_then_fail(*args):
                original(*args)
                raise RuntimeError(SECRET_URL)
            with mock.patch.object(h, 'harden_process', return_value=self.deadline), \
                 mock.patch.object(h, 'load_inputs', return_value=(self.plan, self.inputs, v)), \
                 mock.patch.object(h, 'make_opener', side_effect=self.http.factory), \
                 mock.patch.dict(os.environ, self.env, clear=True), \
                 mock.patch.object(signal, 'setitimer'), mock.patch.object(h.sys, 'stderr', io.StringIO()), \
                 mock.patch.object(h, 'write_receipt', side_effect=write_then_fail):
                status = h.main(['--plan', 'unused', '--plan-sha256', 'f' * 64, '--core', 'unused',
                                 '--receipt', str(target)])
            self.assertEqual(status, 1)
            self.assertEqual(list(Path(directory).iterdir()), [])

    def test_failure_diagnostics_are_static_and_cli_secrets_are_suppressed(self):
        self.assertEqual(h.failure_label(h.Rejected('unapproved signed redirect')), 'unapproved signed redirect')
        for error in (h.Rejected(SECRET_URL), RuntimeError(SECRET_URL), v.Rejected(SECRET_URL)):
            self.assertEqual(h.failure_label(error), 'verification rejected')
        stderr = io.StringIO()
        with mock.patch.object(h.sys, 'stderr', stderr):
            with self.assertRaises(SystemExit):
                h.main(['--url', SECRET_URL])
        self.assertNotIn('DO_NOT_PRINT', stderr.getvalue())
        self.assertNotIn('sig=', stderr.getvalue())
        self.assertIn('phase=arguments', stderr.getvalue())

    def test_http_error_302_is_closed_before_token_free_redirect(self):
        inner = Response(status=302, headers=[('Location', SECRET_URL + '&kind=3')], seen=self.http.closes)
        wrapped = urllib.error.HTTPError(h.API + PREFIX + 'jobs/3/logs', 302, 'Found', inner.headers, inner)
        def raise_redirect():
            raise wrapped
        self.http.routes[h.API + PREFIX + 'jobs/3/logs'] = raise_redirect
        result = self.run_verify()
        self.assertEqual(result['status'], 'BYTE_VERIFIED_ONLY')
        self.assertTrue(inner.fp.raw._sock.closed)

    def test_f2_only_plan_passes_and_reversed_duplicate_lists_fail(self):
        self.plan, self.inputs, self.bodies = plan_and_inputs(2)
        both = copy.deepcopy(self.plan['stages'])
        self.inputs = self.inputs[1:]
        self.plan['stages'] = self.plan['stages'][1:]
        h.validate_plan(self.plan)
        self.http = FakeHTTP(self.plan, self.inputs, self.bodies)
        result = self.run_verify()
        self.assertEqual(result['selected_stages'], ['F2_period_hierarchy'])
        self.assertFalse(any('/artifacts/2/zip' in url for url, _, _ in self.http.opens))
        for rows in (list(reversed(both)), [both[0], both[0]], [both[1], both[1]]):
            changed = copy.deepcopy(self.plan); changed['stages'] = rows
            with self.assertRaises(h.Rejected): h.validate_plan(changed)

    def test_exact_numeric_repository_ids_on_both_runs_and_artifact(self):
        for run_path in ('runs/123', 'runs/456'):
            for field in ('repository', 'head_repository'):
                for wrong in (1407290934, str(h.REPOSITORY_ID), None):
                    with self.subTest(run_path=run_path, field=field, wrong=wrong):
                        self.setUp()
                        self.http.mutate_json(PREFIX + run_path, lambda obj: obj[field].update(id=wrong))
                        self.reject()
        for field in ('repository_id', 'head_repository_id'):
            for wrong in (1407290934, str(h.REPOSITORY_ID), None):
                with self.subTest(field=field, wrong=wrong):
                    self.setUp()
                    self.http.mutate_json(PREFIX + 'runs/123/artifacts?per_page=100&page=1',
                                          lambda obj: obj['artifacts'][0]['workflow_run'].update({field: wrong}))
                    self.reject()


class InputTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.plan, self.inputs, _ = plan_and_inputs()
        self.deadline = time.monotonic() + 100
        files = {
            'ci/verify_official_payload.py': Path(h.__file__).read_bytes(),
            'ci/stream_verify.py': Path(v.__file__).read_bytes(),
            h.CONSUMER_WORKFLOW: b'# workflow fixture\n',
            self.inputs[0]['pin']['expectation_file']: v.canonical_json(self.inputs[0]['expected']),
            self.inputs[0]['pin']['certificate_file']: b'{}\n',
        }
        for name, data in files.items():
            path = self.root / name; path.parent.mkdir(parents=True, exist_ok=True); path.write_bytes(data)
        self.plan['helper_sha256'] = h.sha(files['ci/verify_official_payload.py'])
        self.plan['input_files'] = [{'path': name, 'sha256': h.sha(data)} for name, data in sorted(files.items()) if name != h.CONSUMER_WORKFLOW]
        self.plan_path = self.root / 'payload-verification-plan.json'
        self.seal()
    def tearDown(self): self.tmp.cleanup()
    def seal(self):
        data = h.canonical(self.plan); self.plan_path.write_bytes(data); self.plan_hash = h.sha(data)
    def load(self):
        with mock.patch.object(h, '__file__', str(self.root / 'ci/verify_official_payload.py')):
            return h.load_inputs(self.plan_path, self.plan_hash, self.root / 'ci/stream_verify.py', self.deadline)
    def test_exact_distribution_and_pins_pass(self):
        plan, inputs, core = self.load()
        self.assertEqual(inputs[0]['expected']['origin']['stage_id'], h.STAGES[0])
        self.assertEqual(h.sha((self.root / 'ci/stream_verify.py').read_bytes()), h.CORE_SHA256)
    def test_extra_missing_hardlinked_and_symlink_inputs_rejected(self):
        for variant in ('extra_file', 'empty_dir', 'missing', 'hardlink', 'symlink'):
            with self.subTest(variant=variant):
                path = self.root / 'EXTRA'
                target = self.root / self.inputs[0]['pin']['certificate_file']
                saved = target.read_bytes()
                if variant == 'extra_file': path.write_text('extra')
                if variant == 'empty_dir': path.mkdir()
                if variant == 'missing': target.unlink()
                if variant == 'hardlink': os.link(target, path)
                if variant == 'symlink': target.unlink(); target.symlink_to(self.root / 'ci/stream_verify.py')
                with self.assertRaises(h.Rejected): self.load()
                if path.is_dir(): path.rmdir()
                elif path.exists(): path.unlink()
                if target.is_symlink(): target.unlink()
                if not target.exists(): target.write_bytes(saved)
    def test_wrong_plan_core_helper_and_certificate_pins(self):
        with self.assertRaises(h.Rejected):
            h.load_inputs(self.plan_path, '0' * 64, self.root / 'ci/stream_verify.py', self.deadline)
        for field in ('helper_sha256', 'core_sha256'):
            with self.subTest(field=field):
                original = self.plan[field]; self.plan[field] = '0' * 64; self.seal()
                with self.assertRaises(h.Rejected): self.load()
                self.plan[field] = original; self.seal()
        target = self.root / self.inputs[0]['pin']['certificate_file']; target.write_text('{"changed":true}\n')
        with self.assertRaises(h.Rejected): self.load()
    def test_duplicate_input_missing_pin_and_escape_rejected(self):
        original = copy.deepcopy(self.plan)
        for mutate in (lambda p: p['input_files'].append(p['input_files'][0]),
                       lambda p: p['input_files'].pop(),
                       lambda p: p['input_files'][0].update(path='../escape'),
                       lambda p: p['input_files'].append({'path': h.CONSUMER_WORKFLOW, 'sha256': 'a' * 64})):
            self.plan = copy.deepcopy(original); mutate(self.plan); self.seal()
            with self.assertRaises(h.Rejected): self.load()
    def test_pending_plan_refuses_before_core_loading(self):
        self.plan['review_status'] = 'pending_independent_review'; self.seal()
        with mock.patch.object(h, 'make_opener', side_effect=AssertionError('network forbidden')):
            with self.assertRaisesRegex(h.Rejected, 'inactive'):
                self.load()


if __name__ == '__main__':
    # An accidental networking regression fails immediately. All HTTP is fake.
    with mock.patch.object(socket, 'create_connection', side_effect=AssertionError('offline test network forbidden')):
        unittest.main(verbosity=2)
