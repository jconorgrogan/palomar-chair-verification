#!/usr/bin/env python3
"""C087 exact historical acquisition extension; no native execution or proof claim.

Context/membership/descriptor, certificate orchestration and a quota gate are new. The
reviewed downloader's request/retry/redirect/ZIP/extraction/disk/inode/age code is
imported byte-identically. No second transfer implementation is provided.
"""
from __future__ import annotations
import argparse
import copy
import hashlib
import json
import math
import os
import re
from pathlib import Path
import shutil
import stat
import sys
import time
import urllib.error
import urllib.parse
from datetime import datetime, timezone

HERE = Path(__file__).resolve().parent
FROZEN = HERE.parent / 'frozen_downloader' / 'ci'
FROZEN_FILES = {
 'historical_acquisition.py':'b33959f460cb73992dfbdd86a5ab7a073f64277e2b0c28b135e640fa5a94f3ee',
 'historical_acquisition_pins.json':'427f4a4b8a6c1b324650703979b833127ce729cc8668a4ccfddbca430c2df6af',
 'origin_transport.py':'c5ba140113b98460f8267f55fcdad098c391e4918fdc3a9e8e2f90e8ff5b110b',
 'fresh_stage.py':'9085c9eea092c270fbd6952834839103c66519a7b4716fe09147001c7d96355d',
 'continuation_policy.py':'1759e1fc5587ec2b5462604f9f7a16cebaefdb85f153d563514b36b18d314be2',
 'ci_transport.py':'0e17698024da89562d654978436b707a140fef81c3463a8b0841af8de2355c95',
}
def verify_frozen_directory(directory):
    """Parent must supply a clean read-only checkout; reject every unlisted cache."""
    if {path.name for path in directory.iterdir()} != set(FROZEN_FILES):
        raise RuntimeError('frozen downloader must contain exactly the six source/spec files; no bytecode')
    for name, digest in FROZEN_FILES.items():
        path = directory / name
        for parent in (path, *path.parents):
            if parent.is_symlink(): raise RuntimeError('frozen downloader symlink forbidden')
        info = path.lstat()
        if not stat.S_ISREG(info.st_mode) or info.st_nlink != 1 or hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            raise RuntimeError('frozen downloader pin/type mismatch')

if sys.pycache_prefix is not None:
    raise RuntimeError('alternate bytecode cache root forbidden')
sys.dont_write_bytecode = True
verify_frozen_directory(FROZEN)
sys.path.insert(0, str(FROZEN))
import historical_acquisition as h
if Path(h.__file__).resolve() != FROZEN / 'historical_acquisition.py':
    raise RuntimeError('frozen downloader import shadowing')
f, ot = h.f, h.ot
SPEC_SHA256 = '9c77059b0a48a300e6ae9be0c826812057d0305a61c444736c246389d52b9b80'
LATEST = 'LatestSuccessorOrigin'
OUTER = ('OldOrigin', 'PriorSuccessorOrigin', LATEST)
INTERNAL = ('OldOrigin', 'CurrentOrigin', LATEST)
TO_INTERNAL = {'OldOrigin':'OldOrigin', 'PriorSuccessorOrigin':'CurrentOrigin', LATEST:LATEST}
TO_OUTER = {value:key for key,value in TO_INTERNAL.items()}
TO_NATIVE = {'OldOrigin':'OldOrigin', 'PriorSuccessorOrigin':'PriorSuccessorOrigin', LATEST:'CurrentOrigin'}
LATEST_RUN = '38978663241'
LATEST_PIPELINE = 'bc3f977237bee905dafb4f13eeb6564a4a338b42'
LATEST_CONTRACT = '2848fad58bf59da1958c7e1632e841c1bae78f22ab728b1098a9426977aef334'
LATEST_IDENTITY = '4f8be12f1e9e851917e69e60957136c5e3e60ac5e1e00284ce1111692b4da3a5'
HISTORICAL_GLOBAL = 3009576960
HISTORICAL_SELECTED = 3008552960
OMITTED_RESERVE = 1024000
PAYLOAD_KEYS = {'archive_bytes','archive_sha256','raw_descriptor_sha256','receipt_sha256','identity_sha256'}


def load_spec():
    path = HERE / 'C087_ACQUISITION_SPEC.json'
    f.no_symlink_path(path)
    raw = path.read_bytes()
    f.need(f.sha(raw) == SPEC_SHA256, 'C087 fixed specification changed')
    return f.parse_json(raw)


def utc_now(transport):
    transport._check_age()
    return transport.now().strftime('%Y-%m-%dT%H:%M:%SZ')


class QuotaPacedOpener:
    """Pace the same opener; never transfer, redirect, retry or parse body bytes.

    The frozen metadata call has already started its 60-second attempt and
    180-second aggregate guards before invoking open(). All pacing is charged
    inside those unchanged guards. Storage hops carry no token/quota authority.
    """
    MIN_INTERVAL = 3.7
    RESET_SAFETY = 2.0
    NETWORK_RESERVE = 1.0
    LIMIT = 1000
    HEADER_NAMES = ('X-RateLimit-Limit', 'X-RateLimit-Remaining',
                    'X-RateLimit-Used', 'X-RateLimit-Reset',
                    'X-RateLimit-Resource', 'Date')

    def __init__(self, transport, opener):
        self.transport, self.opener = transport, opener
        self.last_clock = self.last_start = None
        self.reset_epoch = self.reset_monotonic = self.server_date = None
        self.remote_remaining = self.local_remaining = None

    def _clock(self):
        value = time.monotonic()
        f.need(type(value) in (int,float) and math.isfinite(value) and
               (self.last_clock is None or value >= self.last_clock),
               'invalid quota monotonic clock')
        self.last_clock = value
        return value

    @staticmethod
    def _close_rejected(response):
        try: response.close()
        except Exception: raise f.Rejected('quota response cleanup failed') from None

    @classmethod
    def _headers(cls, response):
        headers = response.headers
        f.need(callable(getattr(headers, 'get_all', None)), 'quota headers unavailable')
        values = {}
        for name in cls.HEADER_NAMES:
            rows = headers.get_all(name)
            f.need(type(rows) is list and len(rows) == 1 and type(rows[0]) is str and
                   0 < len(rows[0]) <= 64 and not any(ord(c) < 32 or ord(c) == 127 for c in rows[0]),
                   'quota header missing, duplicated or malformed')
            values[name] = rows[0]
        for name in cls.HEADER_NAMES[:4]:
            f.need(re.fullmatch(r'0|[1-9][0-9]{0,9}', values[name]) is not None,
                   'invalid numeric quota header')
            values[name] = int(values[name])
        limit, remaining, used, reset = (values[k] for k in cls.HEADER_NAMES[:4])
        f.need(limit == cls.LIMIT and 0 <= remaining < limit and used + remaining == limit and
               values['X-RateLimit-Resource'] == 'core', 'conflicting or unexpected quota headers')
        try:
            date = datetime.strptime(values['Date'], '%a, %d %b %Y %H:%M:%S GMT').replace(tzinfo=timezone.utc)
            f.need(date.strftime('%a, %d %b %Y %H:%M:%S GMT') == values['Date'], 'invalid quota Date header')
        except (ValueError, OverflowError):
            raise f.Rejected('invalid quota Date header') from None
        epoch = int(date.timestamp())
        f.need(0 <= reset - epoch <= 3600, 'quota reset outside bounded server window')
        return remaining, reset, epoch

    def _observe(self, response):
        try:
            remaining, reset, date = self._headers(response)
            f.need(remaining > 0, 'authenticated core quota exhausted; no further request')
            now = self._clock(); self.transport._check_age()
            reset_at = now + (reset - date) + self.RESET_SAFETY
            if self.reset_epoch is not None:
                f.need(date >= self.server_date and reset >= self.reset_epoch,
                       'backward authenticated quota clock or reset')
                if reset == self.reset_epoch:
                    f.need(remaining <= self.remote_remaining, 'quota remaining increased within one window')
                    remaining = min(remaining, self.local_remaining)
                    reset_at = min(reset_at, self.reset_monotonic)
                else:
                    f.need(date >= self.reset_epoch, 'quota reset advanced before its authenticated boundary')
            self.remote_remaining = remaining
            self.local_remaining = remaining
            self.reset_epoch, self.reset_monotonic, self.server_date = reset, reset_at, date
        except f.Rejected:
            raise
        except (AttributeError, TypeError, ValueError, OverflowError):
            raise f.Rejected('invalid authenticated quota metadata') from None

    def _pace(self, timeout):
        f.need(type(timeout) in (int,float) and math.isfinite(timeout) and timeout > 0,
               'invalid original request timeout')
        now = self._clock(); self.transport._check_age()
        # Round outward additions/subtractions toward less available budget.
        # Exact-rational elapsed + returned timeout cannot exceed input timeout.
        deadline = min(math.nextafter(now + timeout, -math.inf), self.transport.deadline_monotonic,
                       self.transport.age_deadline_monotonic)
        due = now if self.last_start is None else max(now, math.nextafter(self.last_start + self.MIN_INTERVAL, math.inf))
        if self.reset_monotonic is not None:
            until_reset = max(0.0, self.reset_monotonic - now)
            # Leave enough time for every remaining slot, without probing an
            # exhausted bucket or granting itself any new quota.
            f.need(self.local_remaining > 0, 'authenticated core quota exhausted; no further request')
            interval = math.nextafter(until_reset / self.local_remaining, math.inf)
            due = max(due, math.nextafter(now + interval, math.inf))
        f.need(due + self.NETWORK_RESERVE < deadline,
               'quota pacing cannot fit the unchanged request deadline')
        # Sleep only toward one fixed target. Never recreate attempt/age budgets.
        while now < due:
            self.transport._check_age()
            deadline = min(deadline, self.transport.deadline_monotonic, self.transport.age_deadline_monotonic)
            f.need(due + self.NETWORK_RESERVE < deadline, 'quota wait would exceed tightened deadline')
            delay = min(1.0, due - now)
            time.sleep(delay)
            observed = self._clock()
            f.need(observed > now, 'quota sleep made no monotonic progress')
            now = observed; self.transport._check_age()
            f.need(now + self.NETWORK_RESERVE < deadline, 'quota pacing request deadline exceeded')
        self.transport._check_age()
        self.last_start = self._clock()
        if self.local_remaining is not None:
            self.local_remaining = max(0, self.local_remaining - 1)
        deadline = min(deadline, self.transport.deadline_monotonic, self.transport.age_deadline_monotonic)
        left = min(timeout, math.nextafter(deadline - self.last_start, -math.inf))
        f.need(left > self.NETWORK_RESERVE, 'quota pacing exhausted original request timeout')
        return left

    def open(self, request, timeout):
        # Recheck authority at the adapter boundary; never infer it from headers.
        self.transport._safe_redirect(request.full_url)
        parsed = urllib.parse.urlsplit(request.full_url)
        authorization = request.get_header('Authorization')
        if parsed.hostname != 'api.github.com':
            f.need(authorization is None, 'credentials on a storage request forbidden')
            return self.opener.open(request, timeout=timeout)
        f.need(request.get_method() == 'GET' and
               request.full_url.startswith(ot.API + '/repos/' + ot.REPOSITORY + '/') and
               authorization == 'Bearer ' + self.transport.current.token,
               'quota source must be the authenticated approved repository')
        left = self._pace(timeout)
        try:
            response = self.opener.open(request, timeout=left)
        except urllib.error.HTTPError as error:
            if error.code in (403,429):
                self._close_rejected(error)
                raise f.Rejected('authenticated API quota or authorization failure; no retry') from None
            try: self._observe(error)
            except Exception:
                self._close_rejected(error)
                raise
            raise  # Frozen status/redirect/retry policy remains the sole policy.
        try:
            self._observe(response)
        except Exception:
            self._close_rejected(response)
            raise
        return response


class C087Acquisition(h.HistoricalAcquisition):
    def __init__(self, token, root, *, deadline_monotonic, session_nonce, opener=None, now=None):
        f.need(type(deadline_monotonic) is float and math.isfinite(deadline_monotonic),
               'exact finite parent absolute monotonic float required')
        f.need(type(session_nonce) is str and f.SHA256.fullmatch(session_nonce), 'parent session nonce must be64 lowercase hex')
        # Real frozen historical constructor: validates the original/prior pair.
        # No live CurrentOriginTransport is fabricated or invoked.
        super().__init__(token, root, deadline_monotonic=deadline_monotonic, opener=opener, now=now)
        self.opener = QuotaPacedOpener(self, self.opener)
        self.parent_deadline_monotonic = deadline_monotonic
        self.session_nonce = session_nonce
        self.spec = load_spec()
        latest = copy.deepcopy(self.spec['latest_context'])
        # Expectations are not claims that prepare bytes were already acquired.
        latest['prepare']['identity_sha256'] = latest['expected_identity_sha256']
        latest['prepare']['inventory_sha256'] = latest['expected_inventory_sha256']
        self.contexts[LATEST] = latest
        self._validate_c087_spec()
        self.rows = {row['stage_id']:copy.deepcopy(row) for row in self.spec['stages']}
        self.historical_ids = [row['stage_id'] for row in self.spec['stages'] if row['origin'] != LATEST]
        self.latest_ids = [row['stage_id'] for row in self.spec['stages'] if row['origin'] == LATEST]
        # Retain omitted build_054 in the ledger; never reset by origin.
        self.raw_bytes = OMITTED_RESERVE
        self._check_age()

    def _validate_c087_spec(self):
        s = self.spec
        f.need(s['schema'] == 'c087-fixed-historical-acquisition-spec-v1' and
               s['repository'] == ot.REPOSITORY and s['repository_id'] == ot.REPOSITORY_ID and
               s['original_deadline_utc'] == h.DEADLINE, 'C087 repository/deadline mismatch')
        f.need(s['scope']['target_stage'] == 'build_087' and s['scope']['module_count'] == 6218 and
               [r['stage_id'] for r in s['stages']] == s['scope']['predecessor_stage_ids'] and
               len(s['stages']) == len({r['stage_id'] for r in s['stages']}) == 85, 'exact ordered85 scope required')
        f.need({origin:sum(r['origin'] == origin for r in s['stages']) for origin in OUTER} ==
               {'OldOrigin':37,'PriorSuccessorOrigin':10,LATEST:38}, 'C087 origin membership changed')
        global_rows = s['historical_global_stages']
        f.need(len(global_rows) == 48 and sum(r['pin']['archive_bytes'] for r in global_rows) == HISTORICAL_GLOBAL and
               sum(r['pin']['archive_bytes'] for r in s['stages'] if r['origin'] != LATEST) == HISTORICAL_SELECTED and
               HISTORICAL_GLOBAL - HISTORICAL_SELECTED == OMITTED_RESERVE, 'global48 ledger must not reset to47')
        f.need(s['accounting'] == {'historical_global_raw_bytes':HISTORICAL_GLOBAL,
               'historical_selected_raw_bytes':HISTORICAL_SELECTED,'historical_unrestored_raw_bytes':OMITTED_RESERVE,
               'latest_zip_bytes':84450964,'latest_raw_bytes':None,'aggregate_cap_bytes':h.RAW_CAP}, 'C087 accounting changed')
        original_rows = {r['stage_id']:r for r in self.pins['stages']}
        for row in s['stages']:
            pin = row['pin']
            if row['origin'] != LATEST:
                frozen = original_rows[row['stage_id']]
                f.need(TO_INTERNAL[row['origin']] == frozen['origin'] and all(pin[k] == v for k,v in frozen['pin'].items()),
                       'historical frozen metadata/payload pin changed')
                self._validate_pin(pin, prepare=False, identity=self.contexts[TO_INTERNAL[row['origin']]]['identity'])
            else:
                f.need(set(pin) == ot.STAGE_PIN_KEYS and all(pin[k] is None for k in PAYLOAD_KEYS),
                       'latest payload pins must remain null before actual acquisition')
                for key in ('artifact_id','producer_job_id','artifact_zip_bytes'): ot.positive(pin[key], key)
                ot.digest(pin['artifact_zip_sha256'], 'latest ZIP digest')
                ot.timestamp(pin['expires_at'])
        latest = self.contexts[LATEST]
        identity = latest['identity']
        f.need(f.sha(f.json_bytes(identity)) == LATEST_IDENTITY and
               identity['run_id'] == LATEST_RUN and identity['run_attempt'] == '1' and
               identity['pipeline_commit'] == LATEST_PIPELINE and identity['contract_sha256'] == LATEST_CONTRACT,
               'latest expected native identity changed')
        f.need(identity['prior_identity_sha256'] == self.contexts['CurrentOrigin']['prepare']['identity_sha256'] and
               identity['old_identity_sha256'] == self.contexts['OldOrigin']['prepare']['identity_sha256'],
               'latest native predecessor identity changed')
        ot.validate_workflow(latest['workflow'])
        self._validate_pin(latest['prepare'], prepare=True, identity=identity)
        f.need(sum(r['pin']['artifact_zip_bytes'] for r in s['stages'] if r['origin'] == LATEST) == 84450964,
               'latest38 ZIP metadata total changed')

    def _run(self, origin):
        if origin != LATEST:
            return super()._run(origin)
        # Same terminal-only boundary as frozen historical _run; latest fixed facts.
        c = self._context(origin); identity, workflow = c['identity'], c['workflow']
        run = self._json(f'/repos/{ot.REPOSITORY}/actions/runs/{LATEST_RUN}')
        for key in ('repository','head_repository'):
            repo = run.get(key)
            f.need(type(repo) is dict and type(repo.get('id')) is int and repo['id'] == ot.REPOSITORY_ID and
                   repo.get('full_name') == ot.REPOSITORY, 'latest terminal repository mismatch')
        f.need(type(run.get('id')) is int and str(run['id']) == identity['run_id'] and
               type(run.get('run_attempt')) is int and run['run_attempt'] == 1 and
               run.get('head_sha') == identity['pipeline_commit'] and run.get('event') == 'push' and
               run.get('head_branch') == workflow['head_branch'] and
               type(run.get('workflow_id')) is int and run['workflow_id'] == workflow['workflow_id'] and
               run.get('path') == workflow['path'] and run.get('name') == workflow['name'] and
               run.get('created_at') == identity['run_started_at'], 'latest run/workflow/rerun identity mismatch')
        f.need(run.get('status') == 'completed' and run.get('conclusion') == 'failure' and
               run.get('updated_at') == c['terminal_updated_at'], 'latest must remain exact terminal failure')
        f.need(ot.timestamp(run['created_at']) <= ot.timestamp(run['updated_at']) <= self.now(),
               'latest terminal timestamps invalid')
        return run

    def _download_fixed(self, origin, role, destination, members, max_bytes, pin):
        if origin == LATEST and role != 'prepare':
            f.need(set(self.historical_ids) <= set(self._seen_stages) and self.raw_bytes >= HISTORICAL_GLOBAL,
                   'all47 historical payloads and fixed48 ledger must precede latest transfer')
        for context in INTERNAL: self._run(context)
        # Calls the exact frozen download path, including its unchanged _extract.
        result = super()._download_fixed(origin, role, destination, members, max_bytes, pin)
        for context in INTERNAL: self._run(context)
        return result

    def stage_pin(self, stage_id):
        row = self.rows[stage_id]
        pin = {key:value for key,value in row['pin'].items() if value is not None}
        if row['origin'] == LATEST:
            f.need(LATEST in self._prepared, 'latest authenticated prepare required')
            pin['identity_sha256'] = self._prepared[LATEST]['identity_sha256']
        return pin

    def download_selected_stage(self, stage_id):
        f.need(set(self._prepared) == set(INTERNAL), 'all3 fixed prepares required')
        f.need(stage_id in self.rows and stage_id not in self._seen_stages, 'unselected/repeated C087 stage')
        row = self.rows[stage_id]; origin = TO_INTERNAL[row['origin']]; pin = self.stage_pin(stage_id)
        path = self.root / (row['origin'] + '-' + stage_id)
        path, metadata = self._download_fixed(origin, stage_id, path,
             ['delta.tar','upload-candidate.json'], ot.MAX_ARTIFACT_BYTES + ot.MAX_DESCRIPTOR_BYTES, pin)
        raw = (path/'upload-candidate.json').read_bytes(); raw_sha = f.sha(raw)
        if row['origin'] != LATEST:
            f.need(raw_sha == pin['raw_descriptor_sha256'], 'historical raw descriptor pin changed')
        descriptor = f.parse_json(raw)
        raw_keys = (h.cp.NATIVE_KEYS - {'artifact_zip_sha256'}) | {'archive_path'}
        f.need(type(descriptor) is dict and set(descriptor) == raw_keys and
               all(descriptor[k] is None for k in ('artifact_id','producer_job_id','producer_conclusion')) and
               type(descriptor['archive_path']) is str and descriptor['archive_path'], 'native descriptor fields/placeholders changed')
        f.need(descriptor['schema'] == 'fresh-stage-upload-candidate-v1' and descriptor['stage_id'] == stage_id and
               descriptor['identity'] == self.contexts[origin]['identity'] and
               descriptor['producer_job'] == metadata['role']['producer_job'] and
               type(descriptor['retention_days']) is int and descriptor['retention_days'] == 7,
               'native descriptor identity/producer/retention changed')
        for key in ('archive_sha256','receipt_sha256'): ot.digest(descriptor[key], key)
        f.need(type(descriptor['archive_bytes']) is int and 0 < descriptor['archive_bytes'] <= ot.MAX_ARTIFACT_BYTES and
               descriptor['archive_bytes'] == (path/'delta.tar').stat().st_size and
               descriptor['archive_sha256'] == f.file_sha(path/'delta.tar'), 'native tar bytes/hash mismatch')
        if row['origin'] != LATEST:
            f.need(all(descriptor[k] == pin[k] for k in ('archive_sha256','archive_bytes','receipt_sha256')),
                   'historical native payload pin changed')
        descriptor.update(artifact_id=pin['artifact_id'], producer_job_id=pin['producer_job_id'],
                          producer_conclusion='success', artifact_zip_sha256=pin['artifact_zip_sha256'])
        descriptor.pop('archive_path')
        wrapper = {'origin':row['origin'],'native_descriptor':descriptor,'archive_path':str(path/'delta.tar'),
                   'authenticated_metadata':metadata,'raw_descriptor_sha256':raw_sha}
        self._seen_stages.append(stage_id)
        return wrapper

    def download_stage(self, *args, **kwargs):
        raise f.Rejected('C087 requires exact download_selected_stage dispatch')

    def reauthenticate_selected(self, wrapper):
        sid = wrapper['native_descriptor']['stage_id']; row = self.rows[sid]
        f.need(wrapper['origin'] == row['origin'], 'C087 wrapper outer origin changed')
        origin = TO_INTERNAL[row['origin']]; pin = self.stage_pin(sid)
        run = self._run(origin); self._verify_workflow_source(origin)
        job, binding = self._producer(origin, sid, run, pin)
        artifact = self._artifact(origin, sid, run, job, pin, ot.MAX_ARTIFACT_BYTES + ot.MAX_DESCRIPTOR_BYTES)
        f.need(self._metadata(origin,run,job,artifact,binding) == wrapper['authenticated_metadata'],
               'C087 authenticated metadata changed')
        for context in INTERNAL: self._run(context)
        self._check_age()



class BatchC087Acquisition(C087Acquisition):
    """Explicit two-round terminal run/job observations; artifacts stay uncached.

    This changes the freshness boundary to batch start/end. It does not pretend
    that an in-memory validator call is a new remote observation. Each round uses
    the unchanged bounded authenticated JSON/list reader and quota gate.
    """
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self._snapshot_phase = 'idle'
        self._snapshot_last_monotonic = time.monotonic()
        self._snapshot_runs = self._snapshot_jobs = None
        self._run_paths = {origin:f'/repos/{ot.REPOSITORY}/actions/runs/{self.contexts[origin]["identity"]["run_id"]}' for origin in INTERNAL}
        self._job_paths = {origin:self._run_paths[origin] + '/attempts/1/jobs' for origin in INTERNAL}
        f.need(len(set(self._run_paths.values())) == len(set(self._job_paths.values())) == 3,
               'three distinct fixed terminal contexts required')

    def _snapshot_check(self):
        f.need(self._snapshot_phase != 'poisoned', 'terminal snapshot session poisoned')
        now = time.monotonic()
        f.need(type(now) in (int,float) and math.isfinite(now) and
               math.isfinite(self._snapshot_last_monotonic) and now >= self._snapshot_last_monotonic,
               'terminal snapshot monotonic clock rollback/nonfinite')
        self._snapshot_last_monotonic = now
        self._check_age()

    def _snapshot_fail(self):
        self._snapshot_phase = 'poisoned'
        self._snapshot_runs = self._snapshot_jobs = None

    def _snapshot_copy(self, mapping, path):
        try:
            self._snapshot_check()
            f.need(self._snapshot_phase in ('initial','final') and mapping is not None and path in mapping,
                   'complete terminal snapshot round required')
            result = copy.deepcopy(mapping[path])
            self._snapshot_check()
            return result
        except BaseException:
            self._snapshot_fail()
            raise

    def _json(self, path):
        if path in self._run_paths.values():
            return self._snapshot_copy(self._snapshot_runs, path)
        self._snapshot_check()
        return super()._json(path)

    def _collection(self, path, key):
        if path in self._job_paths.values():
            if key != 'jobs':
                self._snapshot_fail()
                raise f.Rejected('terminal jobs collection key mismatch')
            return self._snapshot_copy(self._snapshot_jobs, path)
        self._snapshot_check()
        return super()._collection(path, key)

    def refresh_terminal_snapshots(self, *, final):
        """One initial and one fresh final batch; any failure consumes this use."""
        try:
            self._snapshot_check()
            f.need(type(final) is bool and self._snapshot_phase == ('initial' if final else 'idle'),
                   'terminal snapshot phase/order mismatch')
            previous_runs,previous_jobs = self._snapshot_runs,self._snapshot_jobs
            self._snapshot_runs = self._snapshot_jobs = None
            self._snapshot_phase = 'loading_final' if final else 'loading_initial'
            runs,jobs = {},{}
            for origin in INTERNAL:
                self._snapshot_check()
                run_path,job_path = self._run_paths[origin],self._job_paths[origin]
                # Explicit superclass calls bypass only this new cache layer.
                # No errors, incomplete lists or artifact bytes enter a cache.
                runs[run_path] = super()._json(run_path)
                rows = super()._collection(job_path, 'jobs')
                ids = [ot.positive(row.get('id'), 'terminal job id') for row in rows]
                f.need(len(ids) == len(set(ids)), 'duplicate terminal job IDs')
                jobs[job_path] = sorted(rows, key=lambda row:row['id'])
                self._snapshot_check()
            if final:
                # Bind complete terminal responses, including OldOrigin.updated_at
                # and every producer/step field, not the smaller certificate view.
                f.need(f.json_bytes(runs) == f.json_bytes(previous_runs) and
                       f.json_bytes(jobs) == f.json_bytes(previous_jobs),
                       'terminal run/job snapshots changed between batch boundaries')
            self._snapshot_runs,self._snapshot_jobs = runs,jobs
            self._snapshot_phase = 'final' if final else 'initial'
            for origin in INTERNAL:
                run = self._run(origin)  # Exact unchanged terminal validators.
                self._producer(origin,'prepare',run,self.contexts[origin]['prepare'])
                for row in self.spec['stages']:
                    if TO_INTERNAL[row['origin']] == origin:
                        self._producer(origin,row['stage_id'],run,row['pin'])
            self._snapshot_check()
        except BaseException:
            self._snapshot_fail()
            raise


def file_record(root, path):
    path = Path(path); info = path.lstat()
    f.need(stat.S_ISREG(info.st_mode) and info.st_nlink == 1, 'C087 retained file type/link mismatch')
    return {'path':path.relative_to(root).as_posix(),'bytes':info.st_size,'sha256':f.file_sha(path)}


def acquire(output_root, token, *, deadline_monotonic, session_nonce, opener=None, now=None):
    root = h.owned_new_root(output_root)
    try:
        transport = BatchC087Acquisition(token,root,deadline_monotonic=deadline_monotonic,
                    session_nonce=session_nonce,opener=opener,now=now)
        transport.refresh_terminal_snapshots(final=False)
        started = utc_now(transport); prepares = {}
        for origin in INTERNAL:
            prepares[origin] = transport.authenticate_prepare(origin,root/(TO_OUTER[origin]+'-prepare'))
        wrappers, raw_paths = {}, {}
        for sid in transport.historical_ids + transport.latest_ids:
            wrapper = transport.download_selected_stage(sid)
            receipt_path = h.copy_native_receipt(transport,wrapper)
            wrappers[sid] = wrapper; raw_paths[sid] = receipt_path
            if sid == transport.historical_ids[-1]:
                f.need(transport.raw_bytes == HISTORICAL_GLOBAL, 'fixed global48 ledger reconciliation failed')
        ordered = [wrappers[sid] for sid in transport.spec['scope']['predecessor_stage_ids']]
        for wrapper in ordered: transport.reauthenticate_selected(wrapper)
        transport.refresh_terminal_snapshots(final=True)
        contexts = {}
        for origin in INTERNAL:
            outer = TO_OUTER[origin]; c = transport.contexts[origin]; run = transport._run(origin); pin = c['prepare']
            job,binding = transport._producer(origin,'prepare',run,pin)
            artifact = transport._artifact(origin,'prepare',run,job,pin,h.MAX_PREPARE)
            metadata = transport._metadata(origin,run,job,artifact,binding)
            f.need(metadata == prepares[origin]['authenticated_metadata'], 'C087 prepare metadata changed')
            projected = copy.deepcopy(metadata['run']); projected.update(name=run['name'],updated_at=run['updated_at'])
            folder = root/(outer+'-prepare'); identity_raw = (folder/'identity.json').read_bytes()
            contexts[outer] = {'native_origin':TO_NATIVE[outer],'identity':c['identity'],
                'identity_path':(folder/'identity.json').relative_to(root).as_posix(),
                'identity_raw_sha256':f.sha(identity_raw),'identity_canonical_sha256':f.sha(f.json_bytes(f.parse_json(identity_raw))),
                'inventory_path':(folder/'inventory.json').relative_to(root).as_posix(),
                'inventory_sha256':f.file_sha(folder/'inventory.json'),'run':projected,'workflow':c['workflow'],
                'prepare':{'pin':copy.deepcopy(pin),'authenticated_metadata':metadata}}
        stage_records, rows = [], []
        for wrapper in ordered:
            sid = wrapper['native_descriptor']['stage_id']; outer = wrapper['origin']; path = Path(wrapper['archive_path']).parent
            pin = transport.stage_pin(sid); d = wrapper['native_descriptor']
            pin.update({k:d[k] for k in ('archive_bytes','archive_sha256','receipt_sha256')})
            pin['raw_descriptor_sha256'] = wrapper['raw_descriptor_sha256']
            stage_records.append({'stage_id':sid,'origin':outer,'native_origin':TO_NATIVE[outer],'pin':pin,
                'raw_descriptor':file_record(root,path/'upload-candidate.json'),
                'raw_receipt':file_record(root,raw_paths[sid]),'archive':file_record(root,path/'delta.tar')})
            rows.append({'wrapper':wrapper,'raw_descriptor_path':str(path/'upload-candidate.json'),
                         'raw_receipt_path':str(raw_paths[sid])})
        latest_raw = sum(w['native_descriptor']['archive_bytes'] for w in ordered if w['origin'] == LATEST)
        selected_raw = sum(w['native_descriptor']['archive_bytes'] for w in ordered)
        f.need(selected_raw == HISTORICAL_SELECTED + latest_raw and
               transport.raw_bytes == HISTORICAL_GLOBAL + latest_raw <= h.RAW_CAP, 'C087 global raw ledger mismatch')
        h.disk_headroom(root,8*ot.MAX_METADATA_BYTES,new_files=4)
        h.write_json(root/'WRAPPERS.json',rows)
        with (root/'ACQUISITION_SPEC.json').open('xb') as out: out.write((HERE/'C087_ACQUISITION_SPEC.json').read_bytes())
        certificate = {'schema':'c087-historical-acquisition-v1','status':'transport_bytes_authenticated_only',
            'proof_pass_claimed':False,'semantic_admission':False,'session_nonce':session_nonce,
            'host_deadline_monotonic':deadline_monotonic,'started_at_utc':started,'authenticated_at_utc':utc_now(transport),
            'original_deadline_utc':h.DEADLINE,'acquisition_spec_sha256':SPEC_SHA256,
            'downloader_sha256':FROZEN_FILES['historical_acquisition.py'],'inputs':transport.spec['inputs'],
            'scope':transport.spec['scope'],'accounting':{'historical_global_raw_bytes':HISTORICAL_GLOBAL,
                'historical_selected_raw_bytes':HISTORICAL_SELECTED,'historical_unrestored_raw_bytes':OMITTED_RESERVE,
                'latest_raw_bytes':latest_raw,'selected_raw_bytes':selected_raw,'charged_raw_bytes':transport.raw_bytes,
                'aggregate_cap_bytes':h.RAW_CAP},'contexts':contexts,'wrappers_path':'WRAPPERS.json','wrappers':ordered,
            'stages':stage_records,'files':h.retained_files(root)}
        transport._check_age(); h.write_json(root/'TRANSPORT_RECEIPT.json',certificate); transport._check_age()
        receipt_sha256 = f.file_sha(root/'TRANSPORT_RECEIPT.json')
        transport._check_age()  # Final hashing must not return past the shared/age deadline.
        return {'root':str(root),'wrappers_path':str(root/'WRAPPERS.json'),
                'transport_receipt_path':str(root/'TRANSPORT_RECEIPT.json'),
                'transport_receipt_sha256':receipt_sha256}
    except BaseException:
        try: shutil.rmtree(root)
        except Exception: raise f.Rejected('owned C087 quarantine cleanup failed') from None
        raise


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--quarantine',required=True)
    parser.add_argument('--deadline-monotonic',required=True,type=float)
    parser.add_argument('--session-nonce',required=True)
    args = parser.parse_args()
    f.need(sys.flags.isolated == 1 and sys.flags.no_site == 1 and sys.flags.dont_write_bytecode == 1,
           'acquisition CLI requires fresh isolated Python -I -S -B')
    h.require_runtime_envelope()
    acquire(args.quarantine,os.environ.get('GH_TOKEN',''),deadline_monotonic=args.deadline_monotonic,session_nonce=args.session_nonce)
    print('C087 transport bytes authenticated; native semantic admission still required.')


if __name__ == '__main__':
    try: main()
    except SystemExit: raise
    except BaseException:
        print('C087 acquisition failed closed; no semantic or proof verdict.',file=sys.stderr)
        sys.exit(1)
