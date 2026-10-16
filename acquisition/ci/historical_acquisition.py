#!/usr/bin/env python3
"""Fixed historical transport only. No proof execution or semantic admission.

The reviewed origin_transport.py is an immutable dependency. Its current-origin
constructor/run semantics are deliberately NOT used. Only authenticated read,
source/job/artifact validation and bounded metadata retry methods are inherited.
Native validator labels remain OldOrigin / CurrentOrigin; both remote origins
are independently and explicitly required to be historical terminal failures.
"""
from __future__ import annotations
import argparse
import copy
import hashlib
import http.client
import json
import math
import os
from pathlib import Path
import re
import resource
import shutil
import stat
import sys
import tarfile
import time
import types
import urllib.error
import urllib.parse
import urllib.request
import zipfile
from datetime import datetime, timezone

HERE = Path(__file__).resolve().parent
DEPENDENCIES = {
    'origin_transport.py': 'c5ba140113b98460f8267f55fcdad098c391e4918fdc3a9e8e2f90e8ff5b110b',
    'fresh_stage.py': '9085c9eea092c270fbd6952834839103c66519a7b4716fe09147001c7d96355d',
    'continuation_policy.py': '1759e1fc5587ec2b5462604f9f7a16cebaefdb85f153d563514b36b18d314be2',
    'ci_transport.py': '0e17698024da89562d654978436b707a140fef81c3463a8b0841af8de2355c95',
}
for _name, _sha in DEPENDENCIES.items():
    _path = HERE / _name
    if _path.is_symlink() or hashlib.sha256(_path.read_bytes()).hexdigest() != _sha:
        raise RuntimeError('historical transport dependency hash mismatch')
# Isolated Python (-I) omits the script directory; restore only this verified bundle.
sys.path.insert(0, str(HERE))
import fresh_stage as f
import continuation_policy as cp
import origin_transport as ot
import ci_transport as ct
for _module in (f, cp, ot, ct):
    if Path(_module.__file__).resolve() != HERE / Path(_module.__file__).name:
        raise RuntimeError('historical transport dependency module shadowing')

PINS_SHA256 = '427f4a4b8a6c1b324650703979b833127ce729cc8668a4ccfddbca430c2df6af'
RAW_CAP = 4 * 1024**3
MIN_FREE = 512 * 1024**2
METADATA_RESERVE = 64 * 1024**2
INODE_RESERVE = 256
MAX_PREPARE = 32 * 1024**2
INTERNAL_SECONDS = 330 * 60
MEMORY_CAP = 8 * 1024**3
DEADLINE = '2026-10-22T06:15:54Z'
ORIGINS = ('OldOrigin', 'CurrentOrigin')
HISTORICAL_NAMES = {'OldOrigin': 'OriginalHistoricalOrigin', 'CurrentOrigin': 'PriorSuccessorHistoricalOrigin'}
PRIOR_RUN = '38917565694'
PRIOR_COMMIT = 'fca406f6c52a622762d9c75167a92f895c3ddd00'
PRIOR_PIN_KEYS = {'artifact_id', 'producer_job_id', 'artifact_name', 'artifact_zip_sha256',
                  'artifact_zip_bytes', 'identity_sha256', 'expires_at'}


def load_pins():
    path = HERE / 'historical_acquisition_pins.json'
    f.no_symlink_path(path)
    raw = path.read_bytes()
    f.need(f.sha(raw) == PINS_SHA256, 'fixed historical acquisition pins changed')
    pins = f.parse_json(raw)
    f.need(pins['schema'] == 'hierarchy-c-historical-acquisition-pins-v1' and
           pins['repository'] == ot.REPOSITORY and pins['repository_id'] == ot.REPOSITORY_ID and
           pins['original_deadline_utc'] == DEADLINE, 'historical repository/deadline mismatch')
    f.need(len(pins['stages']) == 48 and sum(r['origin'] == 'OldOrigin' for r in pins['stages']) == 37,
           'exact original37/prior11 membership required')
    return pins


def disk_headroom(root, additional_bytes, *, new_files):
    """Actual filesystem allocation + metadata/inode reserve, not logical bytes alone."""
    f.need(type(additional_bytes) is int and additional_bytes >= 0 and
           type(new_files) is int and new_files > 0, 'invalid disk reservation')
    root = Path(root)
    f.no_symlink_path(root)
    v = os.statvfs(root)
    block = max(4096, v.f_frsize)
    required = ((additional_bytes + block - 1) // block) * block
    required += new_files * block + METADATA_RESERVE + MIN_FREE
    f.need(v.f_bavail * v.f_frsize >= required, 'insufficient actual free disk including allocation/metadata reserve')
    f.need(v.f_favail >= new_files + INODE_RESERVE, 'insufficient actual free inodes')
    return {'required_bytes': required, 'free_bytes': v.f_bavail * v.f_frsize,
            'required_inodes': new_files + INODE_RESERVE, 'free_inodes': v.f_favail,
            'allocation_unit': block}


def owned_new_root(path):
    path = Path(path)
    f.need(path.is_absolute() and path == path.resolve(), 'quarantine must be a canonical absolute path')
    f.no_symlink_path(path)
    f.need(not path.exists() and path.parent.is_dir(), 'quarantine must be fresh with an existing parent')
    f.need(path.parent.stat().st_uid == os.getuid(), 'quarantine parent must be owned by this user')
    disk_headroom(path.parent, 0, new_files=8)
    path.mkdir(mode=0o700)
    f.need(path.stat().st_uid == os.getuid() and stat.S_IMODE(path.stat().st_mode) == 0o700,
           'quarantine ownership/mode mismatch')
    return path


class HistoricalAcquisition(ot.OriginTransport):
    """Separate historical semantics; never instantiate/spoof trusted current Transport."""
    def __init__(self, token, root, *, opener=None, now=None, deadline_monotonic=None):
        f.need(type(token) is str and bool(token) and not any(ord(c) < 33 or ord(c) == 127 for c in token),
               'ephemeral read-only Actions token missing/invalid')
        self.pins = load_pins()
        self.contexts = copy.deepcopy(self.pins['contexts'])
        # This holder carries a credential only, not an executing-run identity.
        self.current = types.SimpleNamespace(token=token)
        self.opener = opener if opener is not None else urllib.request.build_opener(ct.NoRedirect())
        self.now = now or (lambda: datetime.now(timezone.utc))
        self.root = Path(root)
        f.no_symlink_path(self.root)
        f.need(self.root.is_dir() and self.root.stat().st_uid == os.getuid() and
               stat.S_IMODE(self.root.stat().st_mode) == 0o700, 'fresh owned quarantine required')
        f.need(not list(self.root.iterdir()), 'quarantine must be empty')
        started = time.monotonic()
        self.deadline_monotonic = started + INTERNAL_SECONDS
        if deadline_monotonic is not None:
            f.need(type(deadline_monotonic) in (int, float) and math.isfinite(deadline_monotonic),
                   'invalid shared wall deadline')
            self.deadline_monotonic = min(self.deadline_monotonic, deadline_monotonic)
        self.age_deadline_monotonic = started + (ot.timestamp(DEADLINE) - self.now()).total_seconds()
        self.raw_bytes = 0
        self._prepared = {}
        self._source_verified = set()
        self._active_pin = None
        self._seen_stages = []
        self._validate_contexts()
        self._check_age()

    def _validate_contexts(self):
        old, prior = (self.contexts[x] for x in ORIGINS)
        f.need(old['run_id'] == ot.OLD_RUN_ID and old['run_attempt'] == 1 and
               old['pipeline_commit'] == ot.OLD_PIPELINE and
               all(old['identity'][k] == v for k, v in ot.OLD_FACTS.items()), 'original context changed')
        identity = prior['identity']
        f.need(identity['run_id'] == PRIOR_RUN and identity['run_attempt'] == '1' and
               identity['pipeline_commit'] == PRIOR_COMMIT, 'prior terminal context changed')
        cp.validate_identity_pair(old['identity'], identity)
        for origin, context in self.contexts.items():
            ot.validate_workflow(context['workflow'])
            self._validate_pin(context['prepare'], prepare=True, identity=context['identity'])
            f.need(context['prepare']['identity_sha256'] == f.sha(f.json_bytes(context['identity'])),
                   'prepared native identity hash changed')
        seen = set()
        for row in self.pins['stages']:
            f.need(row['origin'] in ORIGINS and row['historical_origin'] == HISTORICAL_NAMES[row['origin']] and
                   row['stage_id'] not in seen, 'historical stage membership/label duplicate')
            seen.add(row['stage_id'])
            if row['origin'] == 'OldOrigin':
                self._validate_pin(row['pin'], prepare=False, identity=old['identity'])
            else:
                ot.exact_keys(row['pin'], PRIOR_PIN_KEYS, 'prior metadata-only pin')
                for k in ('artifact_id', 'producer_job_id', 'artifact_zip_bytes'):
                    ot.positive(row['pin'][k], k)
                for k in ('artifact_zip_sha256', 'identity_sha256'):
                    ot.digest(row['pin'][k], k)
                f.need(row['pin']['identity_sha256'] == prior['prepare']['identity_sha256'], 'prior identity pin changed')
                ot.timestamp(row['pin']['expires_at'])
        f.need(sum(r['pin']['archive_bytes'] for r in self.pins['stages'] if r['origin'] == 'OldOrigin') == 1861550080,
               'original raw byte total changed')
        f.need(sum(r['pin']['artifact_zip_bytes'] for r in self.pins['stages'] if r['origin'] == 'CurrentOrigin') == 1148047857,
               'prior ZIP byte total changed')

    def _check_age(self):
        super()._check_age()
        now = self.now()
        f.need(now < ot.timestamp(DEADLINE), 'original fixed age deadline reached')
        remaining_age = (ot.timestamp(DEADLINE) - now).total_seconds()
        self.age_deadline_monotonic = min(self.age_deadline_monotonic, time.monotonic() + remaining_age)
        f.need(time.monotonic() < min(self.deadline_monotonic, self.age_deadline_monotonic),
               'shared internal or original age deadline reached')

    def _metadata_remaining(self, budget):
        budget['deadline'] = min(budget['deadline'], self.deadline_monotonic, self.age_deadline_monotonic)
        return super()._metadata_remaining(budget)

    @staticmethod
    def _safe_redirect(url):
        f.need(type(url) is str and bool(url) and not any(ord(c) < 33 or ord(c) == 127 for c in url) and
               '#' not in url and '\\' not in url, 'unsafe storage redirect')
        try:
            parsed = urllib.parse.urlsplit(url)
            good = (parsed.scheme == 'https' and bool(parsed.hostname) and not parsed.username and
                    not parsed.password and parsed.port in (None, 443))
        except ValueError:
            good = False
        f.need(good, 'unsafe storage redirect')

    def _request(self, path, *, authenticated=True):
        if authenticated:
            f.need(type(path) is str and path.startswith('/repos/' + ot.REPOSITORY + '/') and
                   not any(ord(c) < 33 or ord(c) == 127 for c in path) and
                   not any(s in path for s in ('..', '\\', '#', '@', '%')), 'unapproved API repository/path')
            self._safe_redirect(ct.API + path)
        return super()._request(path, authenticated=authenticated)

    def _run(self, origin):
        # Intentionally independent of the base's active/successful-current branch.
        context = self._context(origin)
        identity, workflow = context['identity'], context['workflow']
        run = self._json(f'/repos/{ot.REPOSITORY}/actions/runs/{identity["run_id"]}')
        for key in ('repository', 'head_repository'):
            repo = run.get(key)
            f.need(type(repo) is dict and type(repo.get('id')) is int and repo['id'] == ot.REPOSITORY_ID and
                   repo.get('full_name') == ot.REPOSITORY, 'historical run repository mismatch')
        f.need(type(run.get('id')) is int and str(run['id']) == identity['run_id'] and
               type(run.get('run_attempt')) is int and run['run_attempt'] == 1 and
               run.get('head_sha') == identity['pipeline_commit'] and run.get('event') == 'push' and
               run.get('head_branch') == workflow['head_branch'] and
               type(run.get('workflow_id')) is int and run['workflow_id'] == workflow['workflow_id'] and
               run.get('path') == workflow['path'] and run.get('name') == workflow['name'] and
               run.get('created_at') == identity['run_started_at'], 'historical run identity/workflow/rerun mismatch')
        f.need(run.get('status') == 'completed' and run.get('conclusion') == 'failure',
               'both historical runs must be terminal failures')
        f.need(ot.timestamp(run['created_at']) <= ot.timestamp(run.get('updated_at')) <= self.now(),
               'historical run timestamps invalid')
        if origin == 'CurrentOrigin':
            f.need(run['updated_at'] == context['terminal_updated_at'], 'pinned prior terminal observation changed')
        return run

    @staticmethod
    def _metadata(origin, run, job, artifact, binding):
        # OLD_ORIGIN requests the base's terminal fields for BOTH historical runs.
        return ot.OriginTransport._metadata('OldOrigin', run, job, artifact, binding)

    def _open_zip(self, aid):
        request = self._request(f'/repos/{ot.REPOSITORY}/actions/artifacts/{aid}/zip')
        for redirects in range(ot.MAX_REDIRECTS + 1):
            self._check_age()
            try:
                response = self.opener.open(request, timeout=60)
            except urllib.error.HTTPError as error:
                code = error.code
                location = error.headers.get('Location', '') if error.headers is not None else ''
                try:
                    error.close()
                except Exception:
                    raise f.Rejected('artifact redirect response cleanup failed') from None
                f.need(code in (301, 302, 303, 307, 308), 'artifact GET failed')
                f.need(redirects < ot.MAX_REDIRECTS, 'artifact redirect bound exceeded')
                # Validate raw Location before urljoin can discard controls.
                f.need(type(location) is str and location and not any(ord(c) < 33 or ord(c) == 127 for c in location)
                       and '#' not in location and '\\' not in location, 'unsafe artifact redirect')
                url = urllib.parse.urljoin(request.full_url, location)
                self._safe_redirect(url)
                request = self._request(url, authenticated=False)
            except (OSError, ValueError, http.client.HTTPException):
                raise f.Rejected('artifact request failed; URL suppressed') from None
            else:
                if response.getcode() != 200:
                    try:
                        response.close()
                    except Exception:
                        raise f.Rejected('artifact status response cleanup failed') from None
                    raise f.Rejected('artifact response must be 200')
                return response
        raise f.Rejected('artifact redirect bound exceeded')

    def _check_destination(self, destination):
        destination = Path(destination)
        f.no_symlink_path(destination)
        f.need(destination.parent == self.root and not destination.exists(), 'artifact destination outside fresh owned quarantine')
        return destination

    def _extract(self, artifact, destination, members, max_bytes):
        destination = self._check_destination(destination)
        pin = self._active_pin
        f.need(pin is not None and artifact['id'] == pin['artifact_id'], 'download must have fixed artifact pin')
        self._check_age()
        prepare = members == ['identity.json', 'inventory.json']
        maximum_raw = MAX_PREPARE if prepare else pin.get('archive_bytes', min(ot.MAX_ARTIFACT_BYTES, RAW_CAP - self.raw_bytes))
        f.need(prepare or (maximum_raw > 0 and self.raw_bytes + maximum_raw <= RAW_CAP),
               'whole48 raw cap cannot fit next pinned archive')
        disk_headroom(self.root, artifact['size_in_bytes'] + maximum_raw + ot.MAX_DESCRIPTOR_BYTES, new_files=6)
        destination.mkdir(mode=0o700)
        archive = destination / 'download.zip'
        response = None
        try:
            remaining = min(900, self.deadline_monotonic - time.monotonic(),
                            self.age_deadline_monotonic - time.monotonic())
            with ot._metadata_wall_limit(remaining):
                response = self._open_zip(artifact['id'])
                count, h = 0, hashlib.sha256()
                try:
                    with archive.open('xb') as handle:
                        while True:
                            self._check_age()
                            f.need(self.now() < ot.timestamp(artifact['expires_at']), 'artifact expired during transfer')
                            block = response.read(1024**2)
                            f.need(type(block) is bytes, 'artifact transfer returned non-byte data')
                            if block == b'':
                                break  # EOF is required even after expected length.
                            count += len(block)
                            f.need(count <= max_bytes and count <= artifact['size_in_bytes'], 'ZIP transfer size exceeded')
                            h.update(block)
                            handle.write(block)
                        handle.flush()
                        os.fsync(handle.fileno())
                finally:
                    closing, response = response, None
                    if not isinstance(sys.exc_info()[1], ot._MetadataHardTimeout):
                        try:
                            closing.close()
                        except Exception:
                            raise f.Rejected('artifact response cleanup failed') from None
                f.need(count == artifact['size_in_bytes'] and h.hexdigest() == artifact['digest'][7:], 'ZIP size/digest mismatch')
            with zipfile.ZipFile(archive) as zipped:
                infos = zipped.infolist()
                f.need(len(infos) == len(members) and {i.filename for i in infos} == set(members), 'ZIP exact member/duplicate mismatch')
                total = 0
                raw_size = 0
                for info in infos:
                    f.safe_rel(info.filename)
                    mode = info.external_attr >> 16
                    f.need(not info.is_dir() and stat.S_IFMT(mode) in (0, stat.S_IFREG) and
                           not info.flag_bits & 1 and info.compress_type in (zipfile.ZIP_STORED, zipfile.ZIP_DEFLATED), 'unsafe ZIP member')
                    total += info.file_size
                    f.need(0 <= info.file_size and total <= max_bytes, 'ZIP expansion bound')
                    if info.filename in ('identity.json', 'upload-candidate.json'):
                        f.need(info.file_size <= ot.MAX_DESCRIPTOR_BYTES, 'descriptor/identity expansion bound')
                    if info.filename == 'delta.tar':
                        raw_size = info.file_size
                        f.need(0 < raw_size <= ot.MAX_ARTIFACT_BYTES and self.raw_bytes + raw_size <= RAW_CAP,
                               'whole48 raw archive cap exceeded')
                        f.need('archive_bytes' not in pin or raw_size == pin['archive_bytes'], 'original raw size pin changed')
                disk_headroom(self.root, total, new_files=len(infos) + 2)
                for info in infos:
                    self._check_age()
                    with zipped.open(info) as src, (destination / info.filename).open('xb') as dst:
                        copied = 0
                        while True:
                            self._check_age()
                            block = src.read(1024**2)
                            if not block:
                                break
                            copied += len(block)
                            f.need(copied <= info.file_size, 'overlong ZIP member')
                            dst.write(block)
                        f.need(copied == info.file_size, 'truncated ZIP member')
                        dst.flush()
                        os.fsync(dst.fileno())
            self._check_age()
            f.need(self.now() < ot.timestamp(artifact['expires_at']), 'artifact expired during extraction')
            archive.unlink()  # Only authenticated + fully extracted transient ZIP.
            self.raw_bytes += raw_size
            return destination
        except BaseException:
            # Scope is the exclusively-created artifact directory, never caller data.
            if response is not None:
                try:
                    response.close()
                except Exception:
                    pass
            try:
                shutil.rmtree(destination)
            except Exception:
                raise f.Rejected('owned artifact quarantine cleanup failed') from None
            raise

    def _download_fixed(self, origin, role, destination, members, max_bytes, pin):
        f.need(self._active_pin is None, 'parallel/reentrant downloads forbidden')
        self._active_pin = pin
        try:
            return super()._download(origin, role, destination, members, max_bytes, pin)
        finally:
            self._active_pin = None

    def authenticate_prepare(self, origin, destination, max_bytes=MAX_PREPARE):
        context = self._context(origin)
        f.need(origin not in self._prepared and max_bytes == MAX_PREPARE, 'prepare replay/bound changed')
        pin = context['prepare']
        path, metadata = self._download_fixed(origin, 'prepare', destination,
                ['identity.json', 'inventory.json'], max_bytes, pin)
        raw = (path / 'identity.json').read_bytes()
        f.need(f.sha(raw) == pin['identity_sha256'] and f.parse_json(raw) == context['identity'],
               'authenticated native prepare identity mismatch')
        f.need(f.file_sha(path / 'inventory.json') == pin['inventory_sha256'], 'authenticated canonical inventory mismatch')
        result = {'origin': origin, 'identity': context['identity'], 'identity_sha256': f.sha(raw),
                  'inventory_path': str(path / 'inventory.json'), 'authenticated_metadata': metadata}
        self._prepared[origin] = copy.deepcopy(result)
        return result

    def download_stage(self, origin, stage_id, destination, max_bytes, pin=None):
        f.need(set(self._prepared) == set(ORIGINS), 'both fixed prepares required')
        rows = [r for r in self.pins['stages'] if r['stage_id'] == stage_id and r['origin'] == origin]
        f.need(len(rows) == 1 and rows[0]['pin'] == pin and stage_id not in self._seen_stages,
               'unselected/repeated historical artifact or changed pin')
        f.need(max_bytes == ot.MAX_ARTIFACT_BYTES + ot.MAX_DESCRIPTOR_BYTES, 'stage transfer bound changed')
        path, metadata = self._download_fixed(origin, stage_id, destination,
                ['delta.tar', 'upload-candidate.json'], max_bytes, pin)
        raw = (path / 'upload-candidate.json').read_bytes()
        raw_sha = f.sha(raw)
        if origin == 'OldOrigin':
            f.need(raw_sha == pin['raw_descriptor_sha256'], 'original raw descriptor hash changed')
        descriptor = f.parse_json(raw)
        f.need(type(descriptor) is dict, 'native descriptor object required')
        raw_keys = (cp.NATIVE_KEYS - {'artifact_zip_sha256'}) | {'archive_path'}
        f.need(set(descriptor) == raw_keys and all(descriptor[k] is None for k in
               ('artifact_id', 'producer_job_id', 'producer_conclusion')) and
               type(descriptor['archive_path']) is str, 'native descriptor fields/placeholders changed')
        f.need(descriptor.get('schema') == 'fresh-stage-upload-candidate-v1' and descriptor.get('stage_id') == stage_id and
               descriptor.get('identity') == self._context(origin)['identity'] and
               descriptor.get('producer_job') == metadata['role']['producer_job'] and
               type(descriptor.get('retention_days')) is int and descriptor['retention_days'] == 7,
               'native descriptor identity/role mismatch')
        for field in ('archive_sha256', 'receipt_sha256'):
            ot.digest(descriptor.get(field), field)
        actual_bytes = (path / 'delta.tar').stat().st_size
        f.need(type(descriptor.get('archive_bytes')) is int and 0 < descriptor['archive_bytes'] <= ot.MAX_ARTIFACT_BYTES and
               descriptor['archive_bytes'] == actual_bytes and descriptor['archive_sha256'] == f.file_sha(path / 'delta.tar'),
               'native raw tar digest/size mismatch')
        if origin == 'OldOrigin':
            f.need(all(descriptor[k] == pin[k] for k in ('archive_sha256', 'archive_bytes', 'receipt_sha256')),
                   'original archive/receipt pins changed')
        descriptor.update(artifact_id=pin['artifact_id'], producer_job_id=pin['producer_job_id'],
                          producer_conclusion='success', artifact_zip_sha256=pin['artifact_zip_sha256'])
        descriptor.pop('archive_path', None)
        self._seen_stages.append(stage_id)
        return {'origin': origin, 'native_descriptor': descriptor, 'archive_path': str(path / 'delta.tar'),
                'authenticated_metadata': metadata, 'raw_descriptor_sha256': raw_sha}

    def download_final(self, *args, **kwargs):
        raise f.Rejected('historical admission transport cannot acquire final evidence')

    def reauthenticate_wrapper(self, wrapper, pin=None):
        origin = wrapper.get('origin')
        descriptor = wrapper.get('native_descriptor', {})
        rows = [r for r in self.pins['stages'] if r['origin'] == origin and r['stage_id'] == descriptor.get('stage_id')]
        f.need(len(rows) == 1 and rows[0]['pin'] == pin, 'reauthentication fixed selection mismatch')
        run = self._run(origin)
        self._verify_workflow_source(origin)
        job, binding = self._producer(origin, descriptor['stage_id'], run, pin)
        artifact = self._artifact(origin, descriptor['stage_id'], run, job, pin,
                                  ot.MAX_ARTIFACT_BYTES + ot.MAX_DESCRIPTOR_BYTES)
        metadata = self._metadata(origin, run, job, artifact, binding)
        f.need(metadata == wrapper['authenticated_metadata'], 'historical authenticated metadata changed')
        for other in ORIGINS:
            self._run(other)
        self._check_age()
        return metadata


def write_json(path, value):
    with Path(path).open('xb') as handle:
        handle.write(f.json_bytes(value))
        handle.flush()
        os.fsync(handle.fileno())


def copy_native_receipt(transport, wrapper):
    """Copy exact receipt bytes only; inspect strict USTAR headers without extracting objects.

    Semantic receipt/module/dependency validation remains entirely with the native
    adapter. This narrow reader rejects extensions/links/duplicate/traversal names
    and invalid padding rather than interpreting alternate archive formats.
    """
    path = Path(wrapper['archive_path'])
    destination = path.parent / 'receipt.json'
    descriptor = wrapper['native_descriptor']
    names, total, receipt_hash = set(), 0, None
    size = path.stat().st_size
    f.need(size % tarfile.RECORDSIZE == 0, 'native USTAR record size mismatch')
    with path.open('rb') as archive:
        while True:
            transport._check_age()
            header = archive.read(512)
            f.need(len(header) == 512, 'truncated USTAR header')
            if header == b'\0' * 512:
                remaining = size - archive.tell()
                f.need(remaining >= 512, 'missing USTAR end records')
                while remaining:
                    transport._check_age()
                    block = archive.read(min(1024**2, remaining))
                    f.need(block and not any(block), 'nonzero/truncated native USTAR end padding')
                    remaining -= len(block)
                break
            f.need(header[257:265] == b'ustar\x0000', 'native USTAR format required')
            try:
                member = tarfile.TarInfo.frombuf(header, 'utf-8', 'strict')
            except (tarfile.TarError, UnicodeError, ValueError):
                raise f.Rejected('invalid native USTAR header') from None
            name = f.safe_rel(member.name)
            f.need(member.isreg() and name not in names and not member.pax_headers,
                   'duplicate/nonregular native tar member')
            names.add(name)
            total += member.size
            f.need(0 <= member.size and len(names) <= 100000 and total <= ot.MAX_ARTIFACT_BYTES,
                   'native tar member count/byte bound')
            padded = ((member.size + 511) // 512) * 512
            f.need(archive.tell() + padded + 1024 <= size, 'native tar member beyond archive')
            if name == 'receipt.json':
                f.need(member.size > 0 and receipt_hash is None, 'missing/duplicate raw native receipt')
                disk_headroom(transport.root, member.size, new_files=2)
                h, remaining = hashlib.sha256(), member.size
                with destination.open('xb') as out:
                    while remaining:
                        transport._check_age()
                        block = archive.read(min(1024**2, remaining))
                        f.need(bool(block), 'truncated native receipt')
                        remaining -= len(block)
                        h.update(block)
                        out.write(block)
                    out.flush()
                    os.fsync(out.fileno())
                receipt_hash = h.hexdigest()
                padding = archive.read(padded - member.size)
                f.need(not any(padding), 'nonzero native receipt padding')
            else:
                archive.seek(padded, 1)
    f.need(receipt_hash == descriptor['receipt_sha256'], 'actual native receipt hash mismatch')
    f.need(f.file_sha(path) == descriptor['archive_sha256'], 'native archive changed during receipt copy')
    return destination


def retained_files(root):
    result = {}
    for path in sorted(Path(root).rglob('*')):
        info = path.lstat()
        f.need(not stat.S_ISLNK(info.st_mode), 'symlink in retained acquisition tree')
        if stat.S_ISDIR(info.st_mode):
            continue
        f.need(stat.S_ISREG(info.st_mode) and info.st_nlink == 1, 'nonregular/hardlinked retained acquisition file')
        result[path.relative_to(root).as_posix()] = {'bytes': info.st_size, 'sha256': f.file_sha(path)}
    return result


def acquire(output_root, token, *, deadline_monotonic=None, opener=None, now=None):
    """Acquire exact50 ZIPs (2 prepares + 48 stages), retain all48 native tars.

    Return only paths. TRANSPORT_RECEIPT is authenticated transport evidence,
    not semantic admission. The separate native adapter must validate all bytes.
    """
    root = owned_new_root(output_root)
    try:
        transport = HistoricalAcquisition(token, root, opener=opener, now=now,
                                          deadline_monotonic=deadline_monotonic)
        prepares, contexts = {}, {}
        for origin in ORIGINS:
            path = root / (origin + '-prepare')
            prepares[origin] = transport.authenticate_prepare(origin, path)
            outer = 'OldOrigin' if origin == 'OldOrigin' else 'PriorSuccessorOrigin'
            contexts[outer] = {'identity_path': (path / 'identity.json').relative_to(root).as_posix(),
                               'inventory_path': (path / 'inventory.json').relative_to(root).as_posix()}
        wrappers, output_rows, receipts = [], [], []
        for row in transport.pins['stages']:
            destination = root / (row['origin'] + '-' + row['stage_id'])
            wrapper = transport.download_stage(row['origin'], row['stage_id'], destination,
                        ot.MAX_ARTIFACT_BYTES + ot.MAX_DESCRIPTOR_BYTES, row['pin'])
            wrappers.append(wrapper)
            receipt_path = copy_native_receipt(transport, wrapper)
            outer_wrapper = copy.deepcopy(wrapper)
            if outer_wrapper['origin'] == 'CurrentOrigin':
                outer_wrapper['origin'] = 'PriorSuccessorOrigin'
            output_rows.append({'wrapper': outer_wrapper,
                                'raw_descriptor_path': str(destination / 'upload-candidate.json'),
                                'raw_receipt_path': str(receipt_path)})
            descriptor = wrapper['native_descriptor']
            derived_pin = dict(row['pin'])
            derived_pin.update({k: descriptor[k] for k in ('archive_bytes', 'archive_sha256', 'receipt_sha256')})
            derived_pin['raw_descriptor_sha256'] = wrapper['raw_descriptor_sha256']
            receipts.append({'stage_id': row['stage_id'], 'historical_origin': row['historical_origin'],
                             'native_validator_origin': row['origin'], 'pin': derived_pin,
                             'receipt_hash_status': 'exact raw native bytes authenticated; semantic validation pending'})
        f.need(len(wrappers) == 48 and transport.raw_bytes == sum(w['native_descriptor']['archive_bytes'] for w in wrappers),
               'exact48 shared raw accounting mismatch')
        for row, wrapper in zip(transport.pins['stages'], wrappers):
            transport.reauthenticate_wrapper(wrapper, row['pin'])
        for origin in ORIGINS:
            run = transport._run(origin)
            pin = transport.contexts[origin]['prepare']
            job, binding = transport._producer(origin, 'prepare', run, pin)
            artifact = transport._artifact(origin, 'prepare', run, job, pin, MAX_PREPARE)
            f.need(transport._metadata(origin, run, job, artifact, binding) == prepares[origin]['authenticated_metadata'],
                   'authenticated prepare metadata changed before certificate')
        disk_headroom(root, 8 * ot.MAX_METADATA_BYTES, new_files=4)
        write_json(root / 'WRAPPERS.json', output_rows)
        write_json(root / 'AUTHENTICATED_PREPARES.json', prepares)
        certificate = {'schema': 'historical-origin-acquisition-v1',
                       'status': 'transport_bytes_authenticated_only', 'proof_pass_claimed': False,
                       'semantic_admission': False, 'proof_execution': False, 'final_gate_evidence': False,
                       'acquisition_spec_sha256': PINS_SHA256, 'original_deadline_utc': DEADLINE,
                       'whole48_raw_archive_bytes': transport.raw_bytes, 'whole48_raw_archive_cap': RAW_CAP,
                       'contexts': contexts, 'wrappers_path': 'WRAPPERS.json',
                       'terminal_contexts': {origin: {'historical_origin': HISTORICAL_NAMES[origin],
                                   'native_validator_origin': origin, 'run_id': transport.contexts[origin]['identity']['run_id'],
                                   'run_attempt': 1, 'status': 'completed', 'conclusion': 'failure',
                                   'prepare': prepares[origin]} for origin in ORIGINS},
                       'stages': receipts, 'files': retained_files(root)}
        transport._check_age()
        write_json(root / 'TRANSPORT_RECEIPT.json', certificate)
        return {'root': str(root), 'wrappers_path': str(root / 'WRAPPERS.json'),
                'transport_receipt_path': str(root / 'TRANSPORT_RECEIPT.json'),
                'authenticated_prepares_path': str(root / 'AUTHENTICATED_PREPARES.json')}
    except BaseException:
        # Entire root was created exclusively by this call. Never delete its parent.
        try:
            shutil.rmtree(root)
        except Exception:
            raise f.Rejected('owned acquisition quarantine cleanup failed') from None
        raise


def require_runtime_envelope():
    f.need(sys.platform == 'linux' and os.environ.get('GITHUB_ACTIONS') == 'true' and
           os.environ.get('GITHUB_REPOSITORY') == ot.REPOSITORY, 'reviewed standard Actions context required')
    f.need(len(os.sched_getaffinity(0)) == 1, 'one-CPU affinity required from integrated driver')
    for limit in (resource.RLIMIT_AS, resource.RLIMIT_RSS):
        soft, hard = resource.getrlimit(limit)
        f.need(0 < soft <= MEMORY_CAP and 0 < hard <= MEMORY_CAP, '8 GiB AS/RSS bound required from integrated driver')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--quarantine', required=True)
    parser.add_argument('--deadline-monotonic', required=True, type=float)
    args = parser.parse_args()
    require_runtime_envelope()
    result = acquire(args.quarantine, os.environ.get('GH_TOKEN', ''), deadline_monotonic=args.deadline_monotonic)
    # Deliberately no token, signed storage URL, or object repr in diagnostics.
    print('Authenticated historical transport: 48 stages; native semantic validation still required.')
    return result


if __name__ == '__main__':
    try:
        main()
    except SystemExit:
        raise
    except BaseException:
        print('Historical acquisition failed closed; no semantic or proof verdict.', file=sys.stderr)
        sys.exit(1)
