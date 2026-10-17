"""Strict local consumer of a certificate already authenticated by the parent.

Hash agreement is binding, not authentication. Only the separately reviewed
parent acquisition flow may supply its trusted hash/session/deadline arguments.
This module performs no network work and creates no executable authority.
"""
from __future__ import annotations
import copy
from datetime import datetime, timezone
import math
from pathlib import Path, PurePosixPath
import re
import time
from frozen_native import GRAPH
if GRAPH is None:
    raise RuntimeError("call frozen_native.load_frozen_graph(canonical_root) before importing certificate code")

p, f, transfer = GRAPH.p, GRAPH.f, GRAPH.transfer
RUN = 38978663241
PIPELINE = 'bc3f977237bee905dafb4f13eeb6564a4a338b42'
SOURCE = '5d0612a09e3b7d440be16e7b1dc511ae73035bbb'
CONTRACT = '2848fad58bf59da1958c7e1632e841c1bae78f22ab728b1098a9426977aef334'
WORKFLOW = 387046066
LATEST_IDENTITY_SHA256 = '4f8be12f1e9e851917e69e60957136c5e3e60ac5e1e00284ce1111692b4da3a5'
ORIGINAL_DEADLINE = '2026-10-22T06:15:54Z'
GLOBAL_RAW = 3009576960
SELECTED_RAW = 3008552960
ACQUISITION_SPEC_SHA256 = '9c77059b0a48a300e6ae9be0c826812057d0305a61c444736c246389d52b9b80'
DOWNLOADER_SHA256 = 'b33959f460cb73992dfbdd86a5ab7a073f64277e2b0c28b135e640fa5a94f3ee'
ROOT_KEYS = {'schema','status','proof_pass_claimed','semantic_admission','session_nonce',
 'host_deadline_monotonic','started_at_utc','authenticated_at_utc','original_deadline_utc',
 'acquisition_spec_sha256','downloader_sha256','inputs','scope','accounting','contexts',
 'wrappers_path','wrappers','stages','files'}
INPUT_KEYS = {'accounting_sha256','accounting_review_sha256','latest_driver_sha256',
 'latest_selection_sha256','context_bundle_sha256','latest_contract_sha256'}
CONTEXT_KEYS = {'native_origin','identity','identity_path','identity_raw_sha256',
 'identity_canonical_sha256','inventory_path','inventory_sha256','run','workflow','prepare'}
STAGE_KEYS = {'stage_id','origin','native_origin','pin','raw_descriptor','raw_receipt','archive'}
RUN_KEYS = {'id','run_attempt','head_sha','event','created_at','workflow_id','path','head_branch','repository','head_repository','status','conclusion'}
JOB_KEYS = {'id','name','run_id','run_attempt','head_sha','status','conclusion','started_at','completed_at','steps'}
ARTIFACT_KEYS = {'id','name','size_in_bytes','digest','expired','created_at','expires_at','workflow_run'}
STEP_KEYS = {'number','name','status','conclusion','started_at','completed_at'}
ORIGINS = {'OldOrigin':'OldOrigin','PriorSuccessorOrigin':'PriorSuccessorOrigin','LatestSuccessorOrigin':'CurrentOrigin'}

def exact_value(value, expected):
    if type(value) is not type(expected):
        return False
    if type(value) is dict:
        return set(value) == set(expected) and all(exact_value(value[k], expected[k]) for k in value)
    if type(value) in (list, tuple):
        return len(value) == len(expected) and all(exact_value(a,b) for a,b in zip(value,expected))
    return value == expected


def require(value, expected, label):
    p.need(exact_value(value, expected), label + ' changed or wrong type')

def retained_path(root, name):
    p.need(type(name) is str and bool(name) and '\\' not in name and '\x00' not in name,
           'retained relative path required')
    rel = PurePosixPath(name)
    p.need(not rel.is_absolute() and str(rel) == name and all(x not in ('.','..') for x in rel.parts),
           'unsafe retained path')
    return transfer.canonical(str(root/name))

def pin_file(root, entry):
    p.keys(entry, {'path','bytes','sha256'}, 'retained file entry')
    p.integer(entry['bytes'], 'retained byte count', maximum=4*1024**3, minimum=0)
    p.digest(entry['sha256'])
    path = retained_path(root, entry['path'])
    p.need(transfer.info(path) == {k:entry[k] for k in ('bytes','sha256')}, 'retained bytes changed')
    return path

def validate_wrapper_rows(root, wrappers_path, wrappers, stages):
    """Consume the downloader's exact retained row wire format, without rewriting."""
    wrapper_rows = p.parse_json(retained_path(root, wrappers_path).read_bytes())
    p.need(type(wrapper_rows) is list and len(wrapper_rows) == len(wrappers) == len(stages),
           'retained wrapper row count')
    for row, wrapper, entry in zip(wrapper_rows, wrappers, stages):
        p.keys(row, {'wrapper','raw_descriptor_path','raw_receipt_path'}, 'retained wrapper row')
        require(row['wrapper'], wrapper, 'retained wrapper bytes')
        require(row['raw_descriptor_path'], str(retained_path(root, entry['raw_descriptor']['path'])), 'raw descriptor row path')
        require(row['raw_receipt_path'], str(retained_path(root, entry['raw_receipt']['path'])), 'raw receipt row path')

def validate_producer_metadata(meta, identity, *, role, workflow):
    p.keys(meta, {'run','job','artifact','role'}, 'authenticated producer metadata')
    run, job, artifact, mapping = (meta[x] for x in ('run','job','artifact','role'))
    p.keys(run, RUN_KEYS, 'native run metadata')
    p.keys(job, JOB_KEYS, 'native job metadata')
    p.keys(artifact, ARTIFACT_KEYS, 'native artifact metadata')
    require(run.get('status'), 'completed', 'producer terminal run status')
    require(run.get('conclusion'), 'failure', 'producer terminal run conclusion')
    require(run.get('id'), int(identity['run_id']), 'producer run ID')
    require(run.get('run_attempt'), int(identity['run_attempt']), 'producer run attempt')
    require(run.get('head_sha'), identity['pipeline_commit'], 'producer pipeline')
    require(run.get('event'), 'push', 'native run event')
    require(run.get('created_at'), identity['run_started_at'], 'native original start')
    for key in ('repository','head_repository'):
        require(run.get(key), {'id':p.REPOSITORY_ID,'full_name':p.REPOSITORY}, 'native repository')
        require(run[key]['id'], p.REPOSITORY_ID, 'repository numeric ID')
    if identity['run_id'] == str(RUN):
        require(run.get('workflow_id'), WORKFLOW, 'producer workflow ID')
        require(run.get('path'), '.github/workflows/hierarchy-c-three-context.yml', 'producer workflow path')
        require(run.get('head_branch'), 'verify/hierarchy-c-three-context-20261016', 'producer branch')
    p.integer(job.get('id'), 'producer job ID')
    require(job.get('run_id'), int(identity['run_id']), 'producer job run')
    require(job.get('run_attempt'), int(identity['run_attempt']), 'producer job attempt')
    require(job.get('status'), 'completed', 'producer status')
    require(job.get('conclusion'), 'success', 'producer conclusion')
    require(job.get('head_sha'), identity['pipeline_commit'], 'producer head SHA')
    p.keys(mapping, {'producer_job','job_name','verifier_step','upload_step','upload_locations'}, 'producer role')
    require(mapping, workflow['roles'][role], 'exact pinned producer role mapping')
    require(mapping['upload_locations'], 1, 'unique upload location')
    require(job.get('name'), mapping['job_name'], 'producer job name')
    if role != 'prepare':
        require(job['name'], 'stage '+role, 'stage producer name')
    steps = job.get('steps')
    p.need(type(steps) is list and len(steps) == 2 and all(type(x) is dict for x in steps), 'exact verifier/upload steps required')
    for step in steps:
        p.keys(step, STEP_KEYS, 'native producer step')
    numbers = [x.get('number') for x in steps]
    p.need(all(type(x) is int and x > 0 for x in numbers) and len(set(numbers)) == len(numbers), 'duplicate/Boolean step number')
    for key in ('verifier_step','upload_step'):
        expected = mapping[key]
        p.keys(expected, {'number','name'}, 'producer step mapping')
        p.integer(expected['number'], 'mapped step number')
        matches = [x for x in steps if x['number'] == expected['number'] or x.get('name') == expected['name']]
        p.need(len(matches) == 1 and matches[0]['number'] == expected['number'] and matches[0].get('name') == expected['name'], 'ambiguous producer step')
        require(matches[0].get('status'), 'completed', 'producer step status')
        require(matches[0].get('conclusion'), 'success', 'producer step conclusion')
    p.need(mapping['verifier_step']['number'] < mapping['upload_step']['number'], 'verifier/upload order')
    require(artifact.get('expired'), False, 'artifact expired')
    p.integer(artifact.get('id'), 'artifact ID')
    p.integer(artifact.get('size_in_bytes'), 'artifact ZIP bytes')
    require(artifact.get('name'), 'hierarchy-c-'+identity['run_id']+'-'+identity['run_attempt']+'-'+role, 'artifact role name')
    p.need(type(artifact.get('digest')) is str and re.fullmatch('sha256:[0-9a-f]{64}', artifact['digest']), 'artifact digest')
    workflow = artifact.get('workflow_run')
    p.keys(workflow, {'id','head_sha','head_branch','repository_id','head_repository_id'}, 'artifact workflow')
    for key, value in {'id':int(identity['run_id']),'head_sha':identity['pipeline_commit'],
                       'repository_id':p.REPOSITORY_ID,'head_repository_id':p.REPOSITORY_ID}.items():
        require(workflow.get(key), value, 'artifact workflow '+key)
    p.timestamp(artifact.get('expires_at'))
    return artifact['expires_at']


class TerminalCertificate:
    def __init__(self, *, raw, parent_sha256, expected_session_nonce, acquisition_root,
                 host_deadline_monotonic, identity, inventory, selection, bundle,
                 plan, wrappers, native_bytes):
        p.digest(parent_sha256, 'parent certificate SHA')
        p.need(type(raw) is bytes and len(raw) <= 64*1024**2 and p.sha(raw) == parent_sha256,
               'parent-authenticated certificate bytes changed')
        p.need(type(expected_session_nonce) is str and re.fullmatch('[0-9a-f]{64}', expected_session_nonce),
               'parent session nonce required')
        c = p.parse_json(raw)
        p.keys(c, ROOT_KEYS, 'acquisition certificate')
        require(c['schema'], 'c087-historical-acquisition-v1', 'certificate schema')
        require(c['status'], 'transport_bytes_authenticated_only', 'certificate status')
        require(c['proof_pass_claimed'], False, 'proof claim')
        require(c['semantic_admission'], False, 'semantic claim')
        require(c['session_nonce'], expected_session_nonce, 'parent session')
        p.need(type(host_deadline_monotonic) is float and math.isfinite(host_deadline_monotonic),
               'original absolute host deadline must be a finite float')
        require(c['host_deadline_monotonic'], host_deadline_monotonic, 'original absolute host deadline')
        require(c['original_deadline_utc'], ORIGINAL_DEADLINE, 'original wall deadline')
        for field in ('acquisition_spec_sha256','downloader_sha256'):
            p.digest(c[field], field)
        require(c['acquisition_spec_sha256'], ACQUISITION_SPEC_SHA256, 'frozen acquisition specification')
        require(c['downloader_sha256'], DOWNLOADER_SHA256, 'frozen downloader')
        p.keys(c['inputs'], INPUT_KEYS, 'certificate inputs')
        for field, value in c['inputs'].items():
            p.digest(value, field)
        require(c['inputs']['latest_contract_sha256'], CONTRACT, 'native contract pin')
        require(c['inputs']['latest_driver_sha256'], GRAPH.pins['files']['ci/three_context_driver.py']['sha256'], 'latest driver pin')
        require(c['inputs']['latest_selection_sha256'], selection.raw_sha256, 'native selection')
        require(c['inputs']['context_bundle_sha256'], bundle.raw_sha256, 'native context bundle')
        p.keys(c['scope'], {'target_stage','predecessor_stage_ids','module_count'}, 'C087 scope')
        stages = {s['stage_id']:s for s in plan['stages']}
        expected = stages['build_087']['required_predecessors']
        require(c['scope']['target_stage'], 'build_087', 'target')
        require(c['scope']['predecessor_stage_ids'], expected, 'ordered predecessor scope')
        require(len(expected), 85, 'predecessor count')
        require(c['scope']['module_count'], 6218, 'predecessor module count')
        require(sum(len(stages[s]['modules']) for s in expected), 6218, 'plan module count')
        p.keys(c['contexts'], set(ORIGINS), 'terminal contexts')
        self.root = transfer.canonical(str(acquisition_root))
        transfer.owned_dir(self.root)
        self.raw = raw
        self.sha256 = parent_sha256
        self.data = copy.deepcopy(c)
        self.expiries = []
        self.last_wall = None
        self.file_pins = copy.deepcopy(c['files'])
        p.need(type(self.file_pins) is dict and self.file_pins, 'retained full file inventory required')
        self.rehash()
        require(self.file_pins.get('ACQUISITION_SPEC.json', {}).get('sha256'), c['acquisition_spec_sha256'], 'retained acquisition specification')
        for origin, context in c['contexts'].items():
            p.keys(context, CONTEXT_KEYS, 'terminal context')
            require(context['native_origin'], ORIGINS[origin], 'native origin mapping')
            ci = context['identity']
            expected_identity = identity if origin == 'LatestSuccessorOrigin' else bundle.context(origin)['identity']
            require(ci, expected_identity, 'immutable native identity')
            ipath = retained_path(self.root, context['identity_path'])
            p.need(self.file_pins.get(context['identity_path'], {}).get('bytes', 32*1024**2+1) <= 32*1024**2, 'prepare identity size bound')
            iraw = ipath.read_bytes()
            require(p.sha(iraw), context['identity_raw_sha256'], 'raw prepare identity')
            require(p.parse_json(iraw), ci, 'prepare identity bytes')
            require(p.object_sha(ci), context['identity_canonical_sha256'], 'canonical prepare identity')
            p.need(self.file_pins.get(context['inventory_path'], {}).get('bytes', 32*1024**2+1) <= 32*1024**2, 'inventory JSON size bound')
            invraw = retained_path(self.root, context['inventory_path']).read_bytes()
            require(p.sha(invraw), context['inventory_sha256'], 'raw inventory')
            require(p.parse_json(invraw), inventory, 'unchanged inventory')
            require(p.object_sha(inventory), ci['toolchain_inventory_sha256'], 'identity inventory binding')
            for path in (context['identity_path'], context['inventory_path']):
                p.need(path in self.file_pins, 'prepare file absent from retained inventory')
            run = context['run']
            p.keys(run, RUN_KEYS | {'name','updated_at'}, 'terminal run snapshot')
            require(run.get('status'), 'completed', 'terminal run status')
            require(run.get('conclusion'), 'failure', 'terminal run conclusion')
            require(run.get('id'), int(ci['run_id']), 'terminal run ID')
            require(run.get('run_attempt'), int(ci['run_attempt']), 'terminal attempt')
            require(run.get('head_sha'), ci['pipeline_commit'], 'terminal pipeline')
            p.keys(context['prepare'], {'pin','authenticated_metadata'}, 'authenticated prepare')
            self.expiries.append(validate_producer_metadata(context['prepare']['authenticated_metadata'], ci, role='prepare', workflow=context['workflow']))
            require({k:run[k] for k in RUN_KEYS}, context['prepare']['authenticated_metadata']['run'], 'context/prepare run equality')
            require(run['name'], context['workflow']['name'], 'context workflow name')
            p.need(p.timestamp(run['created_at']) <= p.timestamp(run['updated_at']) <= p.timestamp(c['authenticated_at_utc']), 'terminal run chronology')
            prepare = context['prepare']['pin']
            p.keys(prepare, {'artifact_id','producer_job_id','artifact_name','artifact_zip_sha256',
                            'artifact_zip_bytes','identity_sha256','inventory_sha256','expires_at'}, 'prepare pin')
            meta = context['prepare']['authenticated_metadata']
            bindings = {'artifact_id':meta['artifact']['id'],'producer_job_id':meta['job']['id'],
                        'artifact_name':meta['artifact']['name'],'artifact_zip_bytes':meta['artifact']['size_in_bytes'],
                        'identity_sha256':p.sha(iraw),'inventory_sha256':p.sha(invraw),
                        'expires_at':meta['artifact']['expires_at']}
            for field, expected_value in bindings.items():
                require(prepare[field], expected_value, 'prepare binding '+field)
            p.digest(prepare['artifact_zip_sha256'])
            require(meta['artifact']['digest'], 'sha256:'+prepare['artifact_zip_sha256'], 'prepare ZIP digest')
            GRAPH.loaded['three_context_current_transport'].base.validate_workflow(context['workflow'])
            if origin != 'LatestSuccessorOrigin':
                require(context['workflow'], bundle.context(origin)['workflow'], 'historical workflow')
                require(prepare, bundle.context(origin)['prepare'], 'historical prepare pin')
            if origin == 'LatestSuccessorOrigin':
                for field, value in {'run_id':str(RUN),'run_attempt':'1','pipeline_commit':PIPELINE,
                                     'source_commit':SOURCE,'contract_sha256':CONTRACT}.items():
                    require(ci.get(field), value, 'latest identity '+field)
                require(p.object_sha(ci), LATEST_IDENTITY_SHA256, 'latest complete native identity')
                require(ci['run_started_at'], '2026-10-16T22:56:24Z', 'latest original start')
                require(run.get('workflow_id'), WORKFLOW, 'latest workflow')
                expected_workflow = p.parse_json((GRAPH.root/'ci/three_context_contract.json').read_bytes())['current_workflow']
                expected_workflow['workflow_id'] = WORKFLOW
                expected_workflow['source_sha256'] = GRAPH.pins['files']['.github/workflows/hierarchy-c-three-context.yml']['sha256']
                require(context['workflow'], expected_workflow, 'complete latest frozen workflow role/source mapping')
                require(context['workflow']['workflow_id'], WORKFLOW, 'latest workflow manifest ID')
                for key, value in GRAPH.loaded['three_context_current_transport'].FIXED_WORKFLOW.items():
                    require(context['workflow'].get(key), value, 'latest reviewed workflow '+key)
                require(run.get('path'), '.github/workflows/hierarchy-c-three-context.yml', 'latest workflow path')
        require(c['wrappers'], wrappers, 'certificate wrappers')
        p.need(type(c['stages']) is list and [x.get('stage_id') for x in c['stages']] == expected,
               'exact ordered retained stages required')
        validate_wrapper_rows(self.root, c['wrappers_path'], wrappers, c['stages'])
        p.need(c['wrappers_path'] in self.file_pins, 'wrapper file absent from inventory')
        self.native_wrappers = copy.deepcopy(wrappers)
        latest_raw = historical_raw = 0
        for index, entry in enumerate(c['stages']):
            p.keys(entry, STAGE_KEYS, 'retained stage')
            wrapper = wrappers[index]
            sid = entry['stage_id']
            require(entry['origin'], wrapper['origin'], 'stage origin')
            p.need(entry['origin'] in ORIGINS, 'unknown acquired origin')
            require(entry['native_origin'], ORIGINS[entry['origin']], 'native stage origin')
            self.native_wrappers[index]['origin'] = entry['native_origin']
            d = wrapper['native_descriptor']
            require(d['identity'], c['contexts'][entry['origin']]['identity'], 'stage immutable identity')
            self.expiries.append(validate_producer_metadata(wrapper['authenticated_metadata'], d['identity'], role=sid, workflow=c['contexts'][entry['origin']]['workflow']))
            for key, byte_key in (('raw_descriptor','descriptor'),('raw_receipt','receipt')):
                path = pin_file(self.root, entry[key])
                require(path.read_bytes(), native_bytes[sid][byte_key], 'exact raw native '+byte_key)
                p.need(entry[key]['path'] in self.file_pins, 'native file absent from inventory')
            apath = pin_file(self.root, entry['archive'])
            require(str(apath), wrapper['archive_path'], 'retained native tar path')
            require(entry['archive']['sha256'], d['archive_sha256'], 'retained native tar digest')
            require(entry['archive']['bytes'], d['archive_bytes'], 'retained native tar bytes')
            p.keys(entry['pin'], p.PIN_KEYS, 'native payload pin')
            for key in ('archive_sha256','archive_bytes','receipt_sha256','artifact_id','producer_job_id','artifact_zip_sha256'):
                require(entry['pin'][key], d[key], 'native pin '+key)
            require(entry['pin']['raw_descriptor_sha256'], wrapper['raw_descriptor_sha256'], 'raw descriptor pin')
            require(entry['pin']['identity_sha256'], p.object_sha(d['identity']), 'native identity pin')
            meta = wrapper['authenticated_metadata']
            require(entry['pin']['artifact_name'], meta['artifact']['name'], 'native artifact name pin')
            require(entry['pin']['artifact_zip_bytes'], meta['artifact']['size_in_bytes'], 'native ZIP size pin')
            require(entry['pin']['expires_at'], meta['artifact']['expires_at'], 'native expiry pin')
            p.need(entry['archive']['path'] in self.file_pins, 'native tar absent from inventory')
            if entry['origin'] == 'LatestSuccessorOrigin':
                latest_raw += d['archive_bytes']
            else:
                historical_raw += d['archive_bytes']
        require(sum(w['origin'] == 'CurrentOrigin' for w in self.native_wrappers), 38, 'latest selected count')
        require(sum(w['origin'] != 'CurrentOrigin' for w in self.native_wrappers), 47, 'historical selected count')
        require(historical_raw, SELECTED_RAW, 'selected historical raw ledger')
        expected_accounting = {'historical_global_raw_bytes':GLOBAL_RAW,'historical_selected_raw_bytes':SELECTED_RAW,
          'historical_unrestored_raw_bytes':1024000,'latest_raw_bytes':latest_raw,
          'selected_raw_bytes':SELECTED_RAW+latest_raw,'charged_raw_bytes':GLOBAL_RAW+latest_raw,
          'aggregate_cap_bytes':4294967296}
        require(c['accounting'], expected_accounting, 'full48 raw ledger')
        p.need(all(type(x) is int for x in c['accounting'].values()), 'Boolean/floating raw ledger rejected')
        p.need(GLOBAL_RAW+latest_raw <= p.MAX_RESTORED, 'global raw cap exceeded')
        self.check_age()

    def rehash(self):
        require(self.data, p.parse_json(self.raw), 'certificate in-memory view')
        require(self.file_pins, self.data['files'], 'certificate retained file pin view')
        for name, pin in self.file_pins.items():
            p.need(time.monotonic() < self.data['host_deadline_monotonic'], 'shared host deadline exceeded while hashing')
            p.keys(pin, {'bytes','sha256'}, 'retained inventory file')
            p.integer(pin['bytes'], 'retained file size', maximum=4*1024**3, minimum=0)
            p.digest(pin['sha256'])
            p.need(transfer.info(retained_path(self.root, name)) == pin, 'retained acquisition file changed')
            p.need(time.monotonic() < self.data['host_deadline_monotonic'], 'shared host deadline exceeded after hashing')

    def check_age(self):
        require(p.sha(self.raw), self.sha256, 'certificate raw bytes')
        require(self.data, p.parse_json(self.raw), 'certificate in-memory view')
        require(self.file_pins, self.data['files'], 'certificate retained file pin view')
        expected_expiries = [ctx['prepare']['authenticated_metadata']['artifact']['expires_at']
                             for ctx in self.data['contexts'].values()]
        expected_expiries += [w['authenticated_metadata']['artifact']['expires_at'] for w in self.data['wrappers']]
        require(self.expiries, expected_expiries, 'certificate artifact expiry view')
        expected_wrappers = copy.deepcopy(self.data['wrappers'])
        for wrapper in expected_wrappers:
            wrapper['origin'] = ORIGINS[wrapper['origin']]
        require(self.native_wrappers, expected_wrappers, 'certificate native wrapper view')
        p.need(time.monotonic() < self.data['host_deadline_monotonic'], 'shared host deadline exceeded')
        now = datetime.now(timezone.utc)
        start = p.timestamp(self.data['started_at_utc'])
        acquired = p.timestamp(self.data['authenticated_at_utc'])
        p.need(start <= acquired <= now < p.timestamp(ORIGINAL_DEADLINE), 'certificate chronology/deadline')
        p.need(self.last_wall is None or now >= self.last_wall, 'backward wall clock')
        for expiry in self.expiries:
            p.need(now < p.timestamp(expiry), 'retained native artifact expired')
        self.last_wall = now
