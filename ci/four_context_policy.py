"""Inactive, fixed four-context policy; pure stdlib, no I/O or execution.

This module checks supplied immutable facts. It does not authenticate a download,
perform semantic payload admission, authorize publication, or run a proof. The
historical native validators remain separately frozen and must still be invoked.
"""
from __future__ import annotations
from dataclasses import dataclass
from datetime import datetime, timezone, timedelta
import copy
import hashlib
import json
import re

ORIGINS = ('OldOrigin', 'PriorSuccessorOrigin', 'LatestSuccessorOrigin', 'ProductionSuccessOrigin', 'CurrentOrigin')
RANK = dict(zip(ORIGINS, range(5)))
OLD_RUN = 38860226136
PRIOR_RUN = 38917565694
LATEST_RUN = 38978663241
EXCLUDED_RUN = 38911944324
REPOSITORY = 'jconorgrogan/palomar-chair-verification'
REPOSITORY_ID = 1407290933
OLD_PIPELINE = 'f8c7028dd80232ac522b7cf223052921fca396fa'
PRIOR_PIPELINE = 'fca406f6c52a622762d9c75167a92f895c3ddd00'
OLD_SOURCE = '4a0cbd71ba9cd318620e11694037d956d2393d06'
PRIOR_SOURCE = '5d0612a09e3b7d440be16e7b1dc511ae73035bbb'
PLAN_SHA256 = 'c25336bffaf3ada115c7642840675f445cc3cef145fa1d70e9eec8988567a7ed'
OLD_MANIFEST = '401320e96ea5a511678892c359af43131fae75494a55d8ea1df0e1dc606a326f'
PRIOR_MANIFEST = '09b0371c9acc07b07355824e7a7302a810c4247bbbce20d1e497bd4a02a23392'
SOURCE_DELTA = '12541d2a57fac6c4e6a2e36e849d1bf400d284f968d77c2d43580d40aa7696ef'
OLD_IDENTITY = '1838d66b59cf9ce277f72a2dbd9ec1698296a8d5e64334e981496cdc2b910560'
PRIOR_IDENTITY = '287e19a82589415db3897697c1a5941f7c20cb1b885a4404d3ebb49cb7878bdb'
BUNDLE_SHA256 = '63b8cafcb76e03adf699582d036d34e751968c54023e8964cb19bea7edd770b5'
LATEST_CONTEXT_SHA256 = 'edf6e668761c00adb09423c045b14d1f40749b61e91273a77778020367c06258'
LATEST_ROWS_SHA256 = '2d220c38582d08ff9c2ff16cacd674ba4d2d6fdeb57e252b29e223a341a82aea'
LATEST_PIPELINE = 'bc3f977237bee905dafb4f13eeb6564a4a338b42'
LATEST_IDENTITY = '4f8be12f1e9e851917e69e60957136c5e3e60ac5e1e00284ce1111692b4da3a5'
CURRENT_PROFILES = '991c8f91fbe22278945f423c6c2318a8a1d4f7cd4765dd95ab5856e6ecec32ad'
PRODUCTION_RUN = 39089923663
PRODUCTION_PIPELINE = 'acc99d32b312655d8b526925a7addaab44260551'
PRODUCTION_CONTRACT = 'fae0247cccf29a9b43bd85e86b52e8c83e1a0a1dbcd29c3028d88e6ab3eed9af'
PRODUCTION_PROFILES = '770ccc2c5af5185e550432b678220f10d5981a77f3d3b2dc231fc755efb934dc'
PRODUCTION_IDENTITY = '19a6fb1d2c5c13a06b17b10b74b47f85173baee0ec94d5420312d5ea88da0a76'
PRODUCTION_CONTEXT_SHA256 = '2b8d77178cba28850159393660db804df18ab98795dd1a869da842cd06f6f00d'
PRODUCTION_ROWS_SHA256 = '935d97884b76acdbf8984315cf956c851811a9ec0026e01bda079d0048d99ec2'
PRODUCTION_STAGES = frozenset({'build_087'})
CURRENT_STAGES = frozenset({'build_091', 'build_092'})
OLD_CONTEXT_SHA256 = '36f8a1b1fd943b6e665b805ec49f07b782829fff74415cd4f2e4174c9ffa96f8'
PRIOR_CONTEXT_SHA256 = 'e062f4c9072ef0d0f30cc6260e7830adc4fbf1b60a2b522253c00e9be13fe338'
OLD_ROWS_SHA256 = '5ebe74caf7824058b5201fee805cc5dba7db8fa83b8ce992bcefeeb96df53495'
PRIOR_ROWS_SHA256 = '78b2f89c2676b6f952f0ec007c2327522a183a2def64e7cf334b144452cd4a1a'
OLD_STAGES = frozenset([f'build_{i:03}' for i in range(36)] + ['build_055'])
PRIOR_CANDIDATES = frozenset([f'build_{i:03}' for i in range(36,43)] + ['build_049','build_051','build_054','build_056'])
LATEST_STAGES = frozenset(f'build_{i:03}' for i in range(93)) - OLD_STAGES - PRIOR_CANDIDATES - PRODUCTION_STAGES - CURRENT_STAGES
MAX_AGE = 518400
MAX_ARTIFACT = 1024**3
MAX_RESTORED = 4*1024**3
ORIGINAL_RAW_BYTES = 1861550080
SUFFIXES = ('.olean', '.olean.private', '.olean.server', '.ilean', '.ir', '.ir.sig')
PAYLOAD_KEYS = frozenset({'archive_sha256','archive_bytes','receipt_sha256','raw_descriptor_sha256'})
PIN_KEYS = PAYLOAD_KEYS | {'artifact_id','producer_job_id','artifact_name','artifact_zip_sha256','artifact_zip_bytes','expires_at','identity_sha256'}
NATIVE_KEYS = {'schema','stage_id','producer_job','identity','archive_sha256','receipt_sha256','archive_bytes','artifact_id','producer_job_id','producer_conclusion','retention_days','artifact_zip_sha256'}
WRAPPER_KEYS = {'origin','native_descriptor','archive_path','authenticated_metadata','raw_descriptor_sha256'}

class Rejected(ValueError):
    """A fail-closed policy or evidence boundary rejection."""

def need(test, message):
    if not test: raise Rejected(message)

def json_bytes(value):
    return (json.dumps(value, sort_keys=True, indent=2, allow_nan=False)+'\n').encode()

def sha(data):
    need(type(data) is bytes, 'hash input must be exact bytes')
    return hashlib.sha256(data).hexdigest()

def object_sha(value): return sha(json_bytes(value))

def keys(value, expected, label):
    need(type(value) is dict and set(value)==set(expected), 'unknown/missing '+label+' fields')

def digest(value, label='digest'):
    need(type(value) is str and re.fullmatch(r'[0-9a-f]{64}',value) is not None, 'invalid '+label)

def integer(value,label,maximum=2**63-1,minimum=1):
    need(type(value) is int and minimum<=value<=maximum, 'invalid '+label)

def parse_json(data):
    need(type(data) is bytes and len(data)<=32*1024**2, 'JSON byte bound/type')
    def pairs(items):
        result={}
        for k,v in items:
            need(k not in result,'duplicate JSON key');result[k]=v
        return result
    def constant(_): raise Rejected('nonfinite JSON number')
    try: return json.loads(data,object_pairs_hook=pairs,parse_constant=constant)
    except (UnicodeError,json.JSONDecodeError,RecursionError) as e: raise Rejected('invalid JSON') from e

def timestamp(value):
    need(type(value) is str,'timestamp type')
    try: result=datetime.fromisoformat(value.replace('Z','+00:00'))
    except (ValueError,OverflowError) as e: raise Rejected('invalid timestamp') from e
    need(result.tzinfo is not None,'timestamp timezone missing')
    return result.astimezone(timezone.utc)

@dataclass(frozen=True)
class ContextBundle:
    raw_bytes: bytes
    @property
    def raw_sha256(self): return sha(self.raw_bytes)
    @property
    def data(self): return parse_json(self.raw_bytes)
    @property
    def old_context(self): return self.data['contexts']['OldOrigin']
    @property
    def prior_context(self): return self.data['contexts']['PriorSuccessorOrigin']
    @property
    def latest_context(self): return self.data['contexts']['LatestSuccessorOrigin']
    @property
    def production_context(self): return self.data['contexts']['ProductionSuccessOrigin']
    def context(self, origin):
        need(origin in ORIGINS,'unknown context');return self.data['contexts'][origin]

@dataclass(frozen=True)
class OldOrigin:
    stage_id: str
    pin_bytes: bytes
    @property
    def pin(self): return parse_json(self.pin_bytes)

@dataclass(frozen=True)
class PriorSuccessorOrigin:
    stage_id: str
    pin_bytes: bytes
    @property
    def pin(self): return parse_json(self.pin_bytes)

@dataclass(frozen=True)
class LatestSuccessorOrigin:
    stage_id: str
    pin_bytes: bytes
    @property
    def pin(self): return parse_json(self.pin_bytes)

@dataclass(frozen=True)
class ProductionSuccessOrigin:
    stage_id: str
    pin_bytes: bytes
    @property
    def pin(self): return parse_json(self.pin_bytes)

@dataclass(frozen=True)
class CurrentOrigin:
    stage_id: str

@dataclass(frozen=True)
class Selection:
    raw_bytes: bytes
    bundle_sha256: str
    rows: tuple[OldOrigin|PriorSuccessorOrigin|LatestSuccessorOrigin|ProductionSuccessOrigin|CurrentOrigin,...]
    context_bundle_bytes: bytes
    @property
    def raw_sha256(self): return sha(self.raw_bytes)
    @property
    def data(self): return parse_json(self.raw_bytes)
    @property
    def payload_pins_complete(self):
        return all(all(row.pin[k] is not None for k in PAYLOAD_KEYS) for row in self.rows if type(row) is not CurrentOrigin)
    def row(self,sid):
        found=[r for r in self.rows if r.stage_id==sid]
        need(len(found)==1,'unselected/duplicate stage');return found[0]


def validate_context_bundle(data: bytes, expected_sha256: str) -> ContextBundle:
    digest(expected_sha256,'bundle digest')
    need(sha(data)==expected_sha256==BUNDLE_SHA256,'fixed immutable context bundle changed')
    obj=parse_json(data)
    keys(obj,{'schema','contexts','old_stage_rows','prior_candidate_rows','latest_stage_rows','production_stage_rows'},'context bundle')
    need(obj['schema']=='fixed-five-context-bundle-v1','bundle schema')
    keys(obj['contexts'],ORIGINS,'finite context registry')
    for name,pin in [('OldOrigin',OLD_CONTEXT_SHA256),('PriorSuccessorOrigin',PRIOR_CONTEXT_SHA256),('LatestSuccessorOrigin',LATEST_CONTEXT_SHA256),('ProductionSuccessOrigin',PRODUCTION_CONTEXT_SHA256)]:
        need(object_sha(obj['contexts'][name])==pin,'frozen '+name+' context changed')
    old,prior=obj['contexts']['OldOrigin'],obj['contexts']['PriorSuccessorOrigin']
    need(object_sha(old['identity'])==OLD_IDENTITY and object_sha(prior['identity'])==PRIOR_IDENTITY,'native identity changed')
    need(object_sha(obj['old_stage_rows'])==OLD_ROWS_SHA256,'original 37 stage pins changed')
    need(object_sha(obj['prior_candidate_rows'])==PRIOR_ROWS_SHA256,'terminal 11 metadata candidate pins changed')
    latest=obj['contexts']['LatestSuccessorOrigin']
    need(object_sha(latest['identity'])==LATEST_IDENTITY and latest['identity_sha256']==LATEST_IDENTITY,'latest native identity changed')
    need(latest['run_id']==LATEST_RUN and latest['pipeline_commit']==LATEST_PIPELINE,'latest context changed')
    need(object_sha(obj['latest_stage_rows'])==LATEST_ROWS_SHA256,'fixed 42 latest stage pins changed')
    production=obj['contexts']['ProductionSuccessOrigin']
    need(object_sha(production['identity'])==PRODUCTION_IDENTITY and production['identity_sha256']==PRODUCTION_IDENTITY,'production native identity changed')
    need(production['run_id']==PRODUCTION_RUN and production['pipeline_commit']==PRODUCTION_PIPELINE,'production origin changed')
    need(production['identity']['contract_sha256']==PRODUCTION_CONTRACT and production['identity']['profiles_sha256']==PRODUCTION_PROFILES,'production original contract/profile changed')
    need(object_sha(obj['production_stage_rows'])==PRODUCTION_ROWS_SHA256,'fixed production087 pins changed')
    need(obj['contexts']['CurrentOrigin']=={'rank':4,'parents':['OldOrigin','PriorSuccessorOrigin','LatestSuccessorOrigin','ProductionSuccessOrigin'],
         'source_commit':PRIOR_SOURCE,'source_manifest_sha256':PRIOR_MANIFEST},'current context intent changed')
    return ContextBundle(data)


def _bundle(bundle):
    need(type(bundle) is ContextBundle,'typed context bundle required')
    return validate_context_bundle(bundle.raw_bytes,bundle.raw_sha256)


def validate_plan(plan):
    need(type(plan) is dict and object_sha(plan)==PLAN_SHA256,'original plan changed')
    stages=plan['stages'];need(type(stages) is list and len(stages)==93,'93 original stages required')
    seen={};modules=set()
    for stage in stages:
        sid=stage['stage_id'];need(sid not in seen,'duplicate stage')
        direct=stage['needs_stages'];need(type(direct) is list and len(set(direct))==len(direct),'direct dependency duplicates')
        need(set(direct)<=set(seen),'cycle, forward or unknown dependency')
        closure=set(direct)
        for ancestor in direct: closure.update(seen[ancestor]['required_predecessors'])
        need(stage['required_predecessors']==[s for s in seen if s in closure],'transitive closure or order changed')
        need(stage['producer_job']==f"wave_{stage['wave']:02}",'numeric wave mismatch')
        need(all(seen[p]['wave']<stage['wave'] for p in direct),'dependency wave not earlier')
        need(not modules.intersection(stage['modules']),'duplicate module provider')
        modules.update(stage['modules']);seen[sid]=stage
    need(len(modules)==6369,'source module coverage changed')
    return stages


def _pin(pin, origin, stage_id, baseline, require_payloads):
    keys(pin,PIN_KEYS,'stage pin')
    for k in PIN_KEYS-PAYLOAD_KEYS:
        need(type(pin[k]) is type(baseline[k]) and pin[k]==baseline[k],'frozen metadata pin changed: '+k)
    values=[pin[k] is not None for k in PAYLOAD_KEYS]
    need(all(values) or not any(values),'partially specified payload pins')
    if not any(values):
        need(False,'complete static native payload pins required')
        return
    for k in PAYLOAD_KEYS-{'archive_bytes'}:digest(pin[k],k)
    integer(pin['archive_bytes'],'raw archive bytes',MAX_ARTIFACT)
    integer(pin['artifact_zip_bytes'],'ZIP bytes',MAX_ARTIFACT+1024**2)
    timestamp(pin['expires_at'])
    if origin in ('OldOrigin','LatestSuccessorOrigin','ProductionSuccessOrigin'):need(pin==baseline,'fixed historical payload pins changed')


def parse_selection(data, expected_sha256, plan, bundle, *, require_payloads=False):
    bundle=_bundle(bundle);validate_plan(plan);digest(expected_sha256,'selection digest')
    need(sha(data)==expected_sha256,'selection byte digest mismatch')
    obj=parse_json(data);keys(obj,{'schema','context_bundle_sha256','old_origin','prior_origin','latest_origin','production_origin','stages'},'v3 selection')
    need(obj['schema']=='verified-continuation-selection-v4','selection schema')
    need(obj['context_bundle_sha256']==bundle.raw_sha256,'selection context bundle mismatch')
    need(obj['old_origin']==bundle.old_context and obj['prior_origin']==bundle.prior_context and obj['latest_origin']==bundle.latest_context and obj['production_origin']==bundle.production_context,'selection native context changed')
    need(type(obj['stages']) is list and len(obj['stages'])==93,'selection must cover all stages')
    pins={r['stage_id']:r for r in bundle.data['old_stage_rows']+bundle.data['prior_candidate_rows']+bundle.data['latest_stage_rows']+bundle.data['production_stage_rows']}
    rows=[]
    for stage,row in zip(plan['stages'],obj['stages']):
        need(type(row) is dict and row.get('stage_id')==stage['stage_id'],'missing, duplicate or unordered provider')
        origin=row.get('origin');need(origin in ORIGINS,'unknown origin or alias')
        sid=row['stage_id']
        if origin=='CurrentOrigin':
            keys(row,{'stage_id','origin'},'current row');need(sid in CURRENT_STAGES,'only 091/092 may be current providers')
            rows.append(CurrentOrigin(sid))
        else:
            keys(row,{'stage_id','origin','pin'},'historical row')
            need(sid in pins and pins[sid]['origin']==origin,'historical stage/provider forbidden')
            _pin(row['pin'],origin,sid,pins[sid]['pin'],require_payloads)
            rows.append({'OldOrigin':OldOrigin,'PriorSuccessorOrigin':PriorSuccessorOrigin,'LatestSuccessorOrigin':LatestSuccessorOrigin,'ProductionSuccessOrigin':ProductionSuccessOrigin}[origin](sid,json_bytes(row['pin'])))
    selection=Selection(data,bundle.raw_sha256,tuple(rows),bundle.raw_bytes);validate_provider_dag(selection,plan)
    return selection


def _selection_consistent(selection):
    """Do not let manually constructed dataclasses bypass the parsed seal."""
    need(type(selection) is Selection, 'typed selection required')
    bundle=validate_context_bundle(selection.context_bundle_bytes,selection.bundle_sha256)
    obj=selection.data
    keys(obj,{'schema','context_bundle_sha256','old_origin','prior_origin','latest_origin','production_origin','stages'},'sealed selection')
    need(obj['schema']=='verified-continuation-selection-v4' and obj['context_bundle_sha256']==bundle.raw_sha256,'sealed selection context mismatch')
    need(obj['old_origin']==bundle.old_context and obj['prior_origin']==bundle.prior_context and obj['latest_origin']==bundle.latest_context and obj['production_origin']==bundle.production_context,'sealed native contexts changed')
    need(type(obj['stages']) is list and len(obj['stages'])==len(selection.rows)==93,'sealed stage count')
    pins={r['stage_id']:r for r in bundle.data['old_stage_rows']+bundle.data['prior_candidate_rows']+bundle.data['latest_stage_rows']+bundle.data['production_stage_rows']}
    seen=set()
    for row,record in zip(selection.rows,obj['stages']):
        need(type(row) in (OldOrigin,PriorSuccessorOrigin,LatestSuccessorOrigin,ProductionSuccessOrigin,CurrentOrigin),'sealed origin alias')
        need(row.stage_id not in seen,'sealed duplicate provider');seen.add(row.stage_id)
        origin=type(row).__name__
        expected={'stage_id':row.stage_id,'origin':origin}
        if type(row) is CurrentOrigin:
            need(row.stage_id in CURRENT_STAGES,'sealed fresh current provider changed')
        else:
            need(row.stage_id in pins and pins[row.stage_id]['origin']==origin,'sealed historical provider forbidden')
            _pin(row.pin,origin,row.stage_id,pins[row.stage_id]['pin'],False)
            expected['pin']=row.pin
        need(record==expected and object_sha(record)==object_sha(expected),'typed row differs from sealed bytes')
    need({r.stage_id for r in selection.rows if type(r) is OldOrigin}==OLD_STAGES,'sealed original 37 coverage')
    need({r.stage_id for r in selection.rows if type(r) is PriorSuccessorOrigin}==PRIOR_CANDIDATES,'sealed prior 11 coverage')
    need({r.stage_id for r in selection.rows if type(r) is LatestSuccessorOrigin}==LATEST_STAGES,'sealed latest 42 coverage')
    need({r.stage_id for r in selection.rows if type(r) is ProductionSuccessOrigin}==PRODUCTION_STAGES,'sealed production087 coverage')
    need({r.stage_id for r in selection.rows if type(r) is CurrentOrigin}==CURRENT_STAGES,'sealed fresh 2 coverage')
    return bundle


def validate_provider_dag(selection,plan):
    stages=validate_plan(plan);_selection_consistent(selection)
    need([r.stage_id for r in selection.rows]==[s['stage_id'] for s in stages],'selection canonical order')
    need({r.stage_id for r in selection.rows if type(r) is OldOrigin}==OLD_STAGES,'exact original 37 required')
    seen={}
    for row,stage in zip(selection.rows,stages):
        origin=type(row).__name__;need(type(row) in (OldOrigin,PriorSuccessorOrigin,LatestSuccessorOrigin,ProductionSuccessOrigin,CurrentOrigin),'typed origin alias')
        if origin!='CurrentOrigin':
            for sid in stage['required_predecessors']:
                need(sid in seen and RANK[seen[sid]]<=RANK[origin], 'historical provider lacks dependency closure')
        seen[row.stage_id]=origin
    return {name:tuple(sid for sid,origin in seen.items() if origin==name) for name in ORIGINS}


def validate_prior_current_sources(prior_manifest,current_manifest,prior_identity,current_identity):
    need(object_sha(prior_identity)==PRIOR_IDENTITY,'prior native identity changed')
    need(prior_identity['source_commit']==current_identity.get('source_commit')==PRIOR_SOURCE,'current source commit differs')
    need(prior_identity['source_manifest_sha256']==current_identity.get('source_manifest_sha256')==PRIOR_MANIFEST,'source identity differs')
    need(object_sha(prior_manifest)==PRIOR_MANIFEST,'prior source manifest changed')
    need(current_manifest==prior_manifest and object_sha(current_manifest)==PRIOR_MANIFEST,'all prior/current source records and metadata must be identical')
    need(len(prior_manifest['files'])==prior_manifest['source_count']==6369,'source count')
    return PRIOR_MANIFEST


def validate_original_repair(old_manifest,prior_manifest,delta,plan):
    validate_plan(plan)
    need(object_sha(old_manifest)==OLD_MANIFEST and object_sha(prior_manifest)==PRIOR_MANIFEST and object_sha(delta)==SOURCE_DELTA,'fixed source reconciliation inputs changed')
    old={r['module']:r for r in old_manifest['files']};prior={r['module']:r for r in prior_manifest['files']}
    need(set(old)==set(prior) and len(old)==6369,'source reconciliation coverage')
    changed=[m for m in old if old[m]!=prior[m]]
    need(changed==['SpectreFinite.RadiusFivePrivateFamilyExport'],'only the repaired leaf may differ')
    a=delta['old_source_utf8'].encode();b=delta['new_source_utf8'].encode();insertion=b'meta import SpectreFinite.RadiusFiveFamilyData\n'
    need(b==a[:57]+insertion+a[57:] and len(insertion)==47,'exact 47-byte repair required')
    need(delta['actual_real_diagnostic_compiled'] is False,'historical diagnostic statement must not be rewritten')
    for stage in plan['stages']:
        if stage['stage_id'] in OLD_STAGES:need(all(old[m]==prior[m] for m in stage['modules']),'reused original source changed')
    return tuple(changed)


def validate_current_identity(identity,selection,bundle,*,pipeline_commit,contract_sha256):
    bundle=_bundle(bundle);_selection_consistent(selection);need(selection.bundle_sha256==bundle.raw_sha256,'current selection bundle mismatch');old=bundle.old_context['identity'];prior=bundle.prior_context['identity']
    latest=bundle.latest_context['identity']
    keys(identity,set(latest)|{'latest_identity_sha256','production_identity_sha256'},'current identity')
    digest(contract_sha256,'new reviewed contract');need(contract_sha256 not in {old['contract_sha256'],prior['contract_sha256'],latest['contract_sha256'],PRODUCTION_CONTRACT},'current contract must be new')
    need(type(pipeline_commit) is str and re.fullmatch('[0-9a-f]{40}',pipeline_commit) and pipeline_commit not in {OLD_PIPELINE,PRIOR_PIPELINE,LATEST_PIPELINE,PRODUCTION_PIPELINE},'current pipeline must be distinct')
    fixed={k:latest[k] for k in ('source_commit','source_manifest_sha256','plan_sha256','runner_sha256','lean_archive_sha256','toolchain_inventory_sha256','evidence_mode','run_attempt','old_identity_sha256')}
    fixed.update(profiles_sha256=CURRENT_PROFILES,latest_identity_sha256=LATEST_IDENTITY,production_identity_sha256=PRODUCTION_IDENTITY)
    fixed.update(pipeline_commit=pipeline_commit,contract_sha256=contract_sha256,selection_sha256=selection.raw_sha256,prior_identity_sha256=PRIOR_IDENTITY,context_bundle_sha256=bundle.raw_sha256)
    need(all(identity[k]==v and type(identity[k]) is type(v) for k,v in fixed.items()),'current identity binding mismatch')
    run=identity['run_id'];need(type(run) is str and re.fullmatch('[1-9][0-9]*',run) and int(run) not in {OLD_RUN,PRIOR_RUN,LATEST_RUN,PRODUCTION_RUN,EXCLUDED_RUN},'current run must be distinct initial canonical run')
    need(timestamp(identity['run_started_at'])>=timestamp(bundle.production_context['terminal']['updated_at']),'current run precedes frozen latest terminal')
    return object_sha(identity)


def _wrapper_pin(wrapper,selection,bundle,plan):
    keys(wrapper,WRAPPER_KEYS,'wrapper');d=wrapper['native_descriptor'];keys(d,NATIVE_KEYS,'native hydrated descriptor')
    sid=d['stage_id'];row=selection.row(sid);origin=type(row).__name__
    need(origin!='CurrentOrigin' and wrapper['origin']==origin,'historical invocation provider mismatch')
    identity=bundle.context(origin)['identity'];need(d['identity']==identity,'native descriptor identity mismatch')
    stage=next(s for s in plan['stages'] if s['stage_id']==sid)
    need(d['schema']=='fresh-stage-upload-candidate-v1' and d['producer_job']==stage['producer_job'] and d['producer_conclusion']=='success' and type(d['retention_days']) is int and d['retention_days']==7,'native role/status mismatch')
    metadata=wrapper['authenticated_metadata'];keys(metadata,{'run','job','artifact','role'},'authenticated metadata')
    run,job,artifact=metadata['run'],metadata['job'],metadata['artifact'];context=bundle.context(origin)
    need(run.get('id')==context['run_id'] and type(run.get('run_attempt')) is int and run.get('run_attempt')==1 and run.get('head_sha')==context['pipeline_commit'],'metadata run mismatch')
    need(run.get('created_at')==identity['run_started_at'] and run.get('workflow_id')==context['workflow']['workflow_id'] and run.get('path')==context['workflow']['path'] and run.get('head_branch')==context['workflow']['head_branch'],'metadata event/workflow/start mismatch')
    for key in ('repository','head_repository'):
        need(run.get(key,{}).get('id')==REPOSITORY_ID and run[key].get('full_name')==REPOSITORY,'metadata repository mismatch')
    need(run.get('status')=='completed' and run.get('conclusion')=='failure','historical terminal status changed')
    need(job.get('id')==d['producer_job_id'] and job.get('run_id')==context['run_id'] and type(job.get('run_attempt')) is int and job.get('run_attempt')==1 and job.get('head_sha')==context['pipeline_commit'] and job.get('status')=='completed' and job.get('conclusion')=='success','producer metadata mismatch')
    binding=context['workflow']['roles'][sid];need(metadata['role']==binding and job.get('name')==binding['job_name'],'producer role mismatch')
    start,end=timestamp(job['started_at']),timestamp(job['completed_at']);need(timestamp(identity['run_started_at'])<=start<=end,'producer time order')
    if origin in ('PriorSuccessorOrigin','LatestSuccessorOrigin','ProductionSuccessOrigin'):need(end<=timestamp(context['terminal']['updated_at']),'producer after historical terminal')
    steps=job.get('steps');need(type(steps) is list,'producer steps missing')
    need(len({s.get('number') for s in steps})==len(steps) and len({s.get('name') for s in steps})==len(steps),'duplicate producer steps')
    previous=start
    for label in ('verifier_step','upload_step'):
        wanted=binding[label];matches=[s for s in steps if s.get('number')==wanted['number'] or s.get('name')==wanted['name']]
        need(len(matches)==1,'missing/ambiguous verifier or upload step');step=matches[0]
        need(step['number']==wanted['number'] and step['name']==wanted['name'] and step.get('status')=='completed' and step.get('conclusion')=='success','verifier/upload identity or result')
        s,e=timestamp(step['started_at']),timestamp(step['completed_at']);need(previous<=s<=e<=end,'verifier/upload time order');previous=e
    base={r['stage_id']:r['pin'] for r in bundle.data['old_stage_rows']+bundle.data['prior_candidate_rows']+bundle.data['latest_stage_rows']+bundle.data['production_stage_rows']}[sid]
    expected={'id':base['artifact_id'],'name':base['artifact_name'],'size_in_bytes':base['artifact_zip_bytes'],'digest':'sha256:'+base['artifact_zip_sha256'],'expired':False,'expires_at':base['expires_at']}
    need(all(type(artifact.get(k)) is type(v) and artifact.get(k)==v for k,v in expected.items()),'artifact frozen metadata changed')
    wr=artifact.get('workflow_run',{});need(wr.get('id')==context['run_id'] and wr.get('head_sha')==context['pipeline_commit'] and wr.get('repository_id')==wr.get('head_repository_id')==REPOSITORY_ID and wr.get('head_branch')==context['workflow']['head_branch'],'artifact workflow mismatch')
    pin={k:base[k] for k in PIN_KEYS-PAYLOAD_KEYS}
    pin.update({k:d[k] for k in ('archive_bytes','archive_sha256','receipt_sha256')});pin['raw_descriptor_sha256']=wrapper['raw_descriptor_sha256']
    _pin(pin,origin,sid,base,True)
    for k in ('artifact_id','producer_job_id','artifact_zip_sha256'):need(d[k]==base[k],'descriptor transport binding mismatch')
    return pin


def derive_pinned_inactive_selection(selection,bundle,plan,wrappers):
    """Compatibility seam: this production selection is already statically sealed."""
    raise Rejected('dynamic pin derivation forbidden; exact static 91-stage pins required')


def validate_native_bytes(wrapper,descriptor_bytes,receipt_bytes):
    """Keep raw JSON hashes, never a reserialized substitute for native bytes."""
    d=wrapper['native_descriptor'];need(sha(descriptor_bytes)==wrapper['raw_descriptor_sha256'],'native descriptor byte mutation')
    need(sha(receipt_bytes)==d['receipt_sha256'],'native receipt byte mutation')
    raw=parse_json(descriptor_bytes);keys(raw,(NATIVE_KEYS-{'artifact_zip_sha256'})|{'archive_path'},'raw native descriptor')
    for key in ('artifact_id','producer_job_id','producer_conclusion'):need(raw[key] is None,'native descriptor already rewritten')
    need(type(raw['archive_path']) is str and raw['archive_path'],'native archive path missing')
    hydrated={k:v for k,v in raw.items() if k!='archive_path'}
    for key in ('artifact_id','producer_job_id','producer_conclusion','artifact_zip_sha256'):hydrated[key]=d[key]
    need(hydrated==d,'native descriptor differs beyond authenticated hydration')
    receipt=parse_json(receipt_bytes)
    need(type(receipt) is dict and receipt.get('identity')==d['identity'] and receipt.get('stage_id')==d['stage_id'] and receipt.get('producer_job')==d['producer_job'],'native receipt identity/role mismatch')
    return receipt


def native_prior_invocation_view(wrappers,selection,bundle,plan,*,native_bytes):
    """Map only outer prior role to frozen validator's native CurrentOrigin.

    native_bytes maps each stage to {'descriptor': bytes, 'receipt': bytes}.
    No semantic-pass certificate is required before semantic validation.
    Input native bytes are neither rewritten nor replaced by this view.
    """
    bundle=_bundle(bundle)
    selection=parse_selection(selection.raw_bytes,selection.raw_sha256,plan,bundle,require_payloads=True)
    expected=[r.stage_id for r in selection.rows if type(r) in (OldOrigin,PriorSuccessorOrigin)]
    need([w['native_descriptor']['stage_id'] for w in wrappers]==expected,'complete historical closure required')
    need(type(native_bytes) is dict and set(native_bytes)==set(expected),'exact raw native byte map required')
    admitted={};result=[]
    for wrapper in wrappers:
        sid=wrapper['native_descriptor']['stage_id'];row=selection.row(sid)
        need(_wrapper_pin(wrapper,selection,bundle,plan)==row.pin,'wrapper differs from selected payload pin')
        keys(native_bytes[sid],{'descriptor','receipt'},'native byte pair')
        receipt=validate_native_bytes(wrapper,native_bytes[sid]['descriptor'],native_bytes[sid]['receipt'])
        stage=next(s for s in plan['stages'] if s['stage_id']==sid)
        need(receipt.get('predecessors')==[admitted[s] for s in stage['required_predecessors']],'native predecessor chain differs from selected providers')
        admitted[sid]=copy.deepcopy(wrapper['native_descriptor'])
        view=copy.deepcopy(wrapper)
        if type(row) is PriorSuccessorOrigin:view['origin']='CurrentOrigin'
        result.append(view)
    need([w['native_descriptor'] for w in result]==[w['native_descriptor'] for w in wrappers],'native descriptor mutation in invocation view')
    return result


def validate_import_companions(receipt,expected_module_order,expected_imports,expected_outputs):
    """Optional pure precheck; frozen validator still verifies files/contracts."""
    records=receipt.get('modules');need(type(records) is list and [r.get('module') for r in records]==expected_module_order,'receipt module order')
    need(set(expected_imports)==set(expected_outputs)==set(expected_module_order),'expected import/output coverage')
    for record in records:
        module=record['module'];names={'objects/'+module.replace('.','/')+s for s in SUFFIXES}
        need(type(record.get('outputs')) is dict and set(record['outputs'])==names,'all six companions required')
        for d in record['outputs'].values():digest(d,'companion hash')
        need(record['outputs']==expected_outputs[module],'selected output hashes differ')
        need(record.get('ordered_imports')==expected_imports[module],'ordered import or runtime inventory mismatch')


def deadline_check(bundle,selection,now,*,current_identity=None,artifact_expiries=(),previous_now=None,max_age_seconds=MAX_AGE):
    bundle=_bundle(bundle);_selection_consistent(selection);need(selection.bundle_sha256==bundle.raw_sha256,'deadline selection bundle mismatch');integer(max_age_seconds,'age cap',MAX_AGE)
    need(type(now) is datetime and now.tzinfo is not None,'trusted timezone-aware current time required')
    now=now.astimezone(timezone.utc)
    if previous_now is not None:need(type(previous_now) is datetime and previous_now.tzinfo is not None and now>=previous_now,'backward clock must not renew eligibility')
    identities=[bundle.context(origin)['identity'] for origin in ORIGINS[:4]]
    if current_identity is not None:identities.append(current_identity)
    starts=[timestamp(i['run_started_at']) for i in identities];need(all(s<=now for s in starts),'future run timestamp')
    limits=[s+timedelta(seconds=max_age_seconds) for s in starts]
    limits += [timestamp(bundle.context(o)['prepare']['expires_at']) for o in ORIGINS[:4]]
    limits += [timestamp(r.pin['expires_at']) for r in selection.rows if type(r) is not CurrentOrigin]
    limits += [timestamp(x) for x in artifact_expiries]
    deadline=min(limits);need(now<deadline,'earliest historical deadline/artifact expiry reached')
    return deadline

@dataclass(frozen=True)
class RawArchiveLedger:
    selection_sha256: str
    entries_bytes: bytes
    @property
    def entries(self):return parse_json(self.entries_bytes)
    @property
    def total_bytes(self):return sum(self.entries.values())
    @property
    def remaining_bytes(self):return MAX_RESTORED-self.total_bytes


def cumulative_raw_budget(selection,archive_sizes,*,previous_ledger=None):
    """One global selected-union budget, retained across sessions via ledger.

    Every call always counts all 37 old archives and all selected prior/latest
    archives, even when the current session restores only one payload. ZIP
    sizes must never be supplied here as raw tar sizes.
    """
    _selection_consistent(selection);need(type(archive_sizes) is dict,'exact raw size map required')
    known={r.stage_id:r.pin['archive_bytes'] for r in selection.rows if type(r) is not CurrentOrigin and r.pin['archive_bytes'] is not None}
    need(sum(known[r.stage_id] for r in selection.rows if type(r) is OldOrigin)==ORIGINAL_RAW_BYTES,'original cumulative baseline changed')
    entries=dict(known)
    if previous_ledger is not None:
        need(type(previous_ledger) is RawArchiveLedger and previous_ledger.selection_sha256==selection.raw_sha256,'global ledger context changed')
        for sid,size in previous_ledger.entries.items():
            need(sid not in entries or entries[sid]==size,'previous global ledger conflicts with pinned raw bytes');entries[sid]=size
    for sid,size in archive_sizes.items():
        need(sid in {r.stage_id for r in selection.rows},'unselected raw archive')
        integer(size,'raw archive size',MAX_ARTIFACT)
        need(sid not in entries or entries[sid]==size,'raw archive size replacement/reset');entries[sid]=size
    for sid,size in entries.items():
        need(sid in {r.stage_id for r in selection.rows},'ledger contains unselected archive');integer(size,'global raw archive size',MAX_ARTIFACT)
    need(sum(entries.values())<=MAX_RESTORED,'global four-GiB selected-union archive cap exceeded')
    return RawArchiveLedger(selection.raw_sha256,json_bytes(entries))


def activation_status(selection,bundle,*,prepare_evidence=None,semantic_certificate=None,independent_review=None):
    """This preparation release never activates future-current execution.

    Evidence is reported as missing or present without trusting self-asserted
    booleans. A separately reviewed execution adapter must validate certificates
    against actual files, current event identity and frozen runtime paths.
    """
    _bundle(bundle);_selection_consistent(selection);need(selection.bundle_sha256==bundle.raw_sha256,'activation selection bundle mismatch');missing=[]
    if not selection.payload_pins_complete:missing.append('authenticated_native_payload_pins')
    if prepare_evidence is None:missing.append('authenticated_historical_prepare_bytes')
    if semantic_certificate is None:missing.append('full_frozen_prior_semantic_admission')
    if independent_review is None:missing.append('independent_four_context_review')
    missing.append('separately_reviewed_future_current_execution_adapter')
    return {'active':False,'selection_sha256':selection.raw_sha256,'context_bundle_sha256':bundle.raw_sha256,'missing':missing,'claim':'inactive_candidate_only_clean_rebuild_pending'}


def validate_prepare_bytes(bundle,origin,identity_bytes,inventory_bytes):
    """Check actual authenticated prepare members against native immutable pins."""
    bundle=_bundle(bundle);need(origin in ORIGINS[:4],'historical prepare origin required')
    context=bundle.context(origin)
    need(sha(identity_bytes)==context['prepare']['identity_sha256'],'actual native prepare identity bytes differ')
    need(parse_json(identity_bytes)==context['identity'],'actual prepare identity differs')
    need(sha(inventory_bytes)==context['prepare']['inventory_sha256'],'actual prepared runtime inventory differs')
    return {'origin':origin,'identity_sha256':sha(identity_bytes),'inventory_sha256':sha(inventory_bytes)}


# Immutable original identity, retained separately from the new current profile.
LATEST_WORKFLOW_ID = 387046066
_LATEST_NATIVE_IDENTITY_BYTES = b'{\n  "context_bundle_sha256": "cf1128728122c6230764e6918a6fed3d7080bdc7e3cfac408e67cbe31771247c",\n  "contract_sha256": "2848fad58bf59da1958c7e1632e841c1bae78f22ab728b1098a9426977aef334",\n  "evidence_mode": "verified_continuation",\n  "lean_archive_sha256": "b67d0e0ba959fc74e186f1b44aebca32d6ecb6a28f8e9a029fc4e9f73398a049",\n  "old_identity_sha256": "1838d66b59cf9ce277f72a2dbd9ec1698296a8d5e64334e981496cdc2b910560",\n  "pipeline_commit": "bc3f977237bee905dafb4f13eeb6564a4a338b42",\n  "plan_sha256": "c25336bffaf3ada115c7642840675f445cc3cef145fa1d70e9eec8988567a7ed",\n  "prior_identity_sha256": "287e19a82589415db3897697c1a5941f7c20cb1b885a4404d3ebb49cb7878bdb",\n  "profiles_sha256": "0af17b85b2b469be445bdcb68acbc07bb38507382fc818ffc4bd2bac5e3ce1ee",\n  "run_attempt": "1",\n  "run_id": "38978663241",\n  "run_started_at": "2026-10-16T22:56:24Z",\n  "runner_sha256": "9085c9eea092c270fbd6952834839103c66519a7b4716fe09147001c7d96355d",\n  "selection_sha256": "e7565dcc7925d05aa44225bc916bfd1a18d50b75c5438b07b1ea67d376b33549",\n  "source_commit": "5d0612a09e3b7d440be16e7b1dc511ae73035bbb",\n  "source_manifest_sha256": "09b0371c9acc07b07355824e7a7302a810c4247bbbce20d1e497bd4a02a23392",\n  "toolchain_inventory_sha256": "42bd268b1ca3e9bf89f4149ac427d6c0e76f735233b092a6df4ca27a2c2db7ea"\n}\n'

def latest_native_identity():
    need(sha(_LATEST_NATIVE_IDENTITY_BYTES)==LATEST_IDENTITY,'immutable latest identity changed')
    return parse_json(_LATEST_NATIVE_IDENTITY_BYTES)


# Exact restore-policy APIs, colocated to keep the successor adapter small.
import fresh_stage as f

ACTIVATION_ALLOWED=False
NUMERIC_AND_PROTOCOL_FIELDS=(
 'lean_release','lean_archive_sha256','runner','maximum_parallel_jobs','retention_days',
 'job_timeout_seconds','max_artifact_bytes','max_log_bytes','max_restored_bytes',
 'max_stage_output_bytes','max_run_age_seconds','minimum_free_disk_bytes','module_interface',
 'output_suffixes','reserved_final_jobs','receipt_protocol','toolchain_inventory_mode')
REVIEW_FIELDS=('review_status','storage_adapter_review_status','readonly_commit_review_status',
 'transport_review_status','process_containment_review_status','compiler_adapter_review_status',
 'final_checks_review_status')

@dataclass(frozen=True)
class RestoreScope:
    raw_bytes: bytes
    @property
    def data(self):return parse_json(self.raw_bytes)
    @property
    def sha256(self):return sha(self.raw_bytes)

def validate_execution_context(*,plan,profiles,current_contract,current_manifest,old_manifest,prior_manifest,
        source_delta,inventory,current_identity,selection,bundle,integration_pins,prior_contract):
    import four_context_final as final
    # The exact final-component seam binds current identities and independently
    # reviewed selection/admission pins. Actual admission records are required by
    # the driver before this pure context is used.
    selection=final._selection_context(plan,selection,bundle,current_identity,integration_pins)
    need(object_sha(prior_contract)==bundle.prior_context['identity']['contract_sha256'],'historical prior contract changed')
    need(object_sha(current_contract)==integration_pins['current_contract_sha256'],'current contract hash changed')
    need(object_sha(profiles)==current_identity['profiles_sha256'],'profile bytes changed')
    need(object_sha(inventory)==current_identity['toolchain_inventory_sha256'],'canonical runtime inventory changed')
    validate_prior_current_sources(prior_manifest,current_manifest,bundle.prior_context['identity'],current_identity)
    validate_original_repair(old_manifest,prior_manifest,source_delta,plan)
    for key in NUMERIC_AND_PROTOCOL_FIELDS:
        need(key in current_contract and key in prior_contract and type(current_contract[key]) is type(prior_contract[key]) and current_contract[key]==prior_contract[key],
               'numeric/protocol contract field changed: '+key)
    for key in REVIEW_FIELDS:
        expected='reviewed_for_execution' if key=='review_status' else 'reviewed'
        need(current_contract.get(key)==expected,'inactive execution gate: '+key)
    fixed={'source_commit':PRIOR_SOURCE,'source_manifest_sha256':PRIOR_MANIFEST,'plan_sha256':PLAN_SHA256,
      'profiles_sha256':current_identity['profiles_sha256'],'source_delta_sha256':SOURCE_DELTA,
      'runner_sha256':bundle.prior_context['identity']['runner_sha256'],'selection_sha256':selection.raw_sha256,
      'old_identity_sha256':OLD_IDENTITY,'prior_identity_sha256':PRIOR_IDENTITY,
      'latest_identity_sha256':LATEST_IDENTITY,'production_identity_sha256':PRODUCTION_IDENTITY,'context_bundle_sha256':bundle.raw_sha256}
    need(all(type(current_contract.get(k)) is type(v) and current_contract[k]==v for k,v in fixed.items()),'execution contract identity binding changed')
    f.validate_contract(current_contract,current_manifest,plan,profiles)
    need(current_contract['max_restored_bytes']==MAX_RESTORED and current_contract['max_run_age_seconds']==MAX_AGE,'aggregate cap/deadline changed')
    return selection


def scope_stage_ids(plan,selection,*,target_stage=None,final_role=None):
    validate_plan(plan);validate_provider_dag(selection,plan)
    need((target_stage is None)!=(final_role is None),'exactly one stage/final scope required')
    stages={s['stage_id']:s for s in plan['stages']}
    if target_stage is not None:
        need(type(target_stage) is str and target_stage in stages and type(selection.row(target_stage)) is CurrentOrigin,'fresh current target required')
        expected=stages[target_stage]['required_predecessors']
    else:
        need(final_role in ('export_target','fresh_kernel'),'only full-closure final roles allowed')
        expected=list(stages)
    historical=[sid for sid in expected if type(selection.row(sid)) is not CurrentOrigin]
    current=[sid for sid in expected if type(selection.row(sid)) is CurrentOrigin]
    for sid in historical:need(set(stages[sid]['required_predecessors'])<=set(historical),'historical subset not transitively closed')
    for sid in expected:need(set(stages[sid]['required_predecessors'])<=set(expected),'restore scope not transitively closed')
    return list(expected),historical,current


def validate_restore_scope(*,plan,selection,bundle,wrappers,native_bytes,current_identity,integration_pins,
                           target_stage=None,final_role=None):
    """Validate all native bytes before passing an exact subset to native validators.

    The historical invocation view changes only the outer prior label. Hashes,
    identities, descriptors, receipts and predecessor chains are never rewritten.
    """
    import four_context_final as final
    selection=final._selection_context(plan,selection,bundle,current_identity,integration_pins)
    expected,historical,current=scope_stage_ids(plan,selection,target_stage=target_stage,final_role=final_role)
    need(type(wrappers) is list and [w.get('native_descriptor',{}).get('stage_id') for w in wrappers]==expected,'wrong/missing/duplicate/unordered restore wrappers')
    need(type(native_bytes) is dict and set(native_bytes)==set(expected),'exact native byte map required')
    stages={s['stage_id']:s for s in plan['stages']};admitted={};objects={};view=[];sizes={};all_receipts={};legacy_objects={};legacy_view=[]
    for wrapper in wrappers:
        keys(wrapper,WRAPPER_KEYS,'restore wrapper');d=wrapper['native_descriptor'];sid=d['stage_id'];row=selection.row(sid);origin=type(row).__name__
        need(wrapper['origin']==origin,'selected provider label changed')
        identity=current_identity if origin=='CurrentOrigin' else bundle.context(origin)['identity']
        final._validate_wrapper(wrapper,identity,sid,current_workflow_id=integration_pins['current_workflow_id'] if origin=='CurrentOrigin' else None)
        if origin!='CurrentOrigin':need(_wrapper_pin(wrapper,selection,bundle,plan)==row.pin,'historical payload pin changed')
        keys(native_bytes[sid],{'descriptor','receipt'},'native byte pair')
        receipt=validate_native_bytes(wrapper,native_bytes[sid]['descriptor'],native_bytes[sid]['receipt'])
        need(receipt.get('schema')=='fresh-stage-receipt-v1' and receipt.get('status')=='fresh_compile_check_pairs_only' and receipt.get('proof_pass_claimed') is False,'native receipt scope/status changed')
        if origin=='OldOrigin':need('receipt_protocol' not in receipt,'original receipt protocol rewritten')
        else:need(receipt.get('receipt_protocol')=='readonly_committed_v1','readonly receipt protocol missing')
        need(receipt.get('predecessors')==[admitted[x] for x in stages[sid]['required_predecessors']],'exact original native predecessor chain changed')
        modules=receipt.get('modules');need(type(modules) is list and [x.get('module') for x in modules]==stages[sid]['modules'],'native stage module order/coverage changed')
        files=receipt.get('files');need(type(files) is dict,'native receipt files map missing')
        for entry in modules:
            module=entry['module'];outputs=entry.get('outputs');prefix='objects/'+module.replace('.','/')
            need(type(outputs) is dict and set(outputs)=={prefix+s for s in SUFFIXES},'exact six companions required')
            for name,output_digest in outputs.items():
                digest(output_digest,'native output hash');need(name in files and files[name].get('sha256')==output_digest,'native module/file output hash mismatch')
                integer(files[name].get('bytes'),'native companion byte count',MAX_ARTIFACT,minimum=0)
            if origin!='CurrentOrigin':
                need(module not in objects,'duplicate historical object provider');objects[module]=copy.deepcopy(outputs)
                if origin in ORIGINS[:2]:legacy_objects[module]=copy.deepcopy(outputs)
        if origin!='CurrentOrigin':
            native=copy.deepcopy(wrapper)
            if origin=='PriorSuccessorOrigin':native['origin']='CurrentOrigin'
            view.append(native)
            if origin in ORIGINS[:2]:legacy_view.append(copy.deepcopy(native))
        admitted[sid]=copy.deepcopy(d);all_receipts[sid]=receipt;sizes[sid]=d['archive_bytes']
    ledger=cumulative_raw_budget(selection,sizes)
    value={'schema':'exact-five-context-restore-scope-v1','target_stage':target_stage,'final_role':final_role,
        'expected_stage_ids':expected,'historical_stage_ids':historical,'current_stage_ids':current,
        'native_descriptors':[admitted[s] for s in expected],'historical_native_view':view,
        'historical_objects':objects,
        'legacy_stage_ids':[sid for sid in historical if type(selection.row(sid)) in (OldOrigin,PriorSuccessorOrigin)],
        'latest_stage_ids':[sid for sid in historical if type(selection.row(sid)) is LatestSuccessorOrigin],
        'legacy_objects':legacy_objects,'legacy_native_view':legacy_view,
        'production_stage_ids':[sid for sid in historical if type(selection.row(sid)) is ProductionSuccessOrigin],
        'production_identity':bundle.production_context['identity'],
        'latest_identity':bundle.latest_context['identity'],'raw_archive_bytes':ledger.total_bytes,'remaining_raw_bytes':ledger.remaining_bytes,
        'selection_sha256':selection.raw_sha256,'context_bundle_sha256':bundle.raw_sha256,
        'current_identity':current_identity,'semantic_admission_claimed':False,'activation_allowed':False}
    need([w['native_descriptor'] for w in view]==[admitted[s] for s in historical],'historical native mapping mutated')
    return RestoreScope(json_bytes(value))


def canonical_native_order(plan,descriptors):
    """Order only; never normalize descriptor identity or content."""
    stages=validate_plan(plan);need(type(descriptors) is list,'descriptor list required')
    by={d['stage_id']:d for d in descriptors};need(len(by)==len(descriptors) and set(by)<={s['stage_id'] for s in stages},'duplicate or unknown native descriptor')
    return [copy.deepcopy(by[s['stage_id']]) for s in stages if s['stage_id'] in by]


def archive_ledger_after_build(selection,scope_sizes,stage_id,raw_bytes):
    need(type(selection.row(stage_id)) is CurrentOrigin and stage_id not in scope_sizes,'new current stage must be distinct')
    sizes=copy.deepcopy(scope_sizes);sizes[stage_id]=raw_bytes
    return cumulative_raw_budget(selection,sizes)
