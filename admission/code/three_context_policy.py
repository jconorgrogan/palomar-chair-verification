"""Inactive, fixed three-context policy; pure stdlib, no I/O or execution.

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

ORIGINS = ('OldOrigin', 'PriorSuccessorOrigin', 'CurrentOrigin')
RANK = dict(zip(ORIGINS, range(3)))
OLD_RUN = 38860226136
PRIOR_RUN = 38917565694
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
BUNDLE_SHA256 = 'cf1128728122c6230764e6918a6fed3d7080bdc7e3cfac408e67cbe31771247c'
OLD_CONTEXT_SHA256 = '36f8a1b1fd943b6e665b805ec49f07b782829fff74415cd4f2e4174c9ffa96f8'
PRIOR_CONTEXT_SHA256 = 'e062f4c9072ef0d0f30cc6260e7830adc4fbf1b60a2b522253c00e9be13fe338'
OLD_ROWS_SHA256 = '5ebe74caf7824058b5201fee805cc5dba7db8fa83b8ce992bcefeeb96df53495'
PRIOR_ROWS_SHA256 = '78b2f89c2676b6f952f0ec007c2327522a183a2def64e7cf334b144452cd4a1a'
OLD_STAGES = frozenset([f'build_{i:03}' for i in range(36)] + ['build_055'])
PRIOR_CANDIDATES = frozenset([f'build_{i:03}' for i in range(36,43)] + ['build_049','build_051','build_054','build_056'])
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
class CurrentOrigin:
    stage_id: str

@dataclass(frozen=True)
class Selection:
    raw_bytes: bytes
    bundle_sha256: str
    rows: tuple[OldOrigin|PriorSuccessorOrigin|CurrentOrigin,...]
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
    keys(obj,{'schema','contexts','old_stage_rows','prior_candidate_rows'},'context bundle')
    need(obj['schema']=='fixed-three-context-bundle-v1','bundle schema')
    keys(obj['contexts'],ORIGINS,'finite context registry')
    for name,pin in [('OldOrigin',OLD_CONTEXT_SHA256),('PriorSuccessorOrigin',PRIOR_CONTEXT_SHA256)]:
        need(object_sha(obj['contexts'][name])==pin,'frozen '+name+' context changed')
    old,prior=obj['contexts']['OldOrigin'],obj['contexts']['PriorSuccessorOrigin']
    need(object_sha(old['identity'])==OLD_IDENTITY and object_sha(prior['identity'])==PRIOR_IDENTITY,'native identity changed')
    need(object_sha(obj['old_stage_rows'])==OLD_ROWS_SHA256,'original 37 stage pins changed')
    need(object_sha(obj['prior_candidate_rows'])==PRIOR_ROWS_SHA256,'terminal 11 metadata candidate pins changed')
    need(obj['contexts']['CurrentOrigin']=={'rank':2,'parents':['OldOrigin','PriorSuccessorOrigin'],
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
        need(origin=='PriorSuccessorOrigin' and not require_payloads,'INACTIVE: complete native payload pins required')
        return
    for k in PAYLOAD_KEYS-{'archive_bytes'}:digest(pin[k],k)
    integer(pin['archive_bytes'],'raw archive bytes',MAX_ARTIFACT)
    integer(pin['artifact_zip_bytes'],'ZIP bytes',MAX_ARTIFACT+1024**2)
    timestamp(pin['expires_at'])
    if origin=='OldOrigin':need(pin==baseline,'original payload pins changed')


def parse_selection(data, expected_sha256, plan, bundle, *, require_payloads=False):
    bundle=_bundle(bundle);validate_plan(plan);digest(expected_sha256,'selection digest')
    need(sha(data)==expected_sha256,'selection byte digest mismatch')
    obj=parse_json(data);keys(obj,{'schema','context_bundle_sha256','old_origin','prior_origin','stages'},'v2 selection')
    need(obj['schema']=='verified-continuation-selection-v2','selection schema')
    need(obj['context_bundle_sha256']==bundle.raw_sha256,'selection context bundle mismatch')
    need(obj['old_origin']==bundle.old_context and obj['prior_origin']==bundle.prior_context,'selection native context changed')
    need(type(obj['stages']) is list and len(obj['stages'])==93,'selection must cover all stages')
    pins={r['stage_id']:r for r in bundle.data['old_stage_rows']+bundle.data['prior_candidate_rows']}
    rows=[]
    for stage,row in zip(plan['stages'],obj['stages']):
        need(type(row) is dict and row.get('stage_id')==stage['stage_id'],'missing, duplicate or unordered provider')
        origin=row.get('origin');need(origin in ORIGINS,'unknown origin or alias')
        sid=row['stage_id']
        if origin=='CurrentOrigin':
            keys(row,{'stage_id','origin'},'current row');need(sid not in OLD_STAGES,'original 37 provider must remain unchanged')
            rows.append(CurrentOrigin(sid))
        else:
            keys(row,{'stage_id','origin','pin'},'historical row')
            need(sid in pins and pins[sid]['origin']==origin,'historical stage/provider forbidden')
            _pin(row['pin'],origin,sid,pins[sid]['pin'],require_payloads)
            rows.append((OldOrigin if origin=='OldOrigin' else PriorSuccessorOrigin)(sid,json_bytes(row['pin'])))
    selection=Selection(data,bundle.raw_sha256,tuple(rows),bundle.raw_bytes);validate_provider_dag(selection,plan)
    return selection


def _selection_consistent(selection):
    """Do not let manually constructed dataclasses bypass the parsed seal."""
    need(type(selection) is Selection, 'typed selection required')
    bundle=validate_context_bundle(selection.context_bundle_bytes,selection.bundle_sha256)
    obj=selection.data
    keys(obj,{'schema','context_bundle_sha256','old_origin','prior_origin','stages'},'sealed selection')
    need(obj['schema']=='verified-continuation-selection-v2' and obj['context_bundle_sha256']==bundle.raw_sha256,'sealed selection context mismatch')
    need(obj['old_origin']==bundle.old_context and obj['prior_origin']==bundle.prior_context,'sealed native contexts changed')
    need(type(obj['stages']) is list and len(obj['stages'])==len(selection.rows)==93,'sealed stage count')
    pins={r['stage_id']:r for r in bundle.data['old_stage_rows']+bundle.data['prior_candidate_rows']}
    seen=set()
    for row,record in zip(selection.rows,obj['stages']):
        need(type(row) in (OldOrigin,PriorSuccessorOrigin,CurrentOrigin),'sealed origin alias')
        need(row.stage_id not in seen,'sealed duplicate provider');seen.add(row.stage_id)
        origin=type(row).__name__
        expected={'stage_id':row.stage_id,'origin':origin}
        if type(row) is CurrentOrigin:
            need(row.stage_id not in OLD_STAGES,'sealed original provider changed')
        else:
            need(row.stage_id in pins and pins[row.stage_id]['origin']==origin,'sealed historical provider forbidden')
            _pin(row.pin,origin,row.stage_id,pins[row.stage_id]['pin'],False)
            expected['pin']=row.pin
        need(record==expected and object_sha(record)==object_sha(expected),'typed row differs from sealed bytes')
    need({r.stage_id for r in selection.rows if type(r) is OldOrigin}==OLD_STAGES,'sealed original 37 coverage')
    return bundle


def validate_provider_dag(selection,plan):
    stages=validate_plan(plan);_selection_consistent(selection)
    need([r.stage_id for r in selection.rows]==[s['stage_id'] for s in stages],'selection canonical order')
    need({r.stage_id for r in selection.rows if type(r) is OldOrigin}==OLD_STAGES,'exact original 37 required')
    seen={}
    for row,stage in zip(selection.rows,stages):
        origin=type(row).__name__;need(type(row) in (OldOrigin,PriorSuccessorOrigin,CurrentOrigin),'typed origin alias')
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
    keys(identity,set(prior)|{'prior_identity_sha256','context_bundle_sha256'},'current identity')
    digest(contract_sha256,'new reviewed contract');need(contract_sha256 not in {old['contract_sha256'],prior['contract_sha256']},'current contract must be new')
    need(type(pipeline_commit) is str and re.fullmatch('[0-9a-f]{40}',pipeline_commit) and pipeline_commit not in {OLD_PIPELINE,PRIOR_PIPELINE},'current pipeline must be distinct')
    fixed={k:prior[k] for k in ('source_commit','source_manifest_sha256','plan_sha256','profiles_sha256','runner_sha256','lean_archive_sha256','toolchain_inventory_sha256','evidence_mode','run_attempt','old_identity_sha256')}
    fixed.update(pipeline_commit=pipeline_commit,contract_sha256=contract_sha256,selection_sha256=selection.raw_sha256,prior_identity_sha256=PRIOR_IDENTITY,context_bundle_sha256=bundle.raw_sha256)
    need(all(identity[k]==v and type(identity[k]) is type(v) for k,v in fixed.items()),'current identity binding mismatch')
    run=identity['run_id'];need(type(run) is str and re.fullmatch('[1-9][0-9]*',run) and int(run) not in {OLD_RUN,PRIOR_RUN,EXCLUDED_RUN},'current run must be distinct initial canonical run')
    need(timestamp(identity['run_started_at'])>=timestamp(bundle.prior_context['terminal']['updated_at']),'current run precedes frozen prior terminal')
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
    if origin=='PriorSuccessorOrigin':need(end<=timestamp(context['terminal']['updated_at']),'producer after prior terminal')
    steps=job.get('steps');need(type(steps) is list,'producer steps missing')
    need(len({s.get('number') for s in steps})==len(steps) and len({s.get('name') for s in steps})==len(steps),'duplicate producer steps')
    previous=start
    for label in ('verifier_step','upload_step'):
        wanted=binding[label];matches=[s for s in steps if s.get('number')==wanted['number'] or s.get('name')==wanted['name']]
        need(len(matches)==1,'missing/ambiguous verifier or upload step');step=matches[0]
        need(step['number']==wanted['number'] and step['name']==wanted['name'] and step.get('status')=='completed' and step.get('conclusion')=='success','verifier/upload identity or result')
        s,e=timestamp(step['started_at']),timestamp(step['completed_at']);need(previous<=s<=e<=end,'verifier/upload time order');previous=e
    base={r['stage_id']:r['pin'] for r in bundle.data['old_stage_rows']+bundle.data['prior_candidate_rows']}[sid]
    expected={'id':base['artifact_id'],'name':base['artifact_name'],'size_in_bytes':base['artifact_zip_bytes'],'digest':'sha256:'+base['artifact_zip_sha256'],'expired':False,'expires_at':base['expires_at']}
    need(all(type(artifact.get(k)) is type(v) and artifact.get(k)==v for k,v in expected.items()),'artifact frozen metadata changed')
    wr=artifact.get('workflow_run',{});need(wr.get('id')==context['run_id'] and wr.get('head_sha')==context['pipeline_commit'] and wr.get('repository_id')==wr.get('head_repository_id')==REPOSITORY_ID and wr.get('head_branch')==context['workflow']['head_branch'],'artifact workflow mismatch')
    pin={k:base[k] for k in PIN_KEYS-PAYLOAD_KEYS}
    pin.update({k:d[k] for k in ('archive_bytes','archive_sha256','receipt_sha256')});pin['raw_descriptor_sha256']=wrapper['raw_descriptor_sha256']
    _pin(pin,origin,sid,base,True)
    for k in ('artifact_id','producer_job_id','artifact_zip_sha256'):need(d[k]==base[k],'descriptor transport binding mismatch')
    return pin


def derive_pinned_inactive_selection(selection,bundle,plan,wrappers):
    """Seal authenticated-wrapper pins, without claiming semantic admission.

    The caller must authenticate actual ZIP bytes and prepare first. This pure
    seam independently checks each projected metadata boundary and native pin.
    Its output is always candidate data and cannot activate a workflow.
    """
    bundle=_bundle(bundle);validate_provider_dag(selection,plan)
    prior=[r.stage_id for r in selection.rows if type(r) is PriorSuccessorOrigin]
    need([w['native_descriptor']['stage_id'] for w in wrappers]==prior,'all selected prior wrappers required in plan order')
    derived={w['native_descriptor']['stage_id']:_wrapper_pin(w,selection,bundle,plan) for w in wrappers}
    obj=selection.data
    for row in obj['stages']:
        if row['origin']=='PriorSuccessorOrigin':row['pin']=derived[row['stage_id']]
    data=json_bytes(obj)
    return parse_selection(data,sha(data),plan,bundle,require_payloads=True)


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
    expected=[r.stage_id for r in selection.rows if type(r) is not CurrentOrigin]
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
    identities=[bundle.old_context['identity'],bundle.prior_context['identity']]
    if current_identity is not None:identities.append(current_identity)
    starts=[timestamp(i['run_started_at']) for i in identities];need(all(s<=now for s in starts),'future run timestamp')
    limits=[s+timedelta(seconds=max_age_seconds) for s in starts]
    limits += [timestamp(bundle.context(o)['prepare']['expires_at']) for o in ORIGINS[:2]]
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

    Every call always counts all 37 old archives and all known selected prior
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
    if prepare_evidence is None:missing.append('authenticated_prior_prepare_bytes')
    if semantic_certificate is None:missing.append('full_frozen_prior_semantic_admission')
    if independent_review is None:missing.append('independent_three_context_review')
    missing.append('separately_reviewed_future_current_execution_adapter')
    return {'active':False,'selection_sha256':selection.raw_sha256,'context_bundle_sha256':bundle.raw_sha256,'missing':missing,'claim':'inactive_candidate_only_clean_rebuild_pending'}


def validate_prepare_bytes(bundle,origin,identity_bytes,inventory_bytes):
    """Check actual authenticated prepare members against native immutable pins."""
    bundle=_bundle(bundle);need(origin in ORIGINS[:2],'historical prepare origin required')
    context=bundle.context(origin)
    need(sha(identity_bytes)==context['prepare']['identity_sha256'],'actual native prepare identity bytes differ')
    need(parse_json(identity_bytes)==context['identity'],'actual prepare identity differs')
    need(sha(inventory_bytes)==context['prepare']['inventory_sha256'],'actual prepared runtime inventory differs')
    return {'origin':origin,'identity_sha256':sha(identity_bytes),'inventory_sha256':sha(inventory_bytes)}
