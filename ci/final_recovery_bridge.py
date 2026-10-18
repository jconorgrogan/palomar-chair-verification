"""Fixed Conron retry bridge. Never relabel an original proof or final receipt.

The producer emits a distinct execution receipt. No aggregate verdict exists here.
All archive authentication and native validation remain in their frozen modules.
"""
from __future__ import annotations
import copy
import hashlib
import json
import math
import re

PROOF_IDENTITY_SHA256 = '10bfb9ed515dda11089ec3a3f8e50d296d60e8c6bd0b83f1784d6b5567e67d11'
ORIGINAL_CONTRACT_SHA256 = 'e9ba3c36ace2ab45c42c1d1d30e5340ea8935d24b9e7e6b206707e476977db45'
RESOURCE_SOURCE_SHA256 = 'b91ffe78701b6c16289b55a6f6afdf03a9ee932d1facc7ca5cb939c2d9dd8710'
FAILURE_SHA256 = 'f5cee34f8fd3a3f32e27cb2777a979a3f80f5ae6748b99a3af0e17d40d766ff1'
ORIGINAL_DEADLINE = '2026-10-22T06:15:54Z'
WORKFLOW = {'head_branch':'verify/hierarchy-c-final-check-recovery-20261018',
    'path':'.github/workflows/hierarchy-c-final-check-recovery.yml',
    'name':'Verify hierarchy C final check recovery'}
EXECUTION_FIELDS = {'schema','role','run_id','run_attempt','run_started_at',
    'pipeline_commit','contract_sha256','proof_identity_sha256',
    'resource_source_sha256','workflow_id','workflow_source_sha256'}

class Rejected(RuntimeError): pass

def need(value, reason):
    if not value: raise Rejected(reason)

def digest(raw): return hashlib.sha256(raw).hexdigest()

def parse(raw):
    def pairs(rows):
        out = {}
        for key,value in rows:
            need(key not in out, 'DUPLICATE_JSON_KEY'); out[key] = value
        return out
    return json.loads(raw, object_pairs_hook=pairs,
        parse_constant=lambda _: (_ for _ in ()).throw(Rejected('NONFINITE_JSON')))

def proof_identity(raw):
    need(type(raw) is bytes and len(raw)==1574 and digest(raw)==PROOF_IDENTITY_SHA256,
         'EXACT_ORIGINAL_PROOF_IDENTITY')
    return parse(raw)

def validate_execution(identity, proof, workflow):
    need(type(identity) is dict and set(identity)==EXECUTION_FIELDS, 'EXECUTION_FIELDS')
    need(identity['schema']=='c092-final-retry-execution-identity-v1' and
         identity['role']=='conron' and identity['run_id']!=proof['run_id'] and
         identity['pipeline_commit']!=proof['pipeline_commit'] and
         identity['run_attempt']=='1', 'NEW_CONRON_EXECUTION_REQUIRED')
    need(type(identity['run_id']) is str and re.fullmatch('[1-9][0-9]*',identity['run_id'])
         and type(identity['pipeline_commit']) is str and
         re.fullmatch('[0-9a-f]{40}',identity['pipeline_commit']), 'EXECUTION_IDENTITY')
    for name in ('contract_sha256','workflow_source_sha256'):
        need(type(identity[name]) is str and re.fullmatch('[0-9a-f]{64}',identity[name]), 'EXECUTION_DIGEST')
    need(identity['proof_identity_sha256']==PROOF_IDENTITY_SHA256 and
         identity['resource_source_sha256']==RESOURCE_SOURCE_SHA256, 'EXECUTION_BINDING')
    need(type(identity['workflow_id']) is int and identity['workflow_id']>0, 'WORKFLOW_ID')
    need(type(workflow) is dict and set(workflow)==set(WORKFLOW)|{'workflow_id','source_sha256'} and
         all(workflow.get(k)==v for k,v in WORKFLOW.items())
         and workflow.get('workflow_id')==identity['workflow_id']
         and workflow.get('source_sha256')==identity['workflow_source_sha256'], 'EXECUTION_WORKFLOW')
    from datetime import datetime, timezone
    started=datetime.strptime(identity['run_started_at'],'%Y-%m-%dT%H:%M:%SZ').replace(tzinfo=timezone.utc)
    need(proof['run_started_at']<identity['run_started_at']<ORIGINAL_DEADLINE,
         'EXECUTION_ORIGINAL_DEADLINE')
    return copy.deepcopy(identity)

def validate_export(*, receipt, wrapper, proof, manifest, plan, selection, bundle,
                    integration_pins, now, final, io):
    """Validate actual extracted export and all embedded native proof identities.

    The caller first authenticates/downloads and extracts the pinned native tar
    with unchanged extract_verified_archive. This function never substitutes a
    metadata projection for those complete-byte checks.
    """
    d=final._validate_wrapper(wrapper,proof,'export_target',final=True,
                             current_workflow_id=integration_pins['current_workflow_id'])
    need(receipt.get('schema')=='fresh-final-evidence-v1' and
         receipt.get('role')=='export_target' and receipt.get('identity')==proof and
         receipt.get('status')=='completed_check_only' and
         receipt.get('proof_pass_claimed') is False, 'ORIGINAL_EXPORT_RECEIPT')
    need(d['receipt_sha256']==final.f.sha(final.f.json_bytes(receipt)), 'ORIGINAL_RECEIPT_BYTES')
    final.validate_final_commands(receipt)
    provenance=final.resolve_provenance(plan=plan,selection=selection,bundle=bundle,
        wrappers=receipt['resolved_provenance'],current_identity=proof,integration_pins=integration_pins)
    need(provenance['sha256']==receipt['resolved_provenance_sha256'], 'FULL_PROVENANCE')
    io.native_receipts_from_text(plan,provenance,receipt['native_stage_receipts_utf8'],final)
    context=final.final_context(manifest=manifest,provenance=provenance,
        object_hashes=receipt['restored_object_hashes'],current_identity=proof,integration_pins=integration_pins)
    need(all(type(receipt.get(k)) is type(v) and receipt.get(k)==v for k,v in context.items()),
         'ORIGINAL_EXPORT_CONTEXT')
    need(context['checked_sources'].get(final.DEFINING_SOURCE['module'])==final.DEFINING_SOURCE['sha256'],
         'EXACT_DEFINING_SOURCE')
    deadline=final.check_deadline(bundle,selection,proof,now=now)
    for row in [wrapper,*provenance['rows']]:
        need(now<final._timestamp(row['authenticated_metadata']['artifact']['expires_at']), 'ORIGINAL_ARTIFACT_EXPIRED')
    return {**context,'export_sha256':receipt['export_sha256'],
        'acceptance_deadline':deadline,
        'original_export':copy.deepcopy({k:v for k,v in wrapper.items() if k!='archive_path'})}

def validate_headroom(record):
    need(type(record) is dict and record.get('schema')=='conron-host-headroom-v1' and
         record.get('status')=='observed' and record.get('required_bytes')==8*1024**3 and
         type(record.get('minimum_available_bytes')) is int and
         record['minimum_available_bytes']>=8*1024**3 and
         record.get('exclusive_reservation') is False and
         record.get('sufficient_checker_memory_proved') is False and
         record.get('host_initial_cgroup_namespace_is_trusted_environment_assumption') is True,
         'HEADROOM_RECORD')
    need(type(record.get('samples')) is list and len(record['samples'])==2,
         'HEADROOM_SAMPLES')
    need(len(json.dumps(record,sort_keys=True,allow_nan=False).encode())<=128*1024,
         'HEADROOM_RECORD_BOUND')

def validate_retry_command(record, *, toolchain_root, export_path, resources, final):
    spec=resources.conron_spec(toolchain_root,export_path)
    final._successful_command(record,spec)
    need(record.get('cleanup_bound_seconds')==3.0 and
         type(record.get('cleanup_elapsed_seconds')) in (int,float) and
         math.isfinite(record['cleanup_elapsed_seconds']) and
         0<=record['cleanup_elapsed_seconds']<=3.0, 'UNCHANGED_CLEANUP_BOUND')
    for name in ('stdout','stderr'): final._file_info(record.get(name))
    need(sum(record[name]['bytes'] for name in ('stdout','stderr'))<=32*1024**2,
         'COMBINED_LOG_BOUND')

def retry_receipt(*, proof_raw, execution, workflow, context, command, headroom,
                  files, paths, failure_binding, resources, final):
    proof=proof_identity(proof_raw)
    validate_execution(execution,proof,workflow)
    validate_headroom(headroom)
    validate_retry_command(command,toolchain_root=paths['toolchain_root'],
                           export_path=paths['export_path'],resources=resources,final=final)
    need(type(failure_binding) is dict and failure_binding.get('failure_sha256')==FAILURE_SHA256,
         'EXACT_PRIOR_CONRON_FAILURE')
    need(set(files)=={'conron.stdout','conron.stderr','ORIGINAL_PROOF_IDENTITY.json',
         'ORIGINAL_EXPORT_RECEIPT.json','ORIGINAL_EXPORT_WRAPPER.json','HEADROOM.json',
         'EXECUTION_IDENTITY.json','PRIOR_FAILURE.json','inventory.json'}, 'EXACT_RETRY_MEMBERS')
    for value in files.values(): final._file_info(value)
    need(files['conron.stdout']==command['stdout'] and files['conron.stderr']==command['stderr'],
         'RETRY_LOG_BINDING')
    need(files['ORIGINAL_PROOF_IDENTITY.json']=={'bytes':1574,'sha256':PROOF_IDENTITY_SHA256},
         'ORIGINAL_PROOF_BYTES')
    for name,value in (('HEADROOM.json',headroom),('EXECUTION_IDENTITY.json',execution),
                       ('PRIOR_FAILURE.json',failure_binding),
                       ('ORIGINAL_EXPORT_WRAPPER.json',context['original_export'])):
        raw=final.f.json_bytes(value)
        need(files[name]=={'bytes':len(raw),'sha256':digest(raw)}, 'RETRY_RECORD_BINDING')
    need(files['ORIGINAL_EXPORT_RECEIPT.json']['sha256']==
         context['original_export']['native_descriptor']['receipt_sha256'], 'RETAINED_EXPORT_RECEIPT')
    need(files['inventory.json']=={'bytes':3292808,'sha256':proof['toolchain_inventory_sha256']},
         'RETAINED_EXACT_RUNTIME_INVENTORY')
    return {'schema':'c092-final-retry-evidence-v1','role':'conron',
        'status':'completed_check_only','proof_pass_claimed':False,
        'overall_task_complete':False,'aggregate_verdict':'not_implemented',
        'proof_identity':proof,'execution_identity':copy.deepcopy(execution),
        'execution_workflow':copy.deepcopy(workflow),'resource_source_sha256':RESOURCE_SOURCE_SHA256,
        'original_deadline':ORIGINAL_DEADLINE,'commands':[copy.deepcopy(command)],
        'execution_paths':copy.deepcopy(paths),'files':copy.deepcopy(files),
        'headroom':copy.deepcopy(headroom),'prior_failure':copy.deepcopy(failure_binding),
        'proof_context':copy.deepcopy(context)}

def aggregate_verdict(*args,**kwargs):
    raise Rejected('AGGREGATE_JOIN_NOT_IMPLEMENTED')
