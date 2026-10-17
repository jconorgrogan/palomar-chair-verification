"""Inactive fixed-CI C087 controller, with an explicit trusted one-job boundary.

The trusted workflow owns immutable source/setup trees, one CPU, original job
watchdog and no other writers. Python policy is misuse detection, not hostile
code isolation. No CVE, complete physical-write, or final-proof claim is made.
"""
from __future__ import annotations
import argparse,copy,hashlib,json,math,os,secrets,stat,sys,time,types
from datetime import datetime,timezone
from pathlib import Path

EXECUTION_RELEASED=True
LIMITS={'address_space_bytes':8*1024**3,'rss_tree_bytes':8*1024**3,'max_created_file_bytes':512*1024**2}
ENV={'LANG':'C.UTF-8','LC_ALL':'C.UTF-8','TZ':'UTC'}
CONTRACT_SHA='2848fad58bf59da1958c7e1632e841c1bae78f22ab728b1098a9426977aef334'
INVENTORY_SHA='42bd268b1ca3e9bf89f4149ac427d6c0e76f735233b092a6df4ca27a2c2db7ea'
MAX_JSON=64*1024**2
MAX_EVIDENCE=256*1024**2
EVIDENCE_RESERVE=2*1024**2
_USED=False
class Rejected(ValueError):pass
def need(ok,message):
 if not ok:raise Rejected(message)
def sha(raw):return hashlib.sha256(raw).hexdigest()
def jb(value):return (json.dumps(value,sort_keys=True,indent=2,allow_nan=False)+'\n').encode()
def parse(raw):
 def pairs(rows):
  out={}
  for k,v in rows:need(k not in out,'duplicate JSON key');out[k]=v
  return out
 return json.loads(raw,object_pairs_hook=pairs,parse_constant=lambda _:(_ for _ in ()).throw(Rejected('nonfinite JSON')))
def canonical(path):
 path=Path(path);need(path.is_absolute() and str(path)==str(path.absolute()) and '..' not in path.parts,'absolute canonical path')
 for part in (path,*path.parents):need(not part.is_symlink(),'symlink in path')
 return path
def read(path,maximum=MAX_JSON,expected=None):
 path=canonical(path);fd=os.open(path,os.O_RDONLY|os.O_NOFOLLOW|os.O_NONBLOCK)
 try:
  before=os.fstat(fd);need(stat.S_ISREG(before.st_mode) and before.st_nlink==1 and before.st_uid==os.getuid() and not before.st_mode&0o022 and before.st_size<=maximum,'owned bounded regular file')
  identity=lambda s:(s.st_dev,s.st_ino,s.st_mode,s.st_uid,s.st_gid,s.st_nlink,s.st_size,s.st_mtime_ns,s.st_ctime_ns)
  chunks=[];n=0
  while block:=os.read(fd,min(1024**2,maximum+1-n)):
   chunks.append(block);n+=len(block);need(n<=maximum,'file grew beyond bound')
  raw=b''.join(chunks);need(identity(before)==identity(os.fstat(fd))==identity(path.lstat()) and n==before.st_size,'file changed during read')
  if expected is not None:need({'bytes':len(raw),'sha256':sha(raw)}==expected,'fixed source bytes changed')
  return raw
 finally:os.close(fd)
def load(name,path,pin):
 need(name not in sys.modules,'fixed import alias already present');raw=read(path,expected=pin)
 module=types.ModuleType(name);module.__file__=str(path);sys.modules[name]=module
 try:exec(compile(raw,str(path),'exec',dont_inherit=True),module.__dict__)
 except BaseException:sys.modules.pop(name,None);raise
 return module

def bootstrap(pipeline,contract_sha,budget):
 pipeline=canonical(pipeline);raw=read(pipeline/'c087-minimal-contract.json',4*1024**2)
 need(sha(raw)==contract_sha,'external controller contract pin');contract=parse(raw)
 need(contract['schema']=='c087-minimal-fixed-ci-controller-v1' and contract['activation_allowed'] is EXECUTION_RELEASED,'contract must match the exact reviewed source release state')
 for name,pin in contract['files'].items():
  need(not name.startswith('/') and all(x not in ('','.','..') for x in name.split('/')),'relative package source')
  read(pipeline/name,expected=pin);budget.check()
 return contract

def native_inputs(graph,seam,roots,certificate_raw,certificate_sha,nonce,deadline):
 """Exact0915 input construction; SOURCE_MANIFEST is source-package metadata."""
 f,p,local=graph.f,graph.p,graph.local;latest=roots['latest_pipeline'];prior=roots['prior_pipeline'];ci=latest/'ci'
 cert=p.parse_json(certificate_raw)
 contract=f.pinned_load(ci/'three_context_contract.json',CONTRACT_SHA)
 bundle=p.validate_context_bundle(local.read_pinned(ci/'CONTEXT_BUNDLE.json',p.BUNDLE_SHA256),p.BUNDLE_SHA256)
 plan=f.pinned_load(ci/'plan.json',p.PLAN_SHA256);profiles=f.pinned_load(ci/'profiles.json',contract['profiles_sha256'])
 selection=p.parse_selection(local.read_pinned(ci/'three_context_selection.json',contract['selection_sha256']),contract['selection_sha256'],plan,bundle,require_payloads=True)
 manifest=f.pinned_load(prior/'SOURCE_MANIFEST.json',p.PRIOR_MANIFEST)
 context=cert['contexts']['LatestSuccessorOrigin']
 def acquired(name):
  need(name in cert['files'],'unlisted acquisition metadata');return read(roots['acquisition']/name,expected=cert['files'][name])
 identity=p.parse_json(acquired(context['identity_path']));inventory=p.parse_json(acquired(context['inventory_path']))
 prior_files_raw=local.read_pinned(latest/'admission/inputs/PRIOR_FILES.json',graph.runner.PRIOR_FILES_SHA)
 old_manifest=f.pinned_load(prior/'ci/original/SOURCE_MANIFEST.json',p.OLD_MANIFEST)
 prior_contract=f.pinned_load(prior/'ci/continuation_contract.json',bundle.prior_context['identity']['contract_sha256'])
 source_delta=f.pinned_load(prior/'ci/source_delta.json',p.SOURCE_DELTA)
 native_bytes={s['stage_id']:{'descriptor':acquired(s['raw_descriptor']['path']),'receipt':acquired(s['raw_receipt']['path'])} for s in cert['stages']}
 pins={'current_pipeline_commit':identity['pipeline_commit'],'current_contract_sha256':identity['contract_sha256'],'selection_sha256':selection.raw_sha256,'admission_certificate_sha256':contract['admission_certificate_sha256'],'admission_reconciliation_sha256':contract['admission_reconciliation_sha256'],'current_workflow_id':387046066}
 runner=seam.HistoricalAdmissionRunner(selection=selection,bundle=bundle,integration_pins=pins,prior_root=prior,admission_root=latest/'admission',prior_files_bytes=prior_files_raw,old_manifest=old_manifest,prior_manifest=manifest,source_delta=source_delta,prior_contract=prior_contract,host_deadline_monotonic=deadline,certificate_raw=certificate_raw,parent_certificate_sha256=certificate_sha,expected_session_nonce=nonce,acquisition_root=roots['acquisition'],wrappers=cert['wrappers'],native_bytes=native_bytes,contract=contract,manifest=manifest,plan=plan,profiles=profiles,identity=identity,source_root=roots['research_source'],toolchain_root=roots['runtime_placeholder'],toolchain_inventory=inventory,workspace=roots['container']/'admitted',owned_downloads=None)
 return runner,native_bytes

def derive_outputs(runner,native_bytes,model):
 """Independent before-child map. No report or filesystem hash is an input."""
 origin={row.stage_id:type(row).__name__ for row in runner.selection.rows};scope=runner._scope.data
 static=model.static_outputs(plan=runner.plan,origin_by_stage=origin,wrappers=runner._wrappers,native_bytes=native_bytes,prior_identity=runner.bundle.prior_context['identity'],prior_contract=runner.prior_contract)
 native,selection_raw=runner._native_inputs();native['wrappers']=scope['historical_native_view']
 request={'schema':'inactive-checked-transfer-request-v2','native':native,'native_selection_utf8':selection_raw.decode(),'native_selection_sha256':sha(selection_raw),'scope':{'origin_by_stage':origin,'expected_native_descriptors':[w['native_descriptor'] for w in native['wrappers']],'expected_full_native_descriptors':scope['native_descriptors'],'expected_objects':scope['historical_objects'],'current_identity':runner.identity,'current_manifest':runner.manifest,'current_contract':runner.contract,'target_stage':'build_087'}}
 expected_objects={rec['module']:rec['outputs'] for pair in native_bytes.values() for rec in parse(pair['receipt'])['modules']}
 evidence={sid:{name[len('admitted/restore-evidence/'+sid+'/'):]:pin['sha256'] for name,pin in static['files'].items() if name.startswith('admitted/restore-evidence/'+sid+'/')} for sid in scope['expected_stage_ids']}
 anticipated={'schema':'c087-native-admission-report-v1','status':'native_admission_only','target_stage':'build_087','module_count':6218,'stage_count':85,'companion_count':37308,'certificate_sha256':runner._certificate.sha256,'scope_sha256':runner._scope.sha256,'native_input_binding_sha256':runner._input_binding,'frozen_graph_sha256':sys.modules['frozen_native'].PINS_SHA256,'objects':expected_objects,'native_descriptors':scope['native_descriptors'],'restore_evidence_hashes':evidence,'raw_archive_bytes':scope['raw_archive_bytes'],**{k:False for k in ('executable_authority','activation_allowed','proof_pass_claimed','runtime_installed','kernel_executed')}}
 return static,request,anticipated

def child_layout(package,roots,container,request_path,invocation_path):
 """Fixed no-network/no-runtime admission shell; no nested supervisor."""
 env=dict(ENV);argv=['/usr/bin/bwrap','--unshare-all','--die-with-parent','--clearenv','--proc','/proc','--dev','/dev','--tmpfs','/tmp']
 for path in ['/usr','/bin','/lib','/lib64',str(package),*[str(roots[k]) for k in ('latest_pipeline','prior_pipeline','research_source','source_package','acquisition','runtime_placeholder')]]:argv+=['--ro-bind',path,path]
 argv+=['--bind',str(container),str(container)]
 for key,value in sorted(env.items()):argv+=['--setenv',key,value]
 argv+=['--chdir',str(container),'--','/usr/bin/python3','-I','-S','-B',str(package/'code/minimal.py'),'--admission-child',str(request_path),str(invocation_path)]
 return argv,env

def _accept_result_safety(result,timeout):
 """Immediate actual native supervisor result check, before child files."""
 keys={'exit_code','timed_out','log_overflow','memory_exceeded','surviving_children','escaped_descendants','new_sessions_explicitly_allowed','process_group_empty','descendants_empty','cleanup_bound_seconds','cleanup_elapsed_seconds','peak_sampled_tree_rss_bytes','elapsed_seconds'}
 need(type(result) is dict and set(result)==keys and type(result['exit_code']) is int,'actual native child result required')
 need(all(result[k] is False for k in ('timed_out','log_overflow','memory_exceeded','surviving_children','escaped_descendants','new_sessions_explicitly_allowed')) and all(result[k] is True for k in ('process_group_empty','descendants_empty')),'child containment/resource/cleanup failure')
 need(result['cleanup_bound_seconds']==3.0 and type(result['cleanup_elapsed_seconds']) in (int,float) and math.isfinite(result['cleanup_elapsed_seconds']) and 0<=result['cleanup_elapsed_seconds']<=3,'child cleanup bound')
 need(type(result['peak_sampled_tree_rss_bytes']) is int and 0<=result['peak_sampled_tree_rss_bytes']<=LIMITS['rss_tree_bytes'],'child RSS observation')
 need(type(timeout) is int and 0<timeout<=19800 and type(result['elapsed_seconds']) in (int,float) and math.isfinite(result['elapsed_seconds']) and result['elapsed_seconds']>=0,'child timeout/elapsed result')

def accept_child_result(result,timeout):
 _accept_result_safety(result,timeout)
 need(result['exit_code']==0,'actual successful native child exit required')

class _Context:
 """Constructed only inside one live controller after independent admission."""
 def __init__(self,*args,**kwargs):raise Rejected('no generic engine-context constructor')

class _TrustedRun:
 def __init__(self,*args,**kwargs):raise Rejected('fixed entry owns construction')

# The live orchestration is defined separately below; no callback/receipt factory
# grants it authority, and the inactive public entry refuses before this point.

def _modules(pipeline,contract):
 code=pipeline/'ci/c087';pins=contract['files'];out={}
 for name,rel in [('protocol','admission/code/protocol.py'),('output_model','admission/code/output_model.py'),('frozen_native','admission/code/frozen_native.py'),('probe_policy','engine/probe_policy.py'),('original_probe_commands','engine/original_probe_commands.py'),('probe_engine','engine/probe_engine.py'),('official_runtime','runtime/official_runtime.py')]:
  out[name]=load(name,code/rel,pins['ci/c087/'+rel])
 return out

def _snapshot(module,path,budget,*,max_bytes=16*1024**3,max_entries=300000):
 result=module.snapshot(path,max_bytes=max_bytes,max_entries=max_entries,checkpoint=budget.check)
 budget.check();return result

# Finite diagnostic labels only; these do not grant authority or alter a gate.
SETUP_GATES=('fixed_modules','entry_record','native_graph_load','native_seam_load',
 'native_graph_verify','transfer_fixed_files','source_manifest','source_extract',
 'runtime_download','runtime_archive_length','runtime_installer_load','runtime_install',
 'runtime_inventory_write','runtime_inventory_pin','native_contract','runtime_verify',
 'official_runtime_bind','owned_layout','snapshot_latest_pipeline','snapshot_prior_pipeline',
 'snapshot_research_source','snapshot_helper_source','snapshot_runtime_placeholder','snapshot_controller')

RUN_GATES=('compatibility_smoke', 'compatibility_revalidate', 'acquisition_revalidate', 'acquisition_layout', 'acquisition_process', 'acquisition_completion', 'acquisition_certificate', 'acquisition_snapshot', 'native_inputs', 'native_expected_map', 'admission_prepare', 'admission_process', 'admission_inputs_revalidate', 'admission_expected_transfer', 'admission_outputs', 'admission_report', 'admission_final_revalidate', 'engine_prepare', 'engine_dispatch', 'engine_inputs_revalidate', 'engine_response', 'evidence_copy', 'evidence_revalidate', 'evidence_complete')

def _phase_mark(owner,gate,position):
 owner._run_gate=gate;owner._run_position=position
 if position=='after':owner._run_completed.append(gate)

def _safe_native_result(result):
 """Numeric/boolean result only; never argv, environment, logs or arbitrary repr."""
 booleans=('timed_out','log_overflow','memory_exceeded','surviving_children','escaped_descendants','new_sessions_explicitly_allowed','process_group_empty','descendants_empty')
 times=('cleanup_bound_seconds','cleanup_elapsed_seconds','elapsed_seconds')
 if type(result) is not dict or set(result)!={*booleans,*times,'exit_code','peak_sampled_tree_rss_bytes'}:return None
 if any(type(result[k]) is not bool for k in booleans):return None
 if type(result['exit_code']) is not int or not -255<=result['exit_code']<=255:return None
 if type(result['peak_sampled_tree_rss_bytes']) is not int or not 0<=result['peak_sampled_tree_rss_bytes']<2**63:return None
 if any(type(result[k]) not in (int,float) or not math.isfinite(result[k]) or not 0<=result[k]<=10**9 for k in times):return None
 return dict(result)

def _observe_native_result(owner,phase,result):
 owner._last_native_phase=phase;owner._last_native_result=_safe_native_result(result)

def _setup_mark(owner,gate,position):
 owner._setup_gate=gate;owner._setup_position=position
 if position=='after':owner._setup_completed.append(gate)

def _setup_reason(error):
 # Match exact reviewed types and one bounded builtin string. Never stringify
 # arbitrary arguments, exceptions, traceback locals, URLs or response bodies.
 category='UNCLASSIFIED_EXCEPTION'
 reviewed=type(error) is Rejected
 if reviewed:category='CONTROLLER_REJECTED'
 for name,label in (('frozen_native','FROZEN_SOURCE_REJECTED'),('checked_transfer','FIXED_TRANSFER_REJECTED'),('fresh_stage','NATIVE_SETUP_REJECTED'),('official_runtime','RUNTIME_BIND_REJECTED'),('protocol','INPUT_SNAPSHOT_REJECTED'),('job_budget','BUDGET_REJECTED'),('probe_engine','ENGINE_REJECTED'),('probe_policy','PROBE_POLICY_REJECTED'),('output_model','OUTPUT_MODEL_REJECTED'),('three_context_policy','NATIVE_POLICY_REJECTED'),('three_context_local','NATIVE_LOCAL_REJECTED'),('three_context_final','NATIVE_FINAL_REJECTED'),('three_context_execution_policy','NATIVE_EXECUTION_POLICY_REJECTED'),('three_context_current_transport','NATIVE_TRANSPORT_REJECTED'),('three_context_runner','NATIVE_RUNNER_REJECTED')):
  module=sys.modules.get(name)
  if type(module) is types.ModuleType and type(error) is vars(module).get('Rejected'):
   category=label;reviewed=True;break
 reasons={
  'Boolean/floating raw ledger rejected':'CERTIFICATE_BOOLEAN_FLOATING_RAW_LEDGER_REJECTED',
  'C087 only':'OUTPUT_C087_ONLY',
  'actual invocation/effective timeout mismatch':'PROBE_ACTUAL_INVOCATION_EFFECTIVE_TIMEOUT_MISMATCH',
  'admission already used or poisoned':'ADMISSION_ADMISSION_ALREADY_USED_OR_POISONED',
  'admission seam may not be subclassed':'ADMISSION_ADMISSION_SEAM_MAY_NOT_BE_SUBCLASSED',
  'admission workspace must be new':'ADMISSION_ADMISSION_WORKSPACE_MUST_BE_NEW',
  'admitted predecessors changed':'ENGINE_ADMITTED_PREDECESSORS_CHANGED',
  'aggregate complete logs exceeded':'ENGINE_AGGREGATE_COMPLETE_LOGS_EXCEEDED',
  'all engine roots must be disjoint':'ENGINE_ALL_ENGINE_ROOTS_MUST_BE_DISJOINT',
  'all selected native tars must remain retained in this adapter':'ADMISSION_ALL_SELECTED_NATIVE_TARS_MUST_REMAIN_RETAINED_IN_THIS_ADAPTER',
  'ambiguous producer step':'CERTIFICATE_AMBIGUOUS_PRODUCER_STEP',
  'artifact digest':'CERTIFICATE_ARTIFACT_DIGEST',
  'async-off audit missing':'ENGINE_ASYNC_OFF_AUDIT_MISSING',
  'audit fields differ':'PROBE_AUDIT_FIELDS_DIFFER',
  'audit overclaim':'PROBE_AUDIT_OVERCLAIM',
  'audit target/order differs':'PROBE_AUDIT_TARGET_ORDER_DIFFERS',
  'audit universes differ':'PROBE_AUDIT_UNIVERSES_DIFFER',
  'backward wall clock':'CERTIFICATE_BACKWARD_WALL_CLOCK',
  'bounded raw audit output required':'PROBE_BOUNDED_RAW_AUDIT_OUTPUT_REQUIRED',
  'bounded tree capacity exceeded':'ENGINE_BOUNDED_TREE_CAPACITY_EXCEEDED',
  'certificate chronology/deadline':'CERTIFICATE_CERTIFICATE_CHRONOLOGY_DEADLINE',
  'checker flags changed':'PROBE_CHECKER_FLAGS_CHANGED',
  'checker timeout changed':'PROBE_CHECKER_TIMEOUT_CHANGED',
  'clean path required':'OUTPUT_CLEAN_PATH_REQUIRED',
  'combined output cap exceeded':'PROBE_COMBINED_OUTPUT_CAP_EXCEEDED',
  'command logs already exist':'ENGINE_COMMAND_LOGS_ALREADY_EXIST',
  'command resource/cleanup failure':'PROBE_COMMAND_RESOURCE_CLEANUP_FAILURE',
  'committed diagnostic output changed':'ENGINE_COMMITTED_DIAGNOSTIC_OUTPUT_CHANGED',
  'compile quarantine already exists':'ENGINE_COMPILE_QUARANTINE_ALREADY_EXISTS',
  'compile timeout changed':'PROBE_COMPILE_TIMEOUT_CHANGED',
  'complete bounded logs required':'PROBE_COMPLETE_BOUNDED_LOGS_REQUIRED',
  'complete exact audit output required':'PROBE_COMPLETE_EXACT_AUDIT_OUTPUT_REQUIRED',
  'complete fixed native path map':'OUTPUT_COMPLETE_FIXED_NATIVE_PATH_MAP',
  'complete live log bytes required':'PROBE_COMPLETE_LIVE_LOG_BYTES_REQUIRED',
  'control output changed':'ENGINE_CONTROL_OUTPUT_CHANGED',
  'default/async exact raw theorem audit differs':'PROBE_DEFAULT_ASYNC_EXACT_RAW_THEOREM_AUDIT_DIFFERS',
  'derived certificate reserve':'OUTPUT_DERIVED_CERTIFICATE_RESERVE',
  'diagnostic output directory differs':'ENGINE_DIAGNOSTIC_OUTPUT_DIRECTORY_DIFFERS',
  'diagnostic output top-level files differ':'ENGINE_DIAGNOSTIC_OUTPUT_TOP_LEVEL_FILES_DIFFER',
  'diagnostic/predecessor provider collision':'ENGINE_DIAGNOSTIC_PREDECESSOR_PROVIDER_COLLISION',
  'duplicate audit JSON key':'PROBE_DUPLICATE_AUDIT_JSON_KEY',
  'duplicate engine JSON key':'ENGINE_DUPLICATE_ENGINE_JSON_KEY',
  'duplicate/Boolean step number':'CERTIFICATE_DUPLICATE_BOOLEAN_STEP_NUMBER',
  'engine dependency import path':'ENGINE_ENGINE_DEPENDENCY_IMPORT_PATH',
  'engine input root binding':'ENGINE_ENGINE_INPUT_ROOT_BINDING',
  'engine retained/output root binding':'ENGINE_ENGINE_RETAINED_OUTPUT_ROOT_BINDING',
  'engine source dependency changed':'ENGINE_ENGINE_SOURCE_DEPENDENCY_CHANGED',
  'exact admitted companion count required':'ENGINE_EXACT_ADMITTED_COMPANION_COUNT_REQUIRED',
  'exact live record shape required':'PROBE_EXACT_LIVE_RECORD_SHAPE_REQUIRED',
  'exact marker bytes':'OUTPUT_EXACT_MARKER_BYTES',
  'exact observed inode':'OUTPUT_EXACT_OBSERVED_INODE',
  'exact ordered retained stages required':'CERTIFICATE_EXACT_ORDERED_RETAINED_STAGES_REQUIRED',
  'exact paired profiles required':'PROBE_EXACT_PAIRED_PROFILES_REQUIRED',
  'exact six modern output companions required':'PROBE_EXACT_SIX_MODERN_OUTPUT_COMPANIONS_REQUIRED',
  'exact target source required':'ENGINE_EXACT_TARGET_SOURCE_REQUIRED',
  'exact verifier/upload steps required':'CERTIFICATE_EXACT_VERIFIER_UPLOAD_STEPS_REQUIRED',
  'exclusive registered diagnostic output required':'ENGINE_EXCLUSIVE_REGISTERED_DIAGNOSTIC_OUTPUT_REQUIRED',
  'file changed during hash':'ENGINE_FILE_CHANGED_DURING_HASH',
  'finite shared host deadline required':'ADMISSION_FINITE_SHARED_HOST_DEADLINE_REQUIRED',
  'fixed control expectations required':'ENGINE_FIXED_CONTROL_EXPECTATIONS_REQUIRED',
  'fixed engine RESULT changed':'ENGINE_FIXED_ENGINE_RESULT_CHANGED',
  'fixed engine dependency set':'ENGINE_FIXED_ENGINE_DEPENDENCY_SET',
  'fixed engine manifest binding':'ENGINE_FIXED_ENGINE_MANIFEST_BINDING',
  'fixed engine manifest schema':'ENGINE_FIXED_ENGINE_MANIFEST_SCHEMA',
  'fixed helper prefix changed':'ENGINE_FIXED_HELPER_PREFIX_CHANGED',
  'fixed helper source bytes required':'ENGINE_FIXED_HELPER_SOURCE_BYTES_REQUIRED',
  'fixed native source identity':'ENGINE_FIXED_NATIVE_SOURCE_IDENTITY',
  'fixed output byte sizes':'OUTPUT_FIXED_OUTPUT_BYTE_SIZES',
  'global raw cap exceeded':'CERTIFICATE_GLOBAL_RAW_CAP_EXCEEDED',
  'helper/check/audit failed':'PROBE_HELPER_CHECK_AUDIT_FAILED',
  'historical admission never grants command, build, final, or executor authority':'ADMISSION_HISTORICAL_ADMISSION_NEVER_GRANTS_COMMAND_BUILD_FINAL_OR_EXECUTOR_AUTHORITY',
  'historical admission workspace must be new':'ADMISSION_HISTORICAL_ADMISSION_WORKSPACE_MUST_BE_NEW',
  'historical implementation inventory changed':'ADMISSION_HISTORICAL_IMPLEMENTATION_INVENTORY_CHANGED',
  'host deadline expired or renewed':'ADMISSION_HOST_DEADLINE_EXPIRED_OR_RENEWED',
  'insufficient measured native restore inodes':'ADMISSION_INSUFFICIENT_MEASURED_NATIVE_RESTORE_INODES',
  'insufficient measured native restore/output space':'ADMISSION_INSUFFICIENT_MEASURED_NATIVE_RESTORE_OUTPUT_SPACE',
  'invalid audit output':'PROBE_INVALID_AUDIT_OUTPUT',
  'invalid bounded integer':'PROBE_INVALID_BOUNDED_INTEGER',
  'invalid elapsed time':'PROBE_INVALID_ELAPSED_TIME',
  'invalid native RSS observation':'PROBE_INVALID_NATIVE_RSS_OBSERVATION',
  'invalid native cleanup elapsed':'PROBE_INVALID_NATIVE_CLEANUP_ELAPSED',
  'invalid output digest':'PROBE_INVALID_OUTPUT_DIGEST',
  'invalid remaining shared deadline':'PROBE_INVALID_REMAINING_SHARED_DEADLINE',
  'inventory JSON size bound':'CERTIFICATE_INVENTORY_JSON_SIZE_BOUND',
  'live argv/environment/resource/layout/name differs':'PROBE_LIVE_ARGV_ENVIRONMENT_RESOURCE_LAYOUT_NAME_DIFFERS',
  'live combined logs exceed cap':'PROBE_LIVE_COMBINED_LOGS_EXCEED_CAP',
  'live log bytes/hash mismatch':'PROBE_LIVE_LOG_BYTES_HASH_MISMATCH',
  'live log cap differs':'PROBE_LIVE_LOG_CAP_DIFFERS',
  'live log row schema differs':'PROBE_LIVE_LOG_ROW_SCHEMA_DIFFERS',
  'live nominal timeout differs':'PROBE_LIVE_NOMINAL_TIMEOUT_DIFFERS',
  'live resource caps differ':'PROBE_LIVE_RESOURCE_CAPS_DIFFER',
  'live session escape allowance forbidden':'PROBE_LIVE_SESSION_ESCAPE_ALLOWANCE_FORBIDDEN',
  'live spec/record required':'PROBE_LIVE_SPEC_RECORD_REQUIRED',
  'log changed after hashing':'ENGINE_LOG_CHANGED_AFTER_HASHING',
  'log exceeds bound':'ENGINE_LOG_EXCEEDS_BOUND',
  'measured allocation unit':'OUTPUT_MEASURED_ALLOCATION_UNIT',
  'native certificate bound':'OUTPUT_NATIVE_CERTIFICATE_BOUND',
  'native cleanup bound':'ENGINE_NATIVE_CLEANUP_BOUND',
  'native cleanup elapsed':'ENGINE_NATIVE_CLEANUP_ELAPSED',
  'native cleanup guard differs':'PROBE_NATIVE_CLEANUP_GUARD_DIFFERS',
  'native executor read changed':'ENGINE_NATIVE_EXECUTOR_READ_CHANGED',
  'native executor source changed':'ENGINE_NATIVE_EXECUTOR_SOURCE_CHANGED',
  'native file absent from inventory':'CERTIFICATE_NATIVE_FILE_ABSENT_FROM_INVENTORY',
  'native live result shape differs':'PROBE_NATIVE_LIVE_RESULT_SHAPE_DIFFERS',
  'native origin required':'OUTPUT_NATIVE_ORIGIN_REQUIRED',
  'native payload size':'OUTPUT_NATIVE_PAYLOAD_SIZE',
  'native resource observation':'ENGINE_NATIVE_RESOURCE_OBSERVATION',
  'native result allowed a new session':'PROBE_NATIVE_RESULT_ALLOWED_A_NEW_SESSION',
  'native result shape':'ENGINE_NATIVE_RESULT_SHAPE',
  'native session policy':'ENGINE_NATIVE_SESSION_POLICY',
  'native tar absent from inventory':'CERTIFICATE_NATIVE_TAR_ABSENT_FROM_INVENTORY',
  'new workspace required':'ADMISSION_NEW_WORKSPACE_REQUIRED',
  'nonfinite JSON':'OUTPUT_NONFINITE_JSON',
  'nonfinite audit':'PROBE_NONFINITE_AUDIT',
  'nonfinite engine manifest':'ENGINE_NONFINITE_ENGINE_MANIFEST',
  'nonnegative protocol byte caps':'OUTPUT_NONNEGATIVE_PROTOCOL_BYTE_CAPS',
  'nonstandard/duplicate axioms':'PROBE_NONSTANDARD_DUPLICATE_AXIOMS',
  'observed allocation unit':'OUTPUT_OBSERVED_ALLOCATION_UNIT',
  'only explicit async-off variation allowed':'PROBE_ONLY_EXPLICIT_ASYNC_OFF_VARIATION_ALLOWED',
  'only the exact bounded default thread-creation abort may continue to B':'PROBE_ONLY_THE_EXACT_BOUNDED_DEFAULT_THREAD_CREATION_ABORT_MAY_CONTINUE_TO_B',
  'ordered predecessors required':'OUTPUT_ORDERED_PREDECESSORS_REQUIRED',
  'ordered wrapper scope':'OUTPUT_ORDERED_WRAPPER_SCOPE',
  'original absolute host deadline must be a finite float':'CERTIFICATE_ORIGINAL_ABSOLUTE_HOST_DEADLINE_MUST_BE_A_FINITE_FLOAT',
  'outer native origin mismatch':'OUTPUT_OUTER_NATIVE_ORIGIN_MISMATCH',
  'output map required':'PROBE_OUTPUT_MAP_REQUIRED',
  'output metadata fields differ':'PROBE_OUTPUT_METADATA_FIELDS_DIFFER',
  'paired profile order differs':'PROBE_PAIRED_PROFILE_ORDER_DIFFERS',
  'paired profiles differ beyond async scheduling':'PROBE_PAIRED_PROFILES_DIFFER_BEYOND_ASYNC_SCHEDULING',
  'parent admission session already consumed':'ADMISSION_PARENT_ADMISSION_SESSION_ALREADY_CONSUMED',
  'parent admission session nonce required':'ADMISSION_PARENT_ADMISSION_SESSION_NONCE_REQUIRED',
  'parent engine invocation binding':'ENGINE_PARENT_ENGINE_INVOCATION_BINDING',
  'parent engine invocation changed':'ENGINE_PARENT_ENGINE_INVOCATION_CHANGED',
  'parent session nonce required':'CERTIFICATE_PARENT_SESSION_NONCE_REQUIRED',
  'parent-authenticated certificate bytes changed':'CERTIFICATE_PARENT_AUTHENTICATED_CERTIFICATE_BYTES_CHANGED',
  'predecessor content map differs':'ENGINE_PREDECESSOR_CONTENT_MAP_DIFFERS',
  'prepare file absent from retained inventory':'CERTIFICATE_PREPARE_FILE_ABSENT_FROM_RETAINED_INVENTORY',
  'prepare identity size bound':'CERTIFICATE_PREPARE_IDENTITY_SIZE_BOUND',
  'production capability/controller binding is not yet sealed':'ENGINE_PRODUCTION_CAPABILITY_CONTROLLER_BINDING_IS_NOT_YET_SEALED',
  'raw JSON bytes required':'OUTPUT_RAW_JSON_BYTES_REQUIRED',
  'raw audit gate failed':'PROBE_RAW_AUDIT_GATE_FAILED',
  'raw auditor stderr':'ENGINE_RAW_AUDITOR_STDERR',
  'raw bytes required':'OUTPUT_RAW_BYTES_REQUIRED',
  'raw type/proof absent':'PROBE_RAW_TYPE_PROOF_ABSENT',
  'receipt hash':'OUTPUT_RECEIPT_HASH',
  'regular unshared file required':'ENGINE_REGULAR_UNSHARED_FILE_REQUIRED',
  'relative path required':'OUTPUT_RELATIVE_PATH_REQUIRED',
  'resource ceiling changed':'PROBE_RESOURCE_CEILING_CHANGED',
  'retained acquisition file changed':'CERTIFICATE_RETAINED_ACQUISITION_FILE_CHANGED',
  'retained bytes changed':'CERTIFICATE_RETAINED_BYTES_CHANGED',
  'retained complete profile changed':'ENGINE_RETAINED_COMPLETE_PROFILE_CHANGED',
  'retained failed-profile evidence changed':'ENGINE_RETAINED_FAILED_PROFILE_EVIDENCE_CHANGED',
  'retained full file inventory required':'CERTIFICATE_RETAINED_FULL_FILE_INVENTORY_REQUIRED',
  'retained native artifact expired':'CERTIFICATE_RETAINED_NATIVE_ARTIFACT_EXPIRED',
  'retained relative path required':'CERTIFICATE_RETAINED_RELATIVE_PATH_REQUIRED',
  'retained wrapper row count':'CERTIFICATE_RETAINED_WRAPPER_ROW_COUNT',
  'runtime placeholder must be empty/inventory-only':'ADMISSION_RUNTIME_PLACEHOLDER_MUST_BE_EMPTY_INVENTORY_ONLY',
  'runtime placeholder no longer empty':'ADMISSION_RUNTIME_PLACEHOLDER_NO_LONGER_EMPTY',
  'runtime search path changed':'ENGINE_RUNTIME_SEARCH_PATH_CHANGED',
  'sandbox mount absent':'ENGINE_SANDBOX_MOUNT_ABSENT',
  'separate exact protocol caps':'OUTPUT_SEPARATE_EXACT_PROTOCOL_CAPS',
  'shared host deadline exceeded':'CERTIFICATE_SHARED_HOST_DEADLINE_EXCEEDED',
  'shared host deadline exceeded after hashing':'CERTIFICATE_SHARED_HOST_DEADLINE_EXCEEDED_AFTER_HASHING',
  'shared host deadline exceeded while hashing':'CERTIFICATE_SHARED_HOST_DEADLINE_EXCEEDED_WHILE_HASHING',
  'short durable write':'ENGINE_SHORT_DURABLE_WRITE',
  'successful helper stderr must be empty':'ENGINE_SUCCESSFUL_HELPER_STDERR_MUST_BE_EMPTY',
  'symlink path':'ENGINE_SYMLINK_PATH',
  'target cannot be restored':'ADMISSION_TARGET_CANNOT_BE_RESTORED',
  'target must not occur in predecessor namespace':'ENGINE_TARGET_MUST_NOT_OCCUR_IN_PREDECESSOR_NAMESPACE',
  'terminal run chronology':'CERTIFICATE_TERMINAL_RUN_CHRONOLOGY',
  'tree directory alias':'ENGINE_TREE_DIRECTORY_ALIAS',
  'tree regular unshared file required':'ENGINE_TREE_REGULAR_UNSHARED_FILE_REQUIRED',
  'tree root required':'ENGINE_TREE_ROOT_REQUIRED',
  'true exit code required':'PROBE_TRUE_EXIT_CODE_REQUIRED',
  'unapproved initial engine file':'ENGINE_UNAPPROVED_INITIAL_ENGINE_FILE',
  'unexpected helper checker stdout':'ENGINE_UNEXPECTED_HELPER_CHECKER_STDOUT',
  'unexpected helper compile stdout':'ENGINE_UNEXPECTED_HELPER_COMPILE_STDOUT',
  'unexpected target checker output':'ENGINE_UNEXPECTED_TARGET_CHECKER_OUTPUT',
  'unknown acquired origin':'CERTIFICATE_UNKNOWN_ACQUIRED_ORIGIN',
  'unknown profile':'PROBE_UNKNOWN_PROFILE',
  'unsafe retained path':'CERTIFICATE_UNSAFE_RETAINED_PATH',
  'verifier/upload order':'CERTIFICATE_VERIFIER_UPLOAD_ORDER',
  'whole-module audit closure fields differ':'PROBE_WHOLE_MODULE_AUDIT_CLOSURE_FIELDS_DIFFER',
  'workspace must be fresh':'ENGINE_WORKSPACE_MUST_BE_FRESH',
  'wrapper file absent from inventory':'CERTIFICATE_WRAPPER_FILE_ABSENT_FROM_INVENTORY',
  'absolute canonical path':'PARENT_ABSOLUTE_CANONICAL_PATH',
  'acquisition changed':'PARENT_ACQUISITION_CHANGED',
  'acquisition changed during diagnostic':'PARENT_ACQUISITION_CHANGED_DURING_DIAGNOSTIC',
  'acquisition credential absent':'PARENT_ACQUISITION_CREDENTIAL_ABSENT',
  'actual native child result required':'PARENT_ACTUAL_NATIVE_CHILD_RESULT_REQUIRED',
  'actual successful native child exit required':'PARENT_ACTUAL_SUCCESSFUL_NATIVE_CHILD_EXIT_REQUIRED',
  'admission output device changed':'PARENT_ADMISSION_OUTPUT_DEVICE_CHANGED',
  'admitted inode/hash map changed during diagnostic':'PARENT_ADMITTED_INODE_HASH_MAP_CHANGED_DURING_DIAGNOSTIC',
  'bounded evidence file count':'PARENT_BOUNDED_EVIDENCE_FILE_COUNT',
  'child RSS observation':'PARENT_CHILD_RSS_OBSERVATION',
  'child cleanup bound':'PARENT_CHILD_CLEANUP_BOUND',
  'child completion binding':'PARENT_CHILD_COMPLETION_BINDING',
  'child containment/resource/cleanup failure':'PARENT_CHILD_CONTAINMENT_RESOURCE_CLEANUP_FAILURE',
  'child timeout/elapsed result':'PARENT_CHILD_TIMEOUT_ELAPSED_RESULT',
  'clean complete import smoke logs':'PARENT_CLEAN_COMPLETE_IMPORT_SMOKE_LOGS',
  'complete independently derived native output map':'PARENT_COMPLETE_INDEPENDENTLY_DERIVED_NATIVE_OUTPUT_MAP',
  'complete raw chain/log evidence cap':'PARENT_COMPLETE_RAW_CHAIN_LOG_EVIDENCE_CAP',
  'complete safe admission capture limit':'PARENT_COMPLETE_SAFE_ADMISSION_CAPTURE_LIMIT',
  'complete safe import-smoke capture limit':'PARENT_COMPLETE_SAFE_IMPORT_SMOKE_CAPTURE_LIMIT',
  'contract must match the exact reviewed source release state':'PARENT_CONTRACT_MUST_MATCH_THE_EXACT_REVIEWED_SOURCE_RELEASE_STATE',
  'controller poisoned':'PARENT_CONTROLLER_POISONED',
  'controller source inode/hash changed':'PARENT_CONTROLLER_SOURCE_INODE_HASH_CHANGED',
  'duplicate JSON key':'PARENT_DUPLICATE_JSON_KEY',
  'exact actual CI run/attempt/commit fields':'PARENT_EXACT_ACTUAL_CI_RUN_ATTEMPT_COMMIT_FIELDS',
  'exact bounded acquisition completion':'PARENT_EXACT_BOUNDED_ACQUISITION_COMPLETION',
  'exact failed-diagnostic command specification':'PARENT_EXACT_FAILED_DIAGNOSTIC_COMMAND_SPECIFICATION',
  'exact token-free native environment including fixed bwrap PWD':'PARENT_EXACT_TOKEN_FREE_NATIVE_ENVIRONMENT_INCLUDING_FIXED_BWRAP_PWD',
  'exact trusted workflow context':'PARENT_EXACT_TRUSTED_WORKFLOW_CONTEXT',
  'external controller contract pin':'PARENT_EXTERNAL_CONTROLLER_CONTRACT_PIN',
  'extra native child outputs':'PARENT_EXTRA_NATIVE_CHILD_OUTPUTS',
  'file changed during read':'PARENT_FILE_CHANGED_DURING_READ',
  'file grew beyond bound':'PARENT_FILE_GREW_BEYOND_BOUND',
  'final complete evidence output map':'PARENT_FINAL_COMPLETE_EVIDENCE_OUTPUT_MAP',
  'final diagnostic inode/hash map changed':'PARENT_FINAL_DIAGNOSTIC_INODE_HASH_MAP_CHANGED',
  'final evidence cap':'PARENT_FINAL_EVIDENCE_CAP',
  'fixed acquisition mount position':'PARENT_FIXED_ACQUISITION_MOUNT_POSITION',
  'fixed canonical installed inventory':'PARENT_FIXED_CANONICAL_INSTALLED_INVENTORY',
  'fixed import alias already present':'PARENT_FIXED_IMPORT_ALIAS_ALREADY_PRESENT',
  'fixed import-only smoke completion':'PARENT_FIXED_IMPORT_ONLY_SMOKE_COMPLETION',
  'fixed input inode/hash changed':'PARENT_FIXED_INPUT_INODE_HASH_CHANGED',
  'fixed internal child entry':'PARENT_FIXED_INTERNAL_CHILD_ENTRY',
  'fixed owned invocation location':'PARENT_FIXED_OWNED_INVOCATION_LOCATION',
  'fixed source bytes changed':'PARENT_FIXED_SOURCE_BYTES_CHANGED',
  'fresh acquisition root':'PARENT_FRESH_ACQUISITION_ROOT',
  'fresh failure evidence':'PARENT_FRESH_FAILURE_EVIDENCE',
  'fresh isolated native interpreter':'PARENT_FRESH_ISOLATED_NATIVE_INTERPRETER',
  'fresh official archive path':'PARENT_FRESH_OFFICIAL_ARCHIVE_PATH',
  'fresh work required':'PARENT_FRESH_WORK_REQUIRED',
  'inactive minimal controller requires separate exact release review':'PARENT_INACTIVE_MINIMAL_CONTROLLER_REQUIRES_SEPARATE_EXACT_RELEASE_REVIEW',
  'inactive source-only child; execution not released':'PARENT_INACTIVE_SOURCE_ONLY_CHILD_EXECUTION_NOT_RELEASED',
  'independent complete engine response':'PARENT_INDEPENDENT_COMPLETE_ENGINE_RESPONSE',
  'independent transfer certificate/marker bytes':'PARENT_INDEPENDENT_TRANSFER_CERTIFICATE_MARKER_BYTES',
  'insufficient time for cleanup':'PARENT_INSUFFICIENT_TIME_FOR_CLEANUP',
  'measured complete evidence copy capacity':'PARENT_MEASURED_COMPLETE_EVIDENCE_COPY_CAPACITY',
  'measured official archive headroom':'PARENT_MEASURED_OFFICIAL_ARCHIVE_HEADROOM',
  'native child acquisition binding':'PARENT_NATIVE_CHILD_ACQUISITION_BINDING',
  'native child input binding':'PARENT_NATIVE_CHILD_INPUT_BINDING',
  'native report disagrees with independent expectations':'PARENT_NATIVE_REPORT_DISAGREES_WITH_INDEPENDENT_EXPECTATIONS',
  'official release archive length':'PARENT_OFFICIAL_RELEASE_ARCHIVE_LENGTH',
  'official runtime archive length':'PARENT_OFFICIAL_RUNTIME_ARCHIVE_LENGTH',
  'one CPU':'PARENT_ONE_CPU',
  'one original controller invocation':'PARENT_ONE_ORIGINAL_CONTROLLER_INVOCATION',
  'original deadline changed':'PARENT_ORIGINAL_DEADLINE_CHANGED',
  'original official release download bound':'PARENT_ORIGINAL_OFFICIAL_RELEASE_DOWNLOAD_BOUND',
  'original residual disk/inode headroom before diagnostic':'PARENT_ORIGINAL_RESIDUAL_DISK_INODE_HEADROOM_BEFORE_DIAGNOSTIC',
  'owned bounded regular file':'PARENT_OWNED_BOUNDED_REGULAR_FILE',
  'owned completion marker':'PARENT_OWNED_COMPLETION_MARKER',
  'owned request/deadline binding':'PARENT_OWNED_REQUEST_DEADLINE_BINDING',
  'owned/immutable root replaced':'PARENT_OWNED_IMMUTABLE_ROOT_REPLACED',
  'parent invocation mutated':'PARENT_PARENT_INVOCATION_MUTATED',
  'relative package source':'PARENT_RELATIVE_PACKAGE_SOURCE',
  'runtime setup must be token-free':'PARENT_RUNTIME_SETUP_MUST_BE_TOKEN_FREE',
  'same filesystem allocation unit':'PARENT_SAME_FILESYSTEM_ALLOCATION_UNIT',
  'same live owner admission required':'PARENT_SAME_LIVE_OWNER_ADMISSION_REQUIRED',
  'small complete failure packet':'PARENT_SMALL_COMPLETE_FAILURE_PACKET',
  'smoke cannot admit objects':'PARENT_SMOKE_CANNOT_ADMIT_OBJECTS',
  'symlink in path':'PARENT_SYMLINK_IN_PATH',
  'unlisted acquisition metadata':'PARENT_UNLISTED_ACQUISITION_METADATA',
  'frozen graph manifest changed':'FROZEN_GRAPH_MANIFEST',
  'frozen complete38-file source graph changed':'FROZEN_GRAPH_MEMBERSHIP',
  'frozen compile buffer pin mismatch':'FROZEN_SOURCE_BUFFER',
  'native aliases already populated':'NATIVE_ALIAS_COLLISION',
  'single exclusive main thread required':'NATIVE_THREAD_SCOPE',
  'fixed admission implementation pin changed':'FIXED_ADMISSION_SOURCE_PIN',
  'fixed historical implementation tree changed':'FIXED_HISTORICAL_TREE',
  'fixed historical source changed':'FIXED_HISTORICAL_SOURCE_PIN',
  'selected source archive identity mismatch':'SOURCE_ARCHIVE_IDENTITY',
  'duplicate/unlisted/non-regular source archive member':'SOURCE_ARCHIVE_MEMBER',
  'source archive size mismatch':'SOURCE_ARCHIVE_SIZE',
  'source archive member hash mismatch':'SOURCE_ARCHIVE_MEMBER_HASH',
  'source archive missing selected file':'SOURCE_ARCHIVE_INCOMPLETE',
  'source hash/size mismatch':'SOURCE_FILE_IDENTITY',
  'official toolchain archive SHA256 mismatch':'RUNTIME_ARCHIVE_HASH',
  'insufficient measured disk for bounded runtime extraction':'RUNTIME_EXTRACTION_CAPACITY',
  'toolchain expansion byte limit':'RUNTIME_EXPANSION_LIMIT',
  'toolchain decompression failed':'RUNTIME_DECOMPRESSION',
  'unresolved/cyclic toolchain hardlinks':'RUNTIME_HARDLINK_TARGET',
  'official runtime archive length':'RUNTIME_ARCHIVE_LENGTH',
  'official release archive length':'RUNTIME_DOWNLOAD_LENGTH',
  'original official release download bound':'RUNTIME_DOWNLOAD_BOUND',
  'measured official archive headroom':'RUNTIME_DOWNLOAD_CAPACITY',
  'fixed canonical installed inventory':'RUNTIME_DERIVED_INVENTORY_PIN',
  'toolchain archive hash mismatch':'RUNTIME_VERIFY_ARCHIVE_HASH',
  'toolchain inventory hash mismatch':'RUNTIME_VERIFY_INVENTORY_HASH',
  'toolchain inventory membership mismatch':'RUNTIME_VERIFY_MEMBERSHIP',
  'installed toolchain hash mismatch':'RUNTIME_VERIFY_FILE_HASH',
  'runtime entry is not owned by verifier':'RUNTIME_BIND_OWNER',
  'runtime entry has unsafe mode':'RUNTIME_BIND_MODE',
  'regular file or hardlink':'RUNTIME_BIND_REGULAR_SINGLE_LINK',
  'fixed official inventory digest differs':'RUNTIME_BIND_INVENTORY_PIN',
  'extra or duplicate runtime entry':'RUNTIME_BIND_EXTRA_ENTRY',
  'missing runtime entries':'RUNTIME_BIND_MISSING_ENTRY',
  'regular file size/mode differs':'RUNTIME_BIND_SIZE_MODE',
  'regular file hash differs':'RUNTIME_BIND_FILE_HASH',
  'alias target text differs':'RUNTIME_BIND_ALIAS',
  'official runtime filesystem check failed':'RUNTIME_BIND_FILESYSTEM',
  'owned directory':'SNAPSHOT_DIRECTORY_OWNER_MODE',
  'owned single-link regular file':'SNAPSHOT_FILE_OWNER_MODE',
  'regular tree file':'SNAPSHOT_REGULAR_SINGLE_LINK',
  'symlink entry':'SNAPSHOT_SYMLINK',
  'tree logical bytes':'SNAPSHOT_BYTE_LIMIT',
  'tree entries':'SNAPSHOT_ENTRY_LIMIT',
  'fixed source bytes changed':'CONTROLLER_SOURCE_PIN',
 }
 planner={'canonical absolute path required':'PLANNER_CANONICAL_PATH','native command helper pin differs':'PLANNER_NATIVE_HELPER_PIN','native helper import path differs':'PLANNER_NATIVE_IMPORT_PATH','command roots must be disjoint':'PLANNER_DISJOINT_ROOTS'}
 if type(error) is ValueError:
  args=BaseException.args.__get__(error)
  if type(args) is tuple and len(args)==1 and type(args[0]) is str and len(args[0])<=160 and args[0] in planner:return 'COMMAND_PLANNER_REJECTED',planner[args[0]]
 args=BaseException.args.__get__(error) if reviewed else None
 reason='REQUIRED_GATE_FAILED'
 if reviewed and type(args) is tuple and len(args)==1 and type(args[0]) is str and len(args[0])<=160:
  reason=reasons.get(args[0],reason)
 return category,reason

def _setup_transport_reason(error):
 # Only exact standard-library types; never call str() on error or reason.
 module=sys.modules.get('urllib.error')
 known=vars(module) if type(module) is types.ModuleType else {}
 if type(error) is known.get('HTTPError'):
  result={'exception_category':'OFFICIAL_DOWNLOAD_HTTP_ERROR','reason_code':'OFFICIAL_DOWNLOAD_HTTP_ERROR'}
  code=vars(error).get('code')
  if type(code) is int and 100<=code<=599:result['http_status']=code
  return result
 if type(error) is TimeoutError or (type(error) is known.get('URLError') and type(vars(error).get('reason')) is TimeoutError):
  return {'exception_category':'OFFICIAL_DOWNLOAD_TIMEOUT','reason_code':'OFFICIAL_DOWNLOAD_TIMEOUT'}
 if type(error) is known.get('URLError'):
  return {'exception_category':'OFFICIAL_DOWNLOAD_URL_ERROR','reason_code':'OFFICIAL_DOWNLOAD_URL_ERROR'}
 return {}

# Diagnostic interface SHA256: 9a93db503ae0ed8fa257cf74f27789b6f99270cf46a0192039e7f31bbafa1b16
ACQUISITION_FAILURE_PHASES=('bootstrap', 'arguments', 'runtime_envelope', 'quarantine_create', 'constructor', 'initial_snapshots', 'prepare_transfer', 'stage_transfer', 'receipt_copy', 'historical_ledger', 'stage_reauthentication', 'final_snapshots', 'prepare_reauthentication', 'certificate_build', 'certificate_write', 'certificate_finalize', 'cleanup')
ACQUISITION_FAILURE_PAIRS=(('AUTHORIZATION', 'API_PATH_REJECTED'), ('AUTHORIZATION', 'API_QUOTA_OR_AUTHORIZATION'), ('AUTHORIZATION', 'API_SOURCE_BINDING'), ('AUTHORIZATION', 'STORAGE_CREDENTIAL_REJECTED'), ('AUTHORIZATION', 'STORAGE_REDIRECT_REJECTED'), ('AUTHORIZATION', 'TOKEN_MISSING_OR_INVALID'), ('CAPACITY', 'DISK_FULL'), ('CAPACITY', 'DISK_HEADROOM'), ('CAPACITY', 'FILE_DESCRIPTORS'), ('CAPACITY', 'GLOBAL_RAW_LEDGER'), ('CAPACITY', 'HISTORICAL_GLOBAL_LEDGER'), ('CAPACITY', 'INODE_HEADROOM'), ('CAPACITY', 'MEMORY_FAILURE'), ('CLEANUP', 'METADATA_ERROR_CLEANUP'), ('CLEANUP', 'METADATA_RESPONSE_CLEANUP'), ('CLEANUP', 'QUARANTINE_CLEANUP'), ('CLEANUP', 'QUOTA_RESPONSE_CLEANUP'), ('DEADLINE', 'METADATA_DEADLINE_EXPIRED'), ('DEADLINE', 'ORIGINAL_AGE_EXPIRED'), ('DEADLINE', 'QUOTA_CLOCK_INVALID'), ('DEADLINE', 'QUOTA_PACING_BUDGET'), ('DEADLINE', 'QUOTA_REQUEST_BUDGET'), ('DEADLINE', 'QUOTA_SLEEP_NO_PROGRESS'), ('DEADLINE', 'QUOTA_TIMEOUT_BUDGET'), ('DEADLINE', 'QUOTA_WAIT_BUDGET'), ('DEADLINE', 'REQUEST_TIMEOUT_INVALID'), ('DEADLINE', 'SHARED_DEADLINE_EXPIRED'), ('ENVELOPE', 'AFFINITY_REJECTED'), ('ENVELOPE', 'INTERPRETER_FLAGS'), ('FILESYSTEM', 'FILESYSTEM_PERMISSION'), ('FILESYSTEM', 'OS_FAILURE'), ('FILESYSTEM', 'QUARANTINE_CANONICAL'), ('FILESYSTEM', 'QUARANTINE_EMPTY'), ('FILESYSTEM', 'QUARANTINE_FRESH'), ('FILESYSTEM', 'QUARANTINE_MODE'), ('FILESYSTEM', 'QUARANTINE_OWNER'), ('HTTP', 'HTTP_STATUS_REJECTED'), ('IDENTITY', 'DUPLICATE_TERMINAL_JOB'), ('IDENTITY', 'PREPARE_METADATA_CHANGED'), ('IDENTITY', 'STAGE_METADATA_CHANGED'), ('IDENTITY', 'TERMINAL_SNAPSHOT_CHANGED'), ('NETWORK', 'NETWORK_DNS'), ('NETWORK', 'NETWORK_FAILURE'), ('NETWORK', 'NETWORK_TIMEOUT'), ('PAYLOAD', 'NATIVE_RECEIPT_PIN'), ('PAYLOAD', 'NATIVE_TAR_PIN'), ('PAYLOAD', 'ZIP_SIZE_DIGEST'), ('QUOTA_SCHEMA', 'QUOTA_DATE'), ('QUOTA_SCHEMA', 'QUOTA_HEADERS_UNAVAILABLE'), ('QUOTA_SCHEMA', 'QUOTA_HEADER_CONFLICT'), ('QUOTA_SCHEMA', 'QUOTA_HEADER_SHAPE'), ('QUOTA_SCHEMA', 'QUOTA_METADATA'), ('QUOTA_SCHEMA', 'QUOTA_NUMERIC_HEADER'), ('QUOTA_WINDOW', 'QUOTA_CLOCK_BACKWARD'), ('QUOTA_WINDOW', 'QUOTA_EXHAUSTED'), ('QUOTA_WINDOW', 'QUOTA_REMAINING_INCREASED'), ('QUOTA_WINDOW', 'QUOTA_RESET_EARLY'), ('QUOTA_WINDOW', 'QUOTA_RESET_WINDOW'), ('REJECTION', 'UNCLASSIFIED_REJECTION'), ('SOURCE', 'HISTORICAL_PINS_MISMATCH'), ('SOURCE', 'SPEC_PIN_MISMATCH'))

def _validated_acquisition_failure(value):
 if type(value) is not dict or set(value)!={'schema','phase','category','reason_code','http_status'}:return None
 if any(type(value[k]) is not str for k in ('schema','phase','category','reason_code')):return None
 if value['schema']!='c087-acquisition-failure-v1' or value['phase'] not in ACQUISITION_FAILURE_PHASES:return None
 if (value['category'],value['reason_code']) not in ACQUISITION_FAILURE_PAIRS:return None
 status=value['http_status']
 if status is not None and (type(status) is not int or not 100<=status<=599):return None
 return dict(value)

def _parse_acquisition_failure(raw):
 prefix=b'C087_ACQUISITION_FAILURE_V1 '
 if type(raw) is not bytes or not 0<len(raw)<=1024 or not raw.startswith(prefix) or not raw.endswith(b'\n') or raw.count(b'\n')!=1:return None
 try:
  value=_validated_acquisition_failure(parse(raw[len(prefix):-1]))
  if value is None:return None
  canonical=prefix+json.dumps(value,sort_keys=True,separators=(',',':'),ensure_ascii=True,allow_nan=False).encode('ascii')+b'\n'
  return value if raw==canonical else None
 except BaseException:return None

def _safe_failure(work,phase,error,*,setup_owner=None):
 """Never stringify acquisition exceptions, URLs, headers, bodies or secrets."""
 try:
  out=work/'upload'
  if not out.exists():out.mkdir(mode=0o700)
  completion=out/'COMPLETED.json'
  if completion.exists():
   need(completion.is_file() and not completion.is_symlink(),'owned completion marker');completion.unlink()
  value={'schema':'c087-minimal-failure-v1','status':'failed_closed','phase':phase,'exception_class':{ValueError:'ValueError',RuntimeError:'RuntimeError',OSError:'OSError',TimeoutError:'TimeoutError',MemoryError:'MemoryError',TypeError:'TypeError',KeyError:'KeyError',FileNotFoundError:'FileNotFoundError',PermissionError:'PermissionError',AssertionError:'AssertionError'}.get(type(error),'ReviewedComponentRejected'),'reason_code':'REQUIRED_GATE_FAILED','proof_pass_claimed':False,'resume_allowed':False}
  value['exception_category'],value['reason_code']=_setup_reason(error)
  if setup_owner is not None:
   gate=getattr(setup_owner,'_run_gate',None);position=getattr(setup_owner,'_run_position',None);completed=getattr(setup_owner,'_run_completed',None)
   if type(gate) is str and gate in RUN_GATES and position in ('before','after') and type(completed) is list and completed==list(RUN_GATES[:RUN_GATES.index(gate)+(position=='after')]):
    value['gate']=gate;value['gate_position']=position;value['completed_gates']=completed
   result=_safe_native_result(getattr(setup_owner,'_last_native_result',None))
   native_phase=getattr(setup_owner,'_last_native_phase',None)
   if result is not None and native_phase in ('compatibility','acquisition','admission'):
    value['native_phase']=native_phase;value['native_result']=result
   child=_validated_acquisition_failure(getattr(setup_owner,'_acquisition_failure',None))
   if child is not None:value['acquisition_child']=child
  if phase=='setup':
   if setup_owner is not None:
    gate=setup_owner._setup_gate;position=setup_owner._setup_position;completed=setup_owner._setup_completed
    if type(gate) is str and gate in SETUP_GATES and position in ('before','after') and type(completed) is list and completed==list(SETUP_GATES[:SETUP_GATES.index(gate)+(position=='after')]):
     value['setup_gate']=gate;value['setup_position']=position;value['setup_completed']=completed
     if gate=='runtime_download':value.update(_setup_transport_reason(error))
  raw=jb(value)
  if len(raw)>16*1024:return
  fd=os.open(out/'FAILURE.json',os.O_WRONLY|os.O_CREAT|os.O_EXCL|os.O_NOFOLLOW,0o600)
  try:os.write(fd,raw);os.fsync(fd)
  finally:os.close(fd)
 except BaseException:pass

def _run_candidate(pipeline,work,contract,budget,acquisition_token,ci_identity):
 """Dormant production implementation. Only released fixed entry may call it."""
 global _USED
 need(not _USED,'one original controller invocation');_USED=True
 owner=object.__new__(_TrustedRun);owner._poisoned=False;owner._phase='setup';owner.work=canonical(work)
 owner.nonce=secrets.token_hex(32);owner.deadline=budget.original.deadline_monotonic
 owner._setup_completed=[];owner._setup_gate='fixed_modules';owner._setup_position='before'
 owner._run_completed=[];owner._run_gate=None;owner._run_position='before'
 need(not work.exists(),'fresh work required');work.mkdir(mode=0o700);(work/'upload').mkdir(mode=0o700)
 try:
  _setup_mark(owner,'fixed_modules','before')
  mods=_modules(pipeline,contract);protocol=mods['protocol'];model=mods['output_model'];loader=mods['frozen_native'];engine=mods['probe_engine']
  _setup_mark(owner,'fixed_modules','after')
  _setup_mark(owner,'entry_record','before')
  owner.ci_identity=copy.deepcopy(ci_identity)
  protocol.write_new(work/'entry.json',jb({'schema':'c087-minimal-owned-entry-v1','ci_identity':owner.ci_identity,'session_nonce':owner.nonce,'original_deadline_monotonic':owner.deadline,'historical_native_identity_rewritten':False}),budget.check)
  _setup_mark(owner,'entry_record','after')
  _setup_mark(owner,'native_graph_load','before')
  latest=pipeline.parent/'latest';prior=pipeline.parent/'prior';source_package=pipeline.parent/'source-package'
  graph=loader.load_frozen_graph(str(latest));f,p=graph.f,graph.p
  _setup_mark(owner,'native_graph_load','after')
  _setup_mark(owner,'native_seam_load','before')
  seam=load('terminal_certificate',pipeline/'ci/c087/admission/code/terminal_certificate.py',contract['files']['ci/c087/admission/code/terminal_certificate.py'])
  seam=load('historical_admission',pipeline/'ci/c087/admission/code/historical_admission.py',contract['files']['ci/c087/admission/code/historical_admission.py'])
  _setup_mark(owner,'native_seam_load','after')
  _setup_mark(owner,'native_graph_verify','before')
  graph.verify()
  _setup_mark(owner,'native_graph_verify','after')
  _setup_mark(owner,'transfer_fixed_files','before')
  graph.transfer.check_fixed_files(latest/'admission',prior);budget.check()
  _setup_mark(owner,'transfer_fixed_files','after')
  _setup_mark(owner,'source_manifest','before')
  manifest=f.pinned_load(prior/'SOURCE_MANIFEST.json',p.PRIOR_MANIFEST)
  _setup_mark(owner,'source_manifest','after')
  _setup_mark(owner,'source_extract','before')
  f.extract_sources(source_package/'hierarchy-c-sources.tar.gz',work/'source',manifest);budget.check()
  _setup_mark(owner,'source_extract','after')
  _setup_mark(owner,'runtime_download','before')
  archive=work/'lean.tar.zst';_download_runtime(archive,budget)
  _setup_mark(owner,'runtime_download','after')
  _setup_mark(owner,'runtime_archive_length','before')
  need(archive.stat().st_size==595391556,'official runtime archive length')
  _setup_mark(owner,'runtime_archive_length','after')
  _setup_mark(owner,'runtime_installer_load','before')
  install=load('toolchain_install',latest/'ci/toolchain_install.py',loader.GRAPH.pins['files']['ci/toolchain_install.py'])
  _setup_mark(owner,'runtime_installer_load','after')
  _setup_mark(owner,'runtime_install','before')
  inventory,directory_observation=mods['official_runtime'].install_official_archive(install,archive,work/'runtime',check_deadline=budget.check);budget.check()
  _setup_mark(owner,'runtime_install','after')
  _setup_mark(owner,'runtime_inventory_write','before')
  protocol.write_new(work/'runtime-inventory.json',f.json_bytes(inventory),budget.check)
  _setup_mark(owner,'runtime_inventory_write','after')
  _setup_mark(owner,'runtime_inventory_pin','before')
  need(sha(f.json_bytes(inventory))==INVENTORY_SHA,'fixed canonical installed inventory')
  _setup_mark(owner,'runtime_inventory_pin','after')
  _setup_mark(owner,'native_contract','before')
  native_contract=f.pinned_load(latest/'ci/three_context_contract.json',CONTRACT_SHA)
  _setup_mark(owner,'native_contract','after')
  _setup_mark(owner,'runtime_verify','before')
  f.verify_toolchain(work/'runtime',archive,work/'runtime-inventory.json',native_contract,derived_inventory_sha256=INVENTORY_SHA);budget.check()
  _setup_mark(owner,'runtime_verify','after')
  _setup_mark(owner,'official_runtime_bind','before')
  runtime=mods['official_runtime'].bind_official_runtime(str(work/'runtime'),check_deadline=budget.check,installation=directory_observation)
  protocol.write_new(work/'runtime-directories.json',jb({'schema':'c087-authenticated-runtime-directories-v1','archive_sha256':inventory['archive_sha256'],'inventory_sha256':INVENTORY_SHA,'directories':[entry.path for entry in runtime.entries if entry.kind=='directory']}),budget.check)
  _setup_mark(owner,'official_runtime_bind','after')
  _setup_mark(owner,'owned_layout','before')
  (work/'empty-runtime').mkdir(mode=0o700);(work/'admission').mkdir(mode=0o700);(work/'transfer').mkdir(mode=0o700)
  owner.roots={'latest_pipeline':latest,'prior_pipeline':prior,'source_package':source_package,'research_source':work/'source','official_runtime':work/'runtime','helper_source':pipeline/'ci/c087/helpers','runtime_placeholder':work/'empty-runtime','container':work/'admission','acquisition':work/'transfer/acquired'}
  roots=owner.roots;package=pipeline/'ci/c087/admission'
  _setup_mark(owner,'owned_layout','after')
  fixed_names=('latest_pipeline','prior_pipeline','research_source','helper_source','runtime_placeholder')
  baseline={}
  for name in fixed_names:
   _setup_mark(owner,'snapshot_'+name,'before')
   baseline[name]=_snapshot(protocol,roots[name],budget)
   _setup_mark(owner,'snapshot_'+name,'after')
  _setup_mark(owner,'snapshot_controller','before')
  code_snapshot=_snapshot(protocol,pipeline,budget,max_bytes=64*1024**2,max_entries=4096)
  _setup_mark(owner,'snapshot_controller','after')
  def fixed_check():
   need(not owner._poisoned,'controller poisoned')
   try:
    budget.check();need(owner.deadline==budget.original.deadline_monotonic,'original deadline changed')
    for k in fixed_names:need(_snapshot(protocol,roots[k],budget)==baseline[k],'fixed input inode/hash changed')
    need(_snapshot(protocol,pipeline,budget,max_bytes=64*1024**2,max_entries=4096)==code_snapshot,'controller source inode/hash changed')
    mods['official_runtime'].revalidate_official_runtime(runtime);graph.verify();budget.check()
   except BaseException:owner._poisoned=True;raise
  owner._phase='compatibility'
  _phase_mark(owner,'compatibility_smoke','before')
  _smoke_import(owner,f,protocol,pipeline,contract,budget)
  _phase_mark(owner,'compatibility_smoke','after')
  _phase_mark(owner,'compatibility_revalidate','before')
  fixed_check()
  _phase_mark(owner,'compatibility_revalidate','after')
  owner._phase='acquisition'
  _phase_mark(owner,'acquisition_revalidate','before')
  fixed_check()
  _phase_mark(owner,'acquisition_revalidate','after')
  _acquire_owned(owner,f,protocol,pipeline,budget,acquisition_token)
  acquisition_token=None
  # Hash only after actual supervisor cleanup success. Certificate self-report
  # never authorizes a detached acquisition root or prior invocation.
  _phase_mark(owner,'acquisition_certificate','before')
  certificate_raw=read(roots['acquisition']/'TRANSPORT_RECEIPT.json');certificate_sha=sha(certificate_raw);budget.check()
  _phase_mark(owner,'acquisition_certificate','after')
  _phase_mark(owner,'acquisition_snapshot','before')
  acquired=_snapshot(protocol,roots['acquisition'],budget,max_bytes=5*1024**3,max_entries=4096)
  _phase_mark(owner,'acquisition_snapshot','after')
  _phase_mark(owner,'native_inputs','before')
  runner,native_bytes=native_inputs(graph,seam,roots,certificate_raw,certificate_sha,owner.nonce,owner.deadline)
  _phase_mark(owner,'native_inputs','after')
  _phase_mark(owner,'native_expected_map','before')
  static,transfer_request,anticipated=derive_outputs(runner,native_bytes,model);budget.check();fixed_check()
  _phase_mark(owner,'native_expected_map','after')
  owner._phase='admission'
  _phase_mark(owner,'admission_prepare','before')
  request={'schema':'c087-minimal-admission-request-v1','roots':{k:str(v) for k,v in roots.items() if k not in ('official_runtime','helper_source')},'session_nonce':owner.nonce,'deadline_monotonic':owner.deadline,'original_monotonic':budget.original.original_monotonic,'original_wall':budget.original.original_wall.timestamp(),'expiry_wall':budget.original.expiry_wall.timestamp(),'certificate_sha256':certificate_sha,'package_files':{k.removeprefix('ci/c087/admission/'):v for k,v in contract['files'].items() if k.startswith('ci/c087/admission/')},'input_snapshots':{k:baseline[k] for k in fixed_names if k!='helper_source'},'acquisition_snapshot':acquired}
  container=roots['container'];request_path=container/'request.json';invocation_path=container/'admission-invocation.json'
  request_raw=jb(request);protocol.write_new(request_path,request_raw,budget.check)
  argv,environment=child_layout(package,roots,container,request_path,invocation_path)
  timeout=sys.modules['job_budget'].command_timeout(19800,budget.deadline_monotonic,time.monotonic())
  invocation={'schema':'c087-minimal-owned-admission-invocation-v1','request_sha256':sha(request_raw),'argv':argv,'environment':environment,'timeout_seconds':timeout,'limits':LIMITS,'max_log_bytes':16*1024**2,'original_deadline_monotonic':owner.deadline,'session_nonce':owner.nonce}
  invocation_raw=jb(invocation);protocol.write_new(invocation_path,invocation_raw,budget.check)
  _phase_mark(owner,'admission_prepare','after')
  def dispatch_admission():
   result=f.run_process(argv,cwd=container,env=environment,timeout=timeout,stdout=container/'admission.stdout',stderr=container/'admission.stderr',max_log_bytes=16*1024**2,limits=LIMITS,allow_new_sessions=False)
   _observe_native_result(owner,'admission',result)
   _accept_result_safety(result,timeout);owner._admission_safe_failure=(result,invocation)
   accept_child_result(result,timeout);return result
  _phase_mark(owner,'admission_process','before')
  result=budget.process(dispatch_admission);budget.check() # Before ANY child-created read.
  _phase_mark(owner,'admission_process','after')
  _phase_mark(owner,'admission_inputs_revalidate','before')
  protocol.write_new(work/'admission-process.json',jb({'invocation':invocation,'result':result}),budget.check)
  need(read(request_path)==request_raw and read(invocation_path)==invocation_raw,'parent invocation mutated');budget.check()
  need(_snapshot(protocol,roots['acquisition'],budget,max_bytes=5*1024**3,max_entries=4096)==acquired,'acquisition changed')
  fixed_check()
  _phase_mark(owner,'admission_inputs_revalidate','after')
  _phase_mark(owner,'admission_expected_transfer','before')
  admitted=container/'admitted';historical=container/'admitted-historical-validation'
  inode=lambda path:[path.stat().st_dev,path.stat().st_ino]
  need(admitted.stat().st_dev==historical.stat().st_dev==container.stat().st_dev,'admission output device changed')
  unit=os.statvfs(container).f_frsize;need(unit==os.statvfs(admitted).f_frsize==os.statvfs(historical).f_frsize,'same filesystem allocation unit')
  dynamic=model.transfer_outputs(request=transfer_request,static=static,source_root=str(roots['research_source']),admission_root=str(latest/'admission'),historical_root=str(prior),workspace=str(admitted),historical_workspace=str(historical),workspace_inode=inode(admitted),historical_workspace_inode=inode(historical),allocation_unit=unit)
  expected_files={**static['files'],**{name:model.pin(raw) for name,raw in dynamic.items()}}
  _phase_mark(owner,'admission_expected_transfer','after')
  _phase_mark(owner,'admission_outputs','before')
  admitted_snap={name:_snapshot(protocol,path,budget) for name,path in [('admitted',admitted),('admitted-historical-validation',historical)]}
  actual_files={name+'/'+rel:pin for name,snap in admitted_snap.items() for rel,pin in protocol.contents(snap).items()}
  actual_dirs=sorted(name if rel=='.' else name+'/'+rel for name,snap in admitted_snap.items() for rel,row in snap.items() if row['kind']=='directory')
  need(actual_files==expected_files and actual_dirs==static['directories'],'complete independently derived native output map')
  for name,raw in dynamic.items():need(read(container/name)==raw,'independent transfer certificate/marker bytes')
  _phase_mark(owner,'admission_outputs','after')
  _phase_mark(owner,'admission_report','before')
  expected_report={**anticipated,'session_nonce':owner.nonce,'host_deadline_monotonic':owner.deadline,'workspace':str(admitted),'workspace_inode':inode(admitted),'source_root_inode':inode(roots['research_source']),'workspace_files':protocol.contents(admitted_snap['admitted'])}
  report_raw=read(container/'native-report.json');need(parse(report_raw)==expected_report,'native report disagrees with independent expectations')
  need(parse(read(container/'response.json'))=={'schema':'c087-minimal-admission-completion-v1','request_sha256':sha(request_raw),'invocation_sha256':sha(invocation_raw),'native_report_sha256':sha(report_raw)},'child completion binding')
  need(set(os.listdir(container))=={'request.json','admission-invocation.json','admission.stdout','admission.stderr','native-report.json','response.json','admitted','admitted-historical-validation'},'extra native child outputs')
  _phase_mark(owner,'admission_report','after')
  _phase_mark(owner,'admission_final_revalidate','before')
  budget.check();fixed_check();owner._phase='admitted'
  evidence={'schema':'c087-independent-admission-map-v1','files':actual_files,'directories':actual_dirs,'transfer_certificate_sha256':sha(dynamic['admitted/historical-transfer-certificate.json']),'proof_pass_claimed':False}
  protocol.write_new(work/'independent-admission.json',jb(evidence),budget.check)
  _phase_mark(owner,'admission_final_revalidate','after')
  # Static inputs are immutable read-only child mounts with no other writer.
  # Full maps are checked at admission/engine phase boundaries. The unchanged
  # engine rehashes every predecessor around commands and binds source/engine
  # bytes itself; the frequent context check is intentionally cheap.
  _phase_mark(owner,'engine_prepare','before')
  root_inodes={str(path):(path.stat().st_dev,path.stat().st_ino) for path in [pipeline,*[roots[k] for k in fixed_names],roots['official_runtime'],admitted,historical]}
  def checkpoint():
   try:
    need(not owner._poisoned,'controller poisoned')
    need(owner.deadline==budget.original.deadline_monotonic,'original deadline changed')
    for name,identity in root_inodes.items():
     path=canonical(name);info=path.stat();need((info.st_dev,info.st_ino)==identity,'owned/immutable root replaced')
    remaining=math.nextafter(budget.check()-3,-math.inf);need(remaining>0,'insufficient time for cleanup');return remaining
   except BaseException:owner._poisoned=True;raise
  capacity=os.statvfs(work);need(capacity.f_bavail*capacity.f_frsize>=512*1024**2 and capacity.f_favail>=4096,'original residual disk/inode headroom before diagnostic')
  protocol.write_new(work/'capacity.json',jb({'schema':'c087-measured-phase-headroom-v1','free_bytes':capacity.f_bavail*capacity.f_frsize,'free_inodes':capacity.f_favail,'f_frsize':capacity.f_frsize,'native_restore_checked_its_original_storage_budget':True,'complete_physical_write_bound_claimed':False}),budget.check)
  diagnostic=work/'diagnostic';diagnostic.mkdir(mode=0o700)
  predecessor_files={name.removeprefix('objects/'):pin for name,pin in protocol.contents(admitted_snap['admitted']).items() if name.startswith('objects/')}
  manifest={'schema':'c087-fixed-engine-manifest-v1','native_source_path':str(latest/'ci/fresh_stage.py'),'native_source_sha256':engine.base.NATIVE_SHA,'source_root':str(roots['research_source']),'toolchain_root':str(roots['official_runtime']),'helper_root':str(roots['helper_source']),'predecessor_objects':str(admitted/'objects'),'diagnostic_output':str(diagnostic),'predecessor_files':predecessor_files,'control_expectations':parse(read(pipeline/'ci/c087/engine/CONTROL_EXPECTATIONS.json')),'code_pins':{name:contract['files']['ci/c087/engine/'+name] for name in ('probe_engine.py','probe_policy.py','original_probe_commands.py')}}
  engine_invocation=jb({'schema':'c087-minimal-owned-engine-invocation-v1','session_nonce':owner.nonce,'deadline_monotonic':owner.deadline,'manifest_sha256':sha(jb(manifest)),'admission_map_sha256':sha(jb(evidence))})
  protocol.write_new(diagnostic/'engine-invocation.json',engine_invocation,budget.check)
  need(owner._phase=='admitted' and not owner._poisoned,'same live owner admission required')
  owner._phase='diagnostic_consumed' # One-shot issuance consumed before checking.
  context=object.__new__(_Context)
  context.nonce=owner.nonce;context.deadline_monotonic=owner.deadline
  context.manifest_bytes=jb(manifest);context.manifest_sha256=sha(context.manifest_bytes)
  context.input_roots=tuple((k,str(v)) for k,v in roots.items() if k in ('latest_pipeline','research_source','official_runtime','helper_source'))
  context.admitted_objects=str(admitted/'objects');context.diagnostic_output=str(diagnostic)
  context.engine_invocation_sha256=sha(engine_invocation);context.checkpoint=checkpoint
  checkpoint()
  _phase_mark(owner,'engine_prepare','after')
  _phase_mark(owner,'engine_dispatch','before')
  response=budget.process(lambda:engine.engine(context));checkpoint();fixed_check()
  _phase_mark(owner,'engine_dispatch','after')
  _phase_mark(owner,'engine_inputs_revalidate','before')
  need(_snapshot(protocol,roots['acquisition'],budget,max_bytes=5*1024**3,max_entries=4096)==acquired,'acquisition changed during diagnostic')
  for name,snap in admitted_snap.items():need(_snapshot(protocol,container/name,budget)==snap,'admitted inode/hash map changed during diagnostic')
  _phase_mark(owner,'engine_inputs_revalidate','after')
  _phase_mark(owner,'engine_response','before')
  final_snapshot=_snapshot(protocol,diagnostic,budget,max_bytes=4*1024**3,max_entries=100000)
  output_files=protocol.contents(final_snapshot)
  need(response=={'schema':'c087-fixed-engine-result-v1','status':'diagnostic_complete','session_nonce':owner.nonce,'deadline_monotonic':owner.deadline,'engine_manifest_sha256':context.manifest_sha256,'result_sha256':output_files['RESULT.json']['sha256'],'proof_pass_claimed':False,'output_files':{k:v for k,v in output_files.items() if k!='engine-invocation.json'}},'independent complete engine response')
  _phase_mark(owner,'engine_response','after')
  owner._phase='evidence'
  _phase_mark(owner,'evidence_copy','before')
  _package_evidence(owner,protocol,budget,output_files)
  _phase_mark(owner,'evidence_copy','after')
  _phase_mark(owner,'evidence_revalidate','before')
  checkpoint();need(_snapshot(protocol,diagnostic,budget,max_bytes=4*1024**3,max_entries=100000)==final_snapshot,'final diagnostic inode/hash map changed')
  manifest_raw=read(work/'upload/MANIFEST.json');manifest=parse(manifest_raw)
  copied=_snapshot(protocol,work/'upload',budget,max_bytes=MAX_EVIDENCE,max_entries=4096)
  need(protocol.contents(copied)=={**manifest['files'],'MANIFEST.json':{'bytes':len(manifest_raw),'sha256':sha(manifest_raw)}},'final complete evidence output map')
  _phase_mark(owner,'evidence_revalidate','after')
  _phase_mark(owner,'evidence_complete','before')
  checkpoint();protocol.write_new(work/'upload/COMPLETED.json',jb({'schema':'c087-minimal-completed-v1','status':'diagnostic_completed_pending_terminal_reconciliation','manifest_sha256':sha(manifest_raw),'session_nonce':owner.nonce,'original_deadline_monotonic':owner.deadline,'proof_pass_claimed':False}),budget.check)
  budget.check()
  _phase_mark(owner,'evidence_complete','after')
  owner._phase='complete';return response
 except BaseException as error:
  owner._poisoned=True
  if 'mods' in locals() and 'f' in locals():
   try:_retain_failure(owner,mods['protocol'],mods['probe_engine'],f,budget)
   except BaseException:pass
  _safe_failure(work,owner._phase,error,setup_owner=owner);raise

def _download_runtime(archive,budget):
 """Original driver download loop; no token, custom transport or cache."""
 import urllib.request
 need('GH_TOKEN' not in os.environ,'runtime setup must be token-free')
 need(not archive.exists(),'fresh official archive path');v=os.statvfs(archive.parent)
 need(v.f_bavail*v.f_frsize>=595391556+256*1024**2 and v.f_favail>=4096,'measured official archive headroom')
 started=time.monotonic();downloaded=0
 with urllib.request.urlopen('https://github.com/leanprover/lean4/releases/download/v4.35.0-rc2/lean-4.35.0-rc2-linux.tar.zst',timeout=60) as response,archive.open('xb') as out:
  while True:
   budget.check();block=response.read(1024**2)
   if not block:break
   downloaded+=len(block);need(downloaded<=595391556 and time.monotonic()-started<900,'original official release download bound');out.write(block)
 need(downloaded==595391556,'official release archive length');budget.check()

def _acquire_owned(owner,native,protocol,pipeline,budget,acquisition_token):
 _phase_mark(owner,'acquisition_layout','before')
 package=pipeline/'ci/c087/acquisition';container=owner.work/'transfer';root=owner.roots['acquisition']
 need(not root.exists(),'fresh acquisition root')
 environment={**ENV,'GITHUB_ACTIONS':'true','GH_TOKEN':acquisition_token}
 # The repository literal is source-pinned by the unchanged acquisition spec.
 spec=parse(read(package/'ci/C087_ACQUISITION_SPEC.json'));environment['GITHUB_REPOSITORY']=spec['repository']
 need(environment['GH_TOKEN'],'acquisition credential absent')
 argv=['/usr/bin/bwrap','--unshare-all','--share-net','--die-with-parent','--proc','/proc','--dev','/dev','--tmpfs','/tmp']
 for path in ['/usr','/bin','/lib','/lib64','/etc',str(package)]:argv+=['--ro-bind',path,path]
 argv+=['--bind',str(container),str(container),'--chdir',str(container),'--','/usr/bin/python3','-I','-S','-B',str(package/'ci/c087_acquisition.py'),'--quarantine',str(root),'--deadline-monotonic',repr(owner.deadline),'--session-nonce',owner.nonce]
 timeout=sys.modules['job_budget'].command_timeout(19800,budget.deadline_monotonic,time.monotonic())
 _phase_mark(owner,'acquisition_layout','after')
 # No command line, log, request, result or exception contains the token.
 def dispatch_acquisition():
  result=native.run_process(argv,cwd=container,env=environment,timeout=timeout,stdout=container/'acquisition.stdout',stderr=container/'acquisition.stderr',max_log_bytes=16*1024**2,limits=LIMITS,allow_new_sessions=False)
  _observe_native_result(owner,'acquisition',result)
  _accept_result_safety(result,timeout)
  if result['exit_code']!=0:_read_acquisition_failure(owner,container,budget)
  accept_child_result(result,timeout);return result
 _phase_mark(owner,'acquisition_process','before')
 try:result=budget.process(dispatch_acquisition)
 finally:environment.pop('GH_TOKEN',None);os.environ.pop('GH_TOKEN',None)
 _phase_mark(owner,'acquisition_process','after')
 _phase_mark(owner,'acquisition_completion','before')
 accept_child_result(result,timeout);budget.check()
 need(read(container/'acquisition.stdout',16*1024**2)==b'C087 transport bytes authenticated; native semantic admission still required.\n' and read(container/'acquisition.stderr',16*1024**2)==b'','exact bounded acquisition completion')
 protocol.write_new(owner.work/'acquisition-process.json',jb({'schema':'c087-owned-acquisition-completion-v1','result':result,'session_nonce':owner.nonce,'deadline_monotonic':owner.deadline,'argv':argv,'environment_keys':sorted(environment),'credential_retained':False}),budget.check)
 _phase_mark(owner,'acquisition_completion','after')

def _read_acquisition_failure(owner,container,budget):
 # Called only after native cleanup/resource safety and a nonzero exit. Unknown
 # or incomplete stderr is never retained, decoded for display, or copied.
 try:
  budget.check();raw=read(container/'acquisition.stderr',4096)
  record=_parse_acquisition_failure(raw);budget.check()
  if record is not None:owner._acquisition_failure=record
 except BaseException:pass

def _permanent_native_refusal():
 # Fixed trusted Python can use only the native renameat2 transfer helper. This
 # deliberately does not claim0915's full filesystem/ctypes audit policy.
 def guard(event,args):
  if event.startswith(('socket.','subprocess.','os.exec','os.spawn','os.posix_spawn','os.fork','pty.','multiprocessing.')) or event in ('os.system','os.startfile','os.startfile/2'):
   raise Rejected('native child process/network launch forbidden')
  if event=='open' and args and isinstance(args[0],(str,bytes,os.PathLike)) and os.fsdecode(args[0]).endswith(('.pyc','.pyo')):
   raise FileNotFoundError('native child bytecode refused')
 sys.addaudithook(guard)

def _child_modules(package,pins,latest):
 # Preload the existing standard library before a permanent fixed launch guard.
 import argparse,base64,bz2,contextlib,copy,ctypes,dataclasses,datetime,decimal,errno,fractions
 import http.client,inspect,io,lzma,resource,shutil,signal,socket,ssl,subprocess,sysconfig
 import tarfile,tempfile,threading,typing,urllib.error,urllib.parse,urllib.request,zipfile,zlib
 _permanent_native_refusal()
 protocol=load('protocol',package/'code/protocol.py',pins['code/protocol.py'])
 loader=load('frozen_native',package/'code/frozen_native.py',pins['code/frozen_native.py']);graph=loader.load_frozen_graph(str(latest))
 load('terminal_certificate',package/'code/terminal_certificate.py',pins['code/terminal_certificate.py'])
 seam=load('historical_admission',package/'code/historical_admission.py',pins['code/historical_admission.py'])
 return protocol,loader,graph,seam

def _child_entry(request_path,invocation_path,*,smoke=False):
 need(sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode,'fresh isolated native interpreter')
 need(len(os.sched_getaffinity(0))==1,'one CPU')
 package=Path(__file__).resolve().parents[1];request_raw=read(request_path);invocation_raw=read(invocation_path);request=parse(request_raw);invocation=parse(invocation_raw)
 roots={k:canonical(v) for k,v in request['roots'].items()};container=roots['container']
 need(dict(os.environ)=={**ENV,'PWD':str(container)},'exact token-free native environment including fixed bwrap PWD')
 need(Path.cwd()==container and Path(request_path)==container/'request.json' and Path(invocation_path)==container/'admission-invocation.json','fixed owned invocation location')
 need(sha(request_raw)==invocation['request_sha256'] and request['session_nonce']==invocation['session_nonce'] and request['deadline_monotonic']==invocation['original_deadline_monotonic'],'owned request/deadline binding')
 for name in os.listdir('/proc/self/fd'):
  if name.isdigit() and int(name)>=3:
   try:os.fstat(int(name))
   except OSError:continue
   raise Rejected('inherited nonstdio descriptor')
 for name,pin in request['package_files'].items():read(package/name,expected=pin)
 protocol,loader,graph,seam=_child_modules(package,request['package_files'],roots['latest_pipeline'])
 clock=protocol.OriginalClock(request);clock.check()
 if smoke:
  need(not (container/'admitted').exists(),'smoke cannot admit objects')
  protocol.write_new(container/'response.json',jb({'schema':'c087-minimal-import-smoke-v1','status':'exact_source_imports_only','python':list(sys.version_info[:3]),'native_admission':False,'kernel_executed':False}),clock.check);clock.check();return
 for key,snapshot in request['input_snapshots'].items():need(_snapshot(protocol,roots[key],clock)==snapshot,'native child input binding')
 need(_snapshot(protocol,roots['acquisition'],clock,max_bytes=5*1024**3,max_entries=4096)==request['acquisition_snapshot'],'native child acquisition binding')
 certificate_raw=read(roots['acquisition']/'TRANSPORT_RECEIPT.json');clock.check()
 runner,_=native_inputs(graph,seam,roots,certificate_raw,request['certificate_sha256'],request['session_nonce'],request['deadline_monotonic'])
 report=runner.admit();clock.check();graph.verify();clock.check()
 protocol.write_new(container/'native-report.json',report.raw_bytes,clock.check)
 protocol.write_new(container/'response.json',jb({'schema':'c087-minimal-admission-completion-v1','request_sha256':sha(request_raw),'invocation_sha256':sha(invocation_raw),'native_report_sha256':sha(report.raw_bytes)}),clock.check)
 clock.check()

def _smoke_import(owner,native,protocol,pipeline,contract,budget):
 container=owner.work/'compatibility';container.mkdir(mode=0o700)
 roots={**owner.roots,'container':container};package=pipeline/'ci/c087/admission'
 request={'schema':'c087-minimal-import-smoke-request-v1','roots':{k:str(v) for k,v in roots.items() if k not in ('official_runtime','helper_source')},'session_nonce':owner.nonce,'deadline_monotonic':owner.deadline,'original_monotonic':budget.original.original_monotonic,'original_wall':budget.original.original_wall.timestamp(),'expiry_wall':budget.original.expiry_wall.timestamp(),'package_files':{k.removeprefix('ci/c087/admission/'):v for k,v in contract['files'].items() if k.startswith('ci/c087/admission/')}}
 request_path=container/'request.json';invocation_path=container/'admission-invocation.json';request_raw=jb(request);protocol.write_new(request_path,request_raw,budget.check)
 # No acquisition root exists yet; omit only that mount from this import smoke.
 argv,environment=child_layout(package,roots,container,request_path,invocation_path)
 target=str(roots['acquisition']);i=argv.index(target);need(argv[i-1]=='--ro-bind' and argv[i+1]==target,'fixed acquisition mount position');del argv[i-1:i+2]
 argv[argv.index('--admission-child')]='--smoke-import'
 timeout=sys.modules['job_budget'].command_timeout(120,budget.deadline_monotonic,time.monotonic())
 invocation={'request_sha256':sha(request_raw),'session_nonce':owner.nonce,'original_deadline_monotonic':owner.deadline,'argv':argv,'environment':environment,'timeout_seconds':timeout}
 protocol.write_new(invocation_path,jb(invocation),budget.check)
 def dispatch_smoke():
  result=native.run_process(argv,cwd=container,env=environment,timeout=timeout,stdout=container/'stdout',stderr=container/'stderr',max_log_bytes=16*1024**2,limits=LIMITS,allow_new_sessions=False)
  _observe_native_result(owner,'compatibility',result)
  _accept_result_safety(result,timeout);owner._smoke_safe_failure=(result,invocation)
  accept_child_result(result,timeout);return result
 result=budget.process(dispatch_smoke);budget.check()
 response=parse(read(container/'response.json'));need(set(response)=={'schema','status','python','native_admission','kernel_executed'} and response['schema']=='c087-minimal-import-smoke-v1' and response['status']=='exact_source_imports_only' and response['native_admission'] is False and response['kernel_executed'] is False,'fixed import-only smoke completion')
 need(read(container/'stdout')==read(container/'stderr')==b'','clean complete import smoke logs');budget.check()
 protocol.write_new(owner.work/'compatibility-process.json',jb({'invocation':invocation,'result':result,'response':response}),budget.check)

def _retain_failure(owner,protocol,engine,native,budget):
 """Current owned invocation only: copy only already-clean bounded captures."""
 selected={};work=owner.work
 if owner._phase=='compatibility' and hasattr(owner,'_smoke_safe_failure'):
  result,invocation=owner._smoke_safe_failure;_accept_result_safety(result,invocation['timeout_seconds'])
  root=work/'compatibility';stdout=read(root/'stdout',16*1024**2);stderr=read(root/'stderr',16*1024**2)
  need(len(stdout)+len(stderr)<=16*1024**2,'complete safe import-smoke capture limit')
  selected={'compatibility.stdout':stdout,'compatibility.stderr':stderr,'compatibility-process.json':jb({'invocation':invocation,'result':result})}
 elif owner._phase=='admission' and hasattr(owner,'_admission_safe_failure'):
  result,invocation=owner._admission_safe_failure
  _accept_result_safety(result,invocation['timeout_seconds'])
  root=owner.roots['container'];stdout=read(root/'admission.stdout',16*1024**2);stderr=read(root/'admission.stderr',16*1024**2)
  need(len(stdout)+len(stderr)<=16*1024**2,'complete safe admission capture limit')
  selected={'admission.stdout':stdout,'admission.stderr':stderr,'admission-process.json':jb({'invocation':invocation,'result':result})}
 elif owner._phase=='diagnostic_consumed':
  roots=owner.roots;out=work/'diagnostic'
  rows=engine.command_plan(native,source_root=roots['research_source'],toolchain_root=roots['official_runtime'],predecessor_objects=roots['container']/'admitted/objects',helper_root=roots['helper_source'],diagnostic_output=out)
  by_name={row['name']:row for row in rows};receipts=out/'receipts'
  # Engine source writes these parent-owned receipts only after live cleanup,
  # resource and complete-log checks. Never read an unreceipted child capture.
  candidates=[]
  if receipts.is_dir():
   for path in sorted(receipts.iterdir()):
    stem=path.name.removesuffix('.json')
    if path.name.endswith('.json') and len(stem)>3 and stem[:2].isdigit() and stem[2]=='-' and stem[3:] in by_name:candidates.append((path,by_name[stem[3:]]))
  for path,spec in candidates[-3:]:
   record_raw=read(path,1024**2);record=parse(record_raw);effective=record['effective_timeout_seconds']
   need(record['spec']==spec,'exact failed-diagnostic command specification')
   engine.prevalidate_native_exit(record['result'],effective)
   root=engine._root(spec);stdout=read(root/'logs'/(spec['name']+'.stdout'),16*1024**2);stderr=read(root/'logs'/(spec['name']+'.stderr'),16*1024**2)
   engine.policy.validate_live_command(spec,record,stdout,stderr,expected_effective_timeout=effective)
   selected['receipts/'+path.name]=record_raw
   selected['logs/'+spec['name']+'.stdout']=stdout;selected['logs/'+spec['name']+'.stderr']=stderr
 if not selected:return
 need(sum(map(len,selected.values()))<=50*1024**2,'small complete failure packet')
 budget.check();root=work/'upload/failure';need(not root.exists(),'fresh failure evidence');root.mkdir(mode=0o700)
 pins={}
 for name,raw in selected.items():
  target=root/name;target.parent.mkdir(mode=0o700,parents=True,exist_ok=True);protocol.write_new(target,raw,budget.check);pins[name]={'bytes':len(raw),'sha256':sha(raw)}
 protocol.write_new(root/'CAPTURES.json',jb({'schema':'c087-clean-failure-captures-v1','phase':owner._phase,'files':pins,'complete_captures':True,'unreceipted_capture_read':False,'acquisition_logs_included':False,'proof_pass_claimed':False}),budget.check)
 budget.check()

def _package_evidence(owner,protocol,budget,diagnostic_files):
 work=owner.work;acquired=owner.roots['acquisition'];container=owner.roots['container'];selection={}
 for name in ('entry.json','runtime-directories.json','acquisition-process.json','compatibility-process.json','admission-process.json','independent-admission.json','capacity.json'):selection[name]=work/name
 for name in ('request.json','admission-invocation.json','native-report.json','response.json','admission.stdout','admission.stderr','admitted/historical-transfer-state.json','admitted/historical-transfer-certificate.json'):selection['admission/'+name]=container/name
 certificate=parse(read(acquired/'TRANSPORT_RECEIPT.json'));selection['acquisition/TRANSPORT_RECEIPT.json']=acquired/'TRANSPORT_RECEIPT.json'
 for name in certificate['files']:
  if not name.endswith('/delta.tar'):selection['acquisition/'+name]=acquired/name
 for name in diagnostic_files:
  if '/objects/' not in name and '/module-quarantine/' not in name:selection['diagnostic/'+name]=work/'diagnostic'/name
 need(len(selection)<=512,'bounded evidence file count');total=sum(path.stat().st_size for path in selection.values());need(total<=MAX_EVIDENCE-EVIDENCE_RESERVE,'complete raw chain/log evidence cap')
 fs=os.statvfs(work/'upload');need(fs.f_bavail*fs.f_frsize>=total+512*1024**2 and fs.f_favail>=len(selection)+4096,'measured complete evidence copy capacity')
 files={}
 for name,path in sorted(selection.items()):
  budget.check();raw=read(path,MAX_JSON if 'log' not in name and not name.endswith(('.stdout','.stderr')) else 16*1024**2)
  destination=work/'upload'/name;destination.parent.mkdir(mode=0o700,parents=True,exist_ok=True);protocol.write_new(destination,raw,budget.check);files[name]={'bytes':len(raw),'sha256':sha(raw)}
 need(sum(v['bytes'] for v in files.values())<=MAX_EVIDENCE-EVIDENCE_RESERVE,'final evidence cap')
 protocol.write_new(work/'upload/MANIFEST.json',jb({'schema':'c087-minimal-evidence-v1','session_nonce':owner.nonce,'original_deadline_monotonic':owner.deadline,'files':files,'bytes':sum(v['bytes'] for v in files.values()),'payload_archives_included':False,'research_objects_included':False,'proof_pass_claimed':False}),budget.check)
 budget.check()

def run(pipeline,work,contract_sha,budget):
 need(EXECUTION_RELEASED,'inactive minimal controller requires separate exact release review')
 ci_identity={key:os.environ.get(key,'') for key in ('GITHUB_ACTIONS','GITHUB_REPOSITORY','GITHUB_RUN_ID','GITHUB_RUN_ATTEMPT','GITHUB_JOB','GITHUB_SHA','GITHUB_REF')}
 need(ci_identity['GITHUB_ACTIONS']=='true' and ci_identity['GITHUB_REPOSITORY']=='jconorgrogan/palomar-chair-verification' and ci_identity['GITHUB_JOB']=='c087_diagnostic' and ci_identity['GITHUB_REF']=='refs/heads/verify/c087-minimal-diagnostic-20261017','exact trusted workflow context')
 need(all(ci_identity[key].isdigit() and int(ci_identity[key])>0 for key in ('GITHUB_RUN_ID','GITHUB_RUN_ATTEMPT')) and len(ci_identity['GITHUB_SHA'])==40 and all(c in '0123456789abcdef' for c in ci_identity['GITHUB_SHA']),'exact actual CI run/attempt/commit fields')
 acquisition_token=os.environ.pop('GH_TOKEN','')
 os.environ.clear();os.environ.update(ENV) # Installer/native descendants inherit no unrelated CI credentials.
 contract=bootstrap(pipeline,contract_sha,budget)
 with budget:return _run_candidate(pipeline,work,contract,budget,acquisition_token,ci_identity)

def main():
 need(EXECUTION_RELEASED,'inactive source-only child; execution not released')
 need(len(sys.argv)==4 and sys.argv[1] in ('--admission-child','--smoke-import'),'fixed internal child entry')
 _child_entry(sys.argv[2],sys.argv[3],smoke=sys.argv[1]=='--smoke-import')
if __name__=='__main__':main()
