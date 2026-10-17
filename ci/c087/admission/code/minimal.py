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

def _setup_mark(owner,gate,position):
 owner._setup_gate=gate;owner._setup_position=position
 if position=='after':owner._setup_completed.append(gate)

def _setup_reason(error):
 # Match exact reviewed types and one bounded builtin string. Never stringify
 # arbitrary arguments, exceptions, traceback locals, URLs or response bodies.
 category='UNCLASSIFIED_EXCEPTION'
 reviewed=type(error) is Rejected
 if reviewed:category='CONTROLLER_REJECTED'
 for name,label in (('frozen_native','FROZEN_SOURCE_REJECTED'),('checked_transfer','FIXED_TRANSFER_REJECTED'),('fresh_stage','NATIVE_SETUP_REJECTED'),('official_runtime','RUNTIME_BIND_REJECTED'),('protocol','INPUT_SNAPSHOT_REJECTED'),('job_budget','BUDGET_REJECTED')):
  module=sys.modules.get(name)
  if type(module) is types.ModuleType and type(error) is vars(module).get('Rejected'):
   category=label;reviewed=True;break
 reasons={
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

def _safe_failure(work,phase,error,*,setup_owner=None):
 """Never stringify acquisition exceptions, URLs, headers, bodies or secrets."""
 try:
  out=work/'upload'
  if not out.exists():out.mkdir(mode=0o700)
  completion=out/'COMPLETED.json'
  if completion.exists():
   need(completion.is_file() and not completion.is_symlink(),'owned completion marker');completion.unlink()
  value={'schema':'c087-minimal-failure-v1','status':'failed_closed','phase':phase,'exception_class':type(error).__name__ if type(error).__module__=='builtins' else 'ReviewedComponentRejected','reason_code':'REQUIRED_GATE_FAILED','proof_pass_claimed':False,'resume_allowed':False}
  if phase=='setup':
   value['exception_category'],value['reason_code']=_setup_reason(error)
   if setup_owner is not None:
    gate=setup_owner._setup_gate;position=setup_owner._setup_position;completed=setup_owner._setup_completed
    if type(gate) is str and gate in SETUP_GATES and position in ('before','after') and type(completed) is list and completed==list(SETUP_GATES[:SETUP_GATES.index(gate)+(position=='after')]):
     value['setup_gate']=gate;value['setup_position']=position;value['setup_completed']=completed
     if gate=='runtime_download':value.update(_setup_transport_reason(error))
  raw=jb(value);fd=os.open(out/'FAILURE.json',os.O_WRONLY|os.O_CREAT|os.O_EXCL|os.O_NOFOLLOW,0o600)
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
  inventory=install.install_archive(archive,work/'runtime');budget.check()
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
  runtime=mods['official_runtime'].bind_official_runtime(str(work/'runtime'),check_deadline=budget.check)
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
  owner._phase='compatibility';_smoke_import(owner,f,protocol,pipeline,contract,budget);fixed_check()
  owner._phase='acquisition';fixed_check()
  _acquire_owned(owner,f,protocol,pipeline,budget,acquisition_token)
  acquisition_token=None
  # Hash only after actual supervisor cleanup success. Certificate self-report
  # never authorizes a detached acquisition root or prior invocation.
  certificate_raw=read(roots['acquisition']/'TRANSPORT_RECEIPT.json');certificate_sha=sha(certificate_raw);budget.check()
  acquired=_snapshot(protocol,roots['acquisition'],budget,max_bytes=5*1024**3,max_entries=4096)
  runner,native_bytes=native_inputs(graph,seam,roots,certificate_raw,certificate_sha,owner.nonce,owner.deadline)
  static,transfer_request,anticipated=derive_outputs(runner,native_bytes,model);budget.check();fixed_check()
  owner._phase='admission'
  request={'schema':'c087-minimal-admission-request-v1','roots':{k:str(v) for k,v in roots.items() if k not in ('official_runtime','helper_source')},'session_nonce':owner.nonce,'deadline_monotonic':owner.deadline,'original_monotonic':budget.original.original_monotonic,'original_wall':budget.original.original_wall.timestamp(),'expiry_wall':budget.original.expiry_wall.timestamp(),'certificate_sha256':certificate_sha,'package_files':{k.removeprefix('ci/c087/admission/'):v for k,v in contract['files'].items() if k.startswith('ci/c087/admission/')},'input_snapshots':{k:baseline[k] for k in fixed_names if k!='helper_source'},'acquisition_snapshot':acquired}
  container=roots['container'];request_path=container/'request.json';invocation_path=container/'admission-invocation.json'
  request_raw=jb(request);protocol.write_new(request_path,request_raw,budget.check)
  argv,environment=child_layout(package,roots,container,request_path,invocation_path)
  timeout=sys.modules['job_budget'].command_timeout(19800,budget.deadline_monotonic,time.monotonic())
  invocation={'schema':'c087-minimal-owned-admission-invocation-v1','request_sha256':sha(request_raw),'argv':argv,'environment':environment,'timeout_seconds':timeout,'limits':LIMITS,'max_log_bytes':16*1024**2,'original_deadline_monotonic':owner.deadline,'session_nonce':owner.nonce}
  invocation_raw=jb(invocation);protocol.write_new(invocation_path,invocation_raw,budget.check)
  def dispatch_admission():
   result=f.run_process(argv,cwd=container,env=environment,timeout=timeout,stdout=container/'admission.stdout',stderr=container/'admission.stderr',max_log_bytes=16*1024**2,limits=LIMITS,allow_new_sessions=False)
   _accept_result_safety(result,timeout);owner._admission_safe_failure=(result,invocation)
   accept_child_result(result,timeout);return result
  result=budget.process(dispatch_admission);budget.check() # Before ANY child-created read.
  protocol.write_new(work/'admission-process.json',jb({'invocation':invocation,'result':result}),budget.check)
  need(read(request_path)==request_raw and read(invocation_path)==invocation_raw,'parent invocation mutated');budget.check()
  need(_snapshot(protocol,roots['acquisition'],budget,max_bytes=5*1024**3,max_entries=4096)==acquired,'acquisition changed')
  fixed_check()
  admitted=container/'admitted';historical=container/'admitted-historical-validation'
  inode=lambda path:[path.stat().st_dev,path.stat().st_ino]
  need(admitted.stat().st_dev==historical.stat().st_dev==container.stat().st_dev,'admission output device changed')
  unit=os.statvfs(container).f_frsize;need(unit==os.statvfs(admitted).f_frsize==os.statvfs(historical).f_frsize,'same filesystem allocation unit')
  dynamic=model.transfer_outputs(request=transfer_request,static=static,source_root=str(roots['research_source']),admission_root=str(latest/'admission'),historical_root=str(prior),workspace=str(admitted),historical_workspace=str(historical),workspace_inode=inode(admitted),historical_workspace_inode=inode(historical),allocation_unit=unit)
  expected_files={**static['files'],**{name:model.pin(raw) for name,raw in dynamic.items()}}
  admitted_snap={name:_snapshot(protocol,path,budget) for name,path in [('admitted',admitted),('admitted-historical-validation',historical)]}
  actual_files={name+'/'+rel:pin for name,snap in admitted_snap.items() for rel,pin in protocol.contents(snap).items()}
  actual_dirs=sorted(name if rel=='.' else name+'/'+rel for name,snap in admitted_snap.items() for rel,row in snap.items() if row['kind']=='directory')
  need(actual_files==expected_files and actual_dirs==static['directories'],'complete independently derived native output map')
  for name,raw in dynamic.items():need(read(container/name)==raw,'independent transfer certificate/marker bytes')
  expected_report={**anticipated,'session_nonce':owner.nonce,'host_deadline_monotonic':owner.deadline,'workspace':str(admitted),'workspace_inode':inode(admitted),'source_root_inode':inode(roots['research_source']),'workspace_files':protocol.contents(admitted_snap['admitted'])}
  report_raw=read(container/'native-report.json');need(parse(report_raw)==expected_report,'native report disagrees with independent expectations')
  need(parse(read(container/'response.json'))=={'schema':'c087-minimal-admission-completion-v1','request_sha256':sha(request_raw),'invocation_sha256':sha(invocation_raw),'native_report_sha256':sha(report_raw)},'child completion binding')
  need(set(os.listdir(container))=={'request.json','admission-invocation.json','admission.stdout','admission.stderr','native-report.json','response.json','admitted','admitted-historical-validation'},'extra native child outputs')
  budget.check();fixed_check();owner._phase='admitted'
  evidence={'schema':'c087-independent-admission-map-v1','files':actual_files,'directories':actual_dirs,'transfer_certificate_sha256':sha(dynamic['admitted/historical-transfer-certificate.json']),'proof_pass_claimed':False}
  protocol.write_new(work/'independent-admission.json',jb(evidence),budget.check)
  # Static inputs are immutable read-only child mounts with no other writer.
  # Full maps are checked at admission/engine phase boundaries. The unchanged
  # engine rehashes every predecessor around commands and binds source/engine
  # bytes itself; the frequent context check is intentionally cheap.
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
  response=budget.process(lambda:engine.engine(context));checkpoint();fixed_check()
  need(_snapshot(protocol,roots['acquisition'],budget,max_bytes=5*1024**3,max_entries=4096)==acquired,'acquisition changed during diagnostic')
  for name,snap in admitted_snap.items():need(_snapshot(protocol,container/name,budget)==snap,'admitted inode/hash map changed during diagnostic')
  final_snapshot=_snapshot(protocol,diagnostic,budget,max_bytes=4*1024**3,max_entries=100000)
  output_files=protocol.contents(final_snapshot)
  need(response=={'schema':'c087-fixed-engine-result-v1','status':'diagnostic_complete','session_nonce':owner.nonce,'deadline_monotonic':owner.deadline,'engine_manifest_sha256':context.manifest_sha256,'result_sha256':output_files['RESULT.json']['sha256'],'proof_pass_claimed':False,'output_files':{k:v for k,v in output_files.items() if k!='engine-invocation.json'}},'independent complete engine response')
  owner._phase='evidence';_package_evidence(owner,protocol,budget,output_files)
  checkpoint();need(_snapshot(protocol,diagnostic,budget,max_bytes=4*1024**3,max_entries=100000)==final_snapshot,'final diagnostic inode/hash map changed')
  manifest_raw=read(work/'upload/MANIFEST.json');manifest=parse(manifest_raw)
  copied=_snapshot(protocol,work/'upload',budget,max_bytes=MAX_EVIDENCE,max_entries=4096)
  need(protocol.contents(copied)=={**manifest['files'],'MANIFEST.json':{'bytes':len(manifest_raw),'sha256':sha(manifest_raw)}},'final complete evidence output map')
  checkpoint();protocol.write_new(work/'upload/COMPLETED.json',jb({'schema':'c087-minimal-completed-v1','status':'diagnostic_completed_pending_terminal_reconciliation','manifest_sha256':sha(manifest_raw),'session_nonce':owner.nonce,'original_deadline_monotonic':owner.deadline,'proof_pass_claimed':False}),budget.check)
  budget.check();owner._phase='complete';return response
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
 # No command line, log, request, result or exception contains the token.
 def dispatch_acquisition():
  result=native.run_process(argv,cwd=container,env=environment,timeout=timeout,stdout=container/'acquisition.stdout',stderr=container/'acquisition.stderr',max_log_bytes=16*1024**2,limits=LIMITS,allow_new_sessions=False)
  accept_child_result(result,timeout);return result
 try:result=budget.process(dispatch_acquisition)
 finally:environment.pop('GH_TOKEN',None);os.environ.pop('GH_TOKEN',None)
 accept_child_result(result,timeout);budget.check()
 need(read(container/'acquisition.stdout',16*1024**2)==b'C087 transport bytes authenticated; native semantic admission still required.\n' and read(container/'acquisition.stderr',16*1024**2)==b'','exact bounded acquisition completion')
 protocol.write_new(owner.work/'acquisition-process.json',jb({'schema':'c087-owned-acquisition-completion-v1','result':result,'session_nonce':owner.nonce,'deadline_monotonic':owner.deadline,'argv':argv,'environment_keys':sorted(environment),'credential_retained':False}),budget.check)

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
 for name in ('entry.json','acquisition-process.json','compatibility-process.json','admission-process.json','independent-admission.json','capacity.json'):selection[name]=work/name
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
