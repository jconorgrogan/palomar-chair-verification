"""Inactive fixed C087 command sequence. Parent invocation authority is external.

This component never authenticates a downloaded receipt or grants permission to
execute. The separately reviewed parent must own the just-completed admission
child, one-shot capability, exact input/code pins and absolute job deadline.
The production entrypoint stays disabled until that composition is sealed.
"""
from __future__ import annotations
import copy, hashlib, json, math, os, stat, time
from pathlib import Path
import probe_policy as policy
import original_probe_commands as base

GIB=1024**3
TARGET=policy.TARGET
SUFFIXES=policy.SUFFIXES
SOURCE_SHA='5f93adcd7af879789a03ff03b37f500f16545d21a26fbdade911551bfde42f2f'
PROFILE_BYTES=512*1024**2
PREDECESSOR_COMPANIONS=6218*6
CONTROL_SHA='8242c078f3a61c8968c4929e0275ff2fb6bfee26be03f2f86594693bbe3ed5dc'
HELPER_FILES={'AuditC087Raw.lean': {'bytes': 2013, 'sha256': '0347bae8f298608ed8a0e9d2ee89466c1509a56d0550768b09a994741fd49dce'}, 'C087NegativeControls.lean': {'bytes': 7073, 'sha256': '8c058c63f822dcebb7e77baba0fc2a59aa19bbba4b3df0a339e4918db81ae27d'}, 'C087RawContract.lean': {'bytes': 8397, 'sha256': '061b0c9c608eec98f31b6e7c12a58046a56453042211b0ffe93b05f2a9dcc636'}, 'C087SourceShapeControl.lean': {'bytes': 2836, 'sha256': '78f693315b050d126fc472941eee2f398d208bfdc101fc62658e615fb2942a10'}, 'DefaultOptionControl.lean': {'bytes': 766, 'sha256': '1f374ac965af4025fcf757f1d666eb239cc726477a5cb79bd61a540e14bde4a6'}, 'DisabledOptionControl.lean': {'bytes': 773, 'sha256': '3d4f5734ae2a49d98347722fb2b4bcae570adddcd6c3481152acf726ea6a17ec'}}
AGGREGATE_LOG_BYTES=18*16*1024**2
class Rejected(ValueError):pass

def need(ok,message):
 if not ok:raise Rejected(message)
def jb(value):return (json.dumps(value,sort_keys=True,indent=2,allow_nan=False)+'\n').encode()
def digest(raw):return hashlib.sha256(raw).hexdigest()
def pinned_file(path):
 path=Path(path)
 for p in (path,*path.parents):need(not p.is_symlink(),'symlink path')
 fd=os.open(path,os.O_RDONLY|os.O_NOFOLLOW)
 try:
  before=os.fstat(fd);need(stat.S_ISREG(before.st_mode) and before.st_nlink==1,'regular unshared file required')
  h=hashlib.sha256();n=0
  while block:=os.read(fd,1024**2):h.update(block);n+=len(block)
  after=os.fstat(fd)
  need((before.st_dev,before.st_ino,before.st_size,before.st_mtime_ns,before.st_ctime_ns)==(after.st_dev,after.st_ino,after.st_size,after.st_mtime_ns,after.st_ctime_ns) and n==before.st_size,'file changed during hash')
  return {'bytes':n,'sha256':h.hexdigest()}
 finally:os.close(fd)
def tree(root, *, byte_limit=4*GIB, entry_limit=100000):
 root=Path(root);need(root.is_dir() and not root.is_symlink(),'tree root required')
 files={};dirs=set();total=0;entries=0
 for parent,ds,fs in os.walk(root,followlinks=False):
  for n in ds:
   entries+=1;need(entries<=entry_limit,'bounded tree capacity exceeded')
   p=Path(parent)/n;need(p.is_dir() and not p.is_symlink(),'tree directory alias');dirs.add(p.relative_to(root).as_posix())
  for n in fs:
   entries+=1;need(entries<=entry_limit,'bounded tree capacity exceeded')
   p=Path(parent)/n;st=p.lstat();need(stat.S_ISREG(st.st_mode) and st.st_nlink==1,'tree regular unshared file required');total+=st.st_size
   need(total<=byte_limit,'bounded tree capacity exceeded');files[p.relative_to(root).as_posix()]=pinned_file(p)
 return files,dirs

def retained_tree(root, *, byte_limit=4*GIB):
 files,dirs=tree(root,byte_limit=byte_limit);metadata={}
 for name in ['.',*sorted(dirs),*sorted(files)]:
  p=Path(root) if name=='.' else Path(root)/name;st=p.lstat()
  metadata[name]={'dev':st.st_dev,'ino':st.st_ino,'mode':st.st_mode,'nlink':st.st_nlink,
   'uid':st.st_uid,'gid':st.st_gid,'size':st.st_size,'mtime_ns':st.st_mtime_ns,'ctime_ns':st.st_ctime_ns}
 return {'files':files,'directories':sorted(dirs),'inodes':metadata}

def durable_new(path,value):
 raw=jb(value);path=Path(path)
 fd=os.open(path,os.O_WRONLY|os.O_CREAT|os.O_EXCL|os.O_NOFOLLOW,0o600)
 try:
  view=memoryview(raw)
  while view:
   n=os.write(fd,view);need(n>0,'short durable write');view=view[n:]
  os.fsync(fd)
 finally:os.close(fd)
 dfd=os.open(path.parent,os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW)
 try:os.fsync(dfd)
 finally:os.close(dfd)
 return digest(raw)

def command_plan(native, *, source_root,toolchain_root,predecessor_objects,helper_root,diagnostic_output):
 source_root=base.canonical(str(source_root));toolchain_root=base.canonical(str(toolchain_root))
 predecessor_objects=base.canonical(str(predecessor_objects));helper_root=base.canonical(str(helper_root));diagnostic_output=base.canonical(str(diagnostic_output))
 roots=list(map(Path,(source_root,toolchain_root,predecessor_objects,helper_root,diagnostic_output)))
 need(all(a!=b and a not in b.parents and b not in a.parents for i,a in enumerate(roots) for b in roots[i+1:]),'all engine roots must be disjoint')
 args=dict(source_root=source_root,toolchain_root=toolchain_root,helper_root=helper_root,helper_workspace=diagnostic_output+'/helpers')
 a=base.plan(native,stage_workspace=diagnostic_output+'/default',**args)
 b=base.plan(native,stage_workspace=diagnostic_output+'/async_off',**args)
 need(a[:12]==b[:12] and len(a)==len(b)==18,'fixed helper prefix changed')
 rows=copy.deepcopy(a[:15]+b[15:])
 for row in rows[12:]:
  argv=row['argv'];layout=row['sandbox'];i=argv.index('--chdir')
  argv[i:i]=['--ro-bind',predecessor_objects,predecessor_objects]
  i=argv.index('LEAN_PATH');paths=argv[i+1].split(':')
  need(paths[-1]==toolchain_root+'/lib/lean','runtime search path changed')
  paths.insert(len(paths)-1,predecessor_objects);value=':'.join(paths);argv[i+1]=value
  layout['readonly_roots'].append(predecessor_objects);layout['environment']['LEAN_PATH']=value
 return rows

class _PromotionWorkspace:
 """Explicit non-authoritative receiver for the unchanged native file mover only."""
 def __init__(self,root):
  self.workspace=Path(root);self.contract={'output_suffixes':list(SUFFIXES)}

def workspace(root):
 root=Path(root);need(not root.exists(),'workspace must be fresh');root.mkdir(mode=0o700)
 for name in ('objects','scratch','logs','module-quarantine'):(root/name).mkdir(mode=0o700)
 for name in ('home','tmp'):(root/'scratch'/name).mkdir(mode=0o700)
 return root

def _module(row):
 inner=row['inner_argv']
 if row['phase']=='compile':return Path(inner[inner.index('-o')+1]).relative_to(Path(row['sandbox']['writable_roots'][-1])/'objects').as_posix().removesuffix('.olean').replace('/','.')
 return TARGET if row['phase']=='audit' else inner[-1]

def _root(row):
 return Path(row['sandbox']['environment']['HOME']).parents[1]

def _read_log(path,maximum):
 row=pinned_file(path);need(row['bytes']<=maximum,'log exceeds bound')
 raw=Path(path).read_bytes();need({'bytes':len(raw),'sha256':digest(raw)}==row,'log changed after hashing');return raw

def prevalidate_native_exit(result, effective):
 # Reject unsafe cleanup/session/resource outcomes before opening any child file.
 need(type(result) is dict and set(result)==policy.NATIVE_RESULT_KEYS,'native result shape')
 need(result.get('new_sessions_explicitly_allowed') is False,'native session policy')
 need(type(result.get('cleanup_bound_seconds')) in (int,float) and math.isfinite(result['cleanup_bound_seconds']) and result['cleanup_bound_seconds']==3.0,'native cleanup bound')
 need(type(result.get('cleanup_elapsed_seconds')) in (int,float) and math.isfinite(result['cleanup_elapsed_seconds']) and 0<=result['cleanup_elapsed_seconds']<=3.0,'native cleanup elapsed')
 need(type(result.get('peak_sampled_tree_rss_bytes')) is int and 0<=result['peak_sampled_tree_rss_bytes']<=policy.LIMITS['rss_tree_bytes'],'native resource observation')
 policy.safety({**result,'timeout_seconds':effective})

def run_probe(*args,**kwargs):
 raise Rejected('production capability/controller binding is not yet sealed')

def _run_fixed_sequence(native, *, source_root,toolchain_root,predecessor_objects,helper_root,diagnostic_output,
                         predecessor_files,control_expectations,remaining,verify_inputs,executor,initial_files=None):
 """Private integration/test seam. Only a sealed parent may bind real execution."""
 out=Path(diagnostic_output);initial_files={} if initial_files is None else copy.deepcopy(initial_files)
 need(set(initial_files)<= {'engine-invocation.json'},'unapproved initial engine file')
 need(out.is_dir() and not out.is_symlink() and tree(out)==(initial_files,set()),'exclusive registered diagnostic output required')
 rows=command_plan(native,source_root=source_root,toolchain_root=toolchain_root,predecessor_objects=predecessor_objects,helper_root=helper_root,diagnostic_output=out)
 need(pinned_file(Path(source_root)/(TARGET.replace('.','/')+'.lean'))=={'bytes':837,'sha256':SOURCE_SHA},'exact target source required')
 expected_predecessors=copy.deepcopy(predecessor_files)
 need(type(expected_predecessors) is dict and len(expected_predecessors)==PREDECESSOR_COMPANIONS,'exact admitted companion count required')
 need(not any(p.startswith(TARGET.replace('.','/')+'.') for p in expected_predecessors),'target must not occur in predecessor namespace')
 need(tree(predecessor_objects)[0]==expected_predecessors,'predecessor content map differs')
 verify_inputs();policy.effective_timeout(120,remaining())
 control_names={'C087NegativeControls':'negative','C087SourceShapeControl':'shape','DefaultOptionControl':'default','DisabledOptionControl':'disabled'}
 need(set(control_expectations)==set(control_names.values()) and digest(jb(control_expectations))==CONTROL_SHA,'fixed control expectations required')
 need(tree(helper_root)[0]==HELPER_FILES,'fixed helper source bytes required')
 for root in dict.fromkeys(_root(r) for r in rows):workspace(root)
 (out/'receipts').mkdir(mode=0o700)
 records=[];frozen={};failed_frozen={};completed_profiles={};outputs={};audits={};classes={};logs_total=0
 def check_frozen():
  need(all(pinned_file(out/name)==row for name,row in initial_files.items()),'parent engine invocation changed')
  verify_inputs();policy.effective_timeout(120,remaining())
  need(tree(predecessor_objects)[0]==expected_predecessors,'admitted predecessors changed')
  for root,expected in frozen.items():
   actual,dirs=tree(root/'objects');allowed={p.as_posix() for name in expected for p in Path(name).parents if p.as_posix()!='.'}
   need(actual==expected and dirs==allowed,'committed diagnostic output changed')
  for root,expected in failed_frozen.items():need(retained_tree(root)==expected,'retained failed-profile evidence changed')
  for root,expected in completed_profiles.items():need(retained_tree(root)==expected,'retained complete profile changed')
  for root in frozen:
   need(not (set(frozen[root]) & set(expected_predecessors)),'diagnostic/predecessor provider collision')
  policy.effective_timeout(120,remaining())
 def execute(row):
  nonlocal logs_total
  check_frozen();root=_root(row);module=_module(row)
  if row['phase']=='compile':
   quarantine=root/'module-quarantine'/module
   need(not quarantine.exists(),'compile quarantine already exists')
   (quarantine/'objects'/module.replace('.','/')).parent.mkdir(parents=True,mode=0o700)
  for path in row['sandbox']['readonly_roots']+row['sandbox']['writable_roots']:
   native.no_symlink_path(Path(path));need(Path(path).is_dir(),'sandbox mount absent')
  effective=policy.effective_timeout(120,remaining())
  stdout=root/'logs'/(row['name']+'.stdout');stderr=root/'logs'/(row['name']+'.stderr')
  need(not stdout.exists() and not stderr.exists(),'command logs already exist')
  result=executor(row['argv'],cwd=Path(row['sandbox']['cwd']),env=row['sandbox']['environment'],timeout=effective,
    stdout=stdout,stderr=stderr,max_log_bytes=row['max_log_bytes'],limits=row['resource_limits'],allow_new_sessions=False)
  prevalidate_native_exit(result,effective);policy.effective_timeout(120,remaining())
  rawout=_read_log(stdout,row['max_log_bytes']);rawerr=_read_log(stderr,row['max_log_bytes']);logs_total+=len(rawout)+len(rawerr)
  need(logs_total<=AGGREGATE_LOG_BYTES,'aggregate complete logs exceeded')
  record={'spec':row,'effective_timeout_seconds':effective,'result':result,'stdout':{'bytes':len(rawout),'sha256':digest(rawout)},'stderr':{'bytes':len(rawerr),'sha256':digest(rawerr)}}
  durable_new(out/'receipts'/('%02d-%s.json'%(len(records),row['name'])),record)
  records.append(record)
  actual=policy.validate_live_command(row,record,rawout,rawerr,expected_effective_timeout=effective)
  policy.effective_timeout(120,remaining());check_frozen()
  return {**actual,'timeout_seconds':effective},rawout,rawerr
 try:
  for row in rows[:12]:
   result,stdout,stderr=execute(row);policy.require_success(result);need(stderr==b'','successful helper stderr must be empty')
   root=_root(row);module=_module(row)
   if row['phase']=='compile':
    if module in control_names:
     expected=control_expectations[control_names[module]]
     need(expected['module']==module and stdout.decode('utf-8').splitlines()==expected['exact_stdout_lines'],'control output changed')
    else:need(stdout==b'','unexpected helper compile stdout')
    before,total=native.StageRunner.promote_quarantine(_PromotionWorkspace(root),module,PROFILE_BYTES-sum(x['bytes'] for x in frozen.get(root,{}).values()))
    owned={name.removeprefix('objects/'):pinned_file(root/name) for name in before}
    policy.validate_output_map(module,{'objects/'+k:v for k,v in owned.items()})
    outputs.setdefault(str(root),{}).update(owned);frozen[root]=copy.deepcopy(outputs[str(root)])
   else:need(stdout==b'','unexpected helper checker stdout')
   check_frozen()
  for label,offset in (('default',12),('async_off',15)):
   compile_row,check_row,audit_row=rows[offset:offset+3]
   result,stdout,stderr=execute(compile_row);classification=policy.classify_compile(label,result,stdout,stderr);classes[label]=classification
   root=_root(compile_row)
   if classification=='observed_default_thread_creation_abort_no_outputs_admitted':
    # Preserve every failed output and log in place. Never promote or search it.
    tree(root/'module-quarantine',byte_limit=PROFILE_BYTES)
    failed=retained_tree(root,byte_limit=PROFILE_BYTES+16*1024**2+1024**2);failed_frozen[root]=failed;durable_new(out/'receipts'/'default-abort-retained.json',{'tree':failed,'classification':classification})
    continue
   before,total=native.StageRunner.promote_quarantine(_PromotionWorkspace(root),TARGET,PROFILE_BYTES)
   own={name.removeprefix('objects/'):pinned_file(root/name) for name in before};policy.validate_output_map(TARGET,{'objects/'+k:v for k,v in own.items()})
   outputs[str(root)]=own;frozen[root]=copy.deepcopy(own)
   check,stdout,stderr=execute(check_row);policy.require_success(check);need(stdout==stderr==b'','unexpected target checker output')
   audit,stdout,stderr=execute(audit_row);policy.require_success(audit);need(stderr==b'','raw auditor stderr')
   audits[label]=stdout;policy.parse_audit(stdout);check_frozen()
   durable_new(out/'receipts'/(label+'-accepted.json'),{'profile':label,'outputs':own,'audit_sha256':digest(stdout),'checked':True,'exact_raw_audit':True,'proof_pass_claimed':False})
   completed_profiles[root]=retained_tree(root);check_frozen()
  need('async_off' in audits,'async-off audit missing')
  comparison=policy.compare_successful_profiles(audits['default'],audits['async_off']) if 'default' in audits else {'both_profiles_compiled_checked_audited':False,'raw_type_and_proof_equal':None,'olean_byte_identity_claimed':False,'os_failure_cause_proven':False,'final_C_proof_claimed':False}
  check_frozen();result={'schema':'c087-bounded-ab-diagnostic-v1','status':'both_required_profile_outcomes_validated','commands':records,'profile_classifications':classes,'outputs':outputs,'audit_rows':{k:policy.parse_audit(v) for k,v in audits.items()},'comparison':comparison,'original_source_sha256':SOURCE_SHA,'predecessor_companion_count':len(expected_predecessors),'proof_pass_claimed':False,'native_build087_artifact_claimed':False,'parent_acceptance_pending':True}
  durable_new(out/'RESULT.json',result);check_frozen();return result
 except BaseException:
  # Never delete a preexisting or partially produced tree and never accept a
  # repaired retry. The enclosing one-shot parent must poison its capability.
  raise

ENGINE_DIRS=('helpers','helpers-control-C087NegativeControls','helpers-control-C087SourceShapeControl',
 'helpers-control-DefaultOptionControl','helpers-control-DisabledOptionControl','default','async_off','receipts')

def engine(context):
 """Fixed in-process consumer. It is usable only through the reviewed parent factory.

 The context is an unforgeable-in-that-factory closure binding, not serialized
 authority. This function alone never turns a report/directory into permission.
 """
 import types
 manifest=policy.json.loads(context.manifest_bytes,object_pairs_hook=_unique_pairs,
   parse_constant=lambda _:(_ for _ in ()).throw(Rejected('nonfinite engine manifest')))
 need(type(manifest) is dict and set(manifest)=={'schema','native_source_path','native_source_sha256',
  'source_root','toolchain_root','helper_root','predecessor_objects','diagnostic_output',
  'predecessor_files','control_expectations','code_pins'},'fixed engine manifest schema')
 need(manifest['schema']=='c087-fixed-engine-manifest-v1' and digest(context.manifest_bytes)==context.manifest_sha256,'fixed engine manifest binding')
 roots=dict(context.input_roots)
 for name,field in [('research_source','source_root'),('official_runtime','toolchain_root'),('helper_source','helper_root')]:
  need(name in roots and roots[name]==manifest[field],'engine input root binding')
 need(manifest['predecessor_objects']==context.admitted_objects and manifest['diagnostic_output']==context.diagnostic_output,'engine retained/output root binding')
 need(manifest['native_source_path']==str(Path(roots['latest_pipeline'])/'ci/fresh_stage.py') and manifest['native_source_sha256']==base.NATIVE_SHA,'fixed native source identity')
 code=Path(__file__).resolve().parent
 need(set(manifest['code_pins'])=={'probe_engine.py','probe_policy.py','original_probe_commands.py'},'fixed engine dependency set')
 need(Path(policy.__file__).resolve()==code/'probe_policy.py' and Path(base.__file__).resolve()==code/'original_probe_commands.py','engine dependency import path')
 def pins():
  context.checkpoint()
  for name,row in manifest['code_pins'].items():need(pinned_file(code/name)==row,'engine source dependency changed')
  need(pinned_file(manifest['native_source_path'])['sha256']==base.NATIVE_SHA,'native executor source changed')
  return context.checkpoint()
 pins()
 invocation=Path(context.diagnostic_output)/'engine-invocation.json'
 need(pinned_file(invocation)['sha256']==context.engine_invocation_sha256,'parent engine invocation binding')
 raw=Path(manifest['native_source_path']).read_bytes();need(digest(raw)==base.NATIVE_SHA,'native executor read changed')
 native=types.ModuleType('c087_engine_fixed_native');native.__file__=manifest['native_source_path']
 # Execute the exact just-authenticated buffer, bypassing all bytecode caches.
 exec(compile(raw,native.__file__,'exec'),native.__dict__)
 result=_run_fixed_sequence(native,source_root=manifest['source_root'],toolchain_root=manifest['toolchain_root'],
  predecessor_objects=manifest['predecessor_objects'],helper_root=manifest['helper_root'],diagnostic_output=manifest['diagnostic_output'],
  predecessor_files=manifest['predecessor_files'],control_expectations=manifest['control_expectations'],
  remaining=context.checkpoint,verify_inputs=pins,executor=native.run_process,
  initial_files={'engine-invocation.json':pinned_file(Path(context.diagnostic_output)/'engine-invocation.json')})
 pins();files,dirs=tree(context.diagnostic_output)
 need(set(p.split('/')[0] for p in files)==set(ENGINE_DIRS)|{'RESULT.json','engine-invocation.json'},'diagnostic output top-level files differ')
 need(all(p.split('/')[0] in ENGINE_DIRS for p in dirs),'diagnostic output directory differs')
 need(files['RESULT.json']['sha256']==digest(jb(result)),'fixed engine RESULT changed')
 response={'schema':'c087-fixed-engine-result-v1','status':'diagnostic_complete','session_nonce':context.nonce,
  'deadline_monotonic':context.deadline_monotonic,'engine_manifest_sha256':context.manifest_sha256,
  'result_sha256':files['RESULT.json']['sha256'],'proof_pass_claimed':False,'output_files':{k:v for k,v in files.items() if k!='engine-invocation.json'}}
 pins();return response

def _unique_pairs(rows):
 out={}
 for key,value in rows:need(key not in out,'duplicate engine JSON key');out[key]=value
 return out
