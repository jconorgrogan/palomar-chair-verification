#!/usr/bin/env python3
"""Tiny cloud-only readonly namespace probe; no research theorem imports."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,os,resource,shutil,signal,subprocess,sys,time,urllib.request
ROOT=Path(__file__).resolve().parents[1]
EXPECTED_RUNTIME='42bd268b1ca3e9bf89f4149ac427d6c0e76f735233b092a6df4ca27a2c2db7ea'
ARCHIVE_SHA='b67d0e0ba959fc74e186f1b44aebca32d6ecb6a28f8e9a029fc4e9f73398a049'
ARCHIVE_BYTES=595391556
URL='https://github.com/leanprover/lean4/releases/download/v4.35.0-rc2/lean-4.35.0-rc2-linux.tar.zst'
REPO='jconorgrogan/palomar-chair-verification'
MODULES=['ProbeShared.Seed','ProbeShared.Middle','ProbeShared.Consumer']
def need(ok,msg):
 if not ok:raise RuntimeError(msg)
def sha(path):
 h=hashlib.sha256()
 with path.open('rb') as file:
  for block in iter(lambda:file.read(1024*1024),b''):h.update(block)
 return h.hexdigest()
def write(path,value):path.write_text(json.dumps(value,indent=2,sort_keys=True)+'\n')
def load_module(name,path):
 spec=importlib.util.spec_from_file_location(name,path);module=importlib.util.module_from_spec(spec);sys.modules[name]=module;spec.loader.exec_module(module);return module

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--contract-sha256',required=True);ap.add_argument('--work',type=Path,required=True);a=ap.parse_args()
 need(sys.flags.isolated and sys.dont_write_bytecode,'Use python3 -I -B')
 contract_path=ROOT/'contract.json';need(sha(contract_path)==a.contract_sha256,'probe contract digest mismatch');c=json.loads(contract_path.read_text())
 need(c['review_status']=='reviewed_for_execution','INACTIVE: probe awaits review')
 need(c['scope']=='TINY_READONLY_NAMESPACE_PROBE_ONLY','wrong probe scope')
 need(os.environ.get('GITHUB_ACTIONS')=='true' and os.environ.get('GITHUB_REPOSITORY')==REPO,'cloud probe repository/context mismatch')
 need(os.environ.get('GITHUB_REF')=='refs/heads/'+c['publication_branch'],'probe branch mismatch')
 commit=os.environ.get('GITHUB_SHA','');need(len(commit)==40 and all(x in '0123456789abcdef' for x in commit),'invalid workflow commit')
 need(subprocess.check_output(['/usr/bin/git','-C',str(ROOT),'rev-parse','HEAD'],text=True).strip()==commit,'checkout identity mismatch')
 need(not subprocess.check_output(['/usr/bin/git','-C',str(ROOT),'status','--porcelain=v1','--untracked-files=all','--ignored']),'checkout is not clean')
 expected=set(c['inputs'])|{'contract.json','.github/workflows/readonly-probe.yml'}
 actual={p.relative_to(ROOT).as_posix() for p in ROOT.rglob('*') if '.git' not in p.relative_to(ROOT).parts and (p.is_file() or p.is_symlink())}
 need(actual==expected,'probe package file set mismatch')
 for rel,row in c['inputs'].items():
  p=ROOT/rel;need(not p.is_symlink() and p.stat().st_size==row['bytes'] and sha(p)==row['sha256'],'probe input identity mismatch: '+rel)
 f=load_module('fresh_stage',ROOT/'ci/fresh_stage.py');install=load_module('toolchain_install',ROOT/'ci/toolchain_install.py')
 work=a.work.absolute();f.no_symlink_path(work);need(not work.exists(),'probe work must be new');work.mkdir(parents=True)
 evidence=work/'evidence';evidence.mkdir();deadline=time.monotonic()+c['total_wall_seconds'];signal.alarm(c['total_wall_seconds'])
 if hasattr(os,'sched_setaffinity'):os.sched_setaffinity(0,{min(os.sched_getaffinity(0))})
 resource.setrlimit(resource.RLIMIT_AS,(8*1024**3,8*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(c['total_wall_seconds'],c['total_wall_seconds']))
 result={'schema':'readonly-namespace-probe-v1','status':'INCOMPLETE','research_theorem_claimed':False,'fresh_full_C_claimed':False,'pipeline_commit':commit,'run_id':os.environ.get('GITHUB_RUN_ID'),'run_attempt':os.environ.get('GITHUB_RUN_ATTEMPT'),'contract_sha256':a.contract_sha256}
 write(evidence/'RESULT.json',result)
 stage=None
 try:
  archive=work/'lean.tar.zst';start=time.monotonic();count=0
  with urllib.request.urlopen(URL,timeout=30) as response,archive.open('xb') as out:
   while block:=response.read(1024*1024):
    count+=len(block);need(count<=ARCHIVE_BYTES and time.monotonic()-start<180,'official archive download bound');out.write(block)
  need(count==ARCHIVE_BYTES and sha(archive)==ARCHIVE_SHA,'official runtime archive identity')
  runtime=work/'runtime';inventory=install.install_archive(archive,runtime);inventory_path=work/'runtime-inventory.json';inventory_path.write_bytes(f.json_bytes(inventory))
  need(sha(inventory_path)==EXPECTED_RUNTIME,'official inventory identity')
  tiny_contract={'schema':'fresh-stage-contract-v1','scope':'TINY_READONLY_NAMESPACE_PROBE_ONLY','review_status':'reviewed_for_execution','source_commit':commit,'lean_release':'v4.35.0-rc2','lean_archive_sha256':ARCHIVE_SHA,'runner':'ubuntu-22.04','maximum_parallel_jobs':1,'retention_days':7,'reserved_final_jobs':1,'job_timeout_seconds':min(600,max(1,int(deadline-time.monotonic()))),'max_artifact_bytes':32*1024**2,'max_log_bytes':256*1024,'max_restored_bytes':64*1024**2,'max_stage_output_bytes':16*1024**2,'max_run_age_seconds':86400,'minimum_free_disk_bytes':128*1024**2,'module_interface':'modern_exposed_v1','output_suffixes':f.MODERN_SUFFIXES,'transport_review_status':'reviewed','compiler_adapter_review_status':'reviewed','process_containment_review_status':'reviewed','storage_adapter_review_status':'reviewed','readonly_commit_review_status':'reviewed','receipt_protocol':f.READONLY_PROTOCOL,'toolchain_inventory_sha256':EXPECTED_RUNTIME}
  f.verify_toolchain(runtime,archive,inventory_path,tiny_contract,derived_inventory_sha256=EXPECTED_RUNTIME)
  result['official_runtime_inventory_sha256']=EXPECTED_RUNTIME;result['runtime_setup_seconds']=time.monotonic()-start
  # Tiny inert fixtures. Writable roots cannot overlap any read-only input.
  boundary=work/'boundary'
  for rel in ['objects/ProbeShared','module-quarantine/ProbeShared.Seed','scratch/home','scratch/tmp','cache']:(boundary/rel).mkdir(parents=True,exist_ok=True)
  predecessor=boundary/'objects/ProbeShared/Sentinel';predecessor.write_bytes(b'fixed predecessor\n')
  cache=boundary/'cache/Sentinel';cache.write_bytes(b'fixed cache\n')
  protected=[predecessor,ROOT/'src/ProbeShared/Seed.lean',runtime/'lib/lean/Init.olean',cache]
  before={str(p):sha(p) for p in protected};outpath=boundary/'module-quarantine/ProbeShared.Seed/allowed-output'
  paths={'source_root':str(ROOT/'src'),'toolchain_root':str(runtime),'workspace':str(boundary)}
  script='set -eu; for p in "$1" "$2" "$3" "$4"; do if (printf BAD >> "$p") 2>/dev/null; then exit 41; fi; if chmod u+w "$p" 2>/dev/null; then exit 42; fi; if rm "$p" 2>/dev/null; then exit 43; fi; if mkdir "$(dirname "$p")/forbidden-directory" 2>/dev/null; then exit 44; fi; done; printf ALLOWED > "$5"; printf "READONLY_BOUNDARY_PASSED\\n"'
  def boundary_command(name,phase,inner):
   argv,_,layout=f.readonly_command_layout(paths,'ProbeShared.Seed','ProbeShared/Seed.lean',[],phase)
   at=argv.index('--');argv=argv[:at]+['--',*inner]
   at=argv.index('--chdir');argv[at:at]=['--ro-bind',str(boundary/'cache'),str(boundary/'cache')]
   r=f.run_process(argv,cwd=ROOT/'src',env=layout['environment'],timeout=30,stdout=evidence/(name+'.stdout'),stderr=evidence/(name+'.stderr'),max_log_bytes=256*1024,limits={'address_space_bytes':512*1024**2,'rss_tree_bytes':256*1024**2,'max_created_file_bytes':1024*1024})
   r.update(argv=argv,sandbox=layout,extra_readonly_cache_root=str(boundary/'cache'));write(evidence/(name+'.json'),r)
   need(r['exit_code']==0 and not any(r[k] for k in ['timed_out','log_overflow','memory_exceeded','surviving_children','escaped_descendants']) and r['process_group_empty'] and r['descendants_empty'],'boundary command failed or escaped')
   need(before=={str(p):sha(p) for p in protected},'readonly fixture changed')
   return r
  boundary_command('compile-write-denial','compile',['/bin/sh','-c',script,'probe',*map(str,protected),str(outpath)])
  need(outpath.read_bytes()==b'ALLOWED','writable quarantine failed')
  checkscript='set -eu; if (printf BAD >> "$1") 2>/dev/null; then exit 45; fi; if (printf BAD >> "$2") 2>/dev/null; then exit 46; fi; printf "READONLY_CHECKER_BOUNDARY_PASSED\\n"'
  boundary_command('checker-write-denial','check',['/bin/sh','-c',checkscript,'probe',str(predecessor),str(outpath)])
  need(outpath.read_bytes()==b'ALLOWED','checker changed quarantine')
  result['write_denial_boundaries_passed']=True
  files=[]
  for module in MODULES:
   rel=module.replace('.','/')+'.lean';p=ROOT/'src'/rel;data=p.read_bytes();imports,implicit=f.import_header(data)
   files.append({'module':module,'path':rel,'bytes':len(data),'sha256':f.sha(data),'ordered_imports':imports,'implicit_Init':implicit})
  manifest={'source_count':3,'source_bytes':sum(x['bytes'] for x in files),'files':files,'external_imports':['Init']}
  plan={'stages':[{'stage_id':'tiny_chain','modules':MODULES,'required_predecessors':[],'producer_job':'tiny_probe'}]}
  profile={'review_status':'reviewed','compile_flags':['-j1','-M512','-Dcompiler.postponeCompile=false'],'check_flags':['--silent'],'address_space_bytes':4*1024**3,'rss_tree_bytes':2*1024**3,'max_created_file_bytes':64*1024**2,'compile_timeout_seconds':60,'check_timeout_seconds':60}
  profiles={'profiles':{'tiny':profile},'module_profiles':{m:'tiny' for m in MODULES}}
  identity={'source_commit':commit,'run_id':os.environ['GITHUB_RUN_ID'],'run_attempt':os.environ['GITHUB_RUN_ATTEMPT'],'run_started_at':__import__('datetime').datetime.now(__import__('datetime').timezone.utc).isoformat(),'scope':'TINY_READONLY_NAMESPACE_PROBE_ONLY','runner_sha256':sha(ROOT/'ci/fresh_stage.py')}
  stage=work/'stage';runner=f.StageRunner(contract=tiny_contract,manifest=manifest,plan=plan,profiles=profiles,identity=identity,source_root=ROOT/'src',toolchain_root=runtime,toolchain_inventory=inventory,workspace=stage)
  descriptor=runner.run('tiny_chain',[],'tiny_probe');runner.verify_checked_objects()
  need(len(runner.objects)==3 and sum(len(v) for v in runner.objects.values())==18,'tiny output set incomplete')
  need((stage/'delta.tar').stat().st_size<=8*1024**2,'tiny evidence archive bound')
  shutil.copyfile(stage/'delta.tar',evidence/'tiny-stage.tar');write(evidence/'tiny-descriptor.json',descriptor)
  # The second configuration uses the exact conditional runner's sandbox and
  # admission functions, including its explicit nested-session allowance.
  conditional=load_module('conditional_probe',ROOT/'ci/conditional_probe.py')
  conditional.f=load_module('conditional_process',ROOT/'ci/conditional_process.py')
  conditional_commands=[]
  def conditional_command(name,argv,*,cwd,env,seconds,rss,allowed_sessions):
   need(allowed_sessions is True,'conditional topology must explicitly admit nested session')
   remaining=int(deadline-time.monotonic());need(remaining>0,'total probe deadline')
   out=evidence/(name+'.stdout');err=evidence/(name+'.stderr')
   r=conditional.f.run_process(list(map(str,argv)),cwd=cwd,env=env,timeout=min(seconds,remaining),stdout=out,stderr=err,max_log_bytes=256*1024,
      limits={'address_space_bytes':4*1024**3,'rss_tree_bytes':rss,'max_created_file_bytes':64*1024**2},allow_new_sessions=True)
   r.update(name=name,argv=list(map(str,argv)),cwd=str(cwd),stdout_sha256=sha(out),stderr_sha256=sha(err))
   conditional_commands.append(r);write(evidence/'conditional-commands.json',conditional_commands)
   ok=r['exit_code']==0 and not any(r[k] for k in ['timed_out','log_overflow','memory_exceeded','surviving_children']) and r['process_group_empty'] and r['descendants_empty'] and r['new_sessions_explicitly_allowed']
   need(ok,'conditional topology command failed or cleanup incomplete')
   return out,ok
  (work/'home').mkdir();(work/'tmp').mkdir()
  conditional_env={'PATH':str(runtime/'bin')+':/usr/bin:/bin','HOME':str(work/'home'),'TMPDIR':str(work/'tmp'),'LANG':'C.UTF-8','LC_ALL':'C.UTF-8','LEAN_NUM_THREADS':'1'}
  conditional_result=conditional.run_probe(conditional,runtime=runtime,runtime_inventory=inventory,work=work,env=conditional_env,command=conditional_command)
  need(conditional_result['status']=='PASSED_SHARED_READONLY_NAMESPACE_PROBE','conditional topology result incomplete')
  result.update(status='PASSED_TINY_READONLY_NAMESPACE_PROBE',tiny_compile_check_pairs=6,exact_companions=39,source_hashes={x['module']:x['sha256'] for x in files},readonly_argv_protocol=f.READONLY_PROTOCOL,stage_artifact_sha256=sha(stage/'delta.tar'),
    session_configurations={'C_stage':{'new_session':False,'allow_new_sessions':False,'compile_check_pairs':3,'companions':18},'conditional':{'new_session':True,'allow_new_sessions':True,'compile_check_pairs':3,'companions':21,'receipt_sha256':sha(evidence/'shared-readonly-probe.json'),'commands_sha256':sha(evidence/'conditional-commands.json')}})
 except BaseException as error:
  result.update(status='FAILED',error_type=type(error).__name__,error=str(error)[:2000]);raise
 finally:
  if stage and stage.exists():
   if (stage/'logs').exists():shutil.copytree(stage/'logs',evidence/'stage-logs')
   for name in ['last_command.json','promotion-state.json']:
    if (stage/name).is_file():shutil.copyfile(stage/name,evidence/name)
  write(evidence/'RESULT.json',result)
  evidence_files={p.relative_to(evidence).as_posix():{'bytes':p.stat().st_size,'sha256':sha(p)} for p in evidence.rglob('*') if p.is_file()}
  need(sum(x['bytes'] for x in evidence_files.values())<=16*1024**2,'probe evidence bound exceeded')
  write(evidence/'INVENTORY.json',evidence_files)
  need(sum(p.stat().st_size for p in evidence.rglob('*') if p.is_file())<=16*1024**2,'probe evidence including inventory exceeds bound')
if __name__=='__main__':main()
