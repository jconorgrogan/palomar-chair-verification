"""Synthetic host-controller replay. No actual tools or project code run."""
import contextlib,copy,io,json,os,time
from pathlib import Path
from unittest.mock import patch

def exercise(p,C,parent):
 c=copy.deepcopy(C);c['review_status']='reviewed_for_execution';c['independent_driver_review_sha256']='0'*64
 work=parent/'synthetic-work';contract_sha=p.f.file_sha(p.ROOT/'smoke-contract.json');plans={r['name']:r for r in p.command_plan(c)}
 runtime_inventory={'files':{}}
 class Watchdog:
  deadline=time.monotonic()+7200;expired=False;in_command=False
  def check(self):pass
  def failure_receipt_grace(self):pass
 watchdog=Watchdog()
 def acquire(work,env,command):
  runtime=work/'runtime'
  for m in c['runtime_roots']:
   path=runtime/'lib/lean'/(m.replace('.','/')+'.olean');path.parent.mkdir(parents=True,exist_ok=True);data=('SYNTHETIC_RUNTIME_'+m).encode();path.write_bytes(data);runtime_inventory['files'][path.relative_to(runtime).as_posix()]={'bytes':len(data),'sha256':p.f.sha(data),'mode':0o644}
  p.a.RUNTIME_INVENTORY_SHA=p.f.sha(p.f.json_bytes(runtime_inventory));p.a.write_json(work/'evidence/runtime-inventory.json',runtime_inventory)
  for folder in ['preflight-read-only','preflight-quarantine']:(work/folder).mkdir()
  (work/'preflight-read-only/predecessor').write_bytes(b'IMMUTABLE_BOUNDARY_FIXTURE_ONLY\n')
  command('bwrap-preflight');command('read-only-committed-root-preflight')
  p.a.write_json(work/'evidence/read-only-boundary-preflight.json',{'status':'READ_ONLY_PREDECESSOR_WRITES_CHMOD_AND_NAMESPACE_CREATION_REJECTED','quarantine_write_allowed':True,'fixture_sha256':p.f.sha(b'IMMUTABLE_BOUNDARY_FIXTURE_ONLY\n'),'not_a_research_proof':True})
  return runtime
 def process(argv,*,cwd,env,timeout,stdout,stderr,max_log_bytes,limits,allow_new_sessions):
  name=stdout.name.removesuffix('.stdout');r=plans[name];kind=r['kind'];output='';error='';exit_code=0
  if kind=='api':output='INTERFACE_API_SELF_TEST_PASSED\n'
  elif kind in ['common-compile','compile-target','compile-bridge']:
   negative=name=='compile-fixture-wrong-compile-bridge'
   if negative:exit_code=1;error="PilotBridge.lean:14:1: error: tactic 'decide' proved that the proposition is false\n"
   else:
    if kind=='common-compile':module=r['module'];stage=work/'quarantine'/module
    else:
     row=next(x for x in p.variant_rows(c) if x['id']==r['case']);module='PilotBridge' if kind=='compile-bridge' else row['module'];stage=work/'quarantine'/(r['case']+'-'+r['mode'])/('bridge' if kind=='compile-bridge' else 'target')
    for rel in p.a.module_outputs(module):q=stage/rel;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(('SYNTHETIC_ARTIFACT_'+name+'_'+rel).encode())
  elif kind=='audit-bridge':
   row=next(x for x in p.variant_rows(c) if x['id']==r['case']);n=row['bridge_name'];output='BRIDGE_DECL\t'+n+'\ttheorem\t\nBRIDGE_AXIOMS_PASSED\t'+n+'\n'
  elif kind=='compare':
   row=next(x for x in p.variant_rows(c) if x['id']==r['case']);lines=[]
   for d in row['declarations']:lines.append('PUBLIC\t'+d['name']+'\t'+d['kind']+'\t')
   for side in ['original','candidate']:
    for d in row['declarations']:lines.append('KERNEL\t'+side+'\t'+d['name']+'\t'+d['kind']+'\t')
    for m in ['Init']+row['prerequisites']:lines.append('LOADED\t'+side+'\t'+m)
   lines.append('FAST_HEIGHT\t'+row['fast_name']+'\t1\t2');lines.append('PUBLIC_INTERFACE_AXIOMS_PASSED\t'+str(len(row['declarations'])));output='\n'.join(lines)+'\n'
  elif kind=='export':(work/'exports'/(r['case']+'-'+r['mode'])/'rooted.export').write_bytes(('SYNTHETIC_EXPORT_'+name).encode())
  stdout.write_text(output);stderr.write_text(error)
  return {'exit_code':exit_code,'timed_out':False,'log_overflow':False,'memory_exceeded':False,'surviving_children':False,'process_group_empty':True,'descendants_empty':True,'escaped_descendants':False,'new_sessions_explicitly_allowed':True,'elapsed_seconds':0.001,'peak_sampled_tree_rss_bytes':1}
 old_runtime_sha=p.a.RUNTIME_INVENTORY_SHA
 try:
  with patch.object(p,'validate_inputs',lambda c:None),patch.object(p.a,'git_capture',lambda root,*args:b'SYNTHETIC_COMMIT' if args[0]=='rev-parse' else b''),patch.object(p.d,'acquire_runtime',acquire),patch.object(p.d,'revalidate_runtime',lambda runtime,inv:None),patch.object(p.f,'run_process',process),patch.dict(os.environ,{'GITHUB_REF':'refs/heads/'+c['publication_branch'],'GITHUB_SHA':'SYNTHETIC_COMMIT'}),contextlib.redirect_stdout(io.StringIO()):
   p.run(c,contract_sha,work,watchdog)
   p.verify_success(c,contract_sha,work/'evidence',work)
   result=p.f.load_json(work/'evidence/result.json')
   if result['command_count']!=779:raise RuntimeError('synthetic command coverage differs')
   path=work/'evidence/cost-measurements.json';old=path.read_bytes();cost=p.f.load_json(path);cost['small-candidate']['export_replay_elapsed_seconds']=9;p.a.write_json(path,cost);result['terminal_receipts']['cost-measurements.json']=p.f.file_sha(path);p.a.write_json(work/'evidence/result.json',result)
   rejected=False
   try:p.verify_success(c,contract_sha,work/'evidence',work)
   except Exception:rejected=True
   if not rejected:raise RuntimeError('rehash-preserving cost substitution accepted')
   path.write_bytes(old);result['terminal_receipts']['cost-measurements.json']=p.f.file_sha(path);p.a.write_json(work/'evidence/result.json',result)
   p.verify_success(c,contract_sha,work/'evidence',work)
 finally:p.a.RUNTIME_INVENTORY_SHA=old_runtime_sha
 return {'synthetic_only':True,'commands':779,'actual_native_executions':0,'actual_project_compilations':0}
