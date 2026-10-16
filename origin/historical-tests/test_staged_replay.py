import copy,json,os,sys,tempfile,unittest
from pathlib import Path
from unittest.mock import patch
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'ci'))
import cache_diagnostic as c
class StagePlanTests(unittest.TestCase):
 def contract(self):return json.loads((ROOT/'contract.json').read_text())
 def test_exact_partition(self):c.validate_stage_plan(self.contract())
 def test_duplicate_or_missing_module(self):
  for duplicate in [True,False]:
   x=self.contract();rows=x['stages']['F1_curved_existence']['modules']
   rows[0]=rows[1] if duplicate else 'Missing.Source'
   with self.assertRaises(Exception):c.validate_stage_plan(x)
 def test_bad_ancestor_or_edge(self):
  for field in ['needs','admitted_stages']:
   x=self.contract();x['stages']['F3_product_geometry'][field]=[]
   with self.assertRaises(Exception):c.validate_stage_plan(x)
 def test_stage_topology_mutant(self):
  x=self.contract();rows=x['stages']['F2_period_hierarchy']['modules'];rows.reverse()
  with self.assertRaises(Exception):c.validate_stage_plan(x)
 def test_each_new_resource_bound(self):
  for field in ['stage_count','workflow_aggregate_seconds','workflow_outer_runner_minutes','object_artifact_max_bytes','object_artifact_zip_max_bytes','producer_job_log_max_bytes','transport_timeout_seconds','failure_evidence_grace_seconds','maximum_parallel_jobs']:
   x=self.contract();x[field]+=1
   with self.assertRaises(Exception):c.validate_diagnostic_profile(x)
 def test_one_final_job_with_original_five_stage_partition(self):
  x=self.contract();self.assertEqual(x['workflow_job_count'],1);self.assertEqual(x['maximum_parallel_jobs'],1);self.assertEqual(x['execution_stages'],['F4_bridge_and_endpoint_joins']);self.assertEqual(x['workflow_aggregate_seconds'],x['aggregate_command_deadline_seconds']);self.assertEqual(x['workflow_outer_runner_minutes'],x['outer_timeout_minutes']);self.assertEqual([len(x['stages'][s]['modules']) for s in x['stage_order']],[186,890,1226,109,70])
 def test_native_interface_bytes_bound(self):
  inv={'mathlib':{'files':{'lib/a.so':{'sha256':'a'*64,'bytes':5}}}}
  a=c.cache_interface_identity({'A':{'sha256':'b'*64}},inv,'c'*64)
  inv['mathlib']['files']['lib/a.so']['sha256']='d'*64
  self.assertNotEqual(a,c.cache_interface_identity({'A':{'sha256':'b'*64}},inv,'c'*64))
 def test_native_link_rejected(self):
  with self.assertRaises(Exception):c.cache_interface_identity({}, {'m':{'files':{'lib/a.so':{'symlink':'../data'}}}},'x')
 def test_trace_does_not_change_interface(self):
  a=c.cache_interface_identity({}, {'m':{'files':{'a.trace':{'bytes':1}}}},'x')
  b=c.cache_interface_identity({}, {'m':{'files':{'a.trace':{'bytes':2}}}},'x')
  self.assertEqual(a,b)
class SessionPolicyTests(unittest.TestCase):
 def test_exact_official_fetch_explicitly_allowed(self):
  for pin in c.f.load_json(ROOT/'locks/dependencies.json')['packages']:
   work=Path('/fixed/work');argv=['/usr/bin/git','-c','core.hooksPath=/dev/null','-c','core.fsmonitor=false','-C',str(work/'packages'/pin['name']),'fetch','--quiet','--depth=1','--no-tags',pin['url'],pin['rev']]
   c.validate_session_policy(pin['name']+'-fetch',argv,True,work,{})
   with self.assertRaises(Exception):c.validate_session_policy(pin['name']+'-fetch',argv,False,work,{})
   argv[-1]='0'*40
   with self.assertRaises(Exception):c.validate_session_policy(pin['name']+'-fetch',argv,True,work,{})
 def test_unapproved_command_session(self):
  with self.assertRaises(Exception):c.validate_session_policy('ordinary',['/usr/bin/true'],True,Path('/work'),{})
 def test_sandbox_same_topology(self):
  a=c.sandbox(['/bin/true'],runtime=Path('/runtime'),sources=[],writable=[Path('/tmp/w')],cwd=Path('/tmp/w'),env={})
  c.validate_session_policy('bwrap-preflight',a,True,Path('/work'),{})
  a.remove('--new-session')
  with self.assertRaises(Exception):c.validate_session_policy('bwrap-preflight',a,True,Path('/work'),{})
 def test_escaped_session_receipt_rejected(self):
  r={'exit_code':0,'timed_out':False,'log_overflow':False,'memory_exceeded':False,'surviving_children':False,'process_group_empty':True,'descendants_empty':True,'escaped_descendants':True,'new_sessions_explicitly_allowed':False}
  with self.assertRaises(Exception):c.require_success_commands([r])
  r['new_sessions_explicitly_allowed']=True;c.require_success_commands([r])
 def test_timeout_and_profile_serialization(self):
  text=(ROOT/'ci/cache_diagnostic.py').read_text()
  for name in ['requested_timeout_seconds','effective_timeout_seconds','max_log_bytes','max_rss_bytes','address_space_bytes','max_created_file_bytes','allow_new_sessions']:self.assertIn(name,text)
class StageTerminalTests(unittest.TestCase):
 def test_no_premature_audit_claim(self):
  result={'conditional_C_remains_explicit':True,'final_C_proof_certified':False,'unconditional_monotile_proof_certified':False}
  c.validate_terminal_receipt(result,[],[],[],{},final=False)
  with self.assertRaises(Exception):c.validate_terminal_receipt(result,[],[],[],{'ordinary_bridges':True,'conditional_endpoints':True},final=False)
class ExportFailureTests(unittest.TestCase):
 def run_failure(self,late=False):
  with tempfile.TemporaryDirectory() as d:
   work=Path(d);(work/'evidence').mkdir();result={'status':c.STAGE_SUCCESS,'complete_evidence':True}
   clock=[1,11] if late else [1]
   with patch.object(c.time,'monotonic',side_effect=clock),patch.object(c,'export_stage',side_effect=None if late else OSError('synthetic export failure')):
    with self.assertRaises(Exception):c.finalize_stage_export(work,{},'a'*64,'F0_common',{},[],10,result)
   self.assertEqual(result['status'],'FAILED_STAGE_EXPORT_OR_DEADLINE');self.assertFalse(result['complete_evidence'])
   self.assertEqual(json.loads((work/'evidence/result.json').read_text()),result)
 def test_failed_export_rewrites_success(self):self.run_failure()
 def test_late_export_rewrites_success(self):self.run_failure(True)
 def test_interruption_before_atomic_marker_cannot_complete(self):
  with tempfile.TemporaryDirectory() as d:
   work=Path(d);(work/'evidence').mkdir();result={'status':c.STAGE_SUCCESS,'complete_evidence':True}
   with patch.object(c,'export_stage',return_value={'stage_id':'F0_common'}),patch.object(c.os,'replace',side_effect=KeyboardInterrupt('synthetic hard interruption')):
    with self.assertRaises(KeyboardInterrupt):c.finalize_stage_export(work,{},'a'*64,'F0_common',{},[],c.time.monotonic()+20,result)
   self.assertFalse((work/'evidence/stage-export.json').exists())
   self.assertTrue((work/'evidence/.stage-export.pending').exists())
 def test_auditor_quarantine_does_not_shadow_stage_plan(self):
  import ast
  tree=ast.parse((ROOT/'ci/cache_diagnostic.py').read_text())
  assigns=[n for n in ast.walk(tree) if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='stage' for t in n.targets)]
  self.assertEqual(len(assigns),1)
class HostDeadlineTests(unittest.TestCase):
 def test_host_blocked_io_interrupted(self):
  import time,signal
  before=signal.getsignal(signal.SIGALRM);watch=c.HostDeadline(time.monotonic()+0.02)
  watch.arm()
  try:
   with self.assertRaisesRegex(Exception,'host-work aggregate'):time.sleep(0.1)
  finally:watch.close()
  self.assertEqual(signal.getsignal(signal.SIGALRM),before);self.assertEqual(signal.getitimer(signal.ITIMER_REAL),(0.0,0.0))
 def test_deferred_alarm_records_expiry_and_rejects_after_command(self):
  watch=c.HostDeadline(c.time.monotonic()+10);watch.in_command=True;watch.alarm(None,None)
  self.assertTrue(watch.expired);watch.in_command=False
  with self.assertRaises(Exception):watch.check()
 def test_alarm_during_actual_pinned_cleanup_finishes_reaping(self):
  watch=c.HostDeadline(c.time.monotonic()+10);watch.in_command=True
  original=c.f.terminate_owned_processes
  def cleanup(*args,**kwargs):watch.alarm(None,None);return original(*args,**kwargs)
  with tempfile.TemporaryDirectory() as d,patch.object(c.f,'terminate_owned_processes',side_effect=cleanup):
   p=Path(d);row=c.f.run_process(['/bin/sleep','0.01'],cwd=p,env={'PATH':'/usr/bin:/bin'},timeout=2,stdout=p/'out',stderr=p/'err',max_log_bytes=1024,limits={'address_space_bytes':12*c.GIB,'rss_tree_bytes':8*c.GIB,'max_created_file_bytes':512*1024**2})
  self.assertTrue(row['process_group_empty']);self.assertTrue(row['descendants_empty']);self.assertEqual(row['exit_code'],0)
  watch.in_command=False
  with self.assertRaises(Exception):watch.check()
 def test_host_expiry_starts_one_failure_grace(self):
  watch=c.HostDeadline(c.time.monotonic()+10)
  with patch.object(c.signal,'setitimer') as timer:
   with self.assertRaises(Exception):watch.alarm(None,None)
   with self.assertRaises(Exception):watch.alarm(None,None)
   timer.assert_called_once_with(c.signal.ITIMER_REAL,5,1)
 def test_failure_grace_is_bounded_and_cannot_accept(self):
  watch=c.HostDeadline(c.time.monotonic()+10);watch.expired=True
  with patch.object(c.signal,'setitimer') as timer:
   watch.failure_receipt_grace();watch.failure_receipt_grace();timer.assert_called_once_with(c.signal.ITIMER_REAL,5,1)
  with self.assertRaises(Exception):watch.check()
 def test_original_deadline_passed_to_every_transport_operation(self):
  import ast
  tree=ast.parse((ROOT/'ci/cache_diagnostic.py').read_text());calls=[]
  for n in ast.walk(tree):
   if isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute) and isinstance(n.func.value,ast.Name) and n.func.value.id=='transport' and n.func.attr in ['Transport','extract_stage','admit_stage','write_stage']:calls.append(n)
  self.assertEqual(len(calls),4)
  for call in calls:self.assertTrue(any(k.arg=='deadline' and isinstance(k.value,ast.Name) and k.value.id in ('deadline','import_deadline') for k in call.keywords))
  restore=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='restore_stages')
  bound=next(n for n in restore.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='import_deadline' for t in n.targets))
  self.assertEqual(ast.unparse(bound.value),"min(deadline, time.monotonic() + contract['transport_timeout_seconds'])")
  for call in [n for n in ast.walk(restore) if isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute) and n.func.attr in ('Transport','extract_stage','admit_stage')]:
   self.assertTrue(any(k.arg=='deadline' and isinstance(k.value,ast.Name) and k.value.id=='import_deadline' for k in call.keywords))
class StageCollectorTests(unittest.TestCase):
 def fixture(self,work):
  m=c.load_helper('collect_evidence');e=work/'evidence';(e/'logs').mkdir(parents=True);upload=work/'object-upload';upload.mkdir()
  modules=['Fixture.A'];contract={'stages':{'F0_common':{'modules':modules,'admitted_stages':[]}},'final_stage':'F4_bridge_and_endpoint_joins','source_archive':{'sha256':'a'*64,'source_bytes':1},'owned_module_count':1,'inputs':{'src/Fixture/A.lean':{'sha256':'b'*64}},'aggregate_log_max_bytes':64*1024**2,'object_artifact_max_bytes':4*c.GIB}
  commands=[];empty=c.f.sha(b'')
  for phase in ['compile','check']:
   name=phase+'-Fixture.A';commands.append({'name':name,'exit_code':0,'timed_out':False,'log_overflow':False,'memory_exceeded':False,'surviving_children':False,'process_group_empty':True,'descendants_empty':True,'escaped_descendants':False,'new_sessions_explicitly_allowed':True,'stdout_sha256':empty,'stderr_sha256':empty})
   for stream in ['stdout','stderr']:(e/'logs'/(name+'.'+stream)).write_bytes(b'')
  objects={n:{'bytes':0,'sha256':empty} for n in c.module_outputs('Fixture.A')}
  receipt={'module':'Fixture.A','source_sha256':'b'*64,'outputs':objects,'compiler_command':0,'checker_command':1,'checker_passed':True}
  (e/'commands.jsonl').write_text(''.join(json.dumps(x)+'\n' for x in commands));(e/'owned-modules.jsonl').write_text(json.dumps(receipt)+'\n')
  values={'fresh-owned-objects.json':{'files':objects,'bytes':0},'runtime-inventory.json':{},'cached-build-inventory.json':{},'interface-identity.json':{},'imported-stages.json':[], 'source-extraction.json':{'schema':'authenticated-source-extraction-v1','archive':contract['source_archive'],'source_file_count':1,'source_bytes':1,'exact_source_tree':True,'all_source_pins_verified':True}}
  for name,value in values.items():c.write_json(e/name,value)
  result={'status':c.STAGE_SUCCESS,'complete_evidence':True,'contract_sha256':'c'*64,'conditional_C_remains_explicit':True,'final_C_proof_certified':False,'unconditional_monotile_proof_certified':False,'stage_id':'F0_common','stage_modules':modules,'admitted_stages':[],'checked_fresh_module_count':1,'checked_owned_module_count':1,'command_count':2,'complete_log_bytes':0,'raw_audits':{},'source_archive_sha256':'a'*64}
  for name,key in [('commands.jsonl','command_receipts_sha256'),('owned-modules.jsonl','owned_module_receipts_sha256'),('fresh-owned-objects.json','owned_output_inventory_sha256'),('cached-build-inventory.json','cached_build_inventory_sha256'),('runtime-inventory.json','runtime_inventory_sha256'),('source-extraction.json','source_extraction_receipt_sha256'),('interface-identity.json','interface_identity_sha256'),('imported-stages.json','imported_stages_sha256')]:result[key]=c.f.file_sha(e/name)
  c.write_json(e/'result.json',result);(upload/'stage.tar').write_bytes(b'fixture-only');(upload/'descriptor.json').write_bytes(b'{}')
  c.write_json(e/'stage-export.json',{'stage_id':'F0_common','contract_sha256':'c'*64,'stage_tar_bytes':12,'stage_tar_sha256':c.f.file_sha(upload/'stage.tar'),'descriptor_sha256':c.f.file_sha(upload/'descriptor.json')})
  return m,e,contract,result
 def test_stage_receipts_plus_finalized_payload(self):
  with tempfile.TemporaryDirectory() as d:
   m,e,contract,result=self.fixture(Path(d));m.verify_complete(e,contract,'c'*64)
 def test_missing_completion_marker_rejected(self):
  with tempfile.TemporaryDirectory() as d:
   m,e,contract,result=self.fixture(Path(d));(e/'stage-export.json').unlink()
   m.verify_complete(e,contract,'c'*64,require_export=False)
   with self.assertRaises(Exception):m.verify_complete(e,contract,'c'*64)
 def test_nonfinal_cannot_claim_whole_replay(self):
  with tempfile.TemporaryDirectory() as d:
   m,e,contract,result=self.fixture(Path(d));result['status']=c.SUCCESS;c.write_json(e/'result.json',result)
   with self.assertRaises(Exception):m.verify_complete(e,contract,'c'*64)
 def test_changed_payload_rejected(self):
  with tempfile.TemporaryDirectory() as d:
   m,e,contract,result=self.fixture(Path(d));(Path(d)/'object-upload/stage.tar').write_bytes(b'altered')
   with self.assertRaises(Exception):m.verify_complete(e,contract,'c'*64)
if __name__=='__main__':unittest.main()
