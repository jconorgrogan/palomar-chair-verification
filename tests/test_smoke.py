"""Inert controls only: all subprocess, socket, and network calls are forbidden."""
import copy, importlib.util, json, os, socket, subprocess, sys, tempfile, unittest, urllib.request
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def forbidden(*args,**kwargs):raise AssertionError('external/native operation forbidden in inert test')
subprocess.Popen=forbidden;subprocess.run=forbidden;os.system=forbidden
socket.socket=forbidden;socket.create_connection=forbidden;urllib.request.urlopen=forbidden
spec=importlib.util.spec_from_file_location('smoke_test_api',ROOT/'visibility_smoke.py');d=importlib.util.module_from_spec(spec);sys.modules[spec.name]=d;spec.loader.exec_module(d)
class Clock:
 def check(self):pass
class Tests(unittest.TestCase):
 @classmethod
 def setUpClass(cls):cls.c=d.f.load_json(ROOT/'smoke-contract.json')
 def reject(self,func,*args,**kwargs):
  with self.assertRaises((ValueError,RuntimeError,KeyError)):func(*args,**kwargs)
 def safe(self):
  return {'exit_code':0,'timed_out':False,'log_overflow':False,'memory_exceeded':False,'surviving_children':False,'process_group_empty':True,'descendants_empty':True,'escaped_descendants':False,'new_sessions_explicitly_allowed':True}
 def test_inactive_contract_and_all_pins(self):
  d.validate_contract(self.c);d.validate_inputs(self.c);self.reject(d.validate_contract,self.c,reviewed=True)
 def test_profile_mutations(self):
  for field in d.LIMITS:
   c=copy.deepcopy(self.c);c['limits'][field]+=1;self.reject(d.validate_contract,c)
  for field in ['restore_project_objects','full_official_verification_claimed']:
   c=copy.deepcopy(self.c);c[field]=True;self.reject(d.validate_contract,c)
 def test_fresh_source_extraction_and_graph(self):
  with tempfile.TemporaryDirectory() as td:
   work=Path(td);receipt=d.a.extract_owned_sources(ROOT/'owned-sources.tar.gz',work/'source-input',self.c)
   self.assertEqual(receipt['source_file_count'],174);owned=d.validate_graph(self.c,work);self.assertEqual(len(owned),174)
   c=copy.deepcopy(self.c);c['target_closures'][d.TARGETS[3]].pop(0);self.reject(d.validate_graph,c,work)
   c=copy.deepcopy(self.c);c['modules'][0]['ordered_imports']=['Wrong.Module'];self.reject(d.validate_graph,c,work)
 def test_all_native_specs_are_finite_and_fixed(self):
  names=d.command_order(self.c);self.assertEqual(len(names),394);self.assertEqual(len(names),len(set(names)))
  work=Path('/tmp/inert-visibility-fixture')
  for name in names:
   spec=d.command_spec(self.c,work,name,['Mathlib.Tactic.Linarith']);row={**spec,**self.safe(),'limits':{k:d.LIMITS[k] for k in ['address_space_bytes','rss_tree_bytes','max_created_file_bytes']},'max_log_bytes':1024**2,'effective_timeout_seconds':spec['requested_timeout_seconds']}
   row['new_sessions_explicitly_allowed']=spec['allowed_sessions'];d.validate_command_spec(self.c,work,row,['Mathlib.Tactic.Linarith'])
   mutated=copy.deepcopy(row);mutated['argv'].append('--unsafe');self.reject(d.validate_command_spec,self.c,work,mutated,['Mathlib.Tactic.Linarith'])
   if name.startswith(('compile-','check-')):self.assertNotIn('--share-net',spec['argv'])
  for m in d.TARGETS:
   spec=d.command_spec(self.c,work,'compile-original-'+m)
   self.assertTrue(spec['env']['LEAN_PATH'].split(':')[0].endswith('/original-prerequisites/'+m));self.assertNotIn(str(work/'objects'),spec['argv'])
 def test_safety_types_and_flags(self):
  self.assertTrue(d.clean_command(self.safe()))
  for key in self.safe():
   row=self.safe();row[key]='false';self.reject(d.clean_command,row)
  for key in ['timed_out','log_overflow','memory_exceeded','surviving_children']:
   row=self.safe();row[key]=True;self.assertFalse(d.clean_command(row))
  for key in ['process_group_empty','descendants_empty']:
   row=self.safe();row[key]=False;self.assertFalse(d.clean_command(row))
 def test_capture_regular_bounded_no_alias(self):
  with tempfile.TemporaryDirectory() as td:
   p=Path(td)/'capture';p.write_bytes(b'ok');self.assertEqual(d.read_capture(p,2,Clock()),b'ok');self.reject(d.read_capture,p,1,Clock())
   q=Path(td)/'alias';q.symlink_to(p);self.reject(d.read_capture,q,2,Clock());q.unlink();os.link(p,q);self.reject(d.read_capture,p,2,Clock())
 def test_original_exact_diagnostics(self):
  for module,expected in d.EXPECTED_UNKNOWN.items():
   text=''.join('/tmp/'+module.replace('.','/')+f'.lean:{line}:{col or 3}: error: Unknown identifier `{name}`\n' for line,col,name in expected)
   d.failure_diagnostics(module,text)
   for bad in ['',text+text,text.replace('Unknown identifier','type mismatch'),text.replace('.lean:', '.lean:1')]:self.reject(d.failure_diagnostics,module,bad)
  module=d.TARGETS[1];text='/tmp/'+module.replace('.','/')+'.lean:34:15: error: Unknown identifier `translated_contracting`\n'
  for (line,col),message in d.CASCADE.items():text+='/tmp/'+module.replace('.','/')+f'.lean:{line}:{col}: error: {message}\n'
  self.assertEqual(len(d.failure_diagnostics(module,text)['authenticated_cascade_headers']),3)
 def test_unexpected_evidence_rejected(self):
  with tempfile.TemporaryDirectory() as td:
   work=Path(td);(work/'evidence').mkdir();(work/'logs').mkdir();(work/'native-captures').mkdir()
   (work/'evidence/secret.txt').write_text('unexpected');self.reject(d.validate_capture_collection,self.c,work,Clock())
 def test_unreceipted_native_is_never_read(self):
  with tempfile.TemporaryDirectory() as td:
   work=Path(td);(work/'evidence').mkdir();(work/'logs').mkdir();(work/'native-captures').mkdir()
   (work/'native-captures/bwrap-preflight.stdout').symlink_to('/definitely/not/read')
   # Dangling unadmitted capture still must be described, never opened.
   omissions=d.validate_capture_collection(self.c,work,Clock())
   self.assertEqual(len(omissions),1)
 def test_prepopulated_evidence_log_rejected(self):
  with tempfile.TemporaryDirectory() as td:
   work=Path(td)
   for n in ['evidence/logs','logs','native-captures']:(work/n).mkdir(parents=True)
   (work/'evidence/logs/bwrap-preflight.stdout').write_text('unadmitted')
   self.reject(d.validate_capture_collection,self.c,work,Clock())
 def test_unsafe_capture_not_read(self):
  with tempfile.TemporaryDirectory() as td:
   work=Path(td)
   for n in ['evidence','logs','native-captures']:(work/n).mkdir()
   spec=d.command_spec(self.c,work,'bwrap-preflight');r={**spec,**self.safe(),'limits':{k:d.LIMITS[k] for k in ['address_space_bytes','rss_tree_bytes','max_created_file_bytes']},'max_log_bytes':1024**2,'effective_timeout_seconds':30,'capture_status':'excluded_unsafe_native_result'}
   r['timed_out']=True;(work/'evidence/commands.jsonl').write_text(json.dumps(r)+'\n')
   (work/'native-captures/bwrap-preflight.stdout').symlink_to('/definitely/not/read')
   self.assertEqual(len(d.validate_capture_collection(self.c,work,Clock())),1)
 def test_synthetic_success_and_terminal_mutations(self):
  spec=importlib.util.spec_from_file_location('synthetic_success',ROOT/'tests/inert_success_fixture.py');fixture=importlib.util.module_from_spec(spec);spec.loader.exec_module(fixture)
  with tempfile.TemporaryDirectory() as td:
   data=fixture.make(d,self.c,Path(td));old=d.a.RUNTIME_INVENTORY_SHA;d.a.RUNTIME_INVENTORY_SHA=data['synthetic_runtime_sha']
   try:
    d.verify_success(self.c,data['contract_sha'],Path(td)/'evidence',Path(td))
    d.validate_capture_collection(self.c,Path(td),Clock())
    result=Path(td)/'evidence/result.json';before=result.read_bytes();row=d.f.parse_json(before);row['checked_owned_module_count']=173;result.write_bytes(d.f.json_bytes(row))
    self.reject(d.verify_success,self.c,data['contract_sha'],Path(td)/'evidence',Path(td));result.write_bytes(before)
    log=Path(td)/'evidence/logs'/('check-'+self.c['module_order'][-1]+'.stdout');log.write_text('changed')
    self.reject(d.verify_success,self.c,data['contract_sha'],Path(td)/'evidence',Path(td))
   finally:d.a.RUNTIME_INVENTORY_SHA=old
 def test_actual_loop_with_inert_seams(self):
  spec=importlib.util.spec_from_file_location('inert_loop',ROOT/'tests/inert_loop_fixture.py');fixture=importlib.util.module_from_spec(spec);spec.loader.exec_module(fixture)
  with tempfile.TemporaryDirectory() as td:
   result=fixture.run(d,self.c,Path(td));self.assertEqual(result['native_calls'],394)
 def test_missing_result_cannot_pass(self):
  with tempfile.TemporaryDirectory() as td:
   work=Path(td);(work/'result.json').write_text(json.dumps({'status':'INCOMPLETE'}));self.reject(d.verify_success,self.c,'0'*64,work,work)
if __name__=='__main__':unittest.main()
