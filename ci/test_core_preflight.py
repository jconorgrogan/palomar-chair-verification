import copy,hashlib,importlib.util,json,os,sys,tempfile,unittest
from pathlib import Path
from unittest.mock import patch
ROOT=Path(__file__).resolve().parents[1]
def load(name,path):
 spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);sys.modules[name]=m;spec.loader.exec_module(m);return m
p=load('core_preflight_test',ROOT/'ci/core_preflight.py');p.f=load('fresh_stage',ROOT/'ci/fresh_stage.py');p.b=load('boundary_test',ROOT/'ci/boundary.py');p.b.f=p.f
C=json.loads((ROOT/'contract.json').read_text())
class Tests(unittest.TestCase):
 def setUp(self):
  self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup);self.work=Path(self.temp.name)
  for n in ['home','tmp','logs','evidence','quarantine','objects/higher','objects/uniform','runtime/lib/lean']:(self.work/n).mkdir(parents=True)
  self.runtime=self.work/'runtime';self.specs=p.specs(C,self.work,self.runtime);self.outputs={x:{} for x in p.FAMILIES};self.commands=[]
  self.watchdog=type('Watchdog',(),{'check':lambda self:None})()
 def record(self,spec):
  r=dict(spec,exit_code=0,timed_out=False,log_overflow=False,memory_exceeded=False,surviving_children=False,process_group_empty=True,descendants_empty=True,escaped_descendants=True,new_sessions_explicitly_allowed=True,effective_timeout_seconds=spec['requested_timeout_seconds'],timeout_seconds=spec['requested_timeout_seconds'],limits={'address_space_bytes':12*p.GIB,'rss_tree_bytes':8*p.GIB,'max_created_file_bytes':512*1024**2},max_log_bytes=1024**2)
  for stream in ['stdout','stderr']:
   path=self.work/'logs'/(spec['name']+'.'+stream)
   if not path.exists():path.write_bytes(b'')
   r[stream+'_sha256']=p.sha(path)
  return r
 def command(self,name,argv,**kw):
  spec=self.specs[len(self.commands)];self.assertEqual(spec['name'],name);self.assertEqual(spec['argv'],list(map(str,argv)))
  if name.startswith('compile-'):
   module=name.removeprefix('compile-');staging=self.work/'quarantine'/module
   for suffix in p.b.SUFFIXES:(staging/(module+suffix)).write_bytes((module+suffix).encode())
   family=next(x for x,names in p.FAMILIES.items() if module in names)
   if module==p.FAMILIES[family][1]:
    row=C['controls'][family];(self.work/'logs'/(name+'.stdout')).write_text('\n'.join(['PASS '+x for x in row['pass_labels']]+[row['success_marker']])+'\n')
  self.commands.append(self.record(spec));return self.work/'logs'/(name+'.stdout'),True
 def run_pairs(self,cmd=None):
  self.commands=[self.record(s) for s in self.specs[:2]]
  with patch.object(p.shutil,'disk_usage',return_value=type('Disk',(),{'free':8*p.GIB})()):p.run_pairs(C,self.work,self.runtime,self.specs,self.commands,self.outputs,cmd or self.command,self.watchdog)
 def final(self):
  with patch.object(p,'validate_inputs'):p.validate_final(C,self.work,self.commands,self.outputs,self.runtime)
 def test_exact_profile(self):p.profile(C)
 def test_four_pair_fixture(self):self.run_pairs();self.final();self.assertEqual(sum(map(len,self.outputs.values())),28)
 def test_exact_spec_sequence(self):self.assertEqual([s['name'] for s in self.specs],[ 'bwrap-preflight','read-only-committed-root-preflight', *[phase+'-'+m for names in p.FAMILIES.values() for m in names for phase in ['compile','check']]])
 def test_family_roots_are_separate(self):
  for s in self.specs[2:]:
   family='higher' if 'Higher' in s['name'] else 'uniform';env=s['env'];self.assertEqual(env['LEAN_PATH'],str(self.work/'objects'/family)+':'+str(self.runtime/'lib/lean'));self.assertNotIn(str(self.work/'quarantine'),env['LEAN_PATH'])
 def test_no_network_sandbox(self):self.assertTrue(all('--share-net' not in s['argv'] and '--unshare-all' in s['argv'] for s in self.specs))
 def test_control_markers_pass(self):
  for row in C['controls'].values():p.check_markers('\n'.join(['PASS '+x for x in row['pass_labels']]+[row['success_marker']]),row)
 def test_profile_mutations(self):
  for key in ['aggregate_seconds','job_timeout_minutes','compile_seconds','check_seconds','lean_heap_mib','address_space_bytes','rss_tree_bytes','output_max_bytes','expected_command_count']:
   with self.subTest(key=key):
    c=copy.deepcopy(C);c[key]+=1
    with self.assertRaises(RuntimeError):p.profile(c)
 def test_false_scope(self):
  for key in ['research_theorem_claimed','mathlib_cache_used','research_objects_loaded']:
   c=copy.deepcopy(C);c[key]=True
   with self.assertRaises(RuntimeError):p.profile(c)
 def test_command_mutations(self):
  good=self.record(self.specs[2]);mutations={'argv':good['argv']+['-DElab.async=false'],'env':{},'cwd':'/tmp/other','requested_timeout_seconds':181,'allow_new_sessions':False,'limits':{},'max_log_bytes':1,'new_sessions_explicitly_allowed':False,'effective_timeout_seconds':181,'timeout_seconds':1,'exit_code':1,'timed_out':True,'log_overflow':True,'memory_exceeded':True,'surviving_children':True,'process_group_empty':False,'descendants_empty':False}
  for key,value in mutations.items():
   with self.subTest(key=key):
    r=copy.deepcopy(good);r[key]=value
    with self.assertRaises(RuntimeError):p.accept_command(r,self.specs[2],C)
 def test_failed_compile_cannot_admit_or_check(self):
  calls=[]
  def bad(name,*args,**kw):calls.append(name);raise RuntimeError('actual compile rejection')
  with self.assertRaises(RuntimeError):self.run_pairs(bad)
  self.assertEqual(calls,['compile-AuditHigherPhysicalEndpoints']);self.assertEqual(self.outputs,{'higher':{},'uniform':{}});self.assertEqual(list((self.work/'objects/higher').iterdir()),[])
 def test_checker_mutation_detected(self):
  def bad(name,*args,**kw):
   result=self.command(name,*args,**kw)
   if name=='check-AuditHigherPhysicalEndpoints':
    path=self.work/'objects/higher/AuditHigherPhysicalEndpoints.olean';path.chmod(0o644);path.write_bytes(b'changed')
   return result
  with self.assertRaises(Exception):self.run_pairs(bad)
  self.assertEqual(self.commands[-1]['name'],'check-AuditHigherPhysicalEndpoints')
 def test_later_family_mutation_detected(self):
  def bad(name,*args,**kw):
   result=self.command(name,*args,**kw)
   if name=='check-UniformInspectorControl':
    path=self.work/'objects/higher/HigherInspectorControl.olean';path.chmod(0o644);path.write_bytes(b'changed')
   return result
  self.run_pairs(bad)
  with self.assertRaises(Exception):self.final()
 def test_missing_companion_rejects(self):
  def bad(name,*args,**kw):
   result=self.command(name,*args,**kw)
   if name=='compile-AuditHigherPhysicalEndpoints':(self.work/'quarantine/AuditHigherPhysicalEndpoints/AuditHigherPhysicalEndpoints.c').unlink()
   return result
  with self.assertRaises(Exception):self.run_pairs(bad)
  self.assertEqual(len(self.commands),3)
 def test_unlisted_companion_rejects(self):
  def bad(name,*args,**kw):
   result=self.command(name,*args,**kw)
   if name=='compile-AuditHigherPhysicalEndpoints':(self.work/'quarantine/AuditHigherPhysicalEndpoints/extra.olean').write_bytes(b'bad')
   return result
  with self.assertRaises(Exception):self.run_pairs(bad)
 def test_output_symlink_rejects(self):
  def bad(name,*args,**kw):
   result=self.command(name,*args,**kw)
   if name=='compile-AuditHigherPhysicalEndpoints':
    target=self.work/'quarantine/AuditHigherPhysicalEndpoints/AuditHigherPhysicalEndpoints.c';target.unlink();target.symlink_to('AuditHigherPhysicalEndpoints.olean')
   return result
  with self.assertRaises(Exception):self.run_pairs(bad)
 def test_empty_namespace_extra_rejects(self):
  self.run_pairs();(self.work/'objects/higher/Unlisted').mkdir()
  with self.assertRaises(Exception):self.final()
 def test_command_reorder_rejects(self):
  self.run_pairs();self.commands[2],self.commands[3]=self.commands[3],self.commands[2]
  with self.assertRaises(Exception):self.final()
 def test_missing_command_rejects(self):
  self.run_pairs();self.commands.pop()
  with self.assertRaises(Exception):self.final()
 def test_log_mutation_rejects(self):
  self.run_pairs();(self.work/'logs/check-HigherInspectorControl.stdout').write_bytes(b'changed')
  with self.assertRaises(Exception):self.final()
 def test_missing_control_marker(self):
  for row in C['controls'].values():
   with self.assertRaises(RuntimeError):p.check_markers('\n'.join('PASS '+x for x in row['pass_labels']),row)
 def test_extra_control_label(self):
  for row in C['controls'].values():
   with self.assertRaises(RuntimeError):p.check_markers('\n'.join(['PASS '+x for x in row['pass_labels']]+['PASS unlisted',row['success_marker']]),row)
 def test_reordered_control_labels(self):
  for row in C['controls'].values():
   with self.assertRaises(RuntimeError):p.check_markers('\n'.join(['PASS '+x for x in reversed(row['pass_labels'])]+[row['success_marker']]),row)
 def test_duplicate_terminal_marker(self):
  for row in C['controls'].values():
   with self.assertRaises(RuntimeError):p.check_markers('\n'.join(['PASS '+x for x in row['pass_labels']]+[row['success_marker']]*2),row)
 def test_endpoint_marker_rejected(self):
  row=C['controls']['higher']
  with self.assertRaises(RuntimeError):p.check_markers('\n'.join(['PASS '+x for x in row['pass_labels']]+[row['success_marker'],'HIGHER_PHYSICAL_ENDPOINT_AUDIT_PASSED']),row)
 def test_low_disk_stops_before_compile(self):
  self.commands=[self.record(s) for s in self.specs[:2]]
  with patch.object(p.shutil,'disk_usage',return_value=type('Disk',(),{'free':0})()),self.assertRaises(RuntimeError):p.run_pairs(C,self.work,self.runtime,self.specs,self.commands,self.outputs,self.command,self.watchdog)
  self.assertEqual(len(self.commands),2)
 def test_pair_deadline_stops(self):
  self.watchdog.check=lambda:(_ for _ in ()).throw(RuntimeError('expired'))
  with self.assertRaises(RuntimeError):self.run_pairs()
  self.assertEqual(len(self.commands),2)
 def test_combined_output_cap(self):
  c=copy.deepcopy(C);c['output_max_bytes']=1;self.commands=[self.record(s) for s in self.specs[:2]]
  with patch.object(p.shutil,'disk_usage',return_value=type('Disk',(),{'free':8*p.GIB})()),self.assertRaises(Exception):p.run_pairs(c,self.work,self.runtime,self.specs,self.commands,self.outputs,self.command,self.watchdog)
 def test_collection_inventory(self):
  (self.work/'evidence/result.json').write_bytes(b'{}');p.collect(self.work,C);x=json.loads((self.work/'evidence/collection.json').read_text());self.assertEqual(x['files']['result.json']['bytes'],2)
 def test_collection_symlink_rejects(self):
  (self.work/'evidence/link').symlink_to(self.work/'tmp')
  with self.assertRaises(RuntimeError):p.collect(self.work,C)
 def test_collection_cap_includes_manifest(self):
  (self.work/'evidence/result.json').write_bytes(b'{}');c=copy.deepcopy(C);c['evidence_max_bytes']=1
  with self.assertRaises(RuntimeError):p.collect(self.work,c)
 def test_input_exactness(self):p.validate_inputs(C)
 def sealing(self,watchdog=None):
  self.run_pairs();self.watchdog.close=lambda:None
  with patch.object(p,'validate_inputs'),patch.object(p,'verify_runtime'),patch.object(p.shutil,'disk_usage',return_value=type('Disk',(),{'free':8*p.GIB})()):
   p.finalize_success(C,self.work,self.commands,self.outputs,self.runtime,{}, {'status':'INCOMPLETE'},'a'*64,watchdog or self.watchdog)
 def test_completion_marker_binds_final_receipts(self):
  self.sealing();e=self.work/'evidence';marker=json.loads((e/'completion.json').read_text());self.assertEqual(marker['result_sha256'],p.sha(e/'result.json'));self.assertEqual(marker['collection_sha256'],p.sha(e/'collection.json'));self.assertFalse((e/'.completion.pending').exists())
 def test_final_deadline_before_marker_rejects(self):
  count=[0]
  def check():
   count[0]+=1
   if count[0]==3:raise RuntimeError('deadline before marker')
  wd=type('Watchdog',(),{'check':staticmethod(check),'close':lambda self:None})()
  with self.assertRaises(RuntimeError):self.sealing(wd)
  self.assertFalse((self.work/'evidence/completion.json').exists())
 def test_collection_failure_leaves_no_completion(self):
  with patch.object(p,'collect',side_effect=RuntimeError('collection failure')),self.assertRaises(RuntimeError):self.sealing()
  self.assertFalse((self.work/'evidence/completion.json').exists())
 def test_interrupted_marker_rename_rejects(self):
  with patch.object(p.os,'replace',side_effect=RuntimeError('interruption')),self.assertRaises(RuntimeError):self.sealing()
  self.assertFalse((self.work/'evidence/completion.json').exists())
 def test_runtime_final_mutation_stops_seal(self):
  self.run_pairs()
  with patch.object(p,'validate_inputs'),patch.object(p,'verify_runtime',side_effect=RuntimeError('runtime changed')),self.assertRaises(RuntimeError):p.finalize_success(C,self.work,self.commands,self.outputs,self.runtime,{}, {},'a'*64,self.watchdog)
  self.assertFalse((self.work/'evidence/completion.json').exists())
 def test_source_final_mutation_stops_seal(self):
  self.run_pairs()
  with patch.object(p,'validate_inputs',side_effect=RuntimeError('source changed')),self.assertRaises(RuntimeError):p.finalize_success(C,self.work,self.commands,self.outputs,self.runtime,{}, {},'a'*64,self.watchdog)
  self.assertFalse((self.work/'evidence/completion.json').exists())
 def test_exact_boundary_function_copy(self):
  import ast
  source=(ROOT/'ci/boundary.py').read_text();tree=ast.parse(source);actual={n.name:hashlib.sha256(ast.get_source_segment(source,n).encode()).hexdigest() for n in tree.body if isinstance(n,(ast.FunctionDef,ast.ClassDef))};self.assertEqual(actual,json.loads((ROOT/'ci/boundary-lineage.json').read_text())['functions'])
if __name__=='__main__':unittest.main()
