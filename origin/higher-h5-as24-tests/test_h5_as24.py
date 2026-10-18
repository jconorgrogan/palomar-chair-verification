"""AS24 source-only controls; permanent guards must precede selected imports."""
import ast,copy,hashlib,json,sys,tempfile,time,types,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'ci'))
import cache_diagnostic as a
h=a.higher;RAW='audit-AuditHigherPhysicalEndpoints';FIELD='higher_h5_raw_auditor_address_space_gib'
class H5AS24Tests(unittest.TestCase):
 def c(self):return a.f.load_json(ROOT/'contract.json')
 def old(self):return a.f.load_json(ROOT/'origin/higher-h5-as12-contract.json')
 def expected(self,work,c):
  return {'producer_work':str(work),'runtime':work/'runtime','contract':c,'dependency_pins':a.f.load_json(ROOT/'locks/dependencies.json')['packages'],'cache_rows':{},'cache_search':[],'stage_rows':[],'stage_id':'H5_higher_assembly'}
 def test_exact_profile_and_raw_selection(self):
  c=self.c();a.validate_diagnostic_profile(c);self.assertEqual(h.command_address_space_bytes(c,RAW,a),24*a.GIB)
  self.assertEqual(c[FIELD],24);self.assertEqual(c['diagnostic_rss_gib'],8);self.assertFalse(c['higher_h5_retry']['all_per_command_and_per_job_caps_unchanged'])
 def test_previous_active_contract_is_unchanged(self):
  self.assertEqual(a.f.file_sha(ROOT/'origin/higher-h5-as12-contract.json'),'aa6ae7a64d5e8b00e358887ad5d085127b1e318bd8b291ef7ba8ac59886c9369')
  a.validate_diagnostic_profile(self.old());self.assertEqual(h.command_address_space_bytes(self.old(),RAW,a),12*a.GIB)
 def test_original_producer_contracts_keep_as12(self):
  for path in ['producer-contract.json','continuation-producer-contract.json','higher-producer-contract.json','higher-h0-h3-producer-contract.json','higher-h5-as12-contract.json']:
   c=a.f.load_json(ROOT/'origin'/path)
   for name in [RAW,'compile-auditor-AuditHigherPhysicalEndpoints','check-ClarkSeed.PhysicalDimensions','cache-get']:
    self.assertEqual(h.command_address_space_bytes(c,name,a),12*a.GIB)
 def test_all_reconstructed_other_specs_keep_as12(self):
  with tempfile.TemporaryDirectory() as d:
   work=Path(d);current=a.transport.command_specs(self.expected(work,self.c()),a);old=a.transport.command_specs(self.expected(work,self.old()),a)
   self.assertEqual(len(current),len(old));self.assertEqual(sum('address_space_bytes' in r for r in current),1)
   for new,previous in zip(current,old):
    expected=24*a.GIB if new['name']==RAW else 12*a.GIB
    self.assertEqual(h.command_address_space_bytes(self.c(),new['name'],a),expected)
    self.assertEqual(new.get('address_space_bytes',12*a.GIB),expected)
    self.assertEqual(previous.get('address_space_bytes',12*a.GIB),12*a.GIB)
    self.assertEqual({k:v for k,v in new.items() if k!='address_space_bytes'},previous)
 def test_nearby_command_names_cannot_receive_as24(self):
  for name in ['audit-AuditHigherPhysicalEndpoints-extra','audit-AuditOrdinaryBridges','audit-AuditConditionalEndpoints','compile-auditor-AuditHigherPhysicalEndpoints','check-auditor-AuditHigherPhysicalEndpoints','compile-ClarkSeed.PhysicalDimensions','check-ClarkSeed.PhysicalDimensions','cache-bootstrap','cache-get']:
   self.assertEqual(h.command_address_space_bytes(self.c(),name,a),12*a.GIB)
 def test_profile_does_not_broaden_old_higher_stage(self):
  c=a.f.load_json(ROOT/'origin/higher-producer-contract.json');c[FIELD]=24
  with self.assertRaises(Exception):a.validate_diagnostic_profile(c)
 def test_scope_without_fixed_field_is_rejected(self):
  c=self.c();del c[FIELD]
  with self.assertRaises(Exception):a.validate_diagnostic_profile(c)
 def test_scope_and_provenance_mutations_are_rejected(self):
  for key,value in [('raw_auditor_command','audit-AuditOrdinaryBridges'),('rss_tree_bytes',16*a.GIB),('other_commands_address_space_bytes',24*a.GIB),('previous_contract_sha256','0'*64),('failed_h5_objects_reused',True)]:
   c=self.c();c['higher_h5_as24'][key]=value
   with self.assertRaises(Exception):a.validate_diagnostic_profile(c)
 def test_all_prior_caps_and_sources_remain_unchanged(self):
  c=self.c();old=self.old()
  for key in old:
   if any(t in key for t in ['timeout','deadline','max_bytes','_heap_','_rss_','minimum_','failure_evidence_grace']):self.assertEqual(c[key],old[key],key)
  for key in ['stages','source_archive','origin_lock','producer_contracts','native_h0_h3_origin_lock','module_checker_timeout_exceptions','execution_stages','locked_origin_stages']:
   self.assertEqual(c[key],old[key],key)
  for path,pin in old['inputs'].items():
   if path.startswith(('src/','auditors/','locks/')):self.assertEqual(c['inputs'][path],pin,path)
 def fixture(self,root,c):
  e=root/'evidence';(e/'logs').mkdir(parents=True);expected=self.expected(root,c);specs=a.transport.command_specs(expected,a);rows=[]
  for spec in specs:
   limits={'address_space_bytes':spec.get('address_space_bytes',12*a.GIB),'rss_tree_bytes':8*a.GIB,'max_created_file_bytes':512*1024**2}
   row={**spec,'exit_code':0,'timed_out':False,'log_overflow':False,'memory_exceeded':False,'surviving_children':False,'process_group_empty':True,'descendants_empty':True,'escaped_descendants':False,'new_sessions_explicitly_allowed':spec['allow_new_sessions'],'effective_timeout_seconds':spec['requested_timeout_seconds'],'timeout_seconds':spec['requested_timeout_seconds'],'address_space_bytes':limits['address_space_bytes'],'max_created_file_bytes':limits['max_created_file_bytes'],'max_log_bytes':c['per_command_log_max_bytes'],'limits':limits,'elapsed_seconds':0.1,'peak_sampled_tree_rss_bytes':1234}
   for stream in ['stdout','stderr']:
    p=e/'logs'/(spec['name']+'.'+stream);p.write_bytes(b'');row[stream+'_sha256']=hashlib.sha256(b'').hexdigest()
   rows.append(row)
  return rows,e,expected
 def test_new_and_original_full_serialized_command_profiles_pass(self):
  for c in [self.c(),self.old()]:
   with tempfile.TemporaryDirectory() as d:
    args=self.fixture(Path(d),c);self.assertEqual(a.transport.validate_commands(*args,a),0)
 def test_new_raw_as12_receipt_is_rejected(self):
  with tempfile.TemporaryDirectory() as d:
   rows,e,expected=self.fixture(Path(d),self.c());rows[-1]['address_space_bytes']=12*a.GIB;rows[-1]['limits']['address_space_bytes']=12*a.GIB
   with self.assertRaises(Exception):a.transport.validate_commands(rows,e,expected,a)
 def test_old_raw_as24_receipt_is_rejected(self):
  with tempfile.TemporaryDirectory() as d:
   rows,e,expected=self.fixture(Path(d),self.old());rows[-1]['address_space_bytes']=24*a.GIB;rows[-1]['limits']['address_space_bytes']=24*a.GIB
   with self.assertRaises(Exception):a.transport.validate_commands(rows,e,expected,a)
 def test_other_as24_receipt_is_rejected(self):
  with tempfile.TemporaryDirectory() as d:
   rows,e,expected=self.fixture(Path(d),self.c());rows[0]['address_space_bytes']=24*a.GIB;rows[0]['limits']['address_space_bytes']=24*a.GIB
   with self.assertRaises(Exception):a.transport.validate_commands(rows,e,expected,a)
 def test_serialized_nested_limit_mismatch_is_rejected(self):
  with tempfile.TemporaryDirectory() as d:
   rows,e,expected=self.fixture(Path(d),self.c());rows[-1]['limits']['address_space_bytes']=12*a.GIB
   with self.assertRaises(Exception):a.transport.validate_commands(rows,e,expected,a)
 def test_exact_command_closure_sends_and_records_only_selected_as24(self):
  tree=ast.parse((ROOT/'ci/cache_diagnostic.py').read_text());run=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='main');command=next(n for n in run.body if isinstance(n,ast.FunctionDef) and n.name=='command')
  with tempfile.TemporaryDirectory() as d:
   work=Path(d);(work/'logs').mkdir();(work/'evidence').mkdir();calls=[];rows=[];c=self.c()
   def fake_process(argv,**kw):
    calls.append(copy.deepcopy(kw['limits']));kw['stdout'].write_bytes(b'');kw['stderr'].write_bytes(b'')
    return {'exit_code':0,'timed_out':False,'log_overflow':False,'memory_exceeded':False,'surviving_children':False,'process_group_empty':True,'descendants_empty':True,'escaped_descendants':False,'new_sessions_explicitly_allowed':kw['allow_new_sessions']}
   f=types.SimpleNamespace(**vars(a.f));f.run_process=fake_process
   watchdog=types.SimpleNamespace(in_command=False,expired=False,check=lambda:None,failure_receipt_grace=lambda:None)
   env={'__name__':a.__name__,'GIB':a.GIB,'f':f,'higher':h,'sys':sys,'time':time,'json':json,'Path':Path,'work':work,'runtime':work/'runtime','contract':c,'commands':rows,'deadline':time.monotonic()+10000,'watchdog':watchdog,'result':{'complete_log_bytes':0},'write_json':a.write_json,'safe_env':a.safe_env,'validate_session_policy':a.validate_session_policy}
   exec(compile(ast.Module(body=[command],type_ignores=[]),'<exact-command-closure>','exec'),env)
   specs=a.transport.command_specs(self.expected(work,c),a)
   for spec in [specs[0],specs[-2],specs[-1]]:
    env['command'](spec['name'],spec['argv'],seconds=spec['requested_timeout_seconds'],rss=spec['max_rss_bytes'],allowed_sessions=spec['allow_new_sessions'])
   self.assertEqual([r['address_space_bytes'] for r in rows],[12*a.GIB,12*a.GIB,24*a.GIB]);self.assertEqual(calls,[r['limits'] for r in rows])
   for r in rows:self.assertEqual(r['limits']['rss_tree_bytes'],8*a.GIB);self.assertEqual(r['max_created_file_bytes'],512*1024**2)
   persisted=[json.loads(line) for line in (work/'evidence/commands.jsonl').read_text().splitlines()];self.assertEqual(persisted,rows)
 def test_failed_run_observation_and_no_payload_reuse(self):
  result=a.f.load_json(ROOT/'origin/failed-h5-as12-result.json');last=a.f.load_json(ROOT/'origin/failed-h5-as12-last-command.json');obs=a.f.load_json(ROOT/'origin/failed-h5-as12-ir-observation.json')
  self.assertEqual(result['run_id'],'39150122418');self.assertEqual(result['workflow_commit'],'31143d79da8970f60dec6227cb97fd5470321209')
  self.assertEqual(last['max_sampled_process_virtual_size_bytes'],12*a.GIB);self.assertEqual(last['address_space_bytes'],12*a.GIB)
  self.assertEqual(last['peak_sampled_tree_rss_bytes'],6176534528);self.assertEqual(last['exit_code'],1)
  self.assertTrue(obs['matches_expected_h0']);self.assertEqual(obs['observed'],{'bytes':1054344,'sha256':'c23815bcc4aa90a6789c65b76c996848cab3178cde51504fe42b3d352f1c858d'})
  self.assertEqual(self.c()['fresh_execution_module_count'],27);self.assertFalse(self.c()['higher_h5_as24']['failed_h5_objects_reused'])

def bad_value(value):
 def test(self):
  c=self.c();c[FIELD]=value
  with self.assertRaises(Exception):a.validate_diagnostic_profile(c)
  with self.assertRaises(Exception):h.command_address_space_bytes(c,RAW,a)
 return test
for name,value in [('as12',12),('as16',16),('as32',32),('string','24'),('bool',True),('float',24.0),('null',None)]:setattr(H5AS24Tests,'test_invalid_fixed_value_'+name,bad_value(value))
