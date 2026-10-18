"""Source-only controls; run only through the permanently guarded suite runner."""
import ast,copy,hashlib,json,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'ci'))
import cache_diagnostic as a
h=a.higher

class H5RetryTests(unittest.TestCase):
 def c(self):return a.f.load_json(ROOT/'contract.json')
 def original(self):return a.f.load_json(ROOT/'origin/higher-h0-h3-producer-contract.json')
 def lock(self):return a.f.load_json(ROOT/'origin/locked-origins.json')
 def test_exact_27_modules_and_seven_original_predecessors(self):
  c=self.c();a.validate_diagnostic_profile(c);a.validate_stage_plan(c)
  self.assertEqual(c['execution_stages'],['H5_higher_assembly']);self.assertEqual(len(c['stages']['H5_higher_assembly']['modules']),27)
  self.assertEqual(c['locked_origin_stages'],h.OLD+h.HSTAGES[:-1]);self.assertEqual(c['fresh_execution_module_count'],27)
  self.assertEqual(c['retained_higher_module_count'],1111)
 def test_every_original_per_command_and_per_job_cap_is_unchanged(self):
  c=self.c();old=self.original()
  for key in old:
   if any(s in key for s in ['timeout','deadline','max_bytes','_heap_','_rss_','minimum_','failure_evidence_grace']):self.assertEqual(c[key],old[key],key)
  self.assertEqual(c['module_checker_timeout_exceptions'],old['module_checker_timeout_exceptions'])
 def test_all_auditors_research_source_and_import_pins_unchanged(self):
  c=self.c();old=self.original()
  for key,pin in old['inputs'].items():
   if key.startswith(('auditors/','src/')) or key in ['locks/owned-sources.json','locks/required-modules.json','locks/cache-extension.json','locks/higher-visibility-variants.json']:
    self.assertEqual(c['inputs'][key],pin,key)
  self.assertEqual(c['stages'],old['stages']);self.assertEqual(c['source_archive'],old['source_archive'])
 def test_original_producer_and_three_origin_lock_are_exact(self):
  old=self.original();self.assertEqual(a.f.file_sha(ROOT/'origin/higher-h0-h3-producer-contract.json'),h.H5_PRODUCER_SHA)
  a.validate_diagnostic_profile(old);a.validate_stage_plan(old)
  self.assertEqual(a.f.file_sha(ROOT/'origin/higher-h0-h3-producer-origins.json'),old['origin_lock']['sha256'])
  col=a.load_helper('collect_evidence');self.assertEqual(list(col.locked_origin_rows(old)),h.OLD+[h.H4_STAGE])
 def test_current_origin_selection_retains_original_producer_contracts(self):
  c=self.c();selected,locked=a.validate_continuation_origins(c)
  self.assertEqual(set(selected),set(c['locked_origin_stages']));self.assertEqual(locked,self.lock()['stages'])
  for sid in h.HSTAGES[:4]:
   self.assertEqual(h.digest(selected[sid]),h.H5_PRODUCER_SHA)
   self.assertEqual(locked[sid]['origin']['identity'],h.H5_PRODUCER_IDENTITY)
   self.assertEqual(h.producer_cache_role(selected[sid],sid,a),'extended')
 def test_frozen_origin_scope_excludes_h5_payload(self):
  self.assertNotIn('H5_higher_assembly',self.lock()['stages'])
  self.assertFalse(self.c()['higher_h5_retry']['failed_h5_objects_reused'])
  self.assertEqual(a.f.file_sha(ROOT/'origin/failed-h5-terminal-review.json'),'b3316faad3cda79182e2eca04ac0a8630fc9bd17fb496f5644d340bbcd834a01')
  with self.assertRaises(Exception):a.transport.validate_origin_lock({**self.lock()['stages']['H0_common']['origin'],'stage_id':'H5_higher_assembly'})
 def test_native_extended_interface_required_for_every_retained_higher_stage(self):
  c=self.c();interface=a.f.load_json(ROOT/'origin/higher-interface-identity.json')
  for sid in h.HSTAGES[:-1]:
   self.assertEqual(h.require_native_interface(c,sid,interface,a),interface)
   bad={**interface,'runtime_inventory_sha256':'0'*64}
   with self.assertRaises(Exception):h.require_native_interface(c,sid,bad,a)
 def test_native_collector_does_not_relabel_original_as_successor(self):
  col=a.load_helper('collect_evidence');old=self.original();native=col.locked_origin_rows(old);new=col.locked_origin_rows(self.c())
  self.assertEqual(set(native),set(h.OLD+[h.H4_STAGE]));self.assertEqual(set(new),set(h.OLD+h.HSTAGES[:-1]))
  for sid in native:self.assertEqual(native[sid],new[sid])
 def test_failed_h5_observation_and_vms_survive_unchanged_collector(self):
  c=self.c();col=a.load_helper('collect_evidence')
  with tempfile.TemporaryDirectory(prefix='h5-failure-evidence-') as d:
   root=Path(d);e=root/'evidence';e.mkdir();(root/'logs').mkdir()
   values={'result.json':{'status':'FAILED_OR_INCOMPLETE','contract_sha256':h.digest(c)},
    'higher-h5-ir-predispatch-observation.json':{'observation_phase':'immediately_before_raw_audit_dispatch','observed':{'bytes':1054344,'sha256':'c23815bcc4aa90a6789c65b76c996848cab3178cde51504fe42b3d352f1c858d'},'refusal_reason':None},
    'last_command.json':{'exit_code':1,'max_sampled_process_virtual_size_bytes':11000000000,'max_sampled_tree_virtual_size_bytes':13000000000,'virtual_size_sample_count':124}}
   for path,value in values.items():(e/path).write_bytes(a.f.json_bytes(value))
   result=col.collect(root,c,h.digest(c));self.assertTrue(result['all_available_files_copied']);self.assertFalse(result['replay_acceptance_evidence_complete'])
   for path in values:self.assertEqual((root/'upload'/path).read_bytes(),(e/path).read_bytes())
   self.assertEqual(col.MAXIMUM,128*1024**2);self.assertEqual(col.RESERVE,4*1024**2)
 def fixture(self,sid='H0_common'):
  c=self.c();current={r['module']:r for r in a.f.load_json(ROOT/'locks/owned-sources.json')['sources']}
  return copy.deepcopy(self.lock()['stages'][sid]),sid,c,self.original(),current
 def test_no_missing_descriptor_or_tar_pins(self):
  for sid in h.HSTAGES[:4]:h.validate_h0_h3_origin_row(*self.fixture(sid),a)
  for key in ['descriptor_sha256','stage_tar_sha256','receipt_sha256','checked_module_receipts_sha256','independent_review_sha256','stage_tar_bytes']:
   args=list(self.fixture());args[0][key]=None
   with self.assertRaises(Exception):h.validate_h0_h3_origin_row(*args,a)
 def test_original_stage_source_and_identity_mutations_fail(self):
  for key,value in [('run_id','999'),('run_attempt','2'),('workflow_commit','0'*40)]:
   args=list(self.fixture());args[0]['origin']['identity'][key]=value
   with self.assertRaises(Exception):h.validate_h0_h3_origin_row(*args,a)
  args=list(self.fixture());args[0]['producer_contract_sha256']='0'*64
  with self.assertRaises(Exception):h.validate_h0_h3_origin_row(*args,a)
  args=list(self.fixture());module=args[3]['stages']['H0_common']['modules'][0];args[2]['inputs'][args[4][module]['path']]['sha256']='0'*64
  with self.assertRaises(Exception):h.validate_h0_h3_origin_row(*args,a)

def mutant(key,value):
 def test(self):
  c=self.c();c[key]=value
  with self.assertRaises(Exception):a.validate_diagnostic_profile(c)
 return test
for key,value in {'higher_h5_retry_mode':'unknown','higher_recovery_mode':'unknown','execution_stages':['H0_common','H5_higher_assembly'],
 'locked_origin_stages':['F0_common','F3_product_geometry','H4_product_geometry'],'fresh_execution_module_count':834,'retained_higher_module_count':304,
 'workflow_job_count':5,'publication_branch':'wrong-branch','higher_h5_retry':{}}.items():setattr(H5RetryTests,'test_reject_'+key,mutant(key,value))
