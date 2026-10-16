import copy,hashlib,json,shutil,sys,tempfile,unittest
from pathlib import Path
from unittest.mock import patch
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'ci'))
import cache_diagnostic as c
import collect_evidence as collector

def raw(x):return (json.dumps(x,sort_keys=True,indent=2)+'\n').encode()
def row(p):return {'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}

class FinalOriginTests(unittest.TestCase):
 def fixture(self,root):
  contract=json.loads((ROOT/'contract.json').read_bytes());(root/'origin').mkdir()
  for name in ['producer-contract.json','continuation-producer-contract.json','continuation-producer-origins.json','locked-origins.json']:
   shutil.copyfile(ROOT/'origin'/name,root/'origin'/name)
  return contract,json.loads((root/'origin/locked-origins.json').read_bytes())
 def seal(self,root,contract,lock):
  path=root/'origin/locked-origins.json';path.write_bytes(raw(lock));r=row(path);contract['origin_lock']={'path':'origin/locked-origins.json',**r};contract['inputs']['origin/locked-origins.json']=r
 def check(self,root,contract):
  with patch.object(c,'ROOT',root),patch.object(c,'validate_stage_plan'),patch.object(c,'validate_final_auditor_variant'):
   return c.validate_final_origins(contract)
 def test_exact_two_producer_contracts_and_stage_assignment(self):
  with tempfile.TemporaryDirectory() as td:
   root=Path(td);contract,lock=self.fixture(root);selected,rows=self.check(root,contract)
   self.assertEqual(list(selected),list(lock['stages']));self.assertEqual(rows,lock['stages'])
   for sid in rows:self.assertEqual(hashlib.sha256(raw(selected[sid])).hexdigest(),rows[sid]['producer_contract_sha256'])
 def test_wrong_stage_contract_or_origin_rejected(self):
  for sid in ['F0_common','F1_curved_existence','F2_period_hierarchy','F3_product_geometry']:
   for change in ['contract','run','attempt','commit','workflow','stage','failed']:
    with self.subTest(sid=sid,change=change),tempfile.TemporaryDirectory() as td:
     root=Path(td);contract,lock=self.fixture(root);r=lock['stages'][sid]
     if change=='contract':r['producer_contract_sha256']=c.ORIGINAL_STAGE_CONTRACT_SHA if sid=='F3_product_geometry' else c.CONTINUATION_PRODUCER_SHA
     elif change=='workflow':r['origin']['workflow_id']+=1
     elif change=='stage':r['origin']['stage_id']='F4_bridge_and_endpoint_joins'
     elif change=='failed':r['origin']['producer_conclusion']='failure'
     else:r['origin']['identity'][{'run':'run_id','attempt':'run_attempt','commit':'workflow_commit'}[change]]='9' if change!='commit' else '9'*40
     self.seal(root,contract,lock)
     with self.assertRaises(Exception):self.check(root,contract)
 def test_missing_extra_and_unknown_contract_rejected(self):
  for case in ['missing_stage','extra_stage','extra_contract','unknown_contract','missing_contract']:
   with self.subTest(case=case),tempfile.TemporaryDirectory() as td:
    root=Path(td);contract,lock=self.fixture(root)
    if case=='missing_stage':lock['stages'].pop('F3_product_geometry')
    elif case=='extra_stage':lock['stages']['F4_bridge_and_endpoint_joins']=copy.deepcopy(lock['stages']['F3_product_geometry'])
    elif case=='extra_contract':contract['producer_contracts']['f'*64]=copy.deepcopy(next(iter(contract['producer_contracts'].values())))
    elif case=='missing_contract':contract['producer_contracts'].pop(c.CONTINUATION_PRODUCER_SHA)
    else:lock['producer_contracts'][1]='f'*64
    self.seal(root,contract,lock)
    with self.assertRaises(Exception):self.check(root,contract)
 def test_native_predecessor_lock_must_remain_byte_identical(self):
  with tempfile.TemporaryDirectory() as td:
   root=Path(td);contract,lock=self.fixture(root);p=root/'origin/continuation-producer-origins.json';p.write_bytes(p.read_bytes()+b' ')
   with self.assertRaises(Exception):self.check(root,contract)
 def test_selected_predecessor_receipt_cannot_diverge_from_native_f3(self):
  with tempfile.TemporaryDirectory() as td:
   root=Path(td);contract,lock=self.fixture(root);lock['stages']['F0_common']['receipt_sha256']='f'*64;self.seal(root,contract,lock)
   with self.assertRaises(Exception):self.check(root,contract)
 def test_changed_producer_contract_bytes_rejected(self):
  for name in ['producer-contract.json','continuation-producer-contract.json']:
   with self.subTest(name=name),tempfile.TemporaryDirectory() as td:
    root=Path(td);contract,lock=self.fixture(root);p=root/'origin'/name;p.write_bytes(p.read_bytes()+b' ')
    with self.assertRaises(Exception):self.check(root,contract)
 def test_source_and_immutable_input_mismatch_rejected(self):
  for name in ['src/SpectreGeometry.PolygonProductKeyReferenceFinite.lean','locks/dependencies.json','auditors/AuditOrdinaryBridges.lean']:
   with self.subTest(name=name),tempfile.TemporaryDirectory() as td:
    root=Path(td);contract,lock=self.fixture(root)
    if name.startswith('src/'):name='src/SpectreGeometry/PolygonProductKeyReferenceFinite.lean'
    contract['inputs'][name]['sha256']='f'*64
    with self.assertRaises(Exception):self.check(root,contract)
 def test_native_collector_uses_exact_preserved_origin_lock(self):
  native=json.loads((ROOT/'origin/continuation-producer-contract.json').read_bytes());expected=json.loads((ROOT/'origin/continuation-producer-origins.json').read_bytes())['stages'];self.assertEqual(collector.locked_origin_rows(native),expected)
  wrong=copy.deepcopy(native);wrong['review_status']='changed'
  with self.assertRaises(Exception):collector.locked_origin_rows(wrong)
 def test_collector_mixed_lock_retains_per_stage_contract(self):
  contract=json.loads((ROOT/'contract.json').read_bytes());rows=collector.locked_origin_rows(contract)
  self.assertEqual(rows['F3_product_geometry']['producer_contract_sha256'],c.CONTINUATION_PRODUCER_SHA)
  for sid in ['F0_common','F1_curved_existence','F2_period_hierarchy']:self.assertEqual(rows[sid]['producer_contract_sha256'],c.ORIGINAL_STAGE_CONTRACT_SHA)
 def test_one_fresh_job_and_exact_bounds(self):
  contract=json.loads((ROOT/'contract.json').read_bytes());c.validate_diagnostic_profile(contract)
  self.assertEqual(contract['execution_stages'],['F4_bridge_and_endpoint_joins']);self.assertEqual(contract['workflow_job_count'],1)
  self.assertEqual(contract['workflow_aggregate_seconds'],19200);self.assertEqual(contract['workflow_outer_runner_minutes'],330)
  for key,value in [('execution_stages',['F3_product_geometry','F4_bridge_and_endpoint_joins']),('workflow_job_count',2),('workflow_aggregate_seconds',38400),('workflow_outer_runner_minutes',660),('locked_origin_stages',contract['locked_origin_stages'][:-1])]:
   wrong=copy.deepcopy(contract);wrong[key]=value
   with self.subTest(key=key),self.assertRaises(Exception):c.validate_diagnostic_profile(wrong)
 def test_workflow_has_only_final_job_without_stale_needs(self):
  text=(ROOT/'.github/workflows/conditional-geometry.yml').read_text();self.assertNotIn('  F3_product_geometry:',text);self.assertNotIn('needs:',text);self.assertEqual(text.count('  F4_bridge_and_endpoint_joins:'),1)
  self.assertEqual(text.count('timeout-minutes: 330'),1);self.assertIn('cancel-in-progress: false',text)

class AuditorVariantTests(unittest.TestCase):
 def fixture(self,root):
  (root/'auditors').mkdir();(root/'evidence/auditor-provenance').mkdir(parents=True);(root/'locks').mkdir()
  old=(ROOT/'evidence/auditor-provenance/AuditConditionalEndpoints.original.lean').read_bytes();new=old.replace(b'mkConst `Exists [.zero]',b'mkConst `Exists [.succ .zero]',1)
  (root/'evidence/auditor-provenance/AuditConditionalEndpoints.original.lean').write_bytes(old);(root/'auditors/AuditConditionalEndpoints.lean').write_bytes(new)
  lock={'schema':'exact-endpoint-exists-universe-correction-v1','original_sha256':hashlib.sha256(old).hexdigest(),'corrected_sha256':hashlib.sha256(new).hexdigest(),'old_bytes':'mkConst `Exists [.zero]','new_bytes':'mkConst `Exists [.succ .zero]','official_runtime_inventory_sha256':c.RUNTIME_INVENTORY_SHA,'control_manifest_sha256':'1'*64,'independent_control_review_sha256':'2'*64}
  path=root/'locks/endpoint-auditor-correction.json';path.write_bytes(raw(lock));r=row(path)
  contract={'pending_auditor_correction':False,'endpoint_auditor_correction':{'path':'locks/endpoint-auditor-correction.json',**r},'inputs':{n:row(root/n) for n in ['locks/endpoint-auditor-correction.json','evidence/auditor-provenance/AuditConditionalEndpoints.original.lean','auditors/AuditConditionalEndpoints.lean']}}
  producer={'inputs':{'auditors/AuditConditionalEndpoints.lean':row(root/'evidence/auditor-provenance/AuditConditionalEndpoints.original.lean')}}
  return contract,producer,lock
 def check(self,root,contract,producer):
  with patch.object(c,'ROOT',root):c.validate_final_auditor_variant(contract,producer)
 def test_exact_one_line_only(self):
  with tempfile.TemporaryDirectory() as td:
   root=Path(td);contract,producer,lock=self.fixture(root);self.check(root,contract,producer)
 def test_pending_control_rejected(self):
  with tempfile.TemporaryDirectory() as td:
   root=Path(td);contract,producer,lock=self.fixture(root);contract['pending_auditor_correction']=True
   with self.assertRaises(Exception):self.check(root,contract,producer)
 def test_extra_change_even_with_updated_corrected_hash_rejected(self):
  with tempfile.TemporaryDirectory() as td:
   root=Path(td);contract,producer,lock=self.fixture(root);path=root/'auditors/AuditConditionalEndpoints.lean';path.write_bytes(path.read_bytes()+b'\n');r=row(path);contract['inputs']['auditors/AuditConditionalEndpoints.lean']=r;lock['corrected_sha256']=r['sha256'];path=root/'locks/endpoint-auditor-correction.json';path.write_bytes(raw(lock));r=row(path);contract['inputs']['locks/endpoint-auditor-correction.json']=r;contract['endpoint_auditor_correction'].update(r)
   with self.assertRaises(Exception):self.check(root,contract,producer)
 def test_original_changed_or_wrong_universe_rejected(self):
  for case in ['original','uncorrected','wrong_level']:
   with self.subTest(case=case),tempfile.TemporaryDirectory() as td:
    root=Path(td);contract,producer,lock=self.fixture(root)
    if case=='original':path=root/'evidence/auditor-provenance/AuditConditionalEndpoints.original.lean';path.write_bytes(path.read_bytes()+b' ')
    else:
     path=root/'auditors/AuditConditionalEndpoints.lean';path.write_bytes(path.read_bytes().replace(b'mkConst `Exists [.succ .zero]',b'mkConst `Exists [.zero]' if case=='uncorrected' else b'mkConst `Exists [.succ (.succ .zero)]'))
    with self.assertRaises(Exception):self.check(root,contract,producer)


class MixedCertificateTests(unittest.TestCase):
 def fixture(self):
  consumer={'repository':'jconorgrogan/palomar-chair-verification','run_id':'400','run_attempt':'1','workflow_commit':'4'*40};old={**consumer,'run_id':'100','workflow_commit':'1'*40};new={**consumer,'run_id':'200','workflow_commit':'2'*40}
  stages={'F0_common':{'modules':['A'],'admitted_stages':[]},'F3_product_geometry':{'modules':['B'],'admitted_stages':['F0_common']},'F4_bridge_and_endpoint_joins':{'modules':['C'],'admitted_stages':['F0_common','F3_product_geometry']}}
  contract={'schema':c.FINAL_SCHEMA,'stages':stages,'locked_origin_stages':['F0_common','F3_product_geometry'],'source_archive':{'sha256':'f'*64},'official_lean_inventory_sha256':'e'*64}
  locked={};lineage=[]
  for sid,identity,sha in [('F0_common',old,c.ORIGINAL_STAGE_CONTRACT_SHA),('F3_product_geometry',new,c.CONTINUATION_PRODUCER_SHA)]:
   origin={'identity':identity,'stage_id':sid,'artifact_id':11 if sid=='F0_common' else 12};locked[sid]={'origin':origin,'producer_contract_sha256':sha,'receipt_sha256':'a'*64,'checked_module_receipts_sha256':'b'*64};lineage.append({'stage_id':sid,'origin':copy.deepcopy(origin),'receipt_sha256':'a'*64,'checked_module_receipts_sha256':'b'*64,'own_modules':stages[sid]['modules']})
  inventory={m+s:{'bytes':1,'sha256':'c'*64} for m in ['A','B','C'] for s in c.SUFFIXES}
  return contract,consumer,lineage,inventory,locked
 def make(self,x):
  contract,consumer,lineage,inventory,locked=x
  return collector.make_cross_origin_certificate(contract,'d'*64,consumer,'F4_bridge_and_endpoint_joins',{'fixed':True},lineage,inventory,locked)
 def test_certificate_records_native_contract_per_stage(self):
  x=self.fixture();before=copy.deepcopy(x);out=self.make(x);self.assertEqual(x,before);self.assertEqual(out['schema'],'conditional-locked-origin-admissions-v2');self.assertFalse(out['fresh_in_one_run']);self.assertEqual([r['producer_contract_sha256'] for r in out['admissions']],[c.ORIGINAL_STAGE_CONTRACT_SHA,c.CONTINUATION_PRODUCER_SHA])
 def test_missing_f3_lock_cannot_fall_back_to_current_run(self):
  x=self.fixture();x[4].pop('F3_product_geometry');x[2][1]['origin']['identity']=copy.deepcopy(x[1])
  with self.assertRaises(Exception):self.make(x)
 def test_changed_origin_receipt_output_or_stage_rejected(self):
  for case in ['origin','receipt','checked_receipt','modules','missing_output','stage_order']:
   with self.subTest(case=case):
    x=self.fixture()
    if case=='origin':x[2][1]['origin']['identity']['run_id']='300'
    elif case=='receipt':x[2][1]['receipt_sha256']='9'*64
    elif case=='checked_receipt':x[2][1]['checked_module_receipts_sha256']='9'*64
    elif case=='modules':x[2][1]['own_modules']=['X']
    elif case=='missing_output':x[3].pop('B.olean')
    else:x[2].reverse()
    with self.assertRaises(Exception):self.make(x)

class MixedRestoreLoopTests(unittest.TestCase):
 def run_case(self,case=None):
  from contextlib import ExitStack
  stages={'F0_common':{'modules':['A'],'admitted_stages':[]},'F1_curved_existence':{'modules':['B'],'admitted_stages':['F0_common']},'F2_period_hierarchy':{'modules':['C'],'admitted_stages':['F0_common']},'F3_product_geometry':{'modules':['D'],'admitted_stages':['F0_common']},'F4_bridge_and_endpoint_joins':{'modules':['E'],'admitted_stages':['F0_common','F1_curved_existence','F2_period_hierarchy','F3_product_geometry']}}
  contract={'schema':c.FINAL_SCHEMA,'stages':stages,'transport_timeout_seconds':1800,'object_artifact_max_bytes':99999,'owned_output_max_bytes':99999}
  original={'tag':'original','stages':stages};continuation={'tag':'continuation','stages':stages}
  selected={sid:(continuation if sid=='F3_product_geometry' else original) for sid in stages if sid!='F4_bridge_and_endpoint_joins'}
  locked={sid:{'origin':{'stage_id':sid,'identity':{'run_id':'200' if sid=='F3_product_geometry' else '100'}},'producer_contract_sha256':c.CONTINUATION_PRODUCER_SHA if sid=='F3_product_geometry' else c.ORIGINAL_STAGE_CONTRACT_SHA,'receipt_sha256':'a'*64,'checked_module_receipts_sha256':'a'*64,'descriptor_sha256':'a'*64,'stage_tar_sha256':'b'*64,'stage_tar_bytes':42} for sid in selected}
  if case=='missing_f3':locked.pop('F3_product_geometry')
  downloads=[];admissions=[];deadlines=[]
  class Client:
   def __init__(self,*,deadline,origin_lock):self.origin=origin_lock;deadlines.append(deadline)
   def download_stage(self,sid,name,destination,maximum):
    downloads.append(sid)
    return {'stage_id':'wrong'} if case=='wrong_f3' and sid=='F3_product_geometry' else self.origin
  def load(path):
   return {'packages':[]} if path.name=='dependencies.json' else {'archive_sha256':'b'*64,'archive_bytes':42,'receipt_sha256':'a'*64}
  def admit(extracted,*,expected,objects,prior,checked,api,deadline):
   sid=expected['stage_id'];admissions.append(expected);deadlines.append(deadline)
   self.assertIs(expected['contract'],selected[sid]);self.assertEqual(expected['contract_sha256'],locked[sid]['producer_contract_sha256'])
   self.assertEqual([r['stage_id'] for r in expected['predecessor_artifacts']],stages[sid]['admitted_stages'])
   self.assertEqual(set(expected['producer_inventory']),set(c.module_outputs('A')) if sid!='F0_common' else set())
   self.assertNotIn(stages[sid]['modules'][0],checked)
   inventory=dict(prior)
   for m in stages[sid]['modules']:
    for name in c.module_outputs(m):inventory[name]={'bytes':1,'sha256':'c'*64}
   return [{'module':m} for m in stages[sid]['modules']],inventory
  with tempfile.TemporaryDirectory() as td,ExitStack() as stack:
   work=Path(td)
   for obj,name,value in [(c,'validate_continuation_origins',lambda _: (selected,locked)),(c.f,'load_json',load),(c.f,'file_sha',lambda _:'a'*64),(c.transport,'Transport',Client),(c.transport,'extract_stage',lambda *a,**k: {}),(c.transport,'admit_stage',admit),(c.shutil,'rmtree',lambda _:None),(c,'verify_owned_final',lambda *a:None),(c.transport,'check_deadline',lambda d:deadlines.append(d))]:stack.enter_context(patch.object(obj,name,value))
   def run():return c.restore_stages(work,contract,'d'*64,'F4_bridge_and_endpoint_joins',{}, {m:{} for m in 'ABCDE'},{},Path('/runtime'),c.time.monotonic()+2000)
   if case:
    with self.assertRaises(Exception):run()
    self.assertEqual([x['stage_id'] for x in admissions],list(selected)[:3]);self.assertEqual(downloads,list(selected)[:3] if case=='missing_f3' else list(selected))
   else:
    inventory,checked,lineage=run();self.assertEqual(checked,set('ABCD'));self.assertEqual(len(inventory),28);self.assertEqual([r['stage_id'] for r in lineage],list(selected));self.assertEqual(downloads,list(selected));self.assertEqual(len(set(deadlines)),1)
 def test_each_stage_uses_native_contract_and_exact_predecessors(self):self.run_case()
 def test_missing_lock_stops_before_f3_download(self):self.run_case('missing_f3')
 def test_wrong_f3_origin_stops_before_admission(self):self.run_case('wrong_f3')

if __name__=='__main__':unittest.main()
