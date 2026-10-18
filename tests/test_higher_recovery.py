"""Offline controls for exact native H4 continuation; no object or Lean execution."""
import copy,hashlib,json,sys,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'ci'))
import cache_diagnostic as a
h=a.higher
class HigherRecoveryTests(unittest.TestCase):
 def c(self):return a.f.load_json(ROOT/'contract.json')
 def producer(self):return a.f.load_json(ROOT/'origin/higher-producer-contract.json')
 def test_native_higher_contract_exact(self):
  self.assertEqual(a.f.file_sha(ROOT/'origin/higher-producer-contract.json'),h.H4_PRODUCER_SHA)
  a.validate_diagnostic_profile(self.producer());a.validate_stage_plan(self.producer())
 def test_original_native_predecessor_lock_exact(self):
  p=self.producer()['origin_lock'];self.assertEqual(a.f.file_sha(ROOT/'origin/higher-producer-origins.json'),p['sha256'])
  col=a.load_helper('collect_evidence');rows=col.locked_origin_rows(self.producer())
  self.assertEqual(set(rows),set(h.OLD))
 def test_old_native_contract_mutation_rejected(self):
  col=a.load_helper('collect_evidence');c=self.producer();c['check_timeout_seconds']+=1
  with self.assertRaises(Exception):col.locked_origin_rows(c)
 def test_exact_cache_roles(self):
  old=a.f.load_json(ROOT/'origin/producer-contract.json');f3=a.f.load_json(ROOT/'origin/continuation-producer-contract.json')
  self.assertEqual(h.producer_cache_role(old,'F0_common',a),'base')
  self.assertEqual(h.producer_cache_role(f3,'F3_product_geometry',a),'base')
  self.assertEqual(h.producer_cache_role(self.producer(),h.H4_STAGE,a),'extended')
  self.assertEqual(h.producer_cache_role(self.c(),'H0_common',a),'extended')
 def test_base_roles_cannot_be_swapped(self):
  old=a.f.load_json(ROOT/'origin/producer-contract.json');f3=a.f.load_json(ROOT/'origin/continuation-producer-contract.json')
  for c,sid in [(old,h.OLD[1]),(f3,h.OLD[0]),(self.producer(),h.OLD[0]),(old,h.H4_STAGE)]:
   with self.assertRaises(Exception):h.producer_cache_role(c,sid,a)
 def test_base_contract_profile_mutation_rejected(self):
  c=a.f.load_json(ROOT/'origin/producer-contract.json');c['check_timeout_seconds']+=1
  with self.assertRaises(Exception):h.producer_cache_role(c,h.OLD[0],a)
 def test_no_unknown_cache_role(self):
  with self.assertRaises(Exception):h.producer_cache_role(self.c(),'H6_extra',a)
 def test_original_h4_source_graph_and_archive_exact(self):
  c=self.c();old=self.producer()
  self.assertEqual(c['source_archive'],old['source_archive'])
  self.assertEqual(c['stages'][h.H4_STAGE],old['stages'][h.H4_STAGE])
  for m in old['stages'][h.H4_STAGE]['modules']:
   p='src/'+m.replace('.','/')+'.lean';self.assertEqual(c['inputs'][p],old['inputs'][p])
 def test_recovery_executes_27_h5_modules_only(self):
  c=self.c();self.assertEqual(c['execution_stages'],[h.HSTAGES[-1]])
  names=[m for sid in c['execution_stages'] for m in c['stages'][sid]['modules']]
  self.assertEqual(len(names),len(set(names)));self.assertEqual(len(names),27)
  old={m for sid in h.HSTAGES[:-1] for m in c['stages'][sid]['modules']};self.assertEqual(len(old),1111);self.assertFalse(old&set(names))
  self.assertEqual(len(old|set(names)),1138)
 def test_workflow_has_h5_only_and_no_h4_job(self):
  import re
  text=next((ROOT/'.github/workflows').glob('*.yml')).read_text()
  jobs=re.findall(r'^  (H\d_\w+):$',text,re.M)
  self.assertEqual(jobs,self.c()['execution_stages']);self.assertNotIn('"H4_product_geometry"',text)
  self.assertEqual(text.count('timeout-minutes: 330'),1)
 def test_workflow_aggregate_and_per_job_bounds(self):
  c=self.c();self.assertEqual(c['workflow_job_count'],1);self.assertEqual(c['workflow_aggregate_seconds'],19200);self.assertEqual(c['workflow_outer_runner_minutes'],330)
  self.assertEqual(c['aggregate_command_deadline_seconds'],19200);self.assertEqual(c['outer_timeout_minutes'],330)
 def test_transport_only_exact_h0_h4_allowlist_change(self):
  text=(ROOT/'ci/conditional_transport.py').read_text();new="LOCKED_STAGES = ('F0_common','F1_curved_existence','F2_period_hierarchy','F3_product_geometry','H0_common','H1_coarse_contacts','H2_forward_contacts','H3_contact_binding','H4_product_geometry')"
  self.assertEqual(text.count(new),1);restored=text.replace(new,new.replace(",'H0_common','H1_coarse_contacts','H2_forward_contacts','H3_contact_binding','H4_product_geometry'",''))
  before="        address_space=spec.get('address_space_bytes',12*GIB)\n        f.need(command.get('address_space_bytes')==address_space and command.get('max_created_file_bytes')==512*1024**2 and\n               command.get('max_log_bytes')==contract['per_command_log_max_bytes'],'command resource profile differs')\n        f.need(command.get('limits')=={'address_space_bytes':address_space,'rss_tree_bytes':8*GIB,'max_created_file_bytes':512*1024**2},'serialized command limits differ')\n";after="        f.need(command.get('address_space_bytes')==12*GIB and command.get('max_created_file_bytes')==512*1024**2 and\n               command.get('max_log_bytes')==contract['per_command_log_max_bytes'],'command resource profile differs')\n        f.need(command.get('limits')=={'address_space_bytes':12*GIB,'rss_tree_bytes':8*GIB,'max_created_file_bytes':512*1024**2},'serialized command limits differ')\n"
  self.assertEqual(restored.count(before),1);restored=restored.replace(before,after)
  self.assertEqual(hashlib.sha256(restored.encode()).hexdigest(),'25dca67e7f3238a177463ea4d1508bf350b29b8ddf7904ce19a3736d9d73fa89')
 def test_h4_native_contract_keeps_original_control_pin(self):
  self.assertEqual(self.producer()['inputs']['auditors/HigherInspectorControl.lean'],{'bytes':6975,'sha256':'017aadfea7927f7957a5143bcfa8f93af37214ef56f62881e8bddb05af34e482'})
 def test_recovery_mode_is_explicit(self):
  self.assertTrue(h.recovery(self.c()));self.assertFalse(h.recovery(self.producer()))
  c=self.c();c['higher_recovery_mode']='unapproved'
  with self.assertRaises(Exception):h.profile(c,a)

class SyntheticH4OriginTests(unittest.TestCase):
 """Synthetic metadata exercises policy only. These rows are never a selection lock."""
 def fixture(self):
  c=a.f.load_json(ROOT/'contract.json');producer=a.f.load_json(ROOT/'origin/higher-producer-contract.json')
  current={r['module']:r for r in a.f.load_json(ROOT/'locks/owned-sources.json')['sources']}
  row=copy.deepcopy(a.f.load_json(ROOT/'origin/higher-producer-origins.json')['stages'][h.OLD[0]])
  row['producer_contract_sha256']=h.H4_PRODUCER_SHA;o=row['origin'];o['identity']=dict(h.H4_IDENTITY);o['stage_id']=h.H4_STAGE;o['producer_job_name']='conditional '+h.H4_STAGE
  o['artifact_name']='conditional-geometry-38982023996-1-H4_product_geometry-objects'
  return row,c,producer,current
 def test_synthetic_h4_metadata_shape(self):h.validate_h4_origin_row(*self.fixture(),a)
 def test_real_pending_selection_is_rejected(self):
  lock=a.f.load_json(ROOT/'origin/locked-origins.json')
  if lock['stages'][h.H4_STAGE].get('selection_pending') is True:
   with self.assertRaises(Exception):a.validate_continuation_origins(a.f.load_json(ROOT/'contract.json'))
  else:a.validate_continuation_origins(a.f.load_json(ROOT/'contract.json'))

def origin_mutation(kind):
 def test(self):
  row,c,producer,current=self.fixture();o=row['origin']
  if kind in ('run_id','run_attempt'):o['identity'][kind]=str(int(o['identity'][kind])+1)
  elif kind=='commit':o['identity']['workflow_commit']='0'*40
  elif kind=='repository':o['identity']['repository']='wrong/repository'
  elif kind=='stage':o['stage_id']='H0_common'
  elif kind=='workflow':o['workflow_id']+=1
  elif kind=='workflow_path':o['workflow_path']='.github/workflows/other.yml'
  elif kind=='failed_job':o['producer_conclusion']='failure'
  elif kind=='producer_contract':row['producer_contract_sha256']='0'*64
  elif kind=='missing_receipt':del row['receipt_sha256']
  elif kind=='extra_field':row['extra']=True
  elif kind=='tar_limit':row['stage_tar_bytes']=c['object_artifact_max_bytes']+1
  elif kind=='bad_digest':row['checked_module_receipts_sha256']='x'*64
  elif kind=='stage_order':c['stages'][h.H4_STAGE]['modules'].reverse()
  elif kind=='source_hash':c['inputs']['src/'+c['stages'][h.H4_STAGE]['modules'][0].replace('.','/')+'.lean']['sha256']='0'*64
  with self.assertRaises(Exception):h.validate_h4_origin_row(row,c,producer,current,a)
 return test
for _kind in ['run_id','run_attempt','commit','repository','stage','workflow','workflow_path','failed_job','producer_contract','missing_receipt','extra_field','tar_limit','bad_digest','stage_order','source_hash']:
 setattr(SyntheticH4OriginTests,'test_reject_'+_kind,origin_mutation(_kind))

class RestoreCompositionTests(unittest.TestCase):
 def run_case(self,omit_h4=False,wrong_interface=False):
  import tempfile
  from unittest.mock import patch
  c=a.f.load_json(ROOT/'contract.json');sid=c['final_stage'];c['stages'][sid]['admitted_stages']=h.OLD+[h.H4_STAGE]
  producers={h.OLD[0]:a.f.load_json(ROOT/'origin/producer-contract.json'),h.OLD[1]:a.f.load_json(ROOT/'origin/continuation-producer-contract.json'),h.H4_STAGE:a.f.load_json(ROOT/'origin/higher-producer-contract.json')}
  locked=a.f.load_json(ROOT/'origin/higher-producer-origins.json')['stages'];locked[h.H4_STAGE]=SyntheticH4OriginTests().fixture()[0]
  if omit_h4:locked.pop(h.H4_STAGE)
  rows={r['module']:r for r in a.f.load_json(ROOT/'locks/owned-sources.json')['sources']};observed=[]
  with tempfile.TemporaryDirectory() as d:
   work=Path(d);(work/'objects').mkdir();hashes={}
   class Client:
    def __init__(self,*,deadline,origin_lock):self.origin=origin_lock
    def download_stage(self,stage,name,destination,maximum):
     self.assert_stage=stage;destination.mkdir();row=locked[stage]
     descriptor={'archive_sha256':row['stage_tar_sha256'],'archive_bytes':row['stage_tar_bytes'],'receipt_sha256':row['receipt_sha256']}
     (destination/'descriptor.json').write_bytes(a.f.json_bytes(descriptor));hashes[destination/'descriptor.json']=row['descriptor_sha256']
     return self.origin
   def extract(download,destination,*,maximum,deadline):
    stage=download.name.removesuffix('-download');destination.mkdir();(destination/'evidence').mkdir()
    for name,value in [('receipt.json',locked[stage]['receipt_sha256']),('evidence/owned-modules.jsonl',locked[stage]['checked_module_receipts_sha256'])]:
     p=destination/name;p.write_bytes(b'inert fixture');hashes[p]=value
    return {}
   def admit(extracted,*,expected,objects,prior,checked,api,deadline):
    stage=expected['stage_id'];role='base' if stage in h.OLD else 'extended'
    self.assertEqual(expected['cache_rows'],{'role':role});self.assertEqual(expected['interface_identity'],{'role':role})
    self.assertEqual(expected['contract'],producers[stage]);self.assertEqual(expected['contract_sha256'],locked[stage]['producer_contract_sha256'])
    observed.append(stage);own={p:{'bytes':0,'sha256':'0'*64} for m in expected['stage_modules'] for p in a.module_outputs(m)}
    return [{'module':m} for m in expected['stage_modules']],{**prior,**own}
   original_load=a.f.pinned_load
   def pinned_load(path,digest):return {'role':'wrong' if wrong_interface else 'extended'} if path==ROOT/'origin/higher-interface-identity.json' else original_load(path,digest)
   original_sha=a.f.file_sha
   def file_sha(p):return hashes[p] if p in hashes else original_sha(p)
   with patch.object(a,'validate_continuation_origins',return_value=(producers,locked)),patch.object(a.transport,'Transport',Client),patch.object(a.transport,'extract_stage',side_effect=extract),patch.object(a.transport,'admit_stage',side_effect=admit),patch.object(a,'verify_owned_final'),patch.object(a.f,'file_sha',side_effect=file_sha),patch.object(a.f,'pinned_load',side_effect=pinned_load):
    def run():return a.restore_stages(work,c,'0'*64,sid,{'role':'extended'},rows,{'role':'extended'},work/'runtime',a.time.monotonic()+60,{'role':'base'},{'role':'base'})
    if omit_h4 or wrong_interface:
     with self.assertRaisesRegex(Exception,'unlocked earlier producer stage' if omit_h4 else 'native H4 extended interface changed'):run()
     self.assertEqual(observed,h.OLD);return
    prior,checked,lineage=run()
   self.assertEqual(observed,h.OLD+[h.H4_STAGE]);self.assertEqual(len(checked),186+109+304);self.assertEqual(len(prior),7*len(checked));self.assertEqual([r['stage_id'] for r in lineage],observed)

 def test_actual_restore_dispatches_native_interfaces(self):self.run_case()
 def test_actual_restore_rejects_h4_same_run_fallback(self):self.run_case(omit_h4=True)
 def test_actual_restore_rejects_changed_h4_interface(self):self.run_case(wrong_interface=True)

class ControlLayoutTests(unittest.TestCase):
 def test_exact_reviewed_control_layout(self):h.validate_control_layout(a.f.load_json(ROOT/'contract.json'),a)
 def test_all_control_checks_and_production_helpers_preserved(self):
  import re
  old=(ROOT/'origin/HigherInspectorControl.original.lean').read_bytes();new=(ROOT/'auditors/HigherInspectorControl.lean').read_bytes()
  self.assertEqual(new.count(b'meta import Lean.Elab.Command\n'),1)
  self.assertEqual(re.sub(rb'\s+',b'',old),re.sub(rb'\s+',b'',new.replace(b'meta import Lean.Elab.Command\n',b'',1)));self.assertEqual(len(new)-len(old),34)
  self.assertEqual(a.f.file_sha(ROOT/('origin/AuditHigherPhysicalEndpoints.pre-phase.lean' if h.raw_heap7168(a.f.load_json(ROOT/'contract.json')) else 'auditors/AuditHigherPhysicalEndpoints.lean')),'ba9a502d5f121719b7fff10c73d3bf9cfa6857a0f2a42e99b36d39051b64af13')
  self.assertEqual(a.f.file_sha(ROOT/'auditors/HigherPhysicalReference.lean'),'bcf383a13467b15ce7b55e1e4a171bab4f86439e696b0a30ebd13769236c15ea')
 def test_original_control_cannot_satisfy_recovery_profile(self):
  c=a.f.load_json(ROOT/'contract.json');c['inputs']['auditors/HigherInspectorControl.lean']=a.f.load_json(ROOT/'origin/higher-producer-contract.json')['inputs']['auditors/HigherInspectorControl.lean']
  with self.assertRaises(Exception):a.validate_diagnostic_profile(c)
 def test_missing_layout_review_rejected(self):
  c=a.f.load_json(ROOT/'contract.json');del c['higher_control_layout_review_sha256']
  with self.assertRaises(Exception):h.validate_control_layout(c,a)
 def test_changed_layout_review_rejected(self):
  c=a.f.load_json(ROOT/'contract.json');c['higher_control_layout_review_sha256']='0'*64
  with self.assertRaises(Exception):h.validate_control_layout(c,a)
 def test_changed_layout_lineage_rejected(self):
  from unittest.mock import patch
  c=a.f.load_json(ROOT/'contract.json');original=a.f.load_json
  def load(path):
   row=original(path)
   if Path(path)==ROOT/'locks/higher-control-layout-repair.json':row['preserved_control_count']=22
   return row
  with patch.object(a.f,'load_json',side_effect=load):
   with self.assertRaises(Exception):h.validate_control_layout(c,a)
