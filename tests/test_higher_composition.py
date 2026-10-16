"""Inert data-only composition checks on exact production functions and AST slices."""
import ast,copy,hashlib,json,os,sys,tempfile,unittest
from pathlib import Path
from unittest.mock import patch
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'ci'))
import cache_diagnostic as a
h=a.higher
class ProfileTests(unittest.TestCase):
 def test_exact_helper_scope_and_pins(self):a.validate_diagnostic_profile(a.f.load_json(ROOT/'contract.json'))
 def test_wrong_helper_pin(self):
  c=a.f.load_json(ROOT/'contract.json');c['inputs']['auditors/HigherInspectorControl.lean']['sha256']='0'*64
  with self.assertRaises(Exception):a.validate_diagnostic_profile(c)
 def test_wrong_preflight_stages(self):
  c=a.f.load_json(ROOT/'contract.json');c['independent_auditor_preflight_stages']=['H5_higher_assembly']
  with self.assertRaises(Exception):a.validate_diagnostic_profile(c)
 def test_wrong_scope(self):
  c=a.f.load_json(ROOT/'contract.json');c['proof_scope']='all dimensions'
  with self.assertRaises(Exception):a.validate_diagnostic_profile(c)
 def test_wrong_reference_review(self):
  c=a.f.load_json(ROOT/'contract.json');c['higher_reference_static_review_sha256']='0'*64
  with self.assertRaises(Exception):a.validate_diagnostic_profile(c)
class CacheFilesystemTests(unittest.TestCase):
 def run_case(self,mutation=None):
  lock=a.f.load_json(ROOT/'locks/cache-extension.json')
  with tempfile.TemporaryDirectory() as d:
   work=Path(d);paths=[]
   for pin in a.f.load_json(ROOT/'locks/dependencies.json')['packages']:(work/'packages'/pin['name']/'.lake/build/lib/lean').mkdir(parents=True)
   for m,r in {**lock['extension_modules'],**lock['approved_bootstrap_modules']}.items():
    for suffix in r.get('companion_suffixes',lock['cached_modern_companion_suffixes']):
     p=work/'packages'/r['package']/'.lake/build/lib/lean'/(m.replace('.','/')+suffix);p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b'inert companion');paths.append(p)
   if mutation:mutation(work,paths)
   h.validate_extension_companion_files({},work,a)
 def test_regular_single_link_exact(self):self.run_case()
 def test_companion_symlink(self):
  def mutate(w,ps):p=ps[0];p.unlink();p.symlink_to(ps[1])
  with self.assertRaises(Exception):self.run_case(mutate)
 def test_companion_hardlink(self):
  def mutate(w,ps):p=ps[0];p.unlink();os.link(ps[1],p)
  with self.assertRaises(Exception):self.run_case(mutate)
 def test_parent_symlink(self):
  def mutate(w,ps):p=ps[0].parent;q=p.with_name(p.name+'-real');p.rename(q);p.symlink_to(q,target_is_directory=True)
  with self.assertRaises(Exception):self.run_case(mutate)
 def test_search_root_alias(self):
  def mutate(w,ps):
   root=w/'packages/mathlib/.lake/build/lib/lean';real=root.with_name('lean-real');root.rename(real);root.symlink_to(real,target_is_directory=True)
  with self.assertRaises(Exception):self.run_case(mutate)
 def test_missing_companion(self):
  with self.assertRaises(Exception):self.run_case(lambda w,ps:ps[0].unlink())
 def test_absent_zero_provider_root(self):self.run_case(lambda w,ps:(w/'packages/Cli/.lake/build/lib/lean').rmdir())
 def test_absent_zero_provider_build_tree(self):
  import shutil
  self.run_case(lambda w,ps:shutil.rmtree(w/'packages/Cli/.lake/build'))
 def test_absent_required_provider_root(self):
  with self.assertRaisesRegex(Exception,'required cache search root is absent: aesop'):self.run_case(lambda w,ps:(w/'packages/aesop/.lake/build/lib/lean').rmdir())
 def test_zero_provider_root_file(self):
  def mutate(w,ps):p=w/'packages/Cli/.lake/build/lib/lean';p.rmdir();p.write_bytes(b'not a directory')
  with self.assertRaises(Exception):self.run_case(mutate)
 def test_zero_provider_ancestor_file(self):
  def mutate(w,ps):p=w/'packages/Cli/.lake/build/lib';(p/'lean').rmdir();p.rmdir();p.write_bytes(b'not a directory')
  with self.assertRaises(Exception):self.run_case(mutate)
 def test_zero_provider_dangling_root(self):
  def mutate(w,ps):p=w/'packages/Cli/.lake/build/lib/lean';p.rmdir();p.symlink_to('absent-target',target_is_directory=True)
  with self.assertRaises(Exception):self.run_case(mutate)
 def test_zero_provider_existing_root_alias(self):
  def mutate(w,ps):p=w/'packages/Cli/.lake/build/lib/lean';p.rmdir();target=p.with_name('real');target.mkdir();p.symlink_to(target,target_is_directory=True)
  with self.assertRaises(Exception):self.run_case(mutate)
 def test_zero_provider_dangling_ancestor(self):
  def mutate(w,ps):p=w/'packages/Cli/.lake/build/lib';(p/'lean').rmdir();p.rmdir();p.symlink_to('absent-target',target_is_directory=True)
  with self.assertRaises(Exception):self.run_case(mutate)
 def test_bootstrap_provider_requires_root(self):
  original=a.f.load_json
  def read(path):
   r=original(path)
   if Path(path)==ROOT/'locks/cache-extension.json':r=copy.deepcopy(r);r['approved_bootstrap_modules']['Cache.Synthetic']={'package':'Cli','companion_suffixes':['.olean','.ilean']}
   return r
  with patch.object(a.f,'load_json',side_effect=read):
   import shutil
   with self.assertRaisesRegex(Exception,'required cache search root is absent: Cli'):self.run_case(lambda w,ps:shutil.rmtree(w/'packages/Cli/.lake/build/lib/lean'))
class RawReceiptTests(unittest.TestCase):
 def rows(self):
  rows=[]
  for i,target in enumerate(h.TARGETS):rows.append({'schema':'higher-physical-endpoint-audit-v1','status':'pass','mode':'higher-only','target':target,'module':'ClarkSeed.PhysicalDimensions','reference_module':'HigherPhysicalReference','reference_template':'HigherPhysicalReference.'+('ExpectedGeFive' if i==0 else 'ExpectedGeThreeNeFour'),'model_module':'SparseMonotiles.Model','model_definitions':['SparseMonotiles.'+n for n in ['Point','IsTiling','translate','IsPeriod','HasTiling','IsAperiodic','IsAperiodicMonotile']],'level_params':[],'explicit_binders':['d','hd'] if i==0 else ['d','hd','hne'],'explicit_hypotheses':['5 ≤ d'] if i==0 else ['3 ≤ d','d ≠ 4'],'raw_type_equal':True,'raw_model_equal':True,'closed_type_and_proof':True,'selected_declaration_ownership':True,'exact_reference_owned_set':True,'trust_level':0,'plugins_enabled':False,'extensions_loaded':False,'axioms':sorted(a.ALLOWED_AXIOMS)})
  return rows
 def text(self,rows):return '\n'.join([*(json.dumps(r) for r in rows),'HIGHER_PHYSICAL_ENDPOINT_AUDIT_PASSED'])+'\n'
 def test_exact_records(self):self.assertEqual(h.audit_output(self.text(self.rows()),a),self.rows())
 def test_missing_record(self):
  with self.assertRaises(Exception):h.audit_output(self.text(self.rows()[:1]),a)
 def test_extra_record(self):
  with self.assertRaises(Exception):h.audit_output(self.text(self.rows()+self.rows()[:1]),a)
 def test_wrong_marker(self):
  with self.assertRaises(Exception):h.audit_output(self.text(self.rows()).replace('_PASSED','_PENDING'),a)
 def test_control_labels_exact(self):h.validate_control_output('\n'.join(['PASS '+x for x in h.CONTROL_LABELS]+['HIGHER_INSPECTOR_CORE_CONTROL_PASSED'])+'\n',a)
 def test_control_label_missing(self):
  with self.assertRaises(Exception):h.validate_control_output('\n'.join(['PASS '+x for x in h.CONTROL_LABELS[1:]]+['HIGHER_INSPECTOR_CORE_CONTROL_PASSED']),a)
 def test_control_label_reordered(self):
  with self.assertRaises(Exception):h.validate_control_output('\n'.join(['PASS '+x for x in reversed(h.CONTROL_LABELS)]+['HIGHER_INSPECTOR_CORE_CONTROL_PASSED']),a)
def raw_mutant(key,value):
 def test(self):
  rows=self.rows();rows[1][key]=value
  with self.assertRaises(Exception):h.audit_output(self.text(rows),a)
 return test
for k,v in {'explicit_binders':['d','hne','hd'],'explicit_hypotheses':['2 ≤ d','d ≠ 4'],'model_definitions':['SparseMonotiles.HasTiling'],'axioms':['sorryAx'],'C_remains_explicit':True,'raw_type_equal':1,'plugins_enabled':True,'level_params':['u'],'reference_template':'Other.Expected'}.items():setattr(RawReceiptTests,'test_mutated_'+k,raw_mutant(k,v))
class ProductionFinalizationTests(unittest.TestCase):
 def fragment(self):
  tree=ast.parse((ROOT/'ci/cache_diagnostic.py').read_text());main=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='main')
  body=next(n.body for n in main.body if isinstance(n,ast.Try));start=next(i for i,n in enumerate(body) if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='audits' for t in n.targets));end=next(i for i,n in enumerate(body[start:],start) if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='final_owned' for t in n.targets))
  selected=body[start:end];self.assertEqual(len(selected),3)
  return compile(ast.fix_missing_locations(ast.Module(body=copy.deepcopy(selected),type_ignores=[])),'<exact-production-final-auditor-inventory>','exec')
 def run_case(self,mutation=None):
  with tempfile.TemporaryDirectory() as d:
   work=Path(d);maps={};names={'auditor-objects':['AuditHigherPhysicalEndpoints','HigherInspectorControl'],'reference-objects':['HigherPhysicalReference']}
   for root,modules in names.items():
    p=work/root;p.mkdir()
    for name in modules:
     for rel in a.module_outputs(name):(p/rel).write_bytes(('inert '+rel).encode())
    maps[root]=a.checked_inventory(p,maximum=64*1024**2)['files']
   (work/'auditors').mkdir()
   for name in [x for xs in names.values() for x in xs]:(work/'auditors'/(name+'.lean')).write_bytes(b'inert source, never executed')
   before=a.checked_inventory(work/'auditors',maximum=1024**2)
   def raw(*args):
    if mutation:mutation(work,maps)
    return {'higher_physical_endpoints':True}
   env=dict(a.__dict__);env.update(work=work,auditor_maps=maps,auditor_before=before,contract={},runtime=work/'runtime',search=[],env={},command=None,final_stage=True)
   with patch.object(h,'run_auditors',side_effect=raw):exec(self.fragment(),env)
 def test_exact_final_roots_and_sources(self):self.run_case()
 def test_auditor_mutates_inspector(self):
  with self.assertRaises(Exception):self.run_case(lambda w,m:(w/'auditor-objects/AuditHigherPhysicalEndpoints.olean').write_bytes(b'changed'))
 def test_auditor_mutates_control(self):
  with self.assertRaises(Exception):self.run_case(lambda w,m:(w/'auditor-objects/HigherInspectorControl.olean.private').write_bytes(b'changed'))
 def test_auditor_mutates_reference(self):
  with self.assertRaises(Exception):self.run_case(lambda w,m:(w/'reference-objects/HigherPhysicalReference.olean').write_bytes(b'changed'))
 def test_extra_helper_empty_directory(self):
  with self.assertRaises(Exception):self.run_case(lambda w,m:(w/'reference-objects/Shadow').mkdir())
 def test_extra_helper_file(self):
  with self.assertRaises(Exception):self.run_case(lambda w,m:(w/'auditor-objects/Unlisted.olean').write_bytes(b'extra'))
 def test_source_mutation(self):
  with self.assertRaises(Exception):self.run_case(lambda w,m:(w/'auditors/HigherPhysicalReference.lean').write_bytes(b'changed'))
 def test_source_extra(self):
  with self.assertRaises(Exception):self.run_case(lambda w,m:(w/'auditors/Extra.lean').write_bytes(b'extra'))
 def test_aggregate_helper_cap(self):
  with tempfile.TemporaryDirectory() as d:
   with self.assertRaises(Exception):h.verify_auditor_maps(Path(d),{'auditor-objects':{'a':{'bytes':40*1024**2}},'reference-objects':{'b':{'bytes':40*1024**2}}},a)
class PreflightIsolationTests(unittest.TestCase):
 def test_exact_preflight_roots(self):
  c=a.f.load_json(ROOT/'contract.json');work=Path('/review/work');runtime=work/'runtime';search=[str(work/'packages/mathlib/.lake/build/lib/lean')];specs=h.auditor_specs(c,work,runtime,search,a)
  self.assertEqual(len(specs),7)
  for row in specs[:4]:
   self.assertNotIn(str(work/'objects'),row['argv']);self.assertNotIn(str(work/'reference-objects'),row['argv']);self.assertNotIn(str(work/'packages'),row['argv'])
  for row in specs[4:6]:self.assertNotIn(str(work/'objects'),row['argv']);self.assertNotIn(str(work/'auditor-objects'),row['argv'])
  self.assertEqual([r['requested_timeout_seconds'] for r in specs],[180,120,180,120,180,120,600])
 def test_helper_flags_all_seven_companions(self):
  c=a.f.load_json(ROOT/'contract.json');specs=h.auditor_specs(c,Path('/review/work'),Path('/review/runtime'),[],a)
  for row in specs[:6:2]:
   for flag in ['-j1','-M4096','-Dcompiler.postponeCompile=false','-o','-i','-c']:self.assertEqual(row['argv'].count(flag),1)
class ActualLoopImportTests(unittest.TestCase):
 def run_case(self,mutation=None):
  sys.path.insert(0,str(ROOT/'tests'))
  from test_preserved_boundaries import ActualConditionalLoopTests
  def finalizer(prior,receipts,rows,work):
   c={'stages':{'H5_higher_assembly':{'modules':list(rows),'admitted_stages':[]}}}
   if mutation:mutation(receipts)
   h.validate_current_imports(c,'H5_higher_assembly',receipts,prior,rows,{},work/'runtime',a)
  ActualConditionalLoopTests().run_loop(finalizer=finalizer)
 def test_actual_final_module_imports_accept(self):self.run_case()
 def test_actual_final_module_missing_import_reject(self):
  with self.assertRaises(Exception):self.run_case(lambda rs:rs[-1]['ordered_imports'].clear())
 def test_actual_final_module_changed_import_reject(self):
  def mutate(rs):
   rs[-1]['ordered_imports']=copy.deepcopy(rs[-1]['ordered_imports']);next(iter(rs[-1]['ordered_imports'][0]['companions'].values()))['sha256']='0'*64
  with self.assertRaises(Exception):self.run_case(mutate)
class ActualPreflightLoopTests(unittest.TestCase):
 def run_case(self,mutation=None):
  with tempfile.TemporaryDirectory() as d:
   work=Path(d)
   for root in ['quarantine','auditor-objects','reference-objects','evidence','auditors','home','tmp']:(work/root).mkdir()
   c=a.f.load_json(ROOT/'contract.json');events=[]
   def command(name,argv,**kwargs):
    events.append(name);out=work/('log-'+str(len(events)));out.write_text('')
    if name.startswith('compile-'):
     module=name.removeprefix('compile-auditor-');staging=work/'quarantine'/module
     for rel in a.module_outputs(module):(staging/rel).write_bytes(('inert '+rel).encode())
     if module=='HigherInspectorControl':out.write_text('\n'.join(['PASS '+x for x in h.CONTROL_LABELS]+['HIGHER_INSPECTOR_CORE_CONTROL_PASSED'])+'\n')
    elif name=='check-auditor-HigherPhysicalReference' and mutation:mutation(work)
    return out,True
   with patch.object(a.shutil,'disk_usage',return_value=type('Disk',(),{'free':20*a.GIB})()):maps=h.prepare_auditors(c,work,work/'runtime',[],command,a)
   self.assertEqual(len(events),6);self.assertEqual(sum(len(r) for r in maps.values()),21)
 def test_actual_preflight_exact(self):self.run_case()
 def test_later_checker_mutates_inspector(self):
  with self.assertRaises(Exception):self.run_case(lambda w:(w/'auditor-objects/AuditHigherPhysicalEndpoints.olean').write_bytes(b'changed'))
 def test_later_checker_mutates_control(self):
  with self.assertRaises(Exception):self.run_case(lambda w:(w/'auditor-objects/HigherInspectorControl.olean').write_bytes(b'changed'))
 def test_later_checker_mutates_reference(self):
  with self.assertRaises(Exception):self.run_case(lambda w:(w/'reference-objects/HigherPhysicalReference.olean').write_bytes(b'changed'))
if __name__=='__main__':unittest.main()
