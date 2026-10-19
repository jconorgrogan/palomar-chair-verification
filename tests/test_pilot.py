import ast,copy,hashlib,importlib.util,json,shutil,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('pilot',ROOT/'domains_fast_pilot.py');p=importlib.util.module_from_spec(spec);spec.loader.exec_module(p)
C=json.loads((ROOT/'smoke-contract.json').read_text())
class InertControls(unittest.TestCase):
 def test_synthetic_full_controller_and_receipts(self):
  spec=importlib.util.spec_from_file_location('synthetic_loop',ROOT/'tests/synthetic_loop.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
  with tempfile.TemporaryDirectory() as td:self.assertEqual(m.exercise(p,C,Path(td)),{'synthetic_only':True,'commands':779,'actual_native_executions':0,'actual_project_compilations':0})
 def test_profile(self):p.validate_contract(C);p.validate_inputs(C)
 def test_python_syntax(self):
  for path in [ROOT/'domains_fast_pilot.py',ROOT/'tests/run_guarded.py',ROOT/'tests/test_pilot.py']:ast.parse(path.read_text())
 def test_inactive(self):
  self.assertRaises(Exception,p.validate_contract,C,True)
 def test_scope_mutations(self):
  for key,value in [('owned_module_count',369),('publication_branch','other'),('runtime_roots',['Init']),('restore_project_objects',True),('full_official_verification_claimed',True),('recorded_command_count',1)]:
   c=copy.deepcopy(C);c[key]=value;self.assertRaises(Exception,p.validate_contract,c)
 def test_case_mutations(self):
  for field,value in [('fin',38),('source_saving_bytes',1),('module','Other'),('export_roots',['Other'])]:
   c=copy.deepcopy(C);c['cases'][0][field]=value;self.assertRaises(Exception,p.validate_contract,c)
 def test_command_finite(self):
  plan=p.command_plan(C);names=p.command_order(C);self.assertEqual(len(names),len(set(names)));self.assertEqual(len(names),C['recorded_command_count']);self.assertEqual(sum(x['seconds'] for x in plan),C['sum_command_timeout_seconds'])
  self.assertLess(names.index('check-public-fixture'),names.index('compile-'+C['common_module_order'][0]));self.assertEqual(sum(x['kind']=='export' for x in plan),4);self.assertEqual(sum(x['kind']=='replay' for x in plan),4)
 def test_sandbox_cwd_and_isolation(self):
  w=Path('/tmp/inert-pilot-work')
  for name in p.command_order(C):
   s=p.command_spec(C,w,name);a=s['argv'];self.assertEqual(a[0],'/usr/bin/bwrap');self.assertIn('--unshare-all',a);self.assertNotIn('--share-net',a)
   mounts=[Path(a[i+2]) for i,x in enumerate(a) if x in ['--ro-bind','--bind']];cwd=Path(a[a.index('--chdir')+1]);self.assertTrue(any(cwd==m or cwd.is_relative_to(m) for m in mounts),(name,cwd,mounts))
   self.assertNotIn('GITHUB_TOKEN',s['env']);self.assertEqual(s['env']['LEAN_NUM_THREADS'],'1')
 def test_native_spec_mutation(self):
  w=Path('/tmp/inert-pilot-work');s=p.command_spec(C,w,'compile-export-small-original');r={**s,'new_sessions_explicitly_allowed':True,'limits':{k:p.LIMITS[k] for k in ['address_space_bytes','rss_tree_bytes','max_created_file_bytes']},'max_log_bytes':p.LIMITS['per_command_log_max_bytes'],'effective_timeout_seconds':180};p.validate_command_spec(C,w,r);r['argv']=r['argv']+['extra'];self.assertRaises(Exception,p.validate_command_spec,C,w,r)
 def test_exact_extraction_and_source_edits(self):
  with tempfile.TemporaryDirectory() as td:
   w=Path(td);p.a.extract_owned_sources(ROOT/'owned-sources.tar.gz',w/'source-input',C);p.validate_graph(C,w);shutil.copytree(w/'source-input/src',w/'src');r=p.source_controls(C,w);self.assertEqual(sum(x['exact_source_saving_bytes'] for x in r),5006)
   target=w/'src/SpectreFinite/RadiusThreeRoot2Part1.lean';target.chmod(0o644);target.write_text(target.read_text()+'\n-- unrelated change\n');self.assertRaises(Exception,p.source_controls,C,w)
 def test_bridges_preserve_original(self):
  for row in C['cases']:
   orig=(ROOT/'probes'/row['id']/'original/PilotBridge.lean').read_text();cand=(ROOT/'probes'/row['id']/'candidate/PilotBridge.lean').read_text();self.assertEqual(orig.split('theorem original_fast_equals_actual')[0],cand.split('theorem original_fast_equals_actual')[0]);self.assertIn('from by decide',cand);self.assertIn('  rfl',orig)
 def test_wrong_fixture_is_valid_table_alias(self):
  a=(ROOT/'fixtures/original/Fixture.lean').read_text();b=(ROOT/'fixtures/wrong/Fixture.lean').read_text();self.assertIn('| 0 => [0]',a);self.assertIn('| 0 => [1]',b);self.assertIn('some (Domains v)',b);self.assertIn('  rfl',b);self.assertEqual((ROOT/'fixtures/candidate/PilotBridge.lean').read_bytes(),(ROOT/'fixtures/wrong/PilotBridge.lean').read_bytes())
 def test_public_parser_strict(self):
  row=p.variant_rows(C)[0];lines=[]
  for d in row['declarations']:lines.append('PUBLIC\t'+d['name']+'\t'+d['kind']+'\t')
  for side in ['original','candidate']:
   for d in row['declarations']:lines.append('KERNEL\t'+side+'\t'+d['name']+'\t'+d['kind']+'\t')
   lines.append('LOADED\t'+side+'\tInit')
  lines.append('FAST_HEIGHT\tDomainAliasFixture.Fast\t1\t2')
  text='\n'.join(lines+['PUBLIC_INTERFACE_AXIOMS_PASSED\t3'])+'\n';p.parse_public(row,text)
  for bad in [text+'EXTRA\n',text+'LOADED\toriginal\tInit\n',text.replace('PASSED\t3','PASSED\t4'),text.replace('DomainAliasFixture.Domains\tdef','Missing\tdef',1),text.replace('KERNEL\toriginal','KERNEL\tother',1),text.replace('KERNEL\toriginal\tDomainAliasFixture.Domains\tdef','KERNEL\toriginal\tDomainAliasFixture.Domains\tinvalid',1),text.replace('KERNEL\toriginal\tDomainAliasFixture.Domains\tdef\t','KERNEL\toriginal\tDomainAliasFixture.Domains\tdef\tpropext',1)]:self.assertRaises(Exception,p.parse_public,row,bad)
 def test_bridge_parser_strict(self):
  row=p.variant_rows(C)[0];n=row['bridge_name'];good='BRIDGE_DECL\t'+n+'\ttheorem\tpropext\nBRIDGE_AXIOMS_PASSED\t'+n+'\n';p.parse_bridge(row,good)
  for bad in [good.replace('propext','sorryAx'),good.replace('propext','propext,propext'),good.replace('propext','propext,'),good+'BRIDGE_DECL\tOther\ttheorem\t\n',good+'EXTRA\n',good.replace(n,'Other')]:self.assertRaises(Exception,p.parse_bridge,row,bad)
 def test_unchanged_inherited_primitives(self):self.assertEqual(hashlib.sha256((ROOT/'inherited_primitives.py').read_bytes()).hexdigest(),p.PRIMITIVE_SHA)
 def test_rooted_export_arguments(self):
  w=Path('/tmp/inert-pilot-work')
  for row in C['cases']:
   for mode in ['original','candidate']:
    argv=p.command_spec(C,w,'compile-export-'+row['id']+'-'+mode)['argv'];self.assertEqual(argv[-4:],row['export_roots']);self.assertIn(str(w/'runtime/bin/leanexport'),argv)
    check=p.command_spec(C,w,'check-export-'+row['id']+'-'+mode)['argv'];self.assertEqual(check[-3:-1],['--silent','--from-export'])
if __name__=='__main__':unittest.main(verbosity=2)
