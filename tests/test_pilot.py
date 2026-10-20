import ast,copy,hashlib,importlib.util,json,shutil,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('pilot',ROOT/'domains_fast_pilot.py');p=importlib.util.module_from_spec(spec);spec.loader.exec_module(p)
C=json.loads((ROOT/'smoke-contract.json').read_text())
class InertControls(unittest.TestCase):
 def test_synthetic_full_controller_and_receipts(self):
  spec=importlib.util.spec_from_file_location('synthetic_loop',ROOT/'tests/synthetic_loop.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
  with tempfile.TemporaryDirectory() as td:self.assertEqual(m.exercise(p,C,Path(td)),{'synthetic_only':True,'commands':779,'actual_native_executions':0,'actual_project_compilations':0})
 def test_actual_wrong_table_capture(self):
  root=Path('/home/runner/work/_temp/palomar-domains-fast-pilot');out=(ROOT/'provenance/negative-control.stdout').read_bytes();err=(ROOT/'provenance/negative-control.stderr').read_bytes();r=json.loads((ROOT/'provenance/negative-control-command.json').read_text())
  self.assertEqual(len(out),207);self.assertEqual(hashlib.sha256(out).hexdigest(),'4c336872ee5b0b689bc75ae6508abfb79f3d57190e7f72125934858c8c15c704');self.assertEqual(err,b'');p.validate_wrong_table_failure(root,r,out,err)
 def test_wrong_table_diagnostic_negatives(self):
  root=Path('/home/runner/work/_temp/palomar-domains-fast-pilot');out=(ROOT/'provenance/negative-control.stdout').read_bytes();r=json.loads((ROOT/'provenance/negative-control-command.json').read_text())
  bad=[b'',out+out,out.replace(b':11:59:',b':12:59:'),out.replace(b':11:59:',b':11:60:'),out.replace(b'fixture-wrong',b'fixture-candidate'),out.replace(b'PilotBridge.lean',b'Fixture.lean'),out.replace(b'Fin 2',b'Fin 3'),out.replace(b'originalFast v = Fast v',b'Fast v = originalFast v'),out.replace(b'Tactic',b'tactic'),out.replace(b'`decide`',b"'decide'"),out.replace(b'is false',b'is true'),out.rstrip(b'\n'),out.replace(b'\n',b'\r\n'),out.replace(b'\n',b'\r'),b'warning: extra\n'+out,out+b'error: extra\n',out+b'\n']
  for value in bad:self.assertRaises(Exception,p.validate_wrong_table_failure,root,r,value,b'')
  for err in [b'\n',b'error: extra\n',out]:self.assertRaises(Exception,p.validate_wrong_table_failure,root,r,out,err)
  self.assertRaises(Exception,p.validate_wrong_table_failure,root,r,b'',out)
  self.assertRaises(Exception,p.validate_wrong_table_failure,root,r,bytearray(out),b'')
  self.assertRaises(Exception,p.validate_wrong_table_failure,Path('/wrong-root'),r,out,b'')
 def test_wrong_table_resource_and_receipt_negatives(self):
  root=Path('/home/runner/work/_temp/palomar-domains-fast-pilot');out=(ROOT/'provenance/negative-control.stdout').read_bytes();r=json.loads((ROOT/'provenance/negative-control-command.json').read_text())
  for key,value in [('name','compile-fixture-candidate-compile-bridge'),('exit_code',0),('exit_code',2),('exit_code',-9),('exit_code',True),('exit_code','1'),('exit_code',1.0),('capture_status','excluded_unsafe_native_result'),('timed_out',True),('memory_exceeded',True),('log_overflow',True),('surviving_children',True),('process_group_empty',False),('descendants_empty',False),('new_sessions_explicitly_allowed',False),('timed_out',0)]:
   altered=copy.deepcopy(r);altered[key]=value;self.assertRaises(Exception,p.validate_wrong_table_failure,root,altered,out,b'')
 def test_only_two_shared_diagnostic_gate_replacements(self):
  sites=json.loads((ROOT/'provenance/DIAGNOSTIC_REPAIR.json').read_text());text=(ROOT/'domains_fast_pilot.py').read_text();old=(ROOT/'provenance/domains_fast_pilot.predecessor.py').read_text()
  self.assertEqual(text.count('def validate_wrong_table_failure('),1);self.assertEqual(text.count('validate_wrong_table_failure(work,r,'),3)
  for old_key,new_key in [('old_runtime_gate','new_runtime_gate'),('old_terminal_gate','new_terminal_gate')]:
   self.assertEqual(text.count(sites[new_key]),1);text=text.replace(sites[new_key],sites[old_key],1)
  self.assertEqual(text.count(sites['inserted_helper']),1);text=text.replace(sites['inserted_helper'],'',1).replace(sites['new_branch'],sites['old_branch'])
  self.assertEqual(text,old);self.assertEqual(hashlib.sha256(old.encode()).hexdigest(),sites['predecessor_driver_sha256'])
 def test_canonical_active_serialization_and_driver_inputs(self):
  from unittest.mock import patch
  active=copy.deepcopy(C);active['review_status']='reviewed_for_execution';active['independent_driver_review_sha256']='0'*64
  encoded=p.f.json_bytes(active);self.assertEqual(encoded,(json.dumps(active,sort_keys=True,indent=2,allow_nan=False)+'\n').encode())
  with tempfile.TemporaryDirectory() as td:
   dest=Path(td)/'active';shutil.copytree(ROOT,dest);(dest/'smoke-contract.json').write_bytes(encoded);workflow=dest/p.WORKFLOW;text=workflow.read_text();current_active=C['review_status']=='reviewed_for_execution';current_token=hashlib.sha256(p.f.json_bytes(C)).hexdigest() if current_active else '0'*64;current_guard='    if: ${{ true }}\n' if current_active else '    if: ${{ false }}\n';self.assertEqual(text.count('--contract-sha256 '+current_token),2);self.assertEqual(text.count(current_guard),1);workflow.write_text(text.replace('--contract-sha256 '+current_token,'--contract-sha256 '+hashlib.sha256(encoded).hexdigest()).replace(current_guard,'    if: ${{ true }}\n'))
   with patch.object(p,'ROOT',dest):p.validate_contract(active,True);p.validate_inputs(active)
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
