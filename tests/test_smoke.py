"""Source-only controls. The outer permanent audit hook rejects native/network events."""
import re,ctypes,copy,hashlib,importlib.util,json,os,pathlib,socket,subprocess,sys,tempfile,unittest,urllib.request
ROOT=pathlib.Path(__file__).resolve().parents[1]
s=importlib.util.spec_from_file_location('root7_tested',ROOT/'root7_import_cut.py');d=importlib.util.module_from_spec(s);sys.modules[s.name]=d;s.loader.exec_module(d)
c=json.loads((ROOT/'smoke-contract.json').read_text())

class Controls(unittest.TestCase):
 def test_inactive(self):
  d.validate_contract(c)
  with self.assertRaises(d.f.Rejected):d.validate_contract(c,reviewed=True)
 def test_locked_distribution(self):d.validate_inputs(c)
 def test_ledger(self):
  names=d.command_order(c);self.assertEqual(len(names),790);self.assertEqual(len(set(names)),790)
  specs=[d.command_spec(c,pathlib.Path('/tmp/inactive'),n) for n in names]
  self.assertEqual(sum(s['requested_timeout_seconds'] for s in specs),118500)
  for s in specs:
   self.assertNotIn('--share-net',s['argv']);self.assertNotIn('MATHLIB_CACHE_DIR',s['env']);self.assertTrue(s['allowed_sessions'])
 def test_exact_part32_roots(self):
  root=pathlib.Path('/tmp/inactive')
  for name,mode in [('compile-original-'+d.PART32,'original'),('check-original-'+d.PART32,'original'),('compile-'+d.PART32,'candidate'),('check-'+d.PART32,'candidate')]:
   spec=d.command_spec(c,root,name);self.assertEqual(spec['env']['LEAN_PATH'],str(root/('view-'+mode))+':'+str(root/'runtime/lib/lean'));self.assertNotIn(str(root/'objects'),spec['argv'])
 def test_reject_unknown_commands(self):
  for name in ['cache-get','compile-SpectreFinite.Bad','compile-fixture-bad','check-interface-bad']:
   with self.assertRaises(d.f.Rejected):d.command_spec(c,pathlib.Path('/tmp/inactive'),name)
 def test_command_mutations(self):
  root=pathlib.Path('/tmp/inactive');row=d.command_spec(c,root,'compile-'+d.PART32);row.pop('allowed_sessions');row.update(new_sessions_explicitly_allowed=True,limits={k:d.LIMITS[k] for k in ['address_space_bytes','rss_tree_bytes','max_created_file_bytes']},max_log_bytes=1024**2,effective_timeout_seconds=180)
  d.validate_command_spec(c,root,row)
  for key,value in [('argv',row['argv']+['--share-net']),('requested_timeout_seconds',181),('env',{}),('new_sessions_explicitly_allowed',False),('effective_timeout_seconds',True)]:
   bad=copy.deepcopy(row);bad[key]=value
   with self.assertRaises(d.f.Rejected):d.validate_command_spec(c,root,bad)
 def test_typed_safety(self):
  row=dict(timed_out=False,log_overflow=False,memory_exceeded=False,surviving_children=False,process_group_empty=True,descendants_empty=True,escaped_descendants=False,new_sessions_explicitly_allowed=True,exit_code=0)
  self.assertTrue(d.d.clean_command(row))
  for key in row:
   bad=dict(row);bad[key]='false'
   with self.assertRaises(d.f.Rejected):d.d.clean_command(bad)
 def test_exact_source_extraction(self):
  with tempfile.TemporaryDirectory() as tmp:
   work=pathlib.Path(tmp);d.a.extract_owned_sources(ROOT/'owned-sources.tar.gz',work/'source-input',c);owned=d.validate_graph(c,work);self.assertEqual(len(owned),388)
   for mode,count in [('original',325),('candidate',286)]:self.assertEqual(len(c['prerequisite_views'][mode]),count)
 def test_graph_mutations(self):
  with tempfile.TemporaryDirectory() as tmp:
   work=pathlib.Path(tmp);d.a.extract_owned_sources(ROOT/'owned-sources.tar.gz',work/'source-input',c)
   bad=copy.deepcopy(c);bad['prerequisite_views']['candidate'][0]='Fake'
   with self.assertRaises(d.f.Rejected):d.validate_graph(bad,work)
 def test_interface_report(self):
  text=interface_text();r=d.parse_interface(c,text);self.assertEqual(len(r['declarations']),239)
  for bad in [text.replace('PART32_EXACT_COMPARISON_PASSED\t239','PART32_EXACT_COMPARISON_PASSED\t238'),text.replace('LOADED_CANDIDATE\t'+c['prerequisite_views']['candidate'][0],'LOADED_CANDIDATE\t'+d.PART32),text.replace('\ttheorem\t','\taxiom\t',1),text+'UNEXPECTED\n']:
   with self.assertRaises(d.f.Rejected):d.parse_interface(c,bad)
 def test_cover_report(self):
  d.parse_cover(c,cover_text())
  for text in ['COVER_AXIOMS_PASSED\t0\n','COVER_DECL\tX\ttheorem\tsorryAx\nCOVER_AXIOMS_PASSED\t1\n']:
   with self.assertRaises(d.f.Rejected):d.parse_cover(c,text)
 def test_permanent_guards(self):
  for action in [lambda:subprocess.run(['/bin/true']),lambda:socket.socket(),lambda:ctypes.CDLL(None),lambda:urllib.request.urlopen('https://example.com')]:
   with self.assertRaises(RuntimeError):action()
 def test_confirmed_syntax_regression(self):
  record=json.loads((ROOT/'provenance/SYNTAX_REPAIR.json').read_text())
  original=(ROOT/'provenance/ImportCut.predecessor.lean').read_text()
  candidate=(ROOT/'provenance/ImportCut.syntax-predecessor.lean').read_text()
  self.assertEqual(hashlib.sha256(original.encode()).hexdigest(),'d75112a6ff39a486ec2d6946577e1974edc135e66af43935f30cd008bba1187b')
  expected_loops=[('paired_recursor_rules','for xr, yr in x.rules, y.rules do','for xr in x.rules, yr in y.rules do',2),('paired_environment_subtraction','for d, r in delta, raw do','for d in delta, r in raw do',1),('paired_introduced_inventory','for x, y in a.introduced, b.introduced do','for x in a.introduced, y in b.introduced do',1)]
  self.assertEqual([(x['id'],x['old'],x['new'],x['count']) for x in record['replacements'][:3]],expected_loops)
  self.assertEqual([x['id'] for x in record['replacements'][3:]],['definition_literal_layout','recursor_literal_layout'])
  for row in record['replacements'][3:]:
   self.assertEqual(''.join(row['old'].split()),''.join(row['new'].split()))
   self.assertEqual(row['count'],1)
   self.assertIn(':= {\n',row['new'])
  expected=original
  for row in record['replacements']:
   self.assertEqual(expected.count(row['old']),row['count'])
   expected=expected.replace(row['old'],row['new'])
  self.assertEqual(candidate,expected)
  reverted=candidate
  for row in reversed(record['replacements']):
   self.assertEqual(reverted.count(row['new']),row['count'])
   reverted=reverted.replace(row['new'],row['old'])
  self.assertEqual(reverted,original)
  self.assertEqual(sum(x['count'] for x in record['replacements']),6)
  self.assertEqual(record['replacements'][-1]['diagnosed_old_lines'],[])
  stdout=(ROOT/'provenance/failed-api.stdout').read_bytes()
  self.assertEqual(len(stdout),891)
  self.assertEqual(hashlib.sha256(stdout).hexdigest(),'9f776f769ad26955b71898d079f663e3a7b3792955b33b34285f4e68dfe09b66')
  for pin in record['exact_pinned_evidence']:
   self.assertEqual(hashlib.sha256((ROOT/pin['path']).read_bytes()).hexdigest(),pin['sha256'])
  self.assertIn('for name in parts[parts.size-1].1.constNames, ci in parts[parts.size-1].1.constants do',(ROOT/'provenance/checker.lean').read_text())
  self.assertIn('for cname in data.constNames, cinfo in data.constants do',(ROOT/'provenance/Environment.lean').read_text())
  self.assertIn(':= {\n  name := name,\n  levelParams := levelParams,',(ROOT/'provenance/Declaration.lean').read_text())
  scan=json.loads((ROOT/'provenance/SYNTAX_SCAN.json').read_text())
  self.assertEqual(scan['candidate_sha256'],hashlib.sha256(candidate.encode()).hexdigest())
  for row in scan['patterns'].values():
   self.assertEqual(list(re.finditer(row['regex'],candidate,re.M)),[])
   self.assertEqual(row['candidate_lines'],[])
  self.assertEqual(len(scan['patterns']['paired_bindings_before_in']['predecessor_lines']),4)
  self.assertEqual(len(scan['patterns']['inline_first_field_multiline_record']['predecessor_lines']),2)
  names=d.command_order(c)
  self.assertEqual(names[:3],['bwrap-preflight','read-only-committed-root-preflight','check-interface-api'])
  self.assertLess(names.index('check-interface-api'),names.index('compile-fixture-baseline'))
  self.assertLess(names.index('check-interface-fixtures'),names.index('compile-'+c['module_order'][0]))
 def test_confirmed_indexing_regression(self):
  record=json.loads((ROOT/'provenance/INDEXING_REPAIR.json').read_text())
  original=(ROOT/'provenance/ImportCut.syntax-predecessor.lean').read_text()
  candidate=(ROOT/'tools/ImportCut.lean').read_text()
  self.assertEqual(hashlib.sha256(original.encode()).hexdigest(),'291ebd3748073385fa5e48b1224eee4f0829f060302c8832a1112c8db283dfb2')
  self.assertEqual(hashlib.sha256(candidate.encode()).hexdigest(),'a2e53bd09fca4f68cc475025def11a01767b6b44650ad2c673f1e5a4209165cf')
  expected_rows=[('public_part','  let publicData := parts[0]!.1\n','  let some publicData := parts[0]?.map (·.1)\n    | throw <| IO.userError "MISSING_MODULE_PART"\n'),('private_part','  let privateData := parts[2]!.1\n','  let some privateData := parts[2]?.map (·.1)\n    | throw <| IO.userError "MISSING_MODULE_PART"\n')]
  self.assertEqual([(r['id'],r['old'],r['new']) for r in record['replacements']],expected_rows)
  expected=original
  for row in record['replacements']:
   self.assertEqual(row['count'],1)
   self.assertEqual(expected.count(row['old']),1)
   expected=expected.replace(row['old'],row['new'])
  self.assertEqual(candidate,expected)
  reverted=candidate
  for row in reversed(record['replacements']):
   self.assertEqual(reverted.count(row['new']),1)
   reverted=reverted.replace(row['new'],row['old'])
  self.assertEqual(reverted,original)
  prefix='  let parts ← readModuleDataParts fnames\n  require (parts.size == 3) "MISSING_MODULE_PART"\n'
  suffix='  require (privateData.constNames.size == privateData.constants.size) "MALFORMED_PRIVATE_INVENTORY"\n'
  self.assertIn(prefix+''.join(r['new'] for r in record['replacements'])+suffix,candidate)
  # Exact reconstruction above also locks the provider, filename order, private
  # imports, lifetime, declarations, comparisons, axiom checks and every fixture.
  self.assertIn('require (mFile == root / (moduleName.toString.replace "." "/" ++ ".olean")) "WRONG_MODULE_PROVIDER"',candidate)
  self.assertIn('let fnames := #[mFile, OLeanLevel.server.adjustFileName mFile, OLeanLevel.private.adjustFileName mFile]',candidate)
  scan=record['whole_helper_index_scan']
  self.assertEqual(re.findall(scan['bang_array_regex'],original),['[0]!','[2]!'])
  self.assertEqual(re.findall(scan['bang_array_regex'],candidate),[])
  self.assertEqual(candidate.count('todo.back!'),1)
  self.assertIn('while !todo.isEmpty do',candidate)
  self.assertEqual(record['size_requirement'],3)
  self.assertEqual(record['selected_indices'],[0,2])
  self.assertEqual(record['none_error'],'MISSING_MODULE_PART')
  self.assertEqual(record['non_native_bounds_cases'],[{'size':n,'accepted':n==3} for n in range(5)])
  # These finite arithmetic cases validate the retained size policy only; they
  # are explicitly not an execution or substitute implementation of Lean Option.
  self.assertTrue(all(0<=index<3 for index in record['selected_indices']))
  stdout=(ROOT/'provenance/indexing-failed-api.stdout').read_bytes()
  self.assertEqual(len(stdout),660)
  self.assertEqual(hashlib.sha256(stdout).hexdigest(),'9322c2ee0b86491e5d5216fb059265d35687b716337669467846fce2e46b9ef1')
  review=(ROOT/'provenance/INDEXING_FAILURE_REVIEW.json').read_bytes()
  self.assertEqual(hashlib.sha256(review).hexdigest(),'532501a5405d94d83f0cb1bfbe567885131d69556832d77fd1cbce05ae26097a')
  self.assertEqual(json.loads(review)['observations']['owned_modules_checked'],0)
  env=(ROOT/'provenance/Environment.lean').read_text()
  self.assertEqual(hashlib.sha256(env.encode()).hexdigest(),'6c90105aecc4d28efe94cc9aef1704c284e7a748b28270b5f8513d2562331e43')
  self.assertIn('self.parts[0]?.map (·.1)',env)
  self.assertIn('self.parts[level.ctorIdx]?.map (·.1)',env)
  names=d.command_order(c)
  self.assertEqual(names[:10],['bwrap-preflight','read-only-committed-root-preflight','check-interface-api',*['compile-fixture-'+v for v in ['baseline','identical','value','type','axiom','inventory']],'check-interface-fixtures'])
  self.assertEqual(len(names),790)
  self.assertEqual(c['sum_command_timeout_seconds'],118500)
  self.assertIn('compare (root / "baseline") (root / "identical") runtime `Fixture false',candidate)
  self.assertIn('let a ← load left runtime moduleName',candidate)

 def test_actual_loop_synthetic(self):
  # Runs actual extraction, graph/view copies, 388 compile/check admission loops,
  # receipt validation and collection. Only native/acquisition/git/activation seams
  # are synthetic. It proves controller paths, never Lean typing or kernel validity.
  with tempfile.TemporaryDirectory() as tmp:
   work=pathlib.Path(tmp)/'run';cc=copy.deepcopy(c);cc['review_status']='reviewed_for_execution';cc['independent_driver_review_sha256']='1'*64
   prior=(d.validate_inputs,d.a.git_capture,d.d.acquire_runtime,d.f.run_process,d.d.revalidate_runtime,d.a.RUNTIME_INVENTORY_SHA)
   oldenv={k:os.environ.get(k) for k in ['GITHUB_REF','GITHUB_SHA']}
   os.environ.update(GITHUB_REF='refs/heads/'+cc['publication_branch'],GITHUB_SHA='fixture')
   def native(argv,**kw):
    name=kw['stdout'].name[:-7];out=b''
    if name.startswith('compile-'):
     if name.startswith('compile-fixture-'):module='Fixture';stage=work/'fixture-objects'/name[len('compile-fixture-'):]
     elif name.startswith('compile-original-'):module=d.PART32;stage=work/'original-output'
     else:module=name[len('compile-'):];stage=work/'quarantine'/module
     for p in d.a.module_outputs(module):
      q=stage/p;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(('SYNTHETIC NOT LEAN '+name+' '+p).encode())
    elif name=='check-interface-api':out=b'INTERFACE_API_SELF_TEST_PASSED\n'
    elif name=='check-interface-fixtures':out=b'SOURCE_FIXTURES_PASSED\t1-positive-4-negative\n'
    elif name=='check-interface-part32':out=interface_text().encode()
    elif name=='check-cover-axioms':out=cover_text().encode()
    kw['stdout'].write_bytes(out);kw['stderr'].write_bytes(b'')
    return dict(exit_code=0,timed_out=False,log_overflow=False,memory_exceeded=False,surviving_children=False,process_group_empty=True,descendants_empty=True,escaped_descendants=False,new_sessions_explicitly_allowed=True)
   def runtime(work,env,command):
    runtime=work/'runtime';files={}
    for m in cc['runtime_roots']:
     p=runtime/'lib/lean'/(m.replace('.','/')+'.olean');p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(('SYNTHETIC '+m).encode());files[p.relative_to(runtime).as_posix()]={'bytes':p.stat().st_size,'sha256':d.f.file_sha(p),'mode':0o644}
    inv={'files':files,'symlinks':{}};d.a.write_json(work/'evidence/runtime-inventory.json',inv);d.a.RUNTIME_INVENTORY_SHA=d.f.sha(d.f.json_bytes(inv));env.update(d.a.safe_env(runtime,work/'home',work/'tmp'));env['LEAN_PATH']=str(work/'objects')+':'+str(runtime/'lib/lean')
    command('bwrap-preflight');command('read-only-committed-root-preflight');d.a.write_json(work/'evidence/read-only-boundary-preflight.json',{'status':'READ_ONLY_PREDECESSOR_WRITES_CHMOD_AND_NAMESPACE_CREATION_REJECTED','quarantine_write_allowed':True,'fixture_sha256':d.f.sha(b'IMMUTABLE_BOUNDARY_FIXTURE_ONLY\n'),'not_a_research_proof':True});return runtime
   class Watch:
    deadline=d.time.monotonic()+7200;in_command=False;expired=False
    def check(self):pass
    def failure_receipt_grace(self):pass
   try:
    d.validate_inputs=lambda c:None;d.a.git_capture=lambda root,*args:b'fixture\n' if args[0]=='rev-parse' else b'';d.d.acquire_runtime=runtime;d.f.run_process=native;d.d.revalidate_runtime=lambda *args:None
    digest=d.f.file_sha(ROOT/'smoke-contract.json');d.run(cc,digest,work,Watch());self.assertEqual(d.f.load_json(work/'evidence/result.json')['status'],d.SUCCESS)
    d.d.collect(cc,digest,work,Watch());self.assertTrue(d.f.load_json(work/'upload/collection.json')['smoke_acceptance_evidence_complete'])
    bad=d.f.load_json(work/'evidence/part32-views.json');bad['candidate']['prerequisite_modules'].append(d.PART32);d.a.write_json(work/'evidence/part32-views.json',bad)
    with self.assertRaises(d.f.Rejected):d.verify_success(cc,digest,work/'evidence',work)
   finally:
    d.validate_inputs,d.a.git_capture,d.d.acquire_runtime,d.f.run_process,d.d.revalidate_runtime,d.a.RUNTIME_INVENTORY_SHA=prior
    for k,v in oldenv.items():
     if v is None:os.environ.pop(k,None)
     else:os.environ[k]=v

def interface_text():
 lines=['DECL\t'+r['name']+'\t'+r['kind']+'\t' for r in c['explicit_part32_declarations']]
 for mode in ['original','candidate']:
  lines+=['LOADED_'+mode.upper()+'\t'+m for m in c['prerequisite_views'][mode]+c['runtime_roots']]
 return '\n'.join(lines+['PART32_EXACT_COMPARISON_PASSED\t239'])+'\n'

def cover_text():
 return '\n'.join(['COVER_DECL\t'+r['name']+'\t'+r['kind']+'\t' for r in c['explicit_cover_declarations']]+['COVER_AXIOMS_PASSED\t213'])+'\n'

if __name__=='__main__':unittest.main()
