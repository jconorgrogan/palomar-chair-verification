import ast,copy,hashlib,importlib.util,json,sys,tempfile,types,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('continuation_collector_tests',ROOT/'ci/collect_evidence.py');collector=importlib.util.module_from_spec(spec);spec.loader.exec_module(collector)
tree=ast.parse((ROOT/'ci/cache_diagnostic.py').read_text())
class F:
    @staticmethod
    def need(ok,msg):
        if not ok:raise ValueError(msg)
NS={'f':F,'CONTINUATION_SCHEMA':'conditional-geometry-origin-continuation-v3','ASYNC_TARGET':'SpectreGeometry.PolygonProductKeyReferenceFinite','ASYNC_TARGET_SHA':'1bca6dbb7f17e7a897293c3cf8da9b5d686c02245ac5230be3b27c108953a45b'}
node=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='module_compile_arguments');exec(compile(ast.Module(body=[node],type_ignores=[]),'<reviewed-option-helper>','exec'),NS)
class SchedulingTests(unittest.TestCase):
    def fixture(self):return {'schema':NS['CONTINUATION_SCHEMA'],'module_compile_arguments':{NS['ASYNC_TARGET']:['-DElab.async=false']},'inputs':{'src/'+NS['ASYNC_TARGET'].replace('.','/')+'.lean':{'sha256':NS['ASYNC_TARGET_SHA']}}}
    def test_only_exact_target_receives_option(self):
        c=self.fixture();fn=NS['module_compile_arguments'];self.assertEqual(fn(c,NS['ASYNC_TARGET']),['-DElab.async=false'])
        for name in ['SpectreGeometry.Other','AuditConditionalEndpoints','AuditOrdinaryBridges','Init','cache-get']:
            with self.subTest(name=name):self.assertEqual(fn(c,name),[])
        a=fn(c,NS['ASYNC_TARGET']);a.append('bad');self.assertEqual(fn(c,NS['ASYNC_TARGET']),['-DElab.async=false'])
    def test_wrong_flags_scope_and_source_rejected(self):
        cases=[{}, {'Other':['-DElab.async=false']},{NS['ASYNC_TARGET']:['-DElab.async=true']},{NS['ASYNC_TARGET']:['-DElab.async=false','-s64']},{NS['ASYNC_TARGET']:['-DElab.async=false'],'Other':['-DElab.async=false']}]
        for row in cases:
            c=self.fixture();c['module_compile_arguments']=row
            with self.subTest(row=row),self.assertRaises(ValueError):NS['module_compile_arguments'](c,NS['ASYNC_TARGET'])
        c=self.fixture();next(iter(c['inputs'].values()))['sha256']='a'*64
        with self.assertRaises(ValueError):NS['module_compile_arguments'](c,NS['ASYNC_TARGET'])
    def test_legacy_argv_is_explicit_and_unchanged(self):
        c={'schema':'conditional-geometry-staged-replay-v2'};self.assertEqual(NS['module_compile_arguments'](c,NS['ASYNC_TARGET']),[])
        for c in [{},{'schema':'unknown'},{'schema':'conditional-geometry-staged-replay-v2','module_compile_arguments':{}}]:
            with self.subTest(c=c),self.assertRaises(ValueError):NS['module_compile_arguments'](c,NS['ASYNC_TARGET'])
    def test_only_owned_compile_ast_gets_option(self):
        main=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='main')
        calls=[n for n in ast.walk(main) if isinstance(n,ast.Call) and isinstance(n.func,ast.Name) and n.func.id=='module_compile_arguments']
        self.assertEqual(len(calls),1);call=calls[0];self.assertEqual(ast.unparse(call),'module_compile_arguments(contract, module)')
        assignments=[n for n in ast.walk(main) if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='argv' for t in n.targets) and call in list(ast.walk(n))]
        self.assertEqual(len(assignments),1);self.assertIn("'-Dcompiler.postponeCompile=false'",ast.unparse(assignments[0]));self.assertIn("'-o'",ast.unparse(assignments[0]))

class SchedulingCollectorTests(unittest.TestCase):
    def test_only_target_compiler_has_async_override(self):
        rows=[{'name':'compile-SpectreGeometry.PolygonProductKeyReferenceFinite','argv':['lean','-DElab.async=false','source.lean']},
              {'name':'check-SpectreGeometry.PolygonProductKeyReferenceFinite','argv':['leanchecker','module']},
              {'name':'compile-Other','argv':['lean','other.lean']},
              {'name':'audit-AuditConditionalEndpoints','argv':['lean','--run','audit.lean']},
              {'name':'cache-get','argv':['cache','get']}]
        collector.validate_module_scheduling_commands({},rows)
        for index in range(len(rows)):
            changed=copy.deepcopy(rows)
            if index==0:changed[index]['argv'].remove('-DElab.async=false')
            else:changed[index]['argv'].append('-DElab.async=false')
            with self.subTest(index=index),self.assertRaises(ValueError):collector.validate_module_scheduling_commands({},changed)
        for option in ['-DElab.async=true','-DElab.async=false=false']:
            changed=copy.deepcopy(rows);changed[0]['argv'][1]=option
            with self.subTest(option=option),self.assertRaises(ValueError):collector.validate_module_scheduling_commands({},changed)

class CertificateTests(unittest.TestCase):
    def fixture(self):
        ident={'repository':'jconorgrogan/palomar-chair-verification','run_id':'200','run_attempt':'1','workflow_commit':'2'*40};old={**ident,'run_id':'100','workflow_commit':'1'*40}
        stages={'F0_common':{'modules':['Example.Base'],'admitted_stages':[]},'F3_product_geometry':{'modules':['Example.Product'],'admitted_stages':['F0_common']},'F4_bridge_and_endpoint_joins':{'modules':['Example.Final'],'admitted_stages':['F0_common','F3_product_geometry']}}
        c={'schema':'conditional-geometry-origin-continuation-v3','stages':stages,'locked_origin_stages':['F0_common'],'original_stage_contract_sha256':'a'*64,'source_archive':{'sha256':'b'*64},'official_lean_inventory_sha256':'c'*64}
        origin={'identity':old,'stage_id':'F0_common','artifact_id':11};lineage=[{'stage_id':'F0_common','origin':origin,'receipt_sha256':'d'*64,'checked_module_receipts_sha256':'e'*64,'own_modules':['Example.Base']}]
        locked={'F0_common':{'origin':copy.deepcopy(origin),'receipt_sha256':'d'*64,'checked_module_receipts_sha256':'e'*64}}
        inv={m.replace('.','/')+s:{'bytes':1,'sha256':'f'*64} for m in ['Example.Base','Example.Product'] for s in ['.olean','.olean.private','.olean.server','.ilean','.ir.sig','.ir','.c']}
        return c,ident,lineage,locked,inv
    def make(self,values,stage='F3_product_geometry'):
        c,i,l,k,v=values;return collector.make_cross_origin_certificate(c,'9'*64,i,stage,{'interface':'fixed'},l,v,k)
    def test_separate_certificate_preserves_original_lineage(self):
        values=self.fixture();before=copy.deepcopy(values);out=self.make(values);self.assertEqual(values,before);self.assertFalse(out['fresh_in_one_run']);self.assertEqual(len(out['admissions']),1);self.assertEqual(out['admissions'][0]['producer_contract_sha256'],'a'*64)
        self.assertEqual(out['consumer_identity'],values[1]);self.assertEqual(out['admissions'][0]['origin'],values[2][0]['origin'])
    def test_exact_locked_lineage_mutants(self):
        for key,value in [('receipt_sha256','0'*64),('checked_module_receipts_sha256','0'*64),('own_modules',['Example.Other'])]:
            values=self.fixture();values[2][0][key]=value
            with self.subTest(key=key),self.assertRaises(ValueError):self.make(values)
        for key,value in [('artifact_id',12),('stage_id','F1_curved_existence')]:
            values=self.fixture();values[2][0]['origin'][key]=value
            with self.subTest(key=key),self.assertRaises(ValueError):self.make(values)
        for key in ['run_id','run_attempt','workflow_commit']:
            values=self.fixture();values[2][0]['origin']['identity'][key]='wrong'
            with self.subTest(key=key),self.assertRaises(ValueError):self.make(values)
    def test_missing_companion_and_duplicate_stage_rejected(self):
        values=self.fixture();values[4].pop('Example/Base.ir')
        with self.assertRaises(KeyError):self.make(values)
        values=self.fixture();values[2].append(copy.deepcopy(values[2][0]))
        with self.assertRaises(ValueError):self.make(values)
    def test_final_join_only_admits_current_f3(self):
        values=self.fixture();c,i,l,k,v=values;l.append({'stage_id':'F3_product_geometry','origin':{'identity':copy.deepcopy(i)},'receipt_sha256':'4'*64,'checked_module_receipts_sha256':'5'*64,'own_modules':['Example.Product']})
        out=self.make(values,'F4_bridge_and_endpoint_joins');self.assertEqual(len(out['admissions']),1)
        for key in ['run_id','run_attempt','workflow_commit']:
            mutant=copy.deepcopy(values);mutant[2][-1]['origin']['identity'][key]='wrong'
            with self.subTest(key=key),self.assertRaises(ValueError):self.make(mutant,'F4_bridge_and_endpoint_joins')
    def test_old_f3_or_diagnostic_stage_never_falls_back(self):
        values=self.fixture();values[2][0]['stage_id']='F3_product_geometry'
        with self.assertRaises(ValueError):self.make(values)
        values=self.fixture();values[2][0]['stage_id']='async_off'
        with self.assertRaises(ValueError):self.make(values)

class OriginReadinessTests(unittest.TestCase):
    def fixture(self,root):
        old=(ROOT/'origin/producer-contract.json').read_bytes();(root/'origin').mkdir();(root/'origin/producer-contract.json').write_bytes(old)
        c=json.loads((ROOT/'contract.json').read_text());lock=json.loads((ROOT/'origin/locked-origins.json').read_text())
        seed=copy.deepcopy(lock['stages']['F0_common'])
        for index,sid in enumerate(c['locked_origin_stages']):
            row=copy.deepcopy(seed);row['origin']['stage_id']=sid;row['origin']['producer_job_name']='conditional '+sid;row['origin']['artifact_name']='conditional-geometry-38914223883-1-'+sid+'-objects';row['origin']['artifact_id']+=index;row['origin']['producer_job_id']+=index;lock['stages'][sid]=row
        self.write_lock(root,c,lock)
        class LocalF(F):
            SHA256=__import__('re').compile(r'[0-9a-f]{64}')
            @staticmethod
            def pinned_load(path,digest):
                data=path.read_bytes();F.need(hashlib.sha256(data).hexdigest()==digest,'pin mismatch');return json.loads(data)
        ns={'f':LocalF,'ROOT':root,'CONTINUATION_SCHEMA':NS['CONTINUATION_SCHEMA'],'ORIGINAL_STAGE_CONTRACT_SHA':'cbba2b835ef2578ad4810068cab863918af442d5fa30abea5cafcfa78ce35a38','validate_diagnostic_profile':lambda _:None,'validate_stage_plan':lambda _:None,'transport':types.SimpleNamespace(validate_origin_lock=lambda _:None)}
        node=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='validate_continuation_origins');exec(compile(ast.Module(body=[node],type_ignores=[]),'<origin-readiness>','exec'),ns)
        return c,lock,ns['validate_continuation_origins']
    def write_lock(self,root,c,lock):
        data=(json.dumps(lock,sort_keys=True,indent=2)+'\n').encode();(root/'origin/locked-origins.json').write_bytes(data);row={'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()};c['origin_lock']={'path':'origin/locked-origins.json',**row};c['inputs']['origin/locked-origins.json']=row
    def test_complete_expected_origin_shape_and_source_identity(self):
        with tempfile.TemporaryDirectory() as td:
            c,lock,fn=self.fixture(Path(td));producer,rows=fn(c);self.assertEqual(set(rows),set(c['locked_origin_stages']));self.assertEqual(producer['source_archive'],c['source_archive'])
    def test_pending_or_extra_origin_rejected_before_workspace(self):
        for change in ['missing','extra']:
            with self.subTest(change=change),tempfile.TemporaryDirectory() as td:
                root=Path(td);c,lock,fn=self.fixture(root)
                if change=='missing':lock['stages'].pop('F1_curved_existence')
                else:lock['stages']['F3_product_geometry']=copy.deepcopy(lock['stages']['F0_common'])
                self.write_lock(root,c,lock)
                with self.assertRaises(ValueError):fn(c)
    def test_source_archive_interface_and_auditor_mutants(self):
        for field in ['source_archive','modules','stages','cache_roots','official_lean_inventory_sha256']:
            with self.subTest(field=field),tempfile.TemporaryDirectory() as td:
                c,lock,fn=self.fixture(Path(td));c[field]=None
                with self.assertRaises(ValueError):fn(c)
        for name in ['src/SpectreGeometry/PolygonProductKeyReferenceFinite.lean','locks/dependencies.json','locks/required-modules.json','auditors/AuditConditionalEndpoints.lean']:
            with self.subTest(name=name),tempfile.TemporaryDirectory() as td:
                c,lock,fn=self.fixture(Path(td));c['inputs'][name]['sha256']='0'*64
                with self.assertRaises(ValueError):fn(c)
    def test_exact_original_run_and_producer_contract_required(self):
        for key in ['run_id','run_attempt','workflow_commit','repository']:
            with self.subTest(key=key),tempfile.TemporaryDirectory() as td:
                root=Path(td);c,lock,fn=self.fixture(root);lock['stages']['F0_common']['origin']['identity'][key]='wrong';self.write_lock(root,c,lock)
                with self.assertRaises(ValueError):fn(c)
        with tempfile.TemporaryDirectory() as td:
            root=Path(td);c,lock,fn=self.fixture(root);lock['producer_contract_sha256']='0'*64;self.write_lock(root,c,lock)
            with self.assertRaises(ValueError):fn(c)

if __name__=='__main__':unittest.main()
