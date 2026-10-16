import ast,copy,hashlib,importlib.util,json,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('probe_async',ROOT/'probe_async.py');p=importlib.util.module_from_spec(spec);sys.modules[spec.name]=p;spec.loader.exec_module(p)
cs=importlib.util.spec_from_file_location('collect_async_evidence',ROOT/'collect_async_evidence.py');collector=importlib.util.module_from_spec(cs);cs.loader.exec_module(collector)
TREE=ast.parse((ROOT/'probe_async.py').read_text());MAIN=next(n for n in TREE.body if isinstance(n,ast.FunctionDef) and n.name=='main')
COMMAND=next(n for n in ast.walk(MAIN) if isinstance(n,ast.FunctionDef) and n.name=='command')
LOOP=next(n for n in ast.walk(MAIN) if isinstance(n,ast.For) and isinstance(n.target,ast.Tuple) and [x.id for x in n.target.elts]==['profile','extra'])
class Watchdog:
    in_command=False;expired=False
    def check(self):pass
    def failure_receipt_grace(self):pass
class DiagnosticTests(unittest.TestCase):
    def simulate(self,mode='abort',mutant=None,second_fail=False):
        with tempfile.TemporaryDirectory() as td:
            work=Path(td);runtime=work/'runtime';(runtime/'bin').mkdir(parents=True);(runtime/'lib/lean').mkdir(parents=True)
            for n in ['logs','evidence','home','tmp','quarantine','src','packages','auditor-objects']: (work/n).mkdir()
            controls=work/'controls';controls.mkdir();(controls/'AuditAsyncTarget.lean').write_text('')
            target=work/'src'/('SpectreGeometry/PolygonProductKeyReferenceFinite.lean');target.parent.mkdir();target.write_text('SOURCE')
            command_calls=[];last=[]
            def run(argv,**kw):
                name=kw['stdout'].stem;command_calls.append(name)
                result={'exit_code':0,'timed_out':False,'log_overflow':False,'memory_exceeded':False,'surviving_children':False,'process_group_empty':True,'descendants_empty':True,'escaped_descendants':True,'new_sessions_explicitly_allowed':True,'elapsed_seconds':.01,'cleanup_elapsed_seconds':0,'peak_sampled_tree_rss_bytes':1024}
                stdout='';stderr=''
                if name=='compile-profile-default' and mode=='abort':
                    result['exit_code']=134;stderr='libc++abi: terminating due to uncaught exception of type lean::exception: failed to create thread: Resource temporarily unavailable\n'
                    if mutant:result[mutant[0]]=mutant[1]
                elif name.startswith('compile-profile-'):
                    if second_fail and name.endswith('async_off'):result['exit_code']=1;stderr='ordinary error\n'
                    else:
                        out=Path(argv[argv.index('-o')+1]);stem=str(out).removesuffix('.olean')
                        for suffix in p.SUFFIXES if hasattr(p,'SUFFIXES') else p.b.SUFFIXES:Path(stem+suffix).write_bytes(b'FAKE INERT OBJECT '+suffix.encode())
                elif name.startswith('audit-profile-'):stdout='ASYNC_TARGET_RAW_AUDIT_PASSED_NO_FINAL_THEOREM\n'
                kw['stdout'].write_text(stdout);kw['stderr'].write_text(stderr);last.append(result);return result
            f=p.f;old=f.run_process;f.run_process=run
            result={'command_count':0,'complete_log_bytes':0,'profiles':{}}
            env=dict(p.__dict__);env.update(work=work,runtime=runtime,controls=controls,auditor_objects=work/'auditor-objects',
                deadline=p.time.monotonic()+100,commands=[],watchdog=Watchdog(),result=result,
                contract={'per_command_log_max_bytes':1024**2,'aggregate_log_max_bytes':64*1024**2,'owned_output_max_bytes':6*p.GIB,'minimum_free_disk_bytes':0},
                env={'LEAN_PATH':str(runtime/'lib/lean')},search=[],owned_rows={p.TARGET:{}},cache_rows={},
                build_core=lambda *a:None,direct_import_receipt=lambda *a:[],
                validate_session_policy=lambda *a:None)
            try:
                exec(compile(ast.Module(body=[COMMAND],type_ignores=[]),'<actual-command>','exec'),env)
                program=ast.Module(body=[LOOP],type_ignores=[])
                try:exec(compile(program,'<actual-profile-loop>','exec'),env);error=None
                except Exception as e:error=e
                snapshots={x.name:x.read_bytes() for x in (work/'evidence').glob('*') if x.is_file()}
                return command_calls,result,error,snapshots
            finally:f.run_process=old
    def test_clean_known_abort_then_checked_disabled(self):
        calls,r,error,files=self.simulate();self.assertIsNone(error,str(error));self.assertEqual(calls,['compile-profile-default','compile-profile-async_off','check-profile-async_off','audit-profile-async_off']);self.assertFalse(r['profiles']['default']['accepted']);self.assertTrue(r['profiles']['async_off']['accepted']);self.assertIn('profile-default-frozen.json',files)
    def test_successful_default_checked_before_disabled(self):
        calls,r,error,_=self.simulate(mode='success');self.assertIsNone(error,str(error));self.assertEqual(calls,['compile-profile-default','check-profile-default','audit-profile-default','compile-profile-async_off','check-profile-async_off','audit-profile-async_off'])
    def test_all_safety_failures_stop_before_second_profile(self):
        for mutation in [('timed_out',True),('memory_exceeded',True),('log_overflow',True),('surviving_children',True),('process_group_empty',False),('descendants_empty',False),('new_sessions_explicitly_allowed',False)]:
            with self.subTest(mutation=mutation):
                calls,_,error,_=self.simulate(mutant=mutation);self.assertIsNotNone(error);self.assertEqual(calls,['compile-profile-default'])
    def test_unexpected_baseline_exit_stops(self):
        calls,_,error,_=self.simulate(mutant=('exit_code',1));self.assertIsNotNone(error);self.assertEqual(calls,['compile-profile-default'])
    def test_disabled_failure_has_no_checker(self):
        calls,r,error,_=self.simulate(second_fail=True);self.assertIsNotNone(error);self.assertEqual(calls,['compile-profile-default','compile-profile-async_off']);self.assertFalse(r['profiles']['async_off']['accepted'])
    def test_source_and_profile_pins(self):
        c=json.loads((ROOT/'contract.json').read_text());p.validate_package(c)
        for key,value in [('target_sha256','0'*64),('target_bytes',4881),('aggregate_command_deadline_seconds',19201),('address_space_bytes',16*p.GIB),('compile_timeout_seconds',181),('maximum_parallel_jobs',2),('proof_certified',True),('profiles',[{'name':'default','extra_lean_arguments':['-DElab.async=false']}])]:
            with self.subTest(key=key):
                m=copy.deepcopy(c);m[key]=value
                with self.assertRaises(Exception):p.validate_package(m)
    def test_disk_and_combined_output_reserves(self):
        with tempfile.TemporaryDirectory() as td:
            work=Path(td)
            for n in ['auditor-objects','profile-default-objects','profile-async_off-objects','quarantine']:(work/n).mkdir()
            original_disk=p.shutil.disk_usage;original_inventory=p.checked_inventory
            try:
                p.shutil.disk_usage=lambda q:type('Disk',(),{'free':0})()
                with self.assertRaises(Exception):p.require_profile_disk_and_output_budget(work,{'minimum_free_disk_bytes':1,'owned_output_max_bytes':6*p.GIB})
                p.shutil.disk_usage=lambda q:type('Disk',(),{'free':2*p.GIB})()
                p.checked_inventory=lambda *a,**k:{'bytes':2*p.GIB,'files':{}}
                with self.assertRaises(Exception):p.require_profile_disk_and_output_budget(work,{'minimum_free_disk_bytes':1536*1024**2,'owned_output_max_bytes':6*p.GIB})
            finally:p.shutil.disk_usage=original_disk;p.checked_inventory=original_inventory
    def test_shared_implementations_unchanged(self):
        for name in ['sandbox','admit_quarantine','namespace_providers','verify_owned_final','checked_inventory','direct_import_receipt','HostDeadline']:
            self.assertIs(getattr(p,name),getattr(p.b,name))
if __name__=='__main__':unittest.main()
