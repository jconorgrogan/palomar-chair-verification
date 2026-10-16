import copy,hashlib,importlib.util,json,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('probe_async_collector_fixture',ROOT/'probe_async.py');p=importlib.util.module_from_spec(spec);sys.modules[spec.name]=p;spec.loader.exec_module(p)
spec=importlib.util.spec_from_file_location('collector_async_fixture',ROOT/'collect_async_evidence.py');c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
def write(q,x):q.write_text(json.dumps(x,sort_keys=True,indent=2)+'\n')
class CollectorTests(unittest.TestCase):
    def fixture(self,e,default=False):
        contract=c.load(ROOT/'contract.json');e.mkdir();(e/'logs').mkdir()
        # Inert synthetic inventories exercise receipt logic without live artifacts.
        write(e/'runtime-inventory.json',{'files':{'lib/lean/Init.olean':{'bytes':1,'sha256':'a'*64}}})
        contract=copy.deepcopy(contract);contract['official_lean_inventory_sha256']=c.sha(e/'runtime-inventory.json')
        write(e/'source-extraction.json',{'archive':{'sha256':'cb50e75e182ecb21dd428b30a47eafed4af383ecb048ba92c0c2611dae2287c4'},'source_file_count':2481,'all_source_pins_verified':True,'exact_source_tree':True})
        target=next(x for x in c.load(ROOT/'baseline/locks/owned-sources.json')['sources'] if x['module']==p.TARGET)
        required={x['module']:x for x in c.load(ROOT/'baseline/locks/required-modules.json')['modules']};cache={};imports=[]
        for dep in target['ordered_imports']:
            lock=required[dep];stem='lib/lean/'+dep.replace('.','/');suffixes=['.olean','.ilean']+(['.olean.server','.olean.private','.ir.sig','.ir'] if lock['modern_module'] else [])
            companions={stem+x:{'bytes':1,'sha256':'b'*64} for x in suffixes};cache.setdefault(lock['package'],{'files':{}})['files'].update(companions)
            imports.append({'module':dep,'provider':'explicitly_trusted_official_cache','source_sha256':lock['sha256'],'companions':companions})
        imports.append({'module':'Init','provider':'official_runtime','object_sha256':'a'*64})
        write(e/'cached-build-inventory.json',cache)
        r={'schema':contract['schema'],'status':c.SUCCESS,'complete_evidence':True,'proof_certified':False,'conditional_endpoint_replay_completed':False,'final_C_proof_certified':False,'unconditional_monotile_proof_certified':False,'contract_sha256':c.sha(ROOT/'contract.json'),'baseline_contract_sha256':p.BASE_CONTRACT_SHA,'source_sha256':p.TARGET_SHA,'producer_work':contract['work_root'],'runtime_inventory_sha256':c.sha(e/'runtime-inventory.json'),'cached_build_inventory_sha256':c.sha(e/'cached-build-inventory.json'),'source_extraction_receipt_sha256':c.sha(e/'source-extraction.json'),'source_archive_sha256':'cb50e75e182ecb21dd428b30a47eafed4af383ecb048ba92c0c2611dae2287c4','cause_proven':False,'baseline_reproduced':not default,'profiles':{}}
        cmds=[]
        for spec in p.expected_command_specs(contract['work_root'],default):
            x={**spec,'exit_code':0,'timed_out':False,'memory_exceeded':False,'log_overflow':False,'surviving_children':False,'process_group_empty':True,'descendants_empty':True,'escaped_descendants':spec['allow_new_sessions'],'new_sessions_explicitly_allowed':spec['allow_new_sessions'],'limits':{'address_space_bytes':12*p.GIB,'rss_tree_bytes':8*p.GIB,'max_created_file_bytes':512*1024**2},'address_space_bytes':12*p.GIB,'max_created_file_bytes':512*1024**2,'max_log_bytes':1048576,'elapsed_seconds':0.01,'peak_sampled_tree_rss_bytes':1024,'effective_timeout_seconds':spec['requested_timeout_seconds'],'timeout_seconds':spec['requested_timeout_seconds']}
            n=x['name'];out='';err=''
            if n=='compile-control-DefaultOptionControl':out='ASYNC_OPTION_CONTROL_DEFAULT_TRUE\n'
            if n=='compile-control-DisabledOptionControl':out='ASYNC_OPTION_CONTROL_DISABLED_FALSE\n'
            if n.startswith('audit-profile-'):out='ASYNC_TARGET_RAW_AUDIT_PASSED_NO_FINAL_THEOREM\n'
            if n=='compile-profile-default' and not default:x['exit_code']=134;err='libc++abi: terminating due to uncaught exception of type lean::exception: failed to create thread: Resource temporarily unavailable\n'
            for stream,data in [('stdout',out),('stderr',err)]:
                q=e/'logs'/(n+'.'+stream);q.write_text(data);x[stream+'_sha256']=c.sha(q)
            cmds.append(x)
        for name,extra in p.PROFILES:
            accepted=default or name=='async_off';i=next(i for i,x in enumerate(cmds) if x['name']=='compile-profile-'+name)
            row={'ordered_imports':imports,'profile':name,'source_sha256':p.TARGET_SHA,'extra_lean_arguments':extra,'compiler_command':i,'checker_command':i+1 if accepted else None,'audit_command':i+2 if accepted else None,'accepted':accepted,'status':'COMPILED_KERNEL_CHECKED_AND_AUDITED' if accepted else 'BASELINE_THREAD_ABORT_REPRODUCED'}
            if accepted:
                row['outputs']={p.TARGET.replace('.','/')+s:{'bytes':1,'sha256':hashlib.sha256(b'x').hexdigest()} for s in c.SUFFIXES}
                write(e/('profile-'+name+'-final-objects.json'),{'files':row['outputs'],'bytes':7});row['final_output_inventory_sha256']=c.sha(e/('profile-'+name+'-final-objects.json'))
            write(e/('profile-'+name+'.json'),row);row['receipt_sha256']=c.sha(e/('profile-'+name+'.json'));row['log_hashes']={q.name:c.sha(q) for q in (e/'logs').glob('*-profile-'+name+'.*')}
            write(e/('profile-'+name+'-frozen.json'),row);r['profiles'][name]=row
        self.refresh(e,r,cmds);return contract,r,cmds
    def refresh(self,e,r,cmds):
        (e/'commands.jsonl').write_text(''.join(json.dumps(x,sort_keys=True)+'\n' for x in cmds));r['command_count']=len(cmds);r['command_receipts_sha256']=c.sha(e/'commands.jsonl');r['complete_log_bytes']=sum(q.stat().st_size for q in (e/'logs').iterdir());write(e/'result.json',r);write(e/'diagnostic-ready.json',{'result_sha256':c.sha(e/'result.json'),'contract_sha256':c.sha(ROOT/'contract.json')})
    def test_accepts_exact_default_abort_and_success_sequences(self):
        for default in [False,True]:
            with self.subTest(default=default),tempfile.TemporaryDirectory() as td:
                e=Path(td)/'evidence';contract,_,_=self.fixture(e,default);c.verify_complete(e,contract,c.sha(ROOT/'contract.json'))
    def test_complete_argv_and_sequence_mutants(self):
        mutations=['insert_flag','wrong_output','wrong_cwd','wrong_path','missing_setup','extra_setup','wrong_control_option','missing_check','wrong_audit']
        for name in mutations:
            with self.subTest(name=name),tempfile.TemporaryDirectory() as td:
                e=Path(td)/'evidence';contract,r,cmds=self.fixture(e);i=next(i for i,x in enumerate(cmds) if x['name']=='compile-profile-async_off');a=cmds[i]['argv']
                if name=='insert_flag':a.insert(a.index('-o'),'-DmaxRecDepth=999')
                if name=='wrong_output':a[a.index('-o')+1]='/tmp/other.olean'
                if name=='wrong_cwd':cmds[i]['cwd']='/tmp'
                if name=='wrong_path':a[a.index('LEAN_PATH')+1]+=':/tmp'
                if name=='missing_setup':cmds.pop(2)
                if name=='extra_setup':cmds.insert(2,copy.deepcopy(cmds[2]))
                if name=='wrong_control_option':
                    x=next(x for x in cmds if x['name']=='compile-control-DisabledOptionControl');x['argv'].remove('-DElab.async=false')
                if name=='missing_check':cmds.pop(i+1)
                if name=='wrong_audit':cmds[i+2]['argv'][-1]='/tmp/other.lean'
                self.refresh(e,r,cmds)
                with self.assertRaises(Exception):c.verify_complete(e,contract,c.sha(ROOT/'contract.json'))
    def test_profile_output_map_mutant(self):
        with tempfile.TemporaryDirectory() as td:
            e=Path(td)/'evidence';contract,r,cmds=self.fixture(e);row=r['profiles']['async_off'];next(iter(row['outputs'].values()))['sha256']='0'*64
            base={k:v for k,v in row.items() if k not in ['receipt_sha256','log_hashes']};write(e/'profile-async_off.json',base);row['receipt_sha256']=c.sha(e/'profile-async_off.json');write(e/'profile-async_off-frozen.json',row);self.refresh(e,r,cmds)
            with self.assertRaises(Exception):c.verify_complete(e,contract,c.sha(ROOT/'contract.json'))
    def test_incomplete_marker_and_claim_mutants(self):
        for name in ['no_marker','changed_marker','unapproved_escape','raised_limit','false_proof_claim']:
            with self.subTest(name=name),tempfile.TemporaryDirectory() as td:
                e=Path(td)/'evidence';contract,r,cmds=self.fixture(e)
                if name=='unapproved_escape':cmds[2]['escaped_descendants']=True
                if name=='raised_limit':cmds[-1]['limits']['address_space_bytes']=16*p.GIB
                if name=='false_proof_claim':r['proof_certified']=True
                self.refresh(e,r,cmds)
                if name=='no_marker':(e/'diagnostic-ready.json').unlink()
                if name=='changed_marker':write(e/'diagnostic-ready.json',{})
                with self.assertRaises(Exception):c.verify_complete(e,contract,c.sha(ROOT/'contract.json'))
if __name__=='__main__':unittest.main()
