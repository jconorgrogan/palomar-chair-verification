"""Offline adversarial fixtures. No prior-run objects or remote actions are used."""
import copy, importlib.util, io, json, os, shutil, sys, tarfile, tempfile, unittest, urllib.error, zipfile
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

BASE=Path(__file__).resolve().parents[1]/'ci'
HERE=BASE
sys.dont_write_bytecode=True
for name,path in [('fresh_stage',BASE/'fresh_stage.py'),('conditional_transport',HERE/'conditional_transport.py')]:
    spec=importlib.util.spec_from_file_location(name,path); mod=importlib.util.module_from_spec(spec); sys.modules[name]=mod; spec.loader.exec_module(mod)
f=sys.modules['fresh_stage']; t=sys.modules['conditional_transport']
spec=importlib.util.spec_from_file_location('baseline_conditional',BASE/'cache_diagnostic.py'); baseline=importlib.util.module_from_spec(spec); spec.loader.exec_module(baseline)
# baseline loads its pinned fresh_stage; synchronize Rejected identity for tests.
f=baseline.f; t.f=f

def interface(cache,inv,runtime):
    native={package+'/'+name:row for package,v in inv.items() for name,row in v['files'].items() if name.endswith(('.so','.a','.dll','.dylib'))}
    return {'schema':'conditional-external-interface-v1','runtime_inventory_sha256':runtime,
            'required_cache_companion_rows_sha256':f.sha(f.json_bytes(cache)),
            'all_package_native_library_files_sha256':f.sha(f.json_bytes(native))}
api=SimpleNamespace(safe_env=baseline.safe_env,sandbox=baseline.sandbox,direct_import_receipt=baseline.direct_import_receipt,cache_interface_identity=interface)

class Fixture:
    def __init__(self,root):
        self.root=Path(root); self.work=self.root/'work'; self.work.mkdir(); self.objects=self.work/'objects'; self.objects.mkdir()
        self.runtime=self.work/'runtime'; (self.runtime/'lib/lean').mkdir(parents=True); (self.runtime/'lib/lean/Init.olean').write_bytes(b'official runtime fixture')
        self.produced=self.root/'produced'; self.produced.mkdir(); self.evidence=self.root/'evidence'; (self.evidence/'logs').mkdir(parents=True)
        self.identity={'repository':t.REPOSITORY,'run_id':'900','run_attempt':'2','workflow_commit':'a'*40}
        self.rows=[{'module':'Fixture.A','path':'src/Fixture/A.lean','sha256':'1'*64,'bytes':1,'ordered_imports':[],'implicit_Init':True},
                   {'module':'Fixture.B','path':'src/Fixture/B.lean','sha256':'2'*64,'bytes':1,'ordered_imports':['Fixture.A'],'implicit_Init':True}]
        self.contract={'stages':{'F0_common':{'modules':[r['module'] for r in self.rows],'admitted_stages':[],'needs':[]}},
            'cache_roots':[],'diagnostic_timeout_seconds':180,'check_timeout_seconds':120,'auditor_timeout_seconds':600,
            'per_command_log_max_bytes':1024**2,'aggregate_log_max_bytes':64*1024**2,'aggregate_command_deadline_seconds':19200,
            'source_archive':{'sha256':'b'*64,'source_bytes':2},'owned_module_count':2}
        self.runtime_inv={'files':{'lib/lean/Init.olean':{'bytes':24,'sha256':f.file_sha(self.runtime/'lib/lean/Init.olean')}}}
        self.write('runtime-inventory.json',self.runtime_inv); runtime_sha=f.file_sha(self.evidence/'runtime-inventory.json')
        self.meta={'identity':self.identity,'stage_id':'F0_common','stage_modules':[r['module'] for r in self.rows],
                   'admitted_stages':[],'contract_sha256':'c'*64,'interface_identity':interface({}, {},runtime_sha),
                   'producer_work':str(self.work),'runtime_inventory_sha256':runtime_sha,'predecessor_artifacts':[]}
        self.origin={'identity':self.identity,'stage_id':'F0_common','producer_job_name':'conditional F0_common','producer_conclusion':'success',
                     'artifact_name':'conditional-geometry-900-2-F0_common-objects','artifact_id':10,'producer_job_id':20,
                     'artifact_zip_sha256':'d'*64,'artifact_zip_bytes':100,'workflow_path':t.WORKFLOW_PATH,'workflow_id':30,'producer_job_log_sha256':'e'*64}
        self.expected={**self.meta,'contract':self.contract,'stage_rows':self.rows,'owned_rows':{r['module']:r for r in self.rows},
                       'cache_rows':{},'runtime':self.runtime,'cache_search':[],'producer_inventory':{},'origin':self.origin,'dependency_pins':[]}
        self.own={}
        for row in self.rows:
            for name in sorted(t.paths(row['module'])):
                p=self.produced/name; p.parent.mkdir(parents=True,exist_ok=True); p.write_bytes(('checked fixture '+name).encode())
                self.own[name]={'bytes':p.stat().st_size,'sha256':f.file_sha(p)}
        self.commands=[]
        for spec in t.command_specs(self.expected,api):
            for stream in ('stdout','stderr'): (self.evidence/'logs'/(spec['name']+'.'+stream)).write_bytes(b'')
            self.commands.append({**spec,'exit_code':0,'timed_out':False,'log_overflow':False,'memory_exceeded':False,'surviving_children':False,
                'process_group_empty':True,'descendants_empty':True,'escaped_descendants':False,'new_sessions_explicitly_allowed':spec['allow_new_sessions'],
                'effective_timeout_seconds':spec['requested_timeout_seconds'],'timeout_seconds':spec['requested_timeout_seconds'],
                'address_space_bytes':12*t.GIB,'max_created_file_bytes':512*1024**2,'max_log_bytes':1024**2,
                'limits':{'address_space_bytes':12*t.GIB,'rss_tree_bytes':8*t.GIB,'max_created_file_bytes':512*1024**2},
                'elapsed_seconds':0.1,'peak_sampled_tree_rss_bytes':0,'stdout_sha256':f.sha(b''),'stderr_sha256':f.sha(b'')})
        self.receipts=[]; checked=set(); prior={}
        for row in self.rows:
            module=row['module']; a=next(i for i,c in enumerate(self.commands) if c['name']=='compile-'+module)
            record={'module':module,'source_sha256':row['sha256'],'ordered_imports':api.direct_import_receipt(row,self.expected['owned_rows'],checked,prior,{},self.runtime),
                    'outputs':{n:self.own[n] for n in sorted(t.paths(module))},'compiler_command':a,'checker_command':a+1,
                    'checker_passed':True,'conditional_C_remains_explicit':True}
            self.receipts.append(record); prior.update(record['outputs']); checked.add(module)
        self.write('cached-build-inventory.json',{})
        self.write('interface-identity.json',self.meta['interface_identity'])
        self.write('imported-stages.json',[])
        self.write('source-extraction.json',{'schema':'authenticated-source-extraction-v1','archive':self.contract['source_archive'],'source_file_count':2,
            'source_bytes':2,'exact_source_tree':True,'all_source_pins_verified':True})
        self.write('fresh-owned-objects.json',{'files':self.own,'bytes':sum(r['bytes'] for r in self.own.values())})
        self.result={**{k:self.identity[k] for k in ('run_id','run_attempt','workflow_commit')},
            **{k:self.meta[k] for k in ('stage_id','stage_modules','admitted_stages','contract_sha256')},
            'status':'CHECKED_CONDITIONAL_STAGE_COMPLETED_C_EXPLICIT','complete_evidence':True,'conditional_C_remains_explicit':True,
            'final_C_proof_certified':False,'unconditional_monotile_proof_certified':False,'owned_objects_from_prior_runs':False,
            'checked_fresh_module_count':2,'checked_owned_module_count':2,'command_count':len(self.commands),'complete_log_bytes':0,
            'source_archive_sha256':self.contract['source_archive']['sha256'],'raw_audits':{}}
        self.count=0
    def write(self,name,value): (self.evidence/name).write_bytes(f.json_bytes(value))
    def seal(self):
        self.count+=1
        for name,rows in [('commands.jsonl',self.commands),('owned-modules.jsonl',self.receipts)]:
            (self.evidence/name).write_text(''.join(json.dumps(row,sort_keys=True)+'\n' for row in rows))
        for name,key in [('commands.jsonl','command_receipts_sha256'),('owned-modules.jsonl','owned_module_receipts_sha256'),
                         ('fresh-owned-objects.json','owned_output_inventory_sha256'),('runtime-inventory.json','runtime_inventory_sha256'),
                         ('cached-build-inventory.json','cached_build_inventory_sha256'),('source-extraction.json','source_extraction_receipt_sha256'),('interface-identity.json','interface_identity_sha256'),('imported-stages.json','imported_stages_sha256')]: self.result[key]=f.file_sha(self.evidence/name)
        self.write('result.json',self.result)
        self.bundle=self.root/('bundle'+str(self.count)); t.write_stage(self.produced,self.evidence,self.meta,self.bundle)
        self.extracted=self.root/('extracted'+str(self.count)); t.extract_stage(self.bundle,self.extracted)
        return self.extracted
    def admit(self): return t.admit_stage(self.extracted,expected=self.expected,objects=self.objects,prior={},checked=set(),api=api)

class TransportTests(unittest.TestCase):
    def setUp(self):
        self.disk=patch.object(t.shutil,'disk_usage',return_value=SimpleNamespace(free=100*t.GIB)); self.disk.start(); self.addCleanup(self.disk.stop)
        self.temp=tempfile.TemporaryDirectory(dir=HERE); self.fx=Fixture(self.temp.name)
    def tearDown(self): self.temp.cleanup()
    def reject(self):
        self.fx.seal()
        with self.assertRaises((ValueError,KeyError)): self.fx.admit()
        self.assertEqual(t.inventory(self.fx.objects,t.MAX_OWNED),{})
    def test_roundtrip_own_seven_and_single_root(self):
        self.fx.seal(); receipts,inv=self.fx.admit()
        self.assertEqual(len(receipts),2); self.assertEqual(inv,self.fx.own)
        self.assertFalse((self.fx.extracted/'objects').exists())
        self.assertTrue((self.fx.extracted/'receipt.json').is_file())
        self.assertTrue((self.fx.extracted/'evidence/result.json').is_file())
        self.assertTrue(all((self.fx.objects/n).stat().st_mode&0o222==0 for n in inv))
    def test_previous_run(self): self.fx.meta['identity']={**self.fx.identity,'run_id':'899'}; self.reject()
    def test_previous_attempt(self): self.fx.meta['identity']={**self.fx.identity,'run_attempt':'1'}; self.reject()
    def test_wrong_contract(self): self.fx.meta['contract_sha256']='f'*64; self.reject()
    def test_wrong_module_source(self): self.fx.receipts[0]['source_sha256']='f'*64; self.reject()
    def test_missing_checker(self): self.fx.receipts[0]['checker_passed']=False; self.reject()
    def test_nonadjacent_checker(self): self.fx.receipts[0]['checker_command']+=2; self.reject()
    def test_reordered_modules(self): self.fx.receipts.reverse(); self.reject()
    def test_duplicate_pair(self): self.fx.commands[-1]=copy.deepcopy(self.fx.commands[-3]); self.reject()
    def test_changed_compile_flag(self): self.fx.commands[-4]['argv'].append('--run'); self.reject()
    def test_writable_predecessor_root(self):
        row=self.fx.commands[-4]; i=row['argv'].index('--ro-bind',row['argv'].index(str(self.fx.work/'src'))+1); row['argv'][i]='--bind'; self.reject()
    def test_quarantine_on_lean_path(self):
        row=self.fx.commands[-4]; i=row['argv'].index('LEAN_PATH'); row['argv'][i+1]+=':'+str(self.fx.work/'quarantine/Fixture.A'); self.reject()
    def test_missing_process_cleanup(self): self.fx.commands[0]['descendants_empty']=False; self.reject()
    def test_session_escape_without_allow(self): self.fx.commands[2]['escaped_descendants']=True; self.reject()
    def test_session_permission_forged(self): self.fx.commands[2]['allow_new_sessions']=True; self.fx.commands[2]['new_sessions_explicitly_allowed']=True; self.reject()
    def test_profile_rss_change(self): self.fx.commands[-1]['max_rss_bytes']=16*t.GIB; self.reject()
    def test_profile_timeout_change(self): self.fx.commands[-1]['requested_timeout_seconds']=999; self.reject()
    def test_profile_effective_timeout_excess(self): self.fx.commands[-1]['effective_timeout_seconds']=999; self.reject()
    def test_direct_import_object_hash_mismatch(self): self.fx.receipts[1]['ordered_imports'][0]['companions']['Fixture/A.olean']['sha256']='f'*64; self.reject()
    def test_runtime_linkage_mismatch(self): self.fx.receipts[0]['ordered_imports'][0]['object_sha256']='f'*64; self.reject()
    def test_interface_mismatch(self): self.fx.meta['interface_identity']={**self.fx.meta['interface_identity'],'required_cache_companion_rows_sha256':'f'*64}; self.reject()
    def test_unconditional_claim(self): self.fx.result['unconditional_monotile_proof_certified']=True; self.reject()
    def test_failed_run_receipts_only(self): self.fx.result['status']='FAILED_OR_INCOMPLETE'; self.reject()
    def test_result_counts(self): self.fx.result['checked_owned_module_count']=3; self.reject()
    def test_logs_mutated(self):
        (self.fx.evidence/'logs/check-Fixture.A.stdout').write_bytes(b'changed'); self.reject()
    def test_extra_log_file(self): (self.fx.evidence/'logs/unlisted.stdout').write_bytes(b'extra'); self.reject()
    def test_link_in_evidence(self):
        (self.fx.evidence/'alias').symlink_to('result.json')
        with self.assertRaises(ValueError): self.fx.seal()
    def test_hardlink_in_objects(self):
        os.link(self.fx.produced/'Fixture/A.olean',self.fx.root/'hardlink')
        with self.assertRaises(ValueError): self.fx.seal()
    def test_missing_companion(self):
        (self.fx.produced/'Fixture/A.ir.sig').unlink()
        with self.assertRaises(ValueError): self.fx.seal()
    def test_changed_payload_after_extraction(self):
        self.fx.seal(); (self.fx.extracted/'objects/Fixture/A.c').write_bytes(b'corrupt')
        with self.assertRaises(ValueError): self.fx.admit()
        self.assertEqual(t.inventory(self.fx.objects,t.MAX_OWNED),{})
    def test_existing_root_extra(self):
        self.fx.seal(); (self.fx.objects/'unauthorized').write_bytes(b'bad')
        with self.assertRaises(ValueError): self.fx.admit()
    def test_disk_download_reserve(self):
        self.fx.seal()
        with patch.object(t.shutil,'disk_usage',return_value=SimpleNamespace(free=t.DISK_RESERVE)):
            with self.assertRaises(ValueError): self.fx.admit()
        self.assertEqual(t.inventory(self.fx.objects,t.MAX_OWNED),{})
    def test_disk_extract_reserve(self):
        self.fx.seal()
        with patch.object(t.shutil,'disk_usage',return_value=SimpleNamespace(free=t.DISK_RESERVE)):
            with self.assertRaises(ValueError): t.extract_stage(self.fx.bundle,self.fx.root/'lowdisk')
    def test_evidence_cap_separate(self):
        self.fx.seal()
        with self.assertRaises(ValueError): t.write_stage(self.fx.produced,self.fx.evidence,self.fx.meta,self.fx.root/'cap',evidence_maximum=1)
    def test_payload_cap(self):
        self.fx.seal()
        with self.assertRaises(ValueError): t.write_stage(self.fx.produced,self.fx.evidence,self.fx.meta,self.fx.root/'cap',maximum=1024)
    def _changed_tar(self,transform):
        self.fx.seal(); p=self.fx.bundle/'stage.tar'; p.write_bytes(transform(p.read_bytes()))
        desc=f.load_json(self.fx.bundle/'descriptor.json'); desc.update(archive_sha256=f.file_sha(p),archive_bytes=p.stat().st_size)
        (self.fx.bundle/'descriptor.json').write_bytes(f.json_bytes(desc))
        with self.assertRaises((ValueError,tarfile.TarError)): t.extract_stage(self.fx.bundle,self.fx.root/'malicious')
    def test_trailing_tar_payload(self): self._changed_tar(lambda b:b+b'ATTACK')
    def test_trailing_zero_record(self): self._changed_tar(lambda b:b+bytes(10240))
    def test_nonzero_tar_padding(self):
        def mutate(b):
            info=tarfile.TarInfo.frombuf(b[:512],'utf-8','strict'); i=512+info.size
            self.assertNotEqual(i%512,0); return b[:i]+b'x'+b[i+1:]
        self._changed_tar(mutate)
    def test_duplicate_tar_member(self):
        def mutate(b):
            info=tarfile.TarInfo.frombuf(b[:512],'utf-8','strict'); chunk=b[:512+((info.size+511)//512)*512]
            return chunk+chunk+b[len(chunk):]
        self._changed_tar(mutate)
    def test_tar_path_alias(self):
        def mutate(b):
            info=tarfile.TarInfo.frombuf(b[:512],'utf-8','strict'); info.name='./receipt.json'; return info.tobuf(format=tarfile.USTAR_FORMAT)+b[512:]
        self._changed_tar(mutate)
    def test_tar_symlink(self):
        def mutate(b):
            info=tarfile.TarInfo.frombuf(b[:512],'utf-8','strict'); info.type=tarfile.SYMTYPE; info.linkname='elsewhere'; return info.tobuf(format=tarfile.USTAR_FORMAT)+b[512:]
        self._changed_tar(mutate)
    def test_duplicate_json_keys(self):
        with self.assertRaises(ValueError): f.parse_json(b'{"files":{},"files":{}}')
    def test_zip_trailing_payload(self):
        self.fx.seal(); p=self.fx.root/'bad.zip'
        with zipfile.ZipFile(p,'w') as z:
            z.write(self.fx.bundle/'stage.tar','stage.tar'); z.write(self.fx.bundle/'descriptor.json','descriptor.json')
        with p.open('ab') as out: out.write(b'ATTACK')
        dest=self.fx.root/'zip-out'; dest.mkdir()
        with self.assertRaises(ValueError): t._extract_zip(p,dest,t.MAX_ARCHIVE)
    def test_zip_duplicate_member(self):
        p=self.fx.root/'bad.zip'
        with zipfile.ZipFile(p,'w') as z:
            z.writestr('stage.tar',b'a'); z.writestr('stage.tar',b'b')
        dest=self.fx.root/'zip-out'; dest.mkdir()
        with self.assertRaises(ValueError): t._extract_zip(p,dest,t.MAX_ARCHIVE)

    def test_zip_stored_deflated_and_streamed_roundtrip(self):
        self.fx.seal()
        class Streaming(io.BytesIO):
            def seekable(self): return False
            def seek(self,*args): raise io.UnsupportedOperation('streaming')
        for variant in range(3):
            data=Streaming() if variant==2 else io.BytesIO()
            with zipfile.ZipFile(data,'w',compression=zipfile.ZIP_STORED if variant==0 else zipfile.ZIP_DEFLATED) as z:
                z.writestr('stage.tar',(self.fx.bundle/'stage.tar').read_bytes())
                z.writestr('descriptor.json',(self.fx.bundle/'descriptor.json').read_bytes())
            p=self.fx.root/('good'+str(variant)+'.zip'); p.write_bytes(data.getvalue()); dest=self.fx.root/('unzipped'+str(variant)); dest.mkdir()
            t._extract_zip(p,dest,t.MAX_ARCHIVE)
            self.assertEqual((dest/'stage.tar').read_bytes(),(self.fx.bundle/'stage.tar').read_bytes())
    def test_zip_hidden_local_entry(self):
        p=self.fx.root/'hidden.zip'
        with zipfile.ZipFile(p,'w') as z:
            z.writestr('stage.tar',b'tar'); z.writestr('hidden',b'ATTACK'); z.writestr('descriptor.json',b'{}')
        with zipfile.ZipFile(p) as z: start=z.start_dir
        data=p.read_bytes(); cursor=start; records=[]
        while data[cursor:cursor+4]==b'PK\x01\x02':
            header=data[cursor:cursor+46]; values=t.struct.unpack('<4s6H3I5H2I',header); n,x,c=values[10:13]; end=cursor+46+n+x+c
            if data[cursor+46:cursor+46+n]!=b'hidden': records.append(data[cursor:end])
            cursor=end
        central=b''.join(records); eocd=t.struct.pack('<4s4H2IH',b'PK\x05\x06',0,0,2,2,len(central),start,0)
        p.write_bytes(data[:start]+central+eocd); dest=self.fx.root/'hidden-out'; dest.mkdir()
        with self.assertRaisesRegex(ValueError,'hidden ZIP local'): t._extract_zip(p,dest,t.MAX_ARCHIVE)
    def test_zip_local_central_name_mismatch(self):
        p=self.fx.root/'name.zip'
        with zipfile.ZipFile(p,'w') as z: z.writestr('stage.tar',b'tar'); z.writestr('descriptor.json',b'{}')
        data=p.read_bytes(); p.write_bytes(data[:30]+b'stale.tar'+data[39:]); dest=self.fx.root/'name-out'; dest.mkdir()
        with self.assertRaisesRegex(ValueError,'local/central name'): t._extract_zip(p,dest,t.MAX_ARCHIVE)
    def test_zip_local_central_size_mismatch(self):
        p=self.fx.root/'size.zip'
        with zipfile.ZipFile(p,'w') as z: z.writestr('stage.tar',b'tar'); z.writestr('descriptor.json',b'{}')
        data=bytearray(p.read_bytes()); t.struct.pack_into('<I',data,22,4); p.write_bytes(data); dest=self.fx.root/'size-out'; dest.mkdir()
        with self.assertRaisesRegex(ValueError,'sizes or CRC'): t._extract_zip(p,dest,t.MAX_ARCHIVE)
    def test_file_directory_alias(self):
        with self.assertRaisesRegex(ValueError,'path alias'): t.layout_names({'evidence/a','evidence/a/b'})
    def test_deep_directory_fanout(self):
        with self.assertRaisesRegex(ValueError,'depth/length'): t.layout_names({'/'.join(['evidence']*13)})
    def test_inode_reserve(self):
        with patch.object(t.os,'statvfs',return_value=SimpleNamespace(f_frsize=4096,f_favail=2)):
            with self.assertRaisesRegex(ValueError,'inodes'): t.require_disk(self.fx.root,0,entries=2,directories=1)
    def test_inherited_deadline_already_expired(self):
        self.fx.seal()
        with self.assertRaisesRegex(ValueError,'deadline'):
            t.admit_stage(self.fx.extracted,expected=self.fx.expected,objects=self.fx.objects,prior={},checked=set(),api=api,deadline=t.time.monotonic()-1)
    def test_interrupted_admission_is_fatal_and_no_resume(self):
        self.fx.seal()
        def interrupted(src,dst,*args): dst.write(src.read(1)); raise OSError('interrupted host copy')
        with patch.object(t.shutil,'copyfileobj',side_effect=interrupted):
            with self.assertRaisesRegex(OSError,'interrupted'): self.fx.admit()
        with self.assertRaisesRegex(ValueError,'single owned root'): self.fx.admit()
    def test_interface_evidence_mismatch(self):
        self.fx.write('interface-identity.json',{'wrong':'value'}); self.reject()
    def test_lineage_evidence_mismatch(self):
        self.fx.write('imported-stages.json',[{'stage_id':'F0_common'}]); self.reject()
    def test_nonfinal_cannot_claim_terminal_success(self):
        self.fx.result['status']='CACHE_BACKED_CONDITIONAL_GEOMETRY_REPLAY_COMPLETED'; self.reject()

    def test_zip64_streaming_supported(self):
        class Streaming(io.BytesIO):
            def seekable(self): return False
            def seek(self,*args): raise io.UnsupportedOperation('streaming')
        for streaming in (False,True):
            data=Streaming() if streaming else io.BytesIO()
            with zipfile.ZipFile(data,'w',compression=zipfile.ZIP_DEFLATED) as z:
                for name,payload in [('stage.tar',b'tar payload'),('descriptor.json',b'{}')]:
                    with z.open(name,'w',force_zip64=True) as out: out.write(payload)
            p=self.fx.root/('zip64-'+str(streaming)+'.zip'); p.write_bytes(data.getvalue()); dest=self.fx.root/('zip64-'+str(streaming)); dest.mkdir()
            t._extract_zip(p,dest,t.MAX_ARCHIVE)
            self.assertEqual((dest/'stage.tar').read_bytes(),b'tar payload')
    def test_initial_extract_reserves_receipt_and_quarantine(self):
        self.fx.seal(); archive_bytes=(self.fx.bundle/'stage.tar').stat().st_size
        dest=self.fx.root/'initial-reserve-extracted'
        with patch.object(t.shutil,'disk_usage',return_value=SimpleNamespace(free=t.DISK_RESERVE+archive_bytes)):
            with self.assertRaisesRegex(ValueError,'disk'): t.extract_stage(self.fx.bundle,dest)
        self.assertFalse(dest.exists())
        with patch.object(t.os,'statvfs',return_value=SimpleNamespace(f_frsize=4096,f_favail=1024)):
            with self.assertRaisesRegex(ValueError,'inodes'): t.extract_stage(self.fx.bundle,dest)
        self.assertFalse(dest.exists())
    def test_extra_metadata_hidden_payload_rejected(self):
        for extra in [t.struct.pack('<HH',0x5455,6)+b'\x01'+bytes(5), t.struct.pack('<HH',1,9)+bytes(9), t.struct.pack('<HH',0x7875,6)+b'\x01\x01\x00\x01\x00X']:
            with self.assertRaises(ValueError): t._extra_fields(extra)
    def test_unlisted_tar_rejected_before_directory_allocation(self):
        bundle=self.fx.root/'unlisted-bundle'; bundle.mkdir(); source=self.fx.root/'tiny'; source.write_bytes(b'')
        receipt={'schema':t.SCHEMA,**self.fx.meta,'files':{}}
        digest=f.write_tar(bundle/'stage.tar',{'evidence/unlisted/extra':source},receipt,102400)
        p=bundle/'stage.tar'; (bundle/'descriptor.json').write_bytes(f.json_bytes({'schema':'conditional-stage-descriptor-v1','stage_id':'F0_common','archive_bytes':p.stat().st_size,'archive_sha256':f.file_sha(p),'receipt_sha256':digest}))
        dest=self.fx.root/'unlisted-extracted'
        with self.assertRaisesRegex(ValueError,'before allocation'): t.extract_stage(bundle,dest)
        self.assertFalse((dest/'evidence').exists())

class NetworkTests(unittest.TestCase):
    def setUp(self):
        self.disk=patch.object(t.shutil,'disk_usage',return_value=SimpleNamespace(free=100*t.GIB)); self.disk.start(); self.addCleanup(self.disk.stop)
    def fake(self):
        obj=object.__new__(t.Transport); obj.deadline=t.time.monotonic()+1800; obj.workflow_id=30; obj.run_id='900'; obj.attempt='2'; obj.commit='a'*40; obj.token='SECRET'
        obj.identity={'repository':t.REPOSITORY,'run_id':'900','run_attempt':'2','workflow_commit':obj.commit}
        obj._jobs=[{'name':'conditional F0_common','status':'completed','conclusion':'success','id':20,'run_id':900,'run_attempt':2,'head_sha':obj.commit}]
        obj._artifacts=[{'name':obj.artifact_name('F0_common'),'id':10,'expired':False,'size_in_bytes':10,'digest':'sha256:'+'d'*64,'workflow_run':{'id':900,'head_sha':obj.commit}}]
        return obj
    def reject_before_request(self,obj):
        obj.opener=SimpleNamespace(open=lambda *a,**kw:self.fail('unexpected network request'))
        with tempfile.TemporaryDirectory(dir=HERE) as root:
            with self.assertRaises(ValueError): obj.download_stage('F0_common','conditional F0_common',Path(root)/'out')
    def test_failed_producer(self): obj=self.fake(); obj._jobs[0]['conclusion']='failure'; self.reject_before_request(obj)
    def test_duplicate_producer(self): obj=self.fake(); obj._jobs*=2; self.reject_before_request(obj)
    def test_prior_attempt_job(self): obj=self.fake(); obj._jobs[0]['run_attempt']=1; self.reject_before_request(obj)
    def test_prior_run_artifact(self): obj=self.fake(); obj._artifacts[0]['workflow_run']['id']=899; self.reject_before_request(obj)
    def test_missing_digest(self): obj=self.fake(); del obj._artifacts[0]['digest']; self.reject_before_request(obj)
    def test_duplicate_artifact(self): obj=self.fake(); obj._artifacts*=2; self.reject_before_request(obj)
    def test_expired_artifact(self): obj=self.fake(); obj._artifacts[0]['expired']=True; self.reject_before_request(obj)
    def test_oversized_zip(self): obj=self.fake(); obj._artifacts[0]['size_in_bytes']=t.MAX_ARCHIVE+t.ZIP_ALLOWANCE+1; self.reject_before_request(obj)
    def test_redirect_credential_not_forwarded(self):
        obj=self.fake(); captured=[]
        def api_open(req,**kw):
            self.assertEqual(req.get_header('Authorization'),'Bearer SECRET')
            raise urllib.error.HTTPError(req.full_url,302,'Found',{'Location':'https://signed.example/artifact?opaque=1'},None)
        def storage_open(req,**kw):
            captured.append(req); self.assertIsNone(req.get_header('Authorization')); raise OSError('signed URL suppressed')
        obj.opener=SimpleNamespace(open=api_open)
        with tempfile.TemporaryDirectory(dir=HERE) as root, patch.object(t.urllib.request,'build_opener',return_value=SimpleNamespace(open=storage_open)):
            with self.assertRaisesRegex(ValueError,'URL suppressed'): obj.download_stage('F0_common','conditional F0_common',Path(root)/'out')
        self.assertEqual(len(captured),1)
    def test_http_storage_redirect_rejected(self):
        obj=self.fake()
        def api_open(req,**kw): raise urllib.error.HTTPError(req.full_url,302,'Found',{'Location':'http://signed.example/'},None)
        obj.opener=SimpleNamespace(open=api_open)
        with tempfile.TemporaryDirectory(dir=HERE) as root:
            with self.assertRaisesRegex(ValueError,'unsafe artifact storage redirect'): obj.download_stage('F0_common','conditional F0_common',Path(root)/'out')

    def marker(self,obj,**changes):
        artifact=obj._artifacts[0]; marker={'stage_id':'F0_common','artifact_id':str(artifact['id']),'artifact_name':artifact['name'],'artifact_sha256':artifact['digest'][7:]}
        marker.update(changes); return b'2026-10-16T13:00:00.0000000Z CONDITIONAL_STAGE_ARTIFACT_V1 '+json.dumps(marker).encode()+b'\n'
    def test_unique_emitted_job_binding(self):
        obj=self.fake(); data=b"2026-10-16T13:00:00.0000000Z Run printf '%s' 'CONDITIONAL_STAGE_ARTIFACT_V1 {}'\n"+self.marker(obj)
        obj.response=lambda *args,**kwargs:io.BytesIO(data)
        self.assertEqual(obj.bind_producer(obj._jobs[0],obj._artifacts[0],'F0_common'),f.sha(data))
    def test_echoed_marker_only_rejected(self):
        obj=self.fake(); data=b"2026-10-16T13:00:00.0000000Z Run printf '%s' 'CONDITIONAL_STAGE_ARTIFACT_V1 {}'\n"
        obj.response=lambda *args,**kwargs:io.BytesIO(data)
        with self.assertRaisesRegex(ValueError,'binding missing'): obj.bind_producer(obj._jobs[0],obj._artifacts[0],'F0_common')
    def test_wrong_producer_artifact_id_rejected(self):
        obj=self.fake(); obj.response=lambda *args,**kwargs:io.BytesIO(self.marker(obj,artifact_id='11'))
        with self.assertRaisesRegex(ValueError,'binding differs'): obj.bind_producer(obj._jobs[0],obj._artifacts[0],'F0_common')
    def test_wrong_producer_artifact_digest_rejected(self):
        obj=self.fake(); obj.response=lambda *args,**kwargs:io.BytesIO(self.marker(obj,artifact_sha256='e'*64))
        with self.assertRaisesRegex(ValueError,'binding differs'): obj.bind_producer(obj._jobs[0],obj._artifacts[0],'F0_common')
    def test_duplicate_emitted_binding_rejected(self):
        obj=self.fake(); obj.response=lambda *args,**kwargs:io.BytesIO(self.marker(obj)*2)
        with self.assertRaisesRegex(ValueError,'binding missing'): obj.bind_producer(obj._jobs[0],obj._artifacts[0],'F0_common')
    def test_inherited_network_deadline(self):
        obj=self.fake(); obj.deadline=t.time.monotonic()-1
        with self.assertRaisesRegex(ValueError,'deadline'): obj.read_bounded(io.BytesIO(b'input'),10)
    def test_read1_trickle_checks_inherited_deadline(self):
        obj=self.fake(); obj.deadline=5
        with patch.object(t.time,'monotonic',side_effect=[4,6]):
            with self.assertRaisesRegex(ValueError,'deadline'): obj.read_bounded(io.BytesIO(b'input'),10)
    def test_job_log_size_bound(self):
        obj=self.fake()
        with self.assertRaisesRegex(ValueError,'byte cap'): obj.read_bounded(io.BytesIO(b'oversized'),2)

if __name__=='__main__': unittest.main(verbosity=2)
