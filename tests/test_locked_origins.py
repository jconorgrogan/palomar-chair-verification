"""Offline exact-origin and producer-contract tests; no network or child processes."""
import copy, io, json, os, tempfile, unittest, zipfile
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import Mock, patch

import test_conditional_transport as original

f=original.f
t=original.t


class LockedOriginTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root=Path(self.tmp.name)
        self.disk=patch.object(t.shutil,'disk_usage',return_value=SimpleNamespace(free=100*t.GIB))
        self.disk.start(); self.addCleanup(self.disk.stop)
        self.env={'GITHUB_ACTIONS':'true','GITHUB_REPOSITORY':t.REPOSITORY,'GITHUB_RUN_ID':'1000',
                  'GITHUB_RUN_ATTEMPT':'1','GITHUB_SHA':'b'*40,'GH_TOKEN':'inert-offline-fixture'}
        self.identity={'repository':t.REPOSITORY,'run_id':'900','run_attempt':'2','workflow_commit':'a'*40}
        self.stage='F0_common'
        payload=io.BytesIO()
        with zipfile.ZipFile(payload,'w',compression=zipfile.ZIP_DEFLATED) as archive:
            archive.writestr('stage.tar',b'inert unexecuted fixture')
            archive.writestr('descriptor.json',b'{}')
        self.payload=payload.getvalue()
        self.artifact={'name':'conditional-geometry-900-2-F0_common-objects','id':10,'expired':False,
                       'size_in_bytes':len(self.payload),'digest':'sha256:'+f.sha(self.payload),
                       'workflow_run':{'id':900,'head_sha':'a'*40}}
        self.job={'name':'conditional F0_common','id':20,'status':'completed','conclusion':'success',
                  'run_id':900,'run_attempt':2,'head_sha':'a'*40}
        self.run={'id':900,'run_attempt':2,'head_sha':'a'*40,'event':'push',
                  'repository':{'full_name':t.REPOSITORY},'path':t.WORKFLOW_PATH,'workflow_id':30,
                  'status':'completed','conclusion':'failure'}
        self.workflow={'id':30,'path':t.WORKFLOW_PATH}
        self.consumer_run={**copy.deepcopy(self.run),'id':1000,'run_attempt':1,'head_sha':'b'*40,'status':'in_progress','conclusion':None}
        self.marker={'stage_id':self.stage,'artifact_id':'10','artifact_name':self.artifact['name'],
                     'artifact_sha256':f.sha(self.payload)}
        self.log=self.marker_bytes()
        self.lock={'identity':self.identity,'stage_id':self.stage,'artifact_name':self.artifact['name'],
                   'artifact_id':10,'producer_job_name':self.job['name'],'producer_job_id':20,
                   'producer_conclusion':'success','artifact_zip_sha256':f.sha(self.payload),
                   'artifact_zip_bytes':len(self.payload),'workflow_path':t.WORKFLOW_PATH,
                   'workflow_id':30,'producer_job_log_sha256':f.sha(self.log)}
        self.metadata_paths=[]; self.transfer_paths=[]

    def marker_bytes(self,**changes):
        marker={**self.marker,**changes}
        return b'2026-10-16T14:00:00.1234567Z CONDITIONAL_STAGE_ARTIFACT_V1 '+json.dumps(marker,sort_keys=True).encode()+b'\n'

    def metadata(self,path):
        self.metadata_paths.append(path)
        if path.endswith('/actions/runs/900'): return copy.deepcopy(self.run)
        if path.endswith('/actions/runs/1000'): return copy.deepcopy(self.consumer_run)
        if path.endswith('/actions/workflows/conditional-geometry.yml'): return copy.deepcopy(self.workflow)
        if '/attempts/2/jobs?' in path: return {'jobs':[copy.deepcopy(self.job)],'total_count':1}
        if '/actions/runs/900/artifacts?' in path: return {'artifacts':[copy.deepcopy(self.artifact)],'total_count':1}
        # A malformed host pin must still be compared with authenticated origin
        # metadata, rather than silently falling back to the current consumer.
        if '/actions/runs/' in path: return copy.deepcopy(self.run)
        self.fail('unexpected metadata route: '+path)

    def construct(self,lock=None):
        with patch.dict(os.environ,self.env), patch.object(t.Transport,'get',side_effect=self.metadata):
            obj=t.Transport(origin_lock=self.lock if lock is None else lock)
        obj.get=self.metadata
        def response(path,**kwargs):
            self.transfer_paths.append(path)
            if path.endswith('/actions/jobs/20/logs'): return io.BytesIO(self.log)
            if path.endswith('/actions/artifacts/10/zip'): return io.BytesIO(self.payload)
            self.fail('unexpected transfer route: '+path)
        obj.response=response
        return obj

    def download(self,obj,target='download'):
        return obj.download_stage(self.stage,'conditional '+self.stage,self.root/target)

    def reject_constructor(self):
        with self.assertRaises((ValueError,KeyError)): self.construct()
        self.assertFalse(self.transfer_paths)

    def reject_download(self,obj):
        with self.assertRaises((ValueError,KeyError)): self.download(obj)
        self.assertFalse(any(path.endswith('/zip') for path in self.transfer_paths))
        self.assertFalse((self.root/'download').exists())

    def test_exact_locked_origin_preserves_original_lineage_shape(self):
        obj=self.construct(); returned=self.download(obj)
        self.assertEqual(returned,self.lock)
        self.assertEqual(f.json_bytes(returned),f.json_bytes(self.lock))
        self.assertEqual(set(returned),set(t.ORIGIN_KEYS))
        self.assertEqual(obj.identity,self.identity)
        self.assertEqual(obj.consumer_identity['run_id'],'1000')
        self.assertTrue(any('/runs/900/attempts/2/jobs?' in p for p in self.metadata_paths))
        self.assertTrue(any('/runs/900/artifacts?' in p for p in self.metadata_paths))
        self.assertEqual((self.root/'download/stage.tar').read_bytes(),b'inert unexecuted fixture')
        self.assertFalse((self.root/'download/download.zip').exists())
        # A failed aggregate run does not disqualify its independently successful job.
        self.assertEqual(self.run['conclusion'],'failure')

    def test_constructor_freezes_caller_lock(self):
        obj=self.construct(); saved=copy.deepcopy(self.lock)
        self.lock['identity']['run_id']='899'; self.lock['artifact_zip_sha256']='e'*64
        self.assertEqual(self.download(obj),saved)

    def test_repeated_successful_stage_is_rejected_before_lookup_or_transfer(self):
        obj=self.construct(); self.download(obj)
        counts=(len(self.metadata_paths),len(self.transfer_paths))
        with self.assertRaisesRegex(ValueError,'already accepted'): self.download(obj,'second')
        self.assertEqual((len(self.metadata_paths),len(self.transfer_paths)),counts)
        self.assertFalse((self.root/'second').exists())

    def test_wrong_locked_run(self):
        self.lock['identity']['run_id']='899'
        self.lock['artifact_name']='conditional-geometry-899-2-F0_common-objects'
        self.reject_constructor()

    def test_wrong_locked_attempt(self):
        self.lock['identity']['run_attempt']='1'
        self.lock['artifact_name']='conditional-geometry-900-1-F0_common-objects'
        self.reject_constructor()

    def test_wrong_locked_commit(self):
        self.lock['identity']['workflow_commit']='e'*40; self.reject_constructor()

    def test_wrong_authenticated_run_identity(self):
        for field,value in [('id',901),('run_attempt',3),('head_sha','e'*40),('event','workflow_dispatch'),
                            ('repository',{'full_name':'other/repository'})]:
            with self.subTest(field=field):
                saved=self.run; self.run={**saved,field:value}; self.reject_constructor(); self.run=saved

    def test_wrong_current_consumer_run_is_rejected(self):
        for field,value in [('id',1001),('run_attempt',2),('head_sha','e'*40),('event','workflow_dispatch'),
                            ('repository',{'full_name':'other/repository'}),('workflow_id',31),
                            ('path','.github/workflows/other.yml')]:
            with self.subTest(field=field):
                saved=self.consumer_run; self.consumer_run={**saved,field:value}; self.reject_constructor(); self.consumer_run=saved

    def test_locked_producer_run_must_be_terminal(self):
        for status in ['in_progress','queued',None]:
            with self.subTest(status=status):
                self.run['status']=status; self.reject_constructor()

    def test_future_run_cannot_be_a_locked_earlier_origin(self):
        self.env['GITHUB_RUN_ID']='800'; self.reject_constructor()

    def test_wrong_workflow_lock_or_authenticated_path(self):
        for target,field,value in [('lock','workflow_id',31),('lock','workflow_path','.github/workflows/other.yml'),
                                   ('run','workflow_id',31),('run','path','.github/workflows/other.yml'),
                                   ('workflow','id',31),('workflow','path','.github/workflows/other.yml')]:
            with self.subTest(target=target,field=field):
                obj=getattr(self,target); saved=obj[field]; obj[field]=value
                self.reject_constructor(); obj[field]=saved

    def test_incomplete_extra_or_wildcard_lock_is_rejected(self):
        for mutation in [lambda x:x.pop('producer_job_log_sha256'),lambda x:x.update(extra=True),
                         lambda x:x['identity'].update(run_id='*'),lambda x:x['identity'].update(run_attempt='*'),
                         lambda x:x['identity'].update(workflow_commit='*'),lambda x:x.update(artifact_id=True),
                         lambda x:x.update(artifact_zip_bytes=0),lambda x:x.update(artifact_zip_sha256='sha256:'+'a'*64)]:
            with self.subTest(mutation=mutation):
                lock=copy.deepcopy(self.lock); mutation(lock)
                with self.assertRaises(ValueError): self.construct(lock)
        self.assertFalse(self.transfer_paths)

    def test_same_run_cannot_masquerade_as_locked_earlier_origin(self):
        self.env['GITHUB_RUN_ID']='900'; self.reject_constructor()

    def test_final_and_diagnostic_stages_cannot_be_locked(self):
        for stage in ['F4_bridge_and_endpoint_joins','profile_target']:
            with self.subTest(stage=stage):
                lock=copy.deepcopy(self.lock); lock.update(stage_id=stage,producer_job_name='conditional '+stage,
                    artifact_name='conditional-geometry-900-2-'+stage+'-objects')
                with self.assertRaisesRegex(ValueError,'unapproved locked producer stage'): self.construct(lock)

    def test_selected_stage_must_equal_host_lock(self):
        obj=self.construct()
        with self.assertRaisesRegex(ValueError,'origin lock'):
            obj.download_stage('F1_curved_existence','conditional F1_curved_existence',self.root/'wrong')
        self.assertFalse(self.transfer_paths)

    def test_wrong_job_metadata_rejected_before_payload(self):
        for field,value in [('id',21),('name','conditional F1_curved_existence'),('status','in_progress'),
                            ('conclusion','failure'),('run_id',899),('run_attempt',1),('head_sha','e'*40)]:
            with self.subTest(field=field):
                saved=self.job; self.job={**saved,field:value}; self.reject_download(self.construct()); self.job=saved

    def test_duplicate_job_or_artifact_rejected_before_payload(self):
        for collection in ['_jobs','_artifacts']:
            with self.subTest(collection=collection):
                obj=self.construct(); row=self.job if collection=='_jobs' else self.artifact
                setattr(obj,collection,[copy.deepcopy(row),copy.deepcopy(row)])
                self.reject_download(obj)

    def test_missing_job_or_artifact_rejected_before_payload(self):
        for collection in ['_jobs','_artifacts']:
            with self.subTest(collection=collection):
                obj=self.construct(); setattr(obj,collection,[]); self.reject_download(obj)

    def test_wrong_artifact_metadata_rejected_before_payload(self):
        for field,value in [('id',11),('name','conditional-geometry-900-1-F0_common-objects'),('expired',True),
                            ('size_in_bytes',len(self.payload)+1),('digest','sha256:'+'e'*64),
                            ('workflow_run',{'id':899,'head_sha':'a'*40}),
                            ('workflow_run',{'id':900,'head_sha':'e'*40})]:
            with self.subTest(field=field,value=value):
                saved=self.artifact; self.artifact={**saved,field:value}; self.reject_download(self.construct()); self.artifact=saved

    def test_exact_host_artifact_and_job_pins_are_required(self):
        for field,value in [('artifact_id',11),('producer_job_id',21),('artifact_zip_bytes',len(self.payload)+1),
                            ('artifact_zip_sha256','e'*64)]:
            with self.subTest(field=field):
                lock=copy.deepcopy(self.lock); lock[field]=value; self.reject_download(self.construct(lock))

    def test_wrong_actual_producer_marker_rejected(self):
        original_log=self.log
        for field,value in [('stage_id','F1_curved_existence'),('artifact_id','11'),('artifact_name','other'),('artifact_sha256','e'*64)]:
            with self.subTest(field=field):
                self.log=self.marker_bytes(**{field:value}); self.reject_download(self.construct())
        self.log=original_log

    def test_unique_timestamped_marker_required(self):
        original_log=self.log
        for log in [b'',original_log*2,b'echo '+original_log,original_log.replace(b'2026-10-16T14:00:00.1234567Z ',b'')]:
            with self.subTest(log=log):
                self.log=log; self.reject_download(self.construct())
        self.log=original_log

    def test_exact_original_log_digest_required(self):
        self.log=b'2026-10-16T13:59:59Z changed leading transcript\n'+self.log
        self.reject_download(self.construct())

    def test_truncated_or_changed_payload_not_accepted(self):
        for payload in [self.payload[:-1],b'changed'+self.payload[7:]]:
            with self.subTest(length=len(payload)):
                obj=self.construct(); original_payload=self.payload; self.payload=payload
                with self.assertRaisesRegex(ValueError,'digest/size mismatch'): self.download(obj)
                self.assertEqual(obj._accepted_stages,set())
                self.payload=original_payload
                # Failed bytes are quarantine only, never a successful origin.
                import shutil
                shutil.rmtree(self.root/'download')


class ProducerContractScopeTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory(); self.addCleanup(self.tmp.cleanup)
        self.disk=patch.object(t.shutil,'disk_usage',return_value=SimpleNamespace(free=100*t.GIB))
        self.disk.start(); self.addCleanup(self.disk.stop)
        self.fx=original.Fixture(self.tmp.name)

    def reject(self):
        self.fx.seal()
        with self.assertRaises((ValueError,KeyError)): self.fx.admit()
        self.assertEqual(t.inventory(self.fx.objects,t.MAX_OWNED),{})

    def test_legacy_original_contract_requires_false_freshness_scope(self):
        self.fx.result['owned_objects_from_prior_runs']=True; self.reject()

    def prepare_certificate(self):
        contract=self.fx.contract; target=original.baseline.ASYNC_TARGET
        contract.update(schema='conditional-geometry-origin-continuation-v3',owned_objects_from_prior_runs_allowed=True,
                        module_compile_arguments={target:['-DElab.async=false']},
                        inputs={'src/'+target.replace('.','/')+'.lean':{'sha256':original.baseline.ASYNC_TARGET_SHA}})
        stage='F3_product_geometry'; contract['stages'][stage]=contract['stages'].pop('F0_common')
        for obj in [self.fx.meta,self.fx.expected,self.fx.origin,self.fx.result]: obj['stage_id']=stage
        self.fx.origin['producer_job_name']='conditional '+stage
        self.fx.origin['artifact_name']='conditional-geometry-900-2-'+stage+'-objects'
        self.fx.result['owned_objects_from_prior_runs']=True
        certificate={'schema':'inert-certificate-fixture','host_authenticated_inputs':True}
        self.fx.write('cross-origin-admissions.json',certificate)
        self.fx.result['cross_origin_admissions_sha256']=f.file_sha(self.fx.evidence/'cross-origin-admissions.json')
        api=SimpleNamespace(**vars(original.api),module_compile_arguments=original.baseline.module_compile_arguments,
                            cross_origin_certificate=Mock(return_value=copy.deepcopy(certificate)))
        return certificate,api

    def admit_with_api(self,api):
        return t.admit_stage(self.fx.extracted,expected=self.fx.expected,objects=self.fx.objects,
                             prior={},checked=set(),api=api)

    def test_new_producer_requires_exact_certificate_from_host_inputs(self):
        _,api=self.prepare_certificate(); self.fx.seal(); _,inv=self.admit_with_api(api)
        self.assertEqual(inv,self.fx.own)
        api.cross_origin_certificate.assert_called_once_with(self.fx.contract,self.fx.expected['contract_sha256'],
            self.fx.expected['identity'],self.fx.expected['stage_id'],self.fx.expected['interface_identity'],
            self.fx.expected['predecessor_artifacts'],self.fx.expected['producer_inventory'])

    def test_new_certificate_digest_cannot_be_replaced_by_receipt_inventory(self):
        _,api=self.prepare_certificate(); self.fx.result['cross_origin_admissions_sha256']='f'*64; self.fx.seal()
        with self.assertRaisesRegex(ValueError,'certificate digest'): self.admit_with_api(api)
        self.assertEqual(t.inventory(self.fx.objects,t.MAX_OWNED),{})

    def test_new_certificate_content_must_match_independently_reconstructed_value(self):
        _,api=self.prepare_certificate(); api.cross_origin_certificate.return_value={'forged':True}; self.fx.seal()
        with self.assertRaisesRegex(ValueError,'certificate differs'): self.admit_with_api(api)
        self.assertEqual(t.inventory(self.fx.objects,t.MAX_OWNED),{})

    def test_new_certificate_hash_is_mandatory(self):
        _,api=self.prepare_certificate(); self.fx.result.pop('cross_origin_admissions_sha256'); self.fx.seal()
        with self.assertRaisesRegex(ValueError,'certificate digest'): self.admit_with_api(api)
        self.assertEqual(t.inventory(self.fx.objects,t.MAX_OWNED),{})

    def test_new_certificate_file_is_mandatory(self):
        _,api=self.prepare_certificate(); (self.fx.evidence/'cross-origin-admissions.json').unlink(); self.fx.seal()
        with self.assertRaises(FileNotFoundError): self.admit_with_api(api)
        self.assertEqual(t.inventory(self.fx.objects,t.MAX_OWNED),{})

    def test_legacy_producer_cannot_assert_new_certificate_hash(self):
        self.fx.result['cross_origin_admissions_sha256']='f'*64; self.reject()

    def test_legacy_producer_cannot_include_new_certificate_file(self):
        self.fx.write('cross-origin-admissions.json',{'forged':True}); self.reject()

    def test_true_expected_policy_accepts_only_true_result(self):
        self.fx.contract['owned_objects_from_prior_runs_allowed']=True
        self.fx.result['owned_objects_from_prior_runs']=True
        self.fx.seal(); _,inv=self.fx.admit(); self.assertEqual(inv,self.fx.own)

    def test_true_expected_policy_rejects_false_result(self):
        self.fx.contract['owned_objects_from_prior_runs_allowed']=True; self.reject()

    def test_missing_or_nonboolean_contract_policy_rejected(self):
        for value in [None,0,1,'true']:
            with self.subTest(value=value):
                self.fx.contract['owned_objects_from_prior_runs_allowed']=value; self.reject()
        self.fx.contract.pop('owned_objects_from_prior_runs_allowed'); self.reject()

    def test_result_scope_requires_boolean_identity(self):
        self.fx.result['owned_objects_from_prior_runs']=0; self.reject()

    def test_duplicate_imported_stage_cannot_overwrite_accepted_objects(self):
        self.fx.seal(); _,prior=self.fx.admit(); self.fx.seal()
        with self.assertRaisesRegex(ValueError,'duplicate/overwrite'):
            t.admit_stage(self.fx.extracted,expected=self.fx.expected,objects=self.fx.objects,prior=prior,
                          checked=set(self.fx.meta['stage_modules']),api=original.api)
        self.assertEqual(t.inventory(self.fx.objects,t.MAX_OWNED),prior)

    def test_origin_extra_keys_cannot_change_prior_lineage_shape(self):
        self.fx.origin['new_consumer_identity']=copy.deepcopy(self.fx.identity); self.reject()

    def test_original_producer_argv_stays_default_without_mock_helper(self):
        specs=t.command_specs(self.fx.expected,original.api)
        compiles=[s for s in specs if s['name'].startswith('compile-')]
        self.assertEqual(len(compiles),2)
        self.assertFalse(any('-DElab.async=false' in row['argv'] for row in specs))

    def continuation(self):
        contract=self.fx.contract
        contract['schema']='conditional-geometry-origin-continuation-v3'
        contract['owned_objects_from_prior_runs_allowed']=True
        target=original.baseline.ASYNC_TARGET
        contract['module_compile_arguments']={target:['-DElab.async=false']}
        contract['inputs']={'src/'+target.replace('.','/')+'.lean':{'sha256':original.baseline.ASYNC_TARGET_SHA}}
        self.fx.expected['stage_rows']=[{'module':target},{'module':'Fixture.Other'}]
        api=SimpleNamespace(**vars(original.api),module_compile_arguments=original.baseline.module_compile_arguments)
        return target,api

    def test_new_option_is_source_local_compiler_only(self):
        target,api=self.continuation(); specs=t.command_specs(self.fx.expected,api)
        flagged=[row['name'] for row in specs if '-DElab.async=false' in row['argv']]
        self.assertEqual(flagged,['compile-'+target])
        compile_row=next(row for row in specs if row['name']=='compile-'+target)
        i=compile_row['argv'].index('-Dcompiler.postponeCompile=false')
        self.assertEqual(compile_row['argv'][i+1:i+3],['-DElab.async=false','-o'])

    def test_new_schema_without_helper_is_rejected(self):
        self.continuation()
        with self.assertRaisesRegex(ValueError,'scheduling policy'): t.command_specs(self.fx.expected,original.api)

    def test_missing_or_unknown_schema_has_no_default_argv_fallback(self):
        for schema in [None,'unknown']:
            with self.subTest(schema=schema):
                self.fx.contract['schema']=schema
                with self.assertRaisesRegex(ValueError,'scheduling policy'): t.command_specs(self.fx.expected,original.api)

    def test_legacy_contract_cannot_gain_module_override(self):
        self.fx.contract['module_compile_arguments']={}
        with self.assertRaisesRegex(ValueError,'scheduling policy'): t.command_specs(self.fx.expected,original.api)

    def test_new_option_wrong_source_or_broad_scope_is_rejected(self):
        target,api=self.continuation()
        self.fx.contract['module_compile_arguments']['Fixture.Other']=['-DElab.async=false']
        with self.assertRaisesRegex(ValueError,'scheduling exception'): t.command_specs(self.fx.expected,api)
        self.fx.contract['module_compile_arguments']={target:['-DElab.async=false']}
        self.fx.contract['inputs']['src/'+target.replace('.','/')+'.lean']['sha256']='0'*64
        with self.assertRaisesRegex(ValueError,'source bytes'): t.command_specs(self.fx.expected,api)

    def test_original_argv_cannot_be_revalidated_as_new_consumer_argv(self):
        # A real old default compile record remains bound to the old contract;
        # changing only its expected schema cannot confer the new module option.
        target,api=self.continuation()
        fresh_specs=t.command_specs(self.fx.expected,api)
        self.fx.contract['schema']='conditional-geometry-staged-replay-v2'
        self.fx.contract.pop('module_compile_arguments')
        old_specs=t.command_specs(self.fx.expected,original.api)
        new=next(row for row in fresh_specs if row['name']=='compile-'+target)
        old=next(row for row in old_specs if row['name']=='compile-'+target)
        self.assertNotEqual(old['argv'],new['argv'])
        self.assertEqual([x for x in new['argv'] if x!='-DElab.async=false'],old['argv'])


if __name__=='__main__': unittest.main(verbosity=2)
