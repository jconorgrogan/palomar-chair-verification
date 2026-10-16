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

