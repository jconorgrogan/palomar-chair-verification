"""INACTIVE three-context runner composition. No CLI or authority from this module.

The caller must authenticate the current transport, all acquired bytes, the
historical admission/reconciliation and exact source/runtime/implementation pins.
All build/check commands are inherited from the unchanged readonly StageRunner.
"""
from __future__ import annotations
import copy,hashlib,json,math,os,shutil,time,tarfile
from datetime import datetime,timezone
from pathlib import Path
import fresh_stage as f
import four_context_policy as p
import four_context_policy as ep
import three_context_local as local
import four_context_transfer as transfer
from four_context_current_transport import CurrentOriginTransport
from three_context_runner import ThreeContextRunner as FrozenLatestRunner

PRIOR_FILES_SHA='9618bc2900517a9234254ddf2a2ea6fb3c78f643bd12f11967f986f49e7dde1d'

class FourContextRunner(f.StageRunner):
    def __init__(self,*,selection,bundle,integration_pins,current_authority,prior_root,admission_root,
                 prior_files_bytes,old_manifest,prior_manifest,source_delta,prior_contract,
                 host_deadline_monotonic,latest_root,**kwargs):
        self._poisoned=False;self._used=False;self._last_wall=None;self._wrappers=None;self._target=None
        f.need(type(host_deadline_monotonic) in (int,float) and math.isfinite(host_deadline_monotonic),
               'finite shared host deadline required')
        self.host_deadline=float(host_deadline_monotonic)
        f.need(0<self.host_deadline-time.monotonic()<=kwargs['contract']['job_timeout_seconds'],'host deadline expired or renewed')
        f.need(isinstance(current_authority,CurrentOriginTransport),'authenticated current authority required')
        f.need(current_authority.contexts['CurrentOrigin']['identity']==kwargs['identity'] and
               current_authority.selection.raw_bytes==selection.raw_bytes and current_authority.bundle.raw_bytes==bundle.raw_bytes,
               'current authority/context mismatch')
        current_authority._check_age()
        self.selection=ep.validate_execution_context(plan=kwargs['plan'],profiles=kwargs['profiles'],current_contract=kwargs['contract'],
            current_manifest=kwargs['manifest'],old_manifest=old_manifest,prior_manifest=prior_manifest,source_delta=source_delta,
            inventory=kwargs['toolchain_inventory'],current_identity=kwargs['identity'],selection=selection,bundle=bundle,
            integration_pins=integration_pins,prior_contract=prior_contract)
        self.bundle=bundle;self.integration_pins=copy.deepcopy(integration_pins);self.prior_contract=copy.deepcopy(prior_contract)
        self.prior_root=local.canonical(str(prior_root));self.admission_root=local.canonical(str(admission_root))
        f.need(type(prior_files_bytes) is bytes and p.sha(prior_files_bytes)==PRIOR_FILES_SHA,'historical implementation inventory changed')
        self.prior_files=p.parse_json(prior_files_bytes);self.source_delta=copy.deepcopy(source_delta)
        self.latest_root=local.canonical(str(latest_root));latest_ci=self.latest_root/'ci'
        self.latest_identity=copy.deepcopy(bundle.latest_context['identity'])
        self.latest_contract=f.pinned_load(latest_ci/'three_context_contract.json',self.latest_identity['contract_sha256'])
        self.latest_profiles=f.pinned_load(latest_ci/'profiles.json',self.latest_identity['profiles_sha256'])
        f.need(f.file_sha(latest_ci/'fresh_stage.py')==f.file_sha(Path(f.__file__)) and
               p.object_sha(kwargs['plan'])==self.latest_identity['plan_sha256'] and
               p.object_sha(kwargs['manifest'])==self.latest_identity['source_manifest_sha256'],'latest native implementation/source/plan changed')
        self.production_identity=copy.deepcopy(bundle.production_context['identity'])
        self.production_contract=f.pinned_load(Path(__file__).resolve().parent/'production_origin_contract.json',p.PRODUCTION_CONTRACT)
        self.production_profiles=f.pinned_load(Path(__file__).resolve().parent/'production_origin_profiles.json',p.PRODUCTION_PROFILES)
        f.need(self.production_identity['profiles_sha256']==p.PRODUCTION_PROFILES and
               self.production_identity['contract_sha256']==p.PRODUCTION_CONTRACT and
               self.production_identity['runner_sha256']==f.file_sha(Path(f.__file__)) and
               self.production_identity['source_manifest_sha256']==p.object_sha(kwargs['manifest']) and
               self.production_identity['plan_sha256']==p.object_sha(kwargs['plan']),'production native context changed')
        self.old_manifest=copy.deepcopy(old_manifest);self.prior_manifest=copy.deepcopy(prior_manifest)
        super().__init__(**kwargs)
        f.need(self.owned_downloads is None,'all selected native tars must remain retained in this adapter')
        self.check_run_age()

    def check_run_age(self):
        f.need(not self._poisoned and not getattr(self,'_historical_transfer_poisoned',False),'poisoned runner cannot continue')
        now=datetime.now(timezone.utc)
        p.deadline_check(self.bundle,self.selection,now,current_identity=self.identity,previous_now=self._last_wall)
        self._last_wall=now
        f.need(time.monotonic()<self.host_deadline,'shared host deadline exceeded')

    def command(self,module,phase,profile,env,deadline):
        self.check_run_age()
        return super().command(module,phase,profile,env,min(deadline,self.host_deadline))

    @staticmethod
    def _for_runner(wrapper):
        return {**copy.deepcopy(wrapper['native_descriptor']),'archive_path':wrapper['archive_path']}

    def _native_inputs(self):
        with local.frozen_prior(self.prior_root,self.prior_files) as native:
            ci=self.prior_root/'ci';cp=native.p
            plan=native.f.pinned_load(ci/'plan.json',cp.PLAN);profiles=native.f.pinned_load(ci/'profiles.json',cp.OLD_PROFILES)
            contract=native.f.pinned_load(ci/'continuation_contract.json',self.bundle.prior_context['identity']['contract_sha256'])
            old={key:native.f.pinned_load(ci/'original'/name,pin) for key,name,pin in
                 [('contract','contract.json',cp.OLD_CONTRACT),('manifest','SOURCE_MANIFEST.json',cp.MANIFEST),('plan','plan.json',cp.PLAN),('profiles','profiles.json',cp.OLD_PROFILES)]}
            old.update(identity=copy.deepcopy(self.bundle.old_context['identity']),inventory=copy.deepcopy(self.inventory))
            raw=(ci/'continuation_selection.json').read_bytes()
            f.need(p.sha(raw)==self.bundle.prior_context['identity']['selection_sha256'],'prior native selection changed')
            result={'old_context':old,'source_delta':native.f.pinned_load(ci/'source_delta.json',cp.SOURCE_DELTA),
                    'contract':contract,'manifest':copy.deepcopy(self.manifest),'plan':plan,'profiles':profiles,
                    'identity':copy.deepcopy(self.bundle.prior_context['identity']),'inventory':copy.deepcopy(self.inventory)}
        self.check_run_age();return result,raw

    def _current_envelope(self,wrapper):
        # Invoke the exact frozen additional-envelope checker; no replacement
        # for the complete current StageRunner.read_artifacts call below.
        with local.frozen_prior(self.prior_root,self.prior_files) as native:
            native.runner.ContinuationRunner._receipt_envelope(wrapper,self)
        self.check_run_age()

    def run(self,sid,wrappers,producer_job,*,native_bytes):
        f.need(not self._used and not self._poisoned,'runner already used or poisoned')
        self._used=True
        try:
            f.need(type(self.selection.row(sid)) is p.CurrentOrigin,'historical provider cannot be rebuilt here')
            self._scope=ep.validate_restore_scope(plan=self.plan,selection=self.selection,bundle=self.bundle,wrappers=wrappers,
                native_bytes=native_bytes,current_identity=self.identity,integration_pins=self.integration_pins,target_stage=sid)
            self._wrappers=copy.deepcopy(wrappers);self._native_bytes=copy.deepcopy(native_bytes)
            self._target=transfer.arm_empty_target(self,target_stage=sid)
            result=super().run(sid,[self._for_runner(w) for w in wrappers],producer_job)
            self.check_run_age()
            sizes={w['native_descriptor']['stage_id']:w['native_descriptor']['archive_bytes'] for w in wrappers}
            ep.archive_ledger_after_build(self.selection,sizes,sid,result['archive_bytes'])
            self.check_run_age()
            return result
        except BaseException:
            self._poisoned=True;raise

    def read_predecessors(self,sid,descriptors):
        f.need(self._wrappers is not None and self._scope.data['target_stage']==sid,'missing exact typed stage scope')
        f.need(descriptors==[self._for_runner(w) for w in self._wrappers],'native descriptor bridge changed')
        self._restore_scope()

    def _restore_scope(self):
        self.check_run_age();scope=self._scope.data;wrappers=self._wrappers
        f.need(not self.objects and not self.predecessor_descriptors and not self.restore_evidence_hashes,'restore must begin empty')
        native,selection_raw=self._native_inputs()
        native['wrappers']=scope['legacy_native_view']
        transfer_scope={'origin_by_stage':{r.stage_id:type(r).__name__ for r in self.selection.rows},
            'expected_native_descriptors':[w['native_descriptor'] for w in native['wrappers']],
            'expected_full_native_descriptors':scope['native_descriptors'],'expected_objects':scope['legacy_objects'],
            'current_identity':self.identity,'latest_identity':self.latest_identity,'production_identity':self.production_identity,'current_manifest':self.manifest,'current_contract':self.contract}
        # Final v2 transfer request shape is bound explicitly during integration.
        if scope['target_stage'] is not None:transfer_scope.update(target_stage=scope['target_stage'])
        else:transfer_scope.update(target_stage=None,final_role=scope['final_role'])
        request={'schema':'fixed-four-context-transfer-request-v1','native':native,
            'native_selection_utf8':selection_raw.decode(),'native_selection_sha256':p.sha(selection_raw),'scope':transfer_scope}
        raw=p.json_bytes(request)
        if scope['legacy_stage_ids']:
            cap=transfer.admit_historical(request_bytes=raw,request_sha256=p.sha(raw),source_root=str(self.source_root),
                workspace=str(self.workspace.parent/(self.workspace.name+'-historical-validation')),
                admission_root=str(self.admission_root),historical_root=str(self.prior_root),deadline_monotonic=self.host_deadline)
            self._transfer=transfer.transfer_checked(cap,self._target)
        else:
            f.need(not scope['legacy_objects'],'empty legacy history has objects')
            self._transfer=None
        current=[w for w in wrappers if w['origin'] in {'LatestSuccessorOrigin','ProductionSuccessOrigin','CurrentOrigin'}]
        latest_reader=_LatestNativeReader(self)
        production_reader=_ProductionNativeReader(self)
        need=f.storage_restore_budget([self._for_runner(w) for w in current],self.contract,build=scope['target_stage'] is not None,
            stages=self.stages,allocation_unit=os.statvfs(self.workspace).f_frsize)
        f.need(shutil.disk_usage(self.workspace).free>=need,'insufficient measured current restore/output space after historical transfer')
        for wrapper in current:
            self.check_run_age();sid=wrapper['native_descriptor']['stage_id']
            if wrapper['origin']=='LatestSuccessorOrigin':
                latest_reader.read_exact(wrapper)
            elif wrapper['origin']=='ProductionSuccessOrigin':
                production_reader.read_exact(wrapper)
            else:
                self._current_envelope(wrapper)
                f.StageRunner.read_artifacts(self,[sid],[self._for_runner(wrapper)])
            self.predecessor_descriptors=ep.canonical_native_order(self.plan,self.predecessor_descriptors)
        self.check_run_age()
        if self._transfer is not None:
            if scope['target_stage'] is not None:transfer.finalize_predecessors(self._transfer,self._target)
            else:transfer.finalize_final_closure(self._transfer,self._target)
        f.need(self.predecessor_descriptors==scope['native_descriptors'],'full exact native predecessor map differs')
        expected={m for sid in scope['expected_stage_ids'] for m in self.stages[sid]['modules']}
        f.need(set(self.objects)==expected,'full exact imported module set differs')
        self.verify_checked_objects();f.verify_sources(self.source_root,self.manifest);self.check_run_age()
        for wrapper in wrappers:
            path=Path(wrapper['archive_path']);f.no_symlink_path(path)
            f.need(path.stat().st_size==wrapper['native_descriptor']['archive_bytes'] and f.file_sha(path)==wrapper['native_descriptor']['archive_sha256'],'retained native tar changed')
        self.check_run_age()

    def restore_final(self,role,wrappers,*,native_bytes):
        f.need(not self._used and not self._poisoned,'runner already used or poisoned');self._used=True
        try:
            self._scope=ep.validate_restore_scope(plan=self.plan,selection=self.selection,bundle=self.bundle,wrappers=wrappers,
                native_bytes=native_bytes,current_identity=self.identity,integration_pins=self.integration_pins,final_role=role)
            self._wrappers=copy.deepcopy(wrappers);self._native_bytes=copy.deepcopy(native_bytes)
            self._target=transfer.arm_final_target(self,final_role=role)
            f.no_symlink_path(self.workspace);f.need(not self.workspace.exists(),'final workspace must be new');self.workspace.mkdir()
            for name in ('objects','scratch','logs','module-quarantine'):(self.workspace/name).mkdir()
            for name in ('home','tmp'):(self.workspace/'scratch'/name).mkdir()
            f.verify_sources(self.source_root,self.manifest)
            required=f.storage_restore_budget([self._for_runner(w) for w in wrappers],self.contract,build=False,stages=self.stages,allocation_unit=os.statvfs(self.workspace).f_frsize)
            f.need(shutil.disk_usage(self.workspace).free>=required,'insufficient measured final restore space')
            self._restore_scope();return self._scope
        except BaseException:
            self._poisoned=True;raise


class _LatestNativeReader(f.StageRunner):
    """Same-owner native reader, pinned to the actual latest producer context."""
    def __init__(self,owner):
        self._owner=owner
        super().__init__(contract=copy.deepcopy(owner.latest_contract),manifest=copy.deepcopy(owner.manifest),
            plan=copy.deepcopy(owner.plan),profiles=copy.deepcopy(owner.latest_profiles),
            identity=copy.deepcopy(owner.latest_identity),source_root=owner.source_root,
            toolchain_root=owner.toolchain_root,toolchain_inventory=copy.deepcopy(owner.inventory),
            workspace=owner.workspace,executor=self._refused)
        self.prior_root=owner.prior_root;self.prior_files=copy.deepcopy(owner.prior_files)
        self._workspace_inode=transfer.owned_dir(owner.workspace);self._source_inode=transfer.owned_dir(owner.source_root)
    @staticmethod
    def _refused(*args,**kwargs):raise f.Rejected('historical reader cannot execute')
    def check_run_age(self):
        self._owner.check_run_age();f.StageRunner.check_run_age(self)
    def read_exact(self,wrapper):
        owner=self._owner;self.check_run_age()
        f.need(transfer.owned_dir(owner.workspace)==self._workspace_inode and transfer.owned_dir(owner.source_root)==self._source_inode,'latest reader owned roots changed')
        f.need(wrapper['origin']=='LatestSuccessorOrigin' and wrapper['native_descriptor']['identity']==self.identity,
               'exact latest wrapper/identity required')
        f.need(self.identity==owner.latest_identity and self.contract==owner.latest_contract and
               self.profiles==owner.latest_profiles and self.manifest==owner.manifest and self.plan==owner.plan and
               self.workspace==owner.workspace and self.source_root==owner.source_root,'latest reader binding changed')
        # These are the same live maps already populated by the exact prior
        # validator transfer. No report or dictionary supplied by a child issues them.
        self.objects=owner.objects;self.records=owner.records
        self.predecessor_descriptors=owner.predecessor_descriptors
        self.restore_evidence_hashes=owner.restore_evidence_hashes
        before_objects=copy.deepcopy(self.objects);before_evidence=copy.deepcopy(self.restore_evidence_hashes)
        before_records=copy.deepcopy(self.records)
        before_descriptors=copy.deepcopy(self.predecessor_descriptors)
        sid=wrapper['native_descriptor']['stage_id']
        f.need(sid not in self.restore_evidence_hashes,'latest stage already admitted')
        FrozenLatestRunner._current_envelope(self,wrapper)
        f.StageRunner.read_artifacts(self,[sid],[owner._for_runner(wrapper)])
        f.need(self.objects is owner.objects and self.records is owner.records and
               self.predecessor_descriptors is owner.predecessor_descriptors and
               self.restore_evidence_hashes is owner.restore_evidence_hashes,'native latest maps detached')
        f.need(all(self.objects.get(k)==v for k,v in before_objects.items()) and
               all(self.restore_evidence_hashes.get(k)==v for k,v in before_evidence.items()) and
               self.predecessor_descriptors==before_descriptors+[wrapper['native_descriptor']],
               'native latest reader changed admitted prefix')
        f.need(self.records==before_records,'native latest reader changed compile records')
        expected=set(before_objects)|set(self.stages[sid]['modules'])
        f.need(set(self.objects)==expected and set(self.restore_evidence_hashes)==set(before_evidence)|{sid},
               'native latest complete membership differs')
        self.verify_checked_objects()
        f.need(transfer.owned_dir(owner.workspace)==self._workspace_inode and transfer.owned_dir(owner.source_root)==self._source_inode,'latest reader final owned roots changed')
        self.check_run_age()


class _ProductionNativeReader(f.StageRunner):
    """Same-owner native reader, pinned to the actual production producer context."""
    def __init__(self,owner):
        self._owner=owner
        super().__init__(contract=copy.deepcopy(owner.production_contract),manifest=copy.deepcopy(owner.manifest),
            plan=copy.deepcopy(owner.plan),profiles=copy.deepcopy(owner.production_profiles),
            identity=copy.deepcopy(owner.production_identity),source_root=owner.source_root,
            toolchain_root=owner.toolchain_root,toolchain_inventory=copy.deepcopy(owner.inventory),
            workspace=owner.workspace,executor=self._refused)
        self.prior_root=owner.prior_root;self.prior_files=copy.deepcopy(owner.prior_files)
        self._workspace_inode=transfer.owned_dir(owner.workspace);self._source_inode=transfer.owned_dir(owner.source_root)
    @staticmethod
    def _refused(*args,**kwargs):raise f.Rejected('historical reader cannot execute')
    def check_run_age(self):
        self._owner.check_run_age();f.StageRunner.check_run_age(self)
    def read_exact(self,wrapper):
        owner=self._owner;self.check_run_age()
        f.need(transfer.owned_dir(owner.workspace)==self._workspace_inode and transfer.owned_dir(owner.source_root)==self._source_inode,'production reader owned roots changed')
        f.need(wrapper['origin']=='ProductionSuccessOrigin' and wrapper['native_descriptor']['identity']==self.identity,
               'exact production wrapper/identity required')
        f.need(self.identity==owner.production_identity and self.contract==owner.production_contract and
               self.profiles==owner.production_profiles and self.manifest==owner.manifest and self.plan==owner.plan and
               self.workspace==owner.workspace and self.source_root==owner.source_root,'production reader binding changed')
        # These are the same live maps already populated by the exact prior
        # validator transfer. No report or dictionary supplied by a child issues them.
        self.objects=owner.objects;self.records=owner.records
        self.predecessor_descriptors=owner.predecessor_descriptors
        self.restore_evidence_hashes=owner.restore_evidence_hashes
        before_objects=copy.deepcopy(self.objects);before_evidence=copy.deepcopy(self.restore_evidence_hashes)
        before_records=copy.deepcopy(self.records)
        before_descriptors=copy.deepcopy(self.predecessor_descriptors)
        sid=wrapper['native_descriptor']['stage_id']
        f.need(sid not in self.restore_evidence_hashes,'production stage already admitted')
        FrozenLatestRunner._current_envelope(self,wrapper)
        f.StageRunner.read_artifacts(self,[sid],[owner._for_runner(wrapper)])
        f.need(self.objects is owner.objects and self.records is owner.records and
               self.predecessor_descriptors is owner.predecessor_descriptors and
               self.restore_evidence_hashes is owner.restore_evidence_hashes,'native production maps detached')
        f.need(all(self.objects.get(k)==v for k,v in before_objects.items()) and
               all(self.restore_evidence_hashes.get(k)==v for k,v in before_evidence.items()) and
               self.predecessor_descriptors==before_descriptors+[wrapper['native_descriptor']],
               'native production reader changed admitted prefix')
        f.need(self.records==before_records,'native production reader changed compile records')
        expected=set(before_objects)|set(self.stages[sid]['modules'])
        f.need(set(self.objects)==expected and set(self.restore_evidence_hashes)==set(before_evidence)|{sid},
               'native production complete membership differs')
        self.verify_checked_objects()
        f.need(transfer.owned_dir(owner.workspace)==self._workspace_inode and transfer.owned_dir(owner.source_root)==self._source_inode,'production reader final owned roots changed')
        self.check_run_age()
