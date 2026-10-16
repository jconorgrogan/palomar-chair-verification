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
import three_context_policy as p
import three_context_execution_policy as ep
import three_context_local as local
import checked_transfer as transfer
from three_context_current_transport import CurrentOriginTransport

PRIOR_FILES_SHA='9618bc2900517a9234254ddf2a2ea6fb3c78f643bd12f11967f986f49e7dde1d'

class ThreeContextRunner(f.StageRunner):
    def __init__(self,*,selection,bundle,integration_pins,current_authority,prior_root,admission_root,
                 prior_files_bytes,old_manifest,prior_manifest,source_delta,prior_contract,
                 host_deadline_monotonic,**kwargs):
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
        native['wrappers']=scope['historical_native_view']
        transfer_scope={'origin_by_stage':{r.stage_id:type(r).__name__ for r in self.selection.rows},
            'expected_native_descriptors':[w['native_descriptor'] for w in native['wrappers']],
            'expected_full_native_descriptors':scope['native_descriptors'],'expected_objects':scope['historical_objects'],
            'current_identity':self.identity,'current_manifest':self.manifest,'current_contract':self.contract}
        # Final v2 transfer request shape is bound explicitly during integration.
        if scope['target_stage'] is not None:transfer_scope.update(target_stage=scope['target_stage'])
        else:transfer_scope.update(target_stage=None,final_role=scope['final_role'])
        request={'schema':'inactive-checked-transfer-request-v2','native':native,
            'native_selection_utf8':selection_raw.decode(),'native_selection_sha256':p.sha(selection_raw),'scope':transfer_scope}
        raw=p.json_bytes(request)
        if scope['historical_stage_ids']:
            cap=transfer.admit_historical(request_bytes=raw,request_sha256=p.sha(raw),source_root=str(self.source_root),
                workspace=str(self.workspace.parent/(self.workspace.name+'-historical-validation')),
                admission_root=str(self.admission_root),historical_root=str(self.prior_root),deadline_monotonic=self.host_deadline)
            self._transfer=transfer.transfer_checked(cap,self._target)
        else:
            f.need(not scope['historical_objects'],'empty history has objects')
            self._transfer=None
        current=[w for w in wrappers if w['origin']=='CurrentOrigin']
        need=f.storage_restore_budget([self._for_runner(w) for w in current],self.contract,build=scope['target_stage'] is not None,
            stages=self.stages,allocation_unit=os.statvfs(self.workspace).f_frsize)
        f.need(shutil.disk_usage(self.workspace).free>=need,'insufficient measured current restore/output space after historical transfer')
        for wrapper in current:
            self.check_run_age();self._current_envelope(wrapper);sid=wrapper['native_descriptor']['stage_id']
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
