"""Fixed three-run clean-source campaign native seam; unchanged StageRunner validates every artifact."""
from __future__ import annotations
import copy,os,shutil,tarfile,time
from pathlib import Path
import fresh_stage as f
import continuation_policy as p
import clean_policy as campaign
class CleanRunner(f.StageRunner):
    def __init__(self,*,budget,**kwargs):
        campaign.require_latest_selection()
        self.budget=budget;self._used=False;self._poisoned=False
        super().__init__(**kwargs)
        f.need(self.owned_downloads is None,'retained clean native tars required')
        code=Path(__file__).absolute().parent
        self.prior_contract=f.pinned_load(code/'prior_clean_contract.json',campaign.PRIOR_CONTRACT_SHA256)
        self.prior_profiles=f.pinned_load(code/'prior_clean_profiles.json',campaign.PRIOR_PROFILES_SHA256)
        self.latest_contract=f.pinned_load(code/'latest_clean_contract.json',campaign.LATEST_CONTRACT_SHA256)
        self.latest_profiles=f.pinned_load(code/'latest_clean_profiles.json',campaign.LATEST_PROFILES_SHA256)
        f.need(f.file_sha(Path(f.__file__))==campaign.PRIOR_CLEAN_IDENTITY['runner_sha256'] and
               f.sha(f.json_bytes(self.manifest))==campaign.PRIOR_CLEAN_IDENTITY['source_manifest_sha256'] and
               f.sha(f.json_bytes(self.plan))==campaign.PRIOR_CLEAN_IDENTITY['plan_sha256'],
               'original clean native implementation/source/plan changed')
    def check_run_age(self):
        campaign.require_latest_selection();f.need(not self._poisoned,'poisoned clean runner');self.budget.check();super().check_run_age();self.budget.check()
    def command(self,module,phase,profile,env,deadline):
        self.check_run_age()
        return super().command(module,phase,profile,env,min(deadline,self.budget.deadline))

    @staticmethod
    def _receipt_envelope(wrapper,context):
        """Additional exact limits omitted by baseline read_artifacts; never relax it."""
        path=Path(wrapper['archive_path']);d=wrapper['native_descriptor']
        f.need(f.file_sha(path)==d['archive_sha256'],'archive hash mismatch before admission')
        with tarfile.open(path,'r:') as archive:
            members=[m for m in archive.getmembers() if m.name=='receipt.json']
            f.need(len(members)==1 and members[0].isreg() and 0<members[0].size<=context.contract['max_artifact_bytes'],
                   'invalid receipt envelope')
            raw=archive.extractfile(members[0]).read()
        f.need(f.sha(raw)==d['receipt_sha256'],'raw receipt digest mismatch')
        receipt=f.parse_json(raw)
        f.need(receipt.get('schema')=='fresh-stage-receipt-v1' and receipt.get('proof_pass_claimed') is False,
               'receipt schema/claim mismatch')
        def file_info(info):
            p.keys(info,{'bytes','sha256'},'receipt file metadata')
            f.need(type(info['bytes']) is int and info['bytes']>=0,'invalid receipt file byte count')
            p.digest(info['sha256'],'receipt file digest')
        for name,info in receipt['files'].items():
            f.safe_rel(name);file_info(info)
        f.need(sum(x['bytes'] for x in receipt['files'].values())<=context.contract['max_stage_output_bytes'],
               'own output/log budget exceeded')
        for record in receipt['modules']:
            profile=context.profiles['profiles'][context.profiles['module_profiles'][record['module']]]
            for phase in ('compile','check'):
                command=record[phase]
                for stream in ('stdout','stderr'):file_info(command[stream])
                p.integer(command['timeout_seconds'],'recorded command timeout',profile[phase+'_timeout_seconds'])
                f.need(type(command['exit_code']) is int,'boolean/invalid command exit')
                f.need(sum(command[s]['bytes'] for s in ('stdout','stderr'))<=context.contract['max_log_bytes'],
                       'recorded command log bound exceeded')
        return raw,receipt

    def read_artifacts(self,expected,descriptors):
        self.check_run_age()
        f.need(expected==[sid for sid in self.stages if sid in set(expected)] and
               [d['stage_id'] for d in descriptors]==expected,'exact ordered campaign native scope required')
        f.need(sum(d['archive_bytes'] for d in descriptors)<=self.contract['max_restored_bytes'],'campaign raw aggregate cap exceeded')
        prior=_PriorCleanNativeReader(self);latest=_LatestCleanNativeReader(self)
        for descriptor in descriptors:
            self.check_run_age();sid=descriptor['stage_id']
            if campaign.origin_for_stage(sid)=='PriorCleanOrigin':prior.read_exact(descriptor)
            elif campaign.origin_for_stage(sid)=='LatestCleanOrigin':latest.read_exact(descriptor)
            else:
                f.need(descriptor['identity']==self.identity,'current campaign identity changed')
                self._receipt_envelope({'archive_path':descriptor['archive_path'],'native_descriptor':{k:v for k,v in descriptor.items() if k!='archive_path'}},self)
                f.StageRunner.read_artifacts(self,[sid],[descriptor])
            self.verify_checked_objects();self.check_run_age()
        f.need(self.predecessor_descriptors==[{k:v for k,v in d.items() if k!='archive_path'} for d in descriptors],
               'complete campaign native predecessor map differs')
        f.need(set(self.objects)=={m for sid in expected for m in self.stages[sid]['modules']},'complete campaign native object map differs')
        self.verify_checked_objects();self.check_run_age()
    def run(self,sid,descriptors,producer_job):
        f.need(not self._used and not self._poisoned,'clean runner already used');self._used=True
        try:
            f.need(campaign.origin_for_stage(sid)=='CurrentOrigin','prior-clean stage cannot be rebuilt')
            result=super().run(sid,descriptors,producer_job)
            f.need(sum(d['archive_bytes'] for d in descriptors)+result['archive_bytes']<=self.contract['max_restored_bytes'],'clean raw aggregate cap exceeded')
            self.check_run_age();return result
        except BaseException:self._poisoned=True;raise
    def restore_final(self,role,descriptors):
        f.need(role in ('export_target','fresh_kernel') and not self._used and not self._poisoned,'invalid or repeated clean restore');self._used=True
        try:
            f.no_symlink_path(self.workspace);f.need(not self.workspace.exists(),'final workspace must be new');self.workspace.mkdir()
            for name in ('objects','scratch','logs','module-quarantine'):(self.workspace/name).mkdir()
            for name in ('home','tmp'):(self.workspace/'scratch'/name).mkdir()
            f.need(not list((self.workspace/'objects').iterdir()),'initial project object tree must be empty')
            f.verify_sources(self.source_root,self.manifest)
            required=f.storage_restore_budget(descriptors,self.contract,build=False,stages=self.stages,allocation_unit=os.statvfs(self.workspace).f_frsize)
            f.need(shutil.disk_usage(self.workspace).free>=required,'insufficient measured final restore space')
            self.read_artifacts(list(self.stages),descriptors)
            f.need(set(self.objects)==set(self.entries),'clean restored module closure incomplete')
            self.verify_checked_objects();f.verify_sources(self.source_root,self.manifest);self.check_run_age()
        except BaseException:self._poisoned=True;raise


def _owned_dir(path):
    f.no_symlink_path(path);st=path.lstat()
    f.need(path.is_dir(),'owned native root is not a directory')
    return st.st_dev,st.st_ino


class _PriorCleanNativeReader(f.StageRunner):
    """Original-context read-only admission into this owner's shared native maps."""
    def __init__(self,owner):
        self._owner=owner
        super().__init__(contract=copy.deepcopy(owner.prior_contract),manifest=copy.deepcopy(owner.manifest),
            plan=copy.deepcopy(owner.plan),profiles=copy.deepcopy(owner.prior_profiles),
            identity=copy.deepcopy(campaign.PRIOR_CLEAN_IDENTITY),source_root=owner.source_root,
            toolchain_root=owner.toolchain_root,toolchain_inventory=copy.deepcopy(owner.inventory),
            workspace=owner.workspace,executor=self._refused)
        self._workspace_inode=_owned_dir(owner.workspace);self._source_inode=_owned_dir(owner.source_root)
    @staticmethod
    def _refused(*args,**kwargs):raise f.Rejected('prior-clean native reader cannot execute')
    def check_run_age(self):
        self._owner.check_run_age();f.StageRunner.check_run_age(self)
    def read_exact(self,descriptor):
        owner=self._owner;self.check_run_age();sid=descriptor['stage_id']
        f.need(campaign.origin_for_stage(sid)=='PriorCleanOrigin' and descriptor['identity']==self.identity,
               'exact prior-clean descriptor and identity required')
        f.need(_owned_dir(owner.workspace)==self._workspace_inode and _owned_dir(owner.source_root)==self._source_inode,
               'prior-clean native owned roots changed')
        f.need(self.identity==campaign.PRIOR_CLEAN_IDENTITY and self.contract==owner.prior_contract and
               self.profiles==owner.prior_profiles and self.manifest==owner.manifest and self.plan==owner.plan and
               self.workspace==owner.workspace and self.source_root==owner.source_root,'prior-clean reader binding changed')
        self.objects=owner.objects;self.records=owner.records
        self.predecessor_descriptors=owner.predecessor_descriptors;self.restore_evidence_hashes=owner.restore_evidence_hashes
        before_objects=copy.deepcopy(self.objects);before_evidence=copy.deepcopy(self.restore_evidence_hashes)
        before_records=copy.deepcopy(self.records);before_descriptors=copy.deepcopy(self.predecessor_descriptors)
        f.need(sid not in self.restore_evidence_hashes,'prior-clean stage already admitted')
        CleanRunner._receipt_envelope({'archive_path':descriptor['archive_path'],
            'native_descriptor':{k:v for k,v in descriptor.items() if k!='archive_path'}},self)
        f.StageRunner.read_artifacts(self,[sid],[descriptor])
        native={k:v for k,v in descriptor.items() if k!='archive_path'}
        f.need(self.objects is owner.objects and self.records is owner.records and
               self.predecessor_descriptors is owner.predecessor_descriptors and
               self.restore_evidence_hashes is owner.restore_evidence_hashes,'prior-clean native maps detached')
        f.need(all(self.objects.get(k)==v for k,v in before_objects.items()) and
               all(self.restore_evidence_hashes.get(k)==v for k,v in before_evidence.items()) and
               self.predecessor_descriptors==before_descriptors+[native] and self.records==before_records,
               'prior-clean native reader changed admitted prefix')
        f.need(set(self.objects)==set(before_objects)|set(self.stages[sid]['modules']) and
               set(self.restore_evidence_hashes)==set(before_evidence)|{sid},'prior-clean complete membership differs')
        self.verify_checked_objects()
        f.need(_owned_dir(owner.workspace)==self._workspace_inode and _owned_dir(owner.source_root)==self._source_inode,
               'prior-clean native final owned roots changed')
        self.check_run_age()


class _LatestCleanNativeReader(f.StageRunner):
    """Latest-context read-only admission into this owner's shared native maps."""
    def __init__(self,owner):
        self._owner=owner
        super().__init__(contract=copy.deepcopy(owner.latest_contract),manifest=copy.deepcopy(owner.manifest),
            plan=copy.deepcopy(owner.plan),profiles=copy.deepcopy(owner.latest_profiles),
            identity=copy.deepcopy(campaign.LATEST_CLEAN_IDENTITY),source_root=owner.source_root,
            toolchain_root=owner.toolchain_root,toolchain_inventory=copy.deepcopy(owner.inventory),
            workspace=owner.workspace,executor=self._refused)
        self._workspace_inode=_owned_dir(owner.workspace);self._source_inode=_owned_dir(owner.source_root)
    @staticmethod
    def _refused(*args,**kwargs):raise f.Rejected('latest-clean native reader cannot execute')
    def check_run_age(self):
        self._owner.check_run_age();f.StageRunner.check_run_age(self)
    def read_exact(self,descriptor):
        owner=self._owner;self.check_run_age();sid=descriptor['stage_id']
        f.need(campaign.origin_for_stage(sid)=='LatestCleanOrigin' and descriptor['identity']==self.identity,
               'exact latest-clean descriptor and identity required')
        f.need(_owned_dir(owner.workspace)==self._workspace_inode and _owned_dir(owner.source_root)==self._source_inode,
               'latest-clean native owned roots changed')
        f.need(self.identity==campaign.LATEST_CLEAN_IDENTITY and self.contract==owner.latest_contract and
               self.profiles==owner.latest_profiles and self.manifest==owner.manifest and self.plan==owner.plan and
               self.workspace==owner.workspace and self.source_root==owner.source_root,'latest-clean reader binding changed')
        self.objects=owner.objects;self.records=owner.records
        self.predecessor_descriptors=owner.predecessor_descriptors;self.restore_evidence_hashes=owner.restore_evidence_hashes
        before_objects=copy.deepcopy(self.objects);before_evidence=copy.deepcopy(self.restore_evidence_hashes)
        before_records=copy.deepcopy(self.records);before_descriptors=copy.deepcopy(self.predecessor_descriptors)
        f.need(sid not in self.restore_evidence_hashes,'latest-clean stage already admitted')
        CleanRunner._receipt_envelope({'archive_path':descriptor['archive_path'],
            'native_descriptor':{k:v for k,v in descriptor.items() if k!='archive_path'}},self)
        f.StageRunner.read_artifacts(self,[sid],[descriptor])
        native={k:v for k,v in descriptor.items() if k!='archive_path'}
        f.need(self.objects is owner.objects and self.records is owner.records and
               self.predecessor_descriptors is owner.predecessor_descriptors and
               self.restore_evidence_hashes is owner.restore_evidence_hashes,'latest-clean native maps detached')
        f.need(all(self.objects.get(k)==v for k,v in before_objects.items()) and
               all(self.restore_evidence_hashes.get(k)==v for k,v in before_evidence.items()) and
               self.predecessor_descriptors==before_descriptors+[native] and self.records==before_records,
               'latest-clean native reader changed admitted prefix')
        f.need(set(self.objects)==set(before_objects)|set(self.stages[sid]['modules']) and
               set(self.restore_evidence_hashes)==set(before_evidence)|{sid},'latest-clean complete membership differs')
        self.verify_checked_objects()
        f.need(_owned_dir(owner.workspace)==self._workspace_inode and _owned_dir(owner.source_root)==self._source_inode,
               'latest-clean native final owned roots changed')
        self.check_run_age()
