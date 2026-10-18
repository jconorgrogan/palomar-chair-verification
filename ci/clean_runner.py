"""Same-run clean native seam; unchanged StageRunner validates every artifact."""
from __future__ import annotations
import copy,os,shutil,tarfile,time
from pathlib import Path
import fresh_stage as f
import continuation_policy as p
class CleanRunner(f.StageRunner):
    def __init__(self,*,budget,**kwargs):
        self.budget=budget;self._used=False;self._poisoned=False
        super().__init__(**kwargs)
        f.need(self.owned_downloads is None,'retained clean native tars required')
    def check_run_age(self):
        f.need(not self._poisoned,'poisoned clean runner');self.budget.check();super().check_run_age();self.budget.check()
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
        for d in descriptors:self._receipt_envelope({'archive_path':d['archive_path'],'native_descriptor':{k:v for k,v in d.items() if k!='archive_path'}},self)
        result=super().read_artifacts(expected,descriptors)
        self.verify_checked_objects();self.check_run_age();return result
    def run(self,sid,descriptors,producer_job):
        f.need(not self._used and not self._poisoned,'clean runner already used');self._used=True
        try:
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
