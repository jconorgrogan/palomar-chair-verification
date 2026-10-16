"""Explicit two-protocol continuation, never a same-run identity bypass.

Old payloads are verified by the byte-identical original modern StageRunner.
Only their verified objects are atomically moved into the new complete namespace.
Current payloads and fresh execution use the byte-identical reviewed C readonly
runner. Native receipts/descriptors preserve their original identities.
"""
from __future__ import annotations
import copy
import os
from pathlib import Path
import shutil
import stat
import tarfile
import fresh_stage as f
from original import fresh_stage as old_f
import continuation_policy as p


def admission_certificate(wrapper,raw,receipt,identity,contract):
    return {'schema':'old-modern-original-validator-admission-v1',
        'status':'original_receipt_validated_objects_moved_only','proof_pass_claimed':False,
        'original_native_descriptor':wrapper['native_descriptor'],
        'raw_descriptor_sha256':wrapper['raw_descriptor_sha256'],
        'original_receipt_sha256':f.sha(raw),'source_delta_sha256':contract.get('source_delta_sha256'),
        'successor_identity':identity,
        'old_validator_sha256':p.OLD_RUNNER,'new_validator_sha256':contract.get('runner_sha256'),
        'objects':{name:digest for rec in receipt['modules'] for name,digest in rec['outputs'].items()},
        'claim':'Cross-run checked-object admission; original receipt is unchanged; not a fresh source replay.'}


def mixed_storage_budget(wrappers, contract, *, stages, current_identity, build=True, allocation_unit=4096):
    native=[{**copy.deepcopy(w['native_descriptor']), 'archive_path':w['archive_path']} for w in wrappers]
    f.need(type(allocation_unit) is int and allocation_unit>0,'invalid mixed restore allocation unit')
    unit=max(4096,allocation_unit);rounded=lambda n:((n+unit-1)//unit)*unit
    extra=0
    # Budget the original validator's transient second object copy using actual
    # tar headers, allocation rounding, inode and directory allowances. Retained
    # raw receipt and the exact new admission certificate are additional. This
    # is preflight sizing only; every old byte still needs original validation.
    for wrapper in wrappers:
        if wrapper['origin']!='OldOrigin':continue
        directories=set();raw=None
        with tarfile.open(wrapper['archive_path'],'r:') as archive:
            for member in archive:
                name=f.safe_rel(member.name)
                f.need(member.isreg() and not member.pax_headers,'nonregular original storage member')
                if name.startswith('objects/'):
                    extra+=rounded(member.size)+unit
                    directories.update(str(x) for x in Path(name.removeprefix('objects/')).parents if str(x)!='.')
                if name=='receipt.json':
                    f.need(raw is None and 0<member.size<=contract['max_artifact_bytes'],'invalid original receipt budget')
                    raw=archive.extractfile(member).read()
        f.need(raw is not None,'missing original receipt budget')
        receipt=f.parse_json(raw)
        f.need(type(receipt.get('modules')) is list and all(type(x) is dict and type(x.get('outputs')) is dict for x in receipt['modules']),'invalid receipt sizing metadata')
        certificate=admission_certificate(wrapper,raw,receipt,current_identity,contract)
        extra+=unit*(len(directories)+6)+rounded(len(raw))+unit+rounded(len(f.json_bytes(certificate)))+unit
    return f.storage_restore_budget(native,contract,build=build,stages=stages,
        allocation_unit=allocation_unit)+extra


class ContinuationRunner(f.StageRunner):
    def __init__(self, *, selection, old_context, source_delta, **kwargs):
        super().__init__(**kwargs)
        self.selection=selection;self.old_context=copy.deepcopy(old_context)
        self.source_delta=copy.deepcopy(source_delta)
        p.validate_contexts(selection,old_context,{'contract':self.contract,'manifest':self.manifest,
            'plan':self.plan,'profiles':self.profiles,'identity':self.identity,'inventory':self.inventory,
            'source_delta':self.source_delta})
        self._mixed_admission_used=False
        self._build_wrappers=None

    def check_run_age(self):
        p.check_deadline(self.old_context['identity'],self.identity,current_max_age=self.contract['max_run_age_seconds'])

    def run(self,sid,wrappers,producer_job):
        f.need(isinstance(self.selection.row(sid),p.CurrentOrigin),'reused stage must never receive a fresh compile artifact')
        f.need(self._build_wrappers is None,'build adapter already used')
        p.validate_wrappers(self.selection,self.stages[sid]['required_predecessors'],wrappers,
            old_identity=self.old_context['identity'],current_identity=self.identity,plan=self.plan)
        required=mixed_storage_budget(wrappers,self.contract,stages=self.stages,current_identity=self.identity,
            allocation_unit=os.statvfs(self.workspace.parent).f_frsize)
        f.need(shutil.disk_usage(self.workspace.parent).free>=required,'insufficient mixed-protocol restore space')
        self._build_wrappers=copy.deepcopy(wrappers)
        # Native descriptors are supplied only to the unchanged budget code;
        # read_predecessors below restores through the explicit typed adapter.
        return super().run(sid,[self._for_runner(w) for w in wrappers],producer_job)

    def read_predecessors(self,sid,descriptors):
        f.need(self._build_wrappers is not None,'missing typed build origins')
        f.need(descriptors==[self._for_runner(w) for w in self._build_wrappers],
            'native descriptor bridge differs from frozen typed wrappers')
        return self.read_artifacts(self.stages[sid]['required_predecessors'],self._build_wrappers)

    def read_artifacts(self,expected,wrappers):
        self.check_run_age()
        f.need(not self._mixed_admission_used and not self.objects and not self.predecessor_descriptors,
               'mixed restore must start from an empty validation state')
        self._mixed_admission_used=True
        total=p.validate_wrappers(self.selection,expected,wrappers,old_identity=self.old_context['identity'],
            current_identity=self.identity,plan=self.plan)
        f.need(total<=self.contract['max_restored_bytes'],'aggregate mixed-origin budget exceeded')
        f.verify_sources(self.source_root,self.manifest)
        f.exact_tree(self.workspace/'objects',set())
        old_wrappers=[w for w in wrappers if w['origin']=='OldOrigin']
        current_wrappers=[w for w in wrappers if w['origin']=='CurrentOrigin']
        old_workspace=self.workspace/'old-validation'
        f.no_symlink_path(old_workspace);f.need(not old_workspace.exists(),'old validation workspace must be new')
        old_workspace.mkdir();(old_workspace/'deps').mkdir()
        old=old_f.StageRunner(contract=self.old_context['contract'],manifest=self.old_context['manifest'],
            plan=self.old_context['plan'],profiles=self.old_context['profiles'],identity=self.old_context['identity'],
            source_root=self.source_root,toolchain_root=self.toolchain_root,toolchain_inventory=self.inventory,
            workspace=old_workspace,executor=self.executor)
        # The old validator never compiles/executes research code here. It uses
        # the original manifest for exact receipt/source/import/profile checks.
        # The explicit source reconciliation proves every reused module equal.
        old_envelopes={}
        for wrapper in old_wrappers:
            old_envelopes[wrapper['native_descriptor']['stage_id']]=self._receipt_envelope(wrapper,old)
        old.read_artifacts([w['native_descriptor']['stage_id'] for w in old_wrappers],
            [self._for_runner(w) for w in old_wrappers])
        checked={name.removeprefix('objects/'):sha for outputs in old.objects.values() for name,sha in outputs.items()}
        f.exact_tree(old_workspace/'deps',set(checked))
        for name,digest in checked.items():
            source=old_workspace/'deps'/name
            f.no_symlink_path(source)
            f.need(stat.S_ISREG(source.lstat().st_mode),'old validation object replaced by nonregular file')
            f.need(source.stat().st_nlink==1 and f.file_sha(source)==digest,'old validation object mutated/shared before seeding')
            destination=self.workspace/'objects'/name;f.no_symlink_path(destination)
            f.need(not destination.exists(),'old seed shadows an object')
            destination.parent.mkdir(parents=True,exist_ok=True);source.rename(destination)
            f.need(destination.stat().st_nlink==1 and f.file_sha(destination)==digest,'old seed move hash/inode mismatch')
            destination.chmod(0o444)
        shutil.rmtree(old_workspace)  # Only our new fully verified quarantine.
        self.objects=copy.deepcopy(old.objects)
        self.predecessor_descriptors=copy.deepcopy(old.predecessor_descriptors)
        self._canonicalize()
        for wrapper in old_wrappers:
            sid=wrapper['native_descriptor']['stage_id'];raw,receipt=old_envelopes[sid]
            evidence=self.workspace/'restore-evidence'/sid
            f.need(not evidence.exists(),'old admission evidence collision');evidence.mkdir(parents=True)
            (evidence/'receipt.json').write_bytes(raw)
            certificate=admission_certificate(wrapper,raw,receipt,self.identity,self.contract)
            (evidence/'admission.json').write_bytes(f.json_bytes(certificate))
            for path in f.regular_tree(evidence).values():path.chmod(0o444)
            self.restore_evidence_hashes[sid]={name:f.file_sha(path) for name,path in f.regular_tree(evidence).items()}
        for wrapper in current_wrappers:
            self.check_run_age();self._receipt_envelope(wrapper,self)
            sid=wrapper['native_descriptor']['stage_id']
            # Exact readonly protocol checks are unchanged. Seeded old native
            # predecessor identities remain visible in the current receipt chain.
            f.StageRunner.read_artifacts(self,[sid],[self._for_runner(wrapper)])
            self._canonicalize()
        f.need(self.predecessor_descriptors==[w['native_descriptor'] for w in wrappers],
               'restored native map differs from exact requested map')
        expected_hashes={name.removeprefix('objects/'):sha for outputs in self.objects.values() for name,sha in outputs.items()}
        f.exact_tree(self.workspace/'objects',set(expected_hashes))
        f.need(expected_hashes=={name:f.file_sha(path) for name,path in f.regular_tree(self.workspace/'objects').items()},
               'restored tree differs from union of declared verified outputs')
        f.need(checked=={name:f.file_sha(self.workspace/'objects'/name) for name in checked},'verified old objects mutated')
        self.verify_checked_objects()
        f.verify_sources(self.source_root,self.manifest);self.check_run_age()

    @staticmethod
    def _for_runner(wrapper):
        return {**copy.deepcopy(wrapper['native_descriptor']),'archive_path':wrapper['archive_path']}

    def _canonicalize(self):
        order={sid:i for i,sid in enumerate(self.stages)}
        self.predecessor_descriptors.sort(key=lambda d:order[d['stage_id']])

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
