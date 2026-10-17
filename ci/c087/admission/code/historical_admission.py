"""Inactive C087 historical-admission constructor seam; no executable authority.

Use only inside the parent's dedicated no-token/no-network permanently guarded
admission child. It must never be used as a general StageRunner or in a process
that will later install a runtime. The parent separately owns process cleanup,
shared deadline, rehash, and any subsequent diagnostic authorization.
"""
from __future__ import annotations
import copy
from dataclasses import dataclass
import math
import os
import re
from pathlib import Path
import shutil
import time
from frozen_native import GRAPH, PINS_SHA256
if GRAPH is None:
    raise RuntimeError("call frozen_native.load_frozen_graph(canonical_root) before importing admission code")
from terminal_certificate import TerminalCertificate, require, GLOBAL_RAW

f, p, ep, local, transfer = GRAPH.f, GRAPH.p, GRAPH.ep, GRAPH.local, GRAPH.transfer
Native = GRAPH.runner.ThreeContextRunner
_CONSUMED_SESSIONS = set()

@dataclass(frozen=True)
class AdmissionReport:
    """Inert immutable metadata, explicitly not an execution capability."""
    raw_bytes: bytes

    @property
    def data(self):
        return p.parse_json(self.raw_bytes)

    @property
    def sha256(self):
        return p.sha(self.raw_bytes)

class HistoricalAdmissionRunner(f.StageRunner):
    """Explicit constructor, preserving every non-authority native invariant.

    The five native methods below are the exact original function objects.
    ThreeContextRunner.__init__, run and restore_final are never invoked.
    """
    check_run_age = Native.check_run_age
    _for_runner = staticmethod(Native._for_runner)
    _native_inputs = Native._native_inputs
    _current_envelope = Native._current_envelope
    _restore_scope = Native._restore_scope

    def __init__(self, *, selection, bundle, integration_pins, prior_root, admission_root,
                 prior_files_bytes, old_manifest, prior_manifest, source_delta, prior_contract,
                 host_deadline_monotonic, certificate_raw, parent_certificate_sha256,
                 expected_session_nonce, acquisition_root, wrappers, native_bytes,
                 contract, manifest, plan, profiles, identity, source_root, toolchain_root,
                 toolchain_inventory, workspace, owned_downloads=None):
        self._poisoned = False
        self._used = False
        self._last_wall = None
        self._wrappers = None
        self._target = None
        self._report = None
        try:
            f.need(type(self) is HistoricalAdmissionRunner, 'admission seam may not be subclassed')
            f.need(type(expected_session_nonce) is str and re.fullmatch('[0-9a-f]{64}', expected_session_nonce),
                   'parent admission session nonce required')
            f.need(expected_session_nonce not in _CONSUMED_SESSIONS, 'parent admission session already consumed')
            _CONSUMED_SESSIONS.add(expected_session_nonce)
            GRAPH.verify()
            f.need(type(host_deadline_monotonic) in (int,float) and math.isfinite(host_deadline_monotonic),
                   'finite shared host deadline required')
            self.host_deadline = float(host_deadline_monotonic)
            f.need(0 < self.host_deadline-time.monotonic() <= contract['job_timeout_seconds'],
                   'host deadline expired or renewed')
            # The ONLY replaced native constructor boundary: live CurrentOriginTransport
            # authority becomes externally authenticated terminal certificate input.
            self._certificate = TerminalCertificate(raw=certificate_raw, parent_sha256=parent_certificate_sha256,
                expected_session_nonce=expected_session_nonce, acquisition_root=acquisition_root,
                host_deadline_monotonic=host_deadline_monotonic, identity=identity,
                inventory=toolchain_inventory, selection=selection, bundle=bundle, plan=plan,
                wrappers=wrappers, native_bytes=native_bytes)
            self.selection = ep.validate_execution_context(plan=plan, profiles=profiles,
                current_contract=contract, current_manifest=manifest, old_manifest=old_manifest,
                prior_manifest=prior_manifest, source_delta=source_delta, inventory=toolchain_inventory,
                current_identity=identity, selection=selection, bundle=bundle,
                integration_pins=integration_pins, prior_contract=prior_contract)
            self.bundle = bundle
            self.integration_pins = copy.deepcopy(integration_pins)
            self.prior_contract = copy.deepcopy(prior_contract)
            self.prior_root = local.canonical(str(prior_root))
            self.admission_root = local.canonical(str(admission_root))
            f.need(type(prior_files_bytes) is bytes and p.sha(prior_files_bytes) == GRAPH.runner.PRIOR_FILES_SHA,
                   'historical implementation inventory changed')
            self.prior_files = p.parse_json(prior_files_bytes)
            self.source_delta = copy.deepcopy(source_delta)
            self.old_manifest = copy.deepcopy(old_manifest)
            self.prior_manifest = copy.deepcopy(prior_manifest)
            # Additional restore-scope validation is deliberately before StageRunner
            # construction and before ANY workspace/scaffold creation.
            self._scope = ep.validate_restore_scope(plan=plan, selection=self.selection, bundle=bundle,
                wrappers=self._certificate.native_wrappers, native_bytes=native_bytes,
                current_identity=identity, integration_pins=integration_pins, target_stage='build_087')
            super().__init__(contract=copy.deepcopy(contract), manifest=copy.deepcopy(manifest),
                plan=copy.deepcopy(plan), profiles=copy.deepcopy(profiles), identity=copy.deepcopy(identity),
                source_root=source_root, toolchain_root=toolchain_root,
                toolchain_inventory=copy.deepcopy(toolchain_inventory), workspace=workspace,
                executor=self._executor_refused, owned_downloads=owned_downloads)
            f.need(self.owned_downloads is None, 'all selected native tars must remain retained in this adapter')
            self.check_run_age()
            self._wrappers = copy.deepcopy(self._certificate.native_wrappers)
            self._native_bytes = copy.deepcopy(native_bytes)
            self._assert_exact_scope()
            self._check_paths()
            self._input_binding = self._state_binding()
            self._constructor_deadline = self.host_deadline
            self._certificate.check_age()
            GRAPH.verify()
            self._certificate.check_age()
            self.check_run_age()
        except BaseException:
            self._poisoned = True
            raise

    def _assert_exact_scope(self):
        scope = self._scope.data
        expected = self.stages['build_087']['required_predecessors']
        require(scope['target_stage'], 'build_087', 'native scope target')
        require(scope['final_role'], None, 'final-role exclusion')
        require(scope['expected_stage_ids'], expected, 'native ordered C087 predecessor scope')
        require(len(expected), 85, 'C087 predecessor count')
        require(sum(len(self.stages[s]['modules']) for s in expected), 6218, 'C087 predecessor modules')
        require(len(scope['historical_stage_ids']), 47, 'earlier predecessor stages')
        require(len(scope['current_stage_ids']), 38, 'latest predecessor stages')
        f.need('build_087' not in expected, 'target cannot be restored')
        baseline = p.cumulative_raw_budget(self.selection, {})
        require(baseline.total_bytes, GLOBAL_RAW, 'full48 raw baseline')
        require(len(baseline.entries), 48, 'global historical ledger count')
        require(scope['raw_archive_bytes'], self._certificate.data['accounting']['charged_raw_bytes'], 'unchanged raw ledger')

    def _check_paths(self):
        self.source_root = local.canonical(str(self.source_root))
        self.workspace = local.canonical(str(self.workspace))
        self.toolchain_root = local.canonical(str(self.toolchain_root))
        self._parent_inode = transfer.owned_dir(self.workspace.parent)
        self._source_inode = transfer.owned_dir(self.source_root)
        self._runtime_inode = transfer.owned_dir(self.toolchain_root)
        f.need(not self.workspace.exists(), 'admission workspace must be new')
        f.need(not any(self.toolchain_root.iterdir()), 'runtime placeholder must be empty/inventory-only')
        roots = (self.workspace, self.source_root, self.toolchain_root, self._certificate.root,
                 self.prior_root, self.admission_root)
        for i, left in enumerate(roots):
            for right in roots[i+1:]:
                transfer.disjoint(left, right)
        historical = self.workspace.parent/(self.workspace.name+'-historical-validation')
        f.need(not historical.exists(), 'historical admission workspace must be new')
        for root in roots:
            if root != self.workspace:
                transfer.disjoint(historical, root)
        f.verify_sources(self.source_root, self.manifest)
        # Invoke nested immutable-loader checks now, before creating a workspace.
        transfer.check_fixed_files(self.admission_root, self.prior_root)

    def _state_binding(self):
        return p.object_sha({'contract':self.contract,'manifest':self.manifest,'plan':self.plan,
            'profiles':self.profiles,'identity':self.identity,'inventory':self.inventory,
            'selection':self.selection.raw_sha256,'bundle':self.bundle.raw_sha256,
            'integration_pins':self.integration_pins,'prior_contract':self.prior_contract,
            'source_delta':self.source_delta,'old_manifest':self.old_manifest,'prior_manifest':self.prior_manifest,
            'prior_files':self.prior_files,'wrappers':self._wrappers,'scope_sha256':self._scope.sha256,
            'native_bytes':{sid:{key:p.sha(raw) for key,raw in pair.items()} for sid,pair in self._native_bytes.items()},
            'source_root':str(self.source_root),'runtime_root':str(self.toolchain_root),
            'workspace':str(self.workspace),'prior_root':str(self.prior_root),'admission_root':str(self.admission_root),
            'certificate_sha256':self._certificate.sha256,
            'certificate_views':{'data':self._certificate.data,'file_pins':self._certificate.file_pins,
                'expiries':self._certificate.expiries,'native_wrappers':self._certificate.native_wrappers,
                'acquisition_root':str(self._certificate.root)}})

    def _check(self, *, rehash=False):
        self.check_run_age()
        require(self.host_deadline, self._constructor_deadline, 'nonrenewable host deadline')
        require(self._state_binding(), self._input_binding, 'native constructor inputs')
        require(transfer.owned_dir(self.workspace.parent), self._parent_inode, 'workspace parent inode')
        require(transfer.owned_dir(self.source_root), self._source_inode, 'source root inode')
        require(transfer.owned_dir(self.toolchain_root), self._runtime_inode, 'empty runtime inode')
        f.need(not any(self.toolchain_root.iterdir()), 'runtime placeholder no longer empty')
        self._certificate.check_age()
        if rehash:
            self._certificate.rehash()
            f.verify_sources(self.source_root, self.manifest)
            GRAPH.verify()
        self.check_run_age()

    def admit(self):
        """One use, no commands; returns inert complete metadata after real native restore."""
        if self._used or self._poisoned:
            self._poisoned = True
            self._report = None
            raise f.Rejected('admission already used or poisoned')
        self._used = True
        try:
            self._check(rehash=True)
            self._target = transfer.arm_empty_target(self, target_stage='build_087')
            f.no_symlink_path(self.workspace)
            f.need(not self.workspace.exists(), 'new workspace required')
            self.workspace.mkdir(mode=0o700)
            for name in ('objects','scratch','logs','module-quarantine'):
                (self.workspace/name).mkdir(mode=0o700)
            for name in ('home','tmp'):
                (self.workspace/'scratch'/name).mkdir(mode=0o700)
            self._workspace_inode = transfer.owned_dir(self.workspace)
            require(transfer.tree(self.workspace, empty_dirs=transfer.SCAFFOLD), {}, 'exact empty native scaffold')
            f.verify_sources(self.source_root, self.manifest)
            filesystem = os.statvfs(self.workspace)
            needed = f.storage_restore_budget([self._for_runner(w) for w in self._wrappers], self.contract,
                build=True, stages=self.stages, allocation_unit=filesystem.f_frsize)
            f.need(shutil.disk_usage(self.workspace).free >= needed, 'insufficient measured native restore/output space')
            # Conservative three-tree bound from exact full-plan object/log paths,
            # unique directories and per-stage journals/evidence. This includes
            # the original validator copy peak and complements native byte sizing.
            inode_paths = {name for stage in self.stages.values() for module in stage['modules']
                           for name in f.object_paths(module,self.contract['output_suffixes'])+f.log_paths(module)}
            inode_dirs = {str(parent) for name in inode_paths for parent in Path(name).parents if str(parent) != '.'}
            inode_need = 3*(len(inode_paths)+len(inode_dirs)+85*16+len(transfer.SCAFFOLD)+2)
            f.need(filesystem.f_favail >= inode_need, 'insufficient measured native restore inodes')
            self._check()
            self._restore_scope()  # exact frozen function object; no run()/restore_final()
            self._check(rehash=True)
            require(transfer.owned_dir(self.workspace), self._workspace_inode, 'admitted workspace inode')
            self.verify_checked_objects()
            expected = {m for sid in self.stages['build_087']['required_predecessors'] for m in self.stages[sid]['modules']}
            require(set(self.objects), expected, 'all 6218 native modules')
            require(sum(len(v) for v in self.objects.values()), 6218*6, 'all six native companions')
            require(self.predecessor_descriptors, self._scope.data['native_descriptors'], 'native descriptor order and identity')
            inventory = transfer.tree(self.workspace, empty_dirs=transfer.SCAFFOLD|{'quarantine'})
            report = {'schema':'c087-native-admission-report-v1','status':'native_admission_only',
                'executable_authority':False,'activation_allowed':False,'proof_pass_claimed':False,
                'runtime_installed':False,'kernel_executed':False,'target_stage':'build_087',
                'module_count':6218,'stage_count':85,'companion_count':6218*6,
                'session_nonce':self._certificate.data['session_nonce'],
                'host_deadline_monotonic':self.host_deadline,'workspace':str(self.workspace),
                'workspace_inode':list(self._workspace_inode),'source_root_inode':list(self._source_inode),
                'certificate_sha256':self._certificate.sha256,'scope_sha256':self._scope.sha256,
                'native_input_binding_sha256':self._input_binding,'frozen_graph_sha256':PINS_SHA256,
                'objects':self.objects,'native_descriptors':self.predecessor_descriptors,
                'restore_evidence_hashes':self.restore_evidence_hashes,'workspace_files':inventory,
                'raw_archive_bytes':self._scope.data['raw_archive_bytes']}
            raw = p.json_bytes(report)
            self._check(rehash=True)
            require(transfer.tree(self.workspace, empty_dirs=transfer.SCAFFOLD|{'quarantine'}), inventory,
                    'tree changed while serializing report')
            self._certificate.check_age()
            self.check_run_age()
            self._report = AdmissionReport(raw)
            return self._report
        except BaseException:
            self._poisoned = True
            self._historical_transfer_poisoned = True
            self._report = None
            raise

    def _refuse(self, *args, **kwargs):
        self._poisoned = True
        raise f.Rejected('historical admission never grants command, build, final, or executor authority')

    command = _refuse
    run = _refuse
    restore_final = _refuse
    read_predecessors = _refuse
    read_artifacts = _refuse
    promote_quarantine = _refuse
    _executor_refused = _refuse
