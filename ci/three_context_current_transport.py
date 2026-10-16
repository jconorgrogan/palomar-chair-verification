"""Inactive strict current identity seam over the unchanged reviewed status-wait transport.

Historical terminal transport and native validators are separate frozen graphs.
This module never projects or rewrites a native identity. Actual Transport()
construction still performs its original authenticated current-run bootstrap.
"""
from __future__ import annotations
import copy, hashlib, importlib.util, json, stat, sys, threading
from datetime import datetime, timezone
from pathlib import Path

DEPENDENCIES={
 'fresh_stage.py':'9085c9eea092c270fbd6952834839103c66519a7b4716fe09147001c7d96355d',
 'continuation_policy.py':'1759e1fc5587ec2b5462604f9f7a16cebaefdb85f153d563514b36b18d314be2',
 'ci_transport.py':'0e17698024da89562d654978436b707a140fef81c3463a8b0841af8de2355c95',
 'origin_transport.py':'36aaf72618c9547434de9d82cf95a633565c29b0557449b41d8dc8d10adf9ec8',
 'three_context_policy.py':'edc4852bcfe3cd8ca980733229859c98ca20fb7120edddaa61f0c55ed19f53d4'}
HERE=Path(__file__).absolute().parent

def _verify_dependencies():
    for path in [HERE,*HERE.parents]:
        if path.is_symlink():raise RuntimeError('current transport symlink path')
    for name,digest in DEPENDENCIES.items():
        path=HERE/name;s=path.lstat()
        if not stat.S_ISREG(s.st_mode) or s.st_nlink!=1 or hashlib.sha256(path.read_bytes()).hexdigest()!=digest:
            raise RuntimeError('current transport dependency pin mismatch')

_verify_dependencies()
if threading.current_thread() is not threading.main_thread() or threading.active_count()!=1:
    raise RuntimeError('current transport requires one main thread')
_names=tuple(name[:-3] for name in DEPENDENCIES)
_saved={name:sys.modules.get(name) for name in _names};_bytecode=sys.dont_write_bytecode
_loaded={};sys.dont_write_bytecode=True
try:
    for name in _names:sys.modules.pop(name,None)
    for name in _names:
        path=HERE/(name+'.py');spec=importlib.util.spec_from_file_location(name,path)
        module=importlib.util.module_from_spec(spec);sys.modules[name]=module;spec.loader.exec_module(module)
        if Path(module.__file__)!=path:raise RuntimeError('current dependency load path changed')
        _loaded[name]=module
finally:
    for name,previous in _saved.items():
        if previous is None:sys.modules.pop(name,None)
        else:sys.modules[name]=previous
    sys.dont_write_bytecode=_bytecode
f=_loaded['fresh_stage'];cp=_loaded['continuation_policy'];ct=_loaded['ci_transport'];base=_loaded['origin_transport'];p=_loaded['three_context_policy']
if not (base.f is f and base.cp is cp and base.Transport is ct.Transport and cp.f is f and ct.f is f):
    raise RuntimeError('current dependency reference graph changed')
Transport=ct.Transport
FIXED_WORKFLOW={'path':'.github/workflows/hierarchy-c-three-context.yml',
 'name':'Verify hierarchy C with authenticated historical stages',
 'head_branch':'verify/hierarchy-c-three-context-20261016'}

class CurrentOriginTransport(base.OriginTransport):
    def __init__(self,current_transport,*,bundle_bytes,selection_bytes,selection_sha256,plan,
                 current_context,pipeline_commit,contract_sha256,opener=None,now=None):
        _verify_dependencies()
        f.need(isinstance(current_transport,Transport),'authenticated current Transport required')
        f.need(type(current_transport.token) is str and bool(current_transport.token),'read-only workflow token missing')
        self.bundle=p.validate_context_bundle(bundle_bytes,p.BUNDLE_SHA256)
        self.selection=p.parse_selection(selection_bytes,selection_sha256,plan,self.bundle,require_payloads=True)
        f.need(sum(type(row) is p.OldOrigin for row in self.selection.rows)==37 and
               sum(type(row) is p.PriorSuccessorOrigin for row in self.selection.rows)==11,
               'exact 37 original and 11 prior selection required')
        p.keys(current_context,{'identity','workflow'},'future current context')
        cur=current_context['identity'];workflow=current_context['workflow']
        p.validate_current_identity(cur,self.selection,self.bundle,pipeline_commit=pipeline_commit,contract_sha256=contract_sha256)
        base.validate_workflow(workflow)
        f.need(all(workflow[k]==v for k,v in FIXED_WORKFLOW.items()),'future current workflow names changed')
        expected_roles={r.stage_id for r in self.selection.rows if type(r) is p.CurrentOrigin}|{'prepare'}|base.FINAL_ROLES
        f.need(set(workflow['roles'])==expected_roles,'future current workflow role coverage changed')
        f.need(cur['run_id']==current_transport.run_id and cur['run_attempt']==current_transport.attempt and
               cur['pipeline_commit']==current_transport.commit,'authenticated current event/identity mismatch')
        run=current_transport.run
        for key in ('repository','head_repository'):
            repo=run.get(key)
            f.need(type(repo) is dict and type(repo.get('id')) is int and repo['id']==p.REPOSITORY_ID and
                   repo.get('full_name')==p.REPOSITORY,'authenticated current repository mismatch')
        f.need(type(run.get('id')) is int and str(run['id'])==cur['run_id'] and
               type(run.get('run_attempt')) is int and run['run_attempt']==1 and
               run.get('head_sha')==cur['pipeline_commit'] and run.get('event')=='push' and
               run.get('created_at')==cur['run_started_at'] and
               type(run.get('workflow_id')) is int and run['workflow_id']==workflow['workflow_id'] and
               all(run.get(k)==v for k,v in FIXED_WORKFLOW.items()),'authenticated current workflow identity mismatch')
        self.current=current_transport
        self.opener=opener if opener is not None else base.urllib.request.build_opener(base.NoRedirect())
        clock=now or (lambda:datetime.now(timezone.utc))
        self._last_clock_wall=None
        def observed_now():
            value=clock()
            f.need(isinstance(value,datetime) and value.tzinfo is not None and value.utcoffset() is not None,
                   'trusted aware clock required')
            f.need(self._last_clock_wall is None or value>=self._last_clock_wall,'current clock moved backward')
            self._last_clock_wall=value
            return value
        # Every inherited self.now() observation is guarded, not merely the
        # final sample in a multi-read age or metadata operation.
        self.now=observed_now
        self.contexts={base.OLD_ORIGIN:copy.deepcopy(self.bundle.old_context),base.CURRENT_ORIGIN:copy.deepcopy(current_context)}
        # The fixed bundle independently authenticates the unchanged original context.
        cp.validate_old_identity(self.contexts[base.OLD_ORIGIN]['identity'])
        for context in self.contexts.values():base.validate_workflow(context['workflow'])
        self._validate_pin(self.contexts[base.OLD_ORIGIN]['prepare'],prepare=True,identity=self.contexts[base.OLD_ORIGIN]['identity'])
        self._prepared={};self._source_verified=set();self._last_wall=None
        self._check_age()

    def _check_age(self):
        # Preserve base age checks, adding all selected historical expiries and
        # the explicit third-context start. No budget is renewed.
        super()._check_age()
        now=self.now()
        p.deadline_check(self.bundle,self.selection,now,current_identity=self.contexts[base.CURRENT_ORIGIN]['identity'],previous_now=self._last_wall)
        self._last_wall=now

    def download_stage(self,origin,stage_id,destination,max_bytes,pin=None):
        # This graph handles fresh current only. Historical transfer has its own
        # independently pinned terminal transport; no label alias is accepted.
        f.need(origin==base.CURRENT_ORIGIN and type(self.selection.row(stage_id)) is p.CurrentOrigin,
               'current transport cannot acquire a historical selected stage')
        return super().download_stage(origin,stage_id,destination,max_bytes,pin=pin)


def current_workflow_from_run(transport, template, pipeline):
    """Resolve only the current workflow ID from the authenticated current run.

    Contract fixes path/name/branch/roles. Numeric ID and source digest are
    deliberately null until authenticated run metadata and the pinned checkout
    provide them. Original-origin mapping is never passed through this helper.
    """
    f.need(isinstance(transport,Transport),'authenticated current Transport required')
    cp.keys(template,{'workflow_id','path','name','head_branch','source_sha256','roles'},'current workflow template')
    f.need(template['workflow_id'] is None and template['source_sha256'] is None,
           'current workflow ID/source must come from authenticated runtime context')
    fixed={'path':'.github/workflows/hierarchy-c-three-context.yml',
           'name':'Verify hierarchy C with authenticated historical stages',
           'head_branch':'verify/hierarchy-c-three-context-20261016'}
    f.need(all(template[k]==v for k,v in fixed.items()),'current workflow path/name/branch changed')
    run=transport.run
    f.need(type(run) is dict and type(run.get('id')) is int and run['id']>0 and str(run['id'])==transport.run_id and
           type(run.get('run_attempt')) is int and run['run_attempt']==1 and str(run['run_attempt'])==transport.attempt and
           run.get('head_sha')==transport.commit and run.get('event')=='push',
           'authenticated current run identity changed')
    for key in ('repository','head_repository'):
        repo=run.get(key)
        f.need(type(repo) is dict and type(repo.get('id')) is int and repo['id']==cp.REPOSITORY_ID and
               repo.get('full_name')==p.REPOSITORY,'current repository/head repository changed')
    f.need(all(run.get(k)==v for k,v in fixed.items()),'current run workflow fields changed')
    cp.integer(run.get('workflow_id'),'authenticated current workflow ID')
    mapping=dict(template);mapping['workflow_id']=run['workflow_id']
    path=Path(pipeline)/f.safe_rel(mapping['path']);f.no_symlink_path(path)
    f.need(path.is_file(),'pinned current workflow source missing')
    mapping['source_sha256']=f.file_sha(path)
    base.validate_workflow(mapping)
    return mapping
