"""Inactive strict current identity seam over the unchanged reviewed status-wait transport.

Historical terminal transport and native validators are separate frozen graphs.
This module never projects or rewrites a native identity. Actual Transport()
construction still performs its original authenticated current-run bootstrap.
"""
from __future__ import annotations
import copy, hashlib, importlib.util, json, os, stat, sys, threading
from datetime import datetime, timezone
from pathlib import Path

DEPENDENCIES={
 'fresh_stage.py':'9085c9eea092c270fbd6952834839103c66519a7b4716fe09147001c7d96355d',
 'continuation_policy.py':'1759e1fc5587ec2b5462604f9f7a16cebaefdb85f153d563514b36b18d314be2',
 'ci_transport.py':'0e17698024da89562d654978436b707a140fef81c3463a8b0841af8de2355c95',
 'origin_transport.py':'36aaf72618c9547434de9d82cf95a633565c29b0557449b41d8dc8d10adf9ec8',
 'four_context_policy.py':'901f2db258c50a386a499fedd81328533327bd8d77cca700b764fb8afb7593e0'}
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
f=_loaded['fresh_stage'];cp=_loaded['continuation_policy'];ct=_loaded['ci_transport'];base=_loaded['origin_transport'];p=_loaded['four_context_policy']
if not (base.f is f and base.cp is cp and base.Transport is ct.Transport and cp.f is f and ct.f is f):
    raise RuntimeError('current dependency reference graph changed')
class Transport(ct.Transport):
    def __init__(self, *, token, opener):
        f.need(os.environ.get('GITHUB_ACTIONS')=='true' and os.environ.get('GITHUB_REPOSITORY')==ct.REPOSITORY,
               'not the reviewed GitHub repository/action context')
        self.run_id=os.environ.get('GITHUB_RUN_ID','');self.attempt=os.environ.get('GITHUB_RUN_ATTEMPT','')
        self.commit=os.environ.get('GITHUB_SHA','')
        f.need(self.run_id.isdigit() and self.attempt.isdigit() and f.COMMIT.fullmatch(self.commit), 'invalid workflow identity')
        self.token=token;f.need(bool(self.token),'ephemeral read-only workflow token missing')
        self.opener=opener
        self.run=self.get(f'/repos/{ct.REPOSITORY}/actions/runs/{self.run_id}')
        f.need(str(self.run['id'])==self.run_id and self.run['head_sha']==self.commit and
               str(self.run['run_attempt'])==self.attempt and self.run['event']=='push', 'trusted workflow run mismatch')
        self._jobs=None;self._artifacts=None

FIXED_WORKFLOW={'path':'.github/workflows/hierarchy-c-production-recovery.yml',
 'name':'Verify hierarchy C production recovery',
 'head_branch':'verify/hierarchy-c-production-recovery-20261018'}

class CurrentOriginTransport(base.OriginTransport):
    def __init__(self,current_transport,*,bundle_bytes,selection_bytes,selection_sha256,plan,
                 current_context,pipeline_commit,contract_sha256,consumer_roles,consumer_role,github_job,opener=None,now=None):
        _verify_dependencies()
        f.need(isinstance(current_transport,Transport),'authenticated current Transport required')
        f.need(type(current_transport.token) is str and bool(current_transport.token),'read-only workflow token missing')
        self.bundle=p.validate_context_bundle(bundle_bytes,p.BUNDLE_SHA256)
        self.selection=p.parse_selection(selection_bytes,selection_sha256,plan,self.bundle,require_payloads=True)
        f.need(sum(type(row) is p.OldOrigin for row in self.selection.rows)==37 and
               sum(type(row) is p.PriorSuccessorOrigin for row in self.selection.rows)==11 and
               sum(type(row) is p.LatestSuccessorOrigin for row in self.selection.rows)==42 and
               sum(type(row) is p.ProductionSuccessOrigin for row in self.selection.rows)==1 and
               sum(type(row) is p.CurrentOrigin for row in self.selection.rows)==2,
               'exact 37 original, 11 prior, 42 latest, 1 production and 2 fresh selection required')
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
        # Consumer roles are distinct from downloadable provider roles. Verdict
        # remains a mandatory consumer/final job, never an artifact provider.
        f.need(type(consumer_roles) is dict and set(consumer_roles)==expected_roles|{'verdict'},
               'current consumer role coverage changed')
        for role,binding in consumer_roles.items():
            base.exact_keys(binding,{'producer_job','job_name','verifier_step'},'consumer role')
            expected = ({k:workflow['roles'][role][k] for k in binding} if role!='verdict' else
                        {'producer_job':'verdict','job_name':'verdict',
                         'verifier_step':{'number':8,'name':'Run fail-closed verifier'}})
            f.need(binding==expected,'current consumer/provider workflow mapping changed')
            f.need(type(binding['verifier_step']['number']) is int and binding['verifier_step']['number']==8 and
                   binding['verifier_step']['name']=='Run fail-closed verifier','current verifier step changed')
        f.need(type(consumer_role) is str and consumer_role in consumer_roles and
               type(github_job) is str and github_job==consumer_roles[consumer_role]['producer_job'],
               'current invocation role/GITHUB_JOB mismatch')
        self.consumer_role=consumer_role
        self.consumer_binding=copy.deepcopy(consumer_roles[consumer_role])
        self.github_job=github_job
        self.current=current_transport
        f.need(opener is current_transport.opener,'same current acquisition quota opener required')
        self.opener=opener
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

    def _current_run_observation(self,budget,observation):
        f.need(type(observation) is int and 1<=observation<=base.MAX_CURRENT_STATUS_POLLS,
               'current run status poll count exhausted')
        context=self._context(base.CURRENT_ORIGIN);identity=context['identity'];workflow=context['workflow']
        run,poll=self._json(f'/repos/{base.REPOSITORY}/actions/runs/{identity["run_id"]}',
                            budget=budget,poll_headers=True)
        try:
            with base._metadata_wall_limit(self._metadata_remaining(budget),deadline=budget['deadline']):
                for key in ('repository','head_repository'):
                    repo=run.get(key)
                    f.need(type(repo) is dict and type(repo.get('id')) is int and repo['id']==base.REPOSITORY_ID and
                           repo.get('full_name')==base.REPOSITORY,'run repository/head-repository mismatch')
                f.need(type(run.get('id')) is int and str(run['id'])==identity['run_id'] and
                       type(run.get('run_attempt')) is int and str(run['run_attempt'])==identity['run_attempt'] and
                       run.get('head_sha')==identity['pipeline_commit'] and run.get('event')=='push' and
                       run.get('head_branch')==workflow['head_branch'] and
                       type(run.get('workflow_id')) is int and run['workflow_id']==workflow['workflow_id'] and
                       run.get('path')==workflow['path'] and run.get('name')==workflow['name'],
                       'run/workflow identity mismatch or rerun')
                f.need(run.get('created_at')==identity['run_started_at'],'trusted run start mismatch')
                f.need(base.timestamp(run['created_at'])<=base.timestamp(run.get('updated_at'))<=self.now(),
                       'inconsistent run timestamps')
                f.need('status' in run and 'conclusion' in run,'current run status/conclusion missing')
                accepted=((run['status']=='in_progress' and run['conclusion'] is None) or
                          (run['status']=='completed' and run['conclusion']=='success'))
                f.need(accepted or (type(run['status']) is str and run['status'] in base.WAITABLE_CURRENT_STATUSES and
                                   run['conclusion'] is None),'current run is not active/successful; terminal or invalid state')
                # This post-validation record preserves the actual API status.
                record={k:run[k] for k in ('id','run_attempt','workflow_id','head_sha','status','conclusion','created_at','updated_at')}
                record.update(event='current_origin_run_status_observation',observation=observation,identity_validation='passed')
                print(json.dumps(record,sort_keys=True,separators=(',',':')),flush=True)
                self._metadata_remaining(budget)
                return run,poll,accepted,record
        except (base._MetadataWallTimeout,base._MetadataHardTimeout):
            raise f.Rejected('current run status diagnostic/validation deadline exceeded') from None

    def _active_consumer(self,budget,job_id=None):
        context=self._context(base.CURRENT_ORIGIN);identity=context['identity'];workflow=context['workflow']
        binding=self.consumer_binding
        if job_id is None:
            data=self._json(f'/repos/{base.REPOSITORY}/actions/runs/{identity["run_id"]}/attempts/{identity["run_attempt"]}/jobs?per_page=100&page=1',budget=budget)
            try:
                with base._metadata_wall_limit(self._metadata_remaining(budget),deadline=budget['deadline']):
                    rows=data.get('jobs');count=data.get('total_count')
                    f.need(type(rows) is list and type(count) is int and count==len(rows) and 0<count<=52 and
                           all(type(row) is dict for row in rows),'invalid bounded current consumer jobs')
                    ids=[row.get('id') for row in rows]
                    f.need(all(type(n) is int and n>0 for n in ids) and len(set(ids))==len(ids),'duplicate/invalid current job IDs')
                    matches=[row for row in rows if row.get('name')==binding['job_name']]
                    f.need(len(matches)==1,'current consumer job missing or ambiguous')
                    job=matches[0]
                    self._metadata_remaining(budget)
            except (base._MetadataWallTimeout,base._MetadataHardTimeout):
                raise f.Rejected('current consumer list deadline exceeded') from None
        else:
            base.positive(job_id,'current consumer job ID')
            job=self._json(f'/repos/{base.REPOSITORY}/actions/jobs/{job_id}',budget=budget)
        try:
            with base._metadata_wall_limit(self._metadata_remaining(budget),deadline=budget['deadline']):
                f.need(type(job.get('id')) is int and job['id']>0 and (job_id is None or job['id']==job_id) and
                       type(job.get('run_id')) is int and str(job['run_id'])==identity['run_id'] and
                       type(job.get('run_attempt')) is int and str(job['run_attempt'])==identity['run_attempt'] and
                       job.get('head_sha')==identity['pipeline_commit'] and job.get('head_branch')==workflow['head_branch'] and
                       job.get('workflow_name')==workflow['name'] and job.get('name')==binding['job_name'],
                       'current consumer job identity mismatch')
                f.need(job.get('status')=='in_progress' and 'conclusion' in job and job['conclusion'] is None and
                       'completed_at' in job and job['completed_at'] is None,'current consumer job is not active')
                created=base.timestamp(job.get('created_at'));started=base.timestamp(job.get('started_at'))
                f.need(base.timestamp(identity['run_started_at'])<=created<=started<=self.now(),'current consumer job timestamps inconsistent')
                steps=job.get('steps')
                f.need(type(steps) is list and 0<len(steps)<=100 and all(type(step) is dict for step in steps),
                       'invalid bounded current consumer steps')
                numbers=[step.get('number') for step in steps];names=[step.get('name') for step in steps]
                f.need(all(type(n) is int and n>0 for n in numbers) and len(set(numbers))==len(numbers) and
                       all(type(n) is str and n for n in names) and len(set(names))==len(names),
                       'ambiguous current consumer steps')
                matches=[step for step in steps if step.get('number')==binding['verifier_step']['number'] or
                         step.get('name')==binding['verifier_step']['name']]
                f.need(len(matches)==1,'current consumer verifier step missing or ambiguous')
                step=matches[0]
                f.need(step['number']==binding['verifier_step']['number'] and step['name']==binding['verifier_step']['name'] and
                       step.get('status')=='in_progress' and 'conclusion' in step and step['conclusion'] is None and
                       'completed_at' in step and step['completed_at'] is None,'current consumer verifier step is not active')
                f.need(started<=base.timestamp(step.get('started_at'))<=self.now(),'current verifier timestamp inconsistent')
                result={k:job[k] for k in ('id','run_id','run_attempt','head_sha','head_branch','workflow_name','name',
                                         'status','conclusion','created_at','started_at','completed_at')}
                result['step']={k:step[k] for k in ('number','name','status','conclusion','started_at','completed_at')}
                self._metadata_remaining(budget)
                return result
        except (base._MetadataWallTimeout,base._MetadataHardTimeout):
            raise f.Rejected('current consumer validation deadline exceeded') from None

    def _current_status_wait(self,budget,poll,observation):
        delay=base.CURRENT_STATUS_BACKOFF_SECONDS[observation-1]
        if poll is not None:
            f.need(type(poll) is str and base.re.fullmatch(r'[0-9]{1,4}',poll),'invalid current run X-Poll-Interval')
            delay=max(delay,int(poll))
        remaining=self._metadata_remaining(budget)
        f.need(delay<remaining,'current run status wait exceeds aggregate/origin deadline')
        try:
            with base._metadata_wall_limit(remaining,deadline=budget['deadline']):base.time.sleep(delay)
        except (base._MetadataWallTimeout,base._MetadataHardTimeout):
            raise f.Rejected('current run status wait deadline exceeded') from None
        self._metadata_remaining(budget)

    def _run(self,origin):
        if origin!=base.CURRENT_ORIGIN:
            return super()._run(origin)
        started=base.time.monotonic()
        budget={'started':started,'deadline':started+base.MAX_CURRENT_STATUS_SECONDS}
        observation=0
        while observation<base.MAX_CURRENT_STATUS_POLLS:
            observation+=1
            run,poll,accepted,first_run=self._current_run_observation(budget,observation)
            if accepted:
                self._metadata_remaining(budget)
                return run
            if run['status']=='queued':
                f.need(observation<base.MAX_CURRENT_STATUS_POLLS,'current run status poll count exhausted')
                first=self._active_consumer(budget)
                self._current_status_wait(budget,poll,observation)
                second=self._active_consumer(budget,first['id'])
                f.need(first==second,'current active consumer changed between authenticated reads')
                observation+=1
                run,poll,accepted,last_run=self._current_run_observation(budget,observation)
                f.need(base.timestamp(first_run['updated_at'])<=base.timestamp(last_run['updated_at']),
                       'current run update timestamp moved backward')
                if accepted:
                    self._metadata_remaining(budget)
                    return run
                if run['status']=='queued':
                    # Separate live eligibility witness; native receipt metadata
                    # remains byte-identical and still requires successful producers.
                    witness={'event':'current_queued_active_consumer_witness','schema':'current-consumer-v1',
                        'acceptance':'queued_run_with_exact_active_consumer','identity':self.contexts[origin]['identity'],
                        'consumer_role':self.consumer_role,'github_job':self.github_job,'binding':self.consumer_binding,
                        'run_observations':[first_run,last_run],'consumer_observations':[first,second]}
                    try:
                        with base._metadata_wall_limit(self._metadata_remaining(budget),deadline=budget['deadline']):
                            encoded=json.dumps(witness,sort_keys=True,separators=(',',':'))
                            f.need(len(encoded.encode('utf-8'))<=16384,'current consumer witness exceeds bound')
                            print(encoded,flush=True)
                            self._metadata_remaining(budget)
                            return run
                    except (base._MetadataWallTimeout,base._MetadataHardTimeout):
                        raise f.Rejected('current consumer witness deadline exceeded') from None
            f.need(observation<base.MAX_CURRENT_STATUS_POLLS,'current run status poll count exhausted')
            self._current_status_wait(budget,poll,observation)
        raise f.Rejected('current run status poll bound exceeded')

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
    fixed={'path':'.github/workflows/hierarchy-c-production-recovery.yml',
           'name':'Verify hierarchy C production recovery',
           'head_branch':'verify/hierarchy-c-production-recovery-20261018'}
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
