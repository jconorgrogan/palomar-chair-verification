"""Read-only, fixed-export transport for exactly one Lake kernel-and-axiom job.

Uses the original metadata/ZIP primitives and one original 1,000-attempt quota
opener. It cannot acquire stages, other final roles, or aggregate a verdict.
"""
from __future__ import annotations
import copy, hashlib, math, re, time, urllib.request
from datetime import datetime, timezone
from pathlib import Path
from types import SimpleNamespace
import fresh_stage as f
import origin_transport as base

CURRENT=base.CURRENT_ORIGIN
WORKFLOW={'head_branch':'verify/hierarchy-c-export-check-recovery-20261018',
 'path':'.github/workflows/hierarchy-c-export-check-recovery.yml',
 'name':'Verify hierarchy C export check recovery'}
PINS_SHA256='57251fabbd5a91217bbed8aaf1e20362450a159ade21311da73895132eb06991'
ROLES=('lake_export_axioms',)
PROOF_SHA256='10bfb9ed515dda11089ec3a3f8e50d296d60e8c6bd0b83f1784d6b5567e67d11'
DEADLINE='2026-10-22T06:15:54Z'
JOB_KEYS=('id','name','run_id','run_attempt','head_sha','status','conclusion','started_at','completed_at','steps')

class ExportRetryTransport(base.OriginTransport):
 def __init__(self,token,execution_identity,execution_workflow,pins,*,role,acquisition_module,deadline_monotonic,opener=None,now=None):
  f.need(type(role)is str and role in ROLES,'EXACT_EXECUTION_ROLE');self.role=role
  f.need(type(token)is str and token and not any(ord(x)<33 for x in token),'TOKEN_SHAPE')
  f.need(type(pins)is dict and f.sha(f.json_bytes(pins))==PINS_SHA256,'EXACT_ORIGIN_PINS')
  f.need(type(execution_identity)is dict and set(execution_identity)=={'run_id','run_attempt','pipeline_commit'},'EXECUTION_SEED_KEYS')
  f.need(type(execution_identity['run_id'])is str and re.fullmatch('[1-9][0-9]*',execution_identity['run_id']) and execution_identity['run_attempt']=='1' and type(execution_identity['pipeline_commit'])is str and f.COMMIT.fullmatch(execution_identity['pipeline_commit']),'EXECUTION_SEED')
  f.need(execution_identity['run_id']!=pins['proof_identity']['run_id'] and execution_identity['pipeline_commit']!=pins['proof_identity']['pipeline_commit'],'DISTINCT_EXECUTION')
  f.need(type(execution_workflow)is dict and set(execution_workflow)==set(WORKFLOW)|{'source_sha256'} and all(execution_workflow[k]==v for k,v in WORKFLOW.items()),'EXECUTION_WORKFLOW')
  base.digest(execution_workflow['source_sha256'],'execution workflow source')
  f.need(type(deadline_monotonic)in(int,float) and math.isfinite(deadline_monotonic) and 0<deadline_monotonic-time.monotonic()<=19800,'EXECUTION_DEADLINE')
  self.current=SimpleNamespace(token=token);self.now=now or(lambda:datetime.now(timezone.utc))
  self.pins=copy.deepcopy(pins);self.seed=copy.deepcopy(execution_identity);self.execution_workflow=copy.deepcopy(execution_workflow)
  self.contexts={CURRENT:{'identity':copy.deepcopy(pins['proof_identity']),'workflow':copy.deepcopy(pins['workflow'])}}
  base.validate_workflow(pins['workflow']);f.need(f.sha(f.json_bytes(pins['proof_identity']))==PROOF_SHA256 and pins['original_deadline']==DEADLINE,'ORIGINAL_PROOF')
  self.deadline_monotonic=deadline_monotonic;self.age_deadline_monotonic=math.inf;self._prepared={};self._source_verified=set();self.execution=None;self.downloaded=None;self.failure=None
  self._check_age();self.opener=acquisition_module.QuotaPacedOpener(self,opener if opener is not None else urllib.request.build_opener(base.NoRedirect()))
 def _check_age(self):
  now=self.now();f.need(isinstance(now,datetime) and now.tzinfo is not None,'TRUSTED_CLOCK')
  prior=base.timestamp(self.pins['proof_identity']['run_started_at']);end=base.timestamp(DEADLINE)
  f.need(prior<=now<end,'ORIGINAL_ACCEPTANCE_DEADLINE')
  self.age_deadline_monotonic=min(self.age_deadline_monotonic,time.monotonic()+(end-now).total_seconds())
  f.need(time.monotonic()<min(self.deadline_monotonic,self.age_deadline_monotonic),'JOB_DEADLINE')
 def _run(self,origin):
  f.need(origin==CURRENT,'ONLY_ORIGINAL_PROOF_DOMAIN');ctx=self.contexts[CURRENT];ident,wf=ctx['identity'],ctx['workflow'];r=self._json(f'/repos/{base.REPOSITORY}/actions/runs/{ident["run_id"]}')
  self._validate_run(r,ident,wf,prior=True);return r
 def _validate_run(self,r,ident,wf,*,prior):
  for key in ('repository','head_repository'):
   q=r.get(key);f.need(type(q)is dict and type(q.get('id'))is int and q['id']==base.REPOSITORY_ID and q.get('full_name')==base.REPOSITORY,'RUN_REPOSITORY')
  f.need(type(r.get('id'))is int and str(r['id'])==ident['run_id'] and type(r.get('run_attempt'))is int and str(r['run_attempt'])==ident['run_attempt'] and r.get('head_sha')==ident['pipeline_commit'] and r.get('event')=='push' and all(r.get(k)==wf[k]for k in ('head_branch','path','name')),'RUN_IDENTITY')
  f.need(type(r.get('workflow_id'))is int and r['workflow_id']>0 and (wf.get('workflow_id')is None or r['workflow_id']==wf['workflow_id']),'WORKFLOW_ID')
  created,updated=base.timestamp(r.get('created_at')),base.timestamp(r.get('updated_at'));f.need(created<=updated<=self.now(),'RUN_TIMESTAMPS')
  if 'run_started_at'in ident:f.need(r['created_at']==ident['run_started_at'],'RUN_START')
  accepted=(r.get('status')=='in_progress' and r.get('conclusion')is None)or(prior and r.get('status')=='completed' and r.get('conclusion')=='failure')
  f.need(accepted,'RUN_STATE')
 def authenticate_execution(self):
  previous=copy.deepcopy(self.execution)
  r=self._json(f'/repos/{base.REPOSITORY}/actions/runs/{self.seed["run_id"]}');self._validate_run(r,self.seed,self.execution_workflow,prior=False)
  ident={**self.seed,'run_started_at':r['created_at']};wf={**self.execution_workflow,'workflow_id':r['workflow_id']}
  f.need(self.pins['proof_identity']['run_started_at']<ident['run_started_at']<DEADLINE,'EXECUTION_AGE')
  self.contexts['RetryExecution']={'identity':ident,'workflow':wf};self._verify_workflow_source('RetryExecution')
  jobs=self._collection(f'/repos/{base.REPOSITORY}/actions/runs/{ident["run_id"]}/attempts/1/jobs','jobs')
  f.need(len(jobs)==len(ROLES) and all(type(j)is dict for j in jobs),'EXACT_EXECUTION_JOBSET')
  f.need(sorted(j.get('name','')for j in jobs)==sorted(ROLES),'EXACT_EXECUTION_ROLE_NAMES')
  ids=[base.positive(j.get('id'),'execution job')for j in jobs];f.need(len(ids)==len(set(ids)),'EXECUTION_JOB_IDS')
  f.need(all(type(j.get('run_id'))is int and str(j['run_id'])==ident['run_id'] and type(j.get('run_attempt'))is int and j['run_attempt']==1 and j.get('head_sha')==ident['pipeline_commit'] for j in jobs),'EXECUTION_JOB_RUNS')
  j=next(j for j in jobs if j['name']==self.role);f.need(j.get('status')=='in_progress' and j.get('conclusion')is None,'EXECUTION_JOB')
  ident.update(producer_job_id=j['id'],producer_job_name=j['name'])
  steps=j.get('steps');f.need(type(steps)is list and all(type(x)is dict for x in steps),'EXECUTION_STEPS')
  nums=[base.positive(x.get('number'),'step')for x in steps];f.need(len(nums)==len(set(nums)),'EXECUTION_STEP_IDS')
  s=[x for x in steps if x.get('number')==8 or x.get('name')=='Run fail-closed verifier'];f.need(len(s)==1 and s[0].get('number')==8 and s[0].get('name')=='Run fail-closed verifier' and s[0].get('status')=='in_progress' and s[0].get('conclusion')is None,'EXECUTION_VERIFIER')
  f.need(base.timestamp(r['created_at'])<=base.timestamp(j['started_at'])<=base.timestamp(s[0]['started_at'])<=self.now(),'EXECUTION_JOB_TIMES')
  candidate={'identity':ident,'workflow':wf};f.need(previous is None or previous==candidate,'EXECUTION_IDENTITY_CHANGED');self.execution=candidate;return copy.deepcopy(self.execution)
 def _producer(self,origin,role,run,pin):
  f.need(origin==CURRENT and role in ('prepare','export_target') and pin==self.pins[role],'FIXED_PRIOR_ROLE')
  job,binding=super()._producer(origin,role,run,pin);f.need({k:job[k]for k in JOB_KEYS}==pin['producer'],'IMMUTABLE_PRODUCER');return job,binding
 def _artifact(self,origin,role,run,job,pin,max_bytes):
  a=super()._artifact(origin,role,run,job,pin,max_bytes);f.need({k:a[k]for k in pin['artifact']}==pin['artifact'],'IMMUTABLE_ARTIFACT');return a
 def _download(self,origin,role,destination,members,max_bytes,pin):
  if role=='export_target' and pin is None:pin=self.pins['export_target']
  f.need(self.execution is not None and origin==CURRENT and role in ('prepare','export_target') and pin==self.pins[role],'AUTHENTICATED_FIXED_DOWNLOAD')
  f.need(type(max_bytes)is int and 0<max_bytes<=(32*1024**2 if role=='prepare'else base.MAX_FINAL_BYTES+1024**2),'FIXED_TRANSFER_CAP')
  run=self._run(CURRENT);self._verify_workflow_source(CURRENT);job,binding=self._producer(CURRENT,role,run,pin);a=self._artifact(CURRENT,role,run,job,pin,max_bytes)
  out=self._extract(a,destination,members,max_bytes);self._run(CURRENT)
  # Selected completed producer/artifact must also remain exact after transfer.
  j,b=self._producer(CURRENT,role,run,pin);a2=self._artifact(CURRENT,role,run,j,pin,max_bytes);f.need(a2==a and j==job,'TRANSFER_REAUTHENTICATION')
  return out,self._metadata(CURRENT,run,job,a,binding)
 def authenticate_prior_prepare(self,destination):
  f.need(not self._prepared,'PRIOR_PREPARE_ONCE');out,meta=self._download(CURRENT,'prepare',destination,['identity.json','inventory.json'],32*1024**2,self.pins['prepare'])
  raw=(out/'identity.json').read_bytes();f.need(len(raw)==1574 and f.sha(raw)==PROOF_SHA256 and f.parse_json(raw)==self.pins['proof_identity'],'ORIGINAL_PREPARE_BYTES')
  f.need(f.file_sha(out/'inventory.json')==self.pins['proof_identity']['toolchain_inventory_sha256'],'ORIGINAL_INVENTORY')
  self._prepared[CURRENT]={'authenticated_metadata':meta};self.workroot=out.parent
  return {'identity_path':str((out/'identity.json').absolute()),'inventory_path':str((out/'inventory.json').absolute())}
 def download_prior_final(self,role,destination,maximum):
  f.need(role=='export_target' and CURRENT in self._prepared and self.downloaded is None,'ONLY_ONE_FIXED_EXPORT')
  # Original parser and hydrated CurrentOrigin descriptor stay in proof domain.
  out=super().download_final(role,destination,maximum);self.downloaded=copy.deepcopy(out);return out
 def download_final(self,*a,**k):raise f.Rejected('RETRY_CURRENT_FINAL_DOWNLOAD_FORBIDDEN')
 def download_stage(self,*a,**k):raise f.Rejected('STAGE_DOWNLOAD_FORBIDDEN')
 def authenticate_prepare(self,*a,**k):raise f.Rejected('USE_FIXED_PRIOR_PREPARE')
 def reauthenticate_prior_wrapper(self,wrapper):
  f.need(self.downloaded is not None and wrapper==self.downloaded,'EXACT_DOWNLOADED_EXPORT')
  run=self._run(CURRENT);pin=self.pins['export_target'];j,b=self._producer(CURRENT,'export_target',run,pin);a=self._artifact(CURRENT,'export_target',run,j,pin,base.MAX_FINAL_BYTES+1024**2)
  meta=self._metadata(CURRENT,run,j,a,b);f.need(meta==wrapper['authenticated_metadata'],'EXPORT_REAUTHENTICATION');self._check_age();return meta
 def authenticate_failure(self):
  f.need(CURRENT in self._prepared,'FAILURE_AUTHENTICATION_ORDER');pin=self.pins['lean_export_failure'];run=self._run(CURRENT)
  jobs=self._collection(f'/repos/{base.REPOSITORY}/actions/runs/{run["id"]}/attempts/1/jobs','jobs');selected=[j for j in jobs if j.get('id')==pin['producer_job_id'] or j.get('name')=='lean_export']
  f.need(len(selected)==1 and {k:selected[0].get(k)for k in JOB_KEYS}==pin['producer'],'EXACT_FAILED_PRODUCER')
  a=self._json(f'/repos/{base.REPOSITORY}/actions/artifacts/{pin["artifact_id"]}');f.need({k:a.get(k)for k in pin['artifact']}==pin['artifact'] and self.now()<base.timestamp(a['expires_at']),'EXACT_FAILURE_ARTIFACT')
  if self.failure is not None:self._check_age();return copy.deepcopy(self.failure)
  out=self._extract(a,self.workroot/'original-lean-export-failure',['FAILURE.json'],1024**2);raw=(out/'FAILURE.json').read_bytes();f.need(len(raw)<=16384 and f.sha(raw)==self.pins['failure_sha256'],'EXACT_FAILURE_BYTES')
  self._run(CURRENT);a2=self._json(f'/repos/{base.REPOSITORY}/actions/artifacts/{pin["artifact_id"]}');f.need(a2==a,'FAILURE_REAUTHENTICATION')
  self.failure={'failure_sha256':f.sha(raw),'artifact_id':a['id'],'producer_job_id':pin['producer_job_id'],'original_run_id':run['id'],'original_run_attempt':1,'original_pipeline_commit':run['head_sha'],'artifact_zip_sha256':pin['artifact_zip_sha256']};return copy.deepcopy(self.failure)
