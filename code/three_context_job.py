#!/usr/bin/env python3
"""Fixed historical acquisition then no-network native admission, one deadline."""
from __future__ import annotations
import argparse, hashlib, importlib.util, json, math, os, resource, shutil, signal, sys, threading, time
from datetime import datetime, timezone
from pathlib import Path
ENTRY_MONOTONIC=time.monotonic()
HERE=Path(__file__).resolve().parent
BOOTSTRAP_PINS={'three_context_local.py': '0ea2d6be51208e03248f5dd062b57c85bbc6b5768d156b27032891c15d10a06a', 'three_context_policy.py': 'edc4852bcfe3cd8ca980733229859c98ca20fb7120edddaa61f0c55ed19f53d4'}
for name in ('three_context_local','three_context_policy'):
    path=HERE/(name+'.py')
    if path.is_symlink() or hashlib.sha256(path.read_bytes()).hexdigest()!=BOOTSTRAP_PINS[name+'.py']:raise RuntimeError('bootstrap helper pin mismatch')
    spec=importlib.util.spec_from_file_location(name,HERE/(name+'.py'));m=importlib.util.module_from_spec(spec);sys.modules[name]=m;spec.loader.exec_module(m)
import three_context_local as l
import three_context_policy as p

class Expired(RuntimeError): pass

class JobBudget:
    """TERM records expiry during frozen process cleanup; host work stops immediately."""
    def __init__(self,entry=ENTRY_MONOTONIC,wall_clock=None):
        self.deadline=entry+19800;self.expired=False;self.in_child=False;self.previous=None
        self.wall_clock=wall_clock or (lambda:datetime.now(timezone.utc))
        self.last_wall=self.wall_clock();l.need(isinstance(self.last_wall,datetime) and self.last_wall.tzinfo is not None,'aware controller clock required')
        self.wall_deadline=p.timestamp('2026-10-22T06:15:54Z').timestamp()
    def handler(self,signum,frame):
        self.expired=True
        if not self.in_child:raise Expired('outer job deadline reached')
    def __enter__(self):
        l.need(threading.current_thread() is threading.main_thread(),'main-thread controller required')
        self.previous=signal.getsignal(signal.SIGTERM)
        l.need(self.previous in (signal.SIG_DFL,signal.SIG_IGN),'unexpected existing TERM handler')
        signal.signal(signal.SIGTERM,self.handler);return self
    def __exit__(self,*args):signal.signal(signal.SIGTERM,self.previous)
    def tighten(self,deadline):self.deadline=min(self.deadline,deadline);self.check()
    def tighten_wall(self,deadline):
        l.need(type(deadline) in (int,float) and math.isfinite(deadline),'invalid fixed wall deadline')
        self.wall_deadline=min(self.wall_deadline,deadline);self.check()
    def check(self):
        now=self.wall_clock();l.need(isinstance(now,datetime) and now.tzinfo is not None,'aware controller clock required')
        if now<self.last_wall or now.timestamp()>=self.wall_deadline:raise Expired('backward controller clock or historical expiry')
        self.last_wall=now
        self.deadline=min(self.deadline,time.monotonic()+self.wall_deadline-now.timestamp())
        if self.expired or time.monotonic()>=self.deadline:raise Expired('shared job deadline reached')
    def remaining(self):self.check();left=math.floor(self.deadline-time.monotonic());l.need(left>0,'shared deadline exhausted');return left
    def process(self,call):
        self.check();self.in_child=True
        try:return call()
        finally:self.in_child=False;self.check()

ENV_KEYS=('GITHUB_ACTIONS','GITHUB_REPOSITORY','GITHUB_RUN_ID','GITHUB_RUN_ATTEMPT','GITHUB_SHA','GITHUB_REF','GITHUB_JOB','GITHUB_WORKFLOW_REF')

def child_environment(root,*,acquisition):
    env={'PATH':'/usr/bin:/bin','HOME':str(root),'TMPDIR':str(root),'LANG':'C.UTF-8','LC_ALL':'C.UTF-8','PYTHONDONTWRITEBYTECODE':'1'}
    if acquisition:
        env.update({k:os.environ[k] for k in ENV_KEYS if k in os.environ})
        token=os.environ.get('GH_TOKEN','');l.need(bool(token),'read-only Actions token missing');env['GH_TOKEN']=token
    return env


def sandbox_command(python,semantic_argv,write_root,read_roots):
    # All authenticated inputs, including the complete original tars, stay read-only.
    return ['/usr/bin/bwrap','--ro-bind','/','/',
        '--tmpfs','/home','--tmpfs','/root','--tmpfs','/run/user','--tmpfs','/tmp',
        '--dir','/tmp/home',*[x for path in read_roots for x in ('--ro-bind',str(path),str(path))],
        '--bind',str(write_root),str(write_root),'--dev','/dev','--proc','/proc','--clearenv','--unshare-all','--die-with-parent','--new-session',
        '--setenv','PATH','/usr/bin:/bin','--setenv','HOME',str(write_root),'--setenv','TMPDIR',str(write_root),
        '--setenv','LANG','C.UTF-8','--setenv','LC_ALL','C.UTF-8','--',python,'-I','-S','-B',*semantic_argv]


def successful(result,*,sessions):
    l.need(result.get('exit_code')==0 and all(result.get(k) is False for k in ('timed_out','log_overflow','memory_exceeded','surviving_children')) and result.get('process_group_empty') is True and result.get('descendants_empty') is True and result.get('new_sessions_explicitly_allowed') is sessions and
        (sessions or result.get('escaped_descendants') is False),'bounded child failed or cleanup unproven')


def run_job(args,budget):
    budget.check()
    specpath=l.canonical(str(args.spec));raw=l.read_pinned(specpath,args.spec_sha256);spec=l.parse(raw)
    l.need(set(spec)=={'implementation_sha256', 'source_files', 'max_log_bytes', 'prior_files_sha256', 'review_status', 'max_evidence_bytes', 'acquisition_files', 'max_seconds', 'outer_job_minutes', 'admission_spec_sha256', 'bundle_sha256', 'schema', 'memory_bytes'},'unknown/missing job specification fields')
    l.need(spec.get('schema')=='fixed-historical-admission-job-v1' and spec.get('review_status')=='reviewed_for_admission_only','job specification inactive')
    l.need(spec['max_seconds']==19800 and spec['outer_job_minutes']==350 and spec['memory_bytes']==8*1024**3 and spec['max_log_bytes']==16*1024**2 and spec['max_evidence_bytes']==64*1024**2,'job resources changed')
    l.need(set(spec['implementation_sha256'])=={'three_context_policy.py', 'three_context_local.py', 'three_context_job.py', 'three_context_evidence.py', 'three_context_admit.py'},'exact admission implementation set required')
    for name,pin in spec['implementation_sha256'].items():l.need(l.file_sha(HERE/name)==pin,'job code pin changed')
    l.need(os.environ.get('GITHUB_ACTIONS')=='true' and os.environ.get('GITHUB_REPOSITORY')==p.REPOSITORY and os.environ.get('GITHUB_RUN_ATTEMPT')=='1','fresh official Actions attempt required')
    allowed=os.sched_getaffinity(0);l.need(bool(allowed),'no available CPU');os.sched_setaffinity(0,{min(allowed)})
    for limit in (resource.RLIMIT_AS,resource.RLIMIT_RSS):resource.setrlimit(limit,(spec['memory_bytes'],)*2)
    root=l.canonical(str(args.workspace));l.need(not root.exists(),'job workspace must be new');root.mkdir()
    logs=root/'logs';logs.mkdir();write_root=root/'semantic-write';write_root.mkdir()
    prior=l.canonical(str(args.prior_root));acquisition=l.canonical(str(args.acquisition_root));source_package=l.canonical(str(args.source_package))
    for other in (prior,acquisition,source_package):l.need(other!=root and root not in other.parents and other not in root.parents,'job/input roots overlap')
    l.need(l.tree(acquisition)==spec['acquisition_files'],'acquisition helper tree changed')
    for name,info in spec['source_files'].items():
        path=source_package/name;l.need(l.regular(path).st_size==info['bytes'] and l.file_sha(path)==info['sha256'],'fixed source package changed')
    bundle_raw=l.read_pinned(specpath.parent/'CONTEXT_BUNDLE.json',spec['bundle_sha256']);bundle=p.validate_context_bundle(bundle_raw,spec['bundle_sha256'])
    now=datetime.now(timezone.utc);deadline=ENTRY_MONOTONIC+spec['max_seconds']
    earliest=min([p.timestamp(x['identity']['run_started_at']).timestamp()+p.MAX_AGE for x in (bundle.old_context,bundle.prior_context)]+[p.timestamp(x['prepare']['expires_at']).timestamp() for x in (bundle.old_context,bundle.prior_context)]+[p.timestamp(r['pin']['expires_at']).timestamp() for r in bundle.data['old_stage_rows']+bundle.data['prior_candidate_rows']])
    deadline=min(deadline,time.monotonic()+earliest-now.timestamp());budget.tighten_wall(earliest);budget.tighten(deadline)
    priorfiles=l.parse(l.read_pinned(specpath.parent/'PRIOR_FILES.json',spec['prior_files_sha256']))
    commands=[]
    with l.frozen_prior(prior,priorfiles) as native:
        f=native.f
        manifest=f.pinned_load(source_package/'SOURCE_MANIFEST.json',p.PRIOR_MANIFEST)
        f.extract_sources(source_package/'hierarchy-c-sources.tar.gz',root/'source',manifest)
        def command(label,argv,env,sessions):
            remaining=budget.remaining()
            result=budget.process(lambda:f.run_process(argv,cwd=root,env=env,timeout=remaining,stdout=logs/(label+'.stdout'),stderr=logs/(label+'.stderr'),max_log_bytes=spec['max_log_bytes'],
                limits={'address_space_bytes':spec['memory_bytes'],'rss_tree_bytes':spec['memory_bytes'],'max_created_file_bytes':1024**3+1024**2},allow_new_sessions=sessions))
            commands.append({'phase':label,'argv':argv,'result':result,'timeout_seconds':remaining})
            successful(result,sessions=sessions);l.need(time.monotonic()<deadline and datetime.now(timezone.utc).timestamp()<earliest,'shared historical deadline exceeded')
        # Separate process means transport's historical imports cannot contaminate semantics.
        command('acquisition',[sys.executable,'-I','-S','-B',str(acquisition/'historical_acquisition.py'),'--quarantine',str(root/'acquired'),'--deadline-monotonic',str(deadline)],child_environment(root,acquisition=True),False)
        receipt=root/'acquired/TRANSPORT_RECEIPT.json';receipt_sha=l.file_sha(receipt)
        semantic_args=[str(HERE/'three_context_admit.py'),'--spec',str(specpath.parent/'ADMISSION_SPEC.json'),'--spec-sha256',spec['admission_spec_sha256'],
            '--prior-root',str(prior),'--source-root',str(root/'source'),'--source-manifest',str(source_package/'SOURCE_MANIFEST.json'),
            '--transport-root',str(root/'acquired'),'--transport-receipt-sha256',receipt_sha,'--workspace',str(write_root/'workspace'),
            '--output',str(write_root/'output'),'--deadline-monotonic',str(deadline)]
        command('semantic',sandbox_command(sys.executable,semantic_args,write_root,[HERE,specpath.parent,prior,root/'source',source_package,root/'acquired']),child_environment(write_root,acquisition=False),True)
        complete=l.parse((write_root/'output/COMPLETION.json').read_bytes())
        l.need(complete['status']=='historical_payloads_native_validated_only' and complete['proof_pass_claimed'] is False and complete['activation_allowed'] is False and complete['stage_count']==48 and complete['module_count']==3153,'semantic result mismatch')
        l.need(complete['transport_receipt_sha256']==receipt_sha and complete['spec_sha256']==spec['admission_spec_sha256'],'semantic result input binding mismatch')
        native.f.verify_sources(root/'source',manifest)
    result={'schema':'fixed-historical-admission-job-result-v1','status':'admission_only_complete','proof_pass_claimed':False,'activation_allowed':False,'job_spec_sha256':args.spec_sha256,
        'commands':commands,'transport_receipt_sha256':receipt_sha,'semantic_completion_sha256':l.file_sha(write_root/'output/COMPLETION.json'),
        'original_deadline_utc':'2026-10-22T06:15:54Z','independent_reconciliation_required':True}
    finalize_result(root,result,budget)
    return result


def finalize_result(root,result,budget):
    # Called only after the frozen historical loader's final source rehash.
    budget.check();l.durable(root/'RESULT.json',l.json_bytes(result));budget.check()


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    for name in ('spec','workspace','prior-root','acquisition-root','source-package'):ap.add_argument('--'+name,type=Path,required=True)
    ap.add_argument('--spec-sha256',required=True);args=ap.parse_args()
    try:
        with JobBudget() as budget:run_job(args,budget)
    except BaseException:
        print('Historical admission failed closed; no proof or activation verdict.',file=sys.stderr);raise SystemExit(1)
    print('Historical native admission completed; independent reconciliation and all proof gates remain.')
if __name__=='__main__':main()
