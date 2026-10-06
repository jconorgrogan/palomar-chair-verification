#!/usr/bin/env python3
"""Real Lake targets, dependency ready, at most two single-thread Lean compilers.
Does not fabricate or copy Lake trace state. Independent verification is a later phase.
"""
from pathlib import Path
import json,os,re,signal,subprocess,time,sys,hashlib
R=Path(__file__).resolve().parents[1];os.chdir(R)
KiB=1024;GiB=1024*1024
RESERVE=3*GiB//2
MAX_JOBS=min(2,max(1,int(os.environ.get('T5_BUILD_JOBS','2'))))

def meminfo():
 d={}
 for line in Path('/proc/meminfo').read_text().splitlines():
  k,v=line.split(':',1);d[k]=int(v.split()[0])
 return d

def process_rss(pid):
 parents={};rss={}
 for p in Path('/proc').iterdir():
  if not p.name.isdigit():continue
  try:
   s=(p/'status').read_text();parents[int(p.name)]=int(re.search(r'^PPid:\s+(\d+)',s,re.M)[1]);m=re.search(r'^VmRSS:\s+(\d+)',s,re.M);rss[int(p.name)]=int(m[1]) if m else 0
  except (OSError,TypeError,ValueError):pass
 ids={pid};changed=True
 while changed:
  extra={p for p,par in parents.items() if par in ids}-ids;changed=bool(extra);ids|=extra
 return sum(rss.get(p,0) for p in ids)

modules=[m for m in (R/'scripts/project-module-order.txt').read_text().splitlines() if m]
assert len(modules)==len(set(modules))
metrics=json.loads((R/'scripts/build-resource-profile.json').read_text());allowed=set(modules)
deps={};sourcehash={}
for m in modules:
 p=R/(m.replace('.','/')+'.lean');s=p.read_text();sourcehash[m]=hashlib.sha256(p.read_bytes()).hexdigest()
 deps[m]={d for d in re.findall(r'^(?:public )?import(?: all)? (\S+)\s*$',s,re.M) if d in allowed}
assert all(d in set(modules[:i]) for i,m in enumerate(modules) for d in deps[m]),'Order is not topological'
logdir=R/'.verification/build';logdir.mkdir(parents=True,exist_ok=True)
env=dict(os.environ,LEAN_NUM_THREADS='1',MATHLIB_NO_CACHE_ON_UPDATE='1')
if meminfo()['MemTotal']<7*GiB:MAX_JOBS=1
print(json.dumps({'phase':'project-build','max_processes':MAX_JOBS,'reserve_kib':RESERVE,'memory':meminfo(),'modules':len(modules)}),flush=True)
running={};done=set();waiting=list(modules);receipts=[];start=time.monotonic()
def abort(reason):
 print('BUILD_ABORT '+reason,flush=True)
 for j in running.values():
  try:os.killpg(j['process'].pid,signal.SIGTERM)
  except ProcessLookupError:pass
 for j in running.values():
  try:j['process'].wait(timeout=10)
  except subprocess.TimeoutExpired:
   try:os.killpg(j['process'].pid,signal.SIGKILL)
   except ProcessLookupError:pass
  j['output'].close()
 raise SystemExit(1)
try:
 while waiting or running:
  mi=meminfo()
  if running and mi['MemAvailable']<RESERVE:abort('available memory below 1.5 GiB safety reserve')
  for m,j in list(running.items()):
   j['rss']=process_rss(j['process'].pid);j['peak']=max(j['peak'],j['rss']);rc=j['process'].poll()
   if rc is None:continue
   j['output'].close();r={'module':m,'exit_code':rc,'elapsed_seconds':time.monotonic()-j['start'],'observed_peak_tree_rss_kib':j['peak'],'source_sha256':sourcehash[m],'command':['lake','build',m]};receipts.append(r)
   print(json.dumps(r),flush=True)
   (logdir/'receipts.json').write_text(json.dumps(receipts,indent=2)+'\n')
   if rc!=0:
    print(j['log'].read_text(errors='replace'),flush=True);abort('Lake target failed: '+m)
   if hashlib.sha256((R/(m.replace('.','/')+'.lean')).read_bytes()).hexdigest()!=sourcehash[m]:abort('source changed: '+m)
   done.add(m);del running[m]
  if waiting and len(running)<MAX_JOBS:
   selected=None
   for m in waiting:
    if not deps[m]<=done:continue
    measured=metrics.get(m,{}).get('peak_rss_kib') or 2503784
    # 15% compiler headroom, at least 1.25 GiB per admitted target.
    budget=max(5*GiB//4,(measured*115+99)//100)
    reserved=sum(max(0,j['budget']-j['rss']) for j in running.values())
    if meminfo()['MemAvailable']>=RESERVE+reserved+budget:selected=(m,budget);break
   if selected:
    m,budget=selected;waiting.remove(m);p=logdir/(m.replace('.','_')+'.log');f=p.open('w');proc=subprocess.Popen(['lake','build',m],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
    running[m]={'process':proc,'output':f,'log':p,'start':time.monotonic(),'budget':budget,'rss':0,'peak':0}
    print(json.dumps({'start_module':m,'pid':proc.pid,'reserved_peak_kib':budget,'active':len(running),'completed':len(done)}),flush=True)
    continue
   if not running:abort('no ready module fits the memory budget or dependency graph')
  time.sleep(0.5)
except (KeyboardInterrupt,Exception) as e:abort(type(e).__name__+': '+str(e))
print(json.dumps({'phase':'project-build-complete','targets':len(done),'wall_seconds':time.monotonic()-start,'all_exit_zero':True}),flush=True)
