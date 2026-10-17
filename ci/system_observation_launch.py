#!/usr/bin/python3
"""Held-root, bounded system observation. This receipt grants no profile authority."""
import os,sys,time
ENTRY=time.monotonic()
def no_bytecode(event,args):
 if event=='open' and args and isinstance(args[0],(str,bytes,os.PathLike)) and os.fsdecode(args[0]).endswith(('.pyc','.pyo')):raise FileNotFoundError('bytecode refused')
sys.addaudithook(no_bytecode)
import argparse,hashlib,json,math,re,resource,signal,stat,types
from datetime import datetime,timezone
from fractions import Fraction
from pathlib import Path
WALL=datetime.now(timezone.utc)
MIB=1024**2; GIB=1024**3
NATIVE_SHA='9085c9eea092c270fbd6952834839103c66519a7b4716fe09147001c7d96355d'
ENV={'LANG':'C.UTF-8','LC_ALL':'C.UTF-8','TZ':'UTC'}
LIMITS={'address_space_bytes':256*MIB,'rss_tree_bytes':256*MIB,'max_created_file_bytes':MIB}
NAMES={'system-observation.stdout','system-observation.stderr','launch-receipt.json'}
class Rejected(ValueError):pass
def need(ok,msg):
 if not ok:raise Rejected(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def encode(v):return (json.dumps(v,sort_keys=True,indent=2,allow_nan=False)+'\n').encode()
def pin(b):return {'bytes':len(b),'sha256':sha(b)}
def digest(v):return type(v) is str and len(v)==64 and all(c in '0123456789abcdef' for c in v)
def parse(b):
 def pairs(rows):
  v={}
  for k,x in rows:need(k not in v,'duplicate JSON key');v[k]=x
  return v
 return json.loads(b,object_pairs_hook=pairs,parse_constant=lambda _:(_ for _ in ()).throw(Rejected('nonfinite JSON')))
def exact(a,b):
 need(type(a) is type(b),'exact value type')
 if type(a) is dict:
  need(set(a)==set(b),'exact value fields')
  for k in a:exact(a[k],b[k])
 elif type(a) is list:
  need(len(a)==len(b),'exact value length')
  for x,y in zip(a,b):exact(x,y)
 else:need(a==b,'exact value')
def ident(s):return (s.st_dev,s.st_ino,s.st_mode,s.st_nlink,s.st_uid,s.st_gid,s.st_size,s.st_mtime_ns,s.st_ctime_ns)
def did(s):return (s.st_dev,s.st_ino,s.st_mode,s.st_uid,s.st_gid)
def canonical(p):
 s=os.fspath(p);p=Path(p);need(p.is_absolute() and str(p)==s and '..' not in p.parts and len(p.parts)<=24,'canonical absolute path')
 for q in (p,*p.parents):need(not q.is_symlink(),'no path aliases')
 return p
class Budget:
 def __init__(self):self.start=ENTRY;self.last=ENTRY;self.wall=WALL;self.lastwall=WALL;self.failed=False
 def check(self):
  if self.failed:raise Rejected('poisoned launch deadline')
  try:
   n=time.monotonic();w=datetime.now(timezone.utc)
   need(type(n) in (int,float) and math.isfinite(n) and n>=self.last and n-self.start<50 and w>=self.lastwall and (w-self.wall).total_seconds()<50,'original launch deadline')
   self.last=n;self.lastwall=w;return n
  except BaseException:self.failed=True;raise
 def timeout(self):
  n=self.check();v=min(35,int((Fraction(47)-Fraction(n)+Fraction(self.start))//1));need(v>=30,'full observer and cleanup budget');return v
class Signals:
 """Defer termination through the entire pinned native cleanup, then reject."""
 def __init__(self,budget):self.budget=budget;self.native=False;self.expired=False;self.old={}
 def handle(self,signum,frame):
  self.expired=True;self.budget.failed=True
  if not self.native:raise Rejected('observation supervisor signal')
 def __enter__(self):
  remaining=50-(time.monotonic()-self.budget.start);need(0<remaining<=50,'original signal deadline')
  try:
   for sig in (signal.SIGTERM,signal.SIGALRM):self.old[sig]=signal.signal(sig,self.handle)
   signal.setitimer(signal.ITIMER_REAL,remaining)
  except BaseException:
   for sig,old in self.old.items():signal.signal(sig,old)
   raise
  return self
 def __exit__(self,kind,value,trace):
  signal.setitimer(signal.ITIMER_REAL,0)
  for sig,old in self.old.items():signal.signal(sig,old)
  if kind is None:
   need(not self.expired,'deferred observation signal');self.budget.check()
 def run(self,fn,*args,**kwargs):
  self.budget.check();need(not self.native,'single native lifecycle');self.native=True
  try:return fn(*args,**kwargs)
  finally:self.native=False

class Root:
 """No-follow ancestor descriptors retained for the complete native lifecycle."""
 def __init__(self,work,check,create):
  self.path=canonical(work);need(str(self.path)!='/' and len(self.path.parts)>=3,'nonroot work path');self.check=check;self.fds=[];self.ids=[];self.paths=list(reversed((self.path,*self.path.parents)));self.closed=False
  try:
   for i,p in enumerate(self.paths):
    check()
    if i==len(self.paths)-1 and create:
     self.verify();fs=os.fstatvfs(self.fds[-1]);unit=max(fs.f_bsize,fs.f_frsize)
     need(fs.f_bavail*fs.f_frsize>=4*MIB+16*unit and fs.f_favail>=16,'capture receipt and metadata reserve')
     os.mkdir(p.name,0o700,dir_fd=self.fds[-1])
    fd=os.open(str(p) if i==0 else p.name,os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW|os.O_CLOEXEC,**({} if i==0 else {'dir_fd':self.fds[-1]}))
    self.fds.append(fd);s=os.fstat(fd);need(stat.S_ISDIR(s.st_mode),'directory ownership');self.ids.append(did(s));self.verify()
   need(not os.listdir(self.fds[-1]) if create else True,'new empty work root')
  except BaseException:
   self.close(False);raise
 @property
 def fd(self):need(not self.closed,'held root open');return self.fds[-1]
 def verify(self):
  self.check()
  for i,(p,w) in enumerate(zip(self.paths,self.ids)):
   need(did(p.lstat())==w and stat.S_ISDIR(p.lstat().st_mode),'named directory ownership')
   if not self.closed:
    need(did(os.fstat(self.fds[i]))==w,'held directory ownership')
    if i:need(did(os.stat(p.name,dir_fd=self.fds[i-1],follow_symlinks=False))==w,'relative directory ownership')
  self.check()
 def close(self,validate=True):
  if self.closed:return
  first=None
  for fd in reversed(self.fds):
   try:os.close(fd)
   except BaseException as e:
    if first is None:first=e
  self.closed=True
  if validate:self.verify()
  if first:raise first
 def capture(self,name):need(name in NAMES-{'launch-receipt.json'},'fixed capture');return Capture(self,name)
 def read(self,name,maximum=MIB):
  need(name in NAMES,'fixed evidence read');self.verify();fd=os.open(name,os.O_RDONLY|os.O_NOFOLLOW|os.O_CLOEXEC,dir_fd=self.fd)
  try:
   before=os.fstat(fd);need(stat.S_ISREG(before.st_mode) and before.st_nlink==1 and not before.st_mode&0o022 and 0<=before.st_size<=maximum,'bounded owned regular evidence');data=bytearray()
   while True:
    self.check();b=os.read(fd,min(65536,maximum+1-len(data)));self.check()
    if not b:break
    data.extend(b);need(len(data)<=maximum,'evidence read cap')
   need(ident(os.fstat(fd))==ident(before),'unchanged held evidence')
  finally:os.close(fd)
  self.verify();need(ident(os.stat(name,dir_fd=self.fd,follow_symlinks=False))==ident(before),'post-close evidence identity');self.check();return bytes(data),ident(before)
 def write(self,name,data):
  need(name=='launch-receipt.json' and type(data) is bytes and len(data)<=MIB,'bounded fixed receipt');self.verify();fd=os.open(name,os.O_WRONLY|os.O_CREAT|os.O_EXCL|os.O_NOFOLLOW|os.O_CLOEXEC,0o600,dir_fd=self.fd)
  try:
   v=memoryview(data)
   while v:self.check();n=os.write(fd,v);need(n>0,'receipt short write');v=v[n:]
   os.fsync(fd);before=ident(os.fstat(fd))
  finally:os.close(fd)
  os.fsync(self.fd);self.verify();need(ident(os.stat(name,dir_fd=self.fd,follow_symlinks=False))==before,'post-close receipt identity');self.check()
class Capture:
 def __init__(self,root,name):self.root=root;self.name=name;self.owned=None
 def open(self,mode):
  need(mode=='xb' and self.owned is None,'exclusive capture mode');self.root.verify();fd=os.open(self.name,os.O_WRONLY|os.O_CREAT|os.O_EXCL|os.O_NOFOLLOW|os.O_CLOEXEC,0o600,dir_fd=self.root.fd)
  try:s=os.fstat(fd);handle=os.fdopen(fd,'wb')
  except BaseException:
   os.close(fd);raise
  self.owned=(s.st_dev,s.st_ino);return handle
 def stat(self):
  self.root.verify();s=os.stat(self.name,dir_fd=self.root.fd,follow_symlinks=False);need(stat.S_ISREG(s.st_mode) and s.st_nlink==1 and (s.st_dev,s.st_ino)==self.owned,'capture inode binding');return s

def source(path,cap,check):
 p=canonical(path);check();fd=os.open(p,os.O_RDONLY|os.O_NOFOLLOW|os.O_CLOEXEC)
 try:
  s=os.fstat(fd);need(stat.S_ISREG(s.st_mode) and s.st_nlink==1 and not s.st_mode&0o022 and s.st_size<=cap,'bounded regular source');b=bytearray()
  while True:
   check();x=os.read(fd,min(65536,cap+1-len(b)));check()
   if not x:break
   b.extend(x);need(len(b)<=cap,'source cap')
  need(ident(os.fstat(fd))==ident(s),'held source identity')
 finally:os.close(fd)
 check();need(ident(p.lstat())==ident(s),'post-close source identity');data=bytes(b);check();return data
def load(name,b,path):
 need(name not in sys.modules,'fresh native namespace');m=types.ModuleType(name);m.__file__=str(path);sys.modules[name]=m;exec(compile(b,str(path),'exec',dont_inherit=True),m.__dict__);return m

def safety(r,timeout):
 need(type(r) is dict and set(r)=={'exit_code','timed_out','log_overflow','memory_exceeded','surviving_children','escaped_descendants','new_sessions_explicitly_allowed','process_group_empty','descendants_empty','cleanup_bound_seconds','cleanup_elapsed_seconds','peak_sampled_tree_rss_bytes','elapsed_seconds'},'exact native result')
 need(type(r['exit_code']) is int and r['exit_code']==0,'observer exit')
 for k in ('timed_out','log_overflow','memory_exceeded','surviving_children','escaped_descendants','new_sessions_explicitly_allowed'):need(r[k] is False,'native resource rejection')
 for k in ('process_group_empty','descendants_empty'):need(r[k] is True,'native cleanup')
 for k in ('cleanup_bound_seconds','cleanup_elapsed_seconds','elapsed_seconds'):need(type(r[k]) in (int,float) and math.isfinite(r[k]) and r[k]>=0,'finite native time')
 need(r['cleanup_bound_seconds']==3 and r['cleanup_elapsed_seconds']<=3 and r['elapsed_seconds']<=timeout+3,'native cleanup bound')
 need(type(r['peak_sampled_tree_rss_bytes']) is int and 0<=r['peak_sampled_tree_rss_bytes']<=256*MIB,'target-tree RSS')
def observation(raw,stderr,c,contract_sha):
 need(not stderr and 0<len(raw)<=MIB and raw.endswith(b'\n') and len(raw.splitlines())==1,'single observation and empty stderr');v=parse(raw)
 want={'schema','contract_sha256','selected_python_profile_sha256','observed_interpreter','selected_python_executable_and_version_match','full_python_fingerprint_rechecked','system_profile','system_profile_sha256','profile_approved','guard_modes_executed','subprocess_executed','runtime_installed','proof_pass_claimed'}
 need(type(v) is dict and set(v)==want and v['schema']=='c087-unapproved-guard-system-observation-v1' and v['contract_sha256']==contract_sha and v['selected_python_profile_sha256']==c['selected_python_profile_sha256'],'exact observation binding')
 for k in ('full_python_fingerprint_rechecked','profile_approved','guard_modes_executed','subprocess_executed','runtime_installed','proof_pass_claimed'):need(v[k] is False,'observation-only flags')
 need(v['selected_python_executable_and_version_match'] is True,'selected interpreter observation');keys=('invoked_path','executable_realpath','executable','sys_version','version_info','implementation','cache_tag');exact(v['observed_interpreter'],{k:c['selected_python_profile'][k] for k in keys})
 p=v['system_profile'];need(type(p) is dict and set(p)=={'schema','os_release_sha256','binaries','mount_aliases'} and p['schema']=='c087-approved-guard-system-profile-v1' and digest(p['os_release_sha256']) and sha(encode(p))==v['system_profile_sha256'],'system profile shape')
 need(type(p['binaries']) is dict and set(p['binaries'])=={'/usr/bin/bwrap','/usr/bin/prlimit'},'exact observed binaries')
 for r in p['binaries'].values():
  need(type(r) is dict and set(r)=={'realpath','bytes','sha256'} and type(r['realpath']) is str and str(Path(r['realpath']))==r['realpath'] and Path(r['realpath']).is_relative_to('/usr') and '..' not in Path(r['realpath']).parts and type(r['bytes']) is int and 0<r['bytes']<=8*MIB and digest(r['sha256']),'observed binary row')
 need(type(p['mount_aliases']) is dict and set(p['mount_aliases'])=={'/usr','/bin','/lib','/lib64'},'exact mount aliases')
 for r in p['mount_aliases'].values():
  need(type(r) is dict and set(r)=={'kind','realpath','symlink_target'} and r['kind'] in ('symlink','directory') and type(r['realpath']) is str and r['realpath'].startswith('/') and str(Path(r['realpath']))==r['realpath'] and '..' not in Path(r['realpath']).parts,'mount alias shape')
  need(r['symlink_target'] is None if r['kind']=='directory' else type(r['symlink_target']) is str and 0<len(r['symlink_target'])<=4096,'mount alias target')
 return v

def contract_value(c):
 need(type(c) is dict and set(c)=={'schema','review_status','inputs','observer_contract','parent_seconds','outer_seconds','term_watchdog_seconds','kill_grace_seconds','target_timeout_seconds','physical_capture_bytes','profile_approved','guard_modes_allowed'},'exact launcher contract')
 need(c['schema']=='c087-system-observation-launch-contract-v1' and c['review_status']=='reviewed_for_observation' and c['profile_approved'] is False and c['guard_modes_allowed'] is False,'reviewed observation launch')
 for k,v in {'parent_seconds':50,'outer_seconds':70,'term_watchdog_seconds':60,'kill_grace_seconds':10,'target_timeout_seconds':35,'physical_capture_bytes':2*MIB}.items():need(type(c[k]) is int and c[k]==v,'fixed launch bound')
 need(type(c['inputs']) is dict and set(c['inputs'])=={'ci/system_observation_launch.py','ci/guard_system_observer.py','ci/fresh_stage.py'},'fixed code inputs')
 for row in [*c['inputs'].values(),c['observer_contract']]:need(type(row) is dict and set(row)=={'bytes','sha256'} and type(row['bytes']) is int and 0<row['bytes']<=128*1024 and digest(row['sha256']),'exact source pin')

def configuration(root,contract_sha,check):
 check();root=canonical(root);need(Path.cwd()==root,'exact checkout cwd');raw=source(root/'launch-contract.json',65536,check);need(sha(raw)==contract_sha,'launch contract pin');c=parse(raw);contract_value(c)
 buffers={}
 for rel,row in c['inputs'].items():b=source(root/rel,128*1024,check);need(pin(b)==row,'launch input pin');buffers[rel]=b
 need(sha(buffers['ci/fresh_stage.py'])==NATIVE_SHA,'unchanged native helper')
 observer_raw=source(root/'system-observation-contract.json',65536,check);need(pin(observer_raw)==c['observer_contract'],'observer contract pin');oc=parse(observer_raw)
 need(oc.get('review_status')=='reviewed_for_observation' and oc.get('profile_approved') is False and oc.get('guard_modes_allowed') is False and oc.get('selected_python_profile_sha256')==sha(encode(oc.get('selected_python_profile'))),'separate selected observation contract')
 exact(oc['observer'],c['inputs']['ci/guard_system_observer.py'])
 return root,raw,c,buffers,observer_raw,oc

def execute(root,work,contract_sha,budget,signals):
 need(signals.budget is budget,'same original signal budget');check=budget.check;root,raw,c,buffers,observer_raw,oc=configuration(root,contract_sha,check)
 observer=load('_c087_system_observer',buffers['ci/guard_system_observer.py'],root/'ci/guard_system_observer.py');before_python=observer.interpreter_identity(oc['selected_python_profile'],budget);check()
 native=load('_c087_system_launch_native',buffers['ci/fresh_stage.py'],root/'ci/fresh_stage.py');check()
 held=Root(work,check,True);saved={};record=None
 try:
  timeout=budget.timeout();argv=['/usr/bin/python3','-I','-S','-B',str(root/'ci/guard_system_observer.py'),'--contract-sha256',sha(observer_raw)]
  command={'argv':argv,'cwd':str(root),'env':dict(ENV),'timeout_seconds':timeout,'nominal_timeout_seconds':35,'limits':dict(LIMITS),'max_log_bytes':MIB}
  result=signals.run(native.run_process,argv,cwd=root,env=dict(ENV),timeout=timeout,stdout=held.capture('system-observation.stdout'),stderr=held.capture('system-observation.stderr'),max_log_bytes=MIB,limits=dict(LIMITS),allow_new_sessions=False)
  command['native_result']=result
  record={'schema':'c087-system-observation-launch-receipt-v1','status':'REJECTED','contract_sha256':contract_sha,'observer_contract_sha256':sha(observer_raw),'inputs':c['inputs'],'selected_python_profile_sha256':oc['selected_python_profile_sha256'],'command':command,'stdout':None,'stderr':None,'profile_approved':False,'guard_modes_executed':False,'proof_pass_claimed':False}
  safety(result,timeout);check();out,out_id=held.read('system-observation.stdout');err,err_id=held.read('system-observation.stderr');need(len(out)+len(err)<=MIB,'combined accepted capture cap');observation(out,err,oc,sha(observer_raw))
  for rel,row in c['inputs'].items():need(pin(source(root/rel,128*1024,check))==row,'final code rehash')
  need(source(root/'launch-contract.json',65536,check)==raw and source(root/'system-observation-contract.json',65536,check)==observer_raw,'final contract rehash')
  exact(observer.interpreter_identity(oc['selected_python_profile'],budget),before_python);check()
  record.update(status='OBSERVED_UNAPPROVED',stdout=pin(out),stderr=pin(err));saved={'system-observation.stdout':out_id,'system-observation.stderr':err_id}
  held.write('launch-receipt.json',encode(record));receipt,receipt_id=held.read('launch-receipt.json');need(receipt==encode(record),'receipt readback');saved['launch-receipt.json']=receipt_id
  need(set(os.listdir(held.fd))==NAMES,'exact evidence tree')
  for name,i in saved.items():need(ident(os.stat(name,dir_fd=held.fd,follow_symlinks=False))==i,'final capture and receipt binding')
  held.verify();check()
 except BaseException:
  if record is not None:
   try:
    # If a successful receipt already exists, terminal failure still bars eligibility.
    record['status']='REJECTED';held.write('launch-receipt.json',encode(record))
   except BaseException:pass
  raise
 finally:held.close()
 for name,i in saved.items():need(ident((held.path/name).lstat())==i,'final post-close evidence identity')
 held.verify();check()

def receipt_value(r,root,c,oc,contract_sha,observer_sha,out,err):
 need(type(r) is dict and set(r)=={'schema','status','contract_sha256','observer_contract_sha256','inputs','selected_python_profile_sha256','command','stdout','stderr','profile_approved','guard_modes_executed','proof_pass_claimed'},'exact launch receipt')
 need(r['schema']=='c087-system-observation-launch-receipt-v1' and r['status']=='OBSERVED_UNAPPROVED' and r['contract_sha256']==contract_sha and r['observer_contract_sha256']==observer_sha and r['selected_python_profile_sha256']==oc['selected_python_profile_sha256'],'receipt identity')
 for k in ('profile_approved','guard_modes_executed','proof_pass_claimed'):need(r[k] is False,'receipt authority false')
 exact(r['inputs'],c['inputs']);exact(r['stdout'],pin(out));exact(r['stderr'],pin(err))
 cmd=r['command'];need(type(cmd) is dict and set(cmd)=={'argv','cwd','env','timeout_seconds','nominal_timeout_seconds','limits','max_log_bytes','native_result'},'exact command receipt')
 exact(cmd['argv'],['/usr/bin/python3','-I','-S','-B',str(root/'ci/guard_system_observer.py'),'--contract-sha256',observer_sha]);exact(cmd['cwd'],str(root));exact(cmd['env'],ENV);exact(cmd['limits'],LIMITS)
 need(type(cmd['timeout_seconds']) is int and 30<=cmd['timeout_seconds']<=35 and type(cmd['nominal_timeout_seconds']) is int and cmd['nominal_timeout_seconds']==35 and type(cmd['max_log_bytes']) is int and cmd['max_log_bytes']==MIB,'command time and log bounds');safety(cmd['native_result'],cmd['timeout_seconds'])
 observation(out,err,oc,observer_sha)

def marker(root,work,contract_sha,values,check):
 want={'artifact_id':r'[1-9][0-9]{0,19}','artifact_sha256':r'[0-9a-f]{64}','run_id':r'[1-9][0-9]{0,19}','run_attempt':'1','commit':r'[0-9a-f]{40}'}
 need(type(values) is dict and set(values)==set(want),'exact upload binding')
 for k,pattern in want.items():need(type(values[k]) is str and re.fullmatch(pattern,values[k]) is not None,'upload identity shape')
 root,raw,c,buffers,observer_raw,oc=configuration(root,contract_sha,check);held=Root(work,check,False);saved={}
 try:
  need(set(os.listdir(held.fd))==NAMES,'exact uploaded evidence tree')
  out,saved['system-observation.stdout']=held.read('system-observation.stdout');err,saved['system-observation.stderr']=held.read('system-observation.stderr');receipt,saved['launch-receipt.json']=held.read('launch-receipt.json')
  receipt_value(parse(receipt),root,c,oc,contract_sha,sha(observer_raw),out,err)
  result='C087_SYSTEM_OBSERVATION_UPLOADED '+json.dumps(dict(values,contract_sha256=contract_sha,observer_contract_sha256=sha(observer_raw),stdout_sha256=sha(out),launch_receipt_sha256=sha(receipt)),sort_keys=True,separators=(',',':'))
  for name,i in saved.items():need(ident(os.stat(name,dir_fd=held.fd,follow_symlinks=False))==i,'marker final evidence identity')
  held.verify();check()
 finally:held.close()
 for name,i in saved.items():need(ident((held.path/name).lstat())==i,'marker post-close evidence identity')
 held.verify();check();return result

def main():
 budget=Budget();p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--contract-sha256',required=True);p.add_argument('--work',required=True);a=p.parse_args();need(digest(a.contract_sha256),'contract digest');need(sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode,'isolated source-only launcher')
 os.sched_setaffinity(0,{min(os.sched_getaffinity(0))});resource.setrlimit(resource.RLIMIT_AS,(GIB,GIB));resource.setrlimit(resource.RLIMIT_CPU,(60,60));resource.setrlimit(resource.RLIMIT_FSIZE,(MIB,MIB));resource.setrlimit(resource.RLIMIT_CORE,(0,0));resource.setrlimit(resource.RLIMIT_NOFILE,(64,64))
 with Signals(budget) as signals:execute(Path(__file__).resolve().parents[1],a.work,a.contract_sha256,budget,signals)
if __name__=='__main__':main()
