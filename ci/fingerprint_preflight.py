#!/usr/bin/python3
"""Bounded fingerprint observation only. No profile approval or fixture mode."""
import sys,os,time
_ENTRY_MONOTONIC=time.monotonic()
# Source fallback before ordinary imports; -B alone does not refuse cache reads.
def no_bytecode(event,args):
 if event=='open' and args and isinstance(args[0],(str,bytes,os.PathLike)) and os.fsdecode(args[0]).endswith(('.pyc','.pyo')):raise FileNotFoundError('bytecode forbidden')
sys.addaudithook(no_bytecode)
import argparse,hashlib,json,math,resource,stat,time,types
from datetime import datetime,timezone
_ENTRY_WALL=datetime.now(timezone.utc)
from fractions import Fraction
from pathlib import Path
GIB=1024**3
NATIVE_SHA='9085c9eea092c270fbd6952834839103c66519a7b4716fe09147001c7d96355d'
ENV={'LANG':'C.UTF-8','LC_ALL':'C.UTF-8','TZ':'UTC'}
LIMITS={'address_space_bytes':GIB,'rss_tree_bytes':GIB,'max_created_file_bytes':16*1024**2}
LOG_CAP=256*1024
EVIDENCE_NAMES={'stdout.log','stderr.log','command.json','result.json','collection.json','completion.json','incomplete.json'}
STDLIB_NAMES={'pathlib','shutil','tarfile','tempfile','dataclasses','inspect','os','posixpath','stat','fractions','importlib','importlib._bootstrap','importlib._bootstrap_external','ctypes','json','json.encoder','json.decoder'}
EXT_NAMES={'_ctypes','_ssl','_hashlib','_posixsubprocess','zlib','_bz2','_lzma','math'}
class Rejected(ValueError):pass
def need(ok,msg):
 if not ok:raise Rejected(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def encoded(j):return (json.dumps(j,sort_keys=True,indent=2,allow_nan=False)+'\n').encode()
def pairs(rows):
 out={}
 for k,v in rows:need(k not in out,'duplicate JSON key');out[k]=v
 return out
def parse(b):return json.loads(b.decode('utf-8'),object_pairs_hook=pairs,parse_constant=lambda _:(_ for _ in ()).throw(Rejected('nonfinite JSON')))
def pin(b):return {'bytes':len(b),'sha256':sha(b)}
def digest(v):return type(v) is str and len(v)==64 and all(c in '0123456789abcdef' for c in v)
def canonical(p):
 original=os.fspath(p);p=Path(p);need(str(p)==original,'canonical spelling');need(p.is_absolute() and '..' not in p.parts and str(p)!= '/', 'absolute nonroot path')
 for a in (p,*p.parents):need(not a.is_symlink(),'symlink path')
 return p
def read(p,maximum,check):
 check();p=canonical(p);fd=os.open(p,os.O_RDONLY|os.O_NOFOLLOW|os.O_CLOEXEC)
 try:
  before=os.fstat(fd);need(stat.S_ISREG(before.st_mode) and before.st_nlink==1 and 0<=before.st_size<=maximum and not before.st_mode&0o022,'bounded regular input')
  data=bytearray()
  while True:
   check();block=os.read(fd,min(1024**2,maximum+1-len(data)));check()
   if not block:break
   data.extend(block);need(len(data)<=maximum,'read cap')
  after=os.fstat(fd);need((before.st_dev,before.st_ino,before.st_size,before.st_mtime_ns,before.st_ctime_ns)==(after.st_dev,after.st_ino,after.st_size,after.st_mtime_ns,after.st_ctime_ns),'changed input')
 finally:
  try:os.close(fd)
  finally:check()
 check();return bytes(data)
class Budget:
 def __init__(self):
  self.start=_ENTRY_MONOTONIC;self.wall=_ENTRY_WALL;self.last=self.start;self.lastwall=self.wall;self.failed=False
 def check(self):
  if self.failed:raise Rejected('poisoned observation budget')
  try:
   now=time.monotonic();wall=datetime.now(timezone.utc)
   need(type(now) in (int,float) and math.isfinite(now) and now>=self.last and now-self.start<180,'monotonic observation deadline')
   need(wall.tzinfo is not None and wall>=self.lastwall and (wall-self.wall).total_seconds()<180,'wall observation deadline')
   self.last=now;self.lastwall=wall;return now
  except BaseException:self.failed=True;raise
 def timeout(self):
  now=self.check();n=min(120,int((Fraction(177)-Fraction(now)+Fraction(self.start))//1));need(n>0,'positive child budget');return n

def valid_profile(r):
 need(type(r) is dict and set(r)=={'schema','runtime_fingerprint','profile_approved','fixtures_executed','guard_modes_executed','runtime_installed','proof_pass_claimed'},'exact observation schema')
 need(r['schema']=='c087-unapproved-python-fingerprint-v1','observation schema')
 for k in ('profile_approved','fixtures_executed','guard_modes_executed','runtime_installed','proof_pass_claimed'):need(r[k] is False,'observation-only result')
 p=r['runtime_fingerprint'];need(type(p) is dict and set(p)=={'schema','invoked_path','executable_realpath','executable','sys_version','version_info','implementation','cache_tag','stdlib_root','stdlib_sources','stdlib_extensions'},'exact fingerprint schema')
 need(p['schema']=='c087-interpreter-fingerprint-v1' and p['invoked_path']=='/usr/bin/python3' and p['executable_realpath']=='/usr/bin/python3.10' and p['implementation']=='cpython' and p['cache_tag']=='cpython-310' and p['stdlib_root']=='/usr/lib/python3.10','Ubuntu22 Python3.10 observation')
 v=p['version_info'];need(type(v) is list and len(v)==5 and all(type(x) is int for x in v[:3]) and v[:2]==[3,10] and 0<=v[2]<=999 and v[3]=='final' and type(v[4]) is int and v[4]==0,'exact release version shape')
 need(type(p['sys_version']) is str and len(p['sys_version'])<=1024 and p['sys_version'].startswith('3.10.'),'bounded version')
 def file_row(row,with_path=False):
  need(type(row) is dict and set(row)==({'bytes','sha256','relative_path'} if with_path else {'bytes','sha256'}),'exact fingerprint file row')
  need(type(row['bytes']) is int and 0<row['bytes']<=64*1024**2 and digest(row['sha256']),'bounded fingerprint file')
  if with_path:
   x=row['relative_path'];need(type(x) is str and x and len(x)<=1024 and not Path(x).is_absolute() and '..' not in Path(x).parts and str(Path(x))==x,'canonical stdlib path')
 file_row(p['executable']);need(type(p['stdlib_sources']) is dict and set(p['stdlib_sources'])==STDLIB_NAMES and type(p['stdlib_extensions']) is dict and set(p['stdlib_extensions'])==EXT_NAMES,'exact fingerprint module maps')
 for row in p['stdlib_sources'].values():file_row(row,True)
 for row in p['stdlib_extensions'].values():
  if type(row) is dict and set(row)=={'builtin_in_interpreter'}:need(row['builtin_in_interpreter'] is True,'strict builtin')
  else:file_row(row,True)
 return p

def command(observer):
 argv=['/usr/bin/bwrap','--unshare-all','--die-with-parent','--clearenv','--proc','/proc','--dev','/dev','--tmpfs','/tmp']
 for p in ('/usr','/bin','/lib','/lib64'):argv+=['--ro-bind',p,p]
 argv+=['--ro-bind',str(observer.parent),str(observer.parent)]
 for k,v in sorted(ENV.items()):argv+=['--setenv',k,v]
 return argv+['--chdir',str(observer.parent),'--','/usr/bin/python3','-I','-S','-B',str(observer)]
def safety(r,timeout):
 need(type(r) is dict and set(r)=={'exit_code','timed_out','log_overflow','memory_exceeded','surviving_children','escaped_descendants','new_sessions_explicitly_allowed','process_group_empty','descendants_empty','cleanup_bound_seconds','cleanup_elapsed_seconds','peak_sampled_tree_rss_bytes','elapsed_seconds'},'exact native result')
 need(type(r['exit_code']) is int and r['exit_code']==0,'child failed')
 for k in ('timed_out','log_overflow','memory_exceeded','surviving_children','escaped_descendants','new_sessions_explicitly_allowed'):need(r[k] is False,'unsafe native result')
 for k in ('process_group_empty','descendants_empty'):need(r[k] is True,'missing cleanup')
 for k in ('cleanup_bound_seconds','cleanup_elapsed_seconds','elapsed_seconds'):need(type(r[k]) in (int,float) and math.isfinite(r[k]) and r[k]>=0,'bounded native timing')
 need(r['cleanup_bound_seconds']==3 and r['cleanup_elapsed_seconds']<=3 and r['elapsed_seconds']<=timeout+3,'native timing limit')
 need(type(r['peak_sampled_tree_rss_bytes']) is int and 0<=r['peak_sampled_tree_rss_bytes']<=GIB,'native RSS')
def durable(fd,name,data):
 need(name in EVIDENCE_NAMES and type(data) is bytes and len(data)<=1024**2,'fixed evidence write')
 out=os.open(name,os.O_WRONLY|os.O_CREAT|os.O_EXCL|os.O_NOFOLLOW|os.O_CLOEXEC,0o600,dir_fd=fd)
 try:
  view=memoryview(data)
  while view:
   n=os.write(out,view);need(n>0,'short evidence write');view=view[n:]
  os.fsync(out)
 finally:os.close(out)
 os.fsync(fd)
def contract_value(c):
 need(type(c) is dict and set(c)=={'schema','review_status','inputs','approved_profile','fixtures_allowed','child_seconds','controller_seconds','outer_seconds','log_cap','physical_capture_bytes','proof_pass_claimed'},'exact contract')
 need(c['schema']=='c087-python-fingerprint-contract-v1' and c['review_status']=='reviewed_for_execution' and c['approved_profile'] is None and c['fixtures_allowed'] is False and c['proof_pass_claimed'] is False,'reviewed observation only')
 for k,v in {'child_seconds':120,'controller_seconds':180,'outer_seconds':210,'log_cap':LOG_CAP,'physical_capture_bytes':32*1024**2}.items():need(type(c[k]) is int and c[k]==v,'fixed bounds')
 need(type(c['inputs']) is dict and set(c['inputs'])=={'ci/fingerprint_preflight.py','ci/fingerprint_observer.py','ci/fresh_stage.py'},'exact code map')

def remove_completion_owned(work,owned):
 fd=None
 try:
  fd=os.open(work,os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW|os.O_CLOEXEC)
  st=os.fstat(fd);need((st.st_dev,st.st_ino)==owned,'failure cleanup ownership')
  try:os.unlink('completion.json',dir_fd=fd);os.fsync(fd)
  except FileNotFoundError:pass
 finally:
  if fd is not None:os.close(fd)

def execute(root,work,contract_sha,budget):
 check=budget.check;check();root=canonical(root);work=canonical(work);need(work==Path(str(work)) and not work.exists(),'fresh work root')
 raw=read(root/'contract.json',1024**2,check);need(sha(raw)==contract_sha,'contract pin');c=parse(raw);contract_value(c)
 buffers={}
 for rel,row in c['inputs'].items():
  b=read(root/rel,128*1024,check);need(pin(b)==row,'code pin');buffers[rel]=b
 need(sha(buffers['ci/fresh_stage.py'])==NATIVE_SHA,'unchanged native executor')
 os_release=read(Path('/etc/os-release').resolve(strict=True),65536,check).decode();fields={}
 for line in os_release.splitlines():
  if '=' in line:k,v=line.split('=',1);fields[k]=v.strip('"')
 need(fields.get('ID')=='ubuntu' and fields.get('VERSION_ID')=='22.04','Ubuntu22 required')
 parent=work.parent;need(parent.is_dir(),'existing work parent');st=parent.lstat()
 parentfd=os.open(parent,os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW|os.O_CLOEXEC);fd=None
 try:
  held=os.fstat(parentfd);need((held.st_dev,held.st_ino)==(st.st_dev,st.st_ino),'observed parent identity')
  fs=os.fstatvfs(parentfd);unit=max(fs.f_frsize,fs.f_bsize)
  need(fs.f_bavail*fs.f_frsize>=64*1024**2+16*unit and fs.f_favail>=32,'physical capture/evidence reserve')
  check();canonical(parent);need((parent.lstat().st_dev,parent.lstat().st_ino)==(st.st_dev,st.st_ino),'parent before create')
  os.mkdir(work.name,mode=0o700,dir_fd=parentfd)
  fd=os.open(work.name,os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW|os.O_CLOEXEC,dir_fd=parentfd);owned=(os.fstat(fd).st_dev,os.fstat(fd).st_ino)
 except BaseException:
  try:
   if fd is not None:os.close(fd)
  finally:os.close(parentfd)
  raise
 def verify_ownership():
  check();canonical(work);canonical(parent)
  w=work.lstat();par=parent.lstat()
  need(stat.S_ISDIR(w.st_mode) and stat.S_ISDIR(par.st_mode) and (w.st_dev,w.st_ino)==owned and (par.st_dev,par.st_ino)==(st.st_dev,st.st_ino),'owned final output identity');check()
 try:
  verify_ownership()
  name='_c087_fingerprint_native';need(name not in sys.modules,'native namespace occupied');native=types.ModuleType(name);native.__file__=str(root/'ci/fresh_stage.py');sys.modules[name]=native
  exec(compile(buffers['ci/fresh_stage.py'],native.__file__,'exec',dont_inherit=True),native.__dict__);check()
  observer=root/'ci/fingerprint_observer.py';argv=command(observer);timeout=budget.timeout()
  result=native.run_process(argv,cwd=root,env=dict(ENV),timeout=timeout,stdout=work/'stdout.log',stderr=work/'stderr.log',max_log_bytes=LOG_CAP,limits=dict(LIMITS),allow_new_sessions=False)
  try:safety(result,timeout);check() # No child output is read before cleanup/resource acceptance.
  except BaseException:
   durable(fd,'command.json',encoded({'argv':argv,'cwd':str(root),'env':ENV,'timeout_seconds':timeout,'nominal_timeout_seconds':120,'limits':LIMITS,'max_log_bytes':LOG_CAP,'native_result':result,'status':'REJECTED_BEFORE_OUTPUT_READ'}))
   raise
  out=read(work/'stdout.log',LOG_CAP,check);err=read(work/'stderr.log',LOG_CAP,check);need(len(out)+len(err)<=LOG_CAP and not err and out.endswith(b'\n') and len(out.splitlines())==1,'complete exact fingerprint output')
  observation=parse(out);profile=valid_profile(observation)
  record={'argv':argv,'cwd':str(root),'env':ENV,'timeout_seconds':timeout,'nominal_timeout_seconds':120,'limits':LIMITS,'max_log_bytes':LOG_CAP,'native_result':result,'stdout':pin(out),'stderr':pin(err)}
  durable(fd,'command.json',encoded(record));check()
  summary={'schema':'c087-python-fingerprint-observation-result-v1','status':'OBSERVED_UNAPPROVED','contract_sha256':contract_sha,'runtime_fingerprint_sha256':sha(encoded(profile)),'os_release_sha256':sha(os_release.encode()),'profile_approved':False,'fixtures_executed':False,'guard_modes_executed':False,'proof_pass_claimed':False}
  durable(fd,'result.json',encoded(summary));check()
  for rel,row in c['inputs'].items():need(pin(read(root/rel,128*1024,check))==row,'code changed after child')
  need((work.stat().st_dev,work.stat().st_ino)==owned and (parent.stat().st_dev,parent.stat().st_ino)==(st.st_dev,st.st_ino),'owned output identity')
  collection={n:pin(read(work/n,1024**2,check)) for n in ('stdout.log','stderr.log','command.json','result.json')}
  durable(fd,'collection.json',encoded({'schema':'c087-python-fingerprint-collection-v1','files':collection}));check()
  durable(fd,'completion.json',encoded({'schema':'c087-python-fingerprint-completion-v1','contract_sha256':contract_sha,'result_sha256':collection['result.json']['sha256'],'collection_sha256':sha(read(work/'collection.json',1024**2,check)),'profile_approved':False,'guard_modes_executed':False}));verify_ownership();check()
 except BaseException:
  try:
   os.unlink('completion.json',dir_fd=fd);os.fsync(fd)
  except FileNotFoundError:pass
  try:durable(fd,'incomplete.json',encoded({'status':'INCOMPLETE','profile_approved':False,'guard_modes_executed':False,'proof_pass_claimed':False}))
  except BaseException:pass
  raise
 finally:
  try:
   try:os.close(fd)
   finally:os.close(parentfd)
   verify_ownership();check()
  except BaseException:
   try:remove_completion_owned(work,owned)
   except BaseException:pass # Never follow an unowned alias during failure cleanup.
   raise

def main():
 budget=Budget() # Original clock starts before CLI parsing, hashes and setup.
 ap=argparse.ArgumentParser();ap.add_argument('--contract-sha256',required=True);ap.add_argument('--work',required=True);a=ap.parse_args();need(digest(a.contract_sha256),'contract digest')
 need(sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode,'isolated source-only controller')
 os.sched_setaffinity(0,{min(os.sched_getaffinity(0))});resource.setrlimit(resource.RLIMIT_AS,(GIB,GIB));resource.setrlimit(resource.RLIMIT_CPU,(180,180));resource.setrlimit(resource.RLIMIT_FSIZE,(16*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CORE,(0,0));resource.setrlimit(resource.RLIMIT_NOFILE,(64,64))
 execute(Path(__file__).resolve().parents[1],a.work,a.contract_sha256,budget)
if __name__=='__main__':main()
