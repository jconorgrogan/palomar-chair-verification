#!/usr/bin/python3
"""Observation only. Never imports fixtures, executes a child, or approves facts."""
import os,sys,time
START=time.monotonic()
def no_bytecode(event,args):
 if event=='open' and args and isinstance(args[0],(str,bytes,os.PathLike)) and os.fsdecode(args[0]).endswith(('.pyc','.pyo')):raise FileNotFoundError('bytecode refused')
sys.addaudithook(no_bytecode)
import argparse,hashlib,json,math,resource,stat
from datetime import datetime,timezone
from pathlib import Path
WALL=datetime.now(timezone.utc)
class Rejected(ValueError):pass
def need(ok,msg):
 if not ok:raise Rejected(msg)
def sha(raw):return hashlib.sha256(raw).hexdigest()
def encode(value):return (json.dumps(value,sort_keys=True,indent=2,allow_nan=False)+'\n').encode()
def parse(raw):
 def pairs(rows):
  out={}
  for key,value in rows:need(key not in out,'duplicate JSON key');out[key]=value
  return out
 return json.loads(raw,object_pairs_hook=pairs,parse_constant=lambda _:(_ for _ in ()).throw(Rejected('nonfinite JSON')))
def identity(st):return (st.st_dev,st.st_ino,st.st_mode,st.st_nlink,st.st_uid,st.st_gid,st.st_size,st.st_mtime_ns,st.st_ctime_ns)
class Budget:
 def __init__(self):self.last=START;self.lastwall=WALL;self.failed=False
 def check(self):
  if self.failed:raise Rejected('poisoned system observation budget')
  try:
   now=time.monotonic();wall=datetime.now(timezone.utc);need(type(now) in (int,float) and math.isfinite(now) and now>=self.last and now-START<30 and wall>=self.lastwall and (wall-WALL).total_seconds()<30,'original bounded system observation deadline');self.last=now;self.lastwall=wall
  except BaseException:self.failed=True;raise

def read(path,maximum,budget):
 budget.check();p=Path(path);need(p.is_absolute() and '..' not in p.parts and str(p)==str(path),'canonical absolute input')
 for item in (p,*p.parents):need(not item.is_symlink(),'no input aliases')
 before=p.lstat();fd=os.open(p,os.O_RDONLY|os.O_NOFOLLOW|os.O_CLOEXEC);data=bytearray()
 try:
  need(identity(os.fstat(fd))==identity(before) and stat.S_ISREG(before.st_mode) and before.st_nlink==1 and not before.st_mode&0o022 and 0<=before.st_size<=maximum,'bounded nonshared regular source')
  while True:
   budget.check();block=os.read(fd,min(65536,maximum+1-len(data)))
   if not block:break
   data.extend(block);need(len(data)<=maximum,'bounded complete source')
  need(identity(os.fstat(fd))==identity(before)==identity(p.lstat()),'unchanged source inode')
 finally:
  try:os.close(fd)
  finally:budget.check()
 return bytes(data),identity(before)

def alias_chain(invoked,budget):
 """Bounded component observations; no directory listing or runtime tree scan."""
 p=Path(invoked);need(p.is_absolute() and not str(p).startswith('//') and '..' not in p.parts and str(p)==str(invoked) and len(str(p))<=4096,'canonical invoked alias')
 pending=list(p.parts[1:]);settled=[];rows=[];links=0
 root=Path('/');st=root.lstat();need(stat.S_ISDIR(st.st_mode),'directory root');rows.append(('/',identity(st),None))
 while pending:
  budget.check();need(len(rows)<256 and len(pending)<=256,'bounded alias components');part=pending.pop(0)
  if part in ('','.'):continue
  if part=='..':
   if settled:settled.pop()
   continue
  q=Path('/').joinpath(*settled,part);need(len(str(q))<=4096,'bounded resolved alias');st=q.lstat();link=os.readlink(q) if stat.S_ISLNK(st.st_mode) else None
  need(identity(q.lstat())==identity(st),'stable alias component');rows.append((str(q),identity(st),link))
  if link is not None:
   links+=1;need(links<=40 and 0<len(link)<=4096,'bounded symlink chain');target=Path(link)
   if target.is_absolute():settled=[];parts=target.parts[1:]
   else:parts=target.parts
   if link.endswith(('/', '/.')):parts=tuple(parts)+('.',)
   pending=list(parts)+pending
  else:
   need(not pending or stat.S_ISDIR(st.st_mode),'directory alias parent');settled.append(part)
 real=Path('/').joinpath(*settled)
 for name,ident,link in rows:
  budget.check();q=Path(name);st=q.lstat();need(identity(st)==ident and (os.readlink(q) if stat.S_ISLNK(st.st_mode) else None)==link,'stable complete alias chain')
 budget.check();return real,tuple(rows)

def same_alias(invoked,saved,budget):
 need(alias_chain(invoked,budget)==saved,'final complete invoked alias chain');budget.check()

def collect(budget):
 records={};aliases={}
 def source(invoked,maximum):
  chain=alias_chain(invoked,budget);need(invoked not in ('/usr/bin/bwrap','/usr/bin/prlimit') or chain[0].is_relative_to('/usr'),'official system executable root before read');data,ident=read(chain[0],maximum,budget);same_alias(invoked,chain,budget);records[invoked]=(chain,data,ident,maximum);return chain[0],data
 ospath,raw=source('/etc/os-release',65536)
 fields=dict(line.split('=',1) for line in raw.decode().splitlines() if '=' in line);need(fields.get('ID','').strip('"')=='ubuntu' and fields.get('VERSION_ID','').strip('"')=='22.04','Ubuntu22 observation only')
 profile={'schema':'c087-approved-guard-system-profile-v1','os_release_sha256':sha(raw),'binaries':{},'mount_aliases':{}}
 for invoked in ('/usr/bin/bwrap','/usr/bin/prlimit'):
  path,data=source(invoked,8*1024**2);need(path.is_relative_to('/usr'),'official system executable root');profile['binaries'][invoked]={'realpath':str(path),'bytes':len(data),'sha256':sha(data)}
 for name in ('/usr','/bin','/lib','/lib64'):
  chain=alias_chain(name,budget);path=Path(name);st=path.lstat();kind='symlink' if stat.S_ISLNK(st.st_mode) else 'directory' if stat.S_ISDIR(st.st_mode) else 'invalid';need(kind!='invalid','system mount alias kind')
  profile['mount_aliases'][name]={'kind':kind,'realpath':str(chain[0]),'symlink_target':os.readlink(path) if kind=='symlink' else None};same_alias(name,chain,budget);aliases[name]=chain
 for invoked,(chain,data,ident,maximum) in records.items():
  same_alias(invoked,chain,budget);current,observed=read(chain[0],maximum,budget);need(current==data and observed==ident,'final system source rehash');same_alias(invoked,chain,budget)
 for invoked,(chain,data,ident,maximum) in records.items():same_alias(invoked,chain,budget)
 for name,chain in aliases.items():same_alias(name,chain,budget)
 budget.check();return profile

def interpreter_identity(selected,budget):
 need(type(selected) is dict and selected.get('schema')=='c087-interpreter-fingerprint-v1','separately approved Python selection required')
 invoked=alias_chain('/usr/bin/python3',budget);running=alias_chain(sys.executable,budget)
 need(running[0]==invoked[0],'same invoked production interpreter')
 real=invoked[0];raw,ident=read(real,64*1024**2,budget);same_alias('/usr/bin/python3',invoked,budget);same_alias(sys.executable,running,budget)
 observed={'invoked_path':'/usr/bin/python3','executable_realpath':str(real),'executable':{'bytes':len(raw),'sha256':sha(raw)},'sys_version':sys.version,'version_info':list(sys.version_info),'implementation':sys.implementation.name,'cache_tag':sys.implementation.cache_tag}
 def exact(a,b):
  need(type(a) is type(b),'strict selected identity type')
  if type(a) is dict:
   need(set(a)==set(b),'strict selected identity fields')
   for k in a:exact(a[k],b[k])
  elif type(a) is list:
   need(len(a)==len(b),'strict selected identity length')
   for x,y in zip(a,b):exact(x,y)
  else:need(a==b,'selected executable/version identity mismatch')
 for key in observed:exact(observed[key],selected.get(key))
 again,after=read(real,64*1024**2,budget);need(again==raw and after==ident,'final executable rehash');same_alias('/usr/bin/python3',invoked,budget);same_alias(sys.executable,running,budget)
 budget.check();return observed


def main():
 budget=Budget();ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--contract-sha256',required=True);a=ap.parse_args()
 need(sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode,'isolated source observer');os.sched_setaffinity(0,{min(os.sched_getaffinity(0))})
 resource.setrlimit(resource.RLIMIT_AS,(256*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(30,)*2);resource.setrlimit(resource.RLIMIT_FSIZE,(1024**2,)*2);resource.setrlimit(resource.RLIMIT_CORE,(0,0));resource.setrlimit(resource.RLIMIT_NOFILE,(32,32))
 root=Path(__file__).resolve().parents[1];raw,contract_id=read(root/'system-observation-contract.json',65536,budget);need(sha(raw)==a.contract_sha256,'exact separately reviewed system observation contract');c=parse(raw)
 need(type(c) is dict and set(c)=={'schema','review_status','observer','seconds','profile_approved','guard_modes_allowed','selected_python_profile','selected_python_profile_sha256'} and c['schema']=='c087-guard-system-observation-contract-v1' and c['review_status']=='reviewed_for_observation' and type(c['seconds']) is int and c['seconds']==30 and c['profile_approved'] is False and c['guard_modes_allowed'] is False,'closed observation-only contract')
 need(type(c['selected_python_profile']) is dict and c['selected_python_profile_sha256']==sha(encode(c['selected_python_profile'])),'exact separately selected Python profile digest')
 source,source_id=read(Path(__file__).resolve(),65536,budget);need(c['observer']=={'bytes':len(source),'sha256':sha(source)},'source pin')
 interpreter=interpreter_identity(c['selected_python_profile'],budget)
 observed=collect(budget)
 need(interpreter_identity(c['selected_python_profile'],budget)==interpreter,'same interpreter through system observation')
 again,ident=read(Path(__file__).resolve(),65536,budget);need(again==source and ident==source_id,'observer final rehash');again,ident=read(root/'system-observation-contract.json',65536,budget);need(again==raw and ident==contract_id,'contract final rehash')
 value={'schema':'c087-unapproved-guard-system-observation-v1','contract_sha256':a.contract_sha256,'selected_python_profile_sha256':c['selected_python_profile_sha256'],'observed_interpreter':interpreter,'selected_python_executable_and_version_match':True,'full_python_fingerprint_rechecked':False,'system_profile':observed,'system_profile_sha256':sha(encode(observed)),'profile_approved':False,'guard_modes_executed':False,'subprocess_executed':False,'runtime_installed':False,'proof_pass_claimed':False}
 line=json.dumps(value,sort_keys=True,allow_nan=False)+'\n';need(len(line.encode())<=1024**2,'bounded single observation');budget.check();print(line,end='',flush=True);budget.check()
if __name__=='__main__':main()
