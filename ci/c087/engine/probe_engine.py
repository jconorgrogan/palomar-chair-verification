"""Inactive fixed C087 command sequence. Parent invocation authority is external.

This component never authenticates a downloaded receipt or grants permission to
execute. The separately reviewed parent must own the just-completed admission
child, one-shot capability, exact input/code pins and absolute job deadline.
The production entrypoint stays disabled until that composition is sealed.
"""
from __future__ import annotations
import copy, hashlib, json, math, os, stat, time
from pathlib import Path
import probe_policy as policy
import original_probe_commands as base

GIB=1024**3
TARGET=policy.TARGET
SUFFIXES=policy.SUFFIXES
SOURCE_SHA='5f93adcd7af879789a03ff03b37f500f16545d21a26fbdade911551bfde42f2f'
PROFILE_BYTES=512*1024**2
PREDECESSOR_COMPANIONS=6218*6
CONTROL_SHA='8242c078f3a61c8968c4929e0275ff2fb6bfee26be03f2f86594693bbe3ed5dc'
HELPER_FILES={'AuditC087Raw.lean': {'bytes': 2013, 'sha256': '0347bae8f298608ed8a0e9d2ee89466c1509a56d0550768b09a994741fd49dce'}, 'C087NegativeControls.lean': {'bytes': 7073, 'sha256': '8c058c63f822dcebb7e77baba0fc2a59aa19bbba4b3df0a339e4918db81ae27d'}, 'C087RawContract.lean': {'bytes': 8397, 'sha256': '061b0c9c608eec98f31b6e7c12a58046a56453042211b0ffe93b05f2a9dcc636'}, 'C087SourceShapeControl.lean': {'bytes': 2836, 'sha256': '78f693315b050d126fc472941eee2f398d208bfdc101fc62658e615fb2942a10'}, 'DefaultOptionControl.lean': {'bytes': 766, 'sha256': '1f374ac965af4025fcf757f1d666eb239cc726477a5cb79bd61a540e14bde4a6'}, 'DisabledOptionControl.lean': {'bytes': 773, 'sha256': '3d4f5734ae2a49d98347722fb2b4bcae570adddcd6c3481152acf726ea6a17ec'}}
AGGREGATE_LOG_BYTES=18*16*1024**2
class Rejected(ValueError):pass

def need(ok,message):
 if not ok:raise Rejected(message)
def jb(value):return (json.dumps(value,sort_keys=True,indent=2,allow_nan=False)+'\n').encode()
def digest(raw):return hashlib.sha256(raw).hexdigest()
def pinned_file(path):
 path=Path(path)
 for p in (path,*path.parents):need(not p.is_symlink(),'symlink path')
 fd=os.open(path,os.O_RDONLY|os.O_NOFOLLOW)
 try:
  before=os.fstat(fd);need(stat.S_ISREG(before.st_mode) and before.st_nlink==1,'regular unshared file required')
  h=hashlib.sha256();n=0
  while block:=os.read(fd,1024**2):h.update(block);n+=len(block)
  after=os.fstat(fd)
  need((before.st_dev,before.st_ino,before.st_size,before.st_mtime_ns,before.st_ctime_ns)==(after.st_dev,after.st_ino,after.st_size,after.st_mtime_ns,after.st_ctime_ns) and n==before.st_size,'file changed during hash')
  return {'bytes':n,'sha256':h.hexdigest()}
 finally:os.close(fd)
def tree(root, *, byte_limit=4*GIB, entry_limit=100000):
 root=Path(root);need(root.is_dir() and not root.is_symlink(),'tree root required')
 files={};dirs=set();total=0;entries=0
 for parent,ds,fs in os.walk(root,followlinks=False):
  for n in ds:
   entries+=1;need(entries<=entry_limit,'bounded tree capacity exceeded')
   p=Path(parent)/n;need(p.is_dir() and not p.is_symlink(),'tree directory alias');dirs.add(p.relative_to(root).as_posix())
  for n in fs:
   entries+=1;need(entries<=entry_limit,'bounded tree capacity exceeded')
   p=Path(parent)/n;st=p.lstat();need(stat.S_ISREG(st.st_mode) and st.st_nlink==1,'tree regular unshared file required');total+=st.st_size
   need(total<=byte_limit,'bounded tree capacity exceeded');files[p.relative_to(root).as_posix()]=pinned_file(p)
 return files,dirs

def retained_tree(root, *, byte_limit=4*GIB):
 files,dirs=tree(root,byte_limit=byte_limit);metadata={}
 for name in ['.',*sorted(dirs),*sorted(files)]:
  p=Path(root) if name=='.' else Path(root)/name;st=p.lstat()
  metadata[name]={'dev':st.st_dev,'ino':st.st_ino,'mode':st.st_mode,'nlink':st.st_nlink,
   'uid':st.st_uid,'gid':st.st_gid,'size':st.st_size,'mtime_ns':st.st_mtime_ns,'ctime_ns':st.st_ctime_ns}
 return {'files':files,'directories':sorted(dirs),'inodes':metadata}

def durable_new(path,value):
 raw=jb(value);path=Path(path)
 fd=os.open(path,os.O_WRONLY|os.O_CREAT|os.O_EXCL|os.O_NOFOLLOW,0o600)
 try:
  view=memoryview(raw)
  while view:
   n=os.write(fd,view);need(n>0,'short durable write');view=view[n:]
  os.fsync(fd)
 finally:os.close(fd)
 dfd=os.open(path.parent,os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW)
 try:os.fsync(dfd)
 finally:os.close(dfd)
 return digest(raw)

def _original_ab_command_plan(native, *, source_root,toolchain_root,predecessor_objects,helper_root,diagnostic_output):
 source_root=base.canonical(str(source_root));toolchain_root=base.canonical(str(toolchain_root))
 predecessor_objects=base.canonical(str(predecessor_objects));helper_root=base.canonical(str(helper_root));diagnostic_output=base.canonical(str(diagnostic_output))
 roots=list(map(Path,(source_root,toolchain_root,predecessor_objects,helper_root,diagnostic_output)))
 need(all(a!=b and a not in b.parents and b not in a.parents for i,a in enumerate(roots) for b in roots[i+1:]),'all engine roots must be disjoint')
 args=dict(source_root=source_root,toolchain_root=toolchain_root,helper_root=helper_root,helper_workspace=diagnostic_output+'/helpers')
 a=base.plan(native,stage_workspace=diagnostic_output+'/default',**args)
 b=base.plan(native,stage_workspace=diagnostic_output+'/async_off',**args)
 need(a[:12]==b[:12] and len(a)==len(b)==18,'fixed helper prefix changed')
 rows=copy.deepcopy(a[:15]+b[15:])
 for row in rows[12:]:
  argv=row['argv'];layout=row['sandbox'];i=argv.index('--chdir')
  argv[i:i]=['--ro-bind',predecessor_objects,predecessor_objects]
  i=argv.index('LEAN_PATH');paths=argv[i+1].split(':')
  need(paths[-1]==toolchain_root+'/lib/lean','runtime search path changed')
  paths.insert(len(paths)-1,predecessor_objects);value=':'.join(paths);argv[i+1]=value
  layout['readonly_roots'].append(predecessor_objects);layout['environment']['LEAN_PATH']=value
  if row['phase'] in ('check','audit'):
   replacement=with_import_view(row,Path(diagnostic_output)/'receipts'/(_root(row).name+'-imports'));row.clear();row.update(replacement)
 return rows

def command_plan(native,**kwargs):
 """Fixed async-off research plan with a bounded raw-auditor interpreter budget."""
 rows=_original_ab_command_plan(native,**kwargs)
 rows=rows[:12]+rows[15:]
 audit=rows[-1];inner=audit['inner_argv'];start=audit['argv'].index('--')+1
 expected=[base.canonical(str(kwargs['toolchain_root']))+'/bin/lean','-j1','-M768','--run',base.canonical(str(kwargs['helper_root']))+'/AuditC087Raw.lean']
 need(audit['name']=='audit-target-async_off' and audit['phase']=='audit' and inner==expected and audit['argv'][start:]==expected,'fixed research auditor command changed')
 inner[2]='-M4096';audit['argv'][start+2]='-M4096'
 return rows


def _view_identity(st):
 return (st.st_dev,st.st_ino,st.st_mode,st.st_uid,st.st_gid,st.st_nlink,st.st_size,st.st_mtime_ns,st.st_ctime_ns)

def _view_stable(st):return _view_identity(st)[:5]

def _view_plan(predecessor_root,target_root,predecessors,target):
 predecessor_root=Path(base.canonical(str(predecessor_root)));target_root=Path(base.canonical(str(target_root)))
 need(predecessor_root!=target_root and predecessor_root not in target_root.parents and target_root not in predecessor_root.parents,'import view backing roots overlap')
 need(type(predecessors) is dict and type(target) is dict and not (set(predecessors)&set(target)),'import view provider collision')
 bindings={};directories=set()
 for provider,root,rows in (('predecessor',predecessor_root,predecessors),('target',target_root,target)):
  need(root.is_dir() and not root.is_symlink(),'import view backing root required')
  for name,pin in sorted(rows.items()):
   need(type(name) is str and 0<len(name)<=1024 and '\\' not in name and '\x00' not in name,'import view relative path')
   rel=Path(name);need(not rel.is_absolute() and str(rel)==name and len(rel.parts)<=32 and all(x not in ('','.','..') for x in rel.parts),'import view relative path')
   need(type(pin) is dict and set(pin)=={'bytes','sha256'} and type(pin['bytes']) is int and 0<pin['bytes']<=PROFILE_BYTES and type(pin['sha256']) is str and len(pin['sha256'])==64 and all(x in '0123456789abcdef' for x in pin['sha256']),'import view pinned companion')
   bindings[name]={'provider':provider,'target':str(root/rel),'bytes':pin['bytes'],'sha256':pin['sha256']}
   directories.update(p.as_posix() for p in rel.parents if p.as_posix()!='.')
 need(0<len(bindings)<=PREDECESSOR_COMPANIONS+len(SUFFIXES) and len(directories)<=100000 and not (set(bindings)&directories),'import view bounded exact namespace')
 return bindings,directories

def _view_close_all(*fds):
 error=None
 for fd in fds:
  if fd is not None:
   try:os.close(fd)
   except BaseException as caught:
    if error is None:error=caught
 if error is not None:raise Rejected('import view descriptor close failed') from error

def _view_directory(rootfd,parts):
 flags=os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW;fds=[]
 try:
  fds.append(os.dup(rootfd))
  for part in parts:fds.append(os.open(part,flags,dir_fd=fds[-1]))
 except BaseException:
  _view_close_all(*reversed(fds));raise
 result=fds.pop()
 try:_view_close_all(*reversed(fds))
 except BaseException:
  _view_close_all(result);raise
 return result

def create_import_view(root,predecessor_root,target_root,predecessors,target,remaining):
 """Owned ephemeral input only: exact symlinks, no copied or hardlinked bytes."""
 root=Path(base.canonical(str(root)));policy.effective_timeout(120,remaining())
 bindings,dirs=_view_plan(predecessor_root,target_root,predecessors,target)
 backing_roots={str(path):_view_identity(Path(path).lstat()) for path in (predecessor_root,target_root)}
 need(not root.exists() and not root.is_symlink() and root.parent.is_dir() and not root.parent.is_symlink(),'fresh import view required')
 fs=os.statvfs(root.parent);unit=max(fs.f_frsize,4096)
 need(fs.f_bavail*fs.f_frsize>=(len(bindings)+len(dirs)+2)*unit+512*1024**2 and fs.f_favail>=len(bindings)+len(dirs)+4096,'measured import view link capacity')
 parent_identity=_view_stable(root.parent.lstat());flags=os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW
 parentfd=os.open(root.parent,flags);rootfd=None
 try:
  need(_view_stable(os.fstat(parentfd))==parent_identity,'import view parent changed')
  os.mkdir(root.name,mode=0o700,dir_fd=parentfd);created=_view_identity(os.stat(root.name,dir_fd=parentfd,follow_symlinks=False))
  rootfd=os.open(root.name,flags,dir_fd=parentfd);need(_view_identity(os.fstat(rootfd))==created,'import view root changed')
  for name in sorted(dirs,key=lambda x:(len(Path(x).parts),x)):
   rel=Path(name);fd=_view_directory(rootfd,rel.parts[:-1])
   try:os.mkdir(rel.name,mode=0o700,dir_fd=fd)
   finally:_view_close_all(fd)
  for index,(name,row) in enumerate(bindings.items()):
   if index%128==0:policy.effective_timeout(120,remaining())
   rel=Path(name);fd=_view_directory(rootfd,rel.parts[:-1])
   try:os.symlink(row['target'],rel.name,dir_fd=fd)
   finally:_view_close_all(fd)
  identities={'':_view_identity(os.fstat(rootfd))}
  for name in [*sorted(dirs),*sorted(bindings)]:identities[name]=_view_identity(os.stat(name,dir_fd=rootfd,follow_symlinks=False))
 finally:_view_close_all(rootfd,parentfd)
 view={'root':root,'bindings':bindings,'directories':dirs,'identities':identities,'parent_identity':parent_identity,'backing_roots':backing_roots,'map_sha256':digest(jb(bindings))}
 verify_import_view(view,remaining);return view

def verify_import_view(view,remaining):
 root=view['root'];policy.effective_timeout(120,remaining())
 for path,identity in view['backing_roots'].items():need(_view_identity(Path(path).lstat())==identity,'import view backing root changed')
 need(_view_stable(root.parent.lstat())==view['parent_identity'],'import view parent changed')
 files=set();dirs=set();count=0;flags=os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW
 def walk(fd,prefix):
  nonlocal count
  with os.scandir(fd) as entries:
   for entry in entries:
    count+=1;policy.effective_timeout(120,remaining())
    name=prefix+entry.name
    need(count<=len(view['bindings'])+len(view['directories']) and name not in files and name not in dirs and (name in view['bindings'] or name in view['directories']),'import view exact membership changed')
    st=os.stat(entry.name,dir_fd=fd,follow_symlinks=False)
    need(_view_identity(st)==view['identities'][name],'import view inode changed')
    if name in view['directories']:
     need(stat.S_ISDIR(st.st_mode) and st.st_uid==os.getuid() and not st.st_mode&0o077,'import view directory type/owner');dirs.add(name)
     child=os.open(entry.name,flags,dir_fd=fd)
     try:
      need(_view_identity(os.fstat(child))==view['identities'][name],'import view inode changed');walk(child,name+'/')
     finally:_view_close_all(child)
    else:
     need(stat.S_ISLNK(st.st_mode) and st.st_uid==os.getuid() and os.readlink(entry.name,dir_fd=fd)==view['bindings'][name]['target'],'import view link binding changed');files.add(name)
 rootfd=os.open(root,flags)
 try:
  need(_view_identity(os.fstat(rootfd))==view['identities'][''],'import view root changed');walk(rootfd,'')
  need(files==set(view['bindings']) and dirs==view['directories'],'import view exact membership changed')
  need(_view_identity(os.fstat(rootfd))==view['identities'][''],'import view root changed')
 finally:_view_close_all(rootfd)
 need(_view_stable(root.parent.lstat())==view['parent_identity'] and _view_identity(root.lstat())==view['identities'][''],'import view root changed')
 # No descriptor remains: bind every retained name again after the last close.
 for index,name in enumerate([*sorted(view['directories'],key=lambda x:(len(Path(x).parts),x)),*sorted(view['bindings'])]):
  if index%128==0:policy.effective_timeout(120,remaining())
  path=root/name;need(_view_identity(path.lstat())==view['identities'][name],'import view inode changed')
  if name in view['bindings']:need(os.readlink(path)==view['bindings'][name]['target'],'import view link binding changed')
 for path,identity in view['backing_roots'].items():need(_view_identity(Path(path).lstat())==identity,'import view backing root changed')
 policy.effective_timeout(120,remaining())

def close_import_view(view,remaining):
 """Remove only verified owned entries through no-follow directory descriptors."""
 verify_import_view(view,remaining);root=view['root'];flags=os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW
 parentfd=os.open(root.parent,flags);rootfd=None

 try:
  need(_view_stable(os.fstat(parentfd))==view['parent_identity'],'import view cleanup parent changed')
  rootfd=os.open(root.name,flags,dir_fd=parentfd);need(_view_identity(os.fstat(rootfd))==view['identities'][''],'import view cleanup root changed')
  for index,name in enumerate(sorted(view['bindings'])):
   if index%128==0:policy.effective_timeout(120,remaining())
   rel=Path(name);fd=_view_directory(rootfd,rel.parts[:-1])
   try:
    need(_view_identity(os.stat(rel.name,dir_fd=fd,follow_symlinks=False))==view['identities'][name] and os.readlink(rel.name,dir_fd=fd)==view['bindings'][name]['target'],'import view cleanup link changed')
    os.unlink(rel.name,dir_fd=fd)
   finally:_view_close_all(fd)
  for name in sorted(view['directories'],key=lambda x:(len(Path(x).parts),x),reverse=True):
   rel=Path(name);fd=_view_directory(rootfd,rel.parts[:-1])
   try:
    need(_view_stable(os.stat(rel.name,dir_fd=fd,follow_symlinks=False))==view['identities'][name][:5],'import view cleanup directory changed')
    os.rmdir(rel.name,dir_fd=fd)
   finally:_view_close_all(fd)
  need(not os.listdir(rootfd) and _view_stable(os.stat(root.name,dir_fd=parentfd,follow_symlinks=False))==view['identities'][''][:5],'import view cleanup root changed')
  _view_close_all(rootfd);rootfd=None;os.rmdir(root.name,dir_fd=parentfd)
 finally:_view_close_all(rootfd,parentfd)
 need(_view_stable(root.parent.lstat())==view['parent_identity'] and not root.exists() and not root.is_symlink(),'import view cleanup final binding')
 policy.effective_timeout(120,remaining())

def with_import_view(row,view_root):
 """View first; retain backing roots for leanchecker's realPath module lookup."""
 row=copy.deepcopy(row);argv=row['argv'];layout=row['sandbox'];view=str(view_root)
 i=argv.index('--chdir');argv[i:i]=['--ro-bind',view,view]
 i=argv.index('LEAN_PATH');paths=argv[i+1].split(':');need(view not in paths,'duplicate import view search path')
 argv[i+1]=':'.join([view,*paths]);layout['environment']['LEAN_PATH']=argv[i+1];layout['readonly_roots'].append(view)
 return row

class _PromotionWorkspace:
 """Explicit non-authoritative receiver for the unchanged native file mover only."""
 def __init__(self,root):
  self.workspace=Path(root);self.contract={'output_suffixes':list(SUFFIXES)}

def workspace(root):
 root=Path(root);need(not root.exists(),'workspace must be fresh');root.mkdir(mode=0o700)
 for name in ('objects','scratch','logs','module-quarantine'):(root/name).mkdir(mode=0o700)
 for name in ('home','tmp'):(root/'scratch'/name).mkdir(mode=0o700)
 return root

def _module(row):
 inner=row['inner_argv']
 if row['phase']=='compile':return Path(inner[inner.index('-o')+1]).relative_to(Path(row['sandbox']['writable_roots'][-1])/'objects').as_posix().removesuffix('.olean').replace('/','.')
 return TARGET if row['phase']=='audit' else inner[-1]

def _root(row):
 return Path(row['sandbox']['environment']['HOME']).parents[1]

def _read_log(path,maximum):
 row=pinned_file(path);need(row['bytes']<=maximum,'log exceeds bound')
 raw=Path(path).read_bytes();need({'bytes':len(raw),'sha256':digest(raw)}==row,'log changed after hashing');return raw

def prevalidate_native_exit(result, effective):
 # Reject unsafe cleanup/session/resource outcomes before opening any child file.
 need(type(result) is dict and set(result)==policy.NATIVE_RESULT_KEYS,'native result shape')
 need(result.get('new_sessions_explicitly_allowed') is False,'native session policy')
 need(type(result.get('cleanup_bound_seconds')) in (int,float) and math.isfinite(result['cleanup_bound_seconds']) and result['cleanup_bound_seconds']==3.0,'native cleanup bound')
 need(type(result.get('cleanup_elapsed_seconds')) in (int,float) and math.isfinite(result['cleanup_elapsed_seconds']) and 0<=result['cleanup_elapsed_seconds']<=3.0,'native cleanup elapsed')
 need(type(result.get('peak_sampled_tree_rss_bytes')) is int and 0<=result['peak_sampled_tree_rss_bytes']<=policy.LIMITS['rss_tree_bytes'],'native resource observation')
 policy.safety({**result,'timeout_seconds':effective})

def run_probe(*args,**kwargs):
 raise Rejected('production capability/controller binding is not yet sealed')

def _run_fixed_sequence(native, *, source_root,toolchain_root,predecessor_objects,helper_root,diagnostic_output,
                         predecessor_files,control_expectations,remaining,verify_inputs,executor,initial_files=None,observe_native=None):
 """Private integration/test seam. Only a sealed parent may bind real execution."""
 out=Path(diagnostic_output);initial_files={} if initial_files is None else copy.deepcopy(initial_files)
 need(set(initial_files)<= {'engine-invocation.json'},'unapproved initial engine file')
 need(out.is_dir() and not out.is_symlink() and tree(out)==(initial_files,set()),'exclusive registered diagnostic output required')
 rows=command_plan(native,source_root=source_root,toolchain_root=toolchain_root,predecessor_objects=predecessor_objects,helper_root=helper_root,diagnostic_output=out)
 need(pinned_file(Path(source_root)/(TARGET.replace('.','/')+'.lean'))=={'bytes':837,'sha256':SOURCE_SHA},'exact target source required')
 expected_predecessors=copy.deepcopy(predecessor_files)
 need(type(expected_predecessors) is dict and len(expected_predecessors)==PREDECESSOR_COMPANIONS,'exact admitted companion count required')
 need(not any(p.startswith(TARGET.replace('.','/')+'.') for p in expected_predecessors),'target must not occur in predecessor namespace')
 need(tree(predecessor_objects)[0]==expected_predecessors,'predecessor content map differs')
 verify_inputs();policy.effective_timeout(120,remaining())
 control_names={'C087NegativeControls':'negative','C087SourceShapeControl':'shape','DefaultOptionControl':'default','DisabledOptionControl':'disabled'}
 need(set(control_expectations)==set(control_names.values()) and digest(jb(control_expectations))==CONTROL_SHA,'fixed control expectations required')
 need(tree(helper_root)[0]==HELPER_FILES,'fixed helper source bytes required')
 for root in dict.fromkeys(_root(r) for r in rows):workspace(root)
 (out/'receipts').mkdir(mode=0o700)
 records=[];frozen={};completed_profiles={};outputs={};audits={};classes={};logs_total=0;import_views={}
 def check_frozen():
  need(all(pinned_file(out/name)==row for name,row in initial_files.items()),'parent engine invocation changed')
  verify_inputs();policy.effective_timeout(120,remaining())
  need(tree(predecessor_objects)[0]==expected_predecessors,'admitted predecessors changed')
  for root,expected in frozen.items():
   actual,dirs=tree(root/'objects');allowed={p.as_posix() for name in expected for p in Path(name).parents if p.as_posix()!='.'}
   need(actual==expected and dirs==allowed,'committed diagnostic output changed')
  for view in import_views.values():verify_import_view(view,remaining)
  for root,expected in completed_profiles.items():need(retained_tree(root)==expected,'retained complete profile changed')
  for root in frozen:
   need(not (set(frozen[root]) & set(expected_predecessors)),'diagnostic/predecessor provider collision')
  policy.effective_timeout(120,remaining())
 def execute(row):
  nonlocal logs_total
  check_frozen();root=_root(row);module=_module(row)
  if row['phase']=='compile':
   quarantine=root/'module-quarantine'/module
   need(not quarantine.exists(),'compile quarantine already exists')
   (quarantine/'objects'/module.replace('.','/')).parent.mkdir(parents=True,mode=0o700)
  for path in row['sandbox']['readonly_roots']+row['sandbox']['writable_roots']:
   native.no_symlink_path(Path(path));need(Path(path).is_dir(),'sandbox mount absent')
  effective=policy.effective_timeout(120,remaining())
  stdout=root/'logs'/(row['name']+'.stdout');stderr=root/'logs'/(row['name']+'.stderr')
  need(not stdout.exists() and not stderr.exists(),'command logs already exist')
  result=executor(row['argv'],cwd=Path(row['sandbox']['cwd']),env=row['sandbox']['environment'],timeout=effective,
    stdout=stdout,stderr=stderr,max_log_bytes=row['max_log_bytes'],limits=row['resource_limits'],allow_new_sessions=False)
  if observe_native is not None:observe_native(rows.index(row),effective,result)
  prevalidate_native_exit(result,effective);policy.effective_timeout(120,remaining())
  rawout=_read_log(stdout,row['max_log_bytes']);rawerr=_read_log(stderr,row['max_log_bytes']);logs_total+=len(rawout)+len(rawerr)
  need(logs_total<=AGGREGATE_LOG_BYTES,'aggregate complete logs exceeded')
  record={'spec':row,'effective_timeout_seconds':effective,'result':result,'stdout':{'bytes':len(rawout),'sha256':digest(rawout)},'stderr':{'bytes':len(rawerr),'sha256':digest(rawerr)}}
  durable_new(out/'receipts'/('%02d-%s.json'%(len(records),row['name'])),record)
  records.append(record)
  actual=policy.validate_live_command(row,record,rawout,rawerr,expected_effective_timeout=effective)
  policy.effective_timeout(120,remaining());check_frozen()
  return {**actual,'timeout_seconds':effective},rawout,rawerr
 try:
  for row in rows[:12]:
   result,stdout,stderr=execute(row);policy.require_success(result);need(stderr==b'','successful helper stderr must be empty')
   root=_root(row);module=_module(row)
   if row['phase']=='compile':
    if module in control_names:
     expected=control_expectations[control_names[module]]
     need(expected['module']==module and stdout.decode('utf-8').splitlines()==expected['exact_stdout_lines'],'control output changed')
    else:need(stdout==b'','unexpected helper compile stdout')
    before,total=native.StageRunner.promote_quarantine(_PromotionWorkspace(root),module,PROFILE_BYTES-sum(x['bytes'] for x in frozen.get(root,{}).values()))
    owned={name.removeprefix('objects/'):pinned_file(root/name) for name in before}
    policy.validate_output_map(module,{'objects/'+k:v for k,v in owned.items()})
    outputs.setdefault(str(root),{}).update(owned);frozen[root]=copy.deepcopy(outputs[str(root)])
   else:need(stdout==b'','unexpected helper checker stdout')
   check_frozen()
  for label,offset in (('async_off',12),):
   compile_row,check_row,audit_row=rows[offset:offset+3]
   result,stdout,stderr=execute(compile_row);classification=policy.classify_compile(label,result,stdout,stderr);classes[label]=classification
   root=_root(compile_row)
   before,total=native.StageRunner.promote_quarantine(_PromotionWorkspace(root),TARGET,PROFILE_BYTES)
   own={name.removeprefix('objects/'):pinned_file(root/name) for name in before};policy.validate_output_map(TARGET,{'objects/'+k:v for k,v in own.items()})
   outputs[str(root)]=own;frozen[root]=copy.deepcopy(own)
   check_frozen();view=create_import_view(out/'receipts'/(label+'-imports'),predecessor_objects,root/'objects',expected_predecessors,own,remaining);import_views[label]=view
   durable_new(out/'receipts'/(label+'-import-view.json'),{'schema':'c087-fixed-import-view-v1','map_sha256':view['map_sha256'],'companion_count':len(view['bindings']),'predecessor_count':len(expected_predecessors),'target_count':len(own),'payload_bytes_copied':0,'checked':False})
   check,stdout,stderr=execute(check_row);policy.require_success(check);need(stdout==stderr==b'','unexpected target checker output')
   audit,stdout,stderr=execute(audit_row);policy.require_success(audit);need(stderr==b'','raw auditor stderr')
   audits[label]=stdout;policy.parse_audit(stdout);check_frozen()
   close_import_view(view,remaining);del import_views[label];check_frozen()
   durable_new(out/'receipts'/(label+'-accepted.json'),{'profile':label,'outputs':own,'audit_sha256':digest(stdout),'checked':True,'exact_raw_audit':True,'proof_pass_claimed':False})
   completed_profiles[root]=retained_tree(root);check_frozen()
  need('async_off' in audits,'async-off audit missing')
  check_frozen();result={'schema':'c087-bounded-async-off-diagnostic-v1','status':'required_async_off_outcome_validated','selected_mode':'async_off_only','default_target_attempted':False,'commands':records,'profile_classifications':classes,'outputs':outputs,'audit_rows':{k:policy.parse_audit(v) for k,v in audits.items()},'comparison_to_historical_default_claimed':False,'original_source_sha256':SOURCE_SHA,'predecessor_companion_count':len(expected_predecessors),'proof_pass_claimed':False,'native_build087_artifact_claimed':False,'parent_acceptance_pending':True}
  durable_new(out/'RESULT.json',result);check_frozen();return result
 except BaseException:
  # Never delete a preexisting or partially produced tree and never accept a
  # repaired retry. The enclosing one-shot parent must poison its capability.
  raise

ENGINE_DIRS=('helpers','helpers-control-C087NegativeControls','helpers-control-C087SourceShapeControl',
 'helpers-control-DefaultOptionControl','helpers-control-DisabledOptionControl','async_off','receipts')

def engine(context):
 """Fixed in-process consumer. It is usable only through the reviewed parent factory.

 The context is an unforgeable-in-that-factory closure binding, not serialized
 authority. This function alone never turns a report/directory into permission.
 """
 import types
 manifest=policy.json.loads(context.manifest_bytes,object_pairs_hook=_unique_pairs,
   parse_constant=lambda _:(_ for _ in ()).throw(Rejected('nonfinite engine manifest')))
 need(type(manifest) is dict and set(manifest)=={'schema','native_source_path','native_source_sha256',
  'source_root','toolchain_root','helper_root','predecessor_objects','diagnostic_output',
  'predecessor_files','control_expectations','code_pins'},'fixed engine manifest schema')
 need(manifest['schema']=='c087-fixed-engine-manifest-v1' and digest(context.manifest_bytes)==context.manifest_sha256,'fixed engine manifest binding')
 roots=dict(context.input_roots)
 for name,field in [('research_source','source_root'),('official_runtime','toolchain_root'),('helper_source','helper_root')]:
  need(name in roots and roots[name]==manifest[field],'engine input root binding')
 need(manifest['predecessor_objects']==context.admitted_objects and manifest['diagnostic_output']==context.diagnostic_output,'engine retained/output root binding')
 need(manifest['native_source_path']==str(Path(roots['latest_pipeline'])/'ci/fresh_stage.py') and manifest['native_source_sha256']==base.NATIVE_SHA,'fixed native source identity')
 code=Path(__file__).resolve().parent
 need(set(manifest['code_pins'])=={'probe_engine.py','probe_policy.py','original_probe_commands.py'},'fixed engine dependency set')
 need(Path(policy.__file__).resolve()==code/'probe_policy.py' and Path(base.__file__).resolve()==code/'original_probe_commands.py','engine dependency import path')
 def pins():
  context.checkpoint()
  for name,row in manifest['code_pins'].items():need(pinned_file(code/name)==row,'engine source dependency changed')
  need(pinned_file(manifest['native_source_path'])['sha256']==base.NATIVE_SHA,'native executor source changed')
  return context.checkpoint()
 pins()
 invocation=Path(context.diagnostic_output)/'engine-invocation.json'
 need(pinned_file(invocation)['sha256']==context.engine_invocation_sha256,'parent engine invocation binding')
 raw=Path(manifest['native_source_path']).read_bytes();need(digest(raw)==base.NATIVE_SHA,'native executor read changed')
 native=types.ModuleType('c087_engine_fixed_native');native.__file__=manifest['native_source_path']
 # Execute the exact just-authenticated buffer, bypassing all bytecode caches.
 exec(compile(raw,native.__file__,'exec'),native.__dict__)
 result=_run_fixed_sequence(native,source_root=manifest['source_root'],toolchain_root=manifest['toolchain_root'],
  predecessor_objects=manifest['predecessor_objects'],helper_root=manifest['helper_root'],diagnostic_output=manifest['diagnostic_output'],
  predecessor_files=manifest['predecessor_files'],control_expectations=manifest['control_expectations'],
  remaining=context.checkpoint,verify_inputs=pins,executor=native.run_process,
  initial_files={'engine-invocation.json':pinned_file(Path(context.diagnostic_output)/'engine-invocation.json')},observe_native=context.observe_native)
 pins();files,dirs=tree(context.diagnostic_output)
 need(set(p.split('/')[0] for p in files)==set(ENGINE_DIRS)|{'RESULT.json','engine-invocation.json'},'diagnostic output top-level files differ')
 need(all(p.split('/')[0] in ENGINE_DIRS for p in dirs),'diagnostic output directory differs')
 need(files['RESULT.json']['sha256']==digest(jb(result)),'fixed engine RESULT changed')
 response={'schema':'c087-fixed-engine-result-v2','status':'diagnostic_complete','selected_mode':'async_off_only','default_target_attempted':False,'session_nonce':context.nonce,
  'deadline_monotonic':context.deadline_monotonic,'engine_manifest_sha256':context.manifest_sha256,
  'result_sha256':files['RESULT.json']['sha256'],'proof_pass_claimed':False,'output_files':{k:v for k,v in files.items() if k!='engine-invocation.json'}}
 pins();return response

def _unique_pairs(rows):
 out={}
 for key,value in rows:need(key not in out,'duplicate engine JSON key');out[key]=value
 return out

LOOKUP_FIXTURE_FILES={'C087SerializedFixture/Model.lean': {'bytes': 910, 'sha256': '4378210e049bd2488ba176995ca79305a2de4b6e8894b4bac8edbc2cb1de96e6'}, 'SpectreFinite/RadiusFiveCertified.lean': {'bytes': 416, 'sha256': 'a56e08cab450bd4c3ebb51a954ef8738598cfc1b837bd34db54eef3cb4c57c7d'}, 'SpectreFinite/RadiusFivePruningCertified.lean': {'bytes': 1021, 'sha256': '4216e599b4f7c5fc9384da88c0498620e78ee115e1fd295f8b0a01e038baae5d'}, 'SpectreFinite/RadiusFivePruningRounds.lean': {'bytes': 512, 'sha256': '2073b2239828117313062ef8584b76c45740986fb582e432bee195ef9f736083'}}

def lookup_preflight_plan(native,*,fixture_root,toolchain_root,helper_root,work):
 work=Path(work);pred=work/'predecessors'
 rows=_original_ab_command_plan(native,source_root=fixture_root,toolchain_root=toolchain_root,predecessor_objects=pred/'objects',helper_root=helper_root,diagnostic_output=work/'diagnostic')
 selected=rows[:4]
 for module in ('C087SerializedFixture.Model','SpectreFinite.RadiusFiveCertified','SpectreFinite.RadiusFivePruningRounds'):
  for phase in ('compile','check'):
   argv,inner,layout=native.readonly_command_layout({'source_root':str(fixture_root),'toolchain_root':str(toolchain_root),'workspace':str(pred)},module,module.replace('.','/')+'.lean',base.FLAGS if phase=='compile' else [],phase)
   selected.append({'name':phase+'-lookup-'+module,'execution_condition':'all_prior_required_gates_passed','argv':argv,'inner_argv':inner,'sandbox':layout,'phase':phase,'nominal_timeout_seconds':120,'resource_limits':dict(policy.LIMITS),'max_log_bytes':16*1024**2,'new_sessions_explicitly_allowed':False})
 return selected+rows[12:15]

def import_lookup_preflight(native,*,fixture_root,toolchain_root,helper_root,work,remaining,verify_inputs,executor,process,observe_native=None):
 """Fixed synthetic split-root checker+raw-auditor gate, before acquisition."""
 fixture_root=Path(fixture_root);helper_root=Path(helper_root);work=Path(work)
 need(tree(fixture_root)[0]==LOOKUP_FIXTURE_FILES and tree(helper_root)[0]==HELPER_FILES,'fixed lookup fixture/helper sources')
 need(not work.exists() and not work.is_symlink(),'fresh lookup preflight required');work.mkdir(mode=0o700)
 rows=lookup_preflight_plan(native,fixture_root=fixture_root,toolchain_root=toolchain_root,helper_root=helper_root,work=work)
 need(len(rows)==13,'fixed lookup preflight command count')
 (work/'diagnostic').mkdir(mode=0o700);(work/'diagnostic/receipts').mkdir(mode=0o700)
 for root in dict.fromkeys(_root(row) for row in rows):workspace(root)
 (work/'receipts').mkdir(mode=0o700);frozen={};records=[];view=None;log_bytes=0;audit_rows=None
 def check():
  verify_inputs();policy.effective_timeout(120,remaining())
  need(tree(fixture_root)[0]==LOOKUP_FIXTURE_FILES and tree(helper_root)[0]==HELPER_FILES,'fixed lookup fixture/helper sources')
  for root,expected in frozen.items():need(tree(root/'objects')[0]==expected,'lookup preflight backing map changed')
  if view is not None:verify_import_view(view,remaining)
  policy.effective_timeout(120,remaining())
 for index,row in enumerate(rows):
  check();root=_root(row);module=_module(row)
  if row['phase']=='compile':
   quarantine=root/'module-quarantine'/module;need(not quarantine.exists(),'compile quarantine already exists')
   (quarantine/'objects'/module.replace('.','/')).parent.mkdir(mode=0o700,parents=True)
  for path in row['sandbox']['readonly_roots']+row['sandbox']['writable_roots']:
   native.no_symlink_path(Path(path));need(Path(path).is_dir(),'sandbox mount absent')
  effective=policy.effective_timeout(120,remaining());stdout=root/'logs'/(row['name']+'.stdout');stderr=root/'logs'/(row['name']+'.stderr')
  def invoke():
   result=executor(row['argv'],cwd=Path(row['sandbox']['cwd']),env=row['sandbox']['environment'],timeout=effective,stdout=stdout,stderr=stderr,max_log_bytes=row['max_log_bytes'],limits=row['resource_limits'],allow_new_sessions=False)
   if observe_native is not None:observe_native(index,effective,result)
   prevalidate_native_exit(result,effective);return result
  result=process(invoke);policy.effective_timeout(120,remaining())
  rawout=_read_log(stdout,row['max_log_bytes']);rawerr=_read_log(stderr,row['max_log_bytes']);log_bytes+=len(rawout)+len(rawerr)
  need(log_bytes<=2*1024**2,'lookup preflight aggregate logs')
  record={'spec':row,'effective_timeout_seconds':effective,'result':result,'stdout':{'bytes':len(rawout),'sha256':digest(rawout)},'stderr':{'bytes':len(rawerr),'sha256':digest(rawerr)}}
  durable_new(work/'receipts'/('%02d-%s.json'%(index,row['name'])),record);records.append(record)
  actual=policy.validate_live_command(row,record,rawout,rawerr,expected_effective_timeout=effective);policy.require_success({**actual,'timeout_seconds':effective});check()
  need(rawerr==b'','lookup preflight stderr')
  if row['phase']=='compile':
   need(rawout==b'','lookup preflight compile stdout')
   before,total=native.StageRunner.promote_quarantine(_PromotionWorkspace(root),module,64*1024**2-sum(v['bytes'] for values in frozen.values() for v in values.values()))
   owned={name.removeprefix('objects/'):pinned_file(root/name) for name in before};policy.validate_output_map(module,{'objects/'+k:v for k,v in owned.items()})
   frozen.setdefault(root,{}).update(owned);check()
   if module==TARGET:
    view=create_import_view(work/'diagnostic/receipts/default-imports',work/'predecessors/objects',root/'objects',frozen[work/'predecessors'],frozen[root],remaining)
    durable_new(work/'receipts/import-view.json',{'schema':'c087-synthetic-split-root-import-view-v1','map_sha256':view['map_sha256'],'predecessor_count':len(frozen[work/'predecessors']),'target_count':len(frozen[root]),'payload_bytes_copied':0})
  elif row['phase']=='audit':
   audit_rows=policy.parse_audit(rawout);need(all(x['all_owned_transitive_axioms']==[] for x in audit_rows),'lookup fixture axioms must be empty')
  else:need(rawout==b'','lookup preflight checker stdout')
  check()
 need(view is not None and audit_rows is not None,'lookup checker and auditor required')
 check();close_import_view(view,remaining);view=None;check()
 result={'schema':'c087-fixed-import-lookup-preflight-v1','status':'synthetic_split_root_checker_and_raw_auditor_passed','commands':records,'source_files':LOOKUP_FIXTURE_FILES,'audit_rows':audit_rows,'research_objects_loaded':False,'research_proof_claimed':False,'proof_pass_claimed':False,'output_companion_count':sum(map(len,frozen.values()))}
 durable_new(work/'RESULT.json',result);check()
 files=tree(work)[0];selected={name:pin for name,pin in files.items() if name=='RESULT.json' or name.startswith('receipts/') or '/logs/' in name}
 need(sum(x['bytes'] for x in selected.values())<=4*1024**2,'lookup preflight complete evidence bound');policy.effective_timeout(120,remaining());return selected

