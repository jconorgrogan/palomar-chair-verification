"""Strict inert C087 parent/child v2 byte protocol. No public activation factory."""
from __future__ import annotations
import hashlib
import json
import math
from fractions import Fraction
import os
from pathlib import Path
import re
import stat
import time

REQUEST_SCHEMA='c087-parent-admission-v2'
INVOCATION_SCHEMA='c087-owned-dispatch-v2'
RESPONSE_SCHEMA='c087-child-response-v2'
DERIVED_RULE={'admitted/historical-transfer-certificate.json':{'rule':'frozen-native-transfer-certificate-v1'}}
INPUT_ROOTS={'latest_pipeline','prior_pipeline','research_source','acquisition','runtime_placeholder'}
NATIVE_STATIC_KEYS={'schema','status','executable_authority','activation_allowed','proof_pass_claimed',
 'runtime_installed','kernel_executed','target_stage','module_count','stage_count','companion_count',
 'certificate_sha256','scope_sha256','native_input_binding_sha256','frozen_graph_sha256','objects',
 'native_descriptors','restore_evidence_hashes','raw_archive_bytes'}
REQUEST_KEYS={'schema','offline_fixture_only','session_nonce','container','container_inode','native_workspace',
 'original_monotonic','deadline_monotonic','original_wall','expiry_wall','diagnostic_output','diagnostic_output_inode',
 'input_inode_hash_maps','registration','registration_sha256','admission_executor_pin','diagnostic_executor_pin'}
REGISTRATION_KEYS={'input_roots','input_files','source_root_name','expected_files','expected_directories','derived_files',
 'native_static','admission','diagnostic','input_limits','output_limits','filesystem_identity'}
INVOCATION_KEYS={'schema','phase','request_sha256','registration_sha256','argv','environment','bounds','cpus','cwd',
 'stdout','stderr','effective_timeout_seconds','max_log_bytes','allow_new_sessions','deadline_monotonic','session_nonce',
 'container_inode','dispatch_monotonic','effective_deadline_monotonic','retained_inode_hash_map_sha256'}
RESPONSE_KEYS={'schema','status','request_sha256','invocation_sha256','registration_sha256','session_nonce',
 'container_inode','deadline_monotonic','native_report_sha256','expected_files_sha256'}
COMMAND_KEYS={'argv','environment','bounds','cpus','nominal_timeout_seconds','max_log_bytes'}
BOUND_KEYS={'address_space_bytes','rss_tree_bytes','max_created_file_bytes'}
IDENTITY_KEYS={'dev','ino','mode','uid','gid','nlink','size','mtime_ns','ctime_ns'}
PROTOCOL_FILES={'request.json','admission-invocation.json','admission.stdout','admission.stderr','native-report.json','response.json'}
MAX_JSON=64*1024**2

class Rejected(ValueError):pass

def need(ok,message):
    if not ok:raise Rejected(message)

def canonical(value):return json.dumps(value,sort_keys=True,separators=(',',':'),ensure_ascii=True,allow_nan=False).encode()
def sha(raw):return hashlib.sha256(raw).hexdigest()
def exact(a,b,label):
    need(type(a) is type(b),label)
    need(a==b if type(a) in (bytes,set,frozenset) else canonical(a)==canonical(b),label)
def keys(value,wanted,label):need(type(value) is dict and set(value)==wanted,label)
def parse(raw,maximum=MAX_JSON):
    need(type(raw) is bytes and len(raw)<=maximum,'bounded immutable JSON')
    def pairs(items):
        out={}
        for key,value in items:need(key not in out,'duplicate JSON key');out[key]=value
        return out
    return json.loads(raw,object_pairs_hook=pairs,parse_constant=lambda _ : (_ for _ in ()).throw(Rejected('nonfinite JSON')))
def digest(value):need(type(value) is str and re.fullmatch('[0-9a-f]{64}',value),'SHA256 required');return value
def finite(value,label):
    need(type(value) in (int,float) and math.isfinite(value),label);return float(value)
def integer(value,label,minimum=0,maximum=2**64-1):
    need(type(value) is int and minimum<=value<=maximum,label);return value
def relative(value):
    need(type(value) is str and value and '\\' not in value and '\x00' not in value and not value.startswith('/'),'relative path')
    need(all(p not in ('','.','..') for p in value.split('/')),'clean relative path');return value
def absolute(value):
    need(type(value) is str and value.startswith('/') and '\\' not in value and '\x00' not in value and os.path.normpath(value)==value,'canonical absolute path');return value
def inode(value):
    need(type(value) is list and len(value)==2,'inode pair')
    for x in value:integer(x,'inode integer')
    return value

def file_pin(value):
    keys(value,{'bytes','sha256'},'file pin keys');integer(value['bytes'],'file length');digest(value['sha256'])
def limits(value):
    keys(value,{'max_bytes','max_entries'},'tree limits');integer(value['max_bytes'],'logical byte limit',1);integer(value['max_entries'],'entry limit',1)

def validate_request(raw):
    """Parse and structurally bind bytes only; this creates no execution authority."""
    request=parse(raw);keys(request,REQUEST_KEYS,'request fields');exact(request['schema'],REQUEST_SCHEMA,'request schema')
    exact(request['offline_fixture_only'],False,'fixture request rejected');digest(request['session_nonce'])
    container=absolute(request['container']);inode(request['container_inode']);inode(request['diagnostic_output_inode'])
    exact(request['native_workspace'],container+'/admitted','native workspace');absolute(request['diagnostic_output'])
    start=finite(request['original_monotonic'],'original monotonic');deadline=finite(request['deadline_monotonic'],'deadline')
    need(type(request['deadline_monotonic']) is float and 0<deadline-start<=19800,'shared original330-minute maximum')
    original_wall=finite(request['original_wall'],'original wall');expiry=finite(request['expiry_wall'],'expiry wall')
    need(original_wall<expiry,'original wall bound')
    for field in ('admission_executor_pin','diagnostic_executor_pin'):
        value=request[field];need(type(value) is list and len(value)==11,'executor pin shape')
        for index in (0,1):need(type(value[index]) is str and value[index],'executor text pin')
        absolute(value[2])
        for index in (3,4,7,8):integer(value[index],'executor identity')
        for index in (5,6,9,10):digest(value[index])
    r=request['registration'];keys(r,REGISTRATION_KEYS,'registration fields')
    digest(request['registration_sha256']);exact(sha(canonical(r)),request['registration_sha256'],'registration hash')
    keys(r['input_roots'],INPUT_ROOTS,'phase-specific input roots');keys(r['input_files'],INPUT_ROOTS,'input files roots')
    keys(r['input_limits'],INPUT_ROOTS,'input limits roots');keys(request['input_inode_hash_maps'],INPUT_ROOTS,'input snapshot roots')
    exact(r['source_root_name'],'research_source','fixed source root name')
    roots=[]
    for name,root in r['input_roots'].items():
        absolute(root);need(root!=container and not root.startswith(container+'/') and not container.startswith(root+'/'),'input/container overlap')
        need(all(root!=other and not root.startswith(other+'/') and not other.startswith(root+'/') for other in roots),'input roots overlap');roots.append(root)
        need(type(r['input_files'][name]) is dict,'input files mapping');limits(r['input_limits'][name])
        for path,value in r['input_files'][name].items():relative(path);file_pin(value)
        snapshot=request['input_inode_hash_maps'][name];need(type(snapshot) is dict and '.' in snapshot,'input snapshot root')
        files={}
        for path,value in snapshot.items():
            if path!='.':relative(path)
            need(type(value) is dict and value.get('kind') in ('directory','file'),'snapshot kind')
            keys(value,{'kind',*IDENTITY_KEYS}|({'sha256'} if value['kind']=='file' else set()),'snapshot fields')
            for field in IDENTITY_KEYS:integer(value[field],'snapshot integer')
            if value['kind']=='file':digest(value['sha256']);files[path]={'bytes':value['size'],'sha256':value['sha256']}
        exact(files,r['input_files'][name],'registered input contents')
        need(snapshot['.']['kind']=='directory','snapshot root directory')
        need(len(snapshot)<=r['input_limits'][name]['max_entries'] and sum(v['bytes'] for v in files.values())<=r['input_limits'][name]['max_bytes'],'registered input bound')
    exact(r['input_files']['runtime_placeholder'],{},'empty runtime placeholder')
    exact(r['derived_files'],DERIVED_RULE,'single enumerated certificate rule')
    need(type(r['expected_files']) is dict,'expected file map')
    for name,value in r['expected_files'].items():
        relative(name);file_pin(value)
        need(name.startswith(('admitted/','admitted-historical-validation/')) and name not in DERIVED_RULE,'fixed output namespace')
    dirs=r['expected_directories'];need(type(dirs) is list and len(dirs)==len(set(dirs)),'exact directory set')
    for name in dirs:relative(name);need(name in ('admitted','admitted-historical-validation') or name.startswith(('admitted/','admitted-historical-validation/')),'directory namespace')
    need({'admitted','admitted-historical-validation','admitted-historical-validation/empty-runtime'}<=set(dirs),'historical sidecar required')
    need(not set(r['expected_files'])&set(dirs),'file/directory collision')
    limits(r['output_limits']);need(r['output_limits']['max_entries']>=len(r['expected_files'])+len(DERIVED_RULE)+len(dirs)+1+len(PROTOCOL_FILES),'complete output entries')
    need(r['output_limits']['max_bytes']>sum(v['bytes'] for v in r['expected_files'].values()),'derived/protocol byte reserve')
    keys(r['filesystem_identity'],{'st_dev','f_frsize'},'filesystem identity');integer(r['filesystem_identity']['st_dev'],'filesystem device');integer(r['filesystem_identity']['f_frsize'],'allocation unit',1)
    exact(r['filesystem_identity']['st_dev'],request['container_inode'][0],'container mount binding')
    native=r['native_static'];keys(native,NATIVE_STATIC_KEYS,'native static fields')
    for name in ('executable_authority','activation_allowed','proof_pass_claimed','runtime_installed','kernel_executed'):exact(native[name],False,'native false claim')
    for name,wanted in [('schema','c087-native-admission-report-v1'),('status','native_admission_only'),('target_stage','build_087'),('module_count',6218),('stage_count',85),('companion_count',37308)]:exact(native[name],wanted,'fixed native '+name)
    for name in ('certificate_sha256','scope_sha256','native_input_binding_sha256','frozen_graph_sha256'):digest(native[name])
    integer(native['raw_archive_bytes'],'raw archive accounting',3009576960,4294967296)
    for name in ('objects','restore_evidence_hashes'):need(type(native[name]) is dict,'native map')
    need(type(native['native_descriptors']) is list,'native descriptor list')
    command=r['admission'];keys(command,COMMAND_KEYS,'command keys');keys(command['bounds'],BOUND_KEYS,'native bounds')
    for name in ('address_space_bytes','rss_tree_bytes'):exact(command['bounds'][name],8*1024**3,'fixed admission8 GiB')
    integer(command['bounds']['max_created_file_bytes'],'file bound',1,8*1024**3)
    exact(command['cpus'],1,'one admission CPU');integer(command['nominal_timeout_seconds'],'nominal admission bound',1,19800)
    integer(command['max_log_bytes'],'combined log cap',1,16*1024**2)
    need(type(command['argv']) is list and command['argv'] and all(type(v) is str and v and '\x00' not in v for v in command['argv']),'exact argv')
    need(type(command['environment']) is dict and all(type(k) is str and type(v) is str and '\x00' not in k+v for k,v in command['environment'].items()),'exact environment')
    keys(r['diagnostic'],{'kind','parent_registration_sha256','engine_manifest_sha256'},'diagnostic parent binding')
    exact(r['diagnostic']['kind'],'parent_fixed_engine_binding_v1','diagnostic binding kind')
    digest(r['diagnostic']['parent_registration_sha256']);digest(r['diagnostic']['engine_manifest_sha256'])
    return request

def validate_invocation(raw,request_raw,request):
    inv=parse(raw);keys(inv,INVOCATION_KEYS,'invocation fields');exact(inv['schema'],INVOCATION_SCHEMA,'invocation schema')
    r=request['registration'];container=request['container'];command=r['admission']
    expected={'phase':'admission','request_sha256':sha(request_raw),'registration_sha256':request['registration_sha256'],
        'environment':command['environment'],'bounds':command['bounds'],'cpus':1,'cwd':container,'stdout':container+'/admission.stdout',
        'stderr':container+'/admission.stderr','max_log_bytes':command['max_log_bytes'],'allow_new_sessions':False,
        'deadline_monotonic':request['deadline_monotonic'],'session_nonce':request['session_nonce'],'container_inode':request['container_inode'],
        'retained_inode_hash_map_sha256':None}
    substitutions={'$CONTAINER':container,'$WORKSPACE':request['native_workspace'],'$REQUEST':container+'/request.json',
        '$INVOCATION':container+'/admission-invocation.json','$NONCE':request['session_nonce'],'$DEADLINE':repr(request['deadline_monotonic'])}
    expected['argv']=[substitutions.get(v,v) for v in command['argv']]
    for name,value in expected.items():exact(inv[name],value,'invocation '+name)
    dispatch=finite(inv['dispatch_monotonic'],'dispatch clock');need(request['original_monotonic']<=dispatch<request['deadline_monotonic'],'dispatch original window')
    effective_deadline=finite(inv['effective_deadline_monotonic'],'downward-only effective deadline')
    need(type(inv['effective_deadline_monotonic']) is float and dispatch<effective_deadline<=request['deadline_monotonic'],'effective deadline may only tighten')
    effective=command_timeout(command['nominal_timeout_seconds'],inv['effective_deadline_monotonic'],inv['dispatch_monotonic'])
    need(effective>0,'cleanup reserve');exact(inv['effective_timeout_seconds'],effective,'effective timeout')
    return inv

def response_bytes(request_raw,invocation_raw,native_report_raw):
    request=validate_request(request_raw);inv=validate_invocation(invocation_raw,request_raw,request)
    return canonical({'schema':RESPONSE_SCHEMA,'status':'complete_native_admission','request_sha256':sha(request_raw),
        'invocation_sha256':sha(invocation_raw),'registration_sha256':request['registration_sha256'],
        'session_nonce':request['session_nonce'],'container_inode':request['container_inode'],'deadline_monotonic':request['deadline_monotonic'],
        'native_report_sha256':sha(native_report_raw),'expected_files_sha256':sha(canonical(request['registration']['expected_files']))})

def validate_response(raw,request_raw,invocation_raw,native_report_raw):
    obj=parse(raw);keys(obj,RESPONSE_KEYS,'response fields');exact(obj,parse(response_bytes(request_raw,invocation_raw,native_report_raw)),'response binding');return obj

def create_production_binding(*args,**kwargs):
    raise Rejected('production binding disabled pending complete composed review and actual preflight')

def fixed_admission_command(adapter_entry):
    """Pure launch plan; parent must independently pin code/mounts before dispatch."""
    absolute(adapter_entry);need(Path(adapter_entry).name=='admission_child.py','fixed entrypoint basename')
    return {'argv':['/usr/bin/python3','-I','-S','-B',adapter_entry,'--request','$REQUEST','--invocation','$INVOCATION'],
        'environment':{'LANG':'C.UTF-8','LC_ALL':'C.UTF-8','TZ':'UTC'},'cpus':1,'nominal_timeout_seconds':19800,
        'max_log_bytes':16*1024**2,'bounds':{'address_space_bytes':8*1024**3,'rss_tree_bytes':8*1024**3,'max_created_file_bytes':1024**3}}

def identity(st):
    return {'dev':st.st_dev,'ino':st.st_ino,'mode':stat.S_IMODE(st.st_mode),'uid':st.st_uid,'gid':st.st_gid,
        'nlink':st.st_nlink,'size':st.st_size,'mtime_ns':st.st_mtime_ns,'ctime_ns':st.st_ctime_ns}

def checked_path(path):
    path=Path(absolute(str(path)))
    for p in (path,*path.parents):need(not p.is_symlink(),'symlink path')
    return path

def read_file(path,maximum=MAX_JSON):
    path=checked_path(path);before=path.lstat()
    need(stat.S_ISREG(before.st_mode) and before.st_nlink==1 and before.st_uid==os.getuid() and not before.st_mode&0o022,'owned single-link regular file')
    need(before.st_size<=maximum,'bounded file')
    fd=os.open(path,os.O_RDONLY|os.O_NOFOLLOW|os.O_CLOEXEC|os.O_NONBLOCK)
    try:
        exact(identity(os.fstat(fd)),identity(before),'opened inode')
        chunks=[];total=0
        while block:=os.read(fd,min(1024**2,maximum-total+1)):
            total+=len(block);need(total<=maximum,'growing file');chunks.append(block)
        exact(identity(os.fstat(fd)),identity(before),'stable read inode');exact(identity(path.lstat()),identity(before),'stable read path')
        return b''.join(chunks),identity(before)
    finally:os.close(fd)

def snapshot(root,*,max_bytes,max_entries,checkpoint=lambda:None,durable=False):
    """Exact stable inode/hash map on parent-required immutable/owned mounts."""
    root=checked_path(root);found={};seen=set();total=0
    def walk(path,relative_path):
        nonlocal total
        checkpoint();before=path.lstat();need(stat.S_ISDIR(before.st_mode) and before.st_uid==os.getuid() and not before.st_mode&0o022,'owned directory')
        key=(before.st_dev,before.st_ino);need(key not in seen,'directory inode alias');seen.add(key)
        found[relative_path or '.']={'kind':'directory',**identity(before)};need(len(found)<=max_entries,'tree entries')
        names=sorted(os.listdir(path))
        for name in names:
            relative(name);child=path/name;rel=name if not relative_path else relative_path+'/'+name;st=child.lstat()
            need(not stat.S_ISLNK(st.st_mode),'symlink entry')
            if stat.S_ISDIR(st.st_mode):walk(child,rel)
            else:
                need(stat.S_ISREG(st.st_mode) and st.st_nlink==1,'regular tree file')
                total+=st.st_size;need(total<=max_bytes,'tree logical bytes')
                inode_key=(st.st_dev,st.st_ino);need(inode_key not in seen,'file inode alias');seen.add(inode_key)
                digest_value,ident=hash_file(child,st.st_size,checkpoint);exact(ident,identity(st),'snapshot file identity')
                found[rel]={'kind':'file',**ident,'sha256':digest_value};need(len(found)<=max_entries,'tree entries')
                if durable:
                    fd=os.open(child,os.O_RDONLY|os.O_NOFOLLOW);os.fsync(fd);os.close(fd)
                checkpoint()
        exact(sorted(os.listdir(path)),names,'directory membership');exact(identity(path.lstat()),identity(before),'directory identity')
        if durable:
            fd=os.open(path,os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW);os.fsync(fd);os.close(fd)
    walk(root,'');checkpoint();return found

def contents(snapshot_map):return {name:{'bytes':value['size'],'sha256':value['sha256']} for name,value in snapshot_map.items() if value['kind']=='file'}

def observed_container(request):
    path=checked_path(request['container']);st=path.lstat();need(stat.S_ISDIR(st.st_mode) and st.st_uid==os.getuid() and not st.st_mode&0o077,'private parent container')
    exact([st.st_dev,st.st_ino],request['container_inode'],'container inode')
    actual={'st_dev':st.st_dev,'f_frsize':os.statvfs(path).f_frsize}
    exact(actual,request['registration']['filesystem_identity'],'container filesystem');return actual

class OriginalClock:
    def __init__(self,request,effective_deadline=None):
        self.start=request['original_monotonic'];self.original_deadline=request['deadline_monotonic']
        self.deadline=self.original_deadline if effective_deadline is None else finite(effective_deadline,'effective clock bound')
        need(self.start<self.deadline<=self.original_deadline,'clock bound may only tighten')
        self.original_wall=request['original_wall'];self.expiry=request['expiry_wall']
        self.last_mono=self.start;self.last_wall=self.original_wall;self.poisoned=False
    def check(self):
        need(not self.poisoned,'clock poisoned')
        try:
            mono=time.monotonic();wall=time.time()
            need(self.last_mono<=mono<self.deadline and self.last_wall<=wall<self.expiry,'expired/backward original clock')
            self.last_mono=mono;self.last_wall=wall;return self.deadline-mono
        except BaseException:self.poisoned=True;raise

def write_new(path,raw,checkpoint):
    """Exclusive durable output only; failure never resumes or overwrites."""
    need(type(raw) is bytes,'output bytes');path=checked_path(path);checkpoint()
    fd=os.open(path,os.O_WRONLY|os.O_CREAT|os.O_EXCL|os.O_NOFOLLOW|os.O_CLOEXEC,0o600)
    try:
        st=os.fstat(fd);need(stat.S_ISREG(st.st_mode) and st.st_nlink==1 and st.st_uid==os.getuid(),'exclusive regular output')
        remaining=memoryview(raw)
        while remaining:
            written=os.write(fd,remaining);need(written>0,'short durable write');remaining=remaining[written:]
        os.fsync(fd)
    finally:os.close(fd)
    directory=os.open(path.parent,os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW)
    try:os.fsync(directory)
    finally:os.close(directory)
    checkpoint();actual,_=read_file(path,len(raw));exact(actual,raw,'durable exact output');checkpoint()


def command_timeout(nominal,deadline,dispatch):
    integer(nominal,'nominal timeout',1);finite(deadline,'absolute deadline');finite(dispatch,'dispatch instant')
    return min(nominal,math.floor(Fraction(deadline)-Fraction(dispatch)-3))


def hash_file(path,maximum,checkpoint=lambda:None):
    path=checked_path(path);before=path.lstat()
    need(stat.S_ISREG(before.st_mode) and before.st_nlink==1 and before.st_uid==os.getuid() and not before.st_mode&0o022,'owned regular hash file')
    need(before.st_size<=maximum,'bounded hash file')
    fd=os.open(path,os.O_RDONLY|os.O_NOFOLLOW|os.O_CLOEXEC|os.O_NONBLOCK)
    try:
        exact(identity(os.fstat(fd)),identity(before),'hash opened inode');hasher=hashlib.sha256();total=0
        while block:=os.read(fd,1024**2):
            total+=len(block);need(total<=maximum,'growing hash file');hasher.update(block);checkpoint()
        need(total==before.st_size,'truncated hash file');exact(identity(os.fstat(fd)),identity(before),'hash stable inode')
        exact(identity(path.lstat()),identity(before),'hash stable path');return hasher.hexdigest(),identity(before)
    finally:os.close(fd)
