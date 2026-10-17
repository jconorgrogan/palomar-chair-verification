"""Exact reviewed conditional sandbox/admission/deadline primitives."""
from pathlib import Path
import hashlib,json,os,signal,stat,subprocess,time
f=None
GIB=1024**3
SUFFIXES=['.olean','.olean.private','.olean.server','.ilean','.ir.sig','.ir','.c']
def write_json(path,value):
    path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(f.json_bytes(value))

def safe_env(runtime,home,temp):
    # Construct, do not filter, the environment. No inherited GitHub/cache/cloud
    # credentials, proxy configuration, fork scope, endpoint override or old PATH.
    return {'PATH':str(runtime/'bin')+':/usr/bin:/bin','HOME':str(home),'TMPDIR':str(temp),
      'LANG':'C.UTF-8','LC_ALL':'C.UTF-8','LEAN_NUM_THREADS':'1','LEAN_ABORT_ON_PANIC':'1',
      'GIT_CONFIG_NOSYSTEM':'1','GIT_CONFIG_GLOBAL':'/dev/null','GIT_TERMINAL_PROMPT':'0',
      'LAKE_NO_CACHE':'true','LAKE_ARTIFACT_CACHE':'false','MATHLIB_NO_CACHE_ON_UPDATE':'1'}

def sandbox(argv,*,runtime,sources,writable,cwd,env,network=False):
    # Only official source and the runtime are readable during acquisition.
    # Candidate sources are never mounted into this network-enabled namespace.
    out=['/usr/bin/bwrap','--unshare-all','--die-with-parent','--new-session','--clearenv',
         '--proc','/proc','--dev','/dev','--tmpfs','/tmp']
    if network:out+=['--share-net']
    for p in ['/usr','/bin','/lib','/lib64']:
        if Path(p).exists():out+=['--ro-bind',p,p]
    for p in ['/etc/ssl','/etc/resolv.conf','/etc/hosts','/etc/nsswitch.conf']:
        if Path(p).exists():out+=['--ro-bind',p,p]
    for p in [runtime,*sources]:out+=['--ro-bind',str(p),str(p)]
    for p in writable:out+=['--bind',str(p),str(p)]
    for k,v in sorted(env.items()):out+=['--setenv',k,v]
    return out+['--chdir',str(cwd),'--',*map(str,argv)]

def checked_inventory(root,*,maximum=4*GIB,allow_links=False):
    rows={};total=0
    for p in sorted(root.rglob('*')):
        rel=p.relative_to(root).as_posix();f.safe_rel(rel);s=p.lstat()
        if stat.S_ISDIR(s.st_mode):continue
        f.need(len(rows)<100000,'inventory file count exceeded')
        if stat.S_ISLNK(s.st_mode):
            target=os.readlink(p)
            f.need(allow_links and not target.startswith('/') and p.resolve(strict=True).is_relative_to(root.resolve()),'escaping or disallowed artifact link')
            rows[rel]={'symlink':target};continue
        f.need(stat.S_ISREG(s.st_mode) and s.st_nlink==1,'nonregular or hardlinked output')
        total+=s.st_size;f.need(total<=maximum and s.st_size<=512*1024**2,'inventory byte bound')
        rows[rel]={'bytes':s.st_size,'sha256':f.file_sha(p)}
    return {'files':rows,'bytes':total}

def namespace_providers(roots):
    owners={}
    for root in roots:
        if not root.exists():continue
        for p in root.iterdir():
            if p.is_dir():prefix=p.name
            elif p.name.endswith('.olean'):prefix=p.name.removesuffix('.olean')
            else:continue
            f.need(prefix not in owners or owners[prefix]==str(root),'namespace prefix has multiple search roots: '+prefix)
            owners[prefix]=str(root)
    return owners

def git_capture(repo,*args):
    env={'PATH':'/usr/bin:/bin','HOME':'/nonexistent','GIT_CONFIG_NOSYSTEM':'1','GIT_CONFIG_GLOBAL':'/dev/null','GIT_TERMINAL_PROMPT':'0','LANG':'C.UTF-8'}
    p=subprocess.run(['/usr/bin/git','-c','core.hooksPath=/dev/null','-c','core.fsmonitor=false','-C',str(repo),*args],env=env,stdin=subprocess.DEVNULL,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=60,check=True)
    f.need(len(p.stdout)<=16*1024**2 and len(p.stderr)<=65536,'Git metadata bound')
    return p.stdout

def module_outputs(module):
    return {module.replace('.','/')+suffix for suffix in SUFFIXES}

def admit_quarantine(staging,objects,module,prior,maximum):
    expected=module_outputs(module)
    f.exact_tree(staging,expected)
    inv=checked_inventory(staging,maximum=min(maximum,512*1024**2))['files']
    f.need(set(inv)==expected,'quarantine companion set differs')
    f.need(not expected.intersection(prior),'owned output overwrite forbidden')
    f.need(sum(r['bytes'] for r in prior.values())+sum(r['bytes'] for r in inv.values())<=maximum,'aggregate owned output bound')
    # Only the host admits these exact paths. No candidate command can write the
    # committed root, and quarantine never appears on LEAN_PATH.
    for rel in sorted(expected):
        dest=objects/rel;f.no_symlink_path(dest);f.need(not dest.exists(),'preexisting destination object')
    for rel in sorted(expected):
        dest=objects/rel
        dest.parent.mkdir(parents=True,exist_ok=True)
        (staging/rel).rename(dest);dest.chmod(0o444)
        f.need(f.file_sha(dest)==inv[rel]['sha256'],'admission changed output bytes')
    return {**prior,**inv}

def verify_owned_final(objects,prior,maximum):
    f.exact_tree(objects,set(prior))
    now=checked_inventory(objects,maximum=maximum)
    f.need(now['files']==prior,'committed owned output changed, disappeared, or acquired extra files')
    return now

def require_success_commands(commands):
    for r in commands:
        f.need(r['exit_code']==0 and not any(r[k] for k in ['timed_out','log_overflow','memory_exceeded','surviving_children']) and r['process_group_empty'] and r['descendants_empty'] and not (r['escaped_descendants'] and not r['new_sessions_explicitly_allowed']),'terminal receipt contains unsuccessful command')

def readonly_boundary_preflight(runtime,work,env,command):
    committed=work/'preflight-read-only';staging=work/'preflight-quarantine'
    committed.mkdir();staging.mkdir()
    seed=committed/'predecessor';seed.write_bytes(b'IMMUTABLE_BOUNDARY_FIXTURE_ONLY\n')
    before=checked_inventory(committed,maximum=1024)
    script='test -r "$1/predecessor"; if printf bad > "$1/predecessor"; then exit 11; fi; if chmod 0600 "$1/predecessor"; then exit 12; fi; if mkdir "$1/SpectreGeometry"; then exit 13; fi; printf allowed > "$2/output"'
    argv=sandbox(['/bin/sh','-eu','-c',script,'readonly-boundary-control',committed,staging],
      runtime=runtime,sources=[committed],writable=[staging,work/'home',work/'tmp'],cwd=staging,env=env)
    command('read-only-committed-root-preflight',argv,env=env,seconds=30,allowed_sessions=True)
    f.exact_tree(committed,{'predecessor'});f.exact_tree(staging,{'output'})
    f.need(checked_inventory(committed,maximum=1024)==before,'sandbox predecessor write or namespace mutation succeeded')
    f.need((staging/'output').read_bytes()==b'allowed','sandbox writable quarantine did not work')
    write_json(work/'evidence/read-only-boundary-preflight.json',{'status':'READ_ONLY_PREDECESSOR_WRITES_CHMOD_AND_NAMESPACE_CREATION_REJECTED','quarantine_write_allowed':True,'fixture_sha256':f.file_sha(seed),'not_a_research_proof':True})

class HostDeadline:
    """Interrupt host I/O at the fixed deadline without interrupting child cleanup."""
    def __init__(self,deadline):
        self.deadline=deadline;self.in_command=False;self.expired=False;self.old_handler=None;self.failure_grace_started=False
    def alarm(self,signum,frame):
        self.expired=True
        if not self.in_command:
            self.failure_receipt_grace()
            raise f.Rejected('stage host-work aggregate deadline exceeded')
    def arm(self):
        f.need(signal.getitimer(signal.ITIMER_REAL)==(0.0,0.0),'preexisting process alarm')
        self.old_handler=signal.signal(signal.SIGALRM,self.alarm)
        signal.setitimer(signal.ITIMER_REAL,max(0.001,self.deadline-time.monotonic()))
    def failure_receipt_grace(self):
        f.need(self.expired and not self.in_command,'failure grace requires expired deadline and no owned command')
        if not self.failure_grace_started:
            self.failure_grace_started=True
            signal.setitimer(signal.ITIMER_REAL,5,1)
    def check(self):
        f.need(not self.expired and time.monotonic()<self.deadline,'stage aggregate deadline expired')
    def close(self):
        if self.old_handler is not None:
            signal.setitimer(signal.ITIMER_REAL,0)
            signal.signal(signal.SIGALRM,self.old_handler);self.old_handler=None
