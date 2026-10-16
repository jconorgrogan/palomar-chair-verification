"""Exact conditional sandbox/admission functions plus bounded shared tiny probe.
These functions are copied verbatim from the independently reviewed conditional
runner, without executing its cache or research build main function.
"""
from pathlib import Path
import hashlib,inspect,os,shutil,stat,time
GIB=1024**3
SUFFIXES=['.olean','.olean.private','.olean.server','.ilean','.ir.sig','.ir','.c']
f=None

def write_json(path,value):
    path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(f.json_bytes(value))

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

RUNTIME_SHA='42bd268b1ca3e9bf89f4149ac427d6c0e76f735233b092a6df4ca27a2c2db7ea'
SOURCES={
 'ProbeShared.Seed': 'module\npublic import Init\n@[expose] public section\nnamespace ProbeShared\ndef seed : Nat := 40\nend ProbeShared\n',
 'ProbeShared.Middle': 'module\npublic import ProbeShared.Seed\n@[expose] public section\nnamespace ProbeShared\ntheorem seed_eq : seed = 40 := rfl\nend ProbeShared\n',
 'ProbeShared.Consumer': 'module\npublic import ProbeShared.Middle\n@[expose] public section\nnamespace ProbeShared\ndef answer : Nat := seed + 2\ntheorem answer_eq : answer = 42 := rfl\nend ProbeShared\n'}

def run_probe(api, *, runtime, runtime_inventory, work, env, command):
    """Use the caller's exact sandbox, command, admission, namespace and hash code.

    Success returns a receipt only after two actual shell denial controls and all
    three actual Lean compile/kernel-check pairs. Exceptions abort the caller;
    there is no fallback, resume or accepted predecessor after a failed check.
    """
    f=api.f
    f.need(f.sha(f.json_bytes(runtime_inventory))==RUNTIME_SHA,'probe runtime inventory identity')
    runtime=Path(runtime);work=Path(work)
    root=work/'shared-readonly-probe';f.no_symlink_path(root)
    f.need(not root.exists(),'probe workspace must be fresh')
    for rel in ['src/ProbeShared','objects','quarantine','boundary/objects/ProbeShared','boundary/cache','boundary/quarantine']:
        (root/rel).mkdir(parents=True,exist_ok=True)
    started=time.monotonic();commands=[];maximum=16*1024**2
    for module,data in SOURCES.items():
        (root/'src'/(module.replace('.','/')+'.lean')).write_text(data)
    source_before=api.checked_inventory(root/'src',maximum=4096)
    result={'schema':'shared-readonly-namespace-probe-v1','status':'INCOMPLETE',
      'research_theorem_claimed':False,'runtime_inventory_sha256':RUNTIME_SHA,
      'runner_sha256':f.file_sha(Path(api.__file__)),
      'helper_sha256':f.file_sha(Path(__file__)),
      'sandbox_source_sha256':hashlib.sha256(inspect.getsource(api.sandbox).encode()).hexdigest(),
      'source_files':source_before['files'],'process_session_policy':'exact_parent_command_and_sandbox',
      'compile_heap_mib':512,'per_command_wall_seconds':60,'rss_tree_bytes':2*1024**3,
      'aggregate_probe_wall_seconds':480,'exact_companions':21}
    api.write_json(work/'evidence/shared-readonly-probe.json',result)
    def execute(name,inner,*,sources,writable,cwd,environment,seconds=60):
        remaining=480-(time.monotonic()-started)
        f.need(remaining>1,'shared namespace probe deadline')
        argv=api.sandbox(inner,runtime=runtime,sources=sources,writable=writable,cwd=cwd,env=environment)
        f.need('--share-net' not in argv,'probe network isolation missing')
        output,ok=command('namespace-probe-'+name,argv,cwd=cwd,env=environment,
          seconds=min(seconds,max(1,int(remaining))),rss=2*1024**3,allowed_sessions=True)
        f.need(ok,'shared namespace probe command failed')
        commands.append({'name':name,'argv':list(map(str,argv)),'stdout_sha256':f.file_sha(output)})
        f.need(time.monotonic()-started<480,'shared namespace probe deadline')
    try:
        boundary=root/'boundary';pred=boundary/'objects/ProbeShared/Sentinel';cache=boundary/'cache/Sentinel'
        pred.write_bytes(b'PINNED_PREDECESSOR\n');cache.write_bytes(b'PINNED_CACHE\n')
        protected=[pred,root/'src/ProbeShared/Seed.lean',runtime/'lib/lean/Init.olean',cache]
        before={str(p):f.file_sha(p) for p in protected}
        output=boundary/'quarantine/allowed'
        # These operations must fail due to actual mount protection, not Unix mode bits.
        shell='set -eu; for p in "$1" "$2" "$3" "$4"; do if (printf BAD >> "$p") 2>/dev/null; then exit 41; fi; if chmod u+w "$p" 2>/dev/null; then exit 42; fi; if rm "$p" 2>/dev/null; then exit 43; fi; if mkdir "$(dirname "$p")/forbidden-directory" 2>/dev/null; then exit 44; fi; done; printf ALLOWED > "$5"; printf "READONLY_BOUNDARY_PASSED\\n"'
        readonly=[boundary/'objects',boundary/'cache',root/'src']
        execute('compiler-write-denial',['/bin/sh','-c',shell,'probe',*protected,output],
          sources=readonly,writable=[boundary/'quarantine',work/'home',work/'tmp'],cwd=root/'src',environment=env,seconds=30)
        f.need(output.read_bytes()==b'ALLOWED','probe quarantine write denied')
        f.need(before=={str(p):f.file_sha(p) for p in protected},'probe readonly input changed')
        check='set -eu; if (printf BAD >> "$1") 2>/dev/null; then exit 45; fi; if (printf BAD >> "$2") 2>/dev/null; then exit 46; fi; printf "READONLY_CHECKER_BOUNDARY_PASSED\\n"'
        execute('checker-write-denial',['/bin/sh','-c',check,'probe',pred,output],
          sources=readonly,writable=[work/'home',work/'tmp'],cwd=root/'src',environment=env,seconds=30)
        f.need(output.read_bytes()==b'ALLOWED' and before=={str(p):f.file_sha(p) for p in protected},'probe checker wrote protected data')
        f.exact_tree(boundary/'objects',{'ProbeShared/Sentinel'});f.exact_tree(boundary/'cache',{'Sentinel'});f.exact_tree(boundary/'quarantine',{'allowed'})
        prior={};checked=[]
        probe_env=dict(env);probe_env['LEAN_PATH']=str(root/'objects')+':'+str(runtime/'lib/lean')
        for module in SOURCES:
            rel=module.replace('.','/');staging=root/'quarantine'/module;staging.mkdir()
            target=staging/(rel+'.olean');target.parent.mkdir(parents=True)
            f.need(str(staging) not in probe_env['LEAN_PATH'].split(':'),'probe quarantine import root')
            api.namespace_providers([root/'objects',runtime/'lib/lean'])
            src=[root/'src',root/'objects',boundary/'cache']
            argv=[runtime/'bin/lean','-j1','-M512','-Dcompiler.postponeCompile=false','-o',target,'-i',staging/(rel+'.ilean'),'-c',staging/(rel+'.c'),root/'src'/(rel+'.lean')]
            execute('compile-'+module,argv,sources=src,writable=[staging,work/'home',work/'tmp'],cwd=root/'src',environment=probe_env)
            prior=api.admit_quarantine(staging,root/'objects',module,prior,maximum);shutil.rmtree(staging)
            result.update(status='PROVISIONAL_PENDING_KERNEL_CHECK',current_module=module)
            api.write_json(work/'evidence/shared-readonly-probe.json',result)
            execute('check-'+module,[runtime/'bin/leanchecker',module],sources=src,writable=[work/'home',work/'tmp'],cwd=root/'src',environment=probe_env)
            for name in api.module_outputs(module):
                f.need(f.file_sha(root/'objects'/name)==prior[name]['sha256'],'probe checker changed output')
            checked.append(module)
        final=api.verify_owned_final(root/'objects',prior,maximum)
        f.need(len(final['files'])==21 and checked==list(SOURCES),'probe output/checker coverage')
        f.need(api.checked_inventory(root/'src',maximum=4096)==source_before,'probe sources changed')
        f.need(before=={str(p):f.file_sha(p) for p in protected},'probe protected input changed')
        result.update(status='PASSED_SHARED_READONLY_NAMESPACE_PROBE',compile_check_pairs=3,
          outputs=final,commands=commands,wall_seconds=time.monotonic()-started,
          actual_write_denial_passed=True,quarantine_not_imported=True,all_kernel_checks_passed=True)
        api.write_json(work/'evidence/shared-readonly-probe.json',result)
        return result
    except BaseException as error:
        result.update(status='FAILED',error_type=type(error).__name__,error=str(error)[:2000],commands=commands)
        api.write_json(work/'evidence/shared-readonly-probe.json',result)
        raise
