#!/usr/bin/env python3
"""Small cache-backed elaboration diagnostic. Never a theorem certification."""
from __future__ import annotations
import argparse,hashlib,importlib.util,json,os,re,shutil,stat,subprocess,sys,time,urllib.request
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
# Workflow invokes Python -I -B. Check code bytes before loading vendored helpers.
HELPERS={'fresh_stage.py':'0887e6a69ae7a80c2ef4c1ee841b48d50f7eb8c58736c0396ea15e0402279d99',
 'toolchain_install.py':'9b8fefa2020be7e58bbf04f79445f603657bd647c0afe0b1196078f92629f038'}
if set(p.name for p in (ROOT/'ci').iterdir()) != {'cache_diagnostic.py',*HELPERS}:
    raise RuntimeError('unexpected helper-directory entry')
for name,digest in HELPERS.items():
    p=ROOT/'ci'/name
    if p.is_symlink() or hashlib.sha256(p.read_bytes()).hexdigest()!=digest:
        raise RuntimeError('vendored helper identity differs before import')
def load_helper(name):
    spec=importlib.util.spec_from_file_location(name,ROOT/'ci'/(name+'.py'))
    module=importlib.util.module_from_spec(spec);sys.modules[name]=module;spec.loader.exec_module(module);return module
f=load_helper('fresh_stage')
install_archive=load_helper('toolchain_install').install_archive
GIB=1024**3
ARCHIVE_URL='https://github.com/leanprover/lean4/releases/download/v4.35.0-rc2/lean-4.35.0-rc2-linux.tar.zst'
ARCHIVE_BYTES=595391556
RUNTIME_INVENTORY_SHA='42bd268b1ca3e9bf89f4149ac427d6c0e76f735233b092a6df4ca27a2c2db7ea'
HELPER_SHA='0887e6a69ae7a80c2ef4c1ee841b48d50f7eb8c58736c0396ea15e0402279d99'
OFFICIAL_REPOS={'mathlib':'leanprover-community/mathlib4','batteries':'leanprover-community/batteries','Qq':'leanprover-community/quote4','aesop':'leanprover-community/aesop','proofwidgets':'leanprover-community/ProofWidgets4','importGraph':'leanprover-community/import-graph','LeanSearchClient':'leanprover-community/LeanSearchClient','plausible':'leanprover-community/plausible','Cli':'leanprover/lean4-cli'}

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

def verify_prior_outputs(objects,prior):
    now=checked_inventory(objects,maximum=64*1024**2)['files']
    f.need(all(now.get(name)==row for name,row in prior.items()),'previous fresh diagnostic output changed')
    return now

def git_capture(repo,*args):
    env={'PATH':'/usr/bin:/bin','HOME':'/nonexistent','GIT_CONFIG_NOSYSTEM':'1','GIT_CONFIG_GLOBAL':'/dev/null','GIT_TERMINAL_PROMPT':'0','LANG':'C.UTF-8'}
    p=subprocess.run(['/usr/bin/git','-c','core.hooksPath=/dev/null','-c','core.fsmonitor=false','-C',str(repo),*args],env=env,stdin=subprocess.DEVNULL,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=60,check=True)
    f.need(len(p.stdout)<=16*1024**2 and len(p.stderr)<=65536,'Git metadata bound')
    return p.stdout

def source_snapshot(repo,pin):
    f.need(git_capture(repo,'rev-parse','HEAD').decode().strip()==pin['rev'],'dependency HEAD differs')
    f.need(git_capture(repo,'remote','get-url','origin').decode().strip()==pin['url'],'dependency origin differs')
    f.need(not git_capture(repo,'status','--porcelain=v1','--untracked-files=all'),'dependency worktree changed')
    rows={};total=0
    for entry in git_capture(repo,'ls-tree','-rz','HEAD').split(b'\0'):
        if not entry:continue
        meta,name=entry.split(b'\t',1);mode,kind,oid=meta.decode().split();rel=name.decode();f.safe_rel(rel)
        f.need(kind=='blob' and mode in ('100644','100755'),'unsupported official source entry')
        p=repo/rel;f.no_symlink_path(p);data=p.read_bytes();total+=len(data)
        f.need(total<=512*1024**2,'official source snapshot bound')
        actual=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        f.need(actual==oid,'official source does not equal pinned Git blob')
        rows[rel]={'bytes':len(data),'sha256':f.sha(data),'git_blob':oid}
    return {'revision':pin['rev'],'repository':pin['url'],'files':rows,'bytes':total}

def validate_dependencies(pins):
    f.need(len(pins)==9 and {p['name'] for p in pins}==set(OFFICIAL_REPOS),'dependency allowlist differs')
    for p in pins:
        f.need(f.COMMIT.fullmatch(p['rev']) and p['subDir'] is None,'mutable or subdirectory pin')
        f.need(p['url'].removesuffix('.git')=='https://github.com/'+OFFICIAL_REPOS[p['name']],'unofficial dependency URL')

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--contract-sha256',required=True);ap.add_argument('--work',type=Path,required=True)
    ap.add_argument('--runtime',type=Path);ap.add_argument('--runtime-inventory',type=Path)
    ap.add_argument('--local-dependencies',type=Path)
    a=ap.parse_args();f.need(sys.flags.isolated and sys.dont_write_bytecode,'invoke with Python -I -B');contract=f.pinned_load(ROOT/'contract.json',a.contract_sha256)
    f.need(contract['review_status']=='reviewed_for_execution','INACTIVE: diagnostic is not reviewed')
    f.need(f.file_sha(ROOT/'ci/fresh_stage.py')==HELPER_SHA,'bounded runner changed')
    expected=set(contract['inputs'])|{'contract.json','.github/workflows/physical-interface.yml'}
    actual={p.relative_to(ROOT).as_posix() for p in ROOT.rglob('*') if '.git' not in p.relative_to(ROOT).parts and (p.is_file() or p.is_symlink())}
    f.need(actual==expected,'unexpected or missing diagnostic package file')
    f.need(os.environ.get('GITHUB_REF')=='refs/heads/'+contract['publication_branch'],'unexpected diagnostic branch')
    f.need(git_capture(ROOT,'rev-parse','HEAD').decode().strip()==os.environ.get('GITHUB_SHA'),'workflow commit mismatch')
    f.need(not git_capture(ROOT,'status','--porcelain=v1','--untracked-files=all','--ignored'),'workflow checkout is not clean')
    for rel,row in contract['inputs'].items():
        f.safe_rel(rel);p=ROOT/rel;f.no_symlink_path(p)
        f.need(p.stat().st_size==row['bytes'] and f.file_sha(p)==row['sha256'],'diagnostic input changed: '+rel)
    work=a.work.absolute();f.no_symlink_path(work);f.need(not work.exists(),'diagnostic workspace must be new');work.mkdir()
    for n in ['logs','evidence','packages','home','tmp','cache','objects','bootstrap']:(work/n).mkdir()
    deadline=time.monotonic()+4800;commands=[];runtime=None
    result={'schema':'cache-backed-diagnostic-v1','status':'INCOMPLETE','proof_certified':False,
      'fresh_external_source_rebuild':False,'cache_bytes_trusted_not_source_authenticated':True,
      'contract_sha256':a.contract_sha256,'workflow_commit':os.environ.get('GITHUB_SHA'),
      'run_id':os.environ.get('GITHUB_RUN_ID'),'run_attempt':os.environ.get('GITHUB_RUN_ATTEMPT'),'commands':commands}
    write_json(work/'evidence/result.json',result)
    def command(name,argv,*,cwd=None,env=None,seconds=1800,rss=8*GIB,allowed_sessions=False,expect_success=True):
        f.need(time.monotonic()<deadline,'diagnostic aggregate deadline exceeded')
        seconds=min(seconds,max(1,int(deadline-time.monotonic())))
        out=work/'logs'/(name+'.stdout');err=work/'logs'/(name+'.stderr')
        r=f.run_process(list(map(str,argv)),cwd=cwd or work,env=env or safe_env(runtime or Path('/usr'),work/'home',work/'tmp'),timeout=seconds,stdout=out,stderr=err,max_log_bytes=16*1024**2,
          limits={'address_space_bytes':12*GIB,'rss_tree_bytes':rss,'max_created_file_bytes':512*1024**2},allow_new_sessions=allowed_sessions)
        r.update(name=name,argv=list(map(str,argv)),stdout_sha256=f.file_sha(out),stderr_sha256=f.file_sha(err));commands.append(r)
        write_json(work/'evidence/last_command.json',r);write_json(work/'evidence/result.json',result)
        ok=r['exit_code']==0 and not any(r[k] for k in ['timed_out','log_overflow','memory_exceeded','surviving_children']) and r['process_group_empty'] and r['descendants_empty']
        f.need(ok or not expect_success,'command failed/incomplete: '+name)
        return out,ok
    try:
        if a.runtime:
            f.need(a.runtime_inventory is not None,'existing runtime requires official inventory')
            runtime=a.runtime.absolute();f.need(f.file_sha(a.runtime_inventory)==RUNTIME_INVENTORY_SHA,'runtime inventory pin differs');inv=f.load_json(a.runtime_inventory)
            f.need(inv['archive_sha256']==f.TOOLCHAIN_SHA256,'runtime archive pin differs')
            for rel,row in inv['files'].items():
                p=runtime/rel;f.no_symlink_path(p)
                f.need(p.stat().st_size==row['bytes'] and f.file_sha(p)==row['sha256'],'runtime byte mismatch')
            for rel,target in inv['symlinks'].items():
                f.need((runtime/rel).is_symlink() and os.readlink(runtime/rel)==target and (runtime/rel).resolve().is_relative_to(runtime),'runtime symlink mismatch')
        else:
            archive=work/'lean.tar.zst';downloaded=0;start=time.monotonic()
            with urllib.request.urlopen(ARCHIVE_URL,timeout=60) as response,archive.open('xb') as out:
                while True:
                    block=response.read(1024**2)
                    if not block:break
                    downloaded+=len(block);f.need(downloaded<=ARCHIVE_BYTES and time.monotonic()-start<900,'release download bound');out.write(block)
            f.need(downloaded==ARCHIVE_BYTES,'official archive size differs')
            runtime=work/'runtime';inv=install_archive(archive,runtime);archive.unlink()
        f.need(f.sha(f.json_bytes(inv))==RUNTIME_INVENTORY_SHA,'canonical runtime inventory differs')
        actual={p.relative_to(runtime).as_posix() for p in runtime.rglob('*') if not p.is_dir() or p.is_symlink()}
        f.need(actual==set(inv['files'])|set(inv['symlinks']),'runtime has missing/extra entries')
        write_json(work/'evidence/runtime-inventory.json',inv)
        env=safe_env(runtime,work/'home',work/'tmp');env['MATHLIB_CACHE_DIR']=str(work/'cache')
        command('bwrap-preflight',sandbox(['/bin/true'],runtime=runtime,sources=[],writable=[work/'home',work/'tmp'],cwd=work/'tmp',env=env),seconds=30,env=env,allowed_sessions=True)
        curl,_=command('curl-version',['/usr/bin/curl','--disable','--version'],env=env,seconds=30)
        m=re.match(r'curl (\d+)\.(\d+)\.',curl.read_text());f.need(m and tuple(map(int,m.groups()))>=(7,81),'curl fallback download forbidden: approved system curl too old')
        pins=f.load_json(ROOT/'locks/dependencies.json')['packages'];validate_dependencies(pins);before={}
        for pin in pins:
            name=pin['name'];p=work/'packages'/name;p.mkdir()
            base=['/usr/bin/git','-c','core.hooksPath=/dev/null','-c','core.fsmonitor=false','-C',str(p)]
            command(name+'-init',base+['init','--quiet'],env=env,seconds=30)
            command(name+'-remote',base+['remote','add','origin',pin['url']],env=env,seconds=30)
            origin=str(a.local_dependencies/name) if a.local_dependencies else pin['url']
            if a.local_dependencies:source_snapshot(a.local_dependencies/name,pin)
            command(name+'-fetch',base+['fetch','--quiet','--depth=1','--no-tags',origin,pin['rev']],env=env,seconds=300)
            command(name+'-checkout',base+['checkout','--quiet','--detach',pin['rev']],env=env,seconds=60)
            before[name]=source_snapshot(p,pin)
            f.need(not (p/'.lake').exists(),'fresh checkout has prior Lake state')
            (p/'.lake/build').mkdir(parents=True);(p/'.lake/config').mkdir();(p/'.lake/packages').mkdir()
        mathlib=work/'packages/mathlib';manifest=f.load_json(mathlib/'lake-manifest.json')
        expected={p['name']:(p['url'],p['rev']) for p in pins if p['name']!='mathlib'}
        f.need({p['name']:(p['url'],p['rev']) for p in manifest['packages']}==expected,'Mathlib manifest differs from dependency allowlist')
        client=f.load_json(ROOT/'locks/cache-client.json')
        for row in client['files']:
            p=mathlib/row['path'];f.need(p.stat().st_size==row['bytes'] and f.file_sha(p)==row['sha256'],'cache client source pin differs')
        for pin in pins:
            p=work/'packages'/pin['name'];mp=p/'lake-manifest.json'
            if mp.exists():
                for dep in f.load_json(mp)['packages']:
                    f.need(dep['name'] in OFFICIAL_REPOS,'unexpected nested dependency')
                    (p/'.lake/packages'/dep['name']).symlink_to(work/'packages'/dep['name'],target_is_directory=True)
        write_json(work/'evidence/dependency-sources.json',before)
        writable=[work/'home',work/'tmp',work/'cache',*[work/'packages'/p['name']/'.lake' for p in pins]]
        kwargs=dict(runtime=runtime,sources=[work/'packages'],writable=writable,cwd=mathlib,env=env)
        # Bootstrap uses only authenticated source and runtime, with network off.
        command('cache-bootstrap',sandbox([runtime/'bin/lake','build','cache'],**kwargs),env=env,seconds=900,allowed_sessions=True)
        produced=mathlib/'.lake/build/bin/cache';f.need(produced.is_file(),'cache bootstrap did not produce executable')
        cache=work/'bootstrap/cache';shutil.copyfile(produced,cache);cache.chmod(0o555);cache_sha=f.file_sha(cache)
        kwargs['sources'].append(work/'bootstrap')
        write_json(work/'evidence/cache-client-binary.json',{'sha256':f.file_sha(cache),'bytes':cache.stat().st_size,'built_from_official_sources':True})
        roots=contract['cache_roots'];f.need(all(f.MODULE.fullmatch(x) for x in roots),'invalid cache root')
        f.need(shutil.disk_usage(work).free>=9*GIB,'insufficient measured disk for bounded cache acquisition')
        # Exact supported official trust chain. No forks, --unsafe, --scope, endpoint overrides.
        command('cache-get',sandbox([runtime/'bin/lake','env',cache,'get','--cache-from=master,legacy',*roots],network=True,**kwargs),env=env,seconds=1800,allowed_sessions=True)
        required=f.load_json(ROOT/'locks/required-modules.json')['modules']
        command('cache-lookup',sandbox([runtime/'bin/lake','env',cache,'lookup',*[x['module'] for x in required]],**kwargs),env=env,seconds=180,allowed_sessions=True)
        f.need(f.file_sha(cache)==cache_sha,'read-only bootstrap cache executable changed')
        cache_inv=checked_inventory(work/'cache',maximum=3*GIB)
        f.need(not any(Path(n).name.startswith('curl-') and not n.endswith('.cfg') for n in cache_inv['files']),'fallback curl executable is forbidden')
        write_json(work/'evidence/cache-downloads.json',cache_inv)
        inventories={};search=[]
        for pin in pins:
            name=pin['name'];p=work/'packages'/name
            f.need(source_snapshot(p,pin)==before[name],'official sources changed during cache acquisition')
            inventories[name]=checked_inventory(p/'.lake/build',maximum=4*GIB,allow_links=True)
            search.append(str(p/'.lake/build/lib/lean'))
        f.need(sum(i['bytes'] for i in inventories.values())<=5*GIB,'aggregate cached build bound')
        write_json(work/'evidence/cached-build-inventory.json',inventories)
        # Cache get can return zero on 404 misses. Admit the whole requested source closure.
        providers={}
        for pin in pins:
            lib=work/'packages'/pin['name']/'.lake/build/lib/lean'
            for obj in lib.rglob('*.olean'):
                m=obj.relative_to(lib).as_posix().removesuffix('.olean').replace('/','.')
                f.need(m not in providers,'duplicate cached module provider: '+m);providers[m]=pin['name']
        for row in required:
            name=row['package'];m=row['module'];rel=row['path']
            f.need(before[name]['files'][rel]['sha256']==row['sha256'],'required source closure differs')
            f.need(providers.get(m)==name,'missing or wrong cached module provider: '+m)
            stem=work/'packages'/name/'.lake/build/lib/lean'/m.replace('.','/')
            suffixes=['.olean','.ilean']+(['.olean.server','.olean.private','.ir.sig','.ir'] if row['modern_module'] else [])
            for suffix in suffixes:f.need(Path(str(stem)+suffix).is_file(),'missing required cached companion: '+m+suffix)
        for row in contract['diagnostics']:f.need(row['module'] not in providers,'cached object shadows owned module')
        owners=namespace_providers([Path(s) for s in search]+[runtime/'lib/lean'])
        for row in required:
            f.need(owners.get(row['module'].split('.')[0])==str(work/'packages'/row['package']/'.lake/build/lib/lean'),'required namespace has wrong provider')
        f.exact_tree(ROOT/'src',{name.removeprefix('src/') for name in contract['inputs'] if name.startswith('src/')})
        shutil.copytree(ROOT/'src',work/'src');owned_before=checked_inventory(work/'src',maximum=1024**2)
        env['LEAN_PATH']=':'.join([str(work/'objects'),*search,str(runtime/'lib/lean')])
        prior={};expected_outputs=set()
        for entry in contract['diagnostics']:
            module=entry['module'];rel=module.replace('.','/');target=work/'objects'/(rel+'.olean');target.parent.mkdir(parents=True,exist_ok=True)
            argv=[runtime/'bin/lean','-j1','-M1024','-Dcompiler.postponeCompile=false','-o',target,'-i',work/'objects'/(rel+'.ilean'),'-c',work/'objects'/(rel+'.c'),work/'src'/(rel+'.lean')]
            kw=dict(runtime=runtime,sources=[work/'packages',work/'src'],writable=[work/'objects',work/'home',work/'tmp'],cwd=work/'src',env=env)
            namespace_providers([work/'objects',*[Path(s) for s in search],runtime/'lib/lean'])
            verify_prior_outputs(work/'objects',prior)
            command('compile-'+module,sandbox(argv,**kw),env=env,seconds=120,rss=2*GIB,allowed_sessions=True)
            for suffix in ['.olean','.olean.private','.olean.server','.ilean','.ir.sig','.ir','.c']:
                f.need((work/'objects'/(rel+suffix)).is_file(),'diagnostic missing fresh companion: '+module+suffix)
            now=verify_prior_outputs(work/'objects',prior)
            expected_outputs.update(rel+x for x in ['.olean','.olean.private','.olean.server','.ilean','.ir.sig','.ir','.c'])
            f.need(set(now)==expected_outputs,'unexpected fresh output path')
            command('check-'+module,sandbox([runtime/'bin/leanchecker',module],**kw),env=env,seconds=120,rss=2*GIB,allowed_sessions=True)
            prior=verify_prior_outputs(work/'objects',now)
        f.need(time.monotonic()<deadline,'diagnostic aggregate deadline exceeded')
        f.need(checked_inventory(work/'src',maximum=1024**2)==owned_before,'owned diagnostic source changed')
        for pin in pins:
            name=pin['name'];p=work/'packages'/name
            f.need(source_snapshot(p,pin)==before[name],'dependency source changed during consumers')
            f.need(checked_inventory(p/'.lake/build',maximum=4*GIB,allow_links=True)==inventories[name],'cached dependency bytes changed during consumers')
        write_json(work/'evidence/fresh-diagnostic-objects.json',checked_inventory(work/'objects',maximum=64*1024**2))
        bridge=(work/'logs/compile-ContractModelBridgeSmoke.stdout').read_text()
        f.need('sorryAx' not in bridge,'bridge diagnostic depends on a Challenge hole')
        for theorem in ['curved_model_eq','keyed_product_model_eq']:
            f.need(theorem in bridge,'bridge axiom audit was not printed')
        result['status']='CACHE_BACKED_DIAGNOSTIC_ELABORATION_COMPLETED';result['challenge_holes_intentional']=True
    except Exception as e:
        result['error']=str(e);raise
    finally:
        write_json(work/'evidence/result.json',result)
        # Upload bounded evidence only, never cache objects or unrelated files.
        for p in sorted((work/'logs').glob('*')):
            with p.open('rb') as h:
                h.seek(max(0,p.stat().st_size-256*1024));b=h.read(256*1024)
            q=work/'evidence/logs'/p.name;q.parent.mkdir(exist_ok=True);q.write_bytes(b)
        checked_inventory(work/'evidence',maximum=32*1024**2)

if __name__=='__main__':main()
