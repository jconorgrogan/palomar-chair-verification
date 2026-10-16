#!/usr/bin/env python3
"""Bounded cache-backed conditional geometry replay. C remains an explicit premise."""
from __future__ import annotations
import argparse,signal,tarfile,zlib,hashlib,importlib.util,json,os,re,shutil,stat,subprocess,sys,time,urllib.request
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
# Workflow invokes Python -I -B. Check code bytes before loading vendored helpers.
HELPERS={'fresh_stage.py':'0887e6a69ae7a80c2ef4c1ee841b48d50f7eb8c58736c0396ea15e0402279d99',
 'toolchain_install.py':'9b8fefa2020be7e58bbf04f79445f603657bd647c0afe0b1196078f92629f038',
 'collect_evidence.py':'7ca7a19ee3916e344f00539e41cd17614c4bfd2982b466eca84f82b64f4c1851',
 'conditional_transport.py':'d216f92df7c50ab14666923da37afd1dd47290178325b521a44f0360b4b02b1f',
 'source_header.py':'3eca76608279cbd7fb659eec960177bed6e7ad4829c5e5636f6ad23636645701'}
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
header_parser=load_helper('source_header')
transport=load_helper('conditional_transport')
install_archive=load_helper('toolchain_install').install_archive
GIB=1024**3
DIAGNOSTIC_HEAP_MIB=4096
DIAGNOSTIC_RSS_BYTES=8*GIB
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

OFFICIAL_SOURCE_LINKS={
 'mathlib':{
  'scripts/bench/build/fake-root/bin/lean.py':('lean','scripts/bench/build/fake-root/bin/lean','819298943e1a8c331413fb55e2c4bbc98d05e562'),
  'scripts/bench/size/run.py':('run','scripts/bench/size/run','e5224d533ef27b001224859a9b36696846a7e7fe')},
 'batteries':{'docs/README.md':('../README.md','README.md','32d46ee883b58d6a383eed06eb98f33aa6530ded')}}

def validate_source_links(rows):
    for rel,row in rows.items():
        if row['kind']=='symlink':
            target=rows.get(row['resolved_source_path'])
            f.need(target is not None and target['kind']=='regular','source symlink target is not a pinned regular Git entry')

def source_blob(repo,rel,mode,oid):
    p=repo/f.safe_rel(rel);f.no_symlink_path(p.parent)
    if mode=='120000':
        f.need(p.is_symlink(),'pinned source symlink replaced by ordinary file')
        expected=OFFICIAL_SOURCE_LINKS.get(repo.name,{}).get(rel)
        f.need(expected is not None and oid==expected[2],'source symlink not in exact official pin allowlist')
        target=os.readlink(p);f.need(target==expected[0],'official symlink target bytes changed')
        resolved=expected[1];endpoint=repo/resolved;f.no_symlink_path(endpoint)
        f.need(endpoint.is_file(),'official symlink endpoint is not a regular file')
        data=target.encode('utf-8')
        extra={'kind':'symlink','target':target,'resolved_source_path':resolved}
    else:
        f.need(mode in ('100644','100755') and not p.is_symlink() and p.is_file(),'unsupported or replaced regular source')
        data=p.read_bytes();extra={'kind':'regular'}
    actual=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
    f.need(actual==oid,'official source does not equal pinned Git blob')
    return {'bytes':len(data),'sha256':f.sha(data),'git_blob':oid,'git_mode':mode,**extra}

def source_snapshot(repo,pin):
    f.need(git_capture(repo,'rev-parse','HEAD').decode().strip()==pin['rev'],'dependency HEAD differs')
    f.need(git_capture(repo,'remote','get-url','origin').decode().strip()==pin['url'],'dependency origin differs')
    f.need(not git_capture(repo,'status','--porcelain=v1','--untracked-files=all'),'dependency worktree changed')
    rows={};total=0
    for entry in git_capture(repo,'ls-tree','-rz','HEAD').split(b'\0'):
        if not entry:continue
        meta,name=entry.split(b'\t',1);mode,kind,oid=meta.decode().split();rel=name.decode();f.safe_rel(rel)
        f.need(kind=='blob' and mode in ('100644','100755','120000'),'unsupported official source entry: '+rel)
        rows[rel]=source_blob(repo,rel,mode,oid);total+=rows[rel]['bytes']
        f.need(total<=512*1024**2,'official source snapshot bound')
    validate_source_links(rows)
    return {'revision':pin['rev'],'repository':pin['url'],'files':rows,'bytes':total}

def validate_dependencies(pins):
    f.need(len(pins)==9 and {p['name'] for p in pins}==set(OFFICIAL_REPOS),'dependency allowlist differs')
    for p in pins:
        f.need(f.COMMIT.fullmatch(p['rev']) and p['subDir'] is None,'mutable or subdirectory pin')
        f.need(p['url'].removesuffix('.git')=='https://github.com/'+OFFICIAL_REPOS[p['name']],'unofficial dependency URL')

ALLOWED_AXIOMS={'propext','Classical.choice','Quot.sound'}
ENDPOINTS=['NativeFinalAssembly.CurvedOfParent','NativeFinalAssembly.KeyedProductOfParent']
ENDPOINT_THEOREMS=['NativeFinalAssembly.curved_monotile_of_parent','NativeFinalAssembly.keyed_product_monotile_of_parent']
BRIDGES=['KernelCurvedPilot.CurvedGeometryAndTiling','KernelCurvedParentPilot.CurvedPeriodFromParent','KernelSeedPilot.ProductPhysicalExistence','KernelParentPilot.ProductAperiodicityFromParent']
SUFFIXES=['.olean','.olean.private','.olean.server','.ilean','.ir.sig','.ir','.c']
SUCCESS='CACHE_BACKED_CONDITIONAL_GEOMETRY_REPLAY_COMPLETED'
STAGE_SUCCESS='CHECKED_CONDITIONAL_STAGE_COMPLETED_C_EXPLICIT'

CONTINUATION_SCHEMA='conditional-geometry-origin-continuation-v3'
ORIGINAL_STAGE_CONTRACT_SHA='cbba2b835ef2578ad4810068cab863918af442d5fa30abea5cafcfa78ce35a38'
ASYNC_TARGET='SpectreGeometry.PolygonProductKeyReferenceFinite'
ASYNC_TARGET_SHA='1bca6dbb7f17e7a897293c3cf8da9b5d686c02245ac5230be3b27c108953a45b'

def module_compile_arguments(contract,module):
    """A pinned, source-local scheduling exception, never a global Lean option."""
    if contract.get('schema')==CONTINUATION_SCHEMA:
        expected={ASYNC_TARGET:['-DElab.async=false']}
        f.need(contract.get('module_compile_arguments')==expected,'module scheduling exception differs')
        f.need(contract['inputs']['src/'+ASYNC_TARGET.replace('.','/')+'.lean']['sha256']==ASYNC_TARGET_SHA,'scheduled source bytes differ')
        return list(expected.get(module,[]))
    f.need(contract.get('schema')=='conditional-geometry-staged-replay-v2' and
           'module_compile_arguments' not in contract,'unrecognized producer scheduling policy')
    return []

def validate_diagnostic_profile(contract):
    expected={'schema':'conditional-geometry-staged-replay-v2','owned_module_count':2481,
      'finite_prerequisite_count':333,'owned_geometry_count':2144,'ordinary_bridge_count':4,
      'conditional_endpoint_count':2,'lean_heap_mib':4096,'diagnostic_rss_gib':8,
      'diagnostic_timeout_seconds':180,'check_timeout_seconds':120,'outer_timeout_minutes':330,
      'aggregate_command_deadline_seconds':19200,'maximum_parallel_jobs':3,
      'stage_count':5,'workflow_aggregate_seconds':96000,'workflow_outer_runner_minutes':1650,
      'object_artifact_max_bytes':4*GIB,'object_artifact_zip_max_bytes':4*GIB+4*1024**2,
      'producer_job_log_max_bytes':16*1024**2,'transport_timeout_seconds':1800,'failure_evidence_grace_seconds':5,
      'owned_output_max_bytes':6*GIB,'owned_source_max_bytes':32*1024**2,
      'evidence_max_bytes':124*1024**2,'aggregate_log_max_bytes':64*1024**2,
      'per_command_log_max_bytes':1024**2,'minimum_free_disk_bytes':1536*1024**2,
      'auditor_timeout_seconds':600,'cache_module_count':2786}
    continuation=contract.get('schema')==CONTINUATION_SCHEMA
    if continuation:
        expected.update(schema=CONTINUATION_SCHEMA,maximum_parallel_jobs=1,
          workflow_aggregate_seconds=38400,workflow_outer_runner_minutes=660)
        f.need(contract.get('workflow_job_count')==2 and contract.get('execution_stages')==['F3_product_geometry','F4_bridge_and_endpoint_joins'],'continuation job graph differs')
        f.need(contract.get('locked_origin_stages')==['F0_common','F1_curved_existence','F2_period_hierarchy'],'locked producer stage set differs')
        module_compile_arguments(contract,ASYNC_TARGET)
    for key,value in expected.items():f.need(type(contract.get(key)) is type(value) and contract.get(key)==value,'conditional replay profile mismatch: '+key)
    for key,value in {'conditional_C_remains_explicit':True,'final_C_proof_certified':False,
        'unconditional_monotile_proof_certified':False,'fresh_external_source_rebuild':False,
        'owned_objects_from_prior_runs_allowed':continuation,'owned_objects_from_same_run_checked_stages_allowed':True}.items():
        f.need(contract.get(key) is value,'conditional replay trust/scope changed: '+key)
    f.need(contract['conditional_endpoints']==ENDPOINTS and contract['endpoint_theorems']==ENDPOINT_THEOREMS,'endpoint contract differs')
    f.need(set(contract['ordinary_bridges'])==set(BRIDGES),'ordinary bridge set differs')


def distribution_files(contract):
    expected={p for p in contract['inputs'] if not p.startswith('src/')}|{'contract.json','.github/workflows/conditional-geometry.yml','owned-sources.tar.gz'}
    f.need(contract['distribution_files']==sorted(expected) and len(expected)==contract.get('distribution_file_count',29),'distribution manifest differs')
    return expected


def validate_distribution_layout(contract):
    expected=distribution_files(contract);actual=set();allowed_dirs={str(parent) for rel in expected for parent in Path(rel).parents if str(parent)!='.'}
    # Only the root Git metadata directory is excluded. Nested .git paths,
    # empty shadow directories, links and nonregular entries fail closed.
    for parent,dirs,files in os.walk(ROOT,followlinks=False):
        parent=Path(parent)
        if parent==ROOT and '.git' in dirs:dirs.remove('.git')
        for name in dirs:
            p=parent/name;rel=p.relative_to(ROOT).as_posix()
            f.need(not p.is_symlink() and rel in allowed_dirs,'unexpected distribution directory')
        for name in files:
            p=parent/name;rel=p.relative_to(ROOT).as_posix();st=p.lstat()
            f.need(stat.S_ISREG(st.st_mode) and st.st_nlink==1,'nonregular distribution entry')
            actual.add(rel)
    f.need(actual==expected,'unexpected or missing diagnostic distribution file')


def extract_owned_sources(archive,destination,contract):
    """Authenticate once, bound decompression, then write only pinned regular files.

    No tar extraction API runs. Canonical USTAR headers are parsed individually;
    extensions, links, directories, path aliases and unlisted entries are refused.
    A rejected partial destination is never resumed by the fresh-workspace runner.
    """
    lock=contract['source_archive'];pins={p:r for p,r in contract['inputs'].items() if p.startswith('src/')};expected=sorted(pins)
    f.need(lock['format']=='single-gzip-canonical-ustar-regular-sources-v1' and lock['path']=='owned-sources.tar.gz','source archive format/path differs')
    f.need(len(pins)==lock['source_file_count']==contract['owned_module_count'],'source archive file count differs')
    source_bytes=0;tar_bytes=1024
    for rel,row in pins.items():
        f.safe_rel(rel)
        f.need(rel.startswith('src/') and rel.endswith('.lean'),'invalid source archive path')
        f.need(type(row['bytes']) is int and 0<=row['bytes']<=contract['owned_source_max_bytes'],'source member size bound')
        source_bytes+=row['bytes'];tar_bytes+=512+((row['bytes']+511)//512)*512
    tar_bytes=((tar_bytes+10239)//10240)*10240
    f.need(source_bytes==lock['source_bytes'] and source_bytes<=contract['owned_source_max_bytes'],'source archive expanded source bound')
    f.need(type(lock['tar_bytes']) is int and lock['tar_bytes']==tar_bytes<=64*1024**2,'source tar framing bound')
    f.need(type(lock['bytes']) is int and 0<lock['bytes']<=8*1024**2,'source compressed byte bound')
    f.no_symlink_path(archive);st=archive.lstat()
    f.need(stat.S_ISREG(st.st_mode) and st.st_nlink==1 and st.st_size==lock['bytes'],'source archive file/size differs')
    with archive.open('rb') as stream:compressed=stream.read(lock['bytes']+1)
    f.need(len(compressed)==lock['bytes'] and f.sha(compressed)==lock['sha256'],'source archive hash differs')
    decoder=zlib.decompressobj(31)
    data=decoder.decompress(compressed,tar_bytes+1)
    f.need(len(data)==tar_bytes and decoder.eof and not decoder.unconsumed_tail and not decoder.unused_data,'source archive truncated, oversized, or has trailing gzip data')
    f.no_symlink_path(destination);f.need(not destination.exists(),'source extraction destination must be new');destination.mkdir()
    offset=0;seen=[]
    for rel in expected:
        block=data[offset:offset+512];f.need(len(block)==512 and block!=bytes(512),'missing source archive member')
        info=tarfile.TarInfo.frombuf(block,encoding='utf-8',errors='strict')
        f.need(info.type==tarfile.REGTYPE and not info.linkname and not info.pax_headers,'nonregular or extended source archive member')
        f.need(info.name==rel and info.name not in seen,'unordered, duplicate, extra, or aliased source archive path')
        f.safe_rel(info.name)
        f.need(info.size==pins[rel]['bytes'],'source archive member size differs')
        f.need(info.mode==0o644 and info.uid==info.gid==info.mtime==0 and info.uname==info.gname=='' and info.devmajor==info.devminor==0,'noncanonical source archive metadata')
        f.need(info.tobuf(format=tarfile.USTAR_FORMAT,encoding='utf-8',errors='strict')==block,'noncanonical source archive header')
        offset+=512;content=data[offset:offset+info.size];f.need(len(content)==info.size and f.sha(content)==pins[rel]['sha256'],'source archive member hash differs')
        padded=((info.size+511)//512)*512
        f.need(data[offset+info.size:offset+padded]==bytes(padded-info.size),'nonzero source archive padding')
        target=destination/f.safe_rel(rel);f.no_symlink_path(target);target.parent.mkdir(parents=True,exist_ok=True)
        with target.open('xb') as out:out.write(content)
        target.chmod(0o444);seen.append(rel);offset+=padded
    f.need(len(data)-offset>=1024 and data[offset:]==bytes(len(data)-offset),'extra source archive member or nonzero trailer')
    f.exact_tree(destination,set(expected))
    for rel,row in pins.items():
        p=destination/rel;f.need(p.stat().st_size==row['bytes'] and f.file_sha(p)==row['sha256'],'extracted source pin differs')
    return {'schema':'authenticated-source-extraction-v1','archive':lock,'source_file_count':len(seen),'source_bytes':source_bytes,'exact_source_tree':True,'all_source_pins_verified':True}


def validate_owned_graph(contract,owned,required,source_root=ROOT):
    rows=owned['sources'];names=[r['module'] for r in rows];order=owned['module_order']
    f.need(len(names)==2481 and len(set(names))==len(names),'owned module count or uniqueness differs')
    f.need(names==order==[r['module'] for r in contract['modules']],'owned topological order differs')
    f.need(order[-2:]==ENDPOINTS,'both conditional assemblies must be the final owned modules')
    f.need(order[0]==contract.get('early_static_visibility_test_module')=='SpectreGeometry.DeformationHomeomorphism','early independent visibility test order differs')
    f.need(owned['conditional_C_remains_explicit'] is True and owned['no_final_C_proof_module'] is True,'conditional scope differs')
    f.need(sum(r['role']=='finite_C_source' for r in rows)==333,'finite prerequisite scope differs')
    f.need(sum(r['role']=='ordinary_owned_source' for r in rows)==2142,'geometry prerequisite scope differs')
    f.need([r['module'] for r in rows if r['role']=='conditional_assembly']==ENDPOINTS,'conditional role differs')
    f.need({r['module'] for r in rows if r['role']=='uncompiled_ordinary_bridge_replacement'}==set(BRIDGES),'bridge role differs')
    f.need(not set(names).intersection({'ClosedCurvedFinal','ClosedKeyedProductFinal','SpectreFinite.RadiusFivePruningHierarchy'}),'unconditional proof source is forbidden')
    cache_names={r['module'] for r in required['modules']};runtime=set(contract['runtime_roots'])
    f.need(runtime==set(owned['runtime_roots'])==set(required['runtime_roots'])=={'Init','Init.Data.Rat'},'direct runtime boundary differs')
    f.need(len(cache_names)==len(required['modules'])==2786,'cached module count or uniqueness differs')
    f.need(required['roots']==contract['cache_roots'] and set(required['roots'])<=cache_names,'cache root lock differs')
    f.need(not cache_names.intersection(names),'cached module shadows owned source')
    seen=set();external=set();source_paths=set();graph={r['module']:r['ordered_imports'] for r in rows}
    for row in rows:
        mod=row['module'];f.need(f.MODULE.fullmatch(mod),'invalid owned module name')
        rel='src/'+mod.replace('.','/')+'.lean';f.need(row['path']==rel,'owned source path alias')
        f.need(contract['inputs'].get(rel)=={'bytes':row['bytes'],'sha256':row['sha256']},'owned source and contract pin differ')
        parsed=header_parser.header((source_root/rel).read_bytes())
        f.need(parsed['modern'] and not parsed['prelude'],'owned source must be modern with Init')
        f.need([x['module'] for x in parsed['imports']]==row['ordered_imports'],'actual source import header differs')
        for dep in row['ordered_imports']:
            f.need(f.MODULE.fullmatch(dep),'invalid owned import')
            f.need(dep in seen or dep in cache_names or dep in runtime,'unordered or unresolved owned import: '+mod+' -> '+dep)
            if dep in cache_names:external.add(dep)
        seen.add(mod);source_paths.add(rel)
    needed=set()
    def visit(n):
        if n in needed or n not in graph:return
        needed.add(n)
        for dep in graph[n]:visit(dep)
    for n in ENDPOINTS:visit(n)
    f.need(needed==set(names),'owned union has unreachable extras or missing dependencies')
    f.need(external==set(contract['cache_roots']),'direct external import boundary differs')
    f.need(source_paths=={p for p in contract['inputs'] if p.startswith('src/')},'extra or missing owned source pin')


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


def direct_import_receipt(row,owned_rows,checked,prior,cache_rows,runtime):
    imports=[]
    for dep in dict.fromkeys([*row['ordered_imports'],'Init']):
        if dep in owned_rows:
            f.need(dep in checked,'owned import lacks a successful fresh checker receipt: '+dep)
            payload={p:prior[p] for p in sorted(module_outputs(dep))}
            imports.append({'module':dep,'provider':'fresh_owned','companions':payload})
        elif dep in cache_rows:
            imports.append({'module':dep,'provider':'explicitly_trusted_official_cache','source_sha256':cache_rows[dep]['sha256'],'companions':cache_rows[dep]['companions']})
        else:
            f.need(dep.startswith(('Init','Lean','Lake','Std')),'unknown runtime import')
            target=runtime/'lib/lean'/(dep.replace('.','/')+'.olean')
            f.need(target.is_file(),'runtime boundary object missing')
            imports.append({'module':dep,'provider':'official_runtime','object_sha256':f.file_sha(target)})
    return imports


def verify_owned_final(objects,prior,maximum):
    f.exact_tree(objects,set(prior))
    now=checked_inventory(objects,maximum=maximum)
    f.need(now['files']==prior,'committed owned output changed, disappeared, or acquired extra files')
    return now


def require_success_commands(commands):
    for r in commands:
        f.need(r['exit_code']==0 and not any(r[k] for k in ['timed_out','log_overflow','memory_exceeded','surviving_children']) and r['process_group_empty'] and r['descendants_empty'] and not (r['escaped_descendants'] and not r['new_sessions_explicitly_allowed']),'terminal receipt contains unsuccessful command')


def validate_terminal_receipt(result,commands,owned_rows,receipts,audits,*,final=True):
    f.need(result['conditional_C_remains_explicit'] is True and result['final_C_proof_certified'] is False and result['unconditional_monotile_proof_certified'] is False,'terminal conditional scope weakened')
    require_success_commands(commands)
    expected=[(phase,r['module']) for r in owned_rows for phase in ['compile','check']]
    actual=[]
    for command in commands:
        for phase in ['compile','check']:
            if command['name'].startswith(phase+'-') and not command['name'].startswith(phase+'-auditor-'):
                actual.append((phase,command['name'].removeprefix(phase+'-')))
    f.need(actual==expected,'missing, duplicated, or reordered compile/check pair')
    f.need([r['module'] for r in receipts]==[r['module'] for r in owned_rows] and all(r['checker_passed'] is True for r in receipts),'fresh module receipt coverage differs')
    f.need(audits==({'ordinary_bridges':True,'conditional_endpoints':True} if final else {}),'mandatory raw audits missing or premature')

def audit_axiom_output(transcript,theorems):
    f.need('sorryAx' not in transcript,'bridge diagnostic depends on a Challenge hole')
    records={}
    matches=list(re.finditer(r"(?m)^'([^'\n]+)' depends on axioms:\s*\[([^\]]*)\]\s*$",transcript))
    for match in matches:
        name=match.group(1);f.need(name not in records,'duplicate axiom audit for '+name)
        axioms=[a.strip() for a in match.group(2).split(',') if a.strip()]
        f.need(len(axioms)==len(set(axioms)) and set(axioms)<=ALLOWED_AXIOMS,'nonstandard bridge axiom')
        records[name]=axioms
    for match in re.finditer(r"(?m)^'([^'\n]+)' does not depend on any axioms\s*$",transcript):
        name=match.group(1);f.need(name not in records,'duplicate axiom audit for '+name);records[name]=[]
    f.need(set(records)==set(theorems) and len(theorems)==len(set(theorems)),'missing or unexpected bridge theorem axiom audit')
    return records

def audit_endpoint_output(transcript):
    lines=transcript.splitlines()
    f.need(lines and lines[-1]=='CONDITIONAL_ENDPOINT_AUDIT_PASSED' and lines.count('CONDITIONAL_ENDPOINT_AUDIT_PASSED')==1,'conditional audit marker absent, duplicated, or nonterminal')
    records=[f.parse_json(x.encode()) for x in lines if x.startswith('{')]
    f.need(len(records)==2,'conditional endpoint record count differs')
    for i,row in enumerate(records):
        expected={'status':'CONDITIONAL_ENDPOINT_PASSED','theorem':ENDPOINT_THEOREMS[i],
          'module':ENDPOINTS[i],'universe_parameters':[],'explicit_C_binders':1,
          'C_type':'SpectreFinite.HexSearch.NativeHierarchy.ParentOccurrenceTheorem',
          'exact_raw_type':True,'closed_type_and_proof':True,'C_definition_expansion':True,
          'exact_module_owned_set':True,'small_semantic_anchors_only':True}
        f.need(set(row)==set(expected)|{'transitive_axioms'},'unexpected or missing endpoint audit field')
        for key,value in expected.items():
            f.need(type(row[key]) is type(value) and row[key]==value,'conditional endpoint audit differs: '+key)
        axioms=row['transitive_axioms']
        f.need(isinstance(axioms,list) and all(isinstance(x,str) for x in axioms) and len(axioms)==len(set(axioms)) and set(axioms)<=ALLOWED_AXIOMS,'endpoint audit contains nonstandard or duplicate axioms')
    return records


def audit_bridge_output(transcript):
    names=['KernelCurvedPilot.existing_curved_geometry_and_tiling',
      'KernelCurvedParentPilot.curved_period_eq_zero_of_parent',
      'KernelSeedPilot.existing_physical_product_tiling',
      'KernelParentPilot.physical_polygon_product_period_eq_zero_of_parent']
    expected_raw={'EXACT_RAW_TYPE_PROOF_UNIVERSES_AXIOMS: '+n for n in names}
    expected_owned={'EXACT_MODULE_OWNED_SET: '+m+': '+n for m,n in zip(BRIDGES,names)}
    lines=transcript.splitlines()
    f.need(lines and lines[-1]=='ALL_FOUR_EXACT_RAW_BRIDGE_CONTRACTS_PASSED' and lines.count(lines[-1])==1,'bridge audit marker absent, duplicated, or nonterminal')
    raw=[x for x in lines if x.startswith('EXACT_RAW_TYPE_PROOF_UNIVERSES_AXIOMS:')]
    owned=[x for x in lines if x.startswith('EXACT_MODULE_OWNED_SET:')]
    f.need(len(raw)==4 and set(raw)==expected_raw and len(owned)==4 and set(owned)==expected_owned,'bridge audit record coverage differs')
    return {'theorems':names,'exact_raw_type_and_proof':True,'exact_module_owned_sets':True,
      'axioms_checked_by_core_auditor':sorted(ALLOWED_AXIOMS),'individual_axiom_sets_not_printed':True}


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


def validate_stage_plan(contract):
    stages=contract['stages'];order=contract['stage_order']
    expected=['F0_common','F1_curved_existence','F2_period_hierarchy','F3_product_geometry','F4_bridge_and_endpoint_joins']
    f.need(order==expected and set(stages)==set(order),'stage identity/order differs')
    counts=[186,890,1226,109,70];all_modules=[];seen_stages=[];owner={}
    for sid,count in zip(order,counts):
        row=stages[sid];names=row['modules']
        f.need(len(names)==count and len(set(names))==count,'stage count/duplicate differs')
        f.need(row['needs']==([] if sid==order[0] else order[:-1] if sid==order[-1] else [order[0]]),'stage dependency graph differs')
        ancestors=set(row['needs'])
        for dep in row['needs']:ancestors.update(stages[dep]['admitted_stages'])
        f.need(row['admitted_stages']==[x for x in seen_stages if x in ancestors],'stage ancestor admission differs')
        for module in names:
            f.need(module not in owner,'owned module scheduled twice');owner[module]=sid
        all_modules+=names;seen_stages.append(sid)
    f.need(set(all_modules)=={r['module'] for r in contract['modules']} and len(all_modules)==2481,'stage partition differs from exact owned union')
    f.need(contract['final_stage']==order[-1],'wrong final audit stage')
    owned=f.load_json(ROOT/'locks/owned-sources.json')['sources'];rows={r['module']:r for r in owned}
    for sid in order:
        available={m for dep in stages[sid]['admitted_stages'] for m in stages[dep]['modules']}
        for module in stages[sid]['modules']:
            for dep in rows[module]['ordered_imports']:
                f.need(dep not in owner or dep in available,'stage imports unaccepted owned module')
            available.add(module)

def validate_session_policy(name,argv,allowed,work,contract):
    """Explicit authorization, not retrospective acceptance of a cleanup race."""
    is_sandbox=argv[0]=='/usr/bin/bwrap'
    if is_sandbox:
        f.need(name in {'bwrap-preflight','read-only-committed-root-preflight','cache-bootstrap','cache-get','cache-lookup'} or name.startswith(('compile-','check-','audit-')),'unrecognized sandbox command')
        f.need('--new-session' in argv and '--unshare-all' in argv,'sandbox session topology changed')
    is_fetch=False
    pins=f.load_json(ROOT/'locks/dependencies.json')['packages']
    for pin in pins:
        if name==pin['name']+'-fetch':
            expected=['/usr/bin/git','-c','core.hooksPath=/dev/null','-c','core.fsmonitor=false','-C',str(work/'packages'/pin['name']),'fetch','--quiet','--depth=1','--no-tags',pin['url'],pin['rev']]
            f.need(argv==expected,'official fetch argv differs from pinned allowlist');is_fetch=True
    f.need(type(allowed) is bool and allowed==(is_sandbox or is_fetch),'unapproved or missing explicit session policy')

def cache_interface_identity(cache_rows,inventories,runtime_sha):
    native={}
    for package,inventory in inventories.items():
        for name,row in inventory['files'].items():
            if re.search(r'\.(?:so(?:\.[0-9.]+)?|a|dylib|dll)$',name):
                f.need(set(row)=={'bytes','sha256'},'native library symlink is not an admissible cross-stage interface')
                native[package+'/'+name]=row
    return {'schema':'conditional-external-interface-v1','runtime_inventory_sha256':runtime_sha,
      'required_cache_companion_rows_sha256':f.sha(f.json_bytes(cache_rows)),
      'all_package_native_library_files_sha256':f.sha(f.json_bytes(native))}

def stage_identity():
    return {'repository':os.environ['GITHUB_REPOSITORY'],'run_id':os.environ['GITHUB_RUN_ID'],
      'run_attempt':os.environ['GITHUB_RUN_ATTEMPT'],'workflow_commit':os.environ['GITHUB_SHA']}

def validate_continuation_origins(contract):
    f.need(contract['schema']==CONTINUATION_SCHEMA,'origin lock requires continuation schema')
    producer=f.pinned_load(ROOT/'origin/producer-contract.json',ORIGINAL_STAGE_CONTRACT_SHA)
    validate_diagnostic_profile(producer);validate_stage_plan(producer)
    for key in ['modules','stages','stage_order','final_stage','source_archive','cache_roots','conditional_endpoints','endpoint_theorems','ordinary_bridges','official_lean_inventory_sha256']:
        f.need(contract[key]==producer[key],'producer/consumer source or interface contract differs: '+key)
    old_sources={n:r for n,r in producer['inputs'].items() if n.startswith('src/')}
    new_sources={n:r for n,r in contract['inputs'].items() if n.startswith('src/')}
    f.need(new_sources==old_sources,'producer/consumer exact source pins differ')
    for name in ['lean-toolchain','locks/dependencies.json','locks/cache-client.json','locks/owned-sources.json','locks/required-modules.json','locks/source-lineage.json','locks/visibility-exception.json','locks/visibility-predictions.json','locks/auditor-variants.json','auditors/AuditOrdinaryBridges.lean','auditors/AuditConditionalEndpoints.lean']:
        f.need(contract['inputs'][name]==producer['inputs'][name],'producer/consumer immutable input differs: '+name)
    pointer=contract['origin_lock']
    f.need(set(pointer)=={'path','bytes','sha256'} and pointer['path']=='origin/locked-origins.json' and
           contract['inputs'][pointer['path']]=={'bytes':pointer['bytes'],'sha256':pointer['sha256']},'origin lock pointer differs')
    f.need((ROOT/pointer['path']).stat().st_size==pointer['bytes'],'origin lock byte size differs')
    lock=f.pinned_load(ROOT/pointer['path'],pointer['sha256'])
    f.need(set(lock)=={'schema','producer_contract_sha256','stages'} and lock['schema']=='conditional-exact-origin-lock-v1' and
           lock['producer_contract_sha256']==ORIGINAL_STAGE_CONTRACT_SHA and
           set(lock['stages'])==set(contract['locked_origin_stages']),'origin lock stage/contract coverage differs')
    identity={'repository':'jconorgrogan/palomar-chair-verification','run_id':'38914223883','run_attempt':'1','workflow_commit':'318a6900eabfec550b4adf1b0f4bd634c20d67c5'}
    for sid,row in lock['stages'].items():
        transport.validate_origin_lock(row['origin'])
        f.need(set(row)=={'origin','receipt_sha256','checked_module_receipts_sha256','descriptor_sha256','stage_tar_sha256','stage_tar_bytes','independent_review_sha256'},'locked origin row schema differs')
        f.need(row['origin']['identity']==identity and row['origin']['stage_id']==sid and row['origin']['workflow_id']==386423911,'locked original producer identity differs')
        for key in ['receipt_sha256','checked_module_receipts_sha256','descriptor_sha256','stage_tar_sha256','independent_review_sha256']:
            f.need(isinstance(row[key],str) and f.SHA256.fullmatch(row[key]),'locked producer digest missing: '+key)
        f.need(type(row['stage_tar_bytes']) is int and 0<row['stage_tar_bytes']<=contract['object_artifact_max_bytes'],'locked producer tar size bound')
    return producer,lock['stages']


def cross_origin_certificate(contract,contract_sha,identity,stage_id,interface,lineage,inventory):
    collector=load_helper('collect_evidence')
    return collector.make_cross_origin_certificate(contract,contract_sha,identity,stage_id,interface,lineage,inventory,collector.locked_origin_rows(contract))


def restore_stages(work,contract,contract_sha,stage_id,interface,owned_rows,cache_rows,runtime,deadline):
    prior={};checked=set();lineage=[]
    ancestors=contract['stages'][stage_id]['admitted_stages']
    if not ancestors:return prior,checked,lineage
    producer_contract,locked=validate_continuation_origins(contract)
    import_deadline=min(deadline,time.monotonic()+contract['transport_timeout_seconds'])
    root=work/'stage-imports';root.mkdir()
    search=[str(work/'packages'/p['name']/'.lake/build/lib/lean') for p in f.load_json(ROOT/'locks/dependencies.json')['packages']]
    for sid in ancestors:
        origin_row=locked.get(sid)
        selected_contract=producer_contract if origin_row is not None else contract
        selected_sha=ORIGINAL_STAGE_CONTRACT_SHA if origin_row is not None else contract_sha
        producer=selected_contract['stages'][sid];download=root/(sid+'-download')
        f.need(origin_row is not None or sid=='F3_product_geometry','unlocked earlier producer stage')
        client=transport.Transport(deadline=import_deadline,origin_lock=origin_row['origin'] if origin_row is not None else None)
        origin=client.download_stage(sid,'conditional '+sid,download,contract['object_artifact_max_bytes'])
        if origin_row is not None:
            f.need(origin==origin_row['origin'],'downloaded origin differs from exact lock')
            descriptor=f.load_json(download/'descriptor.json')
            f.need(f.file_sha(download/'descriptor.json')==origin_row['descriptor_sha256'] and
                   descriptor['archive_sha256']==origin_row['stage_tar_sha256'] and descriptor['archive_bytes']==origin_row['stage_tar_bytes'] and
                   descriptor['receipt_sha256']==origin_row['receipt_sha256'],'locked descriptor/archive identity differs')
        extracted=root/(sid+'-extracted')
        receipt=transport.extract_stage(download,extracted,maximum=contract['object_artifact_max_bytes'],deadline=import_deadline)
        if origin_row is not None:
            f.need(f.file_sha(extracted/'receipt.json')==origin_row['receipt_sha256'] and
                   f.file_sha(extracted/'evidence/owned-modules.jsonl')==origin_row['checked_module_receipts_sha256'],'locked producer receipt chain differs')
        predecessor=[x for x in lineage if x['stage_id'] in producer['admitted_stages']]
        imported_modules={m for dep in producer['admitted_stages'] for m in selected_contract['stages'][dep]['modules']}
        producer_inventory={name:prior[name] for module in imported_modules for name in module_outputs(module)}
        expected={'identity':origin['identity'],'stage_id':sid,'stage_modules':producer['modules'],
          'admitted_stages':producer['admitted_stages'],'contract_sha256':selected_sha,
          'interface_identity':interface,'producer_work':str(work),'runtime_inventory_sha256':RUNTIME_INVENTORY_SHA,
          'predecessor_artifacts':predecessor,'contract':selected_contract,'stage_rows':[owned_rows[m] for m in producer['modules']],
          'owned_rows':owned_rows,'cache_rows':cache_rows,'runtime':runtime,'cache_search':search,
          'producer_inventory':producer_inventory,'origin':origin,'dependency_pins':f.load_json(ROOT/'locks/dependencies.json')['packages']}
        added,prior=transport.admit_stage(extracted,expected=expected,objects=work/'objects',prior=prior,checked=checked,api=sys.modules[__name__],deadline=import_deadline)
        f.need([r['module'] for r in added]==producer['modules'],'admitted producer coverage differs')
        checked.update(producer['modules'])
        lineage.append({'stage_id':sid,'origin':origin,'receipt_sha256':f.file_sha(extracted/'receipt.json'),
          'own_modules':producer['modules'],'checked_module_receipts_sha256':f.file_sha(extracted/'evidence/owned-modules.jsonl')})
        shutil.rmtree(download)
    verify_owned_final(work/'objects',prior,contract['owned_output_max_bytes'])
    transport.check_deadline(import_deadline)
    return prior,checked,lineage

def export_stage(work,contract,contract_sha,stage_id,interface,lineage,deadline):
    own=contract['stages'][stage_id]
    receipt={'identity':stage_identity(),'stage_id':stage_id,'stage_modules':own['modules'],
      'admitted_stages':own['admitted_stages'],'contract_sha256':contract_sha,'interface_identity':interface,
      'producer_work':str(work),'runtime_inventory_sha256':RUNTIME_INVENTORY_SHA,
      'predecessor_artifacts':lineage}
    collector=load_helper('collect_evidence')
    collector.verify_complete(work/'evidence',contract,contract_sha,require_export=False)
    transport.write_stage(work/'objects',work/'evidence',receipt,work/'object-upload',
      maximum=contract['object_artifact_max_bytes'],evidence_maximum=contract['evidence_max_bytes'],deadline=deadline)
    return {'stage_id':stage_id,'contract_sha256':contract_sha,
      'stage_tar_sha256':f.file_sha(work/'object-upload/stage.tar'),'stage_tar_bytes':(work/'object-upload/stage.tar').stat().st_size,
      'descriptor_sha256':f.file_sha(work/'object-upload/descriptor.json')}


def finalize_stage_export(work,contract,contract_sha,stage_id,interface,lineage,deadline,result,watchdog=None):
    try:
        f.need(time.monotonic()<deadline,'stage aggregate deadline exceeded before export')
        exported=export_stage(work,contract,contract_sha,stage_id,interface,lineage,deadline)
        f.need(time.monotonic()<deadline,'stage aggregate deadline exceeded during export')
        marker=work/'evidence/stage-export.json';pending=work/'evidence/.stage-export.pending'
        f.need(not marker.exists() and not pending.exists(),'preexisting stage completion marker')
        with pending.open('xb') as stream:stream.write(f.json_bytes(exported))
        if watchdog is not None:watchdog.check()
        f.need(time.monotonic()<deadline,'stage aggregate deadline exceeded before completion marker')
        os.replace(pending,marker)
        if watchdog is not None:watchdog.close()
    except Exception as e:
        result['status']='FAILED_STAGE_EXPORT_OR_DEADLINE';result['complete_evidence']=False;result['error']=str(e)
        write_json(work/'evidence/result.json',result)
        raise

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

_ACTIVE_WATCHDOG=None

def execute_cli():
    try:main()
    finally:
        if _ACTIVE_WATCHDOG is not None:_ACTIVE_WATCHDOG.close()


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--stage',required=True);ap.add_argument('--contract-sha256',required=True);ap.add_argument('--work',type=Path,required=True)
    ap.add_argument('--runtime',type=Path);ap.add_argument('--runtime-inventory',type=Path)
    ap.add_argument('--local-dependencies',type=Path)
    a=ap.parse_args();f.need(sys.flags.isolated and sys.dont_write_bytecode,'invoke with Python -I -B');contract=f.pinned_load(ROOT/'contract.json',a.contract_sha256)
    f.need(contract['review_status']=='reviewed_for_execution','INACTIVE: diagnostic is not reviewed')
    validate_diagnostic_profile(contract)
    validate_stage_plan(contract)
    f.need(contract['schema']==CONTINUATION_SCHEMA,'this runner executes only the reviewed continuation contract')
    f.need(a.stage in contract['execution_stages'],'unknown or nonexecuted continuation stage')
    f.need(not a.runtime and not a.runtime_inventory and not a.local_dependencies,'staged production runner requires fresh official acquisition')
    stage=contract['stages'][a.stage];final_stage=a.stage==contract['final_stage']
    f.need(f.file_sha(ROOT/'ci/fresh_stage.py')==HELPER_SHA,'bounded runner changed')
    validate_distribution_layout(contract)
    f.need(os.environ.get('GITHUB_REF')=='refs/heads/'+contract['publication_branch'],'unexpected diagnostic branch')
    f.need(git_capture(ROOT,'rev-parse','HEAD').decode().strip()==os.environ.get('GITHUB_SHA'),'workflow commit mismatch')
    f.need(not git_capture(ROOT,'status','--porcelain=v1','--untracked-files=all','--ignored'),'workflow checkout is not clean')
    for rel,row in contract['inputs'].items():
        if rel.startswith('src/'):continue  # Authenticated source archive is admitted below.
        f.safe_rel(rel);p=ROOT/rel;f.no_symlink_path(p)
        f.need(p.stat().st_size==row['bytes'] and f.file_sha(p)==row['sha256'],'diagnostic input changed: '+rel)
    validate_continuation_origins(contract)
    owned=f.load_json(ROOT/'locks/owned-sources.json');required_lock=f.load_json(ROOT/'locks/required-modules.json')
    work=a.work.absolute();f.no_symlink_path(work);f.need(not work.exists(),'diagnostic workspace must be new');work.mkdir()
    for n in ['logs','evidence','packages','home','tmp','cache','objects','bootstrap','quarantine','auditor-objects']:(work/n).mkdir()
    deadline=time.monotonic()+contract['aggregate_command_deadline_seconds'];commands=[];runtime=None;terminal_ready=False
    global _ACTIVE_WATCHDOG
    watchdog=HostDeadline(deadline);_ACTIVE_WATCHDOG=watchdog;watchdog.arm()
    result={'schema':CONTINUATION_SCHEMA,'status':'INCOMPLETE','proof_certified':False,
      'fresh_external_source_rebuild':False,'cache_bytes_trusted_not_source_authenticated':True,
      'stage_id':a.stage,'stage_modules':stage['modules'],'admitted_stages':stage['admitted_stages'],
      'owned_module_count':2481,'finite_prerequisite_count':333,'conditional_C_remains_explicit':True,
      'final_C_proof_certified':False,'unconditional_monotile_proof_certified':False,
      'owned_objects_from_prior_runs':True,'contract_sha256':a.contract_sha256,
      'workflow_commit':os.environ.get('GITHUB_SHA'),'run_id':os.environ.get('GITHUB_RUN_ID'),
      'run_attempt':os.environ.get('GITHUB_RUN_ATTEMPT'),'command_count':0,'complete_log_bytes':0}
    write_json(work/'evidence/result.json',result)
    def command(name,argv,*,cwd=None,env=None,seconds=1800,rss=8*GIB,allowed_sessions=False,expect_success=True):
        f.need(time.monotonic()<deadline,'diagnostic aggregate deadline exceeded')
        requested_seconds=seconds
        seconds=min(seconds,max(1,int(deadline-time.monotonic())))
        validate_session_policy(name,list(map(str,argv)),allowed_sessions,work,contract)
        out=work/'logs'/(name+'.stdout');err=work/'logs'/(name+'.stderr')
        watchdog.in_command=True
        try:
            r=f.run_process(list(map(str,argv)),cwd=cwd or work,env=env or safe_env(runtime or Path('/usr'),work/'home',work/'tmp'),timeout=seconds,stdout=out,stderr=err,max_log_bytes=contract['per_command_log_max_bytes'],
              limits={'address_space_bytes':12*GIB,'rss_tree_bytes':rss,'max_created_file_bytes':512*1024**2},allow_new_sessions=allowed_sessions)
        finally:
            watchdog.in_command=False
            if watchdog.expired:watchdog.failure_receipt_grace()
        r.update(timeout_seconds=seconds,max_log_bytes=contract['per_command_log_max_bytes'],limits={'address_space_bytes':12*GIB,'rss_tree_bytes':rss,'max_created_file_bytes':512*1024**2},allow_new_sessions=allowed_sessions,
          requested_timeout_seconds=requested_seconds,effective_timeout_seconds=seconds,
          max_rss_bytes=rss,address_space_bytes=12*GIB,max_created_file_bytes=512*1024**2,name=name,argv=list(map(str,argv)),cwd=str(cwd or work),stdout_sha256=f.file_sha(out),stderr_sha256=f.file_sha(err));commands.append(r)
        with (work/'evidence/commands.jsonl').open('a') as h:h.write(json.dumps(r,sort_keys=True,separators=(',',':'))+'\n')
        result['command_count']=len(commands);result['complete_log_bytes']+=out.stat().st_size+err.stat().st_size
        f.need(result['complete_log_bytes']<=contract['aggregate_log_max_bytes'],'aggregate complete log bound exceeded')
        write_json(work/'evidence/last_command.json',r);write_json(work/'evidence/result.json',result)
        watchdog.check()
        ok=r['exit_code']==0 and not any(r[k] for k in ['timed_out','log_overflow','memory_exceeded','surviving_children']) and r['process_group_empty'] and r['descendants_empty'] and not (r['escaped_descendants'] and not r['new_sessions_explicitly_allowed'])
        f.need(ok or not expect_success,'command failed/incomplete: '+name)
        return out,ok
    try:
        source_root=work/'source-input'
        source_receipt=extract_owned_sources(ROOT/'owned-sources.tar.gz',source_root,contract)
        write_json(work/'evidence/source-extraction.json',source_receipt)
        result['source_extraction_receipt_sha256']=f.file_sha(work/'evidence/source-extraction.json')
        result['source_archive_sha256']=contract['source_archive']['sha256']
        validate_owned_graph(contract,owned,required_lock,source_root)
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
        readonly_boundary_preflight(runtime,work,env,command)
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
            command(name+'-fetch',base+['fetch','--quiet','--depth=1','--no-tags',origin,pin['rev']],env=env,seconds=300,allowed_sessions=True)
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
        required=required_lock['modules']
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
        for row in contract['modules']:f.need(row['module'] not in providers,'cached object shadows owned module')
        owners=namespace_providers([Path(s) for s in search]+[runtime/'lib/lean'])
        for row in required:
            f.need(owners.get(row['module'].split('.')[0])==str(work/'packages'/row['package']/'.lake/build/lib/lean'),'required namespace has wrong provider')
        f.exact_tree(source_root/'src',{name.removeprefix('src/') for name in contract['inputs'] if name.startswith('src/')})
        shutil.copytree(source_root/'src',work/'src');owned_before=checked_inventory(work/'src',maximum=contract['owned_source_max_bytes'])
        shutil.copytree(ROOT/'auditors',work/'auditors')
        auditor_before=checked_inventory(work/'auditors',maximum=1024**2)
        # Cached package builds stay read-only. Download archives are no longer inputs.
        shutil.rmtree(work/'cache');(work/'cache').mkdir()
        env['LEAN_PATH']=':'.join([str(work/'objects'),*search,str(runtime/'lib/lean')])
        prior={};checked=set();receipts=[];lineage=[]
        owned_rows={r['module']:r for r in owned['sources']};cache_rows={}
        for r in required:
            prefix='lib/lean/'+r['module'].replace('.','/')
            suffixes=['.olean','.ilean']+(['.olean.server','.olean.private','.ir.sig','.ir'] if r['modern_module'] else [])
            cache_rows[r['module']]={**r,'companions':{prefix+suffix:inventories[r['package']]['files'][prefix+suffix] for suffix in suffixes}}
        result['cached_build_inventory_sha256']=f.file_sha(work/'evidence/cached-build-inventory.json')
        result['runtime_inventory_sha256']=f.file_sha(work/'evidence/runtime-inventory.json')
        interface=cache_interface_identity(cache_rows,inventories,result['runtime_inventory_sha256'])
        write_json(work/'evidence/interface-identity.json',interface)
        result['interface_identity_sha256']=f.file_sha(work/'evidence/interface-identity.json')
        prior,checked,lineage=restore_stages(work,contract,a.contract_sha256,a.stage,interface,owned_rows,cache_rows,runtime,deadline)
        write_json(work/'evidence/imported-stages.json',lineage)
        result['imported_stages_sha256']=f.file_sha(work/'evidence/imported-stages.json')
        write_json(work/'evidence/cross-origin-admissions.json',cross_origin_certificate(contract,a.contract_sha256,stage_identity(),a.stage,interface,lineage,prior))
        result['cross_origin_admissions_sha256']=f.file_sha(work/'evidence/cross-origin-admissions.json')
        for module in stage['modules']:
            row=owned_rows[module];rel=module.replace('.','/')
            print(json.dumps({'phase':'compile_and_check','module':module,'stage':a.stage,'completed':len(receipts),'total':len(stage['modules'])}),flush=True)
            f.need(shutil.disk_usage(work).free>=contract['minimum_free_disk_bytes'],'insufficient measured disk reserve before module')
            staging=work/'quarantine'/module;staging.mkdir()
            target=staging/(rel+'.olean');target.parent.mkdir(parents=True,exist_ok=True)
            inputs=direct_import_receipt(row,owned_rows,checked,prior,cache_rows,runtime)
            result['current_module']=module;result['current_module_state']='COMPILING_WITH_READ_ONLY_PREDECESSORS'
            write_json(work/'evidence/result.json',result)
            argv=[runtime/'bin/lean','-j1','-M'+str(DIAGNOSTIC_HEAP_MIB),'-Dcompiler.postponeCompile=false',*module_compile_arguments(contract,module),'-o',target,'-i',staging/(rel+'.ilean'),'-c',staging/(rel+'.c'),work/'src'/(rel+'.lean')]
            sources=[work/'packages',work/'src',work/'objects']
            kw=dict(runtime=runtime,sources=sources,writable=[staging,work/'home',work/'tmp'],cwd=work/'src',env=env)
            f.need(str(staging) not in env['LEAN_PATH'].split(':'),'quarantine must never be an import root')
            namespace_providers([work/'objects',*[Path(s) for s in search],runtime/'lib/lean'])
            command('compile-'+module,sandbox(argv,**kw),env=env,seconds=contract['diagnostic_timeout_seconds'],rss=DIAGNOSTIC_RSS_BYTES,allowed_sessions=True)
            prior=admit_quarantine(staging,work/'objects',module,prior,contract['owned_output_max_bytes'])
            shutil.rmtree(staging)
            result['current_module_state']='PROVISIONALLY_ADMITTED_PENDING_KERNEL_CHECK'
            write_json(work/'evidence/last-provisional-module.json',{'module':module,'source_sha256':row['sha256'],'outputs':{name:prior[name] for name in sorted(module_outputs(module))},'not_yet_an_accepted_predecessor':True})
            write_json(work/'evidence/result.json',result)
            namespace_providers([work/'objects',*[Path(s) for s in search],runtime/'lib/lean'])
            kw['writable']=[work/'home',work/'tmp']
            command('check-'+module,sandbox([runtime/'bin/leanchecker',module],**kw),env=env,seconds=contract['check_timeout_seconds'],rss=DIAGNOSTIC_RSS_BYTES,allowed_sessions=True)
            # Check current companions after checker, while committed predecessors
            # were read-only in both commands. The final full scan also rejects
            # any unexpected host-side mutation or inventory addition.
            for name in sorted(module_outputs(module)):
                f.need(f.file_sha(work/'objects'/name)==prior[name]['sha256'],'fresh output changed during checker')
            checked.add(module)
            result['current_module_state']='ACCEPTED_AFTER_KERNEL_CHECK'
            receipt={'module':module,'source_sha256':row['sha256'],'ordered_imports':inputs,
              'outputs':{name:prior[name] for name in sorted(module_outputs(module))},
              'compiler_command':len(commands)-2,'checker_command':len(commands)-1,
              'checker_passed':True,'conditional_C_remains_explicit':True}
            receipts.append(receipt)
            with (work/'evidence/owned-modules.jsonl').open('a') as h:h.write(json.dumps(receipt,sort_keys=True,separators=(',',':'))+'\n')
            result['checked_owned_module_count']=len(checked)
            result['checked_fresh_module_count']=len(receipts)
            write_json(work/'evidence/result.json',result)
        # Auditors compile and check against official runtime only, each in its
        # own writable quarantine. Their runtime import environment is read-only.
        audit_prior={};audit_env=safe_env(runtime,work/'home',work/'tmp')
        audit_env['LEAN_PATH']=str(work/'auditor-objects')+':'+str(runtime/'lib/lean')
        audits={}
        for name,key,marker in ([('AuditOrdinaryBridges','ordinary_bridges','ALL_FOUR_EXACT_RAW_BRIDGE_CONTRACTS_PASSED'),('AuditConditionalEndpoints','conditional_endpoints','CONDITIONAL_ENDPOINT_AUDIT_PASSED')] if final_stage else []):
            audit_stage=work/'quarantine'/name;audit_stage.mkdir()
            argv=[runtime/'bin/lean','-j1','-M4096','-Dcompiler.postponeCompile=false','-o',audit_stage/(name+'.olean'),'-i',audit_stage/(name+'.ilean'),'-c',audit_stage/(name+'.c'),work/'auditors'/(name+'.lean')]
            kw=dict(runtime=runtime,sources=[work/'auditors',work/'auditor-objects'],writable=[audit_stage,work/'home',work/'tmp'],cwd=work/'auditors',env=audit_env)
            command('compile-auditor-'+name,sandbox(argv,**kw),env=audit_env,seconds=180,rss=DIAGNOSTIC_RSS_BYTES,allowed_sessions=True)
            audit_prior=admit_quarantine(audit_stage,work/'auditor-objects',name,audit_prior,64*1024**2);shutil.rmtree(audit_stage)
            kw['writable']=[work/'home',work/'tmp']
            command('check-auditor-'+name,sandbox([runtime/'bin/leanchecker',name],**kw),env=audit_env,seconds=120,rss=DIAGNOSTIC_RSS_BYTES,allowed_sessions=True)
            run_env=dict(env);run_env['LEAN_PATH']=str(work/'auditor-objects')+':'+env['LEAN_PATH']
            kw=dict(runtime=runtime,sources=[work/'auditors',work/'auditor-objects',work/'objects',work/'packages'],writable=[work/'home',work/'tmp'],cwd=work/'auditors',env=run_env)
            output,_=command('audit-'+name,sandbox([runtime/'bin/lean','-j1','-M4096','--run',work/'auditors'/(name+'.lean')],**kw),env=run_env,seconds=contract['auditor_timeout_seconds'],rss=DIAGNOSTIC_RSS_BYTES,allowed_sessions=True)
            f.need(output.read_text().splitlines().count(marker)==1,'missing or repeated mandatory audit marker')
            parsed=audit_bridge_output(output.read_text()) if key=='ordinary_bridges' else audit_endpoint_output(output.read_text())
            write_json(work/'evidence'/(key+'-raw-audit.json'),parsed)
            audits[key]=True
        verify_owned_final(work/'auditor-objects',audit_prior,64*1024**2)
        f.need(checked_inventory(work/'auditors',maximum=1024**2)==auditor_before,'auditor source changed')
        final_owned=verify_owned_final(work/'objects',prior,contract['owned_output_max_bytes'])
        write_json(work/'evidence/fresh-owned-objects.json',final_owned)
        f.need(time.monotonic()<deadline,'diagnostic aggregate deadline exceeded')
        f.need(checked_inventory(work/'src',maximum=contract['owned_source_max_bytes'])==owned_before,'owned diagnostic source changed')
        for pin in pins:
            name=pin['name'];p=work/'packages'/name
            f.need(source_snapshot(p,pin)==before[name],'dependency source changed during consumers')
            f.need(checked_inventory(p/'.lake/build',maximum=4*GIB,allow_links=True)==inventories[name],'cached dependency bytes changed during consumers')
        validate_terminal_receipt(result,commands,[owned_rows[m] for m in stage['modules']],receipts,audits,final=final_stage)
        expected_checked={m for sid in [*stage['admitted_stages'],a.stage] for m in contract['stages'][sid]['modules']}
        f.need(checked==expected_checked,'stage checked coverage differs')
        if final_stage:f.need(len(checked)==2481,'final all-module coverage missing')
        result['raw_audits']=audits
        result['status']='ALL_PROOF_GATES_PASSED_EVIDENCE_COLLECTION_PENDING'
        result['owned_companion_bytes']=final_owned['bytes']
        result['owned_output_inventory_sha256']=f.file_sha(work/'evidence/fresh-owned-objects.json')
        result['command_receipts_sha256']=f.file_sha(work/'evidence/commands.jsonl')
        result['owned_module_receipts_sha256']=f.file_sha(work/'evidence/owned-modules.jsonl')
        terminal_ready=True
    except Exception as e:
        terminal_ready=False
        result['status']='FAILED_OR_INCOMPLETE';result['error']=str(e);raise
    finally:
        write_json(work/'evidence/result.json',result)
        # Preserve complete bounded command logs, never tail-only logs on success.
        try:
            for p in sorted((work/'logs').glob('*')):
                f.need(p.is_file() and not p.is_symlink(),'unexpected log entry')
                q=work/'evidence/logs'/p.name;q.parent.mkdir(exist_ok=True);shutil.copyfile(p,q)
            checked_inventory(work/'evidence',maximum=contract['evidence_max_bytes']-8192)
            if terminal_ready:
                result['status']=SUCCESS if final_stage else STAGE_SUCCESS;result['complete_evidence']=True
                write_json(work/'evidence/result.json',result)
        except Exception as e:
            result['status']='FAILED_EVIDENCE_COLLECTION';result['complete_evidence']=False;result['collection_error']=str(e)
            write_json(work/'evidence/result.json',result)
            raise

    finalize_stage_export(work,contract,a.contract_sha256,a.stage,interface,lineage,deadline,result,watchdog)

if __name__=='__main__':execute_cli()
