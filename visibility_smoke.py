#!/usr/bin/env python3
"""Inactive, bounded four-target visibility smoke. No publication or project restoration."""
from __future__ import annotations
import time
ENTRY_TIME = time.monotonic()
import argparse, hashlib, importlib.util, json, os, re, shutil, stat, sys, urllib.request
from pathlib import Path
RAW_FILE = Path(__file__).absolute()
for ancestor in [RAW_FILE,*RAW_FILE.parents]:
    if ancestor.is_symlink():raise RuntimeError('symlink script ancestry')
ROOT = RAW_FILE.parent
VENDOR = ROOT/'vendor/pipeline'
# Before importing trusted helpers: fixed finite file reads only. The eventual
# deadline is measured from ENTRY_TIME, not reset after these checks.
API_SHA = '72d311d1797040e7f9b106792d26b87c6c2b7d9b3a40040af1398e134919cadb'
PREIMPORT_FILES = {'cache_diagnostic.py': {'bytes': 81922, 'sha256': '72d311d1797040e7f9b106792d26b87c6c2b7d9b3a40040af1398e134919cadb'}, 'collect_evidence.py': {'bytes': 22654, 'sha256': '1d6ddba8bc4d29f207da62fb93c1eb226e7dce40269af423f58fb2998840be6a'}, 'conditional_transport.py': {'bytes': 55492, 'sha256': 'd8688bf50ffdd460653a007876798c2adf7a21ed7f7fd0e57b564f7c7021469e'}, 'fresh_stage.py': {'bytes': 50298, 'sha256': '6adfa8e43f8e0997ffef27210c4338d555b203b48ca50cb5c7b7b99ac49991d8'}, 'higher_policy.py': {'bytes': 58899, 'sha256': '5bbb593b97e3e686faa466bd755d5817b0c9d39e5d3ade4d4fd85b3e2f567e8a'}, 'source_header.py': {'bytes': 2551, 'sha256': '3eca76608279cbd7fb659eec960177bed6e7ad4829c5e5636f6ad23636645701'}, 'toolchain_install.py': {'bytes': 6752, 'sha256': '9b8fefa2020be7e58bbf04f79445f603657bd647c0afe0b1196078f92629f038'}}
for name,row in PREIMPORT_FILES.items():
    candidate=VENDOR/'ci'/name
    for ancestor in [candidate,*candidate.parents]:
        if ancestor.is_symlink():raise RuntimeError('symlink helper ancestry')
    st=candidate.lstat()
    if not stat.S_ISREG(st.st_mode) or st.st_nlink!=1 or st.st_size!=row['bytes'] or hashlib.sha256(candidate.read_bytes()).hexdigest()!=row['sha256']:
        raise RuntimeError('fixed helper pre-import identity differs')
p = VENDOR/'ci/cache_diagnostic.py'
for parent in [p,*p.parents]:
    if parent.is_symlink():raise RuntimeError('symlink helper parent')
if p.is_symlink() or p.stat().st_size > 256*1024 or hashlib.sha256(p.read_bytes()).hexdigest() != API_SHA:
    raise RuntimeError('vendored acquisition API identity differs')
spec = importlib.util.spec_from_file_location('visibility_acquisition_api', p)
a = importlib.util.module_from_spec(spec); sys.modules[spec.name] = a; spec.loader.exec_module(a)
f = a.f
GIB = 1024**3
SUCCESS = 'FOUR_TARGET_VISIBILITY_SMOKE_PASSED'
SCHEMA = 'palomar-four-target-visibility-smoke-v1'
TARGETS = ['SpectreClusters.ReverseClusterCocycleIntegration',
           'SpectreGeometry.DeformationHomeomorphism',
           'SpectreGeometry.PolygonProductKeyBody',
           'SpectreGeometry.PhysicalGridRealization']
LIMITS = {'aggregate_command_deadline_seconds':7200, 'outer_timeout_minutes':130,
          'diagnostic_timeout_seconds':180, 'check_timeout_seconds':120,
          'lean_heap_mib':4096, 'address_space_bytes':12*GIB, 'rss_tree_bytes':8*GIB,
          'max_created_file_bytes':512*1024**2, 'per_command_log_max_bytes':1024**2,
          'aggregate_log_max_bytes':64*1024**2, 'evidence_max_bytes':124*1024**2,
          'upload_max_bytes':128*1024**2, 'collection_reserve_bytes':4*1024**2,
          'owned_source_max_bytes':32*1024**2, 'owned_output_max_bytes':6*GIB,
          'minimum_free_disk_bytes':1536*1024**2, 'failure_evidence_grace_seconds':5}
EXPECTED_UNKNOWN = {
 TARGETS[0]: [(60,33,'position_cancel'), (61,25,'position_triangle')],
 TARGETS[1]: [(34,15,'translated_contracting')],
 TARGETS[2]: [(224,24,'product_key_collar_interior_disjoint')],
 TARGETS[3]: [(57,20,'anchor_registered')]}
CASCADE = {
 (31,4): "(kernel) declaration has metavariables 'SpectreGeometry.Deformation.identitySubHomeomorph'",
 (58,16): "(kernel) declaration type mismatch, 'SpectreGeometry.Deformation.identitySubHomeomorph_apply' has type",
 (73,42): 'unsolved goals'}
PHYSICAL_GRID_CASCADE = {
 (60,19): 'Function expected at',
 (70,18): 'Function expected at',
 (78,30): 'Function expected at'}
PHYSICAL_GRID_CONTINUATION = [
 '  tilingLatticeCoordinate f',
 'but this term has type',
 '  Point',
 '',
 'Note: Expected a function because this term is being applied to the argument',
 '  hdirect']


def read_capture(path,maximum,watchdog):
    watchdog.check();f.no_symlink_path(path)
    fd=os.open(path,os.O_RDONLY|os.O_NOFOLLOW|os.O_NONBLOCK)
    def identity(st):return (st.st_dev,st.st_ino,st.st_mode,st.st_nlink,st.st_size,st.st_mtime_ns,st.st_ctime_ns)
    try:
        before=os.fstat(fd);f.need(stat.S_ISREG(before.st_mode) and before.st_nlink==1 and before.st_size<=maximum,'unsafe or oversized probe capture')
        data=bytearray()
        while len(data)<=maximum:
            block=os.read(fd,min(65536,maximum+1-len(data)))
            if not block:break
            data.extend(block)
        after=os.fstat(fd)
        f.need(identity(before)==identity(after) and len(data)==before.st_size,'probe capture changed or short read')
    finally:os.close(fd)
    # Recheck the named file and every parent after the retained descriptor closes.
    f.no_symlink_path(path);f.need(identity(path.lstat())==identity(before),'probe capture named identity changed after close')
    watchdog.check();return bytes(data)

def clean_command(r):
    flags=['timed_out','log_overflow','memory_exceeded','surviving_children','process_group_empty','descendants_empty','escaped_descendants','new_sessions_explicitly_allowed']
    f.need(all(type(r.get(k)) is bool for k in flags) and type(r.get('exit_code')) is int,'native safety receipt scalar types differ')
    return not any(r[k] for k in flags[:4]) and r['process_group_empty'] and r['descendants_empty'] and (not r['escaped_descendants'] or r['new_sessions_explicitly_allowed'])


def failure_diagnostics(module, text):
    """Match plain errors and explicitly coded unknown-identifier errors only."""
    path = module.replace('.','/')+'.lean'
    errors = []
    lines = text.splitlines()
    for index,line in enumerate(lines):
        m = re.fullmatch(r'(.*\.lean):(\d+):(\d+): error(?:\((lean\.unknownIdentifier)\))?: (.*)', line)
        if m:
            f.need(m[1].endswith('/'+path) or m[1]==path, 'diagnostic has wrong source')
            errors.append((int(m[2]),int(m[3]),m[4],m[5],index))
        elif re.search(r'(^|[\s:])error\b', line):
            raise f.Rejected('unrecognized error diagnostic header')
    expected = EXPECTED_UNKNOWN[module]
    unknown=[]; cascades=[]
    for line,col,code,message,index in errors:
        m = re.fullmatch(r'Unknown identifier `([^`]+)`', message)
        if m:
            triple=(line,col,m[1])
            f.need(any(line==l and (c is None or col==c) and m[1]==name for l,c,name in expected),
                   'unexpected unknown identifier diagnostic')
            unknown.append(triple)
        else:
            if module==TARGETS[3]:
                f.need(code is None and PHYSICAL_GRID_CASCADE.get((line,col))==message,
                       'unexpected compiler error beyond authenticated PhysicalGrid cascades')
                end=next((i for i in range(index+1,len(lines)) if re.match(r'.*\.lean:\d+:\d+:',lines[i])),len(lines))
                f.need(lines[index+1:end]==PHYSICAL_GRID_CONTINUATION,
                       'PhysicalGrid cascade continuation differs')
            else:
                f.need(code is None and module==TARGETS[1] and CASCADE.get((line,col))==message,
                       'unexpected compiler error beyond authenticated cascades')
            cascades.append((line,col,message))
    f.need(len(unknown)==len(expected) and len(set(unknown))==len(unknown), 'missing or duplicate expected unknown identifier')
    if module==TARGETS[3]:
        f.need(len(cascades)==len(PHYSICAL_GRID_CASCADE) and {(line,col) for line,col,message in cascades}==set(PHYSICAL_GRID_CASCADE),
               'missing or duplicate PhysicalGrid cascade')
    return {'unknown_identifiers':unknown, 'authenticated_cascade_headers':cascades}


def validate_contract(c, *, reviewed=False):
    f.need(c['schema']==SCHEMA and c['limits']==LIMITS, 'smoke profile differs')
    f.need(c['targets']==TARGETS and c['owned_module_count']==174, 'target scope differs')
    f.need(c['publication_branch']=='verify/palomar-visibility-controls-20261019', 'branch differs')
    f.need(c['source_archive']['path']=='owned-sources.tar.gz', 'source archive path differs')
    f.need(c['owned_source_max_bytes']==LIMITS['owned_source_max_bytes'], 'source limit differs')
    f.need(c['runtime_roots']==['Init','Init.Data.Rat'], 'runtime boundary differs')
    f.need(len(c['cache_roots'])==40 and c['cache_roots']==sorted(set(c['cache_roots'])), 'cache boundary differs')
    f.need(all(x.startswith('Mathlib.') and f.MODULE.fullmatch(x) for x in c['cache_roots']), 'cache root invalid')
    f.need(c['expected_diagnostics']==json.loads(json.dumps(EXPECTED_UNKNOWN)), 'expected diagnostics changed')
    f.need(c['original_probes_use_corrected_prerequisites'] is True and c['restore_project_objects'] is False,
           'probe or freshness scope changed')
    f.need(c['full_official_verification_claimed'] is False, 'smoke claim scope changed')
    f.need(set(c['target_closures'])==set(TARGETS),'target closure map differs')
    f.need([len(c['target_closures'][t]) for t in TARGETS]==[10,1,52,136],'target closure sizes differ')
    f.need(c['init_only_order']==c['module_order'][:10] and c['init_only_order'][-1]==TARGETS[0], 'early Init-only control differs')
    f.need(len(c['module_order'])==len(set(c['module_order']))==174, 'owned order invalid')
    if reviewed:
        f.need(c['review_status']=='reviewed_for_execution', 'INACTIVE: independent review required')
        f.need(type(c.get('independent_driver_review_sha256')) is str and f.SHA256.fullmatch(c['independent_driver_review_sha256']), 'independent driver review pin required')


def validate_workflow(c,contract_sha):
    data=(ROOT/'.github/workflows/palomar-visibility-smoke.yml').read_bytes()
    active=c['review_status']=='reviewed_for_execution'
    token=contract_sha.encode() if active else b'0'*64
    guard=b'    if: ${{ true }}\n' if active else b'    if: ${{ false }}\n'
    f.need(data.count(b'--contract-sha256 '+token)==2 and data.count(guard)==1,'workflow activation slots differ')
    normalized=data.replace(b'--contract-sha256 '+token,b'--contract-sha256 '+b'0'*64).replace(guard,b'    if: ${{ false }}\n')
    f.need(c['workflow_template_sha256']=='a8442740ae8ee66774ba4b895617ec97fb6c675f4e4d37583c749afcea229361'
           and f.sha(normalized)==c['workflow_template_sha256'],'reviewed normalized workflow differs')


def validate_inputs(c):
    expected=set(c['distribution_files'])
    f.need(expected==set(c['inputs'])-set(x for x in c['inputs'] if x.startswith('src/'))
           | {'smoke-contract.json','owned-sources.tar.gz','.github/workflows/palomar-visibility-smoke.yml'},
           'distribution lock differs')
    files={}
    for parent,dirs,names in os.walk(ROOT,followlinks=False):
        if Path(parent)==ROOT and '.git' in dirs: dirs.remove('.git')
        for n in dirs: f.need(not (Path(parent)/n).is_symlink(), 'distribution directory symlink')
        for n in names:
            p=Path(parent)/n; s=p.lstat(); rel=p.relative_to(ROOT).as_posix()
            f.need(stat.S_ISREG(s.st_mode) and s.st_nlink==1, 'nonregular distribution file')
            files[rel]=p
    f.need(set(files)==expected, 'unexpected or missing distribution file')
    validate_workflow(c,f.sha(f.json_bytes(c)))
    for rel,row in c['inputs'].items():
        f.safe_rel(rel)
        if rel.startswith('src/'): continue
        p=files[rel]
        f.need(p.stat().st_size==row['bytes'] and f.file_sha(p)==row['sha256'], 'input pin differs: '+rel)


def validate_graph(c, work):
    rows=c['modules']; owned={r['module']:r for r in rows}
    f.need([r['module'] for r in rows]==c['module_order'], 'graph order differs')
    external=set(); seen=set()
    for row in rows:
        m=row['module']; path='src/'+m.replace('.','/')+'.lean'
        f.need(row['path']==path and c['inputs'][path]=={'bytes':row['bytes'],'sha256':row['sha256']}, 'source row differs')
        parsed=a.header_parser.header((work/'source-input'/path).read_bytes())
        f.need(parsed['modern'] and not parsed['prelude'], 'owned module header differs')
        imports=[x['module'] for x in parsed['imports']]
        f.need(imports==row['ordered_imports'], 'owned direct imports differ')
        for dep in [*imports,'Init']:
            f.need(dep in seen or dep in c['cache_roots'] or dep in c['runtime_roots'], 'unresolved or unordered owned import')
            if dep not in owned: external.add(dep)
        seen.add(m)
    f.need(external==set(c['cache_roots']+c['runtime_roots']), 'external boundary differs')
    reachable=set()
    def visit(m):
        if m not in owned or m in reachable:return
        reachable.add(m)
        for dep in owned[m]['ordered_imports']:visit(dep)
    for m in TARGETS:visit(m)
    f.need(reachable==seen, 'owned closure has extra or missing modules')
    for target in TARGETS:
        reachable.clear();visit(target)
        f.need(reachable==set(c['target_closures'][target]),'per-target closure differs')
    for m in c['init_only_order']:
        f.need(set(owned[m]['ordered_imports'])<=set(c['init_only_order'])|{'Init'}, 'early control is not Init-only')
    return owned


def derive_cache_closure(c, work, snapshots):
    lock=f.load_json(VENDOR/'locks/required-modules.json')
    allowed={r['module']:r for r in lock['modules']}
    f.need(len(allowed)==len(lock['modules'])==2805, 'historical source lock differs')
    selected={}; runtime=set(); visiting=set()
    def visit(m):
        if m in selected or m in runtime:return
        if m.split('.')[0] in ('Init','Lean','Lake','Std'):
            f.need((work/'runtime/lib/lean'/(m.replace('.','/')+'.olean')).is_file(), 'missing runtime cache dependency')
            runtime.add(m);return
        f.need(m in allowed and m not in visiting, 'unlocked or cyclic cache dependency: '+m)
        row=allowed[m]; p=work/'packages'/row['package']/row['path']
        f.need(snapshots[row['package']]['files'][row['path']]['sha256']==row['sha256'], 'cache source differs')
        parsed=a.header_parser.header(p.read_bytes())
        f.need(parsed['modern']==row['modern_module'], 'cache source module mode differs')
        visiting.add(m)
        for dep in [x['module'] for x in parsed['imports']]+([] if parsed['prelude'] else ['Init']):visit(dep)
        visiting.remove(m);selected[m]=row
    for root in c['cache_roots']:visit(root)
    result={'schema':'selected-pinned-official-cache-source-closure-v1','roots':c['cache_roots'],
            'modules':[selected[m] for m in sorted(selected)],'runtime_modules':sorted(runtime),
            'maximum_locked_modules':2805,'derived_from_authenticated_official_source_headers':True}
    a.write_json(work/'evidence/selected-cache-closure.json',result)
    return result['modules']


def acquire_runtime(work, env, command):
    archive=work/'lean.tar.zst'; downloaded=0; start=time.monotonic()
    with urllib.request.urlopen(a.ARCHIVE_URL,timeout=60) as response, archive.open('xb') as out:
        while True:
            block=response.read(1024**2)
            if not block:break
            downloaded+=len(block)
            f.need(downloaded<=a.ARCHIVE_BYTES and time.monotonic()-start<900, 'release download bound')
            out.write(block)
    f.need(downloaded==a.ARCHIVE_BYTES,'official archive size differs')
    runtime=work/'runtime'; inv=a.install_archive(archive,runtime);archive.unlink()
    f.need(f.sha(f.json_bytes(inv))==a.RUNTIME_INVENTORY_SHA,'canonical runtime inventory differs')
    actual={p.relative_to(runtime).as_posix() for p in runtime.rglob('*') if not p.is_dir() or p.is_symlink()}
    f.need(actual==set(inv['files'])|set(inv['symlinks']),'runtime missing/extra entries')
    a.write_json(work/'evidence/runtime-inventory.json',inv)
    env.update(a.safe_env(runtime,work/'home',work/'tmp'))
    env['LEAN_PATH']=str(work/'objects')+':'+str(runtime/'lib/lean')
    command('bwrap-preflight',a.sandbox(['/bin/true'],runtime=runtime,sources=[],writable=[work/'home',work/'tmp'],cwd=work/'tmp',env=env),seconds=30,env=env,allowed_sessions=True)
    a.readonly_boundary_preflight(runtime,work,env,command)
    return runtime


def acquire_cache(c,work,runtime,env,command):
    curl,_=command('curl-version',['/usr/bin/curl','--disable','--version'],env=env,seconds=30)
    m=re.match(r'curl (\d+)\.(\d+)\.',curl.read_text())
    f.need(m and tuple(map(int,m.groups()))>=(7,81),'unapproved fallback curl')
    pins=f.load_json(VENDOR/'locks/dependencies.json')['packages'];a.validate_dependencies(pins);before={}
    for pin in pins:
        name=pin['name'];p=work/'packages'/name;p.mkdir()
        base=['/usr/bin/git','-c','core.hooksPath=/dev/null','-c','core.fsmonitor=false','-C',str(p)]
        command(name+'-init',base+['init','--quiet'],env=env,seconds=30)
        command(name+'-remote',base+['remote','add','origin',pin['url']],env=env,seconds=30)
        command(name+'-fetch',base+['fetch','--quiet','--depth=1','--no-tags',pin['url'],pin['rev']],env=env,seconds=300,allowed_sessions=True)
        command(name+'-checkout',base+['checkout','--quiet','--detach',pin['rev']],env=env,seconds=60)
        before[name]=a.source_snapshot(p,pin)
        f.need(not (p/'.lake').exists(),'prior Lake state')
        (p/'.lake/build').mkdir(parents=True);(p/'.lake/config').mkdir();(p/'.lake/packages').mkdir()
    mathlib=work/'packages/mathlib';manifest=f.load_json(mathlib/'lake-manifest.json')
    expected={p['name']:(p['url'],p['rev']) for p in pins if p['name']!='mathlib'}
    f.need({p['name']:(p['url'],p['rev']) for p in manifest['packages']}==expected,'Mathlib manifest differs')
    required=derive_cache_closure(c,work,before)
    for row in f.load_json(VENDOR/'locks/cache-client.json')['files']:
        p=mathlib/row['path'];f.need(p.stat().st_size==row['bytes'] and f.file_sha(p)==row['sha256'],'cache client pin differs')
    for pin in pins:
        p=work/'packages'/pin['name'];mp=p/'lake-manifest.json'
        if mp.exists():
            for dep in f.load_json(mp)['packages']:
                f.need(dep['name'] in a.OFFICIAL_REPOS,'unexpected nested dependency')
                (p/'.lake/packages'/dep['name']).symlink_to(work/'packages'/dep['name'],target_is_directory=True)
    a.write_json(work/'evidence/dependency-sources.json',before)
    env['MATHLIB_CACHE_DIR']=str(work/'cache')
    # No project sources or objects are mounted in acquisition namespaces.
    acquisition_env=dict(env);acquisition_env.pop('LEAN_PATH',None)
    writable=[work/'home',work/'tmp',work/'cache',*[work/'packages'/p['name']/'.lake' for p in pins]]
    kwargs=dict(runtime=runtime,sources=[work/'packages'],writable=writable,cwd=mathlib,env=acquisition_env)
    command('cache-bootstrap',a.sandbox([runtime/'bin/lake','build','cache'],**kwargs),env=acquisition_env,seconds=900,allowed_sessions=True)
    produced=mathlib/'.lake/build/bin/cache';f.need(produced.is_file(),'cache bootstrap absent')
    cache=work/'bootstrap/cache';shutil.copyfile(produced,cache);cache.chmod(0o555);cache_sha=f.file_sha(cache)
    kwargs['sources'].append(work/'bootstrap')
    a.write_json(work/'evidence/cache-client-binary.json',{'sha256':cache_sha,'bytes':cache.stat().st_size,'built_from_official_sources':True})
    f.need(shutil.disk_usage(work).free>=9*GIB,'insufficient disk for cache acquisition')
    command('cache-get',a.sandbox([runtime/'bin/lake','env',cache,'get','--cache-from=master,legacy',*c['cache_roots']],network=True,**kwargs),env=acquisition_env,seconds=1800,allowed_sessions=True)
    command('cache-lookup',a.sandbox([runtime/'bin/lake','env',cache,'lookup',*[x['module'] for x in required]],**kwargs),env=acquisition_env,seconds=180,allowed_sessions=True)
    f.need(f.file_sha(cache)==cache_sha,'cache client changed')
    cache_inv=a.checked_inventory(work/'cache',maximum=3*GIB)
    f.need(not any(Path(n).name.startswith('curl-') and not n.endswith('.cfg') for n in cache_inv['files']),'fallback curl forbidden')
    a.write_json(work/'evidence/cache-downloads.json',cache_inv)
    inventories={};search=[];providers={}
    for pin in pins:
        name=pin['name'];p=work/'packages'/name
        f.need(a.source_snapshot(p,pin)==before[name],'official source changed during acquisition')
        inventories[name]=a.checked_inventory(p/'.lake/build',maximum=4*GIB,allow_links=True)
        lib=p/'.lake/build/lib/lean';search.append(str(lib))
        for obj in lib.rglob('*.olean'):
            m=obj.relative_to(lib).as_posix().removesuffix('.olean').replace('/','.')
            f.need(m not in providers,'duplicate cached provider');providers[m]=name
    f.need(sum(i['bytes'] for i in inventories.values())<=5*GIB,'aggregate cached build bound')
    a.write_json(work/'evidence/cached-build-inventory.json',inventories)
    cache_rows={}
    for row in required:
        name=row['package'];m=row['module'];prefix='lib/lean/'+m.replace('.','/')
        f.need(providers.get(m)==name,'missing/wrong selected cached provider: '+m)
        suffixes=['.olean','.ilean']+(['.olean.server','.olean.private','.ir.sig','.ir'] if row['modern_module'] else [])
        companions={}
        for suffix in suffixes:
            path=work/'packages'/name/'.lake/build'/(prefix+suffix)
            f.need(path.is_file(),'missing selected cached companion: '+m+suffix)
            companions[prefix+suffix]=inventories[name]['files'][prefix+suffix]
        cache_rows[m]={**row,'companions':companions}
    f.need(not set(providers).intersection(c['module_order']),'cache shadows owned module')
    owners=a.namespace_providers([Path(s) for s in search]+[runtime/'lib/lean'])
    for row in required:
        f.need(owners.get(row['module'].split('.')[0])==str(work/'packages'/row['package']/'.lake/build/lib/lean'),'wrong namespace provider')
    a.write_json(work/'evidence/selected-cache-admission.json',cache_rows)
    shutil.rmtree(work/'cache');(work/'cache').mkdir()
    env['LEAN_PATH']=':'.join([str(work/'objects'),*search,str(runtime/'lib/lean')])
    return pins,before,inventories,search,cache_rows


def revalidate_runtime(runtime,inv):
    f.need(f.sha(f.json_bytes(inv))==a.RUNTIME_INVENTORY_SHA,'final runtime inventory pin differs')
    actual={p.relative_to(runtime).as_posix() for p in runtime.rglob('*') if not p.is_dir() or p.is_symlink()}
    f.need(actual==set(inv['files'])|set(inv['symlinks']),'runtime final membership differs')
    for rel,row in inv['files'].items():
        p=runtime/rel;f.no_symlink_path(p)
        f.need(p.stat().st_size==row['bytes'] and f.file_sha(p)==row['sha256'] and stat.S_IMODE(p.stat().st_mode)==row['mode'],'runtime final bytes/mode differ')
    for rel,target in inv['symlinks'].items():
        f.need((runtime/rel).is_symlink() and os.readlink(runtime/rel)==target and (runtime/rel).resolve(strict=True).is_relative_to(runtime),'runtime final symlink differs')


def compile_argv(runtime,source,staging,module):
    rel=module.replace('.','/')
    return [runtime/'bin/lean','-j1','-M4096','-DElab.async=false',
            '-o',staging/(rel+'.olean'),'-i',staging/(rel+'.ilean'),'-c',staging/(rel+'.c'),source/(rel+'.lean')]


def command_spec(c,work,name,cache_modules=()):
    """Finite full command/bind/environment grammar, shared by runner and collector."""
    runtime=work/'runtime';pins=f.load_json(VENDOR/'locks/dependencies.json')['packages']
    search=[str(work/'packages'/p['name']/'.lake/build/lib/lean') for p in pins]
    env=a.safe_env(runtime,work/'home',work/'tmp');env['LEAN_PATH']=str(work/'objects')+':'+str(runtime/'lib/lean')
    argv=None;seconds=None;allowed=False
    def sand(argv,sources,writable,cwd,seconds,network=False):
        return {'name':name,'argv':list(map(str,a.sandbox(argv,runtime=runtime,sources=sources,writable=writable,cwd=cwd,env=env,network=network))),
                'cwd':str(work),'env':dict(env),'requested_timeout_seconds':seconds,'allowed_sessions':True}
    if name=='bwrap-preflight':return sand(['/bin/true'],[],[work/'home',work/'tmp'],work/'tmp',30)
    if name=='read-only-committed-root-preflight':
        committed=work/'preflight-read-only';staging=work/'preflight-quarantine'
        script='test -r "$1/predecessor"; if printf bad > "$1/predecessor"; then exit 11; fi; if chmod 0600 "$1/predecessor"; then exit 12; fi; if mkdir "$1/SpectreGeometry"; then exit 13; fi; printf allowed > "$2/output"'
        return sand(['/bin/sh','-eu','-c',script,'readonly-boundary-control',committed,staging],[committed],[staging,work/'home',work/'tmp'],staging,30)
    if name=='curl-version':argv=['/usr/bin/curl','--disable','--version'];seconds=30
    for pin in pins:
        base=['/usr/bin/git','-c','core.hooksPath=/dev/null','-c','core.fsmonitor=false','-C',str(work/'packages'/pin['name'])]
        variants={'init':(['init','--quiet'],30,False),'remote':(['remote','add','origin',pin['url']],30,False),
                  'fetch':(['fetch','--quiet','--depth=1','--no-tags',pin['url'],pin['rev']],300,True),
                  'checkout':(['checkout','--quiet','--detach',pin['rev']],60,False)}
        for variant,(tail,timeout,sessions) in variants.items():
            if name==pin['name']+'-'+variant:argv=base+tail;seconds=timeout;allowed=sessions
    if argv is not None:return {'name':name,'argv':argv,'cwd':str(work),'env':env,'requested_timeout_seconds':seconds,'allowed_sessions':allowed}
    if name in ['cache-bootstrap','cache-get','cache-lookup']:
        env.pop('LEAN_PATH');env['MATHLIB_CACHE_DIR']=str(work/'cache')
        writable=[work/'home',work/'tmp',work/'cache',*[work/'packages'/p['name']/'.lake' for p in pins]]
        sources=[work/'packages'];cache=work/'bootstrap/cache'
        if name=='cache-bootstrap':argv=[runtime/'bin/lake','build','cache'];seconds=900
        else:
            sources.append(work/'bootstrap')
            if name=='cache-get':argv=[runtime/'bin/lake','env',cache,'get','--cache-from=master,legacy',*c['cache_roots']];seconds=1800
            else:
                f.need(bool(cache_modules),'cache lookup closure missing')
                argv=[runtime/'bin/lake','env',cache,'lookup',*cache_modules];seconds=180
        return sand(argv,sources,writable,work/'packages/mathlib',seconds,network=name=='cache-get')
    original=name.startswith('compile-original-')
    phase='compile' if name.startswith('compile-') else 'check' if name.startswith('check-') else None
    f.need(phase is not None,'unrecognized command name')
    m=name[len('compile-original-'):] if original else name[len(phase)+1:]
    f.need(m in (TARGETS if original else c['module_order']),'unrecognized command module')
    if m not in c['init_only_order']:
        env['MATHLIB_CACHE_DIR']=str(work/'cache');env['LEAN_PATH']=':'.join([str(work/'objects'),*search,str(runtime/'lib/lean')])
    if original:
        staging=work/'original-output'/m;view=work/'original-prerequisites'/m
        current_search=[] if m in c['init_only_order'] else search
        env['LEAN_PATH']=':'.join([str(view),*current_search,str(runtime/'lib/lean')])
        return sand(compile_argv(runtime,work/'original-input',staging,m),[work/'packages',work/'original-input',view],[staging,work/'home',work/'tmp'],work/'original-input',180)
    staging=work/'quarantine'/m
    return sand(compile_argv(runtime,work/'src',staging,m) if phase=='compile' else [runtime/'bin/leanchecker',m],
                [work/'packages',work/'src',work/'objects'],[staging,work/'home',work/'tmp'] if phase=='compile' else [work/'home',work/'tmp'],work/'src',180 if phase=='compile' else 120)


def command_order(c):
    pins=f.load_json(VENDOR/'locks/dependencies.json')['packages']
    result=['bwrap-preflight','read-only-committed-root-preflight']
    def modules(names):
        for m in names:
            if m in TARGETS:result.append('compile-original-'+m)
            result.extend(['compile-'+m,'check-'+m])
    modules(c['init_only_order']);result.append('curl-version')
    result.extend(p['name']+'-'+variant for p in pins for variant in ['init','remote','fetch','checkout'])
    result.extend(['cache-bootstrap','cache-get','cache-lookup']);modules(c['module_order'][10:])
    return result


def validate_command_spec(c,work,r,cache_modules=()):
    expected=command_spec(c,work,r['name'],cache_modules)
    for key in ['name','argv','cwd','env','requested_timeout_seconds']:
        f.need(r[key]==expected[key],'full command provenance differs: '+key)
    f.need(r['new_sessions_explicitly_allowed']==expected['allowed_sessions'],'command session policy differs')
    f.need(r['limits']=={k:LIMITS[k] for k in ['address_space_bytes','rss_tree_bytes','max_created_file_bytes']}
           and r['max_log_bytes']==LIMITS['per_command_log_max_bytes'],'command limits differ')
    f.need(type(r['effective_timeout_seconds']) is int and 0<r['effective_timeout_seconds']<=expected['requested_timeout_seconds'],'effective timeout differs')


def run(c,contract_sha,work,watchdog):
    validate_contract(c,reviewed=True);validate_inputs(c)
    f.need(os.environ.get('GITHUB_REF')=='refs/heads/'+c['publication_branch'],'unexpected smoke branch')
    f.need(a.git_capture(ROOT,'rev-parse','HEAD').decode().strip()==os.environ.get('GITHUB_SHA'),'workflow commit mismatch')
    f.need(not a.git_capture(ROOT,'status','--porcelain=v1','--untracked-files=all','--ignored'),'workflow checkout not clean')
    f.no_symlink_path(work);f.need(not work.exists(),'workspace must be new');work.mkdir()
    for n in ['logs','evidence','packages','home','tmp','cache','objects','bootstrap','quarantine','original-input','original-output','original-prerequisites','native-captures']:(work/n).mkdir()
    commands=[];receipts=[];probes=[];checked=set();prior={};runtime=None;env={};search=[];cache_rows={}
    result={'schema':SCHEMA,'status':'INCOMPLETE','contract_sha256':contract_sha,'command_count':0,'complete_log_bytes':0,
            'workflow_commit':os.environ.get('GITHUB_SHA'),'run_id':os.environ.get('GITHUB_RUN_ID'),'run_attempt':os.environ.get('GITHUB_RUN_ATTEMPT'),
            'full_official_verification_claimed':False,'fresh_external_source_rebuild':False,'cache_bytes_trusted_not_source_authenticated':True,
            'owned_objects_from_prior_runs':False,'original_probes_use_corrected_prerequisites':True}
    a.write_json(work/'evidence/result.json',result)
    def command(name,argv,*,cwd=None,env=None,seconds=1800,rss=8*GIB,allowed_sessions=False,expect_success=True):
        watchdog.check();requested=seconds;seconds=min(seconds,max(1,int(watchdog.deadline-time.monotonic())))
        # Existing session policy validates exact pinned Git fetch arguments.
        a.validate_session_policy(name,list(map(str,argv)),allowed_sessions,work,c)
        selected=f.load_json(work/'evidence/selected-cache-closure.json')['modules'] if (work/'evidence/selected-cache-closure.json').exists() else []
        spec=command_spec(c,work,name,[r['module'] for r in selected])
        f.need(list(map(str,argv))==list(map(str,spec['argv'])) and str(cwd or work)==spec['cwd'] and env==spec['env'] and requested==spec['requested_timeout_seconds'] and allowed_sessions==spec['allowed_sessions'],'native command differs before execution')
        out=work/'native-captures'/(name+'.stdout');err=work/'native-captures'/(name+'.stderr')
        watchdog.in_command=True
        limits={k:LIMITS[k] for k in ['address_space_bytes','rss_tree_bytes','max_created_file_bytes']}
        try:r=f.run_process(list(map(str,argv)),cwd=cwd or work,env=env or a.safe_env(runtime or Path('/usr'),work/'home',work/'tmp'),timeout=seconds,stdout=out,stderr=err,max_log_bytes=LIMITS['per_command_log_max_bytes'],limits=limits,allow_new_sessions=allowed_sessions)
        finally:
            watchdog.in_command=False
            if watchdog.expired:watchdog.failure_receipt_grace()
        r.update(name=name,argv=list(map(str,argv)),cwd=str(cwd or work),env=dict(env or a.safe_env(runtime or Path('/usr'),work/'home',work/'tmp')),requested_timeout_seconds=requested,effective_timeout_seconds=seconds,
                 limits=limits,max_log_bytes=LIMITS['per_command_log_max_bytes'],capture_status='excluded_pending_safety_and_bounds')
        commands.append(r);result['command_count']=len(commands)
        def persist():
            (work/'evidence/commands.jsonl').write_text(''.join(json.dumps(x,sort_keys=True,separators=(',',':'))+'\n' for x in commands))
            a.write_json(work/'evidence/last_command.json',r);a.write_json(work/'evidence/result.json',result)
        persist()
        # Do not hash, read, copy, or otherwise admit native captures before this gate.
        if not clean_command(r):
            r['capture_status']='excluded_unsafe_native_result';persist()
            raise f.Rejected('unsafe/incomplete command; native captures excluded: '+name)
        watchdog.check()
        stdout_data=read_capture(out,LIMITS['per_command_log_max_bytes'],watchdog)
        stderr_data=read_capture(err,LIMITS['per_command_log_max_bytes'],watchdog)
        f.need(len(stdout_data)+len(stderr_data)<=LIMITS['per_command_log_max_bytes'],'combined native capture bound')
        for stream,data in [('stdout',stdout_data),('stderr',stderr_data)]:
            r[stream+'_sha256']=f.sha(data)
            (work/'logs'/(name+'.'+stream)).write_bytes(data)
        r['capture_status']='accepted_bounded_complete'
        r['captures']={stream:{'bytes':len(data),'sha256':f.sha(data)} for stream,data in [('stdout',stdout_data),('stderr',stderr_data)]}
        result['complete_log_bytes']+=len(stdout_data)+len(stderr_data)
        persist();f.need(result['complete_log_bytes']<=LIMITS['aggregate_log_max_bytes'],'aggregate log bound')
        if name.startswith('compile-') and not name.startswith('compile-original-'):
            text=(stdout_data+stderr_data).decode('utf-8')
            f.need(not re.search(r"(?im)(^.*\berror:|\bsorry\b|declaration uses .sorry.)",text),'candidate error/sorry diagnostic')
        ok=r['exit_code']==0
        f.need(ok or not expect_success,'command failed: '+name)
        return work/'logs'/(name+'.stdout'),ok
    def compile_one(module):
        nonlocal prior
        row=owned[module];rel=module.replace('.','/')
        f.need(shutil.disk_usage(work).free>=LIMITS['minimum_free_disk_bytes'],'minimum disk reserve')
        staging=work/'quarantine'/module;staging.mkdir();(staging/rel).parent.mkdir(parents=True,exist_ok=True)
        imports=a.direct_import_receipt(row,owned,checked,prior,cache_rows,runtime)
        kw=dict(runtime=runtime,sources=[work/'packages',work/'src',work/'objects'],writable=[staging,work/'home',work/'tmp'],cwd=work/'src',env=env)
        f.need(str(staging) not in env['LEAN_PATH'].split(':'),'quarantine is import root')
        a.namespace_providers([work/'objects',*[Path(s) for s in search],runtime/'lib/lean'])
        command('compile-'+module,a.sandbox(compile_argv(runtime,work/'src',staging,module),**kw),env=env,seconds=180,allowed_sessions=True)
        prior=a.admit_quarantine(staging,work/'objects',module,prior,LIMITS['owned_output_max_bytes']);shutil.rmtree(staging)
        kw['writable']=[work/'home',work/'tmp']
        command('check-'+module,a.sandbox([runtime/'bin/leanchecker',module],**kw),env=env,seconds=120,allowed_sessions=True)
        for name in a.module_outputs(module):f.need(f.file_sha(work/'objects'/name)==prior[name]['sha256'],'object changed during checker')
        checked.add(module)
        receipt={'module':module,'source_sha256':row['sha256'],'ordered_imports':imports,
                 'outputs':{n:prior[n] for n in sorted(a.module_outputs(module))},'compiler_command':len(commands)-2,'checker_command':len(commands)-1,'checker_passed':True}
        receipts.append(receipt)
        with (work/'evidence/owned-modules.jsonl').open('a') as h:h.write(json.dumps(receipt,sort_keys=True,separators=(',',':'))+'\n')
        result['checked_owned_module_count']=len(checked);a.write_json(work/'evidence/result.json',result)
        print(json.dumps({'phase':'corrected_compile_and_kernel_check','module':module,'completed':len(checked),'total':174}),flush=True)
    def probe_original(module):
        rel=module.replace('.','/');staging=work/'original-output'/module;staging.mkdir();(staging/rel).parent.mkdir(parents=True,exist_ok=True)
        before=a.verify_owned_final(work/'objects',prior,LIMITS['owned_output_max_bytes'])
        imports=a.direct_import_receipt(owned[module],owned,checked,prior,cache_rows,runtime)
        view=work/'original-prerequisites'/module;view.mkdir()
        needed=set(c['target_closures'][module])-{module}
        f.need(needed<=checked,'original prerequisite not freshly kernel-checked')
        view_map={n:prior[n] for m in needed for n in a.module_outputs(m)}
        planned_view_bytes=sum(r['bytes'] for r in view_map.values())
        f.need(shutil.disk_usage(work).free>=planned_view_bytes+LIMITS['minimum_free_disk_bytes'],'insufficient disk before original prerequisite view copy')
        for name in sorted(view_map):
            dest=view/name;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(work/'objects'/name,dest);dest.chmod(0o444)
        f.need(a.checked_inventory(view,maximum=LIMITS['owned_output_max_bytes'])['files']==view_map,'exact original prerequisite view differs')
        probe_env=dict(env);probe_env['LEAN_PATH']=':'.join([str(view),*search,str(runtime/'lib/lean')])
        kw=dict(runtime=runtime,sources=[work/'packages',work/'original-input',view],writable=[staging,work/'home',work/'tmp'],cwd=work/'original-input',env=probe_env)
        f.need(shutil.disk_usage(work).free>=LIMITS['minimum_free_disk_bytes'],'insufficient disk reserve before original compilation')
        try:
            out,ok=command('compile-original-'+module,a.sandbox(compile_argv(runtime,work/'original-input',staging,module),**kw),env=probe_env,seconds=180,allowed_sessions=True,expect_success=False)
        except Exception:
            probes.append({'module':module,'source_sha256':c['originals'][module]['sha256'],'status':'INCOMPLETE_NATIVE_RESULT','original_objects_admitted':False})
            a.write_json(work/'evidence/original-probes.json',probes);raise
        f.need(a.verify_owned_final(work/'objects',prior,LIMITS['owned_output_max_bytes'])==before,'original probe changed corrected objects')
        f.need(a.checked_inventory(view,maximum=LIMITS['owned_output_max_bytes'])['files']==view_map,'original probe changed prerequisite view')
        row={'module':module,'source_sha256':c['originals'][module]['sha256'],'command':len(commands)-1,
             'corrected_prerequisite_imports':imports,'exact_prerequisite_modules':sorted(needed),'exact_prerequisite_objects':view_map,
             'corrected_object_inventory_unchanged':True,
             'corrected_object_inventory_sha256':f.sha(f.json_bytes(before)),
             'physical_grid_uses_corrected_deformation':module==TARGETS[3], 'original_objects_admitted':False}
        if ok:
            row['status']='UNEXPECTED_ORIGINAL_PASS'
            f.need(module==TARGETS[3],'observed original compiler failure did not reproduce')
            probes.append(row);a.write_json(work/'evidence/original-probes.json',probes)
            raise f.Rejected('PhysicalGrid original unexpectedly passed; stop for source-scope review')
        else:
            try:
                f.need(commands[-1]['exit_code']==1,'original failed with unexpected exit code')
                row['diagnostics']=failure_diagnostics(module,out.read_text()+ (work/'logs'/('compile-original-'+module+'.stderr')).read_text())
            except Exception:
                row['status']='UNEXPECTED_ORIGINAL_REJECTION';row['exit_code']=commands[-1]['exit_code']
                probes.append(row);a.write_json(work/'evidence/original-probes.json',probes);raise
            row['status']='PREDICTED_VISIBILITY_FAILURE_OBSERVED' if module==TARGETS[3] else 'OBSERVED_VISIBILITY_FAILURE_REPRODUCED'
        raw=a.checked_inventory(staging,maximum=512*1024**2)
        f.need(set(raw['files'])<=a.module_outputs(module),'unexpected original probe output')
        row['isolated_diagnostic_outputs']=raw
        probes.append(row);a.write_json(work/'evidence/original-probes.json',probes)
        shutil.rmtree(staging);shutil.rmtree(view)
    terminal=False
    try:
        extraction=a.extract_owned_sources(ROOT/'owned-sources.tar.gz',work/'source-input',c)
        a.write_json(work/'evidence/source-extraction.json',extraction)
        owned=validate_graph(c,work)
        shutil.copytree(work/'source-input/src',work/'src')
        source_before=a.checked_inventory(work/'src',maximum=LIMITS['owned_source_max_bytes'])
        for module,row in c['originals'].items():
            p=work/'original-input'/(module.replace('.','/')+'.lean');p.parent.mkdir(parents=True,exist_ok=True)
            shutil.copyfile(ROOT/row['path'],p);p.chmod(0o444)
        original_before=a.checked_inventory(work/'original-input',maximum=LIMITS['owned_source_max_bytes'])
        runtime=acquire_runtime(work,env,command)
        for module in c['init_only_order']:
            if module==TARGETS[0]:probe_original(module)
            compile_one(module)
        result['init_only_actual_original_corrected_control_passed']=True;a.write_json(work/'evidence/result.json',result)
        pins,before,inventories,search,cache_rows=acquire_cache(c,work,runtime,env,command)
        for module in c['module_order'][10:]:
            if module in TARGETS[1:]:probe_original(module)
            compile_one(module)
        f.need(checked==set(c['module_order']) and len(receipts)==174 and {p['module'] for p in probes}==set(TARGETS),'corrected/probe coverage differs')
        final=a.verify_owned_final(work/'objects',prior,LIMITS['owned_output_max_bytes'])
        a.write_json(work/'evidence/fresh-owned-objects.json',final)
        f.need(a.checked_inventory(work/'src',maximum=LIMITS['owned_source_max_bytes'])==source_before,'corrected sources changed')
        f.need(a.checked_inventory(work/'original-input',maximum=LIMITS['owned_source_max_bytes'])==original_before,'original sources changed')
        for pin in pins:
            name=pin['name'];p=work/'packages'/name
            f.need(a.source_snapshot(p,pin)==before[name],'dependency source changed during consumers')
            f.need(a.checked_inventory(p/'.lake/build',maximum=4*GIB,allow_links=True)==inventories[name],'dependency objects changed during consumers')
        f.need(f.file_sha(work/'bootstrap/cache')==f.load_json(work/'evidence/cache-client-binary.json')['sha256'],'bootstrap client changed during consumers')
        revalidate_runtime(work/'runtime',f.load_json(work/'evidence/runtime-inventory.json'))
        validate_inputs(c)
        f.need(f.file_sha(ROOT/'smoke-contract.json')==contract_sha,'contract changed during run')
        f.need(f.file_sha(ROOT/'owned-sources.tar.gz')==c['source_archive']['sha256'],'source archive changed during run')
        validate_workflow(c,contract_sha)
        result['protected_inputs_and_runtime_revalidated']=True
        result['terminal_receipts']={name:f.file_sha(work/'evidence'/name) for name in [
            'source-extraction.json','runtime-inventory.json','read-only-boundary-preflight.json','dependency-sources.json',
            'selected-cache-closure.json','cached-build-inventory.json','selected-cache-admission.json','cache-client-binary.json',
            'commands.jsonl','owned-modules.jsonl','original-probes.json','fresh-owned-objects.json']}
        watchdog.check();terminal=True
    except Exception as error:
        result['status']='FAILED_OR_INCOMPLETE';result['error']=str(error);raise
    finally:
        a.write_json(work/'evidence/result.json',result)
        try:
            copy_logs(work)
            a.checked_inventory(work/'evidence',maximum=LIMITS['evidence_max_bytes']-8192)
            if terminal:
                watchdog.check();result['status']=SUCCESS;result['complete_evidence']=True
                a.write_json(work/'evidence/result.json',result)
                verify_success(c,contract_sha,work/'evidence',work)
                watchdog.check()
        except Exception as error:
            result['status']='FAILED_EVIDENCE_COLLECTION';result['complete_evidence']=False;result['collection_error']=str(error)
            a.write_json(work/'evidence/result.json',result);raise


EVIDENCE_NAMES={'result.json','commands.jsonl','last_command.json','source-extraction.json','runtime-inventory.json',
 'read-only-boundary-preflight.json','dependency-sources.json','selected-cache-closure.json','cached-build-inventory.json',
 'selected-cache-admission.json','cache-client-binary.json','cache-downloads.json','owned-modules.jsonl',
 'original-probes.json','fresh-owned-objects.json','capture-collection-scope.json'}

def validate_capture_collection(c,work,watchdog):
    names=command_order(c);allowed_logs={name+'.'+stream for name in names for stream in ['stdout','stderr']}
    for directory in ['evidence','logs','native-captures']:
        f.no_symlink_path(work/directory)
    allowed=EVIDENCE_NAMES|{'logs/'+name for name in allowed_logs}
    for p in (work/'evidence').rglob('*'):
        f.need(not p.is_symlink(),'evidence symlink')
        if p.is_dir():f.need(p.relative_to(work/'evidence').as_posix()=='logs','unexpected evidence directory');continue
        st=p.lstat();f.need(stat.S_ISREG(st.st_mode) and st.st_nlink==1 and p.relative_to(work/'evidence').as_posix() in allowed,'unexpected/nonregular evidence member')
    f.need({p.name for p in (work/'logs').glob('*')}<=allowed_logs,'unexpected admitted log')
    f.need({p.name for p in (work/'native-captures').glob('*')}<=allowed_logs,'unexpected native capture')
    commands=[];path=work/'evidence/commands.jsonl'
    if path.exists():
        data=read_capture(path,8*1024**2,watchdog);f.need(data.endswith(b'\n'),'truncated commands')
        commands=[f.parse_json(line) for line in data.splitlines()]
    f.need([r['name'] for r in commands]==names[:len(commands)],'incomplete native command prefix differs')
    selected=[];path=work/'evidence/selected-cache-closure.json'
    if path.exists():selected=f.parse_json(read_capture(path,2*1024**2,watchdog))['modules']
    accepted=set();omitted=[];total=0
    for r in commands:
        validate_command_spec(c,work,r,[x['module'] for x in selected])
        if r['capture_status']!='accepted_bounded_complete':
            omitted.append({'command':r['name'],'reason':'native_captures_not_safety_admitted'});continue
        f.need(clean_command(r),'unsafe capture marked accepted')
        f.need(set(r['captures'])=={'stdout','stderr'},'capture receipt streams differ')
        combined=0
        for stream in ['stdout','stderr']:
            name=r['name']+'.'+stream;row=r['captures'][stream]
            f.need(set(row)=={'bytes','sha256'} and type(row['bytes']) is int and 0<=row['bytes']<=LIMITS['per_command_log_max_bytes'] and f.SHA256.fullmatch(row['sha256']),'capture pin malformed')
            # Raw native captures are never revisited. Only already safety-admitted host copies are read.
            data=read_capture(work/'logs'/name,LIMITS['per_command_log_max_bytes'],watchdog)
            f.need(len(data)==row['bytes'] and f.sha(data)==row['sha256']==r[stream+'_sha256'],'admitted log changed')
            combined+=len(data);accepted.add(name)
        f.need(combined<=LIMITS['per_command_log_max_bytes'],'combined capture overflow');total+=combined
    raw_names={p.name for p in (work/'native-captures').glob('*')}
    for name in names[len(commands):]:
        if any(name+'.'+stream in raw_names for stream in ['stdout','stderr']):
            omitted.append({'command':name,'reason':'native_helper_returned_no_admissible_receipt'})
    f.need({p.name for p in (work/'logs').glob('*')}==accepted,'unadmitted host log')
    for p in (work/'evidence/logs').glob('*'):
        f.need(p.name in accepted,'unadmitted evidence log')
        data=read_capture(p,LIMITS['per_command_log_max_bytes'],watchdog)
        host=read_capture(work/'logs'/p.name,LIMITS['per_command_log_max_bytes'],watchdog)
        f.need(data==host,'evidence log changed from admitted host copy')
    f.need(total<=LIMITS['aggregate_log_max_bytes'],'aggregate admitted log overflow')
    a.write_json(work/'evidence/capture-collection-scope.json',{'native_capture_omissions':omitted,'all_native_captures_admitted':not omitted,'admitted_bytes':total})
    return omitted


def copy_logs(work):
    total=0;dest=work/'evidence/logs';dest.mkdir(exist_ok=True)
    for p in sorted((work/'logs').glob('*')):
        s=p.lstat();f.need(stat.S_ISREG(s.st_mode) and s.st_nlink==1,'nonregular log')
        total+=s.st_size;f.need(total<=LIMITS['aggregate_log_max_bytes']+2*LIMITS['per_command_log_max_bytes'],'interrupted aggregate logs bound')
        q=dest/p.name
        if not q.exists():shutil.copyfile(p,q)
        else:f.need(f.file_sha(q)==f.file_sha(p),'captured log changed')


def verify_success(c,contract_sha,evidence,work):
    result=f.load_json(evidence/'result.json')
    f.need(result['status']==SUCCESS and result['complete_evidence'] is True and result['contract_sha256']==contract_sha,'no complete smoke success')
    f.need(result['full_official_verification_claimed'] is False and result['owned_objects_from_prior_runs'] is False,'claim scope differs')
    f.need(f.sha((evidence/'runtime-inventory.json').read_bytes())==a.RUNTIME_INVENTORY_SHA,'terminal runtime inventory identity differs')
    expected_extraction={'schema':'authenticated-source-extraction-v1','archive':c['source_archive'],'source_file_count':174,'source_bytes':c['source_archive']['source_bytes'],'exact_source_tree':True,'all_source_pins_verified':True}
    f.need(f.load_json(evidence/'source-extraction.json')==expected_extraction,'source extraction receipt differs')
    for name,digest in result['terminal_receipts'].items():f.need(f.file_sha(evidence/name)==digest,'terminal evidence pin differs')
    required={'source-extraction.json','runtime-inventory.json','read-only-boundary-preflight.json','dependency-sources.json','selected-cache-closure.json','cached-build-inventory.json','selected-cache-admission.json','cache-client-binary.json','commands.jsonl','owned-modules.jsonl','original-probes.json','fresh-owned-objects.json'}
    f.need(set(result['terminal_receipts'])==required,'missing terminal receipt')
    commands=[f.parse_json(s) for s in (evidence/'commands.jsonl').read_bytes().splitlines()]
    modules=[f.parse_json(s) for s in (evidence/'owned-modules.jsonl').read_bytes().splitlines()]
    probes=f.load_json(evidence/'original-probes.json');objects=f.load_json(evidence/'fresh-owned-objects.json')['files']
    f.need(len(commands)==result['command_count'] and [r['module'] for r in modules]==c['module_order'] and result['checked_owned_module_count']==174,'success coverage differs')
    expected_outputs=set().union(*(a.module_outputs(m) for m in c['module_order']))
    f.need(set(objects)==expected_outputs,'object companion coverage differs')
    total=0;names=[]
    selected_lock=f.load_json(evidence/'selected-cache-closure.json');selected=selected_lock['modules']
    allowed={r['module']:r for r in f.load_json(VENDOR/'locks/required-modules.json')['modules']}
    f.need(selected_lock['roots']==c['cache_roots'] and selected_lock['maximum_locked_modules']==2805 and selected_lock['derived_from_authenticated_official_source_headers'] is True,'selected cache derivation scope differs')
    selected_names=[r['module'] for r in selected]
    f.need(selected_names==sorted(set(selected_names)) and set(c['cache_roots'])<=set(selected_names) and all(allowed.get(r['module'])==r for r in selected),'selected cache source rows differ')
    cache_rows=f.load_json(evidence/'selected-cache-admission.json');inventories=f.load_json(evidence/'cached-build-inventory.json')
    f.need(set(cache_rows)==set(selected_names),'cache admission membership differs')
    for row in selected:
        m=row['module'];prefix='lib/lean/'+m.replace('.','/')
        suffixes=['.olean','.ilean']+(['.olean.server','.olean.private','.ir.sig','.ir'] if row['modern_module'] else [])
        expected={**row,'companions':{prefix+suffix:inventories[row['package']]['files'][prefix+suffix] for suffix in suffixes}}
        f.need(cache_rows[m]==expected,'cached companion receipt differs')
    expected_preflight={'status':'READ_ONLY_PREDECESSOR_WRITES_CHMOD_AND_NAMESPACE_CREATION_REJECTED','quarantine_write_allowed':True,'fixture_sha256':f.sha(b'IMMUTABLE_BOUNDARY_FIXTURE_ONLY\n'),'not_a_research_proof':True}
    f.need(f.load_json(evidence/'read-only-boundary-preflight.json')==expected_preflight,'read-only preflight receipt differs')
    dependencies=f.load_json(evidence/'dependency-sources.json');pins=f.load_json(VENDOR/'locks/dependencies.json')['packages']
    f.need(set(dependencies)=={p['name'] for p in pins},'dependency receipt coverage differs')
    for pin in pins:
        receipt=dependencies[pin['name']]
        f.need(receipt['revision']==pin['rev'] and receipt['repository']==pin['url'],'dependency source pin differs')
    for row in selected:f.need(dependencies[row['package']]['files'][row['path']]['sha256']==row['sha256'],'selected dependency source hash differs')
    client=f.load_json(evidence/'cache-client-binary.json')
    f.need(set(client)=={'sha256','bytes','built_from_official_sources'} and type(client['sha256']) is str and f.SHA256.fullmatch(client['sha256']) and type(client['bytes']) is int and 0<client['bytes']<=512*1024**2 and client['built_from_official_sources'] is True,'cache client receipt schema differs')
    runtime_inv=f.load_json(evidence/'runtime-inventory.json')
    owned={r['module']:r for r in c['modules']}
    def expected_imports(module):
        out=[]
        for dep in dict.fromkeys([*owned[module]['ordered_imports'],'Init']):
            if dep in owned:out.append({'module':dep,'provider':'fresh_owned','companions':{p:objects[p] for p in sorted(a.module_outputs(dep))}})
            elif dep in cache_rows:out.append({'module':dep,'provider':'explicitly_trusted_official_cache','source_sha256':cache_rows[dep]['sha256'],'companions':cache_rows[dep]['companions']})
            else:out.append({'module':dep,'provider':'official_runtime','object_sha256':runtime_inv['files']['lib/lean/'+dep.replace('.','/')+'.olean']['sha256']})
        return out
    f.need([r['name'] for r in commands]==command_order(c),'full native command sequence differs')
    for i,r in enumerate(commands):
        name=r['name'];f.need(re.fullmatch(r'[A-Za-z0-9_.-]+',name) and '..' not in name and name not in names,'unsafe/duplicate command name');names.append(name)
        f.need(clean_command(r) and r['capture_status']=='accepted_bounded_complete','unsafe command receipt')
        validate_command_spec(c,work,r,[x['module'] for x in selected])
        f.need(r['limits']=={k:LIMITS[k] for k in ['address_space_bytes','rss_tree_bytes','max_created_file_bytes']} and r['max_log_bytes']==LIMITS['per_command_log_max_bytes'],'command resource profile differs')
        f.need(0<r['effective_timeout_seconds']<=r['requested_timeout_seconds']<=1800,'command timeout differs')
        for stream in ['stdout','stderr']:
            p=evidence/'logs'/(name+'.'+stream);s=p.lstat();f.need(stat.S_ISREG(s.st_mode) and s.st_nlink==1 and f.file_sha(p)==r[stream+'_sha256'],'log absent/changed');total+=s.st_size
        if not name.startswith('compile-original-'):f.need(r['exit_code']==0,'non-probe failure in success evidence')
    f.need(total==result['complete_log_bytes'] and total<=LIMITS['aggregate_log_max_bytes'],'aggregate logs differ')
    expected_pairs=[phase+'-'+m for m in c['module_order'] for phase in ['compile','check']]
    f.need([n for n in names if n.startswith(('compile-','check-')) and not n.startswith('compile-original-')]==expected_pairs,'compile/check sequence differs')
    for row in modules:
        m=row['module'];i=row['compiler_command'];j=row['checker_command'];f.need(j==i+1 and row['checker_passed'] is True,'checker receipt invalid')
        f.need(commands[i]['name']=='compile-'+m and commands[j]['name']=='check-'+m,'command receipt indexes differ')
        f.need(row['ordered_imports']==expected_imports(m),'candidate direct-import receipt differs')
        f.need(row['source_sha256']==c['inputs']['src/'+m.replace('.','/')+'.lean']['sha256'],'source receipt differs')
        f.need(row['outputs']=={n:objects[n] for n in sorted(a.module_outputs(m))},'object receipt differs')
        payload=(evidence/'logs'/('compile-'+m+'.stdout')).read_text()+(evidence/'logs'/('compile-'+m+'.stderr')).read_text()
        f.need(not re.search(r'(?im)(^.*\berror:|\bsorry\b|declaration uses .sorry.)',payload),'candidate error/sorry in acceptance evidence')
        argv=commands[i]['argv'];tail=list(map(str,compile_argv(work/'runtime',work/'src',work/'quarantine'/m,m)))
        f.need(argv[-len(tail):]==tail and '--share-net' not in argv,'compiler invocation differs')
        f.need(commands[i]['requested_timeout_seconds']==180 and commands[j]['requested_timeout_seconds']==120,'compile/check bounds differ')
        f.need(commands[j]['argv'][-2:]==[str(work/'runtime/bin/leanchecker'),m] and '--share-net' not in commands[j]['argv'],'checker invocation differs')
    f.need([p['module'] for p in probes]==[m for m in c['module_order'] if m in TARGETS],'original probe order differs')
    for p in probes:
        m=p['module'];r=commands[p['command']]
        f.need(r['name']=='compile-original-'+m and p['source_sha256']==c['originals'][m]['sha256'],'original source/command differs')
        f.need(p['corrected_prerequisite_imports']==expected_imports(m),'original direct-import receipt differs')
        needed=set(c['target_closures'][m])-{m}
        f.need(p['exact_prerequisite_modules']==sorted(needed) and p['exact_prerequisite_objects']=={n:objects[n] for x in needed for n in a.module_outputs(x)},'probe prerequisite map differs')
        prefix=c['module_order'][:c['module_order'].index(m)]
        prefix_map={n:objects[n] for x in prefix for n in a.module_outputs(x)}
        expected_inventory={'files':prefix_map,'bytes':sum(r['bytes'] for r in prefix_map.values())}
        f.need(p['corrected_object_inventory_sha256']==f.sha(f.json_bytes(expected_inventory)) and p['physical_grid_uses_corrected_deformation'] is (m==TARGETS[3]),'probe predecessor prefix checksum/label differs')
        f.need(p['corrected_object_inventory_unchanged'] is True and p['original_objects_admitted'] is False,'original probe isolation differs')
        tail=list(map(str,compile_argv(work/'runtime',work/'original-input',work/'original-output'/m,m)))
        f.need(r['argv'][-len(tail):]==tail and '--share-net' not in r['argv'] and r['requested_timeout_seconds']==180,'original invocation differs')
        text=(evidence/'logs'/(r['name']+'.stdout')).read_text()+(evidence/'logs'/(r['name']+'.stderr')).read_text()
        f.need(r['exit_code']!=0,'original unexpected pass cannot satisfy success')
        if r['exit_code']!=0:
            f.need(r['exit_code']==1 and p['status']==('PREDICTED_VISIBILITY_FAILURE_OBSERVED' if m==TARGETS[3] else 'OBSERVED_VISIBILITY_FAILURE_REPRODUCED'),'unexpected original exit/status')
            f.need(json.loads(json.dumps(failure_diagnostics(m,text)))==p['diagnostics'],'original diagnostic receipt differs')
    f.need(result['init_only_actual_original_corrected_control_passed'] is True and result['protected_inputs_and_runtime_revalidated'] is True,'missing early control or final revalidation')
    return result


def collect(c,contract_sha,work,watchdog):
    validate_contract(c)
    f.no_symlink_path(work);(work/'evidence').mkdir(parents=True,exist_ok=True)
    result=work/'evidence/result.json'
    if not result.exists():a.write_json(result,{'status':'INCOMPLETE_BEFORE_RECEIPT','full_official_verification_claimed':False})
    omissions=validate_capture_collection(c,work,watchdog)
    copy_logs(work)
    issue=None;verified=False
    try:verify_success(c,contract_sha,work/'evidence',work);verified=True
    except Exception as error:issue=str(error)
    upload=work/'upload';f.need(not upload.exists(),'upload directory must be new');upload.mkdir()
    rows=[];omitted=[];total=0
    for p in sorted((work/'evidence').rglob('*'),key=lambda p:(p.name!='result.json',p.as_posix())):
        f.need(not p.is_symlink(),'evidence symlink');s=p.lstat()
        if stat.S_ISDIR(s.st_mode):continue
        f.need(stat.S_ISREG(s.st_mode) and s.st_nlink==1,'nonregular evidence')
        f.need(len(rows)+len(omitted)<20000,'evidence count bound');rel=p.relative_to(work/'evidence').as_posix()
        if total+s.st_size>LIMITS['evidence_max_bytes']:omitted.append({'path':rel,'bytes':s.st_size});continue
        q=upload/rel;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q);total+=s.st_size
        rows.append({'path':rel,'bytes':s.st_size,'sha256':f.file_sha(q)})
    receipt={'schema':'bounded-visibility-smoke-evidence-v1','files':rows,'omitted':omitted,'bytes_copied':total,
             'all_available_files_copied':not omitted,'smoke_acceptance_evidence_complete':verified and not omitted and not omissions,'native_capture_omissions':omissions,
             'acceptance_blocker':issue,'runner_status':f.load_json(result).get('status'),'full_official_verification_claimed':False}
    data=f.json_bytes(receipt);f.need(len(data)<=LIMITS['collection_reserve_bytes'] and total+len(data)<=LIMITS['upload_max_bytes'],'collection manifest bound')
    (upload/'collection.json').write_bytes(data)
    f.need(not omitted,'evidence collection incomplete')
    f.need(receipt['runner_status']!=SUCCESS or receipt['smoke_acceptance_evidence_complete'],'claimed success has inconsistent evidence')
    print(json.dumps({k:v for k,v in receipt.items() if k not in ['files','omitted']},sort_keys=True))


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--contract-sha256',required=True);ap.add_argument('--work',type=Path,required=True);ap.add_argument('--collect',action='store_true');args=ap.parse_args()
    f.need(sys.flags.isolated and sys.dont_write_bytecode,'invoke with Python -I -B')
    work=args.work.absolute();f.need(args.work.is_absolute(),'work path must be absolute')
    # Collection has its separate fixed120-second host envelope. Acceptance run
    # includes imports, contract hashing and all host I/O in the7200-second clock.
    watchdog=a.HostDeadline(ENTRY_TIME+(120 if args.collect else 7200));watchdog.arm()
    try:
        c=f.pinned_load(ROOT/'smoke-contract.json',args.contract_sha256)
        if args.collect:collect(c,args.contract_sha256,work,watchdog)
        else:run(c,args.contract_sha256,work,watchdog)
    finally:watchdog.close()

if __name__=='__main__':main()
