"""Exercise the real driver loop with explicitly synthetic acquisition/native seams.
No subprocess, network, ctypes or Lean is run. Seams: two acquisition functions,
native run_process, checkout metadata, activation file checks, and canonical
runtime SHA (synthetic only). Source extraction/graph, command grammar, safety
admission, quarantine, compile/check iteration, original isolation, final source
and runtime inventory checks, and terminal verifier remain the real functions.
"""
import copy, importlib.util, os
from pathlib import Path
from unittest.mock import patch

def run(d,c,parent):
    spec=importlib.util.spec_from_file_location('loop_seed',Path(__file__).parent/'inert_success_fixture.py');seed=importlib.util.module_from_spec(spec);spec.loader.exec_module(seed)
    seedwork=parent/'seed';fixture=seed.make(d,c,seedwork);work=parent/'run'
    active=copy.deepcopy(c);active['review_status']='reviewed_for_execution';active['independent_driver_review_sha256']='1'*64
    contract_sha=d.f.sha(d.f.json_bytes(active));native_calls=[]
    runtime_inv=d.f.load_json(seedwork/'evidence/runtime-inventory.json')
    for row in runtime_inv['files'].values():row['mode']=0o444
    runtime_sha=d.f.sha(d.f.json_bytes(runtime_inv))
    real_file_sha=d.f.file_sha
    def file_sha(path):return contract_sha if Path(path)==d.ROOT/'smoke-contract.json' else real_file_sha(path)
    def process(argv,**kw):
        native_calls.append(argv)
        stdout=b''
        if argv[:3]==['/usr/bin/curl','--disable','--version']:stdout=b'curl 8.0.0 synthetic fixture\n'
        if 'readonly-boundary-control' in argv:(work/'preflight-quarantine/output').write_bytes(b'allowed')
        if '-o' in argv:
            source=Path(argv[-1]);m=source.relative_to(work/('original-input' if 'original-input' in source.parts else 'src')).as_posix()[:-5].replace('/','.')
            if 'original-input' in source.parts:
                stdout=''.join(str(source)+f':{line}:{col or 3}: error: Unknown identifier `{helper}`\n' for line,col,helper in d.EXPECTED_UNKNOWN[m]).encode()
                code=1
            else:
                target=Path(argv[argv.index('-o')+1]);stem=str(target)[:-6]
                for suffix in d.a.SUFFIXES:Path(stem+suffix).write_bytes(('synthetic '+m.replace('.','/')+suffix).encode())
                code=0
        else:code=0
        kw['stdout'].write_bytes(stdout);kw['stderr'].write_bytes(b'')
        return {'exit_code':code,'timed_out':False,'log_overflow':False,'memory_exceeded':False,'surviving_children':False,'process_group_empty':True,'descendants_empty':True,'escaped_descendants':False,'new_sessions_explicitly_allowed':kw['allow_new_sessions']}
    def runtime_acquire(work,env,command):
        runtime=work/'runtime';runtime.mkdir()
        for m in c['runtime_roots']:
            p=runtime/'lib/lean'/(m.replace('.','/')+'.olean');p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(('synthetic '+m).encode());p.chmod(0o444)
        d.a.write_json(work/'evidence/runtime-inventory.json',runtime_inv)
        env.update(d.a.safe_env(runtime,work/'home',work/'tmp'));env['LEAN_PATH']=str(work/'objects')+':'+str(runtime/'lib/lean')
        command('bwrap-preflight',d.a.sandbox(['/bin/true'],runtime=runtime,sources=[],writable=[work/'home',work/'tmp'],cwd=work/'tmp',env=env),seconds=30,env=env,allowed_sessions=True)
        d.a.readonly_boundary_preflight(runtime,work,env,command)
        return runtime
    def cache_acquire(c,work,runtime,env,command):
        pins=d.f.load_json(d.VENDOR/'locks/dependencies.json')['packages']
        for pin in pins:(work/'packages'/pin['name']/'.lake/build/lib/lean').mkdir(parents=True)
        (work/'bootstrap/cache').write_bytes(b'synthetic client')
        selected=d.f.load_json(seedwork/'evidence/selected-cache-closure.json')
        d.a.write_json(work/'evidence/selected-cache-closure.json',selected)
        cache_rows=d.f.load_json(seedwork/'evidence/selected-cache-admission.json')
        for row in cache_rows.values():
            m=row['module']
            for name in row['companions']:
                suffix=name[len('lib/lean/'+m.replace('.','/')):];p=work/'packages'/row['package']/'.lake/build'/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(('synthetic '+m+suffix).encode())
        for name in ['dependency-sources.json','cached-build-inventory.json','selected-cache-admission.json','cache-client-binary.json']:
            d.a.write_json(work/'evidence'/name,d.f.load_json(seedwork/'evidence'/name))
        names=['curl-version']+[p['name']+'-'+v for p in pins for v in ['init','remote','fetch','checkout']]+['cache-bootstrap','cache-get','cache-lookup']
        for name in names:
            spec=d.command_spec(c,work,name,c['cache_roots'])
            command(name,spec['argv'],env=spec['env'],seconds=spec['requested_timeout_seconds'],allowed_sessions=spec['allowed_sessions'])
        search=[str(work/'packages'/p['name']/'.lake/build/lib/lean') for p in pins]
        env['MATHLIB_CACHE_DIR']=str(work/'cache');env['LEAN_PATH']=':'.join([str(work/'objects'),*search,str(runtime/'lib/lean')])
        return [],{},d.f.load_json(seedwork/'evidence/cached-build-inventory.json'),search,cache_rows
    def git(repo,*args):return b'2'*40+b'\n' if args==('rev-parse','HEAD') else b''
    watchdog=d.a.HostDeadline(d.time.monotonic()+120)
    with patch.object(d,'acquire_runtime',runtime_acquire),patch.object(d,'acquire_cache',cache_acquire),patch.object(d.f,'run_process',process),patch.object(d.a,'git_capture',git),patch.object(d,'validate_inputs',lambda c:None),patch.object(d,'validate_workflow',lambda c,h:None),patch.object(d.f,'file_sha',file_sha),patch.object(d.a,'RUNTIME_INVENTORY_SHA',runtime_sha),patch.dict(os.environ,{'GITHUB_REF':'refs/heads/'+c['publication_branch'],'GITHUB_SHA':'2'*40},clear=False):
        d.run(active,contract_sha,work,watchdog)
        d.verify_success(active,contract_sha,work/'evidence',work)
    return {'work':work,'contract':active,'contract_sha':contract_sha,'native_calls':len(native_calls)}
