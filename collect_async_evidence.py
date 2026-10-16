#!/usr/bin/env python3
"""Bounded evidence collection for a one-module scheduling diagnostic."""
import argparse,hashlib,importlib.util,json,math,re,shutil,stat,sys
from pathlib import Path
MAXIMUM=128*1024**2
RESERVE=4*1024**2
SUCCESS='ONE_MODULE_ASYNC_DIAGNOSTIC_COMPLETED'
TARGET='SpectreGeometry.PolygonProductKeyReferenceFinite'
SUFFIXES=['.olean','.olean.private','.olean.server','.ilean','.ir.sig','.ir','.c']
def need(ok,message):
    if not ok:raise ValueError(message)
def pairs(rows):
    out={}
    for k,v in rows:need(k not in out,'duplicate JSON key');out[k]=v
    return out
def load(path):return json.loads(path.read_text(),object_pairs_hook=pairs)
def sha(path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        for b in iter(lambda:f.read(1024**2),b''):h.update(b)
    return h.hexdigest()
def regular(path):
    s=path.lstat();need(stat.S_ISREG(s.st_mode) and s.st_nlink==1,'nonregular evidence');return s.st_size

def verify_complete(evidence,contract,contract_sha):
    r=load(evidence/'result.json');ready=load(evidence/'diagnostic-ready.json')
    need(r['status']==SUCCESS and r.get('complete_evidence') is True,'diagnostic did not complete')
    need(r['schema']==contract['schema'] and r['contract_sha256']==contract_sha,'contract identity differs')
    need(ready=={'result_sha256':sha(evidence/'result.json'),'contract_sha256':contract_sha},'completion marker differs')
    need(r['proof_certified'] is False and r['conditional_endpoint_replay_completed'] is False and r['final_C_proof_certified'] is False and r['unconditional_monotile_proof_certified'] is False,'diagnostic claim changed')
    need(r['source_sha256']==contract['target_sha256'] and r['baseline_contract_sha256']==contract['baseline_contract_sha256'],'source/baseline identity differs')
    need(r['runtime_inventory_sha256']==sha(evidence/'runtime-inventory.json')==contract['official_lean_inventory_sha256'],'runtime identity differs')
    need(r['cached_build_inventory_sha256']==sha(evidence/'cached-build-inventory.json'),'cache identity differs')
    need(r['source_extraction_receipt_sha256']==sha(evidence/'source-extraction.json'),'source extraction receipt differs')
    extraction=load(evidence/'source-extraction.json');need(extraction['archive']['sha256']==r['source_archive_sha256']=='cb50e75e182ecb21dd428b30a47eafed4af383ecb048ba92c0c2611dae2287c4' and extraction['source_file_count']==2481 and extraction['all_source_pins_verified'] is True and extraction['exact_source_tree'] is True,'source extraction identity differs')
    need(r['command_receipts_sha256']==sha(evidence/'commands.jsonl'),'command stream differs')
    commands=[json.loads(x,object_pairs_hook=pairs) for x in (evidence/'commands.jsonl').read_text().splitlines()]
    need(len(commands)==r['command_count'],'command count differs')
    spec=importlib.util.spec_from_file_location('diagnostic_expected_specs',Path(__file__).resolve().parent/'probe_async.py')
    api=importlib.util.module_from_spec(spec);sys.modules[spec.name]=api;spec.loader.exec_module(api)
    need(r['producer_work']==contract['work_root'],'producer work path differs')
    expected=api.expected_command_specs(r['producer_work'],r['profiles']['default']['accepted'])
    need(len(commands)==len(expected),'exact setup/control/profile command coverage differs')
    for cmd,want in zip(commands,expected):
        for key,value in want.items():need(cmd.get(key)==value,'complete command specification differs: '+want['name']+'/'+key)
    names=[];total=0;elapsed=0
    for cmd in commands:
        n=cmd['name'];need(isinstance(n,str) and re.fullmatch(r'[A-Za-z0-9_.-]+',n) and '..' not in n and n not in names,'unsafe/duplicate command name');names.append(n)
        need(not any(cmd[k] for k in ['timed_out','memory_exceeded','log_overflow','surviving_children']) and cmd['process_group_empty'] and cmd['descendants_empty'] and not(cmd['escaped_descendants'] and not cmd['new_sessions_explicitly_allowed']),'unsafe/incomplete command')
        need(cmd['limits']=={'address_space_bytes':12*1024**3,'rss_tree_bytes':8*1024**3,'max_created_file_bytes':512*1024**2},'command resource profile differs')
        need(cmd['allow_new_sessions'] is cmd['new_sessions_explicitly_allowed'],'session declaration differs')
        need(cmd['address_space_bytes']==12*1024**3 and cmd['max_created_file_bytes']==512*1024**2 and cmd['max_log_bytes']==contract['per_command_log_max_bytes'],'serialized command caps differ')
        duration=cmd['elapsed_seconds'];peak=cmd['peak_sampled_tree_rss_bytes'];need(type(duration) in (int,float) and math.isfinite(duration) and duration>=0 and type(peak) is int and 0<=peak<=8*1024**3,'resource observations differ');elapsed+=duration
        need(type(cmd['effective_timeout_seconds']) is int and 0<cmd['effective_timeout_seconds']<=cmd['requested_timeout_seconds'] and cmd['timeout_seconds']==cmd['effective_timeout_seconds'],'effective timeout differs')
        command_bytes=0
        for s in ['stdout','stderr']:
            q=evidence/'logs'/(n+'.'+s);size=regular(q);command_bytes+=size;total+=size;need(sha(q)==cmd[s+'_sha256'],'log differs')
        need(command_bytes<=contract['per_command_log_max_bytes'],'per-command log cap exceeded')
        need(cmd['exit_code']==0 or (n=='compile-profile-default' and cmd['exit_code']==134),'unexpected nonzero command')
    need(elapsed<=contract['aggregate_command_deadline_seconds'],'aggregate command elapsed cap exceeded')
    actual_logs={q.name for q in (evidence/'logs').iterdir() if regular(q)>=0};need(actual_logs=={n+'.'+s for n in names for s in ['stdout','stderr']},'extra or missing log')
    need(total==r['complete_log_bytes'] and total<=contract['aggregate_log_max_bytes'],'log size differs')
    need(set(r['profiles'])=={'default','async_off'},'profile coverage differs')
    baseline=Path(__file__).resolve().parent/'baseline'
    owned=load(baseline/'locks/owned-sources.json');target_row=next(x for x in owned['sources'] if x['module']==TARGET)
    required={x['module']:x for x in load(baseline/'locks/required-modules.json')['modules']}
    cached=load(evidence/'cached-build-inventory.json');runtime_inv=load(evidence/'runtime-inventory.json');expected_imports=[]
    for dep in [*target_row['ordered_imports'],'Init']:
        if dep in required:
            lock=required[dep];stem='lib/lean/'+dep.replace('.','/')
            suffixes=['.olean','.ilean']+(['.olean.server','.olean.private','.ir.sig','.ir'] if lock['modern_module'] else [])
            expected_imports.append({'module':dep,'provider':'explicitly_trusted_official_cache','source_sha256':lock['sha256'],'companions':{stem+x:cached[lock['package']]['files'][stem+x] for x in suffixes}})
        else:expected_imports.append({'module':dep,'provider':'official_runtime','object_sha256':runtime_inv['files']['lib/lean/'+dep.replace('.','/')+'.olean']['sha256']})
    indexes=[]
    for p,extra in [('default',[]),('async_off',['-DElab.async=false'])]:
        row=r['profiles'][p];frozen=load(evidence/('profile-'+p+'-frozen.json'))
        need(frozen==row and sha(evidence/('profile-'+p+'.json'))==row['receipt_sha256'],'profile checkpoint differs')
        need(row['ordered_imports']==expected_imports,'direct source/runtime/cache import receipt differs')
        need(row['profile']==p and row['source_sha256']==contract['target_sha256'] and row['extra_lean_arguments']==extra,'profile source/option differs')
        for n,digest in row['log_hashes'].items():
            need(re.fullmatch(r'[A-Za-z0-9_.-]+',n) and '..' not in n,'unsafe profile log');need(sha(evidence/'logs'/n)==digest,'profile log changed')
        i=row['compiler_command'];need(type(i) is int and 0<=i<len(commands),'invalid compiler index');indexes.append(i)
        cmd=commands[i];need(cmd['name']=='compile-profile-'+p and cmd['requested_timeout_seconds']==180,'wrong profile compiler')
        argv=cmd['argv'];inner=argv[argv.index('--')+1:]
        expected_prefix=[str(Path(inner[0]).parent/'lean'),'-j1','-M4096','-Dcompiler.postponeCompile=false',*extra]
        need(inner[:len(expected_prefix)]==expected_prefix and inner[-1].endswith('/src/'+TARGET.replace('.','/')+'.lean'),'profile compiler flags/source differ')
        need(inner.count('-DElab.async=false')==(p=='async_off'),'unexpected scheduling option')
        need(type(row['accepted']) is bool,'profile acceptance must be a boolean')
        if row['accepted']:
            need(row['status']=='COMPILED_KERNEL_CHECKED_AND_AUDITED' and cmd['exit_code']==0,'invalid accepted profile')
            j=row['checker_command'];k=row['audit_command'];need(type(j) is int and type(k) is int and j==i+1 and k==j+1 and k<len(commands),'profile command order differs')
            need(commands[j]['name']=='check-profile-'+p and commands[j]['argv'][-2:]==[str(Path(inner[0]).parent/'leanchecker'),TARGET] and commands[j]['requested_timeout_seconds']==120,'wrong checker')
            need(commands[k]['name']=='audit-profile-'+p and commands[k]['requested_timeout_seconds']==600,'wrong auditor')
            inventory_path=evidence/('profile-'+p+'-final-objects.json');need(sha(inventory_path)==row['final_output_inventory_sha256'],'final output inventory differs')
            inventory=load(inventory_path);need(inventory['files']==row['outputs'] and inventory['bytes']==sum(x['bytes'] for x in row['outputs'].values()),'profile output map differs from final inventory')
            need(set(row['outputs'])=={TARGET.replace('.','/')+s for s in SUFFIXES},'seven-companion receipt differs')
            for x in row['outputs'].values():need(type(x['bytes']) is int and 0<=x['bytes']<=512*1024**2 and re.fullmatch('[0-9a-f]{64}',x['sha256']),'invalid output receipt')
            text=(evidence/'logs'/('audit-profile-'+p+'.stdout')).read_text()
            need(text.splitlines().count('ASYNC_TARGET_RAW_AUDIT_PASSED_NO_FINAL_THEOREM')==1,'raw audit marker missing')
        else:
            need(p=='default' and row['status']=='BASELINE_THREAD_ABORT_REPRODUCED' and row['checker_command'] is None and row['audit_command'] is None and cmd['exit_code']==134,'unaccepted profile not allowed')
            need((evidence/'logs'/'compile-profile-default.stdout').read_bytes()==b'' and (evidence/'logs'/'compile-profile-default.stderr').read_text()=='libc++abi: terminating due to uncaught exception of type lean::exception: failed to create thread: Resource temporarily unavailable\n','different baseline failure')
    need(indexes==sorted(indexes) and len(set(indexes))==2 and r['profiles']['async_off']['accepted'] is True,'profile order/disabled success missing')
    for name,marker in [('DefaultOptionControl','ASYNC_OPTION_CONTROL_DEFAULT_TRUE'),('DisabledOptionControl','ASYNC_OPTION_CONTROL_DISABLED_FALSE')]:
        need(names.count('compile-control-'+name)==names.count('check-control-'+name)==1,'option control coverage differs')
        need((evidence/'logs'/('compile-control-'+name+'.stdout')).read_text().splitlines().count(marker)==1,'option behavior marker differs')
    need(names.count('compile-control-AuditAsyncTarget')==names.count('check-control-AuditAsyncTarget')==1,'auditor compile/check missing')
    need(type(r['baseline_reproduced']) is bool and r['baseline_reproduced']==(not r['profiles']['default']['accepted']),'baseline reproduction claim differs')
    need(r['cause_proven'] is False,'runtime cause overclaimed')
    return r

def collect(work,contract,contract_sha):
    evidence=work/'evidence';evidence.mkdir(parents=True,exist_ok=True);result=evidence/'result.json'
    if not result.exists():result.write_text(json.dumps({'status':'INCOMPLETE_BEFORE_RECEIPT'}))
    logs=evidence/'logs';logs.mkdir(exist_ok=True);log_total=0;omitted_logs=[]
    for q in sorted((work/'logs').glob('*')):
        size=regular(q)
        if log_total+size>contract['aggregate_log_max_bytes']+2*contract['per_command_log_max_bytes']:omitted_logs.append(q.name);continue
        log_total+=size;dest=logs/q.name
        if not dest.exists():shutil.copyfile(q,dest)
    issue=None;verified=False
    try:verify_complete(evidence,contract,contract_sha);verified=True
    except Exception as e:issue=str(e)
    upload=work/'upload';upload.mkdir(exist_ok=False);rows=[];omitted=[];total=0
    for q in sorted(evidence.rglob('*'),key=lambda q:(q.name!='result.json',q.as_posix())):
        need(not q.is_symlink(),'evidence symlink forbidden')
        if q.is_dir():continue
        need(len(rows)+len(omitted)<20000,'evidence entry count bound');size=regular(q);rel=str(q.relative_to(evidence))
        if total+size>MAXIMUM-RESERVE:omitted.append(rel);continue
        dest=upload/rel;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(q,dest);total+=size
        rows.append({'path':rel,'bytes':size,'sha256':sha(dest)})
    r={'schema':'bounded-async-diagnostic-evidence-v1','files':rows,'bytes_copied':total,'omitted':omitted,'interrupted_log_omissions':omitted_logs,'all_available_files_copied':not omitted and not omitted_logs,'diagnostic_evidence_complete':verified and not omitted and not omitted_logs,'acceptance_blocker':issue,'runner_status':load(result).get('status'),'proof_certified':False,'conditional_endpoint_replay_completed':False}
    data=(json.dumps(r,sort_keys=True,indent=2)+'\n').encode();need(len(data)<=RESERVE and total+len(data)<=MAXIMUM,'collection exceeds cap');(upload/'collection.json').write_bytes(data)
    return r
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--work',type=Path,required=True);a=ap.parse_args();root=Path(__file__).resolve().parent
    r=collect(a.work,load(root/'contract.json'),sha(root/'contract.json'));print(json.dumps({k:v for k,v in r.items() if k!='files'},sort_keys=True))
    if not r['all_available_files_copied'] or r['runner_status']==SUCCESS and not r['diagnostic_evidence_complete']:raise SystemExit(1)
