#!/usr/bin/env python3
"""Collect bounded available evidence; only complete verified receipts admit replay."""
import argparse,hashlib,json,os,re,shutil,stat
from pathlib import Path
MAXIMUM=128*1024**2
RESERVE=4*1024**2
SUCCESS='CACHE_BACKED_CONDITIONAL_GEOMETRY_REPLAY_COMPLETED'
def need(ok,message):
    if not ok:raise ValueError(message)
def sha(path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        for b in iter(lambda:f.read(1024**2),b''):h.update(b)
    return h.hexdigest()
def pairs(rows):
    out={}
    for k,v in rows:need(k not in out,'duplicate JSON key');out[k]=v
    return out
def load(path):return json.loads(path.read_text(),object_pairs_hook=pairs)
def lines(path):return [json.loads(s,object_pairs_hook=pairs) for s in path.read_text().splitlines()]
def regular(path):
    s=path.lstat();need(stat.S_ISREG(s.st_mode) and s.st_nlink==1,'nonregular or hardlinked evidence');return s.st_size
def verify_complete(evidence,contract,contract_sha):
    result=load(evidence/'result.json')
    need(result['contract_sha256']==contract_sha,'result contract identity differs')
    need(result['status']==SUCCESS and result.get('complete_evidence') is True,'runner did not reach complete conditional success')
    need(result.get('conditional_C_remains_explicit') is True and result.get('final_C_proof_certified') is False and result.get('unconditional_monotile_proof_certified') is False,'conditional claim changed')
    extraction=load(evidence/'source-extraction.json')
    need(sha(evidence/'source-extraction.json')==result['source_extraction_receipt_sha256'],'source extraction receipt hash differs')
    need(result['source_archive_sha256']==contract['source_archive']['sha256'],'source archive receipt identity differs')
    expected_extraction={'schema':'authenticated-source-extraction-v1','archive':contract['source_archive'],'source_file_count':contract['owned_module_count'],'source_bytes':contract['source_archive']['source_bytes'],'exact_source_tree':True,'all_source_pins_verified':True}
    need(extraction==expected_extraction,'source extraction receipt differs')
    commands=lines(evidence/'commands.jsonl');modules=lines(evidence/'owned-modules.jsonl')
    need(len(commands)==result['command_count'] and len(modules)==result['checked_owned_module_count']==2481,'receipt counts differ')
    need([r['module'] for r in modules]==[r['module'] for r in contract['modules']],'module receipt coverage differs')
    for name,key in [('commands.jsonl','command_receipts_sha256'),('owned-modules.jsonl','owned_module_receipts_sha256'),('fresh-owned-objects.json','owned_output_inventory_sha256'),('cached-build-inventory.json','cached_build_inventory_sha256'),('runtime-inventory.json','runtime_inventory_sha256')]:
        need(sha(evidence/name)==result[key],'terminal receipt hash differs: '+name)
    objects=load(evidence/'fresh-owned-objects.json')['files']
    suffixes=['.olean','.olean.private','.olean.server','.ilean','.ir.sig','.ir','.c']
    expected_outputs={r['module'].replace('.','/')+suffix for r in contract['modules'] for suffix in suffixes}
    need(set(objects)==expected_outputs,'owned object inventory coverage differs')
    names=[];log_bytes=0
    for command in commands:
        name=command['name'];need(isinstance(name,str) and re.fullmatch(r'[A-Za-z0-9_.-]+',name) and '..' not in name,'unsafe command log name')
        need(name not in names,'duplicate command name');names.append(name)
        need(command['exit_code']==0 and not any(command[k] for k in ['timed_out','log_overflow','memory_exceeded','surviving_children']) and command['process_group_empty'] and command['descendants_empty'],'unsuccessful command in success evidence')
        for stream in ['stdout','stderr']:
            p=evidence/'logs'/(name+'.'+stream);log_bytes+=regular(p);need(sha(p)==command[stream+'_sha256'],'missing, partial, or changed command log')
    need(log_bytes==result['complete_log_bytes'] and log_bytes<=contract['aggregate_log_max_bytes'],'complete log byte count differs')
    pairs=[name for name in names if name.startswith(('compile-','check-')) and not name.startswith(('compile-auditor-','check-auditor-'))]
    expected_pairs=[phase+'-'+r['module'] for r in contract['modules'] for phase in ['compile','check']]
    need(pairs==expected_pairs,'ordered compile/check coverage differs')
    for row in modules:
        module=row['module'];source='src/'+module.replace('.','/')+'.lean'
        need(row['source_sha256']==contract['inputs'][source]['sha256'],'module source identity differs')
        expected={module.replace('.','/')+suffix:objects[module.replace('.','/')+suffix] for suffix in suffixes}
        need(row['outputs']==expected,'module output map differs from final inventory')
        a=row['compiler_command'];b=row['checker_command']
        need(type(a) is int and type(b) is int and 0<=a<b<len(commands) and a+1==b,'invalid or nonadjacent command indexes')
        need(row['checker_passed'] is True,'module has no successful checker')
        need(commands[row['compiler_command']]['name']=='compile-'+row['module'] and commands[row['checker_command']]['name']=='check-'+row['module'],'module command indexes differ')
    need(result['raw_audits']=={'conditional_endpoints':True,'ordinary_bridges':True},'raw audit completion differs')
    return result

def collect(work,contract,contract_sha=None):
    if contract_sha is None:contract_sha=hashlib.sha256((json.dumps(contract,sort_keys=True,indent=2)+'\n').encode()).hexdigest()
    evidence=work/'evidence';evidence.mkdir(parents=True,exist_ok=True)
    result=evidence/'result.json'
    if not result.exists():result.write_text(json.dumps({'status':'INCOMPLETE_BEFORE_RECEIPT','conditional_C_remains_explicit':True,'final_C_proof_certified':False,'unconditional_monotile_proof_certified':False}))
    # An outer interruption may have prevented the runner's finally block.
    logs=evidence/'logs';logs.mkdir(exist_ok=True);log_total=0;interrupted_log_omissions=[]
    for p in sorted((work/'logs').glob('*')):
        size=regular(p)
        if log_total+size>contract['aggregate_log_max_bytes']+2*contract['per_command_log_max_bytes']:
            interrupted_log_omissions.append({'path':'logs/'+p.name,'bytes':size,'reason':'interrupted log collection bound'});continue
        log_total+=size
        q=logs/p.name
        if not q.exists():shutil.copyfile(p,q)
    issue=None;verified=False
    try:verify_complete(evidence,contract,contract_sha);verified=True
    except Exception as e:issue=str(e)
    upload=work/'upload';upload.mkdir(exist_ok=False);total=0;rows=[];omitted=[]
    for p in sorted(evidence.rglob('*'),key=lambda p:(p.name!='result.json',p.as_posix())):
        need(not p.is_symlink(),'evidence symlink forbidden')
        if p.is_dir():continue
        need(len(rows)+len(omitted)<20000,'evidence entry count bound')
        size=regular(p);rel=p.relative_to(evidence)
        if total+size>MAXIMUM-RESERVE:omitted.append({'path':str(rel),'bytes':size});continue
        q=upload/rel;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q);total+=size
        rows.append({'path':str(rel),'bytes':size,'sha256':sha(q)})
    receipt={'schema':'bounded-conditional-evidence-v1','conditional_C_remains_explicit':True,'unconditional_monotile_proof_certified':False,'bytes_copied':total,'files':rows,'omitted':omitted,'interrupted_log_omissions':interrupted_log_omissions,'all_available_files_copied':not omitted and not interrupted_log_omissions,'replay_acceptance_evidence_complete':verified and not omitted and not interrupted_log_omissions,'acceptance_blocker':issue,'runner_status':load(result).get('status')}
    data=(json.dumps(receipt,sort_keys=True,indent=2)+'\n').encode();need(len(data)<=RESERVE and total+len(data)<=MAXIMUM,'collection manifest exceeds reserved envelope')
    (upload/'collection.json').write_bytes(data)
    return receipt

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--work',type=Path,required=True);a=p.parse_args()
    root=Path(__file__).resolve().parents[1];receipt=collect(a.work,load(root/'contract.json'),sha(root/'contract.json'))
    if not receipt['all_available_files_copied']:raise SystemExit('Evidence cap exceeded; incomplete available-file collection.')
    if receipt['runner_status']==SUCCESS and not receipt['replay_acceptance_evidence_complete']:raise SystemExit('Claimed replay success has incomplete or inconsistent acceptance evidence.')
    # The replay command supplies the failure status; an interrupted collector may
    # still upload diagnostic evidence without inventing a successful replay.
    print(json.dumps({k:v for k,v in receipt.items() if k not in ['files','omitted']},sort_keys=True))
if __name__=='__main__':main()
