#!/usr/bin/env python3
"""Collect bounded available evidence; only complete verified receipts admit replay."""
import argparse,hashlib,json,os,re,shutil,stat,importlib.util,sys
from pathlib import Path
MAXIMUM=128*1024**2
RESERVE=4*1024**2
SUCCESS='CACHE_BACKED_CONDITIONAL_GEOMETRY_REPLAY_COMPLETED'
STAGE_SUCCESS='CHECKED_CONDITIONAL_STAGE_COMPLETED_C_EXPLICIT'
HIGHER_SCHEMA='higher-dimension-staged-replay-v1'
HIGHER_SUCCESS='HIGHER_DIMENSIONS_THREE_AND_GE_FIVE_RAW_AUDITED'
HIGHER_STAGE_SUCCESS='CHECKED_HIGHER_DIMENSION_STAGE_COMPLETED'
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
def make_cross_origin_certificate(contract,contract_sha,identity,stage_id,interface,lineage,inventory,locked):
    """A new consumer certificate; original producer receipts remain unchanged."""
    need(contract['schema'] in ('conditional-geometry-origin-continuation-v3','conditional-geometry-final-origin-v4',HIGHER_SCHEMA),'certificate requires known origin schema')
    higher=contract['schema']==HIGHER_SCHEMA
    final=contract['schema']=='conditional-geometry-final-origin-v4' or higher
    ancestors=contract['stages'][stage_id]['admitted_stages']
    need([r['stage_id'] for r in lineage]==ancestors,'certificate imported stage coverage differs')
    rows=[];suffixes=['.olean','.olean.private','.olean.server','.ilean','.ir.sig','.ir','.c']
    for record in lineage:
        sid=record['stage_id']
        if sid not in locked:
            need(((higher and sid in contract['execution_stages']) or (not final and sid=='F3_product_geometry')) and record['origin']['identity']==identity,'unlocked or third-origin stage')
            continue
        pin=locked[sid]
        need(record['origin']==pin['origin'] and record['receipt_sha256']==pin['receipt_sha256'] and
             record['checked_module_receipts_sha256']==pin['checked_module_receipts_sha256'],'cross-origin producer differs from lock')
        modules=contract['stages'][sid]['modules'];need(record['own_modules']==modules,'certificate module set differs')
        own={m.replace('.','/')+s:inventory[m.replace('.','/')+s] for m in modules for s in suffixes}
        rows.append({'stage_id':sid,'origin':record['origin'],'producer_contract_sha256':pin['producer_contract_sha256'] if final else contract['original_stage_contract_sha256'],
          'producer_receipt_sha256':record['receipt_sha256'],'checked_module_receipts_sha256':record['checked_module_receipts_sha256'],
          'accepted_module_count':len(modules),'exact_own_output_inventory_sha256':hashlib.sha256((json.dumps(own,sort_keys=True,indent=2)+'\n').encode()).hexdigest()})
    need([r['stage_id'] for r in rows]==[sid for sid in ancestors if sid in contract['locked_origin_stages']],'cross-origin certificate coverage differs')
    return {'schema':'higher-locked-origin-admissions-v1' if higher else 'conditional-locked-origin-admissions-v2' if final else 'conditional-locked-origin-admissions-v1','consumer_identity':identity,'consumer_contract_sha256':contract_sha,
      'consumer_stage_id':stage_id,'source_archive_sha256':contract['source_archive']['sha256'],
      'runtime_inventory_sha256':contract['official_lean_inventory_sha256'],'interface_identity':interface,
      'complete_original_checker_lineage_verified':True,'fresh_in_one_run':False,'admissions':rows}


def locked_origin_rows(contract):
    root=Path(__file__).resolve().parents[1];pointer=contract['origin_lock']
    need(pointer['path']=='origin/locked-origins.json','unexpected origin lock path')
    higher=contract.get('schema')==HIGHER_SCHEMA
    final=contract.get('schema')=='conditional-geometry-final-origin-v4' or higher
    if final:
        path=root/pointer['path']
    else:
        need(contract.get('schema')=='conditional-geometry-origin-continuation-v3' and
             hashlib.sha256((json.dumps(contract,sort_keys=True,indent=2)+'\n').encode()).hexdigest()=='288b8adf64db7d9d1bd2ebefb38660debc550d1bdf65f2ab97039b331f7c9070','unrecognized native continuation producer contract')
        path=root/'origin/continuation-producer-origins.json'
    need(regular(path)==pointer['bytes'] and sha(path)==pointer['sha256'],'origin lock bytes/hash differ')
    lock=load(path)
    if final:
        need(set(lock)=={'schema','producer_contracts','stages'} and lock['schema']==('higher-exact-mixed-origin-lock-v1' if higher else 'conditional-exact-mixed-origin-lock-v2') and
             lock['producer_contracts']==['cbba2b835ef2578ad4810068cab863918af442d5fa30abea5cafcfa78ce35a38','288b8adf64db7d9d1bd2ebefb38660debc550d1bdf65f2ab97039b331f7c9070'],'mixed origin producer contracts differ')
        for sid,row in lock['stages'].items():
            expected='288b8adf64db7d9d1bd2ebefb38660debc550d1bdf65f2ab97039b331f7c9070' if sid=='F3_product_geometry' else 'cbba2b835ef2578ad4810068cab863918af442d5fa30abea5cafcfa78ce35a38'
            need(row['producer_contract_sha256']==expected,'wrong per-stage producer contract')
    else:
        need(lock['schema']=='conditional-exact-origin-lock-v1' and lock['producer_contract_sha256']==contract['original_stage_contract_sha256'],'native origin lock scope differs')
    need(set(lock['stages'])==set(contract['locked_origin_stages']),'origin lock stage coverage differs')
    return lock['stages']


def validate_module_scheduling_commands(contract,commands):
    target='SpectreGeometry.PolygonProductKeyReferenceFinite'
    for command in commands:
        argv=command.get('argv');need(isinstance(argv,list) and all(isinstance(x,str) for x in argv),'missing exact command argv for scheduling audit')
        options=[x for x in argv if x.startswith('-DElab.async')]
        expected=['-DElab.async=false'] if contract.get('schema')!=HIGHER_SCHEMA and command['name']=='compile-'+target else []
        need(options==expected,'source-local scheduling option appears on wrong command or differs')


def verify_complete(evidence,contract,contract_sha,*,require_export=True):
    result=load(evidence/'result.json')
    need(result['contract_sha256']==contract_sha,'result contract identity differs')
    expected_status=STAGE_SUCCESS if 'stages' in contract and result.get('stage_id')!=contract['final_stage'] else SUCCESS
    if contract.get('schema')==HIGHER_SCHEMA:expected_status=HIGHER_SUCCESS if result.get('stage_id')==contract['final_stage'] else HIGHER_STAGE_SUCCESS
    need(result['status']==expected_status and result.get('complete_evidence') is True,'runner did not reach complete stage/replay success')
    higher=contract.get('schema')==HIGHER_SCHEMA
    scope_ok=(result.get('proof_scope')=='higher-dimension-sources-and-c-free-endpoints' and 'conditional_C_remains_explicit' not in result) if higher else result.get('conditional_C_remains_explicit') is True
    need(scope_ok and result.get('final_C_proof_certified') is False and result.get('unconditional_monotile_proof_certified') is False,'proof scope changed')
    extraction=load(evidence/'source-extraction.json')
    need(sha(evidence/'source-extraction.json')==result['source_extraction_receipt_sha256'],'source extraction receipt hash differs')
    need(result['source_archive_sha256']==contract['source_archive']['sha256'],'source archive receipt identity differs')
    expected_extraction={'schema':'authenticated-source-extraction-v1','archive':contract['source_archive'],'source_file_count':contract['owned_module_count'],'source_bytes':contract['source_archive']['source_bytes'],'exact_source_tree':True,'all_source_pins_verified':True}
    need(extraction==expected_extraction,'source extraction receipt differs')
    staged='stages' in contract
    if staged:
        sid=result['stage_id'];need(sid in contract['stages'],'unknown result stage')
        stage=contract['stages'][sid];own_names=stage['modules']
        if require_export:
            exported=load(evidence/'stage-export.json')
            need(exported['stage_id']==sid and exported['contract_sha256']==contract_sha,'object export identity differs')
            upload=evidence.parent/'object-upload'
            need(regular(upload/'stage.tar')==exported['stage_tar_bytes']<=contract['object_artifact_max_bytes'] and sha(upload/'stage.tar')==exported['stage_tar_sha256'],'exported object archive absent or changed')
            need(sha(upload/'descriptor.json')==exported['descriptor_sha256'],'exported descriptor absent or changed')
        expected_names=[m for dep in [*stage['admitted_stages'],sid] for m in contract['stages'][dep]['modules']]
        need(result['stage_modules']==own_names and result['admitted_stages']==stage['admitted_stages'],'stage schedule receipt differs')
        need(result['checked_fresh_module_count']==len(own_names),'fresh stage count differs')
        for filename,key in [('interface-identity.json','interface_identity_sha256'),('imported-stages.json','imported_stages_sha256')]:
            need(sha(evidence/filename)==result[key],'stage identity receipt hash differs')
        imported=load(evidence/'imported-stages.json')
        need([x['stage_id'] for x in imported]==stage['admitted_stages'],'imported stage coverage differs')
        for row in imported:
            need(row['own_modules']==contract['stages'][row['stage_id']]['modules'],'imported module coverage differs')
            origin=row['origin']
            if contract.get('schema') in ('conditional-geometry-origin-continuation-v3','conditional-geometry-final-origin-v4',HIGHER_SCHEMA) and row['stage_id'] in contract['locked_origin_stages']:
                pin=locked_origin_rows(contract)[row['stage_id']]
                need(origin==pin['origin'] and row['receipt_sha256']==pin['receipt_sha256'] and row['checked_module_receipts_sha256']==pin['checked_module_receipts_sha256'],'locked cross-origin lineage differs')
            else:
                need(origin['identity']['workflow_commit']==result['workflow_commit'] and str(origin['identity']['run_id'])==str(result['run_id']) and str(origin['identity']['run_attempt'])==str(result['run_attempt']),'cross-run or cross-attempt origin')
            for key in ['receipt_sha256','checked_module_receipts_sha256']:need(re.fullmatch(r'[0-9a-f]{64}',row[key]) is not None,'invalid imported evidence identity')
    else:
        own_names=[r['module'] for r in contract['modules']];expected_names=own_names
    commands=lines(evidence/'commands.jsonl');modules=lines(evidence/'owned-modules.jsonl')
    if contract.get('schema') in ('conditional-geometry-origin-continuation-v3','conditional-geometry-final-origin-v4',HIGHER_SCHEMA):validate_module_scheduling_commands(contract,commands)
    need(len(commands)==result['command_count'] and len(modules)==len(own_names) and result['checked_owned_module_count']==len(expected_names),'receipt counts differ')
    need([r['module'] for r in modules]==own_names,'module receipt coverage differs')
    for name,key in [('commands.jsonl','command_receipts_sha256'),('owned-modules.jsonl','owned_module_receipts_sha256'),('fresh-owned-objects.json','owned_output_inventory_sha256'),('cached-build-inventory.json','cached_build_inventory_sha256'),('runtime-inventory.json','runtime_inventory_sha256')]:
        need(sha(evidence/name)==result[key],'terminal receipt hash differs: '+name)
    objects=load(evidence/'fresh-owned-objects.json')['files']
    suffixes=['.olean','.olean.private','.olean.server','.ilean','.ir.sig','.ir','.c']
    expected_outputs={name.replace('.','/')+suffix for name in expected_names for suffix in suffixes}
    need(set(objects)==expected_outputs,'owned object inventory coverage differs')
    if contract.get('schema') in ('conditional-geometry-origin-continuation-v3','conditional-geometry-final-origin-v4',HIGHER_SCHEMA):
        need(sid in contract['execution_stages'] and result.get('owned_objects_from_prior_runs') is True,'continuation execution/freshness scope differs')
        identity={'repository':'jconorgrogan/palomar-chair-verification','workflow_commit':result['workflow_commit'],'run_id':str(result['run_id']),'run_attempt':str(result['run_attempt'])}
        cert=make_cross_origin_certificate(contract,contract_sha,identity,sid,load(evidence/'interface-identity.json'),imported,objects,locked_origin_rows(contract))
        need(sha(evidence/'cross-origin-admissions.json')==result['cross_origin_admissions_sha256'] and load(evidence/'cross-origin-admissions.json')==cert,'cross-origin admission certificate differs')
    else:
        need('cross_origin_admissions_sha256' not in result,'legacy producer claims a continuation certificate')
    names=[];log_bytes=0
    for command in commands:
        name=command['name'];need(isinstance(name,str) and re.fullmatch(r'[A-Za-z0-9_.-]+',name) and '..' not in name,'unsafe command log name')
        need(name not in names,'duplicate command name');names.append(name)
        need(command['exit_code']==0 and not any(command[k] for k in ['timed_out','log_overflow','memory_exceeded','surviving_children']) and command['process_group_empty'] and command['descendants_empty'] and not (command['escaped_descendants'] and not command['new_sessions_explicitly_allowed']),'unsuccessful command in success evidence')
        for stream in ['stdout','stderr']:
            p=evidence/'logs'/(name+'.'+stream);log_bytes+=regular(p);need(sha(p)==command[stream+'_sha256'],'missing, partial, or changed command log')
    need(log_bytes==result['complete_log_bytes'] and log_bytes<=contract['aggregate_log_max_bytes'],'complete log byte count differs')
    pairs=[name for name in names if name.startswith(('compile-','check-')) and not name.startswith(('compile-auditor-','check-auditor-'))]
    expected_pairs=[phase+'-'+module for module in own_names for phase in ['compile','check']]
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
    final=not staged or sid==contract['final_stage']
    if contract.get('schema')==HIGHER_SCHEMA:
        need(result.get('higher_endpoints_have_no_C_premise') is True and result.get('all_dimension_uniform_proof_certified') is False,'higher claim scope differs')
        need(sha(evidence/'cache-extension-admission.json')==result.get('cache_extension_receipt_sha256'),'higher cache certificate missing or changed')
        extension=load(evidence/'cache-extension-admission.json')
        need(extension.get('schema')=='verified-official-cache-extension-v1' and extension.get('full_interface')==load(evidence/'interface-identity.json') and extension.get('base_module_count')==2786 and extension.get('extension_module_count')==19 and extension.get('full_module_count')==2805 and extension.get('all_old_companions_identical') is True and extension.get('native_library_rows')=={},'higher cache certificate scope differs')
        need(result['raw_audits']==({'higher_physical_endpoints':True} if final else {}),'higher raw audit completion differs')
        if final:need(len(expected_names)==len(set(expected_names))==1433,'higher final union differs')
        root=Path(__file__).resolve().parents[1]
        for name in ['cache_diagnostic.py','higher_policy.py','conditional_transport.py','fresh_stage.py','toolchain_install.py','source_header.py']:
            pin=contract['inputs']['ci/'+name];path=root/'ci'/name
            need(regular(path)==pin['bytes'] and sha(path)==pin['sha256'],'collector verifier helper pin differs')
        spec=importlib.util.spec_from_file_location('higher_collection_verifier',root/'ci/cache_diagnostic.py')
        api=importlib.util.module_from_spec(spec);sys.modules[spec.name]=api;spec.loader.exec_module(api)
        api.higher.validate_current_evidence(contract,evidence,result,commands,api)
    else:
        need(result['raw_audits']==({'conditional_endpoints':True,'ordinary_bridges':True} if final else {}),'raw audit completion differs')
        if staged and final:need(len(expected_names)==len(set(expected_names))==2481,'final exact union coverage differs')
    return result

def collect(work,contract,contract_sha=None):
    if contract_sha is None:contract_sha=hashlib.sha256((json.dumps(contract,sort_keys=True,indent=2)+'\n').encode()).hexdigest()
    evidence=work/'evidence';evidence.mkdir(parents=True,exist_ok=True)
    result=evidence/'result.json'
    if not result.exists():
        empty={'status':'INCOMPLETE_BEFORE_RECEIPT','final_C_proof_certified':False,'unconditional_monotile_proof_certified':False}
        empty.update({'proof_scope':'higher-dimension-sources-and-c-free-endpoints'} if contract.get('schema')==HIGHER_SCHEMA else {'conditional_C_remains_explicit':True})
        result.write_text(json.dumps(empty))
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
    if contract.get('schema')==HIGHER_SCHEMA:
        receipt.pop('conditional_C_remains_explicit');receipt.update(schema='bounded-higher-dimension-evidence-v1',proof_scope='higher-dimension-sources-and-c-free-endpoints')
    data=(json.dumps(receipt,sort_keys=True,indent=2)+'\n').encode();need(len(data)<=RESERVE and total+len(data)<=MAXIMUM,'collection manifest exceeds reserved envelope')
    (upload/'collection.json').write_bytes(data)
    return receipt

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--work',type=Path,required=True);a=p.parse_args()
    root=Path(__file__).resolve().parents[1];receipt=collect(a.work,load(root/'contract.json'),sha(root/'contract.json'))
    if not receipt['all_available_files_copied']:raise SystemExit('Evidence cap exceeded; incomplete available-file collection.')
    if receipt['runner_status'] in (SUCCESS,STAGE_SUCCESS,HIGHER_SUCCESS,HIGHER_STAGE_SUCCESS) and not receipt['replay_acceptance_evidence_complete']:raise SystemExit('Claimed replay success has incomplete or inconsistent acceptance evidence.')
    # The replay command supplies the failure status; an interrupted collector may
    # still upload diagnostic evidence without inventing a successful replay.
    print(json.dumps({k:v for k,v in receipt.items() if k not in ['files','omitted']},sort_keys=True))
if __name__=='__main__':main()
