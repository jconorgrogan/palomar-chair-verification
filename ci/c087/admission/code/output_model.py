"""Pure expected-output derivation for the unchanged frozen native admission.

No admission authority, filesystem access, imports of research code or execution.
The parent must supply authenticated input bytes and independently observed OS
fields after clean child exit. This is preparation code pending protocol review.
"""
from __future__ import annotations
import copy
import hashlib
import json
from pathlib import PurePosixPath

SUFFIXES = ('.olean','.olean.private','.olean.server','.ilean','.ir','.ir.sig')
SCAFFOLD = {'objects','scratch','scratch/home','scratch/tmp','logs','module-quarantine'}
OLD_RUNNER = 'a8cbd69f9904b6f2645177de722f3466cb762045a7cd8c3e6230f1ceaa9c9c1d'
MARKER = 'historical-transfer-state.json'
CERTIFICATE = 'historical-transfer-certificate.json'

class Rejected(ValueError): pass

def need(ok,message):
    if not ok:raise Rejected(message)

def native_json(value):
    return (json.dumps(value,sort_keys=True,indent=2,allow_nan=False)+'\n').encode()

def parse(raw):
    need(type(raw) is bytes,'raw JSON bytes required')
    def pairs(items):
        result={}
        for key,value in items:
            need(key not in result,'duplicate JSON key');result[key]=value
        return result
    return json.loads(raw,object_pairs_hook=pairs,parse_constant=lambda _: (_ for _ in ()).throw(Rejected('nonfinite JSON')))

def pin(raw):
    need(type(raw) is bytes,'raw bytes required')
    return {'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()}

def relative(value):
    need(type(value) is str and value and not value.startswith('/') and '\\' not in value and '\x00' not in value,
         'relative path required')
    need(all(x not in ('','.','..') for x in value.split('/')),'clean path required')
    return value

def object_paths(module):return ['objects/'+module.replace('.','/')+suffix for suffix in SUFFIXES]

def log_paths(module):return ['logs/'+module.replace('.','/')+'.'+phase+'.'+stream
    for phase in ('compile','check') for stream in ('stdout','stderr')]

def parents(paths):
    return {str(p) for name in paths for p in PurePosixPath(name).parents if str(p)!='.'}

def expected_paths(plan, origin_by_stage, target='build_087'):
    """Exact retained path sets, including empty historical-object directories."""
    stages={s['stage_id']:s for s in plan['stages']};ids=stages[target]['required_predecessors']
    need(ids and len(ids)==len(set(ids)),'ordered predecessors required')
    files=set();dirs={'admitted',*{'admitted/'+d for d in SCAFFOLD}}
    historical=[];historical_objects=[]
    for sid in ids:
        origin=origin_by_stage[sid]
        need(origin in ('OldOrigin','PriorSuccessorOrigin','CurrentOrigin'),'native origin required')
        objects=[n for m in stages[sid]['modules'] for n in object_paths(m)]
        files.update('admitted/'+n for n in objects)
        names=['receipt.json','admission.json'] if origin=='OldOrigin' else [
            'receipt.json','restore-state.json',*[n for m in stages[sid]['modules'] for n in log_paths(m)]]
        files.update('admitted/restore-evidence/'+sid+'/'+n for n in names)
        if origin!='CurrentOrigin':
            historical.append(sid);historical_objects.extend(objects)
            files.update('admitted-historical-validation/validation/restore-evidence/'+sid+'/'+n for n in names)
        else:dirs.add('admitted/quarantine')
    if historical:
        files.update('admitted/'+n for n in (MARKER,CERTIFICATE))
        dirs.update({'admitted-historical-validation','admitted-historical-validation/empty-runtime',
            'admitted-historical-validation/validation',
            *{'admitted-historical-validation/validation/'+d for d in SCAFFOLD}})
        if any(origin_by_stage[sid]=='PriorSuccessorOrigin' for sid in historical):
            dirs.add('admitted-historical-validation/validation/quarantine')
        dirs.update('admitted-historical-validation/validation/'+d for d in parents(historical_objects))
    dirs.update(parents(files))
    return {'files':sorted(files),'directories':sorted(dirs)}

def expected_evidence(*, wrapper, raw_receipt, receipt, prior_identity, prior_contract):
    """Native receipt/log pins plus exact original-admission or readonly journal."""
    need(pin(raw_receipt)['sha256']==wrapper['native_descriptor']['receipt_sha256'],'receipt hash')
    descriptor=copy.deepcopy(wrapper['native_descriptor'])
    result={'receipt.json':pin(raw_receipt)};generated={}
    if wrapper['origin']=='OldOrigin':
        obj={'schema':'old-modern-original-validator-admission-v1',
            'status':'original_receipt_validated_objects_moved_only','proof_pass_claimed':False,
            'original_native_descriptor':descriptor,'raw_descriptor_sha256':wrapper['raw_descriptor_sha256'],
            'original_receipt_sha256':pin(raw_receipt)['sha256'],'source_delta_sha256':prior_contract.get('source_delta_sha256'),
            'successor_identity':prior_identity,'old_validator_sha256':OLD_RUNNER,
            'new_validator_sha256':prior_contract.get('runner_sha256'),
            'objects':{name:digest for rec in receipt['modules'] for name,digest in rec['outputs'].items()},
            'claim':'Cross-run checked-object admission; original receipt is unchanged; not a fresh source replay.'}
        generated['admission.json']=native_json(obj)
    else:
        moved=[name for rec in receipt['modules'] for name in object_paths(rec['module'])]
        obj={'status':'restored_verified','descriptor':descriptor,
            'objects':{name:receipt['files'][name]['sha256'] for name in moved},
            'moved':moved,'proof_pass_claimed':False}
        generated['restore-state.json']=native_json(obj)
        for rec in receipt['modules']:
            for name in log_paths(rec['module']):result[relative(name)]=copy.deepcopy(receipt['files'][name])
    result.update({name:pin(raw) for name,raw in generated.items()})
    return result,generated

def static_outputs(*,plan,origin_by_stage,wrappers,native_bytes,prior_identity,prior_contract):
    """All non-transfer native output pins, without reading any output files."""
    paths=expected_paths(plan,origin_by_stage);files={};generated={};historical_objects={};historical_evidence={}
    ids=next(s['required_predecessors'] for s in plan['stages'] if s['stage_id']=='build_087')
    need([w['native_descriptor']['stage_id'] for w in wrappers]==ids,'ordered wrapper scope')
    for wrapper in wrappers:
        sid=wrapper['native_descriptor']['stage_id'];raw=native_bytes[sid]['receipt'];receipt=parse(raw)
        need(wrapper['origin']==origin_by_stage[sid],'outer native origin mismatch')
        evidence,generated_stage=expected_evidence(wrapper=wrapper,raw_receipt=raw,receipt=receipt,
            prior_identity=prior_identity,prior_contract=prior_contract)
        for rec in receipt['modules']:
            for name in object_paths(rec['module']):
                files['admitted/'+name]=copy.deepcopy(receipt['files'][name])
                if wrapper['origin']!='CurrentOrigin':historical_objects[name.removeprefix('objects/')]=copy.deepcopy(receipt['files'][name])
        for name,value in evidence.items():
            files['admitted/restore-evidence/'+sid+'/'+name]=value
            if wrapper['origin']!='CurrentOrigin':
                historical_evidence[sid+'/'+name]=value
                files['admitted-historical-validation/validation/restore-evidence/'+sid+'/'+name]=copy.deepcopy(value)
        for name,raw in generated_stage.items():
            generated['admitted/restore-evidence/'+sid+'/'+name]=raw
            if wrapper['origin']!='CurrentOrigin':generated['admitted-historical-validation/validation/restore-evidence/'+sid+'/'+name]=raw
    missing={'admitted/'+MARKER,'admitted/'+CERTIFICATE}
    need(set(files)==set(paths['files'])-missing,'complete fixed native path map')
    return {'files':files,'directories':paths['directories'],'historical_objects':historical_objects,
        'historical_evidence':historical_evidence,'generated':generated,'os_dependent_file':'admitted/'+CERTIFICATE}

def transfer_outputs(*,request,static,source_root,admission_root,historical_root,workspace,
                     historical_workspace,workspace_inode,historical_workspace_inode,allocation_unit):
    """Exact final two files; ONLY observed inodes/allocation unit are post-exit inputs."""
    for inode in (workspace_inode,historical_workspace_inode):
        need(type(inode) in (tuple,list) and len(inode)==2 and all(type(x) is int and x>=0 for x in inode),'exact observed inode')
    need(type(allocation_unit) is int and allocation_unit>0,'observed allocation unit')
    scope=request['scope'];native=request['native'];target=scope['target_stage']
    need(target=='build_087' and scope.get('final_role') is None,'C087 only')
    required=next(s['required_predecessors'] for s in native['plan']['stages'] if s['stage_id']==target)
    historical=[sid for sid in required if scope['origin_by_stage'][sid]!='CurrentOrigin']
    current=[sid for sid in required if scope['origin_by_stage'][sid]=='CurrentOrigin']
    request_sha=pin(native_json(request))['sha256']
    marker={'schema':'historical-transfer-attempt-v2','status':'incomplete_until_live_capability_return',
        'request_sha256':request_sha,'target_stage':target,'final_role':None,'activation_allowed':False}
    cert={'schema':'checked-historical-transfer-v2','request_sha256':request_sha,'target_stage':target,'final_role':None,
        'historical_stage_ids':historical,'remaining_current_stage_ids':current,'required_providers':required,
        'source_workspace':historical_workspace,'destination_workspace':workspace,
        'source_workspace_inode':list(historical_workspace_inode),'destination_workspace_inode':list(workspace_inode),
        'native_source_root':source_root,'current_source_root':source_root,'admission_implementation_root':admission_root,
        'historical_implementation_root':historical_root,'native_descriptors':scope['expected_native_descriptors'],
        'objects':static['historical_objects'],'preserved_native_evidence':static['historical_evidence'],
        'native_source_manifest_sha256':pin(native_json(native['manifest']))['sha256'],'current_identity':scope['current_identity'],
        'complete_target_closure':False,'activation_allowed':False,'proof_pass_claimed':False,
        'claim':'Historical subset only; unchanged native validators admitted payloads; raw receipts preserved.'}
    bound=len(native_json(cert))+2048;marker_raw=native_json(marker);unit=max(4096,allocation_unit)
    round_up=lambda size:((size+unit-1)//unit)*unit
    paths=['restore-evidence/'+n for n in static['historical_evidence']]+['objects/'+n for n in static['historical_objects']]
    directories=parents(paths)-SCAFFOLD;sizes=[p['bytes'] for p in static['historical_evidence'].values()]
    new_files=len(sizes)+2
    payload=sum(round_up(n) for n in sizes)+round_up(bound)+round_up(len(marker_raw))
    overhead=unit*(new_files+len(directories)+len(static['historical_objects'])+4)
    cert['additional_transfer_copy_budget']={'allocation_unit':unit,'required_additional_free_bytes':payload+overhead,
        'required_free_inodes':new_files+len(directories),'evidence_copy_bytes':sum(sizes),'certificate_bytes_bound':bound,
        'marker_bytes':len(marker_raw),'new_directories':len(directories),'new_regular_files':new_files,
        'object_payload_copy_bytes':0,'deletion_credit_bytes':0}
    certificate_raw=native_json(cert);need(len(certificate_raw)<=bound,'native certificate bound')
    return {'admitted/'+MARKER:marker_raw,'admitted/'+CERTIFICATE:certificate_raw}

def transfer_marker(request):
    return native_json({'schema':'historical-transfer-attempt-v2','status':'incomplete_until_live_capability_return',
        'request_sha256':pin(native_json(request))['sha256'],'target_stage':'build_087','final_role':None,'activation_allowed':False})

def allocation_budget(*,static,native_bytes,origin_by_stage,marker_bytes,derived_certificate_bytes_bound,
                      allocation_unit,protocol_caps):
    """Conservative additional native peak; retained inputs are already allocated.

    Final output is reserved in full. Additional transient allocation is the max
    of the full historical extracted closure (including discarded old logs) and
    the largest latest-stage quarantine extraction. Those phases do not overlap.
    Each directory gets a base block AND an entry allowance; the enclosing root
    and temporary scaffold are explicit. This is separate from the raw-tar cap.
    """
    need(type(allocation_unit) is int and allocation_unit>0,'measured allocation unit')
    need(type(derived_certificate_bytes_bound) is int and derived_certificate_bytes_bound>0,'derived certificate reserve')
    need(type(marker_bytes) is bytes,'exact marker bytes')
    required_protocol={'request.json','admission-invocation.json','native-report.json','response.json','combined_stdout_stderr'}
    need(type(protocol_caps) is dict and set(protocol_caps)==required_protocol,'separate exact protocol caps')
    need(all(type(x) is int and x>=0 for x in protocol_caps.values()),'nonnegative protocol byte caps')
    unit=max(4096,allocation_unit);round_up=lambda n:((n+unit-1)//unit)*unit
    final_sizes=[v['bytes'] for v in static['files'].values()]+[len(marker_bytes),derived_certificate_bytes_bound]
    need(all(type(n) is int and n>=0 for n in final_sizes),'fixed output byte sizes')
    final_files=len(final_sizes);final_dirs=len(static['directories']);enclosing_dirs=1
    final_payload=sum(round_up(n) for n in final_sizes)
    historical_sizes=[];historical_paths=[];latest=[]
    def phase(name,sizes,directories):
        payload=sum(round_up(n) for n in sizes);files=len(sizes)
        base=unit*directories;entries=unit*(files+directories)
        return {'name':name,'files':files,'directories':directories,'logical_bytes':sum(sizes),
            'allocated_payload_bytes':payload,'directory_base_bytes':base,'entry_allowance_bytes':entries,
            'allocated_total_bytes':payload+base+entries,'inodes':files+directories}
    for sid,pair in native_bytes.items():
        receipt=parse(pair['receipt']);sizes=[len(pair['receipt'])];paths=[sid+'/receipt.json']
        for name,value in receipt['files'].items():
            relative(name);need(type(value['bytes']) is int and value['bytes']>=0,'native payload size')
            sizes.append(value['bytes']);paths.append(sid+'/'+name)
        if origin_by_stage[sid]=='CurrentOrigin':
            # Eight scaffold directories additionally cover quarantine/stage
            # ancestors and journal directories; object/log parents are exact.
            latest.append(phase(sid,sizes,len(parents(paths))+8))
        else:historical_sizes.extend(sizes);historical_paths.extend(paths)
    # Historical stage extraction plus old deps object parents and sixteen
    # additional temporary ancestors/scaffold directories conservatively bound
    # the original validator's quarantine+deps copy before source object rename.
    historical_dirs=len(parents(historical_paths))+len(parents(['deps/'+n for n in static['historical_objects']]))+16
    historical=phase('historical_extra_closure',historical_sizes,historical_dirs)
    largest_latest=max(latest,key=lambda value:value['allocated_total_bytes'],default=phase('none',[],0))
    transient=max((historical,largest_latest),key=lambda value:value['allocated_total_bytes'])
    transient_inodes=max([historical['inodes'],*[value['inodes'] for value in latest]])
    # Combined stdout/stderr occupy at most two files; an extra unit covers the
    # unknown split without expanding their registered combined logical cap.
    protocol_payload=sum(round_up(x) for x in protocol_caps.values())+unit;protocol_files=6
    directory_base=unit*(final_dirs+enclosing_dirs)+transient['directory_base_bytes']
    entry_allowance=unit*(final_files+final_dirs+enclosing_dirs+protocol_files)+transient['entry_allowance_bytes']
    fixed_metadata_reserve=16*unit
    metadata_overhead=directory_base+entry_allowance+fixed_metadata_reserve
    return {'schema':'c087-native-admission-allocation-budget-v2','allocation_unit':unit,
        'retained_native_files':final_files,'retained_native_directories':final_dirs,'enclosing_root_directories':enclosing_dirs,
        'retained_native_logical_bytes_bound':sum(final_sizes),'retained_native_allocated_payload_bytes_bound':final_payload,
        'derived_certificate_bytes_bound':derived_certificate_bytes_bound,'protocol_logical_caps':copy.deepcopy(protocol_caps),
        'protocol_logical_bytes_bound':sum(protocol_caps.values()),'protocol_allocated_payload_bytes_bound':protocol_payload,
        'extra_historical_payload_files':historical['files'],'extra_historical_payload_directories_bound':historical_dirs,
        'extra_historical_scaffold_directories_bound':16,'extra_historical_payload_logical_bytes':historical['logical_bytes'],
        'extra_historical_payload_allocated_bytes':historical['allocated_payload_bytes'],
        'historical_transient_phase':historical,'largest_latest_transient_phase':largest_latest,
        'latest_scaffold_directories_per_stage_bound':8,'transient_phase_selected':transient['name'],
        'transient_phase_allocation_bytes_bound':transient['allocated_total_bytes'],'transient_inode_bound':transient_inodes,
        'directory_base_allocation_bytes':directory_base,'directory_entry_allowance_bytes':entry_allowance,
        'fixed_metadata_reserve_bytes':fixed_metadata_reserve,'metadata_allocation_allowance_bytes':metadata_overhead,
        'required_additional_free_bytes':final_payload+protocol_payload+transient['allocated_payload_bytes']+metadata_overhead,
        'required_additional_free_inodes':final_files+final_dirs+enclosing_dirs+protocol_files+transient_inodes+16,
        'retained_raw_archives_included':False,'all_input_roots_included':False,'deletion_credit_bytes':0}
