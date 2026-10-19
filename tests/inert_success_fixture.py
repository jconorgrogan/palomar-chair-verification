"""Synthetic scalar/file fixture only; never a Lean/native proof run.
Caller supplies imported driver d and work path. Only seam is temporarily setting
 d.a.RUNTIME_INVENTORY_SHA to returned synthetic_runtime_sha while verifying;
 restore it afterward. No production bypass or runtime tool is invoked.
"""
import json

def make(d,c,work):
    for folder in ['evidence/logs','logs','native-captures']:(work/folder).mkdir(parents=True)
    evidence=work/'evidence';contract_sha=d.f.sha(d.f.json_bytes(c))
    def write(name,value):d.a.write_json(evidence/name,value)
    def pin(data):return {'bytes':len(data),'sha256':d.f.sha(data)}
    runtime={'files':{'lib/lean/'+m.replace('.','/')+'.olean':pin(('synthetic '+m).encode()) for m in c['runtime_roots']},'symlinks':{}}
    write('runtime-inventory.json',runtime)
    write('source-extraction.json',{'schema':'authenticated-source-extraction-v1','archive':c['source_archive'],'source_file_count':174,'source_bytes':c['source_archive']['source_bytes'],'exact_source_tree':True,'all_source_pins_verified':True})
    allowed={r['module']:r for r in d.f.load_json(d.VENDOR/'locks/required-modules.json')['modules']}
    selected=[allowed[m] for m in c['cache_roots']]
    write('selected-cache-closure.json',{'roots':c['cache_roots'],'modules':selected,'maximum_locked_modules':2805,'derived_from_authenticated_official_source_headers':True})
    inventories={p['name']:{'files':{},'bytes':0} for p in d.f.load_json(d.VENDOR/'locks/dependencies.json')['packages']};cache_rows={}
    for row in selected:
        m=row['module'];prefix='lib/lean/'+m.replace('.','/');suffixes=['.olean','.ilean']+(['.olean.server','.olean.private','.ir.sig','.ir'] if row['modern_module'] else [])
        companions={prefix+s:pin(('synthetic '+m+s).encode()) for s in suffixes}
        inventories[row['package']]['files'].update(companions);cache_rows[m]={**row,'companions':companions}
    write('cached-build-inventory.json',inventories);write('selected-cache-admission.json',cache_rows)
    write('read-only-boundary-preflight.json',{'status':'READ_ONLY_PREDECESSOR_WRITES_CHMOD_AND_NAMESPACE_CREATION_REJECTED','quarantine_write_allowed':True,'fixture_sha256':d.f.sha(b'IMMUTABLE_BOUNDARY_FIXTURE_ONLY\n'),'not_a_research_proof':True})
    deps={p['name']:{'revision':p['rev'],'repository':p['url'],'files':{}} for p in d.f.load_json(d.VENDOR/'locks/dependencies.json')['packages']}
    for row in selected:deps[row['package']]['files'][row['path']]={'sha256':row['sha256']}
    write('dependency-sources.json',deps);write('cache-client-binary.json',{'sha256':d.f.sha(b'synthetic client'),'bytes':16,'built_from_official_sources':True})
    objects={n:pin(('synthetic '+n).encode()) for m in c['module_order'] for n in sorted(d.a.module_outputs(m))}
    write('fresh-owned-objects.json',{'files':objects,'bytes':sum(x['bytes'] for x in objects.values())})
    commands=[];index={};log_bytes=0
    for name in d.command_order(c):
        spec=d.command_spec(c,work,name,c['cache_roots']);row={k:v for k,v in spec.items() if k!='allowed_sessions'}
        row.update(exit_code=1 if name.startswith('compile-original-') else 0,timed_out=False,log_overflow=False,memory_exceeded=False,surviving_children=False,process_group_empty=True,descendants_empty=True,escaped_descendants=False,new_sessions_explicitly_allowed=spec['allowed_sessions'],effective_timeout_seconds=spec['requested_timeout_seconds'],limits={k:d.LIMITS[k] for k in ['address_space_bytes','rss_tree_bytes','max_created_file_bytes']},max_log_bytes=1024**2,capture_status='accepted_bounded_complete')
        out=b''
        if name.startswith('compile-original-'):
            m=name[len('compile-original-'):]
            out=''.join(str(work/'original-input')+'/'+m.replace('.','/')+f'.lean:{line}:{col or 3}: error: Unknown identifier `{helper}`\n' for line,col,helper in d.EXPECTED_UNKNOWN[m]).encode()
        row['captures']={}
        for stream,data in [('stdout',out),('stderr',b'')]:
            row[stream+'_sha256']=d.f.sha(data);row['captures'][stream]=pin(data);(work/'logs'/(name+'.'+stream)).write_bytes(data);(evidence/'logs'/(name+'.'+stream)).write_bytes(data);log_bytes+=len(data)
        index[name]=len(commands);commands.append(row)
    (evidence/'commands.jsonl').write_text(''.join(json.dumps(r,sort_keys=True,separators=(',',':'))+'\n' for r in commands))
    owned={r['module']:r for r in c['modules']}
    def imports(module):
        result=[]
        for dep in dict.fromkeys([*owned[module]['ordered_imports'],'Init']):
            if dep in owned:result.append({'module':dep,'provider':'fresh_owned','companions':{p:objects[p] for p in sorted(d.a.module_outputs(dep))}})
            elif dep in cache_rows:result.append({'module':dep,'provider':'explicitly_trusted_official_cache','source_sha256':cache_rows[dep]['sha256'],'companions':cache_rows[dep]['companions']})
            else:result.append({'module':dep,'provider':'official_runtime','object_sha256':runtime['files']['lib/lean/'+dep.replace('.','/')+'.olean']['sha256']})
        return result
    modules=[];probes=[]
    for m in c['module_order']:
        modules.append({'module':m,'source_sha256':owned[m]['sha256'],'ordered_imports':imports(m),'outputs':{n:objects[n] for n in sorted(d.a.module_outputs(m))},'compiler_command':index['compile-'+m],'checker_command':index['check-'+m],'checker_passed':True})
        if m in d.TARGETS:
            name='compile-original-'+m;needed=set(c['target_closures'][m])-{m};text=(evidence/'logs'/(name+'.stdout')).read_text()
            prefix=c['module_order'][:c['module_order'].index(m)];prefix_map={n:objects[n] for x in prefix for n in d.a.module_outputs(x)}
            inventory={'files':prefix_map,'bytes':sum(r['bytes'] for r in prefix_map.values())}
            probes.append({'corrected_object_inventory_sha256':d.f.sha(d.f.json_bytes(inventory)),'physical_grid_uses_corrected_deformation':m==d.TARGETS[3],'module':m,'source_sha256':c['originals'][m]['sha256'],'command':index[name],'corrected_prerequisite_imports':imports(m),'exact_prerequisite_modules':sorted(needed),'exact_prerequisite_objects':{n:objects[n] for x in needed for n in d.a.module_outputs(x)},'corrected_object_inventory_unchanged':True,'original_objects_admitted':False,'status':'PREDICTED_VISIBILITY_FAILURE_OBSERVED' if m==d.TARGETS[3] else 'OBSERVED_VISIBILITY_FAILURE_REPRODUCED','diagnostics':d.failure_diagnostics(m,text)})
    (evidence/'owned-modules.jsonl').write_text(''.join(json.dumps(r,sort_keys=True,separators=(',',':'))+'\n' for r in modules));write('original-probes.json',probes)
    names=['source-extraction.json','runtime-inventory.json','read-only-boundary-preflight.json','dependency-sources.json','selected-cache-closure.json','cached-build-inventory.json','selected-cache-admission.json','cache-client-binary.json','commands.jsonl','owned-modules.jsonl','original-probes.json','fresh-owned-objects.json']
    result={'schema':d.SCHEMA,'status':d.SUCCESS,'complete_evidence':True,'contract_sha256':contract_sha,'full_official_verification_claimed':False,'owned_objects_from_prior_runs':False,'command_count':len(commands),'complete_log_bytes':log_bytes,'checked_owned_module_count':174,'init_only_actual_original_corrected_control_passed':True,'protected_inputs_and_runtime_revalidated':True,'terminal_receipts':{name:d.f.file_sha(evidence/name) for name in names}}
    write('result.json',result)
    return {'work':work,'contract':c,'contract_sha':contract_sha,'synthetic_runtime_sha':d.f.sha(d.f.json_bytes(runtime)),'commands':commands,'modules':modules,'probes':probes}
