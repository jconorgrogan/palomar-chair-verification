#!/usr/bin/env python3
"""Best-effort bounded incomplete evidence only; never a successful proof artifact."""
import argparse,hashlib,json,os
from pathlib import Path
MAX_TAIL=256*1024
MAX_LOGS=16
MAX_RECEIPT=128*1024

def main():
    p=argparse.ArgumentParser();p.add_argument('role');p.add_argument('--stage');a=p.parse_args()
    import re
    if not re.fullmatch(r'[a-z][a-z0-9_]*',a.role) or (a.stage and not re.fullmatch(r'[a-z][a-z0-9_]*',a.stage)):
        raise SystemExit('invalid diagnostic role')
    base=Path(os.environ['RUNNER_TEMP'])
    root=base/('hierarchy-c-'+a.role+(('-'+a.stage) if a.stage else ''))
    out=base/('hierarchy-c-failure-'+a.role+(('-'+a.stage) if a.stage else ''))
    if out.exists() or out.is_symlink():raise SystemExit('failure output already exists')
    out.mkdir();entries=[];logs=[]
    if root.exists() and not root.is_symlink():
        for directory in [root/'logs',root/'stage'/'logs']:
            if directory.is_dir() and not directory.is_symlink():
                for path in directory.rglob('*'):
                    if path.is_symlink() or any(p.is_symlink() for p in path.parents):continue
                    if path.is_file() and path.suffix in ('.stdout','.stderr') and path.name!='target_export.stdout':logs.append(path)
                    if len(logs)>4096:raise SystemExit('diagnostic enumeration bound exceeded')
        for index,path in enumerate(sorted(logs,key=lambda p:p.stat().st_mtime_ns,reverse=True)[:MAX_LOGS]):
            size=path.stat().st_size
            with path.open('rb') as h:h.seek(max(0,size-MAX_TAIL));data=h.read(MAX_TAIL)
            name=f'log-{index:02d}{path.suffix}.tail';(out/name).write_bytes(data)
            entries.append({'file':name,'original_relative_path':path.relative_to(root).as_posix(),'original_bytes':size,'tail_bytes':len(data),'tail_sha256':hashlib.sha256(data).hexdigest(),'truncated':size>len(data)})
        for index,path in enumerate([root/'last_command.json',root/'stage'/'last_command.json']):
            if path.is_file() and not any(p.is_symlink() for p in [path,*path.parents]) and path.stat().st_size<=MAX_RECEIPT:
                value=json.loads(path.read_bytes());safe={k:value[k] for k in ['name','exit_code','timed_out','log_overflow','memory_exceeded','surviving_children','escaped_descendants','process_group_empty','descendants_empty','elapsed_seconds','timeout_seconds'] if k in value}
                name=f'last-command-{index}.json';(out/name).write_text(json.dumps(safe,sort_keys=True,indent=2)+'\n')
    result={'schema':'hierarchy-c-incomplete-evidence-v1','status':'incomplete_or_failed','proof_pass_claimed':False,'role':a.role,'stage':a.stage,'run_id':os.environ.get('GITHUB_RUN_ID'),'run_attempt':os.environ.get('GITHUB_RUN_ATTEMPT'),'pipeline_commit':os.environ.get('GITHUB_SHA'),'logs':entries,'note':'Bounded diagnostic tails only. Missing logs are possible after cancellation or VM shutdown. This artifact is never a successful stage or final receipt.'}
    (out/'incomplete.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print(json.dumps({'status':'incomplete_or_failed','diagnostic_files':len(list(out.iterdir())),'maximum_log_tail_bytes':MAX_LOGS*MAX_TAIL}))
if __name__=='__main__':main()
