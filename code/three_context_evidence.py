#!/usr/bin/env python3
"""Always-run small evidence bundle; cannot authorize semantic admission."""
from __future__ import annotations
import argparse,hashlib,importlib.util,json,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
# BOOTSTRAP_PIN is sealed together with the helper before publication.
BOOTSTRAP_PIN='0ea2d6be51208e03248f5dd062b57c85bbc6b5768d156b27032891c15d10a06a'
path=HERE/'three_context_local.py'
if path.is_symlink() or hashlib.sha256(path.read_bytes()).hexdigest()!=BOOTSTRAP_PIN:raise RuntimeError('evidence helper pin mismatch')
spec=importlib.util.spec_from_file_location('three_context_local',path);l=importlib.util.module_from_spec(spec);sys.modules[spec.name]=l;spec.loader.exec_module(l)
CAP=64*1024**2

def candidates(root):
    fixed=['RESULT.json','logs/acquisition.stdout','logs/acquisition.stderr','logs/semantic.stdout','logs/semantic.stderr',
        'acquired/TRANSPORT_RECEIPT.json','acquired/WRAPPERS.json','acquired/AUTHENTICATED_PREPARES.json',
        'semantic-write/output/SELECTED_CANDIDATE.json','semantic-write/output/NATIVE_VALIDATION.json','semantic-write/output/COMPLETION.json']
    rows=[root/name for name in fixed if (root/name).exists()]
    acquired=root/'acquired'
    if acquired.exists():
        l.canonical(str(acquired))
        for path in sorted(acquired.rglob('*')):
            l.need(not path.is_symlink(),'evidence symlink forbidden')
            if path.is_file() and path.name in {'identity.json','inventory.json','upload-candidate.json','receipt.json'}:rows.append(path)
    l.need(len(rows)==len(set(rows)),'duplicate selected evidence')
    return rows

def bundle(workspace,output):
    root=l.canonical(str(workspace));out=l.canonical(str(output));l.need(root!=out and root not in out.parents and out not in root.parents,'evidence roots overlap')
    l.need(not out.exists(),'evidence output must be new');rows=candidates(root) if root.exists() else []
    sizes={p:l.regular(p).st_size for p in rows};total=sum(sizes.values())
    # Fail closed on oversized full evidence but retain only bounded command tails.
    truncated=total>CAP-1024**2
    if truncated:rows=[p for p in rows if p.relative_to(root).as_posix().startswith('logs/')]
    out.mkdir();files={}
    for path in rows:
        name=path.relative_to(root).as_posix();dest=out/name;dest.parent.mkdir(parents=True,exist_ok=True)
        if truncated:
            with path.open('rb') as stream:stream.seek(max(0,sizes[path]-1024**2));raw=stream.read(1024**2)
            dest=dest.with_name(dest.name+'.tail');name=dest.relative_to(out).as_posix()
        else:raw=path.read_bytes()
        l.durable(dest,raw);files[name]={'bytes':len(raw),'sha256':l.sha(raw)}
    status={'schema':'historical-admission-evidence-bundle-v1','status':'bounded_partial_evidence' if truncated or 'RESULT.json' not in files else 'complete_candidate_evidence',
        'proof_pass_claimed':False,'activation_allowed':False,'terminal_job_success_and_controller_exit_zero_required':True,
        'original_selected_bytes':total,'truncated':truncated,'files':files}
    l.durable(out/'EVIDENCE.json',l.json_bytes(status));l.need(sum(p.stat().st_size for p in out.rglob('*') if p.is_file())<=CAP,'evidence cap exceeded')
    return status

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--workspace',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args();bundle(args.workspace,args.output)
if __name__=='__main__':main()
