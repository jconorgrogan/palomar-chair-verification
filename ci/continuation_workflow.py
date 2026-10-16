"""Pure candidate renderer. Returns text only, never installs or runs a workflow."""
from __future__ import annotations
import re
import fresh_stage as f
import continuation_policy as p


def render_candidate(template: str, selection: p.Selection, plan: dict, contract_sha256: str, source_commit: str) -> str:
    p.digest(contract_sha256,'candidate contract hash')
    f.need(isinstance(selection,p.Selection),'inactive/null selection cannot generate a workflow')
    f.need(f.sha(template.encode())=='517d4ca8778dc6797c32755c8d47c0cb758f01a47c8c6ecb1fb1edf8899676d4','original workflow template hash mismatch')
    f.need(f.COMMIT.fullmatch(source_commit or '') and source_commit!=p.SOURCE,'exact new source commit required')
    header,body=template.split('jobs:\n',1)
    header=header.replace('verify/hierarchy-c-modern-20261016','verify/hierarchy-c-meta-continuation-20261016')
    header=header.replace('hierarchy-c-modern.yml','hierarchy-c-meta-continuation.yml')
    header=header.replace('Fresh modern hierarchy C verification (work in progress)','Continued modern hierarchy C verification (clean rebuild pending)')
    header=header.replace('group: hierarchy-c-modern-', 'group: hierarchy-c-meta-continuation-')
    parts=re.split(r'(?m)^(  [a-z][a-z0-9_]*:\n)',body)
    f.need(len(parts)>1 and parts[0]=='','unexpected reviewed workflow template')
    groups={w['job_id']:w for w in p.nonempty_waves(selection,plan)}
    f.need(groups,'no fresh stages selected')
    blocks={parts[i][2:-2]:parts[i]+parts[i+1] for i in range(1,len(parts),2)}
    expected={'prepare',*[s['producer_job'] for s in plan['stages']],
              'export_target','fresh_kernel','lean_export','nanoda','conron','verdict'}
    f.need(set(blocks)==expected,'unexpected job set in template')
    result=header+'jobs:\n'
    last=list(groups)[-1]
    for name,block in blocks.items():
        if name.startswith('wave_'):
            if name not in groups:continue
            group=groups[name]
            block,n=re.subn(r'(?m)^    needs: \[[^\n]*\]$',
                '    needs: ['+', '.join(group['needs'])+']',block);f.need(n==1,'wave dependency ambiguity')
            block,n=re.subn(r'(?m)^        stage: \[[^\n]*\]$',
                '        stage: ['+', '.join('"'+s+'"' for s in group['stage_ids'])+']',block);f.need(n==1,'matrix ambiguity')
        elif name in ('export_target','fresh_kernel'):
            block,n=re.subn(r'(?m)^    needs: \[[^\n]*\]$',
                '    needs: [prepare, '+last+']',block);f.need(n==1,'final restore dependency ambiguity')
        block=block.replace('pipeline/ci/ci_driver.py','pipeline/ci/continuation_driver.py')
        block,n=re.subn(r'--contract-sha256 [0-9a-f]{64}', '--contract-sha256 '+contract_sha256,block)
        f.need(n==1,'job must have exactly one verifier invocation')
        block=block.replace('4a0cbd71ba9cd318620e11694037d956d2393d06',source_commit)
        result+=block
    f.need('max-parallel: 4' in result and 'ubuntu-22.04' in result,'runner limits absent')
    return '# SOURCE-ONLY CANDIDATE. Requires separate publication authority and review.\n'+result
