#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[1]
j=json.loads((R/'SOURCE_MANIFEST.json').read_text())
assert j['selected_theorem']=='PalomarMonotiles.T5_isAperiodicMonotile' and j['definition_names']==[]
for name,h in j['files'].items():
 p=R/name;assert p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==h,name
for p in R.rglob('*.lean'):
 if '.lake' in p.parts:continue
 s=p.read_text();assert s.startswith('module\n'),str(p);assert len(s.splitlines())<=10000,str(p)
 # Remove nested Lean block/line comments for admission-token checks.
 out=[];i=0;depth=0;quoted=False
 while i<len(s):
  if depth:
   if s.startswith('/-',i):depth+=1;i+=2
   elif s.startswith('-/',i):depth-=1;i+=2
   else:i+=1
  elif quoted:
   if s[i]=='\\':i+=2
   elif s[i]=='"':quoted=False;i+=1
   else:i+=1
  elif s.startswith('/-',i):depth=1;i+=2
  elif s.startswith('--',i):
   k=s.find('\n',i);i=len(s) if k<0 else k
  elif s[i]=='"':quoted=True;i+=1
  else:out.append(s[i]);i+=1
 code=''.join(out)
 assert not re.search(r'\b(?:axiom|admit|native_decide)\b|Lean\.(?:ofReduceBool|trustCompiler)',code),str(p)
 holes=len(re.findall(r'\bsorry\b',code))
 assert holes==(1 if p.name=='Challenge.lean' and p.parent==R else 0),(str(p),holes)
 if p.name=='Challenge.lean' and p.parent==R:
  assert len(s.encode())<=102400 and len(s.splitlines())<=1000
cfg=json.loads((R/'comparator.json').read_text())
assert cfg['theorem_names']==['PalomarMonotiles.T5_isAperiodicMonotile']
assert cfg['definition_names']==[]
assert set(cfg['permitted_axioms'])=={'propext','Quot.sound','Classical.choice'}
assert 'external_kernels' not in cfg
print('Source manifest and selected statement surface verified; this is not a proof check.')
