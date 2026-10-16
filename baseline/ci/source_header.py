"""Copied bounded source-header parser; no staging or execution API."""
import re
MOD=re.compile(rb"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*")

def need(ok,msg):
 if not ok:raise ValueError(msg)

def skip(b,i):
 while i<len(b):
  if b[i:i+1] in (b' ',b'\t',b'\r',b'\n'):i+=1
  elif b[i:i+2]==b'--':
   j=b.find(b'\n',i);i=len(b) if j<0 else j+1
  elif b[i:i+2]==b'/-':
   depth=1;i+=2
   while i<len(b) and depth:
    if b[i:i+2]==b'/-':depth+=1;i+=2
    elif b[i:i+2]==b'-/':depth-=1;i+=2
    else:i+=1
   need(depth==0,'unterminated header block comment')
  else:break
 return i

def tok(b,i):
 i=skip(b,i);m=MOD.match(b,i)
 return (m.group().decode(),i,m.end()) if m else (None,i,i)

def check_import_line_tail(b,i):
 # The supported corpus has one import per physical line. Preserve inline
 # comments, but never silently treat a second module name as body syntax.
 while i<len(b) and b[i:i+1] not in (b'\n',b'\r'):
  if b[i:i+1] in (b' ',b'\t'):i+=1
  elif b[i:i+2]==b'--':return
  elif b[i:i+2]==b'/-':
   start=i;depth=1;i+=2
   while i<len(b) and depth:
    if b[i:i+2]==b'/-':depth+=1;i+=2
    elif b[i:i+2]==b'-/':depth-=1;i+=2
    else:i+=1
   need(depth==0,'unterminated trailing import comment')
   if b'\n' in b[start:i] or b'\r' in b[start:i]:return
  else:raise ValueError('unsupported trailing token or multiple modules on import line')

def header(b):
 need(not b.startswith(b'\xef\xbb\xbf'),'BOM is unsupported; requires explicit review')
 i=0;modern=False;prelude=False;imports=[];commands=[]
 t,s,e=tok(b,i)
 if t=='module':modern=True;commands.append((s,e));i=e;t,s,e=tok(b,i)
 if t=='prelude':prelude=True;commands.append((s,e));i=e
 while True:
  t,s,e=tok(b,i);start=s;mods=[]
  if t=='private':
   following,_,_=tok(b,e);need(following!='import','private import is unsupported')
  while t in ('public','meta'):
   mods.append(t);i=e;t,s,e=tok(b,i)
  if t!='import':
   break
  need(mods in ([],['public'],['meta'],['public','meta']),'unsupported import modifiers')
  i=e;name,ns,ne=tok(b,i);all_import=False
  if name=='all':all_import=True;i=ne;name,ns,ne=tok(b,i)
  need(name is not None and name not in ('import','module','prelude'),'missing import module')
  need(not (all_import and 'public' in mods),'public import all forbidden by Lean')
  check_import_line_tail(b,ne)
  imports.append({'module':name,'start':start,'end':ne,'modifiers':mods,'all':all_import})
  commands.append((start,ne));i=ne
 return {'modern':modern,'prelude':prelude,'imports':imports,'header_end':commands[-1][1] if commands else 0}
