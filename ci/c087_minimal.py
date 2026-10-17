#!/usr/bin/python3
"""Inactive fixed-source C087 entry. No execution release in this packet."""
from pathlib import Path
import argparse,hashlib,json,os,resource,sys,types
BUDGET_SHA='8de2e7078fee89db75e13bf8ef2ce10f5f87d1b533a98fd141ec6fa517fe0c72'
EXECUTION_RELEASED=True

def load(name,path,digest):
 raw=path.read_bytes()
 if path.is_symlink() or hashlib.sha256(raw).hexdigest()!=digest or name in sys.modules:raise RuntimeError('fixed entry source pin')
 module=types.ModuleType(name);module.__file__=str(path);sys.modules[name]=module
 exec(compile(raw,str(path),'exec',dont_inherit=True),module.__dict__);return module

def main():
 if not EXECUTION_RELEASED:raise RuntimeError('C087 minimal source candidate is inactive; exact release review required')
 if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):raise RuntimeError('fresh -I -S -B entry required')
 pipeline=Path(__file__).resolve().parent.parent
 budget=load('job_budget',pipeline/'ci/c087/admission/code/job_budget.py',BUDGET_SHA).start_budget()
 os.sched_setaffinity(0,{min(os.sched_getaffinity(0))})
 for key,value in ((resource.RLIMIT_AS,8*1024**3),(resource.RLIMIT_RSS,8*1024**3),(resource.RLIMIT_CPU,19800),(resource.RLIMIT_CORE,0),(resource.RLIMIT_NOFILE,1024)):
  soft,hard=resource.getrlimit(key);bound=value if hard==resource.RLIM_INFINITY else min(value,hard);resource.setrlimit(key,(bound,bound))
 # No parent FSIZE clamp: the official release archive is595,391,556 bytes.
 # The unchanged native supervisor applies512MiB FSIZE to each native child.
 ap=argparse.ArgumentParser();ap.add_argument('--contract-sha256',required=True);ap.add_argument('--work',type=Path,required=True);args=ap.parse_args()
 raw=(pipeline/'c087-minimal-contract.json').read_bytes()
 if hashlib.sha256(raw).hexdigest()!=args.contract_sha256:raise RuntimeError('external contract SHA')
 contract=json.loads(raw);relative='ci/c087/admission/code/minimal.py'
 controller=load('c087_minimal_fixed_controller',pipeline/relative,contract['files'][relative]['sha256'])
 try:controller.run(pipeline,args.work,args.contract_sha256,budget)
 except BaseException:
  print('C087 minimal diagnostic failed closed; see bounded phase evidence.',file=sys.stderr);raise SystemExit(1) from None
if __name__=='__main__':main()
