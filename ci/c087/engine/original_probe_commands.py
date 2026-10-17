"""Pure exact command planner. It cannot execute or authenticate a restored tree."""
from pathlib import Path
import hashlib,importlib.util,sys
NATIVE_SHA='9085c9eea092c270fbd6952834839103c66519a7b4716fe09147001c7d96355d'
TARGET='SpectreFinite.RadiusFivePruningCertified'
FLAGS=['-j1','-M768','-Dcompiler.postponeCompile=false']
LIMITS={'address_space_bytes':8589934592,'rss_tree_bytes':8589934592,'max_created_file_bytes':536870912}

def canonical(value):
 if type(value) is not str or not value.startswith('/') or str(Path(value))!=value or '..' in Path(value).parts:raise ValueError('canonical absolute path required')
 return value

def native_module(path):
 path=Path(canonical(str(path)))
 if path.is_symlink() or hashlib.sha256(path.read_bytes()).hexdigest()!=NATIVE_SHA:raise ValueError('native command helper pin differs')
 name='c087_pinned_native_fresh_stage';spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);sys.modules[name]=m;spec.loader.exec_module(m)
 if Path(m.__file__)!=path:raise ValueError('native helper import path differs')
 return m

def plan(native,*,source_root,toolchain_root,stage_workspace,helper_root,helper_workspace):
 paths={k:canonical(v) for k,v in dict(source_root=source_root,toolchain_root=toolchain_root,workspace=stage_workspace).items()}
 helper_root=canonical(helper_root);helper_workspace=canonical(helper_workspace)
 roots=[Path(x) for x in (source_root,toolchain_root,stage_workspace,helper_root,helper_workspace)]
 roots += [Path(helper_workspace+'-control-'+x) for x in ('C087NegativeControls','C087SourceShapeControl','DefaultOptionControl','DisabledOptionControl')]
 if any(a==b or a in b.parents or b in a.parents for i,a in enumerate(roots) for b in roots[i+1:]):raise ValueError('command roots must be disjoint')
 specs=[]
 def add(name,argv,inner,layout,phase):
  specs.append(dict(name=name,execution_condition='default_compile_succeeded' if name in ('check-target-default','audit-target-default') else 'all_prior_required_gates_passed',argv=argv,inner_argv=inner,sandbox=layout,phase=phase,nominal_timeout_seconds=120,resource_limits=dict(LIMITS),max_log_bytes=16*1024**2,new_sessions_explicitly_allowed=False))
 # All helper compilation uses only official runtime plus this empty helper
 # object namespace; no project object/source root is in the read set.
 hp={'source_root':helper_root,'toolchain_root':toolchain_root,'workspace':helper_workspace}
 for module in ('C087RawContract','AuditC087Raw'):
  for phase in ('compile','check'):
   argv,inner,layout=native.readonly_command_layout(hp,module,module+'.lean',FLAGS if phase=='compile' else [],phase)
   add(phase+'-helper-'+module,argv,inner,layout,phase)
 # Each synthetic/option control gets a separate object namespace. Only the
 # real helper namespace is added, never another control or research objects.
 for module,extra in [('C087NegativeControls',[]),('C087SourceShapeControl',[]),('DefaultOptionControl',[]),('DisabledOptionControl',['-DElab.async=false'])]:
  cp={**hp,'workspace':helper_workspace+'-control-'+module}
  for phase in ('compile','check'):
   argv,inner,layout=native.readonly_command_layout(cp,module,module+'.lean',FLAGS+extra if phase=='compile' else [],phase)
   split=argv.index('--chdir');argv[split:split]=['--ro-bind',helper_workspace+'/objects',helper_workspace+'/objects']
   i=argv.index('LEAN_PATH');argv[i+1]=layout['environment']['LEAN_PATH'].split(':')[0]+':'+helper_workspace+'/objects:'+toolchain_root+'/lib/lean'
   layout={**layout,'readonly_roots':layout['readonly_roots']+[helper_workspace+'/objects'],
           'environment':{**layout['environment'],'LEAN_PATH':argv[i+1]}}
   add(phase+'-control-'+module,argv,inner,layout,phase)
 for profile,extra in [('default',[]),('async_off',['-DElab.async=false'])]:
  for phase in ('compile','check'):
   argv,inner,layout=native.readonly_command_layout(paths,TARGET,TARGET.replace('.','/')+'.lean',FLAGS+extra if phase=='compile' else [],phase)
   add(phase+'-target-'+profile,argv,inner,layout,phase)
  # Exact immutable target object namespace is the same one used by the
  # native checker. Helper code/objects add a separate, disjoint core namespace.
  argv,_,layout=native.readonly_command_layout(paths,TARGET,TARGET.replace('.','/')+'.lean',[],'check')
  argv=argv[:argv.index('--')]
  split=argv.index('--chdir');argv[split:split]=['--ro-bind',helper_root,helper_root,'--ro-bind',helper_workspace+'/objects',helper_workspace+'/objects']
  i=argv.index('LEAN_PATH');argv[i+1]=helper_workspace+'/objects:'+argv[i+1]
  inner=[toolchain_root+'/bin/lean','-j1','-M768','--run',helper_root+'/AuditC087Raw.lean']
  argv+=['--',*inner]
  layout={**layout,'readonly_roots':layout['readonly_roots']+[helper_root,helper_workspace+'/objects'],
          'environment':{**layout['environment'],'LEAN_PATH':helper_workspace+'/objects:'+layout['environment']['LEAN_PATH']}}
  add('audit-target-'+profile,argv,inner,layout,'audit')
 return specs
