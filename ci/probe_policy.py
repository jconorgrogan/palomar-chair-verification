"""Pure, inactive C087 A/B policy. No acquisition, process execution, or admission."""
from __future__ import annotations
import copy,hashlib,json,math,re
TARGET='SpectreFinite.RadiusFivePruningCertified'
TARGETS=('SpectreFinite.HexSearch.RadiusFivePruning.certifiedFamily_occurrenceComplete',
         'SpectreFinite.HexSearch.RadiusFivePruning.extract_mem_certifiedFamily')
SUFFIXES=('.olean','.olean.private','.olean.server','.ilean','.ir','.ir.sig')
FLAGS=['-j1','-M768','-Dcompiler.postponeCompile=false']
LIMITS={'address_space_bytes':8589934592,'rss_tree_bytes':8589934592,'max_created_file_bytes':536870912}
THREAD_ABORT=b"libc++abi: terminating due to uncaught exception of type lean::exception: failed to create thread: Resource temporarily unavailable\n"
FALSE_FLAGS=('timed_out','memory_exceeded','log_overflow','surviving_children','escaped_descendants')
TRUE_FLAGS=('process_group_empty','descendants_empty')
class Rejected(ValueError):pass
def need(ok,msg):
 if not ok:raise Rejected(msg)
def sha(raw):return hashlib.sha256(raw).hexdigest()
def checked_integer(v,maximum):need(type(v) is int and 0<v<=maximum,'invalid bounded integer');return v

def validate_profiles(profiles):
 need(type(profiles) is list and len(profiles)==2,'exact paired profiles required')
 need([x.get('name') for x in profiles]==['default','async_off'],'paired profile order differs')
 a,b=[x['profile'] for x in profiles]
 need(a['compile_flags']==FLAGS and b['compile_flags']==FLAGS+['-DElab.async=false'],'only explicit async-off variation allowed')
 need(a=={**b,'compile_flags':FLAGS},'paired profiles differ beyond async scheduling')
 for p in (a,b):
  need(p['check_flags']==[],'checker flags changed')
  need(type(p['compile_timeout_seconds']) is int and p['compile_timeout_seconds']==120,'compile timeout changed')
  need(type(p['check_timeout_seconds']) is int and p['check_timeout_seconds']==120,'checker timeout changed')
  need(all(type(p.get(k)) is int and p[k]==v for k,v in LIMITS.items()),'resource ceiling changed')
 return copy.deepcopy(profiles)

def effective_timeout(nominal,remaining):
 checked_integer(nominal,120)
 need(type(remaining) in (float,int) and math.isfinite(remaining) and remaining>0,'invalid remaining shared deadline')
 effective=min(nominal,math.floor(remaining));checked_integer(effective,nominal)
 return effective

def safety(record):
 need(type(record) is dict and type(record.get('exit_code')) is int,'true exit code required')
 need(all(record.get(k) is False for k in FALSE_FLAGS) and all(record.get(k) is True for k in TRUE_FLAGS),'command resource/cleanup failure')
 checked_integer(record.get('timeout_seconds'),120)
 need(type(record.get('elapsed_seconds')) in (float,int) and math.isfinite(record['elapsed_seconds']) and record['elapsed_seconds']>=0,'invalid elapsed time')
 # The external process watchdog's bounded cleanup can outlast its execution
 # timeout. It must report timed_out rather than disguising that as success.
 return record

def classify_compile(profile,record,stdout,stderr):
 need(profile in ('default','async_off'),'unknown profile')
 need(type(stdout) is bytes and type(stderr) is bytes and len(stdout)+len(stderr)<=16*1024**2,'complete bounded logs required')
 safety(record)
 if record['exit_code']==0:return 'compiled_pending_check_and_raw_audit'
 need(profile=='default' and record['exit_code']==134 and stdout==b'' and stderr==THREAD_ABORT,
      'only the exact bounded default thread-creation abort may continue to B')
 return 'observed_default_thread_creation_abort_no_outputs_admitted'

def require_success(record):safety(record);need(record['exit_code']==0,'helper/check/audit failed')

def validate_output_map(module,files,byte_limit=536870912):
 need(type(files) is dict,'output map required')
 expected={'objects/'+module.replace('.','/')+s for s in SUFFIXES}
 need(set(files)==expected,'exact six modern output companions required')
 total=0
 for row in files.values():
  need(type(row) is dict and set(row)=={'bytes','sha256'},'output metadata fields differ')
  total+=checked_integer(row['bytes'],byte_limit)
  need(type(row['sha256']) is str and re.fullmatch('[0-9a-f]{64}',row['sha256']) is not None,'invalid output digest')
 need(total<=byte_limit,'combined output cap exceeded')
 return total

def parse_audit(raw):
 need(type(raw) is bytes and len(raw)<=16*1024**2,'bounded raw audit output required')
 def pairs(items):
  out={}
  for key,value in items:need(key not in out,'duplicate audit JSON key');out[key]=value
  return out
 try:
  text=raw.decode('utf-8','strict');lines=text.splitlines()
  need(len(lines)==3 and lines[-1]=='C087_RAW_CONTRACT_PASSED' and text.endswith('\n'),'complete exact audit output required')
  rows=[json.loads(line,object_pairs_hook=pairs,parse_constant=lambda _:(_ for _ in ()).throw(Rejected('nonfinite audit'))) for line in lines[:2]]
 except (UnicodeError,json.JSONDecodeError) as e:raise Rejected('invalid audit output') from e
 keys={'status','module','theorem','universe_parameters','exact_raw_type','exact_raw_source_proof','closed_type_and_proof','exact_module_owned_set','raw_type','raw_proof','all_owned_transitive_axioms','visited_raw_dependencies','independent_kernel_check_claimed','fresh_source_provenance_claimed'}
 for name,row in zip(TARGETS,rows):
  need(type(row) is dict and set(row)==keys,'audit fields differ')
  need(row['status']=='C087_EXACT_RAW_THEOREM_CONTRACT_PASSED' and row['module']==TARGET and row['theorem']==name,'audit target/order differs')
  need(row['universe_parameters']==[],'audit universes differ')
  need(all(row[x] is True for x in ('exact_raw_type','exact_raw_source_proof','closed_type_and_proof','exact_module_owned_set')),'raw audit gate failed')
  need(all(row[x] is False for x in ('independent_kernel_check_claimed','fresh_source_provenance_claimed')),'audit overclaim')
  need(all(type(row[x]) is str and row[x] for x in ('raw_type','raw_proof')),'raw type/proof absent')
  ax=row['all_owned_transitive_axioms'];need(type(ax) is list and all(type(x) is str for x in ax) and len(ax)==len(set(ax)) and set(ax)<={'propext','Classical.choice','Quot.sound'},'nonstandard/duplicate axioms')
  checked_integer(row['visited_raw_dependencies'],1000000)
 need(rows[0]['all_owned_transitive_axioms']==rows[1]['all_owned_transitive_axioms'] and rows[0]['visited_raw_dependencies']==rows[1]['visited_raw_dependencies'],'whole-module audit closure fields differ')
 return rows

def compare_successful_profiles(default_audit,async_audit):
 a,b=parse_audit(default_audit),parse_audit(async_audit)
 need(a==b,'default/async exact raw theorem audit differs')
 return {'both_profiles_compiled_checked_audited':True,'raw_type_and_proof_equal':True,'olean_byte_identity_claimed':False,'os_failure_cause_proven':False,'final_C_proof_claimed':False}

# Distinct live gate: the compact historical tail cannot satisfy this schema.
# This validates a record from the pinned controller; it does not by itself
# authenticate a process, shared deadline, output path, or supplied dictionary.
NATIVE_RESULT_KEYS={'exit_code','timed_out','log_overflow','memory_exceeded','surviving_children',
 'escaped_descendants','new_sessions_explicitly_allowed','process_group_empty','descendants_empty',
 'cleanup_bound_seconds','cleanup_elapsed_seconds','peak_sampled_tree_rss_bytes','elapsed_seconds'}
def validate_live_command(expected_spec,record,stdout,stderr,*,expected_effective_timeout):
 need(type(expected_spec) is dict and type(record) is dict,'live spec/record required')
 need(set(record)=={'spec','effective_timeout_seconds','result','stdout','stderr'},'exact live record shape required')
 need(record['spec']==expected_spec,'live argv/environment/resource/layout/name differs')
 need(expected_spec.get('new_sessions_explicitly_allowed') is False,'live session escape allowance forbidden')
 need(expected_spec.get('resource_limits')==LIMITS and all(type(v) is int for v in expected_spec['resource_limits'].values()),'live resource caps differ')
 need(type(expected_spec.get('nominal_timeout_seconds')) is int and expected_spec['nominal_timeout_seconds']==120,'live nominal timeout differs')
 need(type(expected_spec.get('max_log_bytes')) is int and expected_spec['max_log_bytes']==16*1024**2,'live log cap differs')
 checked_integer(expected_effective_timeout,120)
 need(type(record['effective_timeout_seconds']) is int and record['effective_timeout_seconds']==expected_effective_timeout,'actual invocation/effective timeout mismatch')
 result=record['result'];need(type(result) is dict and set(result)==NATIVE_RESULT_KEYS,'native live result shape differs')
 need(result['new_sessions_explicitly_allowed'] is False,'native result allowed a new session')
 need(type(result['cleanup_bound_seconds']) in (int,float) and math.isfinite(result['cleanup_bound_seconds']) and result['cleanup_bound_seconds']==3.0,'native cleanup guard differs')
 need(type(result['cleanup_elapsed_seconds']) in (int,float) and math.isfinite(result['cleanup_elapsed_seconds']) and 0<=result['cleanup_elapsed_seconds']<=3,'invalid native cleanup elapsed')
 need(type(result['peak_sampled_tree_rss_bytes']) is int and 0<=result['peak_sampled_tree_rss_bytes']<=LIMITS['rss_tree_bytes'],'invalid native RSS observation')
 safety({**result,'timeout_seconds':expected_effective_timeout})
 for stream,raw in (('stdout',stdout),('stderr',stderr)):
  need(type(raw) is bytes,'complete live log bytes required')
  row=record[stream];need(type(row) is dict and set(row)=={'bytes','sha256'} and type(row['bytes']) is int and type(row['sha256']) is str,'live log row schema differs')
  need(row=={'bytes':len(raw),'sha256':sha(raw)},'live log bytes/hash mismatch')
 need(len(stdout)+len(stderr)<=expected_spec['max_log_bytes'],'live combined logs exceed cap')
 return copy.deepcopy(result)
