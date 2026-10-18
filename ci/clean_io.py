"""Inactive bounded driver support. No CLI or automatic external action."""
from __future__ import annotations
import copy,hashlib,importlib.util,json,math,os,signal,stat,sys,threading,time
from pathlib import Path
from datetime import datetime,timezone
import fresh_stage as f
import clean_local as l
ENTRY_MONOTONIC=time.monotonic()
class Expired(RuntimeError):pass

class JobBudget:
    """TERM records expiry during frozen process cleanup; host work stops immediately."""
    def __init__(self,entry=ENTRY_MONOTONIC,wall_clock=None):
        self.deadline=entry+19800;self.expired=False;self.in_child=False;self.previous=None
        self.wall_clock=wall_clock or (lambda:datetime.now(timezone.utc))
        self.last_wall=self.wall_clock();l.need(isinstance(self.last_wall,datetime) and self.last_wall.tzinfo is not None,'aware controller clock required')
        self.wall_deadline=self.last_wall.timestamp()+518400
    def handler(self,signum,frame):
        self.expired=True
        if not self.in_child:raise Expired('outer job deadline reached')
    def __enter__(self):
        l.need(threading.current_thread() is threading.main_thread(),'main-thread controller required')
        self.previous=signal.getsignal(signal.SIGTERM)
        l.need(self.previous in (signal.SIG_DFL,signal.SIG_IGN),'unexpected existing TERM handler')
        signal.signal(signal.SIGTERM,self.handler);return self
    def __exit__(self,*args):signal.signal(signal.SIGTERM,self.previous)
    def tighten(self,deadline):self.deadline=min(self.deadline,deadline);self.check()
    def tighten_wall(self,deadline):
        l.need(type(deadline) in (int,float) and math.isfinite(deadline),'invalid fixed wall deadline')
        self.wall_deadline=min(self.wall_deadline,deadline);self.check()
    def check(self):
        now=self.wall_clock();l.need(isinstance(now,datetime) and now.tzinfo is not None,'aware controller clock required')
        if now<self.last_wall or now.timestamp()>=self.wall_deadline:raise Expired('backward controller clock or clean expiry')
        self.last_wall=now
        self.deadline=min(self.deadline,time.monotonic()+self.wall_deadline-now.timestamp())
        if self.expired or time.monotonic()>=self.deadline:raise Expired('shared job deadline reached')
    def remaining(self):self.check();left=math.floor(self.deadline-time.monotonic());l.need(left>0,'shared deadline exhausted');return left
    def process(self,call):
        self.check();self.in_child=True
        try:return call()
        finally:self.in_child=False;self.check()

def native_receipts_to_text(plan,provenance,native_bytes,final):
    final.validate_native_predecessor_order(plan=plan,provenance=provenance,native_receipt_bytes=native_bytes)
    f.need(sum(len(raw) for raw in native_bytes.values()) <= final.FINAL_ARTIFACT_LIMIT,'native receipt map exceeds unchanged final artifact cap')
    result={sid:raw.decode('utf-8','strict') for sid,raw in native_bytes.items()}
    f.need(all(result[sid].encode('utf-8')==raw for sid,raw in native_bytes.items()),'native receipt UTF-8 roundtrip differs')
    return result

def native_receipts_from_text(plan,provenance,value,final):
    f.need(type(value) is dict and set(value)=={s['stage_id'] for s in plan['stages']} and all(type(x) is str for x in value.values()),'exact native receipt text map required')
    raw={sid:text.encode('utf-8','strict') for sid,text in value.items()}
    f.need(sum(len(value) for value in raw.values()) <= final.FINAL_ARTIFACT_LIMIT,'native receipt map exceeds unchanged final artifact cap')
    final.validate_native_predecessor_order(plan=plan,provenance=provenance,native_receipt_bytes=raw)
    return raw

def run_final_command(*,spec,root,environment,budget,executor=f.run_process,final):
    """Bind actual process timeout to the same nominal/absolute budget receipt."""
    budget.check()
    remaining=budget.remaining()
    f.need(type(remaining) is int and remaining>0,'invalid remaining shared deadline')
    nominal=spec.get('timeout_seconds')
    f.need(type(nominal) is int and nominal>0,'invalid nominal final command cap')
    effective=min(nominal,remaining)
    out=Path(root)/'logs'/(spec['name']+'.stdout');err=Path(root)/'logs'/(spec['name']+'.stderr')
    for path in (out,err):f.no_symlink_path(path);f.need(not path.exists(),'final log path already exists')
    result=budget.process(lambda:executor(spec['argv'],cwd=root,env=environment,timeout=effective,
        stdout=out,stderr=err,max_log_bytes=spec['max_log_bytes'],limits=spec['resource_limits'],
        allow_new_sessions=spec['new_sessions_explicitly_allowed']))
    budget.check()
    for path in (out,err):
        f.no_symlink_path(path);st=path.lstat();f.need(stat.S_ISREG(st.st_mode) and st.st_nlink==1,'final log must be regular single-link')
    record=copy.deepcopy(result);record.update(copy.deepcopy(spec));record['effective_timeout_seconds']=effective
    record.update(stdout={'bytes':out.stat().st_size,'sha256':f.file_sha(out)},stderr={'bytes':err.stat().st_size,'sha256':f.file_sha(err)})
    f.need(sum(record[s]['bytes'] for s in ('stdout','stderr'))<=spec['max_log_bytes'],'combined final logs exceed original cap')
    final._successful_command(record,spec)
    budget.check()
    return record,out
