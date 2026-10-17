"""Fixed C087 outer job clock/TERM boundary; no execution authority or process API."""
from __future__ import annotations
from dataclasses import dataclass
from datetime import datetime,timezone
from fractions import Fraction
import math,signal,threading,time,weakref
MAX_SECONDS=19800
FIXED_EXPIRY=datetime(2026,10,22,6,15,54,tzinfo=timezone.utc)
_issued=weakref.WeakSet()
_production_started=False
class Expired(RuntimeError):pass
class Rejected(ValueError):pass
def need(ok,msg):
 if not ok:raise Rejected(msg)
def number(x):return type(x) in (int,float) and math.isfinite(x)
def aware(x):return isinstance(x,datetime) and x.tzinfo is not None and x.utcoffset() is not None

def lower_deadline(start,seconds):
 need(number(start) and start>=0 and number(seconds) and seconds>0,'finite positive clock interval required')
 value=math.nextafter(float(start)+float(seconds),-math.inf)
 need(math.isfinite(value) and value>start,'unrepresentable positive clock interval')
 return value

def command_timeout(nominal,deadline,dispatch):
 need(type(nominal) is int and 0<nominal<=MAX_SECONDS,'positive bounded nominal timeout required')
 need(number(deadline) and number(dispatch) and 0<=dispatch<deadline,'finite ordered dispatch clocks required')
 remaining=Fraction(deadline)-Fraction(dispatch)-3
 seconds=min(nominal,remaining.numerator//remaining.denominator)
 if seconds<=0:raise Expired('insufficient original deadline for execution and cleanup')
 return seconds

@dataclass(frozen=True)
class OriginalDeadline:
 original_monotonic:float
 deadline_monotonic:float
 original_wall:datetime
 expiry_wall:datetime

class JobBudget:
 def __init__(self,*args,**kwargs):raise Rejected('use the fixed entry-time budget factory')
 def _observe_checked(self):
  now=self._clock();wall=self._wall()
  need(number(now) and now>=self._last_mono and aware(wall),'invalid/backward controller clock')
  need(wall>=self._last_wall,'backward controller wall clock')
  self._last_mono=float(now);self._last_wall=wall
  if self._expired or now>=self._deadline or wall>=self._expiry:raise Expired('original controller deadline exhausted')
  # A forward wall jump can tighten but can never renew the absolute budget.
  self._deadline=min(self._deadline,lower_deadline(float(now),(self._expiry-wall).total_seconds()))
  if now>=self._deadline:raise Expired('original controller deadline exhausted')
  return float(now),wall
 def _observe(self):
  try:return self._observe_checked()
  except BaseException:
   self._expired=True
   raise
 @property
 def original(self):
  return OriginalDeadline(self._entry,self._initial_deadline,self._entry_wall,self._initial_expiry)
 @property
 def deadline_monotonic(self):self.check();return self._deadline
 @property
 def expiry_wall(self):self.check();return self._expiry
 def check(self):
  now,_=self._observe();left=self._deadline-now
  if not math.isfinite(left) or left<=0:
   self._expired=True;raise Expired('original controller deadline exhausted')
  return math.nextafter(left,-math.inf)
 def remaining(self):
  seconds=math.floor(self.check())
  if seconds<=0:raise Expired('positive whole-second command budget unavailable')
  return seconds
 def tighten_expiry(self,expiry):
  need(aware(expiry),'aware fixed expiry required')
  self._expiry=min(self._expiry,expiry);self.check()
 def handler(self,signum,frame):
  self._expired=True
  if not self._in_process:raise Expired('outer supervisor expired during host work')
 def process(self,call):
  # Complete the pinned native supervisor, including its finally cleanup, before
  # rejecting a TERM. Engine consumption is one synchronous protected operation;
  # each post-native-command checkpoint sees the recorded expiry immediately.
  need(not self._in_process,'nested controller process boundary')
  self.check();self._in_process=True
  try:return call()
  finally:self._in_process=False;self.check()
 def __enter__(self):
  need(not self._entered and threading.current_thread() is threading.main_thread(),'one main-thread TERM scope required')
  previous=signal.getsignal(signal.SIGTERM)
  need(previous in (signal.SIG_DFL,signal.SIG_IGN),'unexpected TERM handler')
  self.check();self._previous=previous;signal.signal(signal.SIGTERM,self.handler);self._entered=True;return self
 def __exit__(self,*args):
  need(self._entered,'TERM scope absent')
  try:signal.signal(signal.SIGTERM,self._previous)
  finally:self._entered=False

def _make(entry,entry_wall,clock,wall,*,synthetic):
 need(number(entry) and entry>=0 and aware(entry_wall),'entry clock values required')
 need(entry_wall<FIXED_EXPIRY,'original historical expiry already passed')
 obj=object.__new__(JobBudget)
 obj._clock=clock;obj._wall=wall;obj._entry=float(entry);obj._entry_wall=entry_wall
 obj._last_mono=float(entry);obj._last_wall=entry_wall;obj._expiry=FIXED_EXPIRY
 obj._deadline=min(lower_deadline(float(entry),MAX_SECONDS),lower_deadline(float(entry),(FIXED_EXPIRY-entry_wall).total_seconds()))
 obj._initial_deadline=obj._deadline;obj._initial_expiry=FIXED_EXPIRY
 obj._expired=False;obj._in_process=False;obj._entered=False;obj._previous=None;obj._synthetic=synthetic
 obj.check()
 if not synthetic:_issued.add(obj)
 return obj

def start_budget():
 # Call as the controller's first operation, before setup hashes/extraction.
 global _production_started
 need(not _production_started,'original production budget cannot be renewed')
 _production_started=True
 entry=time.monotonic();wall=datetime.now(timezone.utc)
 return _make(entry,wall,time.monotonic,lambda:datetime.now(timezone.utc),synthetic=False)

def require_production_budget(value):
 need(type(value) is JobBudget and value in _issued and not value._synthetic,'fixed in-process production budget required')
 value.check();return value

def _for_tests(entry,entry_wall,clock,wall):return _make(entry,entry_wall,clock,wall,synthetic=True)
