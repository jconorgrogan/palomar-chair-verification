"""Single clean-run authenticated transport. No historical context or fallback."""
from __future__ import annotations
import copy,hashlib,http.client,json,math,os,re,shutil,socket,stat,sys,tarfile,time,urllib.error,urllib.parse,urllib.request,zipfile
from pathlib import Path
from datetime import datetime,timezone
import fresh_stage as f
import continuation_policy as cp
import ci_transport as ct
import origin_transport as base
import clean_policy as p
ot=base
RAW_CAP=4*1024**3
MIN_FREE=512*1024**2
METADATA_RESERVE=64*1024**2
INODE_RESERVE=256
MAX_PREPARE=32*1024**2
DIAGNOSTIC_PREFIX = 'CLEAN_TRANSPORT_FAILURE_V2 '
DIAGNOSTIC_PHASES = ('bootstrap','arguments','runtime_envelope','quarantine_create',
 'constructor','initial_snapshots','prepare_transfer','stage_transfer','receipt_copy',
 'historical_ledger','stage_reauthentication','final_snapshots','prepare_reauthentication',
 'certificate_build','certificate_write','certificate_finalize','cleanup')
DIAGNOSTIC_MESSAGES = {
 'quota headers unavailable':('QUOTA_SCHEMA','QUOTA_HEADERS_UNAVAILABLE'),
 'quota header missing, duplicated or malformed':('QUOTA_SCHEMA','QUOTA_HEADER_SHAPE'),
 'invalid numeric quota header':('QUOTA_SCHEMA','QUOTA_NUMERIC_HEADER'),
 'conflicting or unexpected quota headers':('QUOTA_SCHEMA','QUOTA_HEADER_CONFLICT'),
 'unexpected authenticated quota limit':('QUOTA_SCHEMA','QUOTA_LIMIT_UNEXPECTED'),
 'quota remaining outside limit':('QUOTA_SCHEMA','QUOTA_REMAINING_RANGE'),
 'quota used outside limit':('QUOTA_SCHEMA','QUOTA_USED_RANGE'),
 'quota used and remaining conflict':('QUOTA_SCHEMA','QUOTA_USED_REMAINING_MISMATCH'),
 'unexpected authenticated quota resource':('QUOTA_SCHEMA','QUOTA_RESOURCE_UNEXPECTED'),
 'invalid quota Date header':('QUOTA_SCHEMA','QUOTA_DATE'),
 'invalid authenticated quota metadata':('QUOTA_SCHEMA','QUOTA_METADATA'),
 'quota reset outside bounded server window':('QUOTA_WINDOW','QUOTA_RESET_WINDOW'),
 'backward authenticated quota clock or reset':('QUOTA_WINDOW','QUOTA_CLOCK_BACKWARD'),
 'quota remaining increased within one window':('QUOTA_WINDOW','QUOTA_REMAINING_INCREASED'),
 'quota reset advanced before its authenticated boundary':('QUOTA_WINDOW','QUOTA_RESET_EARLY'),
 'authenticated core quota exhausted; no further request':('QUOTA_WINDOW','QUOTA_EXHAUSTED'),
 'quota pacing cannot fit the unchanged request deadline':('DEADLINE','QUOTA_PACING_BUDGET'),
 'quota wait would exceed tightened deadline':('DEADLINE','QUOTA_WAIT_BUDGET'),
 'quota pacing request deadline exceeded':('DEADLINE','QUOTA_REQUEST_BUDGET'),
 'quota pacing exhausted original request timeout':('DEADLINE','QUOTA_TIMEOUT_BUDGET'),
 'invalid quota monotonic clock':('DEADLINE','QUOTA_CLOCK_INVALID'),
 'quota sleep made no monotonic progress':('DEADLINE','QUOTA_SLEEP_NO_PROGRESS'),
 'invalid original request timeout':('DEADLINE','REQUEST_TIMEOUT_INVALID'),
 'authenticated API quota or authorization failure; no retry':('AUTHORIZATION','API_QUOTA_OR_AUTHORIZATION'),
 'ephemeral read-only Actions token missing/invalid':('AUTHORIZATION','TOKEN_MISSING_OR_INVALID'),
 'quota source must be the authenticated approved repository':('AUTHORIZATION','API_SOURCE_BINDING'),
 'credentials on a storage request forbidden':('AUTHORIZATION','STORAGE_CREDENTIAL_REJECTED'),
 'unapproved API repository/path':('AUTHORIZATION','API_PATH_REJECTED'),
 'unsafe storage redirect':('AUTHORIZATION','STORAGE_REDIRECT_REJECTED'),
 'original fixed age deadline reached':('DEADLINE','ORIGINAL_AGE_EXPIRED'),
 'shared acquisition wall/age deadline reached':('DEADLINE','SHARED_DEADLINE_EXPIRED'),
 'metadata aggregate/origin deadline exceeded':('DEADLINE','METADATA_DEADLINE_EXPIRED'),
 'insufficient actual free disk including allocation/metadata reserve':('CAPACITY','DISK_HEADROOM'),
 'insufficient actual free inodes':('CAPACITY','INODE_HEADROOM'),
 'quarantine must be a canonical absolute path':('FILESYSTEM','QUARANTINE_CANONICAL'),
 'quarantine must be fresh with an existing parent':('FILESYSTEM','QUARANTINE_FRESH'),
 'quarantine parent must be owned by this user':('FILESYSTEM','QUARANTINE_OWNER'),
 'quarantine ownership/mode mismatch':('FILESYSTEM','QUARANTINE_MODE'),
 'quarantine must be empty':('FILESYSTEM','QUARANTINE_EMPTY'),
 'quota response cleanup failed':('CLEANUP','QUOTA_RESPONSE_CLEANUP'),
 'metadata response cleanup failed':('CLEANUP','METADATA_RESPONSE_CLEANUP'),
 'metadata error-response cleanup failed':('CLEANUP','METADATA_ERROR_CLEANUP'),
 'owned PRODUCTION90 quarantine cleanup failed':('CLEANUP','QUARANTINE_CLEANUP'),
 'one-CPU affinity required from integrated driver':('ENVELOPE','AFFINITY_REJECTED'),
 'acquisition CLI requires fresh isolated Python -I -S -B':('ENVELOPE','INTERPRETER_FLAGS'),
 'PRODUCTION90 fixed specification changed':('SOURCE','SPEC_PIN_MISMATCH'),
 'fixed historical acquisition pins changed':('SOURCE','HISTORICAL_PINS_MISMATCH'),
 'terminal run/job snapshots changed between batch boundaries':('IDENTITY','TERMINAL_SNAPSHOT_CHANGED'),
 'duplicate terminal job IDs':('IDENTITY','DUPLICATE_TERMINAL_JOB'),
 'PRODUCTION90 authenticated metadata changed':('IDENTITY','STAGE_METADATA_CHANGED'),
 'PRODUCTION90 prepare metadata changed':('IDENTITY','PREPARE_METADATA_CHANGED'),
 'PRODUCTION90 global raw ledger mismatch':('CAPACITY','GLOBAL_RAW_LEDGER'),
 'fixed global48 ledger reconciliation failed':('CAPACITY','HISTORICAL_GLOBAL_LEDGER'),
 'ZIP size/digest mismatch':('PAYLOAD','ZIP_SIZE_DIGEST'),
 'native tar bytes/hash mismatch':('PAYLOAD','NATIVE_TAR_PIN'),
 'actual native receipt hash mismatch':('PAYLOAD','NATIVE_RECEIPT_PIN'),
}
DIAGNOSTIC_GENERIC = {
 'HTTP':('HTTP','HTTP_STATUS_REJECTED'),
 'TIMEOUT':('NETWORK','NETWORK_TIMEOUT'),
 'DNS':('NETWORK','NETWORK_DNS'),
 'NETWORK':('NETWORK','NETWORK_FAILURE'),
 'MEMORY':('CAPACITY','MEMORY_FAILURE'),
 'DISK':('CAPACITY','DISK_FULL'),
 'FD':('CAPACITY','FILE_DESCRIPTORS'),
 'PERMISSION':('FILESYSTEM','FILESYSTEM_PERMISSION'),
 'OS':('FILESYSTEM','OS_FAILURE'),
 'UNKNOWN':('REJECTION','UNCLASSIFIED_REJECTION'),
}
_diagnostic_phase = 'bootstrap'
_diagnostic_last = None
_diagnostic_http_status = None
_diagnostic_quota = None

def _diagnostic_mark(phase):
    global _diagnostic_phase, _diagnostic_last, _diagnostic_http_status, _diagnostic_quota
    if phase not in DIAGNOSTIC_PHASES: raise RuntimeError('invalid fixed diagnostic phase')
    _diagnostic_phase = phase
    _diagnostic_last = None
    _diagnostic_http_status = None
    _diagnostic_quota = None

def _diagnostic_classify(error):
    # BaseException's own storage avoids invoking a hostile __str__/repr/property.
    args = BaseException.args.__get__(error)
    if type(args) is tuple and len(args) == 1 and type(args[0]) is str:
        selected = DIAGNOSTIC_MESSAGES.get(args[0])
        if selected is not None: return selected
    if isinstance(error, urllib.error.HTTPError): return DIAGNOSTIC_GENERIC['HTTP']
    if isinstance(error, TimeoutError): return DIAGNOSTIC_GENERIC['TIMEOUT']
    if isinstance(error, socket.gaierror): return DIAGNOSTIC_GENERIC['DNS']
    if isinstance(error, urllib.error.URLError):
        cause = error.reason
        if isinstance(cause, socket.gaierror): return DIAGNOSTIC_GENERIC['DNS']
        if isinstance(cause, TimeoutError): return DIAGNOSTIC_GENERIC['TIMEOUT']
        return DIAGNOSTIC_GENERIC['NETWORK']
    if isinstance(error, MemoryError): return DIAGNOSTIC_GENERIC['MEMORY']
    if isinstance(error, OSError):
        number = error.errno
        if type(number) is int:
            if number == 28: return DIAGNOSTIC_GENERIC['DISK']
            if number in (23,24): return DIAGNOSTIC_GENERIC['FD']
            if number in (1,13): return DIAGNOSTIC_GENERIC['PERMISSION']
        return DIAGNOSTIC_GENERIC['OS']
    return DIAGNOSTIC_GENERIC['UNKNOWN']

def _diagnostic_http(error):
    global _diagnostic_http_status
    if isinstance(error, urllib.error.HTTPError):
        code = error.code
        if type(code) is int and 100 <= code <= 599: _diagnostic_http_status = code

def _diagnostic_record(error):
    selected = _diagnostic_classify(error)
    if selected == DIAGNOSTIC_GENERIC['UNKNOWN'] and _diagnostic_last is not None:
        selected = _diagnostic_last
    _diagnostic_http(error)
    return {'schema':'clean-transport-failure-v2','phase':_diagnostic_phase,
            'category':selected[0],'reason_code':selected[1],
            'http_status':_diagnostic_http_status, 'quota':copy.deepcopy(_diagnostic_quota)}

def _diagnostic_emit(error):
    record = _diagnostic_record(error)
    line = DIAGNOSTIC_PREFIX + json.dumps(record,sort_keys=True,separators=(',',':')) + '\n'
    if len(line.encode('ascii')) > 1024: raise RuntimeError('fixed diagnostic bound')
    sys.stderr.write(line)


def disk_headroom(root, additional_bytes, *, new_files):
    """Actual filesystem allocation + metadata/inode reserve, not logical bytes alone."""
    f.need(type(additional_bytes) is int and additional_bytes >= 0 and
           type(new_files) is int and new_files > 0, 'invalid disk reservation')
    root = Path(root)
    f.no_symlink_path(root)
    v = os.statvfs(root)
    block = max(4096, v.f_frsize)
    required = ((additional_bytes + block - 1) // block) * block
    required += new_files * block + METADATA_RESERVE + MIN_FREE
    f.need(v.f_bavail * v.f_frsize >= required, 'insufficient actual free disk including allocation/metadata reserve')
    f.need(v.f_favail >= new_files + INODE_RESERVE, 'insufficient actual free inodes')
    return {'required_bytes': required, 'free_bytes': v.f_bavail * v.f_frsize,
            'required_inodes': new_files + INODE_RESERVE, 'free_inodes': v.f_favail,
            'allocation_unit': block}

def owned_new_root(path):
    path = Path(path)
    f.need(path.is_absolute() and path == path.resolve(), 'quarantine must be a canonical absolute path')
    f.no_symlink_path(path)
    f.need(not path.exists() and path.parent.is_dir(), 'quarantine must be fresh with an existing parent')
    f.need(path.parent.stat().st_uid == os.getuid(), 'quarantine parent must be owned by this user')
    disk_headroom(path.parent, 0, new_files=8)
    path.mkdir(mode=0o700)
    f.need(path.stat().st_uid == os.getuid() and stat.S_IMODE(path.stat().st_mode) == 0o700,
           'quarantine ownership/mode mismatch')
    return path

def copy_native_receipt(transport, wrapper):
    """Copy exact receipt bytes only; inspect strict USTAR headers without extracting objects.

    Semantic receipt/module/dependency validation remains entirely with the native
    adapter. This narrow reader rejects extensions/links/duplicate/traversal names
    and invalid padding rather than interpreting alternate archive formats.
    """
    path = Path(wrapper['archive_path'])
    destination = path.parent / 'receipt.json'
    descriptor = wrapper['native_descriptor']
    names, total, receipt_hash = set(), 0, None
    size = path.stat().st_size
    f.need(size % tarfile.RECORDSIZE == 0, 'native USTAR record size mismatch')
    with path.open('rb') as archive:
        while True:
            transport._check_age()
            header = archive.read(512)
            f.need(len(header) == 512, 'truncated USTAR header')
            if header == b'\0' * 512:
                remaining = size - archive.tell()
                f.need(remaining >= 512, 'missing USTAR end records')
                while remaining:
                    transport._check_age()
                    block = archive.read(min(1024**2, remaining))
                    f.need(block and not any(block), 'nonzero/truncated native USTAR end padding')
                    remaining -= len(block)
                break
            f.need(header[257:265] == b'ustar\x0000', 'native USTAR format required')
            try:
                member = tarfile.TarInfo.frombuf(header, 'utf-8', 'strict')
            except (tarfile.TarError, UnicodeError, ValueError):
                raise f.Rejected('invalid native USTAR header') from None
            name = f.safe_rel(member.name)
            f.need(member.isreg() and name not in names and not member.pax_headers,
                   'duplicate/nonregular native tar member')
            names.add(name)
            total += member.size
            f.need(0 <= member.size and len(names) <= 100000 and total <= ot.MAX_ARTIFACT_BYTES,
                   'native tar member count/byte bound')
            padded = ((member.size + 511) // 512) * 512
            f.need(archive.tell() + padded + 1024 <= size, 'native tar member beyond archive')
            if name == 'receipt.json':
                f.need(member.size > 0 and receipt_hash is None, 'missing/duplicate raw native receipt')
                disk_headroom(transport.root, member.size, new_files=2)
                h, remaining = hashlib.sha256(), member.size
                with destination.open('xb') as out:
                    while remaining:
                        transport._check_age()
                        block = archive.read(min(1024**2, remaining))
                        f.need(bool(block), 'truncated native receipt')
                        remaining -= len(block)
                        h.update(block)
                        out.write(block)
                    out.flush()
                    os.fsync(out.fileno())
                receipt_hash = h.hexdigest()
                padding = archive.read(padded - member.size)
                f.need(not any(padding), 'nonzero native receipt padding')
            else:
                archive.seek(padded, 1)
    f.need(receipt_hash == descriptor['receipt_sha256'], 'actual native receipt hash mismatch')
    f.need(f.file_sha(path) == descriptor['archive_sha256'], 'native archive changed during receipt copy')
    return destination

class QuotaPacedOpener:
    """Pace the same opener; never transfer, redirect, retry or parse body bytes.

    The frozen metadata call has already started its 60-second attempt and
    180-second aggregate guards before invoking open(). All pacing is charged
    inside those unchanged guards. Storage hops carry no token/quota authority.
    """
    MIN_INTERVAL = 3.7
    RESET_SAFETY = 2.0
    NETWORK_RESERVE = 1.0
    LIMIT = 1000  # Fixed conservative local ceiling, even for larger server quotas.
    SERVER_LIMITS = (1000, 5000, 15000)  # Documented limits; 5000 observed in this exact job.
    HEADER_NAMES = ('X-RateLimit-Limit', 'X-RateLimit-Remaining',
                    'X-RateLimit-Used', 'X-RateLimit-Reset',
                    'X-RateLimit-Resource', 'Date')

    def __init__(self, transport, opener):
        self.transport, self.opener = transport, opener
        self.last_clock = self.last_start = None
        self.reset_epoch = self.reset_monotonic = self.server_date = None
        self.remote_remaining = None
        self.local_remaining = self.LIMIT  # One-shot request ceiling; no header can replenish it.

    def _clock(self):
        value = time.monotonic()
        f.need(type(value) in (int,float) and math.isfinite(value) and
               (self.last_clock is None or value >= self.last_clock),
               'invalid quota monotonic clock')
        self.last_clock = value
        return value

    @staticmethod
    def _close_rejected(response):
        try: response.close()
        except Exception: raise f.Rejected('quota response cleanup failed') from None

    @classmethod
    def _headers(cls, response):
        global _diagnostic_quota
        _diagnostic_quota = None
        headers = response.headers
        f.need(callable(getattr(headers, 'get_all', None)), 'quota headers unavailable')
        values = {}
        for name in cls.HEADER_NAMES:
            rows = headers.get_all(name)
            f.need(type(rows) is list and len(rows) == 1 and type(rows[0]) is str and
                   0 < len(rows[0]) <= 64 and not any(ord(c) < 32 or ord(c) == 127 for c in rows[0]),
                   'quota header missing, duplicated or malformed')
            values[name] = rows[0]
        for name in cls.HEADER_NAMES[:4]:
            f.need(re.fullmatch(r'0|[1-9][0-9]{0,9}', values[name]) is not None,
                   'invalid numeric quota header')
            values[name] = int(values[name])
        limit, remaining, used, reset = (values[k] for k in cls.HEADER_NAMES[:4])
        _diagnostic_quota = {'limit':limit, 'remaining':remaining, 'used':used, 'reset':reset,
                             'resource':'CORE' if values['X-RateLimit-Resource'] == 'core' else 'OTHER'}
        f.need(limit in cls.SERVER_LIMITS, 'unexpected authenticated quota limit')
        f.need(0 <= remaining < limit, 'quota remaining outside limit')
        f.need(0 <= used <= limit, 'quota used outside limit')
        f.need(used + remaining == limit, 'quota used and remaining conflict')
        f.need(values['X-RateLimit-Resource'] == 'core', 'unexpected authenticated quota resource')
        try:
            date = datetime.strptime(values['Date'], '%a, %d %b %Y %H:%M:%S GMT').replace(tzinfo=timezone.utc)
            f.need(date.strftime('%a, %d %b %Y %H:%M:%S GMT') == values['Date'], 'invalid quota Date header')
        except (ValueError, OverflowError):
            raise f.Rejected('invalid quota Date header') from None
        epoch = int(date.timestamp())
        f.need(reset > 0 and reset - epoch <= 3600, 'quota reset outside bounded server window')
        return min(remaining, cls.LIMIT), reset, epoch

    def _observe(self, response):
        try:
            remaining, reset, date = self._headers(response)
            f.need(remaining > 0, 'authenticated core quota exhausted; no further request')
            now = self._clock(); self.transport._check_age()
            reset_at = now + max(0, reset - date) + self.RESET_SAFETY
            # Regional Date/reset values do not define a globally ordered window.
            # Charge every attempt locally and never refund a slot, even across hours.
            remaining = min(remaining, self.local_remaining)
            if self.reset_monotonic is not None:
                reset_at = max(reset_at, self.reset_monotonic)
            self.remote_remaining = remaining
            self.local_remaining = remaining
            self.reset_epoch, self.reset_monotonic, self.server_date = reset, reset_at, date
        except f.Rejected:
            raise
        except (AttributeError, TypeError, ValueError, OverflowError):
            raise f.Rejected('invalid authenticated quota metadata') from None

    def _pace(self, timeout):
        f.need(type(timeout) in (int,float) and math.isfinite(timeout) and timeout > 0,
               'invalid original request timeout')
        now = self._clock(); self.transport._check_age()
        # Round outward additions/subtractions toward less available budget.
        # Exact-rational elapsed + returned timeout cannot exceed input timeout.
        deadline = min(math.nextafter(now + timeout, -math.inf), self.transport.deadline_monotonic,
                       self.transport.age_deadline_monotonic)
        due = now if self.last_start is None else max(now, math.nextafter(self.last_start + self.MIN_INTERVAL, math.inf))
        f.need(self.local_remaining > 0, 'authenticated core quota exhausted; no further request')
        if self.reset_monotonic is not None:
            until_reset = max(0.0, self.reset_monotonic - now)
            # Leave enough time for every remaining slot, without probing an
            # exhausted bucket or granting itself any new quota.
            f.need(self.local_remaining > 0, 'authenticated core quota exhausted; no further request')
            interval = math.nextafter(until_reset / self.local_remaining, math.inf)
            due = max(due, math.nextafter(now + interval, math.inf))
        f.need(due + self.NETWORK_RESERVE < deadline,
               'quota pacing cannot fit the unchanged request deadline')
        # Sleep only toward one fixed target. Never recreate attempt/age budgets.
        while now < due:
            self.transport._check_age()
            deadline = min(deadline, self.transport.deadline_monotonic, self.transport.age_deadline_monotonic)
            f.need(due + self.NETWORK_RESERVE < deadline, 'quota wait would exceed tightened deadline')
            delay = min(1.0, due - now)
            time.sleep(delay)
            observed = self._clock()
            f.need(observed > now, 'quota sleep made no monotonic progress')
            now = observed; self.transport._check_age()
            f.need(now + self.NETWORK_RESERVE < deadline, 'quota pacing request deadline exceeded')
        self.transport._check_age()
        self.last_start = self._clock()
        self.local_remaining -= 1
        deadline = min(deadline, self.transport.deadline_monotonic, self.transport.age_deadline_monotonic)
        left = min(timeout, math.nextafter(deadline - self.last_start, -math.inf))
        f.need(left > self.NETWORK_RESERVE, 'quota pacing exhausted original request timeout')
        return left

    def open(self, request, timeout):
        global _diagnostic_last, _diagnostic_http_status, _diagnostic_quota
        _diagnostic_last = None
        _diagnostic_http_status = None
        _diagnostic_quota = None
        try:
            result = self._open_observed(request, timeout)
        except BaseException as error:
            _diagnostic_http(error)
            _diagnostic_last = _diagnostic_classify(error)
            raise
        _diagnostic_last = None
        _diagnostic_http_status = None
        _diagnostic_quota = None
        return result

    def _open_observed(self, request, timeout):
        # Recheck authority at the adapter boundary; never infer it from headers.
        self.transport._safe_redirect(request.full_url)
        parsed = urllib.parse.urlsplit(request.full_url)
        authorization = request.get_header('Authorization')
        if parsed.hostname != 'api.github.com':
            f.need(authorization is None, 'credentials on a storage request forbidden')
            return self.opener.open(request, timeout=timeout)
        f.need(request.get_method() == 'GET' and
               request.full_url.startswith(ot.API + '/repos/' + ot.REPOSITORY + '/') and
               authorization == 'Bearer ' + self.transport.current.token,
               'quota source must be the authenticated approved repository')
        left = self._pace(timeout)
        try:
            response = self.opener.open(request, timeout=left)
        except urllib.error.HTTPError as error:
            _diagnostic_http(error)
            if error.code in (403,429):
                self._close_rejected(error)
                raise f.Rejected('authenticated API quota or authorization failure; no retry') from None
            try: self._observe(error)
            except Exception:
                self._close_rejected(error)
                raise
            raise  # Frozen status/redirect/retry policy remains the sole policy.
        try:
            self._observe(response)
        except Exception:
            self._close_rejected(response)
            raise
        return response

FIXED_WORKFLOW=dict(p.CURRENT_WORKFLOW)
class CleanTransport(base.OriginTransport,ct.Transport):
    def __init__(self,*,token,root,budget,now=None,opener=None):
        f.need(os.environ.get('GITHUB_ACTIONS')=='true' and os.environ.get('GITHUB_REPOSITORY')==ct.REPOSITORY,'not the reviewed GitHub repository/action context')
        self.run_id=os.environ.get('GITHUB_RUN_ID','');self.attempt=os.environ.get('GITHUB_RUN_ATTEMPT','');self.commit=os.environ.get('GITHUB_SHA','')
        f.need(self.run_id.isdigit() and self.attempt=='1' and f.COMMIT.fullmatch(self.commit),'invalid clean workflow identity')
        f.need(type(token) is str and bool(token) and not any(ord(c)<33 or ord(c)==127 for c in token),'ephemeral read-only Actions token missing/invalid')
        self.token=token;self.current=self;self.budget=budget;self.root=owned_new_root(root)
        self.contexts={};self.deadline_monotonic=float(budget.deadline);self.age_deadline_monotonic=self.deadline_monotonic
        self.raw_bytes=0;self._prepared={};self._source_verified=set();self._active_pin=None;self._last_wall=None
        self.now=now or (lambda:datetime.now(timezone.utc))
        self.opener=QuotaPacedOpener(self,opener if opener is not None else urllib.request.build_opener(ct.NoRedirect()))
        self.run=self.get(f'/repos/{ct.REPOSITORY}/actions/runs/{self.run_id}')
        f.need(str(self.run['id'])==self.run_id and self.run['head_sha']==self.commit and str(self.run['run_attempt'])==self.attempt and self.run['event']=='push','trusted workflow run mismatch')
        self._jobs=None;self._artifacts=None;self._check_age()

    def bind(self,*,identity,workflow,plan,consumer_roles,consumer_role,github_job):
        f.need(not self.contexts,'clean context already bound')
        p.validate_identity(identity,identity['contract_sha256'],self.commit);p.validate_workflow(workflow,plan)
        f.need(identity['run_id']==self.run_id and identity['run_attempt']==self.attempt and identity['run_started_at']==self.run['created_at'],'clean bootstrap identity mismatch')
        self.stages={s['stage_id']:s for s in plan['stages']}
        expected_roles=set(workflow['roles'])
        f.need(type(consumer_roles) is dict and set(consumer_roles)==expected_roles|{'verdict'},'clean consumer role coverage changed')
        for role,binding in consumer_roles.items():
            base.exact_keys(binding,{'producer_job','job_name','verifier_step'},'consumer role')
            expected=({k:workflow['roles'][role][k] for k in binding} if role!='verdict' else {'producer_job':'verdict','job_name':'verdict','verifier_step':{'number':6,'name':'Run fail-closed verifier'}})
            f.need(binding==expected,'clean consumer/provider mapping changed')
        f.need(type(consumer_role) is str and consumer_role in consumer_roles and github_job==consumer_roles[consumer_role]['producer_job'],'clean invocation role/GITHUB_JOB mismatch')
        self.consumer_role=consumer_role;self.consumer_binding=copy.deepcopy(consumer_roles[consumer_role]);self.github_job=github_job
        self.contexts={base.CURRENT_ORIGIN:{'identity':copy.deepcopy(identity),'workflow':copy.deepcopy(workflow)},
            'PriorCleanOrigin':{'identity':copy.deepcopy(p.PRIOR_CLEAN_IDENTITY),'workflow':copy.deepcopy(p.PRIOR_CLEAN_WORKFLOW)}}
        self._check_age();self._run(base.CURRENT_ORIGIN)

    def _check_age(self):
        self.budget.check();now=self.now()
        f.need(type(now) is datetime and now.tzinfo is not None and (self._last_wall is None or now>=self._last_wall),'clean clock moved backward')
        self._last_wall=now
        if self.contexts:
            deadline=p.check_deadline(self.contexts[base.CURRENT_ORIGIN]['identity'],now)
            self.age_deadline_monotonic=min(self.age_deadline_monotonic,time.monotonic()+(deadline-now).total_seconds())
        self.deadline_monotonic=min(self.deadline_monotonic,self.budget.deadline)
        f.need(time.monotonic()<min(self.deadline_monotonic,self.age_deadline_monotonic),'shared acquisition wall/age deadline reached')

    def _context(self,origin):
        f.need(origin in ('PriorCleanOrigin',base.CURRENT_ORIGIN) and origin in self.contexts,'only bound clean-campaign origins permitted')
        return self.contexts[origin]

    def _selection_pin(self,origin,role):
        context=self._context(origin)
        if origin==CURRENT_ORIGIN:
            f.need(role not in p.PRIOR_STAGES,'prior-clean stage cannot be relabeled current')
            return None
        f.need(role=='prepare' or role in p.PRIOR_STAGES,'unselected prior-clean role')
        pin=copy.deepcopy(p.PRIOR_CLEAN_PREPARE_PIN if role=='prepare' else p.PRIOR_STAGE_PINS[role])
        expected={'artifact_id','producer_job_id','artifact_zip_sha256','artifact_zip_bytes','expires_at'}
        base.exact_keys(pin,expected,'prior-clean API pin')
        for key in ('artifact_id','producer_job_id','artifact_zip_bytes'):base.positive(pin[key],key)
        base.digest(pin['artifact_zip_sha256'],'prior-clean ZIP hash');base.timestamp(pin['expires_at'])
        pin['artifact_name']=f"hierarchy-c-{context['identity']['run_id']}-{context['identity']['run_attempt']}-{role}"
        return pin

    def _prior_run(self):
        context=self._context('PriorCleanOrigin');identity=context['identity'];workflow=context['workflow']
        run=self._json(f"/repos/{base.REPOSITORY}/actions/runs/{identity['run_id']}")
        for key in ('repository','head_repository'):
            repo=run.get(key)
            f.need(type(repo) is dict and type(repo.get('id')) is int and repo['id']==base.REPOSITORY_ID and
                   repo.get('full_name')==base.REPOSITORY,'prior-clean repository mismatch')
        f.need(type(run.get('id')) is int and str(run['id'])==identity['run_id'] and
               type(run.get('run_attempt')) is int and str(run['run_attempt'])==identity['run_attempt'] and
               run.get('head_sha')==identity['pipeline_commit'] and run.get('event')=='push' and
               all(run.get(k)==workflow[k] for k in ('head_branch','path','name')) and
               type(run.get('workflow_id')) is int and run['workflow_id']==workflow['workflow_id'] and
               run.get('created_at')==identity['run_started_at'],'prior-clean run/workflow/attempt identity mismatch')
        f.need(all(run.get(k)==v for k,v in p.PRIOR_CLEAN_TERMINAL.items()),'prior-clean terminal snapshot changed')
        f.need(base.timestamp(run['created_at'])<=base.timestamp(run['updated_at'])<=self.now(),'prior-clean terminal timestamps invalid')
        self._check_age();return run

    @staticmethod
    def _metadata(origin,run,job,artifact,binding):
        result=base.OriginTransport._metadata(origin,run,job,artifact,binding)
        if origin=='PriorCleanOrigin':result['run'].update(status=run['status'],conclusion=run['conclusion'])
        return result

    def authenticate_prepare(self,origin,destination,max_bytes=32*1024**2):
        result=super().authenticate_prepare(origin,destination,max_bytes)
        if origin=='PriorCleanOrigin':
            f.need(result['identity_sha256']==f.sha(f.json_bytes(p.PRIOR_CLEAN_IDENTITY)),'prior-clean raw prepare identity hash changed')
        self._check_age();return result

    def _current_run_observation(self,budget,observation):
        f.need(type(observation) is int and 1<=observation<=base.MAX_CURRENT_STATUS_POLLS,
               'current run status poll count exhausted')
        context=self._context(base.CURRENT_ORIGIN);identity=context['identity'];workflow=context['workflow']
        run,poll=self._json(f'/repos/{base.REPOSITORY}/actions/runs/{identity["run_id"]}',
                            budget=budget,poll_headers=True)
        try:
            with base._metadata_wall_limit(self._metadata_remaining(budget),deadline=budget['deadline']):
                for key in ('repository','head_repository'):
                    repo=run.get(key)
                    f.need(type(repo) is dict and type(repo.get('id')) is int and repo['id']==base.REPOSITORY_ID and
                           repo.get('full_name')==base.REPOSITORY,'run repository/head-repository mismatch')
                f.need(type(run.get('id')) is int and str(run['id'])==identity['run_id'] and
                       type(run.get('run_attempt')) is int and str(run['run_attempt'])==identity['run_attempt'] and
                       run.get('head_sha')==identity['pipeline_commit'] and run.get('event')=='push' and
                       run.get('head_branch')==workflow['head_branch'] and
                       type(run.get('workflow_id')) is int and run['workflow_id']==workflow['workflow_id'] and
                       run.get('path')==workflow['path'] and run.get('name')==workflow['name'],
                       'run/workflow identity mismatch or rerun')
                f.need(run.get('created_at')==identity['run_started_at'],'trusted run start mismatch')
                f.need(base.timestamp(run['created_at'])<=base.timestamp(run.get('updated_at'))<=self.now(),
                       'inconsistent run timestamps')
                f.need('status' in run and 'conclusion' in run,'current run status/conclusion missing')
                accepted=((run['status']=='in_progress' and run['conclusion'] is None) or
                          (run['status']=='completed' and run['conclusion']=='success'))
                f.need(accepted or (type(run['status']) is str and run['status'] in base.WAITABLE_CURRENT_STATUSES and
                                   run['conclusion'] is None),'current run is not active/successful; terminal or invalid state')
                # This post-validation record preserves the actual API status.
                record={k:run[k] for k in ('id','run_attempt','workflow_id','head_sha','status','conclusion','created_at','updated_at')}
                record.update(event='current_origin_run_status_observation',observation=observation,identity_validation='passed')
                print(json.dumps(record,sort_keys=True,separators=(',',':')),flush=True)
                self._metadata_remaining(budget)
                return run,poll,accepted,record
        except (base._MetadataWallTimeout,base._MetadataHardTimeout):
            raise f.Rejected('current run status diagnostic/validation deadline exceeded') from None

    def _active_consumer(self,budget,job_id=None):
        context=self._context(base.CURRENT_ORIGIN);identity=context['identity'];workflow=context['workflow']
        binding=self.consumer_binding
        if job_id is None:
            data=self._json(f'/repos/{base.REPOSITORY}/actions/runs/{identity["run_id"]}/attempts/{identity["run_attempt"]}/jobs?per_page=100&page=1',budget=budget)
            try:
                with base._metadata_wall_limit(self._metadata_remaining(budget),deadline=budget['deadline']):
                    rows=data.get('jobs');count=data.get('total_count')
                    f.need(type(rows) is list and type(count) is int and count==len(rows) and 0<count<=100 and
                           all(type(row) is dict for row in rows),'invalid bounded current consumer jobs')
                    ids=[row.get('id') for row in rows]
                    f.need(all(type(n) is int and n>0 for n in ids) and len(set(ids))==len(ids),'duplicate/invalid current job IDs')
                    matches=[row for row in rows if row.get('name')==binding['job_name']]
                    f.need(len(matches)==1,'current consumer job missing or ambiguous')
                    job=matches[0]
                    self._metadata_remaining(budget)
            except (base._MetadataWallTimeout,base._MetadataHardTimeout):
                raise f.Rejected('current consumer list deadline exceeded') from None
        else:
            base.positive(job_id,'current consumer job ID')
            job=self._json(f'/repos/{base.REPOSITORY}/actions/jobs/{job_id}',budget=budget)
        try:
            with base._metadata_wall_limit(self._metadata_remaining(budget),deadline=budget['deadline']):
                f.need(type(job.get('id')) is int and job['id']>0 and (job_id is None or job['id']==job_id) and
                       type(job.get('run_id')) is int and str(job['run_id'])==identity['run_id'] and
                       type(job.get('run_attempt')) is int and str(job['run_attempt'])==identity['run_attempt'] and
                       job.get('head_sha')==identity['pipeline_commit'] and job.get('head_branch')==workflow['head_branch'] and
                       job.get('workflow_name')==workflow['name'] and job.get('name')==binding['job_name'],
                       'current consumer job identity mismatch')
                f.need(job.get('status')=='in_progress' and 'conclusion' in job and job['conclusion'] is None and
                       'completed_at' in job and job['completed_at'] is None,'current consumer job is not active')
                created=base.timestamp(job.get('created_at'));started=base.timestamp(job.get('started_at'))
                f.need(base.timestamp(identity['run_started_at'])<=created<=started<=self.now(),'current consumer job timestamps inconsistent')
                steps=job.get('steps')
                f.need(type(steps) is list and 0<len(steps)<=100 and all(type(step) is dict for step in steps),
                       'invalid bounded current consumer steps')
                numbers=[step.get('number') for step in steps];names=[step.get('name') for step in steps]
                f.need(all(type(n) is int and n>0 for n in numbers) and len(set(numbers))==len(numbers) and
                       all(type(n) is str and n for n in names) and len(set(names))==len(names),
                       'ambiguous current consumer steps')
                matches=[step for step in steps if step.get('number')==binding['verifier_step']['number'] or
                         step.get('name')==binding['verifier_step']['name']]
                f.need(len(matches)==1,'current consumer verifier step missing or ambiguous')
                step=matches[0]
                f.need(step['number']==binding['verifier_step']['number'] and step['name']==binding['verifier_step']['name'] and
                       step.get('status')=='in_progress' and 'conclusion' in step and step['conclusion'] is None and
                       'completed_at' in step and step['completed_at'] is None,'current consumer verifier step is not active')
                f.need(started<=base.timestamp(step.get('started_at'))<=self.now(),'current verifier timestamp inconsistent')
                result={k:job[k] for k in ('id','run_id','run_attempt','head_sha','head_branch','workflow_name','name',
                                         'status','conclusion','created_at','started_at','completed_at')}
                result['step']={k:step[k] for k in ('number','name','status','conclusion','started_at','completed_at')}
                self._metadata_remaining(budget)
                return result
        except (base._MetadataWallTimeout,base._MetadataHardTimeout):
            raise f.Rejected('current consumer validation deadline exceeded') from None

    def _current_status_wait(self,budget,poll,observation):
        delay=base.CURRENT_STATUS_BACKOFF_SECONDS[observation-1]
        if poll is not None:
            f.need(type(poll) is str and base.re.fullmatch(r'[0-9]{1,4}',poll),'invalid current run X-Poll-Interval')
            delay=max(delay,int(poll))
        remaining=self._metadata_remaining(budget)
        f.need(delay<remaining,'current run status wait exceeds aggregate/origin deadline')
        try:
            with base._metadata_wall_limit(remaining,deadline=budget['deadline']):base.time.sleep(delay)
        except (base._MetadataWallTimeout,base._MetadataHardTimeout):
            raise f.Rejected('current run status wait deadline exceeded') from None
        self._metadata_remaining(budget)

    def _run(self,origin):
        self._context(origin)
        if origin=='PriorCleanOrigin':return self._prior_run()
        started=base.time.monotonic()
        budget={'started':started,'deadline':started+base.MAX_CURRENT_STATUS_SECONDS}
        observation=0
        while observation<base.MAX_CURRENT_STATUS_POLLS:
            observation+=1
            run,poll,accepted,first_run=self._current_run_observation(budget,observation)
            if accepted:
                self._metadata_remaining(budget)
                return run
            if run['status']=='queued':
                f.need(observation<base.MAX_CURRENT_STATUS_POLLS,'current run status poll count exhausted')
                first=self._active_consumer(budget)
                self._current_status_wait(budget,poll,observation)
                second=self._active_consumer(budget,first['id'])
                f.need(first==second,'current active consumer changed between authenticated reads')
                observation+=1
                run,poll,accepted,last_run=self._current_run_observation(budget,observation)
                f.need(base.timestamp(first_run['updated_at'])<=base.timestamp(last_run['updated_at']),
                       'current run update timestamp moved backward')
                if accepted:
                    self._metadata_remaining(budget)
                    return run
                if run['status']=='queued':
                    # Separate live eligibility witness; native receipt metadata
                    # remains byte-identical and still requires successful producers.
                    witness={'event':'current_queued_active_consumer_witness','schema':'current-consumer-v1',
                        'acceptance':'queued_run_with_exact_active_consumer','identity':self.contexts[origin]['identity'],
                        'consumer_role':self.consumer_role,'github_job':self.github_job,'binding':self.consumer_binding,
                        'run_observations':[first_run,last_run],'consumer_observations':[first,second]}
                    try:
                        with base._metadata_wall_limit(self._metadata_remaining(budget),deadline=budget['deadline']):
                            encoded=json.dumps(witness,sort_keys=True,separators=(',',':'))
                            f.need(len(encoded.encode('utf-8'))<=16384,'current consumer witness exceeds bound')
                            print(encoded,flush=True)
                            self._metadata_remaining(budget)
                            return run
                    except (base._MetadataWallTimeout,base._MetadataHardTimeout):
                        raise f.Rejected('current consumer witness deadline exceeded') from None
            f.need(observation<base.MAX_CURRENT_STATUS_POLLS,'current run status poll count exhausted')
            self._current_status_wait(budget,poll,observation)
        raise f.Rejected('current run status poll bound exceeded')

    def _open_zip(self, aid):
        request = self._request(f'/repos/{ot.REPOSITORY}/actions/artifacts/{aid}/zip')
        for redirects in range(ot.MAX_REDIRECTS + 1):
            self._check_age()
            try:
                response = self.opener.open(request, timeout=60)
            except urllib.error.HTTPError as error:
                code = error.code
                location = error.headers.get('Location', '') if error.headers is not None else ''
                try:
                    error.close()
                except Exception:
                    raise f.Rejected('artifact redirect response cleanup failed') from None
                f.need(code in (301, 302, 303, 307, 308), 'artifact GET failed')
                f.need(redirects < ot.MAX_REDIRECTS, 'artifact redirect bound exceeded')
                # Validate raw Location before urljoin can discard controls.
                f.need(type(location) is str and location and not any(ord(c) < 33 or ord(c) == 127 for c in location)
                       and '#' not in location and '\\' not in location, 'unsafe artifact redirect')
                url = urllib.parse.urljoin(request.full_url, location)
                self._safe_redirect(url)
                request = self._request(url, authenticated=False)
            except (OSError, ValueError, http.client.HTTPException):
                raise f.Rejected('artifact request failed; URL suppressed') from None
            else:
                if response.getcode() != 200:
                    try:
                        response.close()
                    except Exception:
                        raise f.Rejected('artifact status response cleanup failed') from None
                    raise f.Rejected('artifact response must be 200')
                return response
        raise f.Rejected('artifact redirect bound exceeded')

    def _check_destination(self, destination):
        destination = Path(destination)
        f.no_symlink_path(destination)
        f.need(destination.parent == self.root and not destination.exists(), 'artifact destination outside fresh owned quarantine')
        return destination

    def _extract(self, artifact, destination, members, max_bytes):
        destination = self._check_destination(destination)
        pin = self._active_pin
        f.need(pin is not None and artifact['id'] == pin['artifact_id'], 'download must have authenticated artifact pin')
        self._check_age()
        prepare = members == ['identity.json', 'inventory.json']
        final = members == ['payload.tar', 'upload-candidate.json']
        maximum_raw = MAX_PREPARE if prepare else (ot.MAX_FINAL_BYTES if final else min(ot.MAX_ARTIFACT_BYTES, RAW_CAP - self.raw_bytes))
        f.need(prepare or final or (maximum_raw > 0 and self.raw_bytes + maximum_raw <= RAW_CAP),
               'clean-run raw cap cannot fit next pinned archive')
        disk_headroom(self.root, artifact['size_in_bytes'] + maximum_raw + ot.MAX_DESCRIPTOR_BYTES, new_files=6)
        destination.mkdir(mode=0o700)
        archive = destination / 'download.zip'
        response = None
        try:
            remaining = min(900, self.deadline_monotonic - time.monotonic(),
                            self.age_deadline_monotonic - time.monotonic())
            with ot._metadata_wall_limit(remaining):
                response = self._open_zip(artifact['id'])
                count, h = 0, hashlib.sha256()
                try:
                    with archive.open('xb') as handle:
                        while True:
                            self._check_age()
                            f.need(self.now() < ot.timestamp(artifact['expires_at']), 'artifact expired during transfer')
                            block = response.read(1024**2)
                            f.need(type(block) is bytes, 'artifact transfer returned non-byte data')
                            if block == b'':
                                break  # EOF is required even after expected length.
                            count += len(block)
                            f.need(count <= max_bytes and count <= artifact['size_in_bytes'], 'ZIP transfer size exceeded')
                            h.update(block)
                            handle.write(block)
                        handle.flush()
                        os.fsync(handle.fileno())
                finally:
                    closing, response = response, None
                    if not isinstance(sys.exc_info()[1], ot._MetadataHardTimeout):
                        try:
                            closing.close()
                        except Exception:
                            raise f.Rejected('artifact response cleanup failed') from None
                f.need(count == artifact['size_in_bytes'] and h.hexdigest() == artifact['digest'][7:], 'ZIP size/digest mismatch')
            with zipfile.ZipFile(archive) as zipped:
                infos = zipped.infolist()
                f.need(len(infos) == len(members) and {i.filename for i in infos} == set(members), 'ZIP exact member/duplicate mismatch')
                total = 0
                raw_size = 0
                for info in infos:
                    f.safe_rel(info.filename)
                    mode = info.external_attr >> 16
                    f.need(not info.is_dir() and stat.S_IFMT(mode) in (0, stat.S_IFREG) and
                           not info.flag_bits & 1 and info.compress_type in (zipfile.ZIP_STORED, zipfile.ZIP_DEFLATED), 'unsafe ZIP member')
                    total += info.file_size
                    f.need(0 <= info.file_size and total <= max_bytes, 'ZIP expansion bound')
                    if info.filename in ('identity.json', 'upload-candidate.json'):
                        f.need(info.file_size <= ot.MAX_DESCRIPTOR_BYTES, 'descriptor/identity expansion bound')
                    if info.filename == 'payload.tar':
                        f.need(0 < info.file_size <= ot.MAX_FINAL_BYTES, 'final raw archive cap exceeded')
                    if info.filename == 'delta.tar':
                        raw_size = info.file_size
                        f.need(0 < raw_size <= ot.MAX_ARTIFACT_BYTES and self.raw_bytes + raw_size <= RAW_CAP,
                               'clean-run raw archive cap exceeded')
                        f.need('archive_bytes' not in pin or raw_size == pin['archive_bytes'], 'original raw size pin changed')
                disk_headroom(self.root, total, new_files=len(infos) + 2)
                for info in infos:
                    self._check_age()
                    with zipped.open(info) as src, (destination / info.filename).open('xb') as dst:
                        copied = 0
                        while True:
                            self._check_age()
                            block = src.read(1024**2)
                            if not block:
                                break
                            copied += len(block)
                            f.need(copied <= info.file_size, 'overlong ZIP member')
                            dst.write(block)
                        f.need(copied == info.file_size, 'truncated ZIP member')
                        dst.flush()
                        os.fsync(dst.fileno())
            self._check_age()
            f.need(self.now() < ot.timestamp(artifact['expires_at']), 'artifact expired during extraction')
            archive.unlink()  # Only authenticated + fully extracted transient ZIP.
            self.raw_bytes += raw_size
            return destination
        except BaseException:
            # Scope is the exclusively-created artifact directory, never caller data.
            if response is not None:
                try:
                    response.close()
                except Exception:
                    pass
            try:
                shutil.rmtree(destination)
            except Exception:
                raise f.Rejected('owned artifact quarantine cleanup failed') from None
            raise

    def _download(self,origin,role,destination,members,max_bytes,pin):
        self._context(origin);expected=self._selection_pin(origin,role)
        f.need((pin is None or pin==expected) and self._active_pin is None,'external pin or reentrant download forbidden')
        pin=expected
        base.positive(max_bytes,'download bound')
        f.need(max_bytes <= (base.MAX_FINAL_BYTES if role in base.FINAL_ROLES else base.MAX_ARTIFACT_BYTES)+1024**2,'download bound exceeds fixed cap')
        run=self._run(origin);self._verify_workflow_source(origin)
        job,binding=self._producer(origin,role,run,pin)
        artifact=self._artifact(origin,role,run,job,pin,max_bytes)
        self._active_pin={'artifact_id':artifact['id']}
        try:destination=self._extract(artifact,destination,members,max_bytes)
        finally:self._active_pin=None
        self._run(origin)
        metadata=self._metadata(origin,run,job,artifact,binding)
        self._check_age();return destination,metadata

    def download_stage(self, origin, stage_id, destination, max_bytes, pin=None):
        context = self._context(origin)
        f.need(stage_id in self.stages and origin==p.origin_for_stage(stage_id) and pin is None,'unplanned stage, wrong origin or external pin')
        f.need(set(self._prepared) == {CURRENT_ORIGIN,'PriorCleanOrigin'}, 'both clean-campaign prepares required')
        f.need(isinstance(stage_id, str) and re.fullmatch(r'build_\d{3}', stage_id), 'invalid stage role')
        pin=self._selection_pin(origin,stage_id)
        path, metadata = self._download(origin, stage_id, destination, ['delta.tar', 'upload-candidate.json'], max_bytes, pin)
        raw = (path / 'upload-candidate.json').read_bytes()
        raw_sha = f.sha(raw)
        descriptor = f.parse_json(raw)
        f.need(type(descriptor) is dict and descriptor.get('schema') == 'fresh-stage-upload-candidate-v1' and
               descriptor.get('stage_id') == stage_id and descriptor.get('identity') == context['identity'] and
               descriptor.get('producer_job') == metadata['role']['producer_job'] and
               type(descriptor.get('retention_days')) is int and descriptor['retention_days'] == 7, 'native descriptor identity/role mismatch')
        for field in ('archive_sha256', 'receipt_sha256'):
            digest(descriptor.get(field), field)
        archive_bytes = positive(descriptor.get('archive_bytes'), 'archive_bytes')
        f.need(archive_bytes <= MAX_ARTIFACT_BYTES and archive_bytes == (path / 'delta.tar').stat().st_size and
               descriptor['archive_sha256'] == f.file_sha(path / 'delta.tar'), 'native archive digest/size mismatch')
        descriptor.update(artifact_id=metadata['artifact']['id'], producer_job_id=metadata['job']['id'],
                          producer_conclusion='success', artifact_zip_sha256=metadata['artifact']['digest'][7:])
        descriptor.pop('archive_path', None)
        # No origin, path, source normalization or extra transport fields in D(s).
        return {'origin': origin, 'native_descriptor': descriptor, 'archive_path': str(path / 'delta.tar'),
                'authenticated_metadata': metadata, 'raw_descriptor_sha256': raw_sha}

    def reauthenticate_wrapper(self, wrapper, pin=None):
        """Recheck current API facts without transferring the large payload again.

        The old selection pin remains mandatory. Current native artifact/job IDs
        are frozen to those in the already independently resolved map; the API
        must still resolve the same unique current role and those exact IDs.
        """
        fields = {'origin', 'native_descriptor', 'authenticated_metadata', 'raw_descriptor_sha256'}
        f.need(type(wrapper) is dict and (set(wrapper) == fields or set(wrapper) == fields | {'archive_path'}),
               'unknown/missing resolved wrapper fields')
        origin = wrapper['origin']
        context = self._context(origin)
        f.need(set(self._prepared) == {CURRENT_ORIGIN,'PriorCleanOrigin'}, 'both clean-campaign prepares required')
        descriptor = wrapper['native_descriptor']
        f.need(type(descriptor) is dict and descriptor.get('identity') == context['identity'], 'wrapper identity mismatch')
        stage = descriptor.get('stage_id')
        role = stage if stage is not None else descriptor.get('role')
        f.need(isinstance(role, str) and (re.fullmatch(r'build_\d{3}', role) or role in FINAL_ROLES), 'wrapper role invalid')
        f.need(stage is not None or origin == CURRENT_ORIGIN, 'old final artifacts forbidden')
        f.need(pin is None,'external wrapper pin forbidden')
        if stage is not None:f.need(origin==p.origin_for_stage(stage),'wrapper stage origin changed')
        pin=self._selection_pin(origin,role)
        run = self._run(origin)
        self._verify_workflow_source(origin)
        job, binding = self._producer(origin, role, run, pin)
        maximum = (MAX_ARTIFACT_BYTES if stage is not None else MAX_FINAL_BYTES) + 1024**2
        artifact = self._artifact(origin, role, run, job, pin, maximum)
        f.need(descriptor.get('artifact_id') == artifact['id'] and descriptor.get('producer_job_id') == job['id'] and
               descriptor.get('producer_conclusion') == 'success' and
               descriptor.get('artifact_zip_sha256') == artifact['digest'][7:], 'resolved wrapper authoritative identity changed')
        f.need(stage is None or descriptor.get('producer_job') == binding['producer_job'], 'resolved wrapper producer role changed')
        metadata = self._metadata(origin, run, job, artifact, binding)
        f.need(metadata == wrapper['authenticated_metadata'], 'resolved authenticated metadata changed')
        self._run(CURRENT_ORIGIN)
        self._check_age()
        return metadata

CURRENT_ORIGIN=base.CURRENT_ORIGIN
OLD_ORIGIN=base.OLD_ORIGIN
FINAL_ROLES=base.FINAL_ROLES
MAX_ARTIFACT_BYTES=base.MAX_ARTIFACT_BYTES
MAX_FINAL_BYTES=base.MAX_FINAL_BYTES
digest=base.digest
positive=base.positive

def current_workflow_from_run(transport, template, pipeline):
    """Resolve only the current workflow ID from the authenticated current run.

    Contract fixes path/name/branch/roles. Numeric ID and source digest are
    deliberately null until authenticated run metadata and the pinned checkout
    provide them. Original-origin mapping is never passed through this helper.
    """
    f.need(isinstance(transport,CleanTransport),'authenticated current Transport required')
    cp.keys(template,{'workflow_id','path','name','head_branch','source_sha256','roles'},'current workflow template')
    f.need(template['workflow_id'] is None and template['source_sha256'] is None,
           'current workflow ID/source must come from authenticated runtime context')
    fixed={'path':'.github/workflows/hierarchy-c-clean-recovery.yml',
           'name':'Verify hierarchy C clean recovery',
           'head_branch':'verify/hierarchy-c-clean-recovery-20261018'}
    f.need(all(template[k]==v for k,v in fixed.items()),'current workflow path/name/branch changed')
    run=transport.run
    f.need(type(run) is dict and type(run.get('id')) is int and run['id']>0 and str(run['id'])==transport.run_id and
           type(run.get('run_attempt')) is int and run['run_attempt']==1 and str(run['run_attempt'])==transport.attempt and
           run.get('head_sha')==transport.commit and run.get('event')=='push',
           'authenticated current run identity changed')
    for key in ('repository','head_repository'):
        repo=run.get(key)
        f.need(type(repo) is dict and type(repo.get('id')) is int and repo['id']==cp.REPOSITORY_ID and
               repo.get('full_name')==p.REPOSITORY,'current repository/head repository changed')
    f.need(all(run.get(k)==v for k,v in fixed.items()),'current run workflow fields changed')
    cp.integer(run.get('workflow_id'),'authenticated current workflow ID')
    mapping=dict(template);mapping['workflow_id']=run['workflow_id']
    path=Path(pipeline)/f.safe_rel(mapping['path']);f.no_symlink_path(path)
    f.need(path.is_file(),'pinned current workflow source missing')
    mapping['source_sha256']=f.file_sha(path)
    base.validate_workflow(mapping)
    return mapping
