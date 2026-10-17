"""Bounded exact-origin transport of checked conditional Lean objects.

Successful current-run producers or explicitly host-locked earlier producers are eligible.
Archives are data, never LEAN_PATH entries. Admission is a host-only copy into the
single owned-object root after every byte and receipt has been checked.
"""
from __future__ import annotations
import hashlib, io, math, os, re, shutil, stat, struct, tarfile, time, zlib
import urllib.error, urllib.parse, urllib.request, zipfile
from pathlib import Path
import fresh_stage as f

REPOSITORY = 'jconorgrogan/palomar-chair-verification'
API = 'https://api.github.com'
WORKFLOW_PATH = '.github/workflows/conditional-geometry.yml'
MAX_JOB_LOG = 16*1024**2
GIB = 1024**3
MAX_ARCHIVE = 4*GIB
MAX_OWNED = 6*GIB
MAX_EVIDENCE = 124*1024**2
MAX_METADATA = 4*1024**2
DISK_RESERVE = 1536*1024**2
ZIP_ALLOWANCE = 4*1024**2
SUFFIXES = ('.olean','.olean.private','.olean.server','.ilean','.ir.sig','.ir','.c')
SCHEMA = 'same-run-conditional-checked-objects-v1'
IDENTITY_KEYS = ('repository','run_id','run_attempt','workflow_commit')
META_KEYS = ('identity','stage_id','stage_modules','admitted_stages','contract_sha256',
             'interface_identity','producer_work','runtime_inventory_sha256','predecessor_artifacts')
ORIGIN_KEYS = ('identity','stage_id','artifact_name','artifact_id','producer_job_name','producer_job_id',
               'producer_conclusion','artifact_zip_sha256','artifact_zip_bytes','workflow_path','workflow_id',
               'producer_job_log_sha256')
LOCKED_STAGES = ('F0_common','F1_curved_existence','F2_period_hierarchy','F3_product_geometry','H4_product_geometry')


def paths(module):
    f.need(isinstance(module,str) and f.MODULE.fullmatch(module),'invalid module')
    return {module.replace('.','/')+s for s in SUFFIXES}


def regular(path):
    path=Path(path); f.no_symlink_path(path); s=path.lstat()
    f.need(stat.S_ISREG(s.st_mode) and s.st_nlink==1,'nonregular/hardlinked transport file')
    return s.st_size


def inventory(root, maximum):
    files=f.regular_tree(Path(root)); result={}; total=0
    f.need(len(files)<=40000,'transport file count bound')
    for name,p in sorted(files.items()):
        size=regular(p); total+=size
        f.need(size<=512*1024**2 and total<=maximum,'transport inventory byte bound')
        result[name]={'bytes':size,'sha256':f.file_sha(p)}
    f.exact_tree(Path(root),set(result))
    return result


def check_deadline(deadline):
    f.need(deadline is None or (type(deadline) in (int,float) and math.isfinite(deadline) and time.monotonic()<deadline),
           'absolute stage transport deadline exceeded')


def require_disk(path, needed, entries=0, directories=0):
    path=Path(path); f.no_symlink_path(path)
    while not path.exists(): path=path.parent
    vfs=os.statvfs(path); block=max(4096,vfs.f_frsize)
    allocation=needed+block*(2*entries+directories)
    f.need(type(needed) is int and needed>=0 and shutil.disk_usage(path).free>=allocation+DISK_RESERVE,
           'insufficient measured disk for transport allocation plus reserve')
    f.need(vfs.f_favail>=entries+directories+1024,'insufficient free inodes for transport plus reserve')


def _row(row):
    f.need(isinstance(row,dict) and set(row)=={'bytes','sha256'} and
           type(row['bytes']) is int and 0<=row['bytes']<=512*1024**2 and
           isinstance(row['sha256'],str) and f.SHA256.fullmatch(row['sha256']), 'invalid inventory row')


def _identity(identity):
    f.need(isinstance(identity,dict) and set(identity)==set(IDENTITY_KEYS),'invalid run identity keys')
    f.need(identity['repository']==REPOSITORY and
           all(isinstance(identity[k],str) and re.fullmatch(r'[1-9][0-9]*',identity[k]) for k in ('run_id','run_attempt')) and
           isinstance(identity['workflow_commit'],str) and f.COMMIT.fullmatch(identity['workflow_commit']), 'invalid run identity')


def validate_origin_lock(origin):
    """Validate a complete host-provided pin, not artifact-supplied provenance."""
    f.need(isinstance(origin,dict) and set(origin)==set(ORIGIN_KEYS),'origin lock keys differ')
    _identity(origin['identity']); identity=origin['identity']; stage=origin['stage_id']
    f.need(stage in LOCKED_STAGES,'unapproved locked producer stage')
    f.need(origin['producer_job_name']=='conditional '+stage and origin['producer_conclusion']=='success',
           'locked producer role/conclusion differs')
    f.need(origin['artifact_name']==f"conditional-geometry-{identity['run_id']}-{identity['run_attempt']}-{stage}-objects",
           'locked artifact name differs')
    f.need(all(type(origin[k]) is int and origin[k]>0 for k in ('artifact_id','producer_job_id','workflow_id')),
           'invalid locked producer/artifact/workflow identifier')
    f.need(type(origin['artifact_zip_bytes']) is int and 0<origin['artifact_zip_bytes']<=MAX_ARCHIVE+ZIP_ALLOWANCE,
           'invalid locked artifact size')
    f.need(all(isinstance(origin[k],str) and f.SHA256.fullmatch(origin[k]) for k in ('artifact_zip_sha256','producer_job_log_sha256')),
           'invalid locked artifact/log digest')
    f.need(origin['workflow_path']==WORKFLOW_PATH,'locked workflow path differs')


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self,*args,**kwargs): return None


class Transport:
    origin_lock=None

    def __init__(self,*,deadline=None,origin_lock=None):
        check_deadline(deadline); self.deadline=min(deadline,time.monotonic()+1800) if deadline is not None else time.monotonic()+1800
        f.need(os.environ.get('GITHUB_ACTIONS')=='true' and os.environ.get('GITHUB_REPOSITORY')==REPOSITORY,
               'not the approved repository/action context')
        self.consumer_identity={'repository':REPOSITORY,'run_id':os.environ.get('GITHUB_RUN_ID',''),
                       'run_attempt':os.environ.get('GITHUB_RUN_ATTEMPT',''),'workflow_commit':os.environ.get('GITHUB_SHA','')}
        _identity(self.consumer_identity)
        if origin_lock is not None:
            validate_origin_lock(origin_lock)
            f.need(int(origin_lock['identity']['run_id'])<int(self.consumer_identity['run_id']),'locked origin must be an earlier distinct run')
            # Copy the host pin before any remote lookup; callers cannot mutate
            # an in-progress transfer by later changing their input dictionary.
            self.origin_lock=f.parse_json(f.json_bytes(origin_lock))
        self.identity=dict(self.origin_lock['identity'] if self.origin_lock is not None else self.consumer_identity)
        _identity(self.identity); self.run_id=self.identity['run_id']; self.attempt=self.identity['run_attempt']
        self.commit=self.identity['workflow_commit']; self.token=os.environ.get('GH_TOKEN','')
        f.need(bool(self.token),'ephemeral read-only workflow token missing')
        self.opener=urllib.request.build_opener(NoRedirect()); self._jobs=None; self._artifacts=None; self._accepted_stages=set()
        workflow=self.get(f'/repos/{REPOSITORY}/actions/workflows/conditional-geometry.yml')
        f.need(workflow['path']==WORKFLOW_PATH and type(workflow['id']) is int and workflow['id']>0,
               'authenticated workflow path/id differs')
        self.workflow_id=workflow['id']
        self.authenticate_run(self.consumer_identity)
        if self.origin_lock is not None:
            f.need(self.workflow_id==self.origin_lock['workflow_id'],'locked workflow identifier differs')
            run=self.authenticate_run(self.identity)
            f.need(run.get('status')=='completed','locked producer run is not terminal')

    def authenticate_run(self,identity):
        run=self.get(f'/repos/{REPOSITORY}/actions/runs/{identity["run_id"]}')
        f.need(str(run['id'])==identity['run_id'] and run['head_sha']==identity['workflow_commit'] and
               str(run['run_attempt'])==identity['run_attempt'] and run['event']=='push' and
               run['repository']['full_name']==REPOSITORY,'authenticated workflow run identity mismatch')
        f.need(run['path']==WORKFLOW_PATH and run['workflow_id']==self.workflow_id,
               'authenticated workflow path/id differs')
        return run

    def request(self,path):
        f.need(path.startswith(f'/repos/{REPOSITORY}/actions/') and not any(x in path for x in ('..','\\','#')),'unapproved API path')
        return urllib.request.Request(API+path,headers={'Authorization':'Bearer '+self.token,
            'Accept':'application/vnd.github+json','X-GitHub-Api-Version':'2022-11-28','User-Agent':'conditional-checked-stage-transport'})

    def response(self,path,*,signed_redirect=False):
        check_deadline(self.deadline)
        timeout=min(60,max(0.001,self.deadline-time.monotonic())) if self.deadline is not None else 60
        try: return self.opener.open(self.request(path),timeout=timeout)
        except urllib.error.HTTPError as error:
            f.need(signed_redirect and error.code in (301,302,303,307,308),'GitHub API request failed')
            url=error.headers.get('Location',''); parsed=urllib.parse.urlsplit(url)
            f.need(parsed.scheme=='https' and parsed.hostname and not parsed.username and not parsed.password and not parsed.fragment,'unsafe artifact storage redirect')
            try:
                check_deadline(self.deadline)
                timeout=min(60,max(0.001,self.deadline-time.monotonic())) if self.deadline is not None else 60
                return urllib.request.build_opener(NoRedirect()).open(urllib.request.Request(url,headers={'User-Agent':'conditional-checked-stage-transport'}),timeout=timeout)
            except Exception: raise f.Rejected('signed artifact storage request failed; URL suppressed') from None

    def read_bounded(self,response,maximum):
        chunks=[]; count=0
        while True:
            check_deadline(self.deadline)
            block=getattr(response,'read1',response.read)(min(1024**2,maximum+1-count))
            check_deadline(self.deadline)
            if not block: break
            count+=len(block); f.need(count<=maximum,'remote metadata/log byte cap'); chunks.append(block)
        return b''.join(chunks)

    def get(self,path):
        with self.response(path) as response: data=self.read_bounded(response,8*1024**2)
        return f.parse_json(data)

    def bind_producer(self,job,artifact,stage):
        with self.response(f'/repos/{REPOSITORY}/actions/jobs/{job["id"]}/logs',signed_redirect=True) as response:
            data=self.read_bounded(response,MAX_JOB_LOG)
        emitted=re.findall(rb'^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}(?:\.\d+)?Z CONDITIONAL_STAGE_ARTIFACT_V1 (\{[^\r\n]*\})\r?$',data,re.M)
        f.need(len(emitted)==1,'unique emitted producer artifact binding missing')
        marker=f.parse_json(emitted[0]); expected={'stage_id':stage,'artifact_id':str(artifact['id']),
            'artifact_sha256':artifact['digest'][7:],'artifact_name':artifact['name']}
        f.need(marker==expected,'producer job artifact ID/name/digest binding differs')
        return f.sha(data)

    def collection(self,path,key):
        result=[]
        for page in range(1,7):
            obj=self.get(path+f'?per_page=100&page={page}'); rows=obj[key]
            f.need(isinstance(rows,list) and len(rows)<=100,'invalid API list'); result.extend(rows)
            if len(rows)<100:
                f.need(len(result)==obj['total_count'],'inconsistent API collection count')
                return result
        raise f.Rejected('GitHub metadata pagination bound exceeded')

    def jobs(self):
        if self._jobs is None: self._jobs=self.collection(f'/repos/{REPOSITORY}/actions/runs/{self.run_id}/attempts/{self.attempt}/jobs','jobs')
        return self._jobs

    def artifacts(self):
        if self._artifacts is None: self._artifacts=self.collection(f'/repos/{REPOSITORY}/actions/runs/{self.run_id}/artifacts','artifacts')
        return self._artifacts

    def artifact_name(self,stage):
        f.need(isinstance(stage,str) and re.fullmatch(r'(?:F[0-4]|H[0-5])_[a-z][a-z0-9_]*',stage),'invalid stage role')
        return f'conditional-geometry-{self.run_id}-{self.attempt}-{stage}-objects'

    def download_stage(self,stage,producer_name,target,max_bytes=MAX_ARCHIVE):
        if not hasattr(self,'_accepted_stages'): self._accepted_stages=set()
        f.need(stage not in self._accepted_stages,'stage already accepted by this transport')
        lock=self.origin_lock
        if lock is not None:
            f.need(stage==lock['stage_id'] and producer_name==lock['producer_job_name'],'requested stage differs from origin lock')
        f.need(type(max_bytes) is int and 0<max_bytes<=MAX_ARCHIVE,'invalid artifact payload cap')
        f.need(producer_name=='conditional '+stage,'unexpected producer job name')
        jobs=[j for j in self.jobs() if j['name']==producer_name]
        f.need(len(jobs)==1,'required producer job missing or duplicated'); job=jobs[0]
        f.need(job['status']=='completed' and job['conclusion']=='success' and type(job['id']) is int and job['id']>0
               and str(job['run_id'])==self.run_id and str(job['run_attempt'])==self.attempt and job['head_sha']==self.commit,
               'producer unsuccessful or not selected run/attempt/commit')
        f.need(sum(row['id']==job['id'] for row in self.jobs())==1,'duplicate producer job identifier')
        if lock is not None: f.need(job['id']==lock['producer_job_id'],'locked producer job identifier differs')
        matches=[a for a in self.artifacts() if a['name']==self.artifact_name(stage)]
        f.need(len(matches)==1,'selected-run artifact missing/duplicate'); artifact=matches[0]
        f.need(artifact['expired'] is False and type(artifact['id']) is int and artifact['id']>0,'artifact expired/invalid')
        f.need(sum(a['id']==artifact['id'] for a in self.artifacts())==1,'duplicate artifact identifier')
        maximum=max_bytes+ZIP_ALLOWANCE
        f.need(type(artifact['size_in_bytes']) is int and 0<artifact['size_in_bytes']<=maximum,'artifact transfer bound')
        digest=artifact.get('digest',''); f.need(isinstance(digest,str) and re.fullmatch(r'sha256:[0-9a-f]{64}',digest),'authoritative artifact digest absent')
        run=artifact.get('workflow_run',{})
        f.need(str(run.get('id'))==self.run_id and run.get('head_sha')==self.commit,'artifact run/commit mismatch')
        if lock is not None:
            f.need(artifact['id']==lock['artifact_id'] and artifact['name']==lock['artifact_name'] and
                   artifact['size_in_bytes']==lock['artifact_zip_bytes'] and digest[7:]==lock['artifact_zip_sha256'],
                   'locked artifact identifier/name/size/digest differs')
        binding_sha=self.bind_producer(job,artifact,stage)
        if lock is not None: f.need(binding_sha==lock['producer_job_log_sha256'],'locked producer log digest differs')
        target=Path(target); f.no_symlink_path(target); f.need(not target.exists(),'download destination must be new')
        require_disk(target,artifact['size_in_bytes'],entries=1,directories=1); target.mkdir(parents=True); archive=target/'download.zip'
        path=f'/repos/{REPOSITORY}/actions/artifacts/{artifact["id"]}/zip'
        response=self.response(path,signed_redirect=True)
        h=hashlib.sha256(); count=0
        with response,archive.open('xb') as out:
            while True:
                check_deadline(self.deadline)
                block=getattr(response,'read1',response.read)(1024**2)
                check_deadline(self.deadline)
                if not block: break
                count+=len(block); f.need(count<=maximum,'artifact ZIP transfer bound'); h.update(block); out.write(block)
        f.need(count==artifact['size_in_bytes'] and h.hexdigest()==digest[7:],'artifact ZIP digest/size mismatch')
        _extract_zip(archive,target,max_bytes)
        archive.unlink()
        origin={'identity':dict(self.identity),'stage_id':stage,'artifact_name':artifact['name'],
                'artifact_id':artifact['id'],'producer_job_name':producer_name,'producer_job_id':job['id'],
                'producer_conclusion':'success','artifact_zip_sha256':digest[7:],'artifact_zip_bytes':count,
                'workflow_path':WORKFLOW_PATH,'workflow_id':self.workflow_id,'producer_job_log_sha256':binding_sha}
        if lock is not None: f.need(origin==lock,'downloaded producer origin differs from exact host lock')
        self._accepted_stages.add(stage)
        return origin


def _extra_fields(data):
    result={}; pos=0
    while pos<len(data):
        f.need(pos+4<=len(data),'truncated ZIP extra metadata')
        tag,size=struct.unpack_from('<HH',data,pos); pos+=4
        f.need(tag not in result and pos+size<=len(data) and tag in (1,0x5455,0x7875),'unapproved/duplicate ZIP extra metadata')
        value=data[pos:pos+size]
        if tag==1: f.need(size in (8,16,24,28),'invalid ZIP64 extra layout')
        elif tag==0x5455:
            f.need(size>=1 and value[0] in range(1,8) and size==1+4*value[0].bit_count(),'invalid ZIP timestamp layout')
        else:
            f.need(size>=5 and value[0]==1 and value[1] in (1,2,4,8),'invalid ZIP UID layout')
            at=2+value[1]; f.need(at<size and value[at] in (1,2,4,8) and size==at+1+value[at],'invalid ZIP GID layout')
        result[tag]=value; pos+=size
    return result


def _zip_layout(archive,z):
    """Prove a contiguous two-entry ZIP with no hidden records or payload gaps."""
    infos=z.infolist(); size=regular(archive)
    f.need(size>=22 and len(infos)==2 and {x.filename for x in infos}=={'stage.tar','descriptor.json'},'ZIP members differ')
    with Path(archive).open('rb') as raw:
        raw.seek(-22,2); end=raw.read(22)
        f.need(end[:4]==b'PK\x05\x06' and end[-2:]==b'\0\0','ZIP comment/trailing payload forbidden')
        _,disk,cd_disk,disk_count,count,cd_size,cd_offset,comment=struct.unpack('<4s4H2IH',end)
        f.need(disk==cd_disk==0 and disk_count==count==2 and comment==0,'multipart ZIP forbidden')
        cd_end=size-22
        if size>=42:
            raw.seek(size-42); locator=raw.read(20)
            if locator[:4]==b'PK\x06\x07':
                _,start_disk,offset,disks=struct.unpack('<4sIQI',locator)
                f.need(start_disk==0 and disks==1 and offset+56==size-42,'ZIP64 locator differs')
                raw.seek(offset); e64=raw.read(56)
                sig,record_size,made,needed,disk,cd_disk,n_disk,n_total,sz,off=struct.unpack('<4sQ2H2I4Q',e64)
                f.need(sig==b'PK\x06\x06' and record_size==44 and disk==cd_disk==0 and n_disk==n_total==2 and needed<=45,'ZIP64 end metadata differs')
                f.need(cd_size in (sz,0xffffffff) and cd_offset in (off,0xffffffff),'ZIP64 central metadata differs')
                cd_size,cd_offset,cd_end=sz,off,offset
        f.need(cd_offset==z.start_dir and cd_offset+cd_size==cd_end,'ZIP central-directory gap/alias')
        raw.seek(cd_offset)
        for info in infos:
            header=raw.read(46); f.need(len(header)==46 and header[:4]==b'PK\x01\x02','ZIP central header differs')
            values=struct.unpack('<4s6H3I5H2I',header); nlen,xlen,clen=values[10:13]
            f.need(clen==0 and values[13]==0,'ZIP comment/multiple disks forbidden')
            name=raw.read(nlen); extra=raw.read(xlen); fields=_extra_fields(extra)
            q=b''
            for raw_value,actual_value in ((values[9],info.file_size),(values[8],info.compress_size),(values[16],info.header_offset)):
                if raw_value==0xffffffff: q+=struct.pack('<Q',actual_value)
            f.need(fields.get(1,b'')==q,'ZIP64 central extra fields/length differ')
            f.need(name==info.filename.encode('ascii') and values[3]==info.flag_bits and values[4]==info.compress_type,'ZIP central name/method differs')
        f.need(raw.tell()==cd_end,'hidden ZIP central records/trailing payload')
        position=0; offsets={}
        for info in sorted(infos,key=lambda row:row.header_offset):
            f.need(info.header_offset==position,'hidden ZIP local entry/gap/alias')
            raw.seek(position); header=raw.read(30)
            f.need(len(header)==30 and header[:4]==b'PK\x03\x04','ZIP local header differs')
            sig,version,flags,method,mtime,mdate,crc,csize,usize,nlen,xlen=struct.unpack('<4s5H3I2H',header)
            name=raw.read(nlen); extras=_extra_fields(raw.read(xlen)); data_start=raw.tell()
            f.need(name==info.filename.encode('ascii') and flags==info.flag_bits and method==info.compress_type and not flags&~(8|2048),'ZIP local/central name/flags/method differ')
            raw_usize,raw_csize=usize,csize
            local_q=extras.get(1,b'')
            required_fields=(usize==0xffffffff)+(csize==0xffffffff)
            f.need(len(local_q)==8*required_fields,'ZIP64 local extra length differs')
            if flags&8 and local_q:
                advertised=[]
                if usize==0xffffffff: advertised.append(info.file_size)
                if csize==0xffffffff: advertised.append(info.compress_size)
                f.need(all(value in (0,actual) for value,actual in zip(struct.unpack('<'+'Q'*required_fields,local_q),advertised)),
                       'ZIP64 streamed local sizes differ')
            if not flags&8:
                if usize==0xffffffff or csize==0xffffffff:
                    q=extras.get(1,b''); offset=0
                    if usize==0xffffffff: f.need(len(q)>=offset+8,'missing ZIP64 size'); usize=struct.unpack_from('<Q',q,offset)[0]; offset+=8
                    if csize==0xffffffff: f.need(len(q)>=offset+8,'missing ZIP64 compressed size'); csize=struct.unpack_from('<Q',q,offset)[0]
                f.need((crc,csize,usize)==(info.CRC,info.compress_size,info.file_size),'ZIP local/central sizes or CRC differ')
            else:
                f.need(crc in (0,info.CRC) and csize in (0,0xffffffff,info.compress_size) and usize in (0,0xffffffff,info.file_size),'ZIP streaming local metadata differs')
            position=data_start+info.compress_size; f.need(position<=cd_offset,'ZIP entry overlaps central directory')
            if flags&8:
                raw.seek(position); tail=raw.read(24)
                candidates=[struct.pack('<III',info.CRC,info.compress_size,info.file_size)] if max(info.compress_size,info.file_size)<=0xffffffff else []
                candidates.append(struct.pack('<IQQ',info.CRC,info.compress_size,info.file_size))
                candidates += [b'PK\x07\x08'+value for value in list(candidates)]
                matches=[value for value in candidates if tail.startswith(value)]
                f.need(len(matches)==1,'ZIP data descriptor differs or aliases'); position+=len(matches[0])
            offsets[info.filename]=data_start
        f.need(position==cd_offset,'hidden ZIP local/trailing payload before central directory')
    return offsets


def _extract_zip(archive,target,maximum):
    with zipfile.ZipFile(archive) as z:
        infos=z.infolist(); offsets=_zip_layout(archive,z)
        for info in infos:
            f.safe_rel(info.filename); mode=info.external_attr>>16
            f.need(not info.is_dir() and stat.S_IFMT(mode) in (0,stat.S_IFREG) and not info.flag_bits&1 and info.compress_type in (zipfile.ZIP_STORED,zipfile.ZIP_DEFLATED),'unsafe ZIP member')
            cap=MAX_METADATA if info.filename=='descriptor.json' else maximum
            f.need(0<info.file_size<=cap,'ZIP expansion bound')
        require_disk(target,sum(info.file_size for info in infos),entries=2)
        for info in infos:
            out=Path(target)/info.filename; f.no_symlink_path(out)
            with Path(archive).open('rb') as src,out.open('xb') as dst:
                src.seek(offsets[info.filename]); remaining=info.compress_size; copied=0; crc=0
                decoder=zlib.decompressobj(-15) if info.compress_type==zipfile.ZIP_DEFLATED else None
                while remaining:
                    chunk=src.read(min(remaining,1024**2)); f.need(bool(chunk),'truncated ZIP compressed stream'); remaining-=len(chunk)
                    while chunk:
                        block=decoder.decompress(chunk,1024**2) if decoder else chunk
                        copied+=len(block); f.need(copied<=info.file_size,'ZIP expansion exceeds advertised size'); crc=zlib.crc32(block,crc); dst.write(block)
                        if decoder:
                            f.need(not decoder.unused_data,'hidden trailing compressed ZIP payload'); chunk=decoder.unconsumed_tail
                        else: chunk=b''
                f.need(copied==info.file_size and crc==info.CRC and (decoder is None or decoder.eof),'ZIP size/CRC/deflate EOF differs')


def layout_names(names):
    names=set(names); dirs=set()
    for name in names:
        f.safe_rel(name); parts=Path(name).parts
        f.need(len(parts)<=12 and len(name.encode())<=255,'transport path depth/length bound')
        dirs.update(str(p) for p in Path(name).parents if str(p)!='.')
    f.need(not names.intersection(dirs),'transport file/directory path alias')
    return dirs


def write_stage(objects,evidence,stage_receipt,destination,maximum=MAX_ARCHIVE,evidence_maximum=MAX_EVIDENCE,*,deadline=None):
    check_deadline(deadline)
    f.need(type(maximum) is int and 0<maximum<=MAX_ARCHIVE and type(evidence_maximum) is int and 0<evidence_maximum<=MAX_EVIDENCE,'invalid transport bounds')
    f.need(set(stage_receipt)==set(META_KEYS),'stage receipt metadata keys differ'); _identity(stage_receipt['identity'])
    modules=stage_receipt['stage_modules']; f.need(modules and len(modules)==len(set(modules)),'empty/duplicate stage modules')
    own=set().union(*(paths(m) for m in modules)); objects=Path(objects); evidence=Path(evidence)
    source_files=f.regular_tree(objects); f.need(own<=set(source_files),'missing checked own companion')
    evidence_rows=inventory(evidence,evidence_maximum)
    files={'objects/'+n:source_files[n] for n in own}; files.update({'evidence/'+n:evidence/n for n in evidence_rows})
    layout_names(files)
    rows={name:{'bytes':regular(p),'sha256':f.file_sha(p)} for name,p in sorted(files.items())}
    f.need(sum(x['bytes'] for x in rows.values())<=maximum,'stage payload budget exceeded')
    receipt={'schema':SCHEMA,**stage_receipt,'files':rows}
    f.need(len(f.json_bytes(receipt))<=MAX_METADATA,'receipt metadata cap exceeded')
    destination=Path(destination); f.no_symlink_path(destination); f.need(not destination.exists(),'stage output directory must be new')
    raw_bytes=sum(512+((size+511)//512)*512 for size in [len(f.json_bytes(receipt)),*[row['bytes'] for row in rows.values()]])
    tar_bytes=((raw_bytes+1024+10239)//10240)*10240
    f.need(tar_bytes<=maximum,'canonical raw tar exceeds hard cap before creation')
    require_disk(destination,tar_bytes+MAX_METADATA,entries=2,directories=1); destination.mkdir(parents=True)
    archive=destination/'stage.tar'; receipt_sha=f.write_tar(archive,files,receipt,maximum)
    descriptor={'schema':'conditional-stage-descriptor-v1','stage_id':stage_receipt['stage_id'],
                'archive_bytes':regular(archive),'archive_sha256':f.file_sha(archive),'receipt_sha256':receipt_sha}
    (destination/'descriptor.json').write_bytes(f.json_bytes(descriptor))
    check_deadline(deadline)
    return descriptor


def extract_stage(download_dir,destination,maximum=MAX_ARCHIVE,*,deadline=None):
    check_deadline(deadline)
    f.need(type(maximum) is int and 0<maximum<=MAX_ARCHIVE,'invalid archive maximum')
    download_dir=Path(download_dir); f.exact_tree(download_dir,{'stage.tar','descriptor.json'})
    f.need(regular(download_dir/'descriptor.json')<=MAX_METADATA,'descriptor metadata bound')
    descriptor=f.load_json(download_dir/'descriptor.json')
    f.need(set(descriptor)=={'schema','stage_id','archive_bytes','archive_sha256','receipt_sha256'} and descriptor['schema']=='conditional-stage-descriptor-v1','descriptor schema differs')
    archive=download_dir/'stage.tar'; size=regular(archive)
    f.need(type(descriptor['archive_bytes']) is int and size==descriptor['archive_bytes'] and 0<size<=maximum,'raw tar byte bound')
    f.need(isinstance(descriptor['archive_sha256'],str) and f.SHA256.fullmatch(descriptor['archive_sha256']) and f.file_sha(archive)==descriptor['archive_sha256'],'raw tar digest differs')
    destination=Path(destination); f.no_symlink_path(destination); f.need(not destination.exists(),'stage quarantine must be new')
    require_disk(destination,size,entries=1,directories=1); destination.mkdir(parents=True)
    names=[]; total=0; position=0; declared=None; declared_names=[]
    with archive.open('rb') as raw:
        while True:
            header=raw.read(512); position+=len(header); f.need(len(header)==512,'truncated tar header')
            if header==bytes(512):
                # write_tar uses canonical 10240-byte records: two end blocks,
                # then only the exact required all-zero record padding.
                end=((position-512+1024+10239)//10240)*10240
                f.need(size==end,'noncanonical/trailing tar payload')
                rest=raw.read(); f.need(len(rest)>=512 and not any(rest),'tar trailing payload/nonzero padding'); break
            try: info=tarfile.TarInfo.frombuf(header,'utf-8','strict')
            except Exception: raise f.Rejected('invalid canonical tar header') from None
            name=f.safe_rel(info.name); f.need(name not in names and info.isreg() and not info.pax_headers,'duplicate/nonregular tar entry')
            canonical=tarfile.TarInfo(name); canonical.mode=0o644; canonical.size=info.size
            f.need(header==canonical.tobuf(format=tarfile.USTAR_FORMAT,encoding='utf-8',errors='strict'),'noncanonical tar metadata/link/pax')
            f.need(type(info.size) is int and 0<=info.size<=512*1024**2,'tar member size cap')
            layout_names({name})
            if not names: f.need(name=='receipt.json' and info.size<=MAX_METADATA,'receipt must be first and bounded')
            else:
                index=len(names)-1
                f.need(index<len(declared_names) and name==declared_names[index] and info.size==declared[name]['bytes'],
                       'actual tar name/order/size differs from bounded declaration before allocation')
            names.append(name); total+=info.size; f.need(len(names)<=40001 and total<=maximum,'tar expansion cap')
            out=destination/name; out.parent.mkdir(parents=True,exist_ok=True); remaining=info.size
            with out.open('xb') as dest:
                while remaining:
                    block=raw.read(min(remaining,1024**2)); f.need(bool(block),'truncated tar member'); dest.write(block); remaining-=len(block)
            if name=='receipt.json':
                early=f.load_json(out); declared=early['files']; f.need(isinstance(declared,dict) and len(declared)<=40000,'tar declared file count bound')
                declared_names=sorted(declared)
                dirs=layout_names({'receipt.json',*declared})
                for row in declared.values(): _row(row)
                total_declared=sum(row['bytes'] for row in declared.values())
                f.need(total_declared<=maximum and all(n.startswith(('objects/','evidence/')) for n in declared),'tar declared payload differs')
                require_disk(destination,total_declared,entries=len(declared),directories=len(dirs))
            padding=(-info.size)%512; f.need(raw.read(padding)==bytes(padding),'nonzero/truncated member padding'); position+=info.size+padding
    f.need(names and f.file_sha(destination/'receipt.json')==descriptor['receipt_sha256'],'receipt digest differs')
    receipt=f.load_json(destination/'receipt.json')
    f.need(receipt['schema']==SCHEMA and receipt['stage_id']==descriptor['stage_id'],'receipt stage/schema differs')
    files=receipt['files']; f.need(isinstance(files,dict) and names==['receipt.json',*sorted(files)],'unlisted/missing/reordered tar members')
    f.exact_tree(destination,set(names))
    for name,row in files.items():
        f.safe_rel(name); _row(row); p=destination/name
        f.need(regular(p)==row['bytes'] and f.file_sha(p)==row['sha256'],'archive member bytes/hash differ')
    check_deadline(deadline)
    return receipt


def command_specs(expected,api):
    """Reconstruct the complete approved command sequence, not receipt-supplied argv."""
    work=Path(expected['producer_work']); runtime=Path(expected['runtime']); contract=expected['contract']
    legacy=contract.get('schema')=='conditional-geometry-staged-replay-v2'
    f.need((legacy and 'module_compile_arguments' not in contract) or
           (contract.get('schema') in ('conditional-geometry-origin-continuation-v3','higher-dimension-staged-replay-v1') and
            callable(getattr(api,'module_compile_arguments',None))), 'unrecognized producer scheduling policy')
    f.need(work.is_absolute() and str(work)==str(work.absolute()) and runtime==work/'runtime','producer work/runtime path differs')
    f.no_symlink_path(work); f.no_symlink_path(runtime)
    env=api.safe_env(runtime,work/'home',work/'tmp'); env['MATHLIB_CACHE_DIR']=str(work/'cache')
    specs=[]
    def add(name,argv,seconds,allowed=False):
        specs.append({'name':name,'argv':list(map(str,argv)),'cwd':str(work),
                      'requested_timeout_seconds':seconds,'max_rss_bytes':8*GIB,'allow_new_sessions':allowed})
    add('bwrap-preflight',api.sandbox(['/bin/true'],runtime=runtime,sources=[],writable=[work/'home',work/'tmp'],cwd=work/'tmp',env=env),30,True)
    committed=work/'preflight-read-only'; staging=work/'preflight-quarantine'
    script='test -r "$1/predecessor"; if printf bad > "$1/predecessor"; then exit 11; fi; if chmod 0600 "$1/predecessor"; then exit 12; fi; if mkdir "$1/SpectreGeometry"; then exit 13; fi; printf allowed > "$2/output"'
    add('read-only-committed-root-preflight',api.sandbox(['/bin/sh','-eu','-c',script,'readonly-boundary-control',committed,staging],runtime=runtime,sources=[committed],writable=[staging,work/'home',work/'tmp'],cwd=staging,env=env),30,True)
    add('curl-version',['/usr/bin/curl','--disable','--version'],30)
    pins=expected['dependency_pins']
    for pin in pins:
        name=pin['name']; base=['/usr/bin/git','-c','core.hooksPath=/dev/null','-c','core.fsmonitor=false','-C',str(work/'packages'/name)]
        add(name+'-init',base+['init','--quiet'],30)
        add(name+'-remote',base+['remote','add','origin',pin['url']],30)
        add(name+'-fetch',base+['fetch','--quiet','--depth=1','--no-tags',pin['url'],pin['rev']],300,True)
        add(name+'-checkout',base+['checkout','--quiet','--detach',pin['rev']],60)
    kwargs=dict(runtime=runtime,sources=[work/'packages'],writable=[work/'home',work/'tmp',work/'cache',*[work/'packages'/p['name']/'.lake' for p in pins]],cwd=work/'packages/mathlib',env=env)
    add('cache-bootstrap',api.sandbox([runtime/'bin/lake','build','cache'],**kwargs),900,True)
    cache=work/'bootstrap/cache'; kwargs['sources'].append(work/'bootstrap')
    add('cache-get',api.sandbox([runtime/'bin/lake','env',cache,'get','--cache-from=master,legacy',*contract['cache_roots']],network=True,**kwargs),1800,True)
    add('cache-lookup',api.sandbox([runtime/'bin/lake','env',cache,'lookup',*expected['cache_rows']],**kwargs),180,True)
    if contract.get('schema')=='higher-dimension-staged-replay-v1' and expected['stage_id'] in ['H0_common','H5_higher_assembly']:
        specs.extend(api.higher.auditor_specs(contract,work,runtime,expected['cache_search'],api)[:-1])
    env['LEAN_PATH']=':'.join([str(work/'objects'),*map(str,expected['cache_search']),str(runtime/'lib/lean')])
    for row in expected['stage_rows']:
        module=row['module']; rel=module.replace('.','/'); staging=work/'quarantine'/module
        kwargs=dict(runtime=runtime,sources=[work/'packages',work/'src',work/'objects'],writable=[staging,work/'home',work/'tmp'],cwd=work/'src',env=env)
        options=[] if legacy else api.module_compile_arguments(contract,module)
        argv=[runtime/'bin/lean','-j1','-M4096','-Dcompiler.postponeCompile=false',*options,'-o',staging/(rel+'.olean'),'-i',staging/(rel+'.ilean'),'-c',staging/(rel+'.c'),work/'src'/(rel+'.lean')]
        add('compile-'+module,api.sandbox(argv,**kwargs),contract['diagnostic_timeout_seconds'],True)
        kwargs['writable']=[work/'home',work/'tmp']
        add('check-'+module,api.sandbox([runtime/'bin/leanchecker',module],**kwargs),api.higher.checker_seconds(contract,module) if contract.get('schema')=='higher-dimension-staged-replay-v1' else contract['check_timeout_seconds'],True)
    if expected['stage_id']=='F4_bridge_and_endpoint_joins':
        audit_env=api.safe_env(runtime,work/'home',work/'tmp'); audit_env['LEAN_PATH']=str(work/'auditor-objects')+':'+str(runtime/'lib/lean')
        for name in ['AuditOrdinaryBridges','AuditConditionalEndpoints']:
            staging=work/'quarantine'/name
            kwargs=dict(runtime=runtime,sources=[work/'auditors',work/'auditor-objects'],writable=[staging,work/'home',work/'tmp'],cwd=work/'auditors',env=audit_env)
            argv=[runtime/'bin/lean','-j1','-M4096','-Dcompiler.postponeCompile=false','-o',staging/(name+'.olean'),'-i',staging/(name+'.ilean'),'-c',staging/(name+'.c'),work/'auditors'/(name+'.lean')]
            add('compile-auditor-'+name,api.sandbox(argv,**kwargs),180,True)
            kwargs['writable']=[work/'home',work/'tmp']; add('check-auditor-'+name,api.sandbox([runtime/'bin/leanchecker',name],**kwargs),120,True)
            run_env=dict(env); run_env['LEAN_PATH']=str(work/'auditor-objects')+':'+env['LEAN_PATH']
            kwargs=dict(runtime=runtime,sources=[work/'auditors',work/'auditor-objects',work/'objects',work/'packages'],writable=[work/'home',work/'tmp'],cwd=work/'auditors',env=run_env)
            add('audit-'+name,api.sandbox([runtime/'bin/lean','-j1','-M4096','--run',work/'auditors'/(name+'.lean')],**kwargs),contract['auditor_timeout_seconds'],True)
    if contract.get('schema')=='higher-dimension-staged-replay-v1' and expected['stage_id']==contract['final_stage']:
        specs.extend(api.higher.auditor_specs(contract,work,runtime,expected['cache_search'],api)[-1:])
    return specs


def _json_lines(path):
    data=path.read_bytes(); f.need(data.endswith(b'\n'),'JSONL missing complete last line')
    return [f.parse_json(line) for line in data.splitlines()]


def validate_commands(commands,evidence,expected,api):
    specs=command_specs(expected,api); contract=expected['contract']
    f.need(len(commands)==len(specs),'command sequence coverage differs')
    total=0; elapsed=0
    for command,spec in zip(commands,specs):
        for key,value in spec.items(): f.need(command.get(key)==value,'command specification differs: '+spec['name']+'/'+key)
        f.need(type(command.get('exit_code')) is int and command['exit_code']==0,'unsuccessful command')
        for key in ('timed_out','log_overflow','memory_exceeded','surviving_children'):
            f.need(command.get(key) is False,'failed/incomplete command cleanup: '+key)
        for key in ('process_group_empty','descendants_empty'):
            f.need(command.get(key) is True,'unclean command process tree: '+key)
        allowed=spec['allow_new_sessions']
        f.need(type(command.get('escaped_descendants')) is bool and command.get('new_sessions_explicitly_allowed') is allowed and
               (not command['escaped_descendants'] or allowed),'unapproved escaped descendants/session policy')
        requested=spec['requested_timeout_seconds']; effective=command.get('effective_timeout_seconds')
        f.need(type(effective) is int and 0<effective<=requested and command.get('timeout_seconds')==effective,'effective timeout differs')
        f.need(command.get('address_space_bytes')==12*GIB and command.get('max_created_file_bytes')==512*1024**2 and
               command.get('max_log_bytes')==contract['per_command_log_max_bytes'],'command resource profile differs')
        f.need(command.get('limits')=={'address_space_bytes':12*GIB,'rss_tree_bytes':8*GIB,'max_created_file_bytes':512*1024**2},'serialized command limits differ')
        duration=command.get('elapsed_seconds'); peak=command.get('peak_sampled_tree_rss_bytes')
        f.need(type(duration) in (int,float) and math.isfinite(duration) and duration>=0 and
               type(peak) is int and 0<=peak<=8*GIB,'invalid command resource observations'); elapsed+=duration
        command_bytes=0
        for stream in ('stdout','stderr'):
            p=evidence/'logs'/(spec['name']+'.'+stream); command_bytes+=regular(p)
            f.need(f.file_sha(p)==command.get(stream+'_sha256'),'command log bytes differ')
        f.need(command_bytes<=contract['per_command_log_max_bytes'],'per-command logs exceeded cap'); total+=command_bytes
    f.need(total<=contract['aggregate_log_max_bytes'] and elapsed<=contract['aggregate_command_deadline_seconds'],'aggregate command/log budget exceeded')
    expected_logs={s['name']+'.'+stream for s in specs for stream in ('stdout','stderr')}
    f.exact_tree(evidence/'logs',expected_logs)
    return total


def contract_stage(contract,sid):
    return contract['stages'][sid]['modules']


def admit_stage(extracted,*,expected,objects,prior,checked,api,deadline=None):
    """Validate all receipt relations, then merge only the producer's new objects.

    expected and api are host-produced from the pinned contract and independently
    acquired current runtime/cache; none may be supplied by artifact metadata.
    On validation rejection, objects is untouched. Host I/O failure during the
    final merge is fatal; no receipt is returned and the caller must stop.
    """
    check_deadline(deadline)
    extracted=Path(extracted); objects=Path(objects)
    f.need(regular(extracted/'receipt.json')<=MAX_METADATA,'stage receipt metadata bound')
    receipt=f.load_json(extracted/'receipt.json')
    f.need(set(receipt)=={'schema','files',*META_KEYS} and receipt['schema']==SCHEMA,'stage receipt schema differs')
    _identity(expected['identity'])
    for key in META_KEYS: f.need(receipt[key]==expected[key],'stage metadata differs: '+key)
    origin=expected['origin']
    f.need(isinstance(origin,dict) and set(origin)==set(ORIGIN_KEYS),'transport provenance keys differ')
    f.need(origin['identity']==expected['identity'] and origin['stage_id']==expected['stage_id'] and
           origin['producer_job_name']=='conditional '+expected['stage_id'] and origin['producer_conclusion']=='success',
           'transport provenance differs')
    f.need(origin['artifact_name']==f"conditional-geometry-{expected['identity']['run_id']}-{expected['identity']['run_attempt']}-{expected['stage_id']}-objects",
           'transport artifact name differs')
    f.need(type(origin['artifact_id']) is int and origin['artifact_id']>0 and type(origin['producer_job_id']) is int and origin['producer_job_id']>0
           and isinstance(origin['artifact_zip_sha256'],str) and f.SHA256.fullmatch(origin['artifact_zip_sha256']) and
           type(origin['artifact_zip_bytes']) is int and 0<origin['artifact_zip_bytes']<=MAX_ARCHIVE+ZIP_ALLOWANCE,'invalid authenticated transport origin')
    f.need(origin.get('workflow_path')==WORKFLOW_PATH and type(origin.get('workflow_id')) is int and origin['workflow_id']>0 and
           isinstance(origin.get('producer_job_log_sha256'),str) and f.SHA256.fullmatch(origin['producer_job_log_sha256']),
           'producer job/workflow binding absent')
    stage=expected['contract']['stages'][expected['stage_id']]
    modules=[row['module'] for row in expected['stage_rows']]
    f.need(modules==expected['stage_modules']==stage['modules'] and len(modules)==len(set(modules)) and modules,'stage module coverage differs')
    f.need(expected['admitted_stages']==stage['admitted_stages'],'predecessor stage closure differs')
    f.need([r['stage_id'] for r in expected['predecessor_artifacts']]==expected['admitted_stages'],'predecessor artifact coverage differs')
    for row in expected['stage_rows']:
        f.need(row==expected['owned_rows'][row['module']],'stage source row differs from owned source lock')
    own=set().union(*(paths(m) for m in modules)); files=receipt['files']
    f.need(isinstance(files,dict) and len(files)<=40000,'stage file inventory invalid')
    f.exact_tree(extracted,{'receipt.json',*files})
    object_files={n.removeprefix('objects/') for n in files if n.startswith('objects/')}
    f.need(object_files==own and all(n.startswith(('objects/','evidence/')) for n in files),'stage companion coverage differs')
    evidence_bytes=0; payload_bytes=0
    for name,row in files.items():
        f.safe_rel(name); _row(row); p=extracted/name
        f.need(regular(p)==row['bytes'] and f.file_sha(p)==row['sha256'],'stage file hash/bytes differ')
        payload_bytes+=row['bytes']
        if name.startswith('evidence/'): evidence_bytes+=row['bytes']
    f.need(evidence_bytes<=MAX_EVIDENCE and payload_bytes<=MAX_ARCHIVE,'stage payload/evidence cap exceeded')
    own_inv={name:files['objects/'+name] for name in sorted(own)}
    f.need(not own.intersection(prior),'duplicate/overwrite owned module objects')
    f.need(not set(modules).intersection(checked),'duplicate checked stage module')
    f.need(inventory(objects,MAX_OWNED)==prior,'current single owned root changed/unlisted')
    producer_prior=expected['producer_inventory']
    producer_checked={m for sid in expected['admitted_stages'] for m in contract_stage(expected['contract'],sid)}
    ancestor_paths=set().union(*(paths(m) for m in producer_checked)) if producer_checked else set()
    f.need(set(producer_prior)==ancestor_paths and producer_checked<=set(checked),'producer ancestor object/checked coverage differs')
    f.need(all(prior.get(n)==r for n,r in producer_prior.items()) and not own.intersection(producer_prior),'producer predecessor inventory differs')
    combined={**prior,**own_inv}; producer_final={**producer_prior,**own_inv}
    f.need(sum(row['bytes'] for row in combined.values())<=MAX_OWNED,'aggregate owned root cap exceeded')
    evidence=extracted/'evidence'; result=f.load_json(evidence/'result.json'); contract=expected['contract']
    success='CACHE_BACKED_CONDITIONAL_GEOMETRY_REPLAY_COMPLETED' if expected['stage_id']=='F4_bridge_and_endpoint_joins' else 'CHECKED_CONDITIONAL_STAGE_COMPLETED_C_EXPLICIT'
    if contract.get('schema')=='higher-dimension-staged-replay-v1':success=api.higher.SUCCESS if expected['stage_id']==contract['final_stage'] else api.higher.STAGE_SUCCESS
    f.need(result.get('status')==success and result.get('complete_evidence') is True,'producer evidence incomplete/failed')
    for key in ('run_id','run_attempt','workflow_commit'): f.need(result.get(key)==expected['identity'][key],'result run identity differs')
    for key in ('stage_id','stage_modules','admitted_stages','contract_sha256'): f.need(result.get(key)==expected[key],'result stage identity differs: '+key)
    freshness=contract.get('owned_objects_from_prior_runs_allowed')
    f.need(type(freshness) is bool,'producer contract freshness policy missing')
    scope_ok=(result.get('proof_scope')=='higher-dimension-sources-and-c-free-endpoints' and 'conditional_C_remains_explicit' not in result) if contract.get('schema')=='higher-dimension-staged-replay-v1' else result.get('conditional_C_remains_explicit') is True
    f.need(scope_ok and result.get('final_C_proof_certified') is False and
           result.get('unconditional_monotile_proof_certified') is False and result.get('owned_objects_from_prior_runs') is freshness,
           'producer conditional/freshness scope differs')
    f.need(result.get('checked_fresh_module_count')==len(modules) and result.get('checked_owned_module_count')==len(producer_final)//len(SUFFIXES),'checked module count differs')
    required_hashes={'commands.jsonl':'command_receipts_sha256','owned-modules.jsonl':'owned_module_receipts_sha256',
                     'fresh-owned-objects.json':'owned_output_inventory_sha256','runtime-inventory.json':'runtime_inventory_sha256',
                     'cached-build-inventory.json':'cached_build_inventory_sha256','source-extraction.json':'source_extraction_receipt_sha256',
                     'interface-identity.json':'interface_identity_sha256','imported-stages.json':'imported_stages_sha256'}
    for name,key in required_hashes.items(): f.need(f.file_sha(evidence/name)==result.get(key),'result evidence hash differs: '+name)
    if contract.get('schema') in ('conditional-geometry-origin-continuation-v3','higher-dimension-staged-replay-v1'):
        certificate=evidence/'cross-origin-admissions.json'
        f.need(f.file_sha(certificate)==result.get('cross_origin_admissions_sha256'),
               'cross-origin admission certificate digest differs')
        f.need(f.load_json(certificate)==api.cross_origin_certificate(contract,expected['contract_sha256'],
               expected['identity'],expected['stage_id'],expected['interface_identity'],
               expected['predecessor_artifacts'],producer_prior),'cross-origin admission certificate differs')
    else:
        f.need('cross_origin_admissions_sha256' not in result and
               'evidence/cross-origin-admissions.json' not in files,'legacy producer asserts a cross-origin certificate')
    f.need(f.load_json(evidence/'interface-identity.json')==expected['interface_identity'] and
           f.load_json(evidence/'imported-stages.json')==expected['predecessor_artifacts'],'evidence interface/lineage differs')
    f.need(result['runtime_inventory_sha256']==expected['runtime_inventory_sha256'] and
           expected['interface_identity']['runtime_inventory_sha256']==expected['runtime_inventory_sha256'],'runtime interface differs')
    producer_cached=f.load_json(evidence/'cached-build-inventory.json')
    for module,row in expected['cache_rows'].items():
        f.need(all(producer_cached[row['package']]['files'].get(name)==value for name,value in row['companions'].items()),
               'producer cached companion bytes differ: '+module)
    reconstructed_interface=api.cache_interface_identity(expected['cache_rows'],producer_cached,expected['runtime_inventory_sha256'])
    if contract.get('schema')=='higher-dimension-staged-replay-v1':
        reconstructed_interface=api.higher.cache_extension(contract,expected['cache_rows'],producer_cached,expected['runtime_inventory_sha256'],api)[2]
    f.need(expected['interface_identity']==reconstructed_interface,'producer external cache/native interface differs')
    if contract.get('schema')=='higher-dimension-staged-replay-v1':
        _,_,_,extension=api.higher.cache_extension(contract,expected['cache_rows'],producer_cached,expected['runtime_inventory_sha256'],api)
        f.need(result.get('higher_endpoints_have_no_C_premise') is True and result.get('all_dimension_uniform_proof_certified') is False,'higher producer claim scope differs')
        f.need(f.file_sha(evidence/'cache-extension-admission.json')==result.get('cache_extension_receipt_sha256') and f.load_json(evidence/'cache-extension-admission.json')==extension,'higher cache extension certificate differs')
    f.need(f.load_json(evidence/'fresh-owned-objects.json')=={'files':producer_final,'bytes':sum(r['bytes'] for r in producer_final.values())},'producer final object inventory differs')
    source_receipt={'schema':'authenticated-source-extraction-v1','archive':contract['source_archive'],'source_file_count':contract['owned_module_count'],
                    'source_bytes':contract['source_archive']['source_bytes'],'exact_source_tree':True,'all_source_pins_verified':True}
    f.need(f.load_json(evidence/'source-extraction.json')==source_receipt and result.get('source_archive_sha256')==contract['source_archive']['sha256'],'producer source extraction identity differs')
    commands=_json_lines(evidence/'commands.jsonl'); receipts=_json_lines(evidence/'owned-modules.jsonl')
    logs=validate_commands(commands,evidence,expected,api)
    f.need(result.get('command_count')==len(commands) and result.get('complete_log_bytes')==logs,'complete command/log counts differ')
    f.need([r['module'] for r in receipts]==modules,'ordered checked module receipt coverage differs')
    accepted=set(producer_checked); available=dict(producer_prior)
    for index,(row,record) in enumerate(zip(expected['stage_rows'],receipts)):
        module=row['module']; a=record.get('compiler_command'); b=record.get('checker_command')
        scope_key='proof_scope' if contract.get('schema')=='higher-dimension-staged-replay-v1' else 'conditional_C_remains_explicit'
        scope_value='higher-dimension-sources-and-c-free-endpoints' if scope_key=='proof_scope' else True
        f.need(set(record)=={'module','source_sha256','ordered_imports','outputs','compiler_command','checker_command','checker_passed',scope_key},'module receipt schema differs')
        f.need(type(a) is int and type(b) is int and 0<=a<b<len(commands) and a+1==b and
               commands[a]['name']=='compile-'+module and commands[b]['name']=='check-'+module,'compile/check adjacency or indexes differ')
        f.need(record['source_sha256']==row['sha256'] and record['checker_passed'] is True and record[scope_key]==scope_value,'module source/check/scope differs')
        f.need(record['outputs']=={n:own_inv[n] for n in sorted(paths(module))},'module companion inventory differs')
        imports=api.direct_import_receipt(row,expected['owned_rows'],accepted,available,expected['cache_rows'],Path(expected['runtime']))
        f.need(record['ordered_imports']==imports,'direct import checked-receipt linkage differs')
        accepted.add(module); available.update(record['outputs'])
    audits={'ordinary_bridges':True,'conditional_endpoints':True} if expected['stage_id']=='F4_bridge_and_endpoint_joins' else {}
    if contract.get('schema')=='higher-dimension-staged-replay-v1':audits={'higher_physical_endpoints':True} if expected['stage_id']==contract['final_stage'] else {}
    f.need(result.get('raw_audits')==audits,'stage raw-audit scope differs')
    if contract.get('schema')=='higher-dimension-staged-replay-v1':api.higher.validate_audit_evidence(contract,evidence,result,api)
    # No candidate is running here. Quarantine and downloaded roots never enter
    # LEAN_PATH. Validate all destinations before creating even the first file.
    own_dirs=layout_names(own)
    require_disk(objects,sum(row['bytes'] for row in own_inv.values()),entries=len(own),directories=len(own_dirs))
    for name in sorted(own):
        dest=objects/name; f.no_symlink_path(dest); f.need(not dest.exists(),'object destination already exists')
    for name in sorted(own):
        dest=objects/name; dest.parent.mkdir(parents=True,exist_ok=True)
        with (extracted/'objects'/name).open('rb') as src,dest.open('xb') as out: shutil.copyfileobj(src,out,1024**2)
        dest.chmod(0o444)
        f.need(regular(dest)==own_inv[name]['bytes'] and f.file_sha(dest)==own_inv[name]['sha256'],'host admission changed object bytes')
    f.need(inventory(objects,MAX_OWNED)==combined,'final admitted root differs')
    shutil.rmtree(extracted/'objects')  # Only these verified temporary copies; evidence/receipt remain.
    check_deadline(deadline)
    return receipts,combined
