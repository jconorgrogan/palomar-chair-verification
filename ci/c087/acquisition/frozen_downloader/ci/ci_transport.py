"""Authenticated, same-run GitHub artifact reads. Never changes remote state."""
from __future__ import annotations
import hashlib,json,os,re,stat,urllib.error,urllib.parse,urllib.request,zipfile
from pathlib import Path
import fresh_stage as f
REPOSITORY='jconorgrogan/palomar-chair-verification'
API='https://api.github.com'
class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self,*args,**kwargs):return None
class Transport:
    def __init__(self):
        f.need(os.environ.get('GITHUB_ACTIONS')=='true' and os.environ.get('GITHUB_REPOSITORY')==REPOSITORY,
               'not the reviewed GitHub repository/action context')
        self.run_id=os.environ.get('GITHUB_RUN_ID','');self.attempt=os.environ.get('GITHUB_RUN_ATTEMPT','')
        self.commit=os.environ.get('GITHUB_SHA','')
        f.need(self.run_id.isdigit() and self.attempt.isdigit() and f.COMMIT.fullmatch(self.commit), 'invalid workflow identity')
        self.token=os.environ.get('GH_TOKEN','');f.need(bool(self.token),'ephemeral read-only workflow token missing')
        self.opener=urllib.request.build_opener(NoRedirect())
        self.run=self.get(f'/repos/{REPOSITORY}/actions/runs/{self.run_id}')
        f.need(str(self.run['id'])==self.run_id and self.run['head_sha']==self.commit and
               str(self.run['run_attempt'])==self.attempt and self.run['event']=='push', 'trusted workflow run mismatch')
        self._jobs=None;self._artifacts=None
    def request(self,path):
        f.need(path.startswith(f'/repos/{REPOSITORY}/actions/'),'unapproved API path')
        return urllib.request.Request(API+path,headers={'Authorization':'Bearer '+self.token,
          'Accept':'application/vnd.github+json','X-GitHub-Api-Version':'2022-11-28','User-Agent':'hierarchy-c-fresh-verifier'})
    def get(self,path):
        with self.opener.open(self.request(path),timeout=60) as response:
            data=response.read(8*1024**2+1)
        f.need(len(data)<=8*1024**2,'oversized GitHub metadata')
        return f.parse_json(data)
    def collection(self,path,key):
        result=[]
        for page in range(1,7):
            obj=self.get(path+f'?per_page=100&page={page}');rows=obj[key];f.need(isinstance(rows,list),'invalid API list')
            result.extend(rows)
            if len(rows)<100:return result
        raise f.Rejected('GitHub metadata pagination bound exceeded')
    def jobs(self):
        if self._jobs is None:self._jobs=self.collection(f'/repos/{REPOSITORY}/actions/runs/{self.run_id}/attempts/{self.attempt}/jobs','jobs')
        return self._jobs
    def artifacts(self):
        if self._artifacts is None:self._artifacts=self.collection(f'/repos/{REPOSITORY}/actions/runs/{self.run_id}/artifacts','artifacts')
        return self._artifacts
    def artifact_name(self,role):
        f.need(re.fullmatch(r'[a-z][a-z0-9_]*',role),'invalid artifact role')
        return f'hierarchy-c-{self.run_id}-{self.attempt}-{role}'
    def successful_job(self,name):
        matches=[j for j in self.jobs() if j['name']==name]
        f.need(len(matches)==1 and matches[0]['status']=='completed' and matches[0]['conclusion']=='success',
               'required producer job is missing, duplicated, failed, or incomplete: '+name)
        return matches[0]
    def download(self,role,producer_name,destination,members,max_bytes):
        job=self.successful_job(producer_name)
        matches=[a for a in self.artifacts() if a['name']==self.artifact_name(role)]
        f.need(len(matches)==1,'required same-run artifact missing/duplicate: '+role);artifact=matches[0]
        f.need(artifact['expired'] is False and type(artifact['id']) is int and artifact['id']>0,'artifact expired/invalid')
        f.need(type(artifact['size_in_bytes']) is int and 0<artifact['size_in_bytes']<=max_bytes,'artifact transfer bound')
        digest=artifact.get('digest','');f.need(re.fullmatch(r'sha256:[0-9a-f]{64}',digest),'authoritative artifact digest missing')
        workflow=artifact.get('workflow_run',{})
        f.need(str(workflow.get('id'))==self.run_id and workflow.get('head_sha')==self.commit,'artifact run/commit mismatch')
        # Never forward the GitHub bearer token to the redirected signed storage URL.
        path=f'/repos/{REPOSITORY}/actions/artifacts/{artifact["id"]}/zip'
        try:
            response=self.opener.open(self.request(path),timeout=60)
        except urllib.error.HTTPError as error:
            f.need(error.code in (301,302,303,307,308),'artifact download API failed')
            url=error.headers.get('Location','');u=urllib.parse.urlsplit(url)
            f.need(u.scheme=='https' and u.hostname and not u.username and not u.password,'unsafe artifact redirect')
            try:
                response=urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'hierarchy-c-fresh-verifier'}),timeout=60)
            except Exception:
                raise f.Rejected('signed artifact storage request failed; URL suppressed') from None
        destination=Path(destination);f.no_symlink_path(destination);f.need(not destination.exists(),'artifact destination must be new')
        destination.mkdir(parents=True);archive=destination/'download.zip';h=hashlib.sha256();count=0
        with response,archive.open('xb') as handle:
            while True:
                block=response.read(1024**2)
                if not block:break
                count+=len(block);f.need(count<=max_bytes,'artifact ZIP exceeds transfer bound');h.update(block);handle.write(block)
        f.need(h.hexdigest()==digest[7:] and count==artifact['size_in_bytes'],'artifact ZIP digest/size mismatch')
        total=0
        with zipfile.ZipFile(archive) as z:
            infos=z.infolist();f.need(len(infos)==len(members) and {i.filename for i in infos}==set(members),'artifact ZIP member mismatch')
            for info in infos:
                f.safe_rel(info.filename);mode=info.external_attr>>16
                f.need(not info.is_dir() and not stat.S_ISLNK(mode) and not info.flag_bits&1,'unsafe ZIP member')
                total+=info.file_size;f.need(0<=info.file_size and total<=max_bytes,'ZIP expansion bound')
                out=destination/info.filename;f.no_symlink_path(out)
                with z.open(info) as src,out.open('xb') as dst:
                    copied=0
                    while True:
                        block=src.read(1024**2)
                        if not block:break
                        copied+=len(block);f.need(copied<=info.file_size,'overlong ZIP member');dst.write(block)
                    f.need(copied==info.file_size,'truncated ZIP member')
        archive.unlink() # Only this newly downloaded, verified temporary ZIP.
        return {'artifact_id':artifact['id'],'producer_job_id':job['id'],'producer_conclusion':'success',
                'artifact_zip_sha256':digest[7:]}
