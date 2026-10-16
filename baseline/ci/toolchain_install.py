#!/usr/bin/env python3
"""Install only the pinned official release and derive a canonical inventory.

No network access, credential access, project objects, or pre-existing runtime is
used. The caller downloads the official release and bounds this preparatory job.
"""
from __future__ import annotations
import argparse,hashlib,json,os,posixpath,shutil,stat,subprocess,tarfile
from pathlib import Path,PurePosixPath
import fresh_stage as f
PREFIX='lean-4.35.0-rc2-linux'
MAX_UNPACKED=5*1024**3
MAX_FILES=100000

def relative_member(name,prefix):
    name=name.rstrip('/')
    f.need(name==prefix or name.startswith(prefix+'/'),'toolchain member outside expected root')
    if name==prefix:return ''
    rel=name[len(prefix)+1:]
    return f.safe_rel(rel)

def safe_link_target(relative,target):
    f.need(target and not target.startswith('/') and '\\' not in target and '\x00' not in target,
           'absolute or malformed toolchain symlink')
    resolved=posixpath.normpath(posixpath.join(posixpath.dirname(relative),target))
    f.safe_rel(resolved)
    return resolved

def install_archive(archive,destination,*,expected_hash=f.TOOLCHAIN_SHA256,prefix=PREFIX,
                    max_unpacked=MAX_UNPACKED,max_files=MAX_FILES):
    archive=Path(archive).absolute();destination=Path(destination).absolute()
    f.no_symlink_path(archive);f.no_symlink_path(destination)
    f.need(archive.is_file() and f.file_sha(archive)==expected_hash,'official toolchain archive SHA256 mismatch')
    f.need(not destination.exists(),'runtime destination must be new')
    f.need(shutil.disk_usage(destination.parent).free>=max_unpacked+256*1024**2,
           'insufficient measured disk for bounded runtime extraction')
    destination.mkdir()
    files={};links={};hardlinks={};seen=set();total=0;count=0
    # A verified archive is decompressed by the system zstd package, never a submitted executable.
    with subprocess.Popen(['/usr/bin/zstd','--decompress','--quiet','--stdout',str(archive)],
                          stdin=subprocess.DEVNULL,stdout=subprocess.PIPE,stderr=subprocess.PIPE) as child:
        try:
            with tarfile.open(fileobj=child.stdout,mode='r|') as tf:
                for member in tf:
                    rel=relative_member(member.name,prefix)
                    if not rel:
                        f.need(member.isdir(),'toolchain root is not directory');continue
                    f.need(rel not in seen,'duplicate toolchain member');seen.add(rel);count+=1
                    f.need(count<=max_files,'too many toolchain members')
                    f.need(not member.mode & 0o6000,'setuid/setgid toolchain member forbidden')
                    out=destination/rel;f.no_symlink_path(out)
                    if member.isdir():out.mkdir(parents=True,exist_ok=True);continue
                    out.parent.mkdir(parents=True,exist_ok=True);f.no_symlink_path(out.parent)
                    if member.issym():
                        safe_link_target(rel,member.linkname);links[rel]=member.linkname
                    elif member.islnk():
                        target=relative_member(member.linkname,prefix)
                        f.need(bool(target),'invalid hardlink target');hardlinks[rel]=target
                    else:
                        f.need(member.isreg() and not member.sparse,'unsupported toolchain archive member')
                        total+=member.size;f.need(0<=member.size and total<=max_unpacked,'toolchain expansion byte limit')
                        reader=tf.extractfile(member);f.need(reader is not None,'missing toolchain payload')
                        h=hashlib.sha256();copied=0
                        with out.open('xb') as handle:
                            while True:
                                block=reader.read(1024**2)
                                if not block:break
                                copied+=len(block);f.need(copied<=member.size,'overlong toolchain payload')
                                h.update(block);handle.write(block)
                        f.need(copied==member.size,'truncated toolchain payload')
                        mode=member.mode & 0o777;os.chmod(out,mode)
                        files[rel]={'bytes':copied,'sha256':h.hexdigest(),'mode':mode}
            error=child.stderr.read(65537)
            f.need(len(error)<=65536 and child.wait(timeout=30)==0,'toolchain decompression failed')
        finally:
            if child.poll() is None:child.kill();child.wait(timeout=10)
    # Materialize hard links only after all regular targets are validated.
    while hardlinks:
        ready=[name for name,target in hardlinks.items() if target in files]
        f.need(bool(ready),'unresolved/cyclic toolchain hardlinks')
        for name in ready:
            target=hardlinks.pop(name);out=destination/name;f.no_symlink_path(destination/target)
            total+=files[target]['bytes'];f.need(total<=max_unpacked,'hardlink logical byte limit')
            os.link(destination/target,out);files[name]=dict(files[target])
    # Symlinks are last: no archive file can write through an earlier symlink.
    for name,target in links.items():
        f.need(not (destination/name).exists(),'toolchain symlink shadows an existing path')
        os.symlink(target,destination/name)
    for name in links:
        f.need((destination/name).resolve(strict=True).is_relative_to(destination),
               'toolchain symlink target escapes/missing')
    for executable in ('lean','lake','leanchecker','leanexport','nanoda_bin','con-ron'):
        f.need('bin/'+executable in files and os.access(destination/'bin'/executable,os.X_OK),
               'official archive missing required checker executable')
    return {'schema':'official-lean-release-inventory-v1','archive_sha256':expected_hash,
            'archive_prefix':prefix,'logical_file_bytes':total,'files':dict(sorted(files.items())),
            'symlinks':dict(sorted(links.items()))}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--archive',type=Path,required=True);p.add_argument('--destination',type=Path,required=True)
    p.add_argument('--inventory',type=Path,required=True)
    args=p.parse_args();f.no_symlink_path(args.inventory);f.need(not args.inventory.exists(),'inventory output must be new')
    inventory=install_archive(args.archive,args.destination)
    args.inventory.write_bytes(f.json_bytes(inventory))
    print(json.dumps({'archive_sha256':f.TOOLCHAIN_SHA256,'inventory_sha256':f.file_sha(args.inventory),
                      'files':len(inventory['files']),'symlinks':len(inventory['symlinks']),
                      'logical_file_bytes':inventory['logical_file_bytes']}))

if __name__=='__main__':main()
