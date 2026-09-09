#!/usr/bin/env python3
"""Install a reviewed overlay only. Default is a no-write preview.
Never invokes git, pip, Lean, Elan, Lake, a network service, or a model.
Refuses unknown local modifications; preserves a recoverable content backup.
"""
from pathlib import Path, PurePosixPath
import argparse, hashlib, json, os, shutil, sys, uuid

PACKAGE=Path(__file__).resolve().parent

def digest(data):return hashlib.sha256(data).hexdigest()
def require(v,msg):
    if not v:raise ValueError(msg)

def safe_path(root,relative):
    p=PurePosixPath(relative)
    require(not p.is_absolute() and '..' not in p.parts and '\\' not in relative and ':' not in relative,'UNSAFE_PATH '+relative)
    require(bool(p.parts),'EMPTY_PATH')
    target=root.joinpath(*p.parts)
    cur=root
    require(not root.is_symlink(),'SYMLINK_ROOT')
    for part in p.parts:
        cur=cur/part
        require(not cur.is_symlink(),'SYMLINK_PATH '+relative)
    return target

def plan(package,repo,role):
    package=Path(package);repo=Path(repo)
    require(repo.is_dir(),'Repository path must already exist')
    require(not repo.is_symlink(),'SYMLINK_ROOT')
    repo=repo.resolve()
    manifest=json.loads((package/'PAYLOAD_MANIFEST.json').read_text(encoding='utf-8'))
    require(role in manifest['roles'],'UNKNOWN_ROLE')
    overlay=package/'overlays'/role
    rows=manifest['roles'][role];seen=set();output=[]
    for r in rows:
        rel=r['path'];require(rel not in seen,'DUPLICATE_PATH');seen.add(rel)
        src=safe_path(overlay,rel);dst=safe_path(repo,rel)
        require(src.is_file(),'MISSING_PAYLOAD '+rel)
        require(digest(src.read_bytes())==r['sha256'],'PAYLOAD_HASH_MISMATCH '+rel)
        if dst.exists():
            require(dst.is_file(),'TARGET_NOT_FILE '+rel)
            old=digest(dst.read_bytes())
            if old==r['sha256']:mode='unchanged'
            elif old in r.get('reviewed_overwrite_sha256',[]):mode='reviewed_replace'
            else:raise ValueError('UNKNOWN_LOCAL_MODIFICATION '+rel+'; review the diff before changing reviewed hashes; no force mode')
        else:mode='create';old=None
        output.append({'path':rel,'action':mode,'old_sha256':old,'new_sha256':r['sha256']})
    return output

def install(package,repo,role,apply=False):
    package=Path(package);repo=Path(repo)
    rows=plan(package,repo,role)
    if not apply:return {'mode':'PREVIEW_NO_WRITES','role':role,'files':rows}
    repo=repo.resolve();work=safe_path(repo,'work/ulm-consolidated-install')
    work.mkdir(parents=True,exist_ok=True);txn=work/uuid.uuid4().hex;txn.mkdir()
    changes=[]
    try:
        # Preflight already checked the entire overlay. Recheck each write against concurrent changes.
        for r in rows:
            if r['action']=='unchanged':continue
            target=safe_path(repo,r['path']);src=safe_path(package/'overlays'/role,r['path'])
            require(digest(src.read_bytes())==r['new_sha256'],'PAYLOAD_CHANGED_DURING_INSTALL')
            if r['old_sha256'] is None:require(not target.exists(),'TARGET_APPEARED_DURING_INSTALL')
            else:require(target.is_file() and digest(target.read_bytes())==r['old_sha256'],'TARGET_CHANGED_DURING_INSTALL')
            backup=None
            if target.exists():
                backup=txn/'before'/r['path'];backup.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(target,backup)
            target.parent.mkdir(parents=True,exist_ok=True)
            staged=target.with_name('.'+target.name+'.ulm-'+uuid.uuid4().hex)
            staged.write_bytes(src.read_bytes());changes.append((target,backup))
            os.replace(staged,target)
        result={'mode':'APPLIED','role':role,'files':rows,'backup':str(txn),'no_remote_actions':True}
    except Exception:
        for target,backup in reversed(changes):
            if backup is not None:shutil.copy2(backup,target)
            elif target.exists():target.unlink()
        raise
    (txn/'receipt.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    return result

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--role',choices=['lmm','jc','harness'],default='lmm');ap.add_argument('--apply',action='store_true');a=ap.parse_args()
    try:print(json.dumps(install(PACKAGE,a.repo,a.role,a.apply),ensure_ascii=False,indent=2))
    except (ValueError,OSError,KeyError) as e:print(str(e),file=sys.stderr);raise SystemExit(1)
