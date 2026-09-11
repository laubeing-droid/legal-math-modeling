"""Small same-run evidence checks; ordinary hashes, not signatures or truth claims."""
from __future__ import annotations
from hashlib import sha256
from pathlib import Path,PurePosixPath
import json,os,subprocess

IDENTITY_FIELDS=('repository','commit','tree','run_id','run_attempt','toolchain_sha256','manifest_sha256')
ALLOWED_AXIOMS={'propext','Classical.choice','Quot.sound'}
REQUIRED=(
 'full_binding_exact','full_binding_refuses_change','read_write_doc',
 'read_write_calculation','seven_axis_business_root','full_projection_accepts_normal',
 'wrong_selected_input_rejected','changed_doc_metadata_rejected','changed_json_metadata_rejected',
 'wrong_debtor_rejected','wrong_threshold_rejected','wrong_action_grid_rejected',
 'wrong_case_rejected','selected_numerical_correspondence','accepted_root_has_original_input',
 'input_model_preserved','input_sources_preserved','duplicate_world_positions_rejected')
PREFIX='JurisLean.BusinessRoot.SevenAxis.'


def verify_environment(text: str) -> dict:
    lines=[x.split('=',1)[1] for x in text.splitlines() if x.startswith('SEVEN_AXIS_COMPILED_ENV_JSON=')]
    if len(lines)!=1:raise ValueError('Exactly one actual environment record required')
    rows=json.loads(lines[0]);names=set();byname={}
    if type(rows) is not list or not rows:raise ValueError('Empty declaration set')
    for row in rows:
        n=row.get('name');a=row.get('axioms');d=row.get('proof_dependencies')
        if type(n) is not str or not n.startswith(PREFIX) or n in names:raise ValueError('Declaration identity')
        if type(a) is not list or any(type(x) is not str for x in a) or set(a)-ALLOWED_AXIOMS:raise ValueError('Axiom policy')
        if type(d) is not list or any(type(x) is not str for x in d):raise ValueError('Dependency data')
        names.add(n);byname[n]=row
    missing={PREFIX+n for n in REQUIRED}-names
    if missing:raise ValueError('Missing required statements '+str(sorted(missing)))
    root=byname[PREFIX+'seven_axis_business_root']
    if not {'JurisLean.BusinessRoot.root_worlds_match','JurisLean.BusinessRoot.root_joint_sem',
            'JurisLean.BusinessRoot.root_task_sat'}<=set(root['proof_dependencies']):
        raise ValueError('Concrete numerical root obligations disconnected')
    return {'status':'PASS','declared_count':len(rows),'required_count':len(REQUIRED),
            'scope':'KERNEL_CHECKED_TYPED_FIXED_INPUT_ROOT_ONLY',
            'python_refinement':'CROSS_CHECK_ONLY','byte_parser':'TCB_NOT_KERNEL_PROVED'}


def identity(repo: Path) -> dict:
    def git(*args):return subprocess.run(['git',*args],cwd=repo,capture_output=True,text=True,check=True).stdout.strip()
    b=repo/'proofs/lean/juris_lean'
    commit=git('rev-parse','HEAD');expected=os.environ.get('GITHUB_SHA')
    if expected and expected!=commit:raise ValueError('Checkout does not match this workflow subject')
    return {'repository':os.environ.get('GITHUB_REPOSITORY','LOCAL'), 'commit':commit,
            'tree':git('rev-parse','HEAD^{tree}'),'run_id':os.environ.get('GITHUB_RUN_ID','LOCAL'),
            'run_attempt':os.environ.get('GITHUB_RUN_ATTEMPT','LOCAL'),
            'toolchain_sha256':sha256((b/'lean-toolchain').read_bytes()).hexdigest(),
            'manifest_sha256':sha256((b/'lake-manifest.json').read_bytes()).hexdigest()}


def bundle_receipt(root: Path,subject:dict,kind:str) -> dict:
    files=[]
    for p in sorted(root.rglob('*')):
        if p.is_file() and p.name!='receipt.json':
            if p.is_symlink():raise ValueError('Evidence symlink')
            files.append({'path':p.relative_to(root).as_posix(),'sha256':sha256(p.read_bytes()).hexdigest()})
    if not files:raise ValueError('No actual evidence')
    return {'schema':'ulm/audit-repair-evidence/1','kind':kind,'status':'PASS',
            'subject':subject,'files':files}


def verify_receipt(root:Path,receipt:dict,subject:dict,kind:str) -> None:
    if receipt.get('status')!='PASS' or receipt.get('kind')!=kind:raise ValueError('Evidence status/kind')
    if any(receipt.get('subject',{}).get(k)!=subject.get(k) or not subject.get(k) for k in IDENTITY_FIELDS):
        raise ValueError('Cross-run/attempt/tree/toolchain evidence')
    entries=receipt.get('files');seen=set()
    if type(entries) is not list or not entries:raise ValueError('Empty evidence')
    for row in entries:
        rel=PurePosixPath(row['path'])
        if rel.is_absolute() or '..' in rel.parts or '\\' in row['path'] or row['path'] in seen:raise ValueError('Evidence path')
        seen.add(row['path']);p=root/Path(*rel.parts)
        if p.is_symlink() or not p.is_file() or sha256(p.read_bytes()).hexdigest()!=row['sha256']:
            raise ValueError('Evidence bytes changed')
    actual={p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file() and p.name!='receipt.json'}
    if actual!=seen:raise ValueError('Evidence file-set mismatch')


def verify_jobs(needs: dict,required: set[str]) -> None:
    if not required<=set(needs):raise ValueError('Missing upstream job')
    if any(needs[n].get('result')!='success' for n in required):raise ValueError('Unsuccessful upstream job')


def flatten_without_overwrite(source:Path,target:Path) -> None:
    """Compatibility for old release scripts. Never overwrite a same-name file.

    Same-name files with identical bytes may be deduplicated. Different bytes
    are a visible conflict. Strong seven-axis receipts stay in separate folders.
    """
    import shutil
    target.mkdir(parents=True,exist_ok=True)
    for p in sorted(source.rglob('*')):
        if not p.is_file():continue
        if p.is_symlink():raise ValueError('Artifact symlink')
        d=target/p.name
        if d.exists():
            if d.read_bytes()!=p.read_bytes():raise ValueError('Artifact filename collision '+p.name)
        else:shutil.copy2(p,d)
