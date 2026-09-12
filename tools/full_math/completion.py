"""Whole-plan evidence accounting. This is not a theorem prover.

Only actual Lean elaboration checks proofs. This module enforces scope, identity,
full task coverage, input generality declarations and links to executed tests.
No `mark-done`, allowlist of omitted mathematical goals, or demo-only success.
"""
from __future__ import annotations
from dataclasses import dataclass
from hashlib import sha256
from pathlib import Path, PurePosixPath
from typing import Any
import json, os, subprocess, re

HERE=Path(__file__).resolve().parent
SPEC=HERE/'spec'
PREFIX='FULL_MATH_ENV_JSON='
ALLOWED={'propext','Classical.choice','Quot.sound'}
NAME=re.compile(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*')

class EvidenceError(ValueError):pass

def unique_pairs(items):
    out={}
    for k,v in items:
        if k in out:raise EvidenceError('duplicate JSON key: '+k)
        out[k]=v
    return out

def loads(text):
    return json.loads(text,object_pairs_hook=unique_pairs,
                      parse_constant=lambda s: (_ for _ in ()).throw(EvidenceError('nonfinite JSON')))

def read(path):return loads(Path(path).read_text(encoding='utf-8'))
def digest(path):return sha256(Path(path).read_bytes()).hexdigest()
def dump(path,data):
    p=Path(path);p.parent.mkdir(parents=True,exist_ok=True)
    p.write_text(json.dumps(data,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')

def safe_file(repo:Path,rel:str)->Path:
    r=PurePosixPath(rel)
    if not rel or '\\' in rel or r.is_absolute() or any(x in ('..','.') for x in r.parts):
        raise EvidenceError('unsafe evidence path '+rel)
    p=repo/Path(*r.parts)
    if not p.is_file() or p.is_symlink() or repo.resolve() not in p.resolve().parents:
        raise EvidenceError('file missing or outside repository: '+rel)
    return p


def requirements(spec:Path=SPEC):
    scope=read(spec/'SCOPE.json');reqs=read(spec/'REQUIREMENTS.json')
    ids=[r['id'] for r in reqs];names=[r['theorem'] for r in reqs]
    if len(ids)!=217 or len(set(ids))!=217 or len(set(names))!=217:
        raise EvidenceError('full plan must retain 217 distinct mandatory registrations')
    if set(names)!=set(scope['all_required_names']):raise EvidenceError('scope and required declarations differ')
    target_ids={f'{p}{i:02d}' for p,n in [('F',14),('P',13),('N',10),('B',7),('G',5),('C',7)] for i in range(1,n+1)} | {'E01'}
    expected_ids=({'TARGET:'+s for s in target_ids}
        | {'EXT:EXT'+str(i).zfill(2) for i in range(1,10)}
        | {'DEMAND:D'+str(i).zfill(3) for i in range(1,135)}
        | {'GAP:X'+str(i).zfill(2) for i in range(1,11)}
        | {'ROOT:'+s for s in ['GENERIC_FINITE','SYMBOLIC_EXACT','STATISTICAL_COMPOSITION','CIVIL','CRIMINAL','ADMINISTRATIVE','DOCUMENT_DELIVERY']})
    if set(ids)!=expected_ids:raise EvidenceError('original scope IDs must not be replaced or relabeled')
    expected={'TARGET':57,'EXT':9,'DEMAND':134,'GAP':10,'ROOT':7}
    for typ,n in expected.items():
        if sum(x.startswith(typ+':') for x in ids)!=n:raise EvidenceError('scope category '+typ)
    if set(scope['proof_target_ids'])!={r['id'].split(':')[1] for r in reqs if r['id'].startswith('TARGET:')}:
        raise EvidenceError('lost original mathematical target')
    if scope['terminal_state']!='MATH_BUILD_COMPLETE' or scope['decision']!='MATH_FIRST_COMPLETE_THEN_PRODUCTION':
        raise EvidenceError('changed execution contract')
    return scope,reqs


def validate_binding(row:dict,required:dict,repo:Path|None=None):
    if not isinstance(row,dict) or row.get('id')!=required['id']:raise EvidenceError('binding identity')
    for key in ('theorem','contract'):
        if row.get(key)!=required[key] or not NAME.fullmatch(row[key]):raise EvidenceError('binding '+key)
    if row.get('proof_mode')!='KERNEL_CONTRACT_PROOF':
        raise EvidenceError('fixed example or cross-check is not a full-plan proof: '+row['id'])
    for key in ('formal_scope','independent_semantics','algorithm','observation_contract','external_assumptions'):
        if not isinstance(row.get(key),str) or not row[key].strip():raise EvidenceError('missing concrete '+key)
    if row.get('scope_restriction') in ('FROZEN_INPUT','DEMO_ONLY','TWO_FIXED_SCENARIOS') and required['id'] not in {'TARGET:F08','TARGET:F13','TARGET:N04'}:
        raise EvidenceError('frozen case cannot close full mathematical requirement')
    for key in ('proof_sources','implementation_sources','test_ids','negative_test_ids','semantic_links'):
        v=row.get(key)
        if not isinstance(v,list) or not v or len(set(v))!=len(v) or any(not isinstance(x,str) or not x for x in v):
            raise EvidenceError('missing/duplicate '+key+': '+row['id'])
    if set(row['test_ids']) & set(row['negative_test_ids']):raise EvidenceError('positive and adverse tests are distinct')
    if repo:
        for k in ('proof_sources','implementation_sources'):
            for f in row[k]:safe_file(repo,f)
    # The source descriptions still require semantic review; this is not a proof of their truth.


def binding_inventory(path:Path,spec:Path=SPEC,repo:Path|None=None):
    _,req=requirements(spec);expected={r['id']:r for r in req}
    obj=read(path) if path.exists() else {'bindings':[]}
    rows=obj.get('bindings',[]) if isinstance(obj,dict) else []
    if not isinstance(rows,list):raise EvidenceError('bindings must be list')
    found={};errors=[]
    for x in rows:
        try:
            key=x.get('id') if isinstance(x,dict) else None
            if key not in expected or key in found:raise EvidenceError('unknown/duplicate binding '+str(key))
            validate_binding(x,expected[key],repo);found[key]=x
        except EvidenceError as e:errors.append(str(e))
    return found,sorted(set(expected)-set(found)),errors


def source_manifest(repo:Path,bindings:dict,spec:Path=SPEC):
    paths=set()
    for b in bindings.values():paths.update(b['proof_sources']);paths.update(b['implementation_sources'])
    # Audit source and frozen completion semantics themselves are part of evidence.
    for p in spec.glob('*.json'):
        if repo.resolve() in p.resolve().parents:paths.add(p.relative_to(repo).as_posix())
    files=[]
    for rel in sorted(paths):files.append({'path':rel,'sha256':digest(safe_file(repo,rel))})
    return files


def identity(repo:Path,github_required=False):
    if github_required and os.environ.get('GITHUB_ACTIONS')!='true':raise EvidenceError('final mathematical receipt must use actual GitHub run')
    def git(*aa):return subprocess.run(['git',*aa],cwd=repo,check=True,text=True,capture_output=True).stdout.strip()
    commit=git('rev-parse','HEAD');tree=git('rev-parse','HEAD^{tree}')
    if os.environ.get('GITHUB_SHA') and commit!=os.environ['GITHUB_SHA']:raise EvidenceError('GitHub subject mismatch')
    base=repo/'proofs/lean/juris_lean'
    return {'commit':commit,'tree':tree,'repository':os.environ.get('GITHUB_REPOSITORY','LOCAL'),
            'run_id':os.environ.get('GITHUB_RUN_ID','LOCAL'),'attempt':os.environ.get('GITHUB_RUN_ATTEMPT','LOCAL'),
            'lean_toolchain_sha256':digest(base/'lean-toolchain'),'lake_manifest_sha256':digest(base/'lake-manifest.json')}


def check_identity(a,b):
    for k in ('commit','tree','repository','run_id','attempt','lean_toolchain_sha256','lake_manifest_sha256'):
        if not a.get(k) or a.get(k)!=b.get(k):raise EvidenceError('evidence from another subject/run: '+k)


def parse_compiled(text:str):
    lines=[x[len(PREFIX):] for x in text.splitlines() if x.startswith(PREFIX)]
    if len(lines)!=1:raise EvidenceError('exactly one Lean compiled-environment output required')
    obj=loads(lines[0])
    if not isinstance(obj,list) or not obj:raise EvidenceError('empty compiled evidence')
    seen={}
    for r in obj:
        n=r.get('name') if isinstance(r,dict) else None
        if not n or n in seen:raise EvidenceError('duplicate/absent compiled name')
        if r.get('kind')!='theorem':raise EvidenceError('definition/import cannot satisfy theorem evidence')
        axs=r.get('axioms');deps=r.get('dependencies');typ=r.get('type')
        if not isinstance(axs,list) or set(axs)-ALLOWED:raise EvidenceError('unapproved axiom '+str(n))
        if not isinstance(deps,list) or not isinstance(typ,str) or not typ:raise EvidenceError('type/dependency evidence missing')
        seen[n]=r
    return seen


def dependency_closure(name,records):
    seen=set();pending=[name]
    while pending:
        n=pending.pop()
        for d in records.get(n,{}).get('dependencies',[]):
            if d not in seen:seen.add(d);pending.append(d)
    return seen


def evaluate_full_plan(spec:Path,bindings_path:Path,compiled:dict,tests:dict,
                       source_records:list,expected_subject:dict,repo:Path|None=None):
    scope,req=requirements(spec);bindings,missing,errors=binding_inventory(bindings_path,spec,repo)
    if missing or errors:return {'status':'INCOMPLETE','missing_bindings':missing,'errors':errors}
    check_identity(compiled.get('subject',{}),expected_subject)
    check_identity(tests.get('subject',{}),expected_subject)
    records=parse_compiled(compiled.get('log',''))
    t=tests.get('tests')
    if tests.get('status')!='PASS' or not isinstance(t,list) or not t:raise EvidenceError('test run absent or failed')
    testmap={}
    for x in t:
        if x.get('id') in testmap:raise EvidenceError('duplicate test result')
        testmap[x.get('id')]=x
    if any(x.get('status')!='PASS' for x in t):raise EvidenceError('failed/error/skipped test cannot complete math profile')
    files={}
    for row in source_records:
        if row['path'] in files:raise EvidenceError('duplicate source record')
        files[row['path']]=row['sha256']
        if repo and digest(safe_file(repo,row['path']))!=row['sha256']:raise EvidenceError('source changed since verification')
    for r in req:
        b=bindings[r['id']];name=r['theorem'];c=r['contract']
        if name not in records:errors.append('UNCOMPILED:'+r['id']);continue
        rec=records[name]
        if rec.get('contract')!=c or rec.get('typecheck')!='LEAN_ASSIGNMENT_ELABORATED':errors.append('TYPE_NOT_CHECKED:'+r['id'])
        if r['id'].startswith('ROOT:') and b.get('generality')!='PARAMETRIC':errors.append('FIXED_PROOF:'+r['id'])
        for tid in b['test_ids']+b['negative_test_ids']:
            if tid not in testmap or testmap[tid].get('status')!='PASS':errors.append('MISSING_TEST:'+r['id']+':'+tid)
        for f in b['proof_sources']+b['implementation_sources']:
            if f not in files:errors.append('UNBOUND_SOURCE:'+f)
        closure=dependency_closure(name,records)
        if not set(b['semantic_links']) & closure:errors.append('SEMANTIC_LINK_NOT_IN_PROOF:'+r['id'])
        if r['id']=='TARGET:C07':
            roots={x['theorem'] for x in req if x['id'].startswith('ROOT:')}
            if not roots<=closure:errors.append('UNIFIED_ROOTS_NOT_CONNECTED:'+','.join(sorted(roots-closure)))
        if r['id']=='EXT:EXT09':
            domain_roots={'JurisLean.FullMath.Acceptance.root_'+n for n in ('CIVIL','CRIMINAL','ADMINISTRATIVE')}
            if not domain_roots<=closure:errors.append('THREE_DOMAIN_ROOTS_NOT_CONNECTED')
        if r['id'].startswith('ROOT:'):
            # Narrow static screen supplements, never replaces, contract review.
            if any(s in rec['type'] for s in ['selectedInput','rootInput','frozen_main','DEMO-PRINCIPAL']):errors.append('FROZEN_ROOT_SIGNATURE:'+r['id'])
    if errors:return {'status':'INCOMPLETE','missing_bindings':[], 'errors':sorted(set(errors))}
    return {'status':'MATH_BUILD_COMPLETE','subject':expected_subject,'scope':'ALL_DECLARED_FORMAL_PARTS_OF_ORIGINAL_PLAN',
            'target_count':57,'extension_count':9,'business_requirement_count':134,
            'gap_formal_count':10,'general_roots':7,'mandatory_registrations':217,
            'not_established':['actual_JC_Harness_integration','E01_real_data_validation','truth_of_external_facts','unrestricted_natural_language_or_entire_legal_system'],
            'original_external_tasks_status':'PRESERVED_NOT_CLOSED_BY_MATH','source_files':len(files),
            'evidence_type':'Lean kernel proofs of declared contracts plus current reference tests; not kernel proof of CPython'}
