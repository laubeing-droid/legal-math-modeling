#!/usr/bin/env python3
"""Validate consolidation coverage, never execute Lean or claim mathematical closure."""
from pathlib import Path
import argparse, hashlib, json

ROOT=Path(__file__).resolve().parents[1]

def load(p):return json.loads(Path(p).read_text(encoding='utf-8'))
def require(v,msg):
    if not v: raise ValueError(msg)

def check_dag(tasks):
    by={t['id']:t for t in tasks}
    require(len(by)==len(tasks),'Duplicate task ID')
    visited=set();active=set()
    def visit(k):
        require(k in by,'Missing dependency '+k)
        if k in visited:return
        require(k not in active,'Cyclic dependency '+k)
        active.add(k)
        for dep in by[k].get('depends_on',[]):visit(dep)
        active.remove(k);visited.add(k)
    for k in by:visit(k)
    return by

def validate(plan_dir, repo=None):
    p=Path(plan_dir)
    current=load(p/'TASKS.json'); tasks=current['tasks'];by=check_dag(tasks)
    base=load(p/'V21_TASKS_ORIGINAL.json')['tasks']
    require(len(base)==34,'Original 25+9 task count')
    require(all(t['id'] in by for t in base),'Dropped original task')
    for t in base:
        for key in ['title','actions','acceptance','proof_targets','depends_on']:
            if key in t:require(by[t['id']].get(key)==t[key],f'Original task silently changed {t["id"]}.{key}')
    require({f'T{i:02d}' for i in range(25)} <= set(by),'Original T00–24 not complete')
    require({f'REV{i:02d}' for i in range(1,10)} <= set(by),'Missing REV')
    require({f'EXT{i:02d}' for i in range(1,10)} <= set(by),'Missing EXT')
    require({f'ROOT{i:02d}' for i in range(1,9)} <= set(by),'Missing root obligation')
    require({f'BRFIX-{i:02d}' for i in range(1,7)} <= set(by),'Missing latest BRFIX')
    require(len(tasks)==57,'Unexpected total task count')
    reqs=load(p/'REQUIREMENTS_134.json');orig=load(p/'FORMALIZATION_134_ORIGINAL.json')
    rq={r['requirement_id']:r for r in reqs}
    require(len(reqs)==134 and set(rq)=={f'D{i:03d}' for i in range(1,135)},'Requirement ID/count mismatch')
    for r in orig:
        n=rq[r['requirement_id']]
        require(all(n.get(k)==v for k,v in r.items()),'Original requirement modified '+r['requirement_id'])
        require(len(n['seven_axis_obligations'])==7,'Missing BR axis')
        require(n['proof_status']=='OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED','Unsupported requirement closure')
        require(n['task_ids'] and set(n['task_ids'])<=set(by),'Unknown/unassigned task for '+r['requirement_id'])
    b=load(p/'BENCHMARKS_20.json')
    require(len(b)==20 and {r['benchmark_id'] for r in b}==({f'CN{i:02d}' for i in range(1,16)}|{f'US{i:02d}' for i in range(1,6)}),'15CN+5US count changed')
    require(len(load(p/'GAPS_10_ORIGINAL.json'))==10,'Gaps dropped')
    require(len(load(p/'PROOF_FAMILIES_16.json'))==16,'Families dropped')
    require(len(load(p/'PROOF_TARGETS_57.json'))==57,'Original proof targets dropped')
    require(len(load(p/'ORIGINAL_REQUIREMENTS_26.json'))==26,'Original requirements dropped')
    seeds=load(p/'LEAN_SEEDS_84.json')['declarations']
    require(len(seeds)==84 and len({r['name'] for r in seeds})==84,'Source seed inventory mismatch')
    require(all(r['status']=='SOURCE_DRAFT_CI_NOT_RUN' for r in seeds),'Inventory pretends to be compile evidence')
    if repo:
        repo=Path(repo)
        for item in load(p/'RETAINED_SOURCE_LOCK.json'):
            f=repo/item['path']
            require(f.is_file() and hashlib.sha256(f.read_bytes()).hexdigest()==item['sha256'],'Retained source mismatch '+item['path'])
    return {'status':'PASS','scope':'PLAN_IDENTITIES_AND_RETAINED_SOURCE_ONLY','tasks':57,'base_tasks':34,'requirements':134,'proof_targets':57,'families':16,'gaps':10,'cn_benchmarks':15,'us_related_benchmarks':5,'seed_names':84,'root_proof':'NOT_ESTABLISHED_BY_THIS_CHECK','remote_ci':'NOT_RUN_BY_THIS_CHECK'}

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--plan-dir',type=Path,default=ROOT/'plans');ap.add_argument('--repo-root',type=Path);ap.add_argument('--output',type=Path)
    a=ap.parse_args()
    try:out=validate(a.plan_dir,a.repo_root)
    except (ValueError,KeyError,TypeError,OSError) as e:out={'status':'FAIL','error':str(e)}
    s=json.dumps(out,ensure_ascii=False,indent=2)+'\n';print(s)
    if a.output:a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(s,encoding='utf-8')
    raise SystemExit(0 if out['status']=='PASS' else 1)
