#!/usr/bin/env python3
"""Run retained regressions + revised reference code. NO Lean subprocesses."""
import argparse,datetime,json,platform,subprocess,sys,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from v21.demo import main_demo,law_slice_demos
from v21.joint import JointInput,evaluate_joint,check_joint
from v21.checker import DungProblem
from v21.context import synthetic_context
from v21.model_binding import bind_synthetic_model,BoundObservation
from reference.core import Node
from fractions import Fraction as Q

def flatten(s):
    for x in s:
        if isinstance(x,unittest.TestSuite):yield from flatten(x)
        else:yield x.id()
def concrete_joint():
    c=synthetic_context(target='recognition_weight_to_lawful_settlement')
    model=bind_synthetic_model(c,(Node('A',('yes','no'),(),{():(Q(1,2),Q(1,2))}),
       Node('E',('yes','no'),('A',),{('yes',):(Q(4,5),Q(1,5)),('no',):(Q(1,5),Q(4,5))})))
    obs=(BoundObservation(c,'e1','source-family-1','source-snapshot-1','E','yes'),)
    d=JointInput(c,DungProblem(('entitled',),frozenset(),'grounded'),frozenset({'entitled'}),model,obs,'A','yes',
       (Q(100),Q(40),Q(5),Q(4),Q(1,2),Q(1,2),Q(80)),tuple(Q(x) for x in (60,64,66,68,70,72)),
       'SYNTHETIC_STIPULATED_LAWFUL_GRID')
    r=evaluate_joint(d)
    if not check_joint(d,r):raise AssertionError('Concrete independent joint check failed')
    return r

def run_case_main(args) -> int:
    """v3 main-chain entry (J.13.1): --case + --policy.  Without --case
    the legacy regression entry runs unchanged."""
    sys.path.insert(0, str(ROOT.parents[1]))  # repo root: theory/ lives there
    from theory.spec.canonical_v2.case import (
        AdmissionBasis, BasisKind, CaseInput, Claim, FactRecord,
        FactStanding, LegalEnvironment, Polar, ProcessState, ScopedAtom,
    )
    from theory.spec.canonical_v2.kernel import (
        Jurisdiction, JurisdictionRoute, NormState,
    )
    from unified.pipeline import run_case
    from reference.legal_semantics import check_case_run

    def _atom(predicate, polar):
        return ScopedAtom(case_id='case-1', subject='D', issue='loan', stage='trial',
                          predicate=predicate, polar=getattr(Polar, polar))

    case_doc = json.loads(Path(args.case).read_text(encoding='utf-8'))
    policy_doc = json.loads(Path(args.policy).read_text(encoding='utf-8')) if args.policy else {}
    facts = tuple(
        FactRecord(
            fact_id=row['id'],
            proposition=_atom(row['predicate'], row.get('polar', 'POS')),
            standing=getattr(FactStanding, row.get('standing', 'ADMITTED_POSITIVE')),
            produced_at=row.get('produced_at', 0),
            known_at=row.get('known_at', 0),
        )
        for row in case_doc.get('facts', [])
    )
    claims = tuple(
        Claim(c['id'], c['claimant'], c['respondent'], c['basis'],
              c.get('object', 'money'), c.get('remedy', 'payment'))
        for c in case_doc.get('claims', ())
    ) or (Claim('c1', 'C', 'D', case_doc.get('issue', 'loan'), 'money', 'payment'),)
    bases = tuple(
        AdmissionBasis(b['id'], getattr(BasisKind, b['kind']), b['issue'],
                       b.get('subject', 'C'), b.get('stage', 'trial'),
                       b.get('version', 'v1'),
                       premise_refs=tuple(b.get('premises', ())),
                       block_refs=tuple(b.get('blocks', ())))
        for b in policy_doc.get('admission_bases', ())
    )
    env = LegalEnvironment(
        environment_id=policy_doc.get('env_id', 'env-1'),
        jurisdiction=Jurisdiction(route=JurisdictionRoute.MAINLAND),
        admission_bases=bases,
    )
    case = CaseInput(
        case_id=case_doc.get('case_id', 'case-1'),
        initial_state=ProcessState(r=NormState(relations=()),
                                   environment_id=env.environment_id),
        parties=tuple(case_doc.get('parties', ('C', 'D'))),
        issues=(case_doc.get('issue', 'loan'),),
        claims=claims,
        defenses=(),
        fact_records=facts,
        evidence_records=(),
        questions=(),
        quantities=(),
    )
    run = run_case(case, env)
    check = check_case_run(case, env, run)
    payload = {
        'schema': 'unified-v3-case-run/1',
        'case_id': run.case_id,
        'status': run.status.value,
        'branches': [
            {
                'selection': sorted(b.selection),
                'extension': sorted(b.extension),
                'standards': [
                    {'claim': s.claim, 'civil_high': s.civil_high,
                     'live_counters': list(s.live_counters)} for s in b.standards
                ],
                'finalizations': [
                    {'claim': f.claim, 'judgment': f.judgment.value, 'basis': f.basis.value}
                    for f in b.finalizations
                ],
            }
            for b in run.branches
        ],
        'pending': list(run.pending),
        'failures': list(run.failures),
        'independent_check': {'ok': check.ok, 'reasons': list(check.reasons)},
        'lean': 'CI_NOT_RUN', 'empirical': 'SYNTHETIC_ONLY',
    }
    args.output.write_text(
        json.dumps(payload, ensure_ascii=False, indent=2, default=str) + '\n',
        encoding='utf-8',
    )
    print(json.dumps({'status': payload['status'],
                      'independent_check_ok': check.ok}))
    return 0 if check.ok else 1


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--output',type=Path,required=False)
    p.add_argument('--case',type=Path,help='v3 case JSON (J.13.1 main chain)')
    p.add_argument('--policy',type=Path,help='policy JSON with admission bases')
    p.add_argument('--events',type=Path,help='events JSONL (reserved)')
    p.add_argument('--check-only',type=Path,help='re-check a stored v3 result (reserved)')
    p.add_argument('--resume',type=Path,help='resume from a stored input (reserved)')
    a=p.parse_args()
    if a.case:
        if a.output is None:
            p.error('--output is required with --case')
        return run_case_main(a)
    if a.output is None:
        p.error('--output is required')
    out=a.output;out.mkdir(parents=True,exist_ok=True)
    suite=unittest.defaultTestLoader.discover(str(ROOT/'tests'));ids=list(flatten(suite))
    (out/'collection.json').write_text(json.dumps(ids,indent=2)+'\n',encoding='utf-8')
    with (out/'tests.log').open('w',encoding='utf-8') as stream:
        result=unittest.TextTestRunner(stream=stream,verbosity=2).run(suite)
    status='PASS' if result.wasSuccessful() and not result.skipped and result.testsRun==len(ids) and ids else 'FAIL'
    demos={}
    if status=='PASS':
        try:demos={'standalone':main_demo(),'law_slices':law_slice_demos(),'joint':concrete_joint()}
        except Exception as ex:status='FAIL';demos={'error':str(ex)}
    (out/'joint-and-slice-demos.json').write_text(json.dumps(demos,default=str,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    report={'status':status,'scope':'V21_REFERENCE_PYTHON_ONLY','collected':len(ids),'run':result.testsRun,
       'failures':len(result.failures),'errors':len(result.errors),'skipped':len(result.skipped),
       'python':platform.python_version(),'time_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
       'lean':'CI_NOT_RUN_BY_THIS_SCRIPT','jc':'NOT_RUN_BY_THIS_SCRIPT','empirical':'NO_REAL_DATA_USED'}
    (out/'python-result.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(report));return 0 if status=='PASS' else 1
if __name__=='__main__':raise SystemExit(main())
