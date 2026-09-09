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

def main():
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
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
