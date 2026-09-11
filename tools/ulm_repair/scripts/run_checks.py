#!/usr/bin/env python3
"""Run audit-delta Python tests and byte readback. Does not launch Lean or network."""
from pathlib import Path
import argparse,datetime,io,json,platform,sys,unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
import projection_reference as P


def main():
    a=argparse.ArgumentParser();a.add_argument('--output',type=Path,required=True);args=a.parse_args()
    out=args.output.resolve();out.mkdir(parents=True,exist_ok=True)
    stream=io.StringIO();suite=unittest.defaultTestLoader.discover(str(ROOT/'tests'))
    result=unittest.TextTestRunner(stream=stream,verbosity=2).run(suite)
    (out/'tests.log').write_text(stream.getvalue(),encoding='utf-8')
    report={'status':'FAIL','run':result.testsRun,'failures':len(result.failures),
       'errors':len(result.errors),'skipped':len(result.skipped),
       'python':platform.python_version(),'time_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
       'scope':'PYTHON_REFERENCE_AND_BUILD_PLANNER_TESTS_ONLY',
       'lean':'NOT_RUN_BY_THIS_PROGRAM','production':'NOT_INTEGRATED','empirical':'NO_REAL_DATA'}
    if result.wasSuccessful() and result.testsRun and not result.skipped:
        try:
            demo=P.materialize(out/'actual-files')
            report['actual_files_accepted']=demo['accepted'];report['status']='PASS'
        except Exception as e:report['error']=str(e)
    (out/'repair-python.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(report,ensure_ascii=False,indent=2));return 0 if report['status']=='PASS' else 1
if __name__=='__main__':raise SystemExit(main())
