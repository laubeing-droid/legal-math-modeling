#!/usr/bin/env python3
"""CLI for scoped reference tests and synthetic demos (never a JC release)."""
from pathlib import Path
import argparse,sys,json,unittest,datetime
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))

def flatten(suite):
    for test in suite:
        if isinstance(test,unittest.TestSuite):yield from flatten(test)
        else:yield test.id()

def main():
    p=argparse.ArgumentParser();p.add_argument('--output',required=True)
    args=p.parse_args();out=Path(args.output);out.mkdir(parents=True,exist_ok=True)
    suite=unittest.defaultTestLoader.discover(str(ROOT/'tests'))
    ids=list(flatten(suite))
    (out/'collection.json').write_text(json.dumps(ids,indent=2)+'\n')
    with (out/'unittest.log').open('w') as stream:
        result=unittest.TextTestRunner(stream=stream,verbosity=2).run(suite)
    report={'status':'PASS' if result.wasSuccessful() and not result.skipped and len(ids)==result.testsRun else 'FAIL',
            'scope':'REFERENCE_PYTHON_ONLY','collected':len(ids),'run':result.testsRun,'failures':len(result.failures),
            'errors':len(result.errors),'skipped':len(result.skipped),'lean_status':'CI_NOT_RUN_BY_THIS_SCRIPT',
            'jc_integration_status':'NOT_PERFORMED_BY_THIS_SCRIPT','real_data_validation':'NOT_PERFORMED_BY_THIS_SCRIPT',
            'execution_time_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
    (out/'python-result.json').write_text(json.dumps(report,indent=2)+'\n')
    from unified.pipeline import combined_demo,all_fields_demo
    (out/'synthetic-unified-demo.json').write_text(json.dumps(combined_demo(),indent=2,default=str)+'\n')
    (out/'all-fields-conditional-demo.json').write_text(json.dumps(all_fields_demo(),ensure_ascii=False,indent=2,default=str)+'\n')
    print(json.dumps(report));return 0 if report['status']=='PASS' else 1
if __name__=='__main__':raise SystemExit(main())
