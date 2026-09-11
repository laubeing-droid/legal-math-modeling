#!/usr/bin/env python3
"""Re-run retained Python suites in isolated processes; never run Lean locally.
BR's original runner writes to its own directory, so it is executed from a
scratch copy. Reports are always produced by this run, never copied from history.
"""
from pathlib import Path
import argparse,datetime,hashlib,json,os,platform,shutil,subprocess,sys,tempfile,uuid

ROOT=Path(__file__).resolve().parents[1]
REPO=ROOT.parents[1]

def read(p):return json.loads(Path(p).read_text(encoding='utf-8'))
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def run(cmd,log,cwd):
    log.parent.mkdir(parents=True,exist_ok=True)
    with log.open('w',encoding='utf-8') as f:
        p=subprocess.run(cmd,cwd=cwd,stdout=f,stderr=subprocess.STDOUT,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1','PYTHONUTF8':'1'})
    if p.returncode:raise RuntimeError('Command failed, see '+str(log))

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();out=a.output.resolve();out.mkdir(parents=True,exist_ok=True)
    rid=uuid.uuid4().hex
    report={'status':'FAIL','scope':'CONSOLIDATED_REFERENCE_PYTHON_ONLY','run_id':rid,'python':platform.python_version(),'time_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'tests':{},'lean':'NOT_RUN_BY_THIS_SCRIPT','jc':'NOT_RUN_BY_THIS_SCRIPT','finite_business_root':'PENDING_FORMAL_REFINEMENT','empirical':'NO_REAL_DATA_USED','legal_approval':'NOT_PERFORMED'}
    try:
        run([sys.executable,'-B',str(ROOT/'scripts/validate_plan.py'),'--repo-root',str(REPO),'--output',str(out/'plan.json')],out/'plan.log',REPO)
        run([sys.executable,'-B',str(REPO/'tools/unified_math_v2/scripts/run_v21.py'),'--output',str(out/'v21')],out/'v21-run.log',REPO)
        v=read(out/'v21/python-result.json');report['tests']['v21']={k:v[k] for k in ['run','failures','errors','skipped']}
        run([sys.executable,'-B',str(REPO/'tools/unified_math_v2/scripts/win_model_cli.py'),'--synthetic-example','--output',str(out/'win-example.json')],out/'win-example.log',REPO)
        with tempfile.TemporaryDirectory(prefix='ulm-br-') as tmp:
            work=Path(tmp)/'br';shutil.copytree(REPO/'tools/business_relations',work)
            run([sys.executable,'-B',str(work/'ci/run_reference.py')],out/'br-run.log',work)
            shutil.copytree(work/'evidence',out/'br',dirs_exist_ok=True);shutil.copytree(work/'examples',out/'br/examples',dirs_exist_ok=True)
        b=read(out/'br/reference_result.json');report['tests']['business_root_reference']={'run':b['tests'],'failures':b['failures'],'errors':b['errors'],'skipped':b['skips']}
        report['actual_two_file_readback']=b['delivery_root']
        # Run finite probes without executing their historical __main__ output writers.
        for module in ['ext_math_probes','business_semantics_probes']:
            loader=("import io,json,sys,unittest; from pathlib import Path; "
                    "sys.path.insert(0,sys.argv[1]); "
                    "suite=unittest.defaultTestLoader.loadTestsFromName(sys.argv[2]); "
                    "stream=io.StringIO(); r=unittest.TextTestRunner(stream=stream,verbosity=2).run(suite); "
                    "Path(sys.argv[3]).write_text(stream.getvalue(),encoding='utf-8'); "
                    "Path(sys.argv[4]).write_text(json.dumps(dict(run=r.testsRun,failures=len(r.failures),errors=len(r.errors),skipped=len(r.skipped)),indent=2),encoding='utf-8'); "
                    "sys.exit(0 if r.wasSuccessful() and not r.skipped and r.testsRun else 1)")
            run([sys.executable,'-B','-c',loader,str(ROOT/'probes'),module,str(out/(module+'.log')),str(out/(module+'.json'))],out/(module+'-exec.log'),REPO)
            report['tests'][module]=read(out/(module+'.json'))
        run([sys.executable,'-B',str(ROOT/'scripts/run_consolidation_tests.py'),'--output',str(out/'consolidation-tests')],out/'consolidation-tests.log',REPO)
        report['tests']['consolidation_checks']=read(out/'consolidation-tests/result.json')
        counts=list(report['tests'].values())
        if any(x['failures'] or x['errors'] or x['skipped'] or x['run']==0 for x in counts):raise RuntimeError('Failed/empty/skipped reference suite')
        report['total_test_executions']=sum(x['run'] for x in counts)
        report['scope_note']='Counts include finite illustrative probes and consolidation checks; not that many independent legal cases or proven theorems.'
        report['status']='PASS'
    except Exception as e:report['error']=str(e)
    report['evidence_files']=[{'path':p.relative_to(out).as_posix(),'sha256':sha(p)} for p in sorted(out.rglob('*')) if p.is_file() and p.name!='consolidated-python.json']
    (out/'consolidated-python.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n',encoding='utf-8');print(json.dumps(report,ensure_ascii=False,indent=2))
    return 0 if report['status']=='PASS' else 1
if __name__=='__main__':raise SystemExit(main())
