#!/usr/bin/env python3
"""Run independent suites in isolated processes, with actual per-test results.
Use --self-test for package tests without asserting implementation completion.
"""
from pathlib import Path
import argparse, json, os, subprocess, sys, unittest, time
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
import completion as C

class ActualResult(unittest.TextTestResult):
    def __init__(self,*a,**kw):super().__init__(*a,**kw);self.results=[]
    def addSuccess(self,test):super().addSuccess(test);self.results.append({'id':test.id(),'status':'PASS'})
    def addFailure(self,test,err):super().addFailure(test,err);self.results.append({'id':test.id(),'status':'FAIL','message':self._exc_info_to_string(err,test)})
    def addError(self,test,err):super().addError(test,err);self.results.append({'id':test.id(),'status':'ERROR','message':self._exc_info_to_string(err,test)})
    def addSkip(self,test,reason):super().addSkip(test,reason);self.results.append({'id':test.id(),'status':'SKIP','reason':reason})
    def addExpectedFailure(self,test,err):super().addExpectedFailure(test,err);self.results.append({'id':test.id(),'status':'EXPECTED_FAILURE_NOT_COMPLETE'})
    def addUnexpectedSuccess(self,test):super().addUnexpectedSuccess(test);self.results.append({'id':test.id(),'status':'UNEXPECTED_SUCCESS'})

def pytest_worker(directory,output,repo):
    # A subprocess per suite avoids old bare module names polluting other suites.
    scripts=Path(__file__).resolve().parent
    env={**os.environ,'PYTHONUTF8':'1','PYTHONDONTWRITEBYTECODE':'1',
         'PYTHONPATH':str(scripts)+os.pathsep+os.environ.get('PYTHONPATH','')}
    cmd=[sys.executable,'-B','-m','pytest',str(directory),'-q','-ra',
         '--rootdir',str(directory),'--import-mode=importlib','-p','no:cacheprovider',
         '-p','pytest_evidence_plugin','--math-evidence-output',str(output)]
    run=subprocess.run(cmd,cwd=repo,env=env)
    if run.returncode:return run.returncode
    if not output.is_file():return 1
    report=C.read(output)
    return 0 if report.get('status')=='PASS' else 1


def worker(directory,output):
    suite=unittest.defaultTestLoader.discover(str(directory),pattern='test_*.py')
    result=unittest.TextTestRunner(verbosity=2,resultclass=ActualResult).run(suite)
    C.dump(output,{'count':result.testsRun,'tests':result.results})
    return 0 if result.wasSuccessful() and not result.skipped and result.testsRun>0 else 1

def main():
    p=argparse.ArgumentParser();p.add_argument('--repo',type=Path,default=Path.cwd());p.add_argument('--output',type=Path,required=True)
    p.add_argument('--worker',type=Path);p.add_argument('--self-test',action='store_true');p.add_argument('--pytest-worker',action='store_true');a=p.parse_args()
    if a.worker:return pytest_worker(a.worker,a.output,a.repo) if a.pytest_worker else worker(a.worker,a.output)
    repo=a.repo.resolve();out=a.output.resolve();out.parent.mkdir(parents=True,exist_ok=True)
    dirs=[ROOT/'tests']
    if not a.self_test:
        bs,missing,errors=C.binding_inventory(ROOT/'spec/BINDINGS.json',repo=repo)
        if missing or errors:
            C.dump(out,{'status':'INCOMPLETE','missing':missing,'errors':errors});return 2
        # Whole tree of this implementation, not the finite legacy demonstration alone.
        for rel in ['tests','tools/full_math/implementation_tests','tools/unified_math_v2/tests','tools/business_relations/tests','tools/business_relations/root','tools/ulm_repair/tests']:
            d=repo/rel
            if d.exists() and d not in dirs:dirs.append(d)
    tests=[];failures=[]
    for k,d in enumerate(dirs):
        if not any(d.rglob('test_*.py')):continue
        label=d.relative_to(repo).as_posix() if repo in d.parents else d.name
        dest=out.parent/f'suite-{k}.json'
        with (out.parent/f'suite-{k}.log').open('w',encoding='utf-8') as f:
            cmd=[sys.executable,'-B',str(Path(__file__)),'--worker',str(d),'--output',str(dest),'--repo',str(repo)]
            if not a.self_test:cmd.append('--pytest-worker')
            proc=subprocess.run(cmd,cwd=repo,stdout=f,stderr=subprocess.STDOUT,env={**os.environ,'PYTHONUTF8':'1','PYTHONDONTWRITEBYTECODE':'1'})
        if proc.returncode:failures.append(label)
        if dest.exists():
            for t in C.read(dest)['tests']:t['id']=label+'::'+t['id'];tests.append(t)
    status='PASS' if tests and not failures and all(t['status']=='PASS' for t in tests) else 'FAIL'
    subject={'local_only':True} if a.self_test else C.identity(repo)
    C.dump(out,{'status':status,'scope':'PACKAGE_SELF_TESTS_NOT_MATH_COMPLETION' if a.self_test else 'ALL_REGISTERED_IMPLEMENTATION_TESTS',
                'subject':subject,'python':sys.version,'tests':tests,'failed_suites':failures,'total':len(tests)})
    print(json.dumps({'status':status,'total':len(tests),'scope':'self-tests' if a.self_test else 'implementation'}))
    return 0 if status=='PASS' else 1
if __name__=='__main__':raise SystemExit(main())
