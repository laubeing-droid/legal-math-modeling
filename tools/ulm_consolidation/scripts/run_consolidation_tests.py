from pathlib import Path
import argparse,io,json,sys,unittest
root=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(root/'scripts'))
sys.path.insert(0,str(root))
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args();a.output.mkdir(parents=True,exist_ok=True)
suite=unittest.defaultTestLoader.discover(str(root/'tests'))
f=io.StringIO();r=unittest.TextTestRunner(stream=f,verbosity=2).run(suite)
out={'run':r.testsRun,'failures':len(r.failures),'errors':len(r.errors),'skipped':len(r.skipped)}
(a.output/'tests.log').write_text(f.getvalue(),encoding='utf-8');(a.output/'result.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out));raise SystemExit(0 if r.wasSuccessful() and r.testsRun and not r.skipped else 1)
