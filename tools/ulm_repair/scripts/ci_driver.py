#!/usr/bin/env python3
"""Commands used inside the existing authority workflow.

No automatic trigger/push. `build` is refused outside GitHub Actions.
Other commands are local static/data checks and do not execute Lean.
"""
from pathlib import Path
import argparse,importlib.util,json,os,subprocess,sys
R=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
import ci_evidence as E


def main():
    ap=argparse.ArgumentParser();sp=ap.add_subparsers(dest='command',required=True)
    p=sp.add_parser('receipt');p.add_argument('--directory',type=Path,required=True);p.add_argument('--kind',required=True)
    p=sp.add_parser('audit');p.add_argument('--log',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
    p=sp.add_parser('gate');p.add_argument('--python-dir',type=Path,required=True);p.add_argument('--lean-dir',type=Path,required=True);p.add_argument('--needs',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
    p=sp.add_parser('flatten');p.add_argument('--source',type=Path,required=True);p.add_argument('--target',type=Path,required=True)
    p=sp.add_parser('build');p.add_argument('--plan',type=Path,required=True)
    p=sp.add_parser('pins')
    args=ap.parse_args()
    if args.command=='receipt':
        receipt=E.bundle_receipt(args.directory,E.identity(R),args.kind)
        (args.directory/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
    elif args.command=='audit':
        report=E.verify_environment(args.log.read_text(encoding='utf-8'));args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    elif args.command=='gate':
        needs=json.loads(args.needs.read_text());E.verify_jobs(needs,{'python-gates','lean-full-clean-build'})
        subject=E.identity(R)
        for directory,kind in [(args.python_dir,'seven-axis-python'),(args.lean_dir,'seven-axis-lean')]:
            E.verify_receipt(directory,json.loads((directory/'receipt.json').read_text()),subject,kind)
        py=json.loads((args.python_dir/'repair/repair-python.json').read_text())
        root=json.loads((args.python_dir/'root/root-python.json').read_text())
        retained=json.loads((args.python_dir/'retained/consolidated-python.json').read_text())
        lean=json.loads((args.lean_dir/'seven-axis-audit.json').read_text())
        for item in [py,root,retained,lean]:
            if item.get('status')!='PASS':raise ValueError('Unsuccessful detailed report')
        if any(py.get(k) for k in ['failures','errors','skipped']) or py.get('run',0)==0:raise ValueError('Bad Python run')
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps({'status':'PASS','subject':subject,
             'scope':'FROZEN_TYPED_SEVEN_AXIS_ROOT_WITH_PYTHON_CROSS_CHECKS',
             'NOT_ESTABLISHED':['arbitrary_I0_root','Python_kernel_refinement','byte_parser_kernel_proof','JC_Harness_production','legal_source_truth','real_win_rate']},indent=2)+'\n',encoding='utf-8')
    elif args.command=='flatten':E.flatten_without_overwrite(args.source,args.target)
    elif args.command=='pins':
        b=R/'proofs/lean/juris_lean'
        if (b/'lean-toolchain').read_text().strip()!='leanprover/lean4:v4.30.0':raise ValueError('Toolchain drift')
        packages=json.loads((b/'lake-manifest.json').read_text())['packages']
        ms=[x for x in packages if x['name']=='mathlib']
        if len(ms)!=1 or ms[0]['rev']!='c5ea00351c28e24afc9f0f84379aa41082b1188f':raise ValueError('Mathlib drift')
    elif args.command=='build':
        if os.environ.get('GITHUB_ACTIONS')!='true':raise ValueError('Lean execution is GitHub-only')
        spec=importlib.util.spec_from_file_location('planner',R/'scripts/ci/changed_lean_modules.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
        plan=json.loads(args.plan.read_text());current=m.current_sources(R);targets=[x['target'] for x in plan['include']]
        if not targets or len(targets)!=len(set(targets)) or any(x not in current for x in targets):raise ValueError('Unknown/empty/duplicate target')
        subprocess.run(['lake','build',*targets],cwd=R/'proofs/lean/juris_lean',check=True)
    return 0
if __name__=='__main__':raise SystemExit(main())
