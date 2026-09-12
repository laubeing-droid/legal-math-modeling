#!/usr/bin/env python3
"""Extend the existing single authority; preserve all existing jobs and gates.
Preview by default. This does not start Actions or install credentials.
"""
from pathlib import Path
import argparse,copy,hashlib,json,sys
import yaml

AUDIT='proofs/lean/juris_lean/JurisLean/FullMath/CompletionAudit.lean'

def patch(data):
    data=copy.deepcopy(data)
    # PyYAML YAML 1.1 can decode the Actions key 'on' as boolean True.
    if True in data and 'on' not in data:data['on']=data.pop(True)
    jobs=data.get('jobs',{})
    required={'python-gates','lean-full-clean-build','seven-axis-acceptance','release-certificate','final-gate'}
    if not required<=set(jobs):raise ValueError('Current authority shape changed; preserve and reconcile it, do not replace with old YAML')
    # No second workflow or alternative final success path.
    py=jobs['python-gates']['steps'];ln=jobs['lean-full-clean-build']['steps']
    def once(steps,name,new,index=None):
        hits=[x for x in steps if x.get('name')==name]
        if hits:
            if hits!=[new]:raise ValueError('Existing full-math step differs: '+name)
            return
        if index is None:steps.append(new)
        else:steps.insert(index,new)
    once(py,'All mathematics implementation tests',{'name':'All mathematics implementation tests','run':'set -euo pipefail\npython tools/full_math/scripts/run_all_registered_tests.py --output work/full-math-python/tests.json\n'})
    once(py,'Upload full mathematics Python evidence',{'name':'Upload full mathematics Python evidence','if':'always()','uses':'actions/upload-artifact@ea165f8d65b6e75b540449e92b4886f43607fa02','with':{'name':'full-math-python-${{ github.run_id }}-${{ github.run_attempt }}','path':'work/full-math-python'}})
    before=next((i for i,s in enumerate(ln) if s.get('name')=='Build all project Lean modules from a clean project build'),None)
    if before is None:raise ValueError('Cannot locate recursive full build; manual explicit reconciliation required')
    once(ln,'Generate and verify all mathematics type assertions',{'name':'Generate and verify all mathematics type assertions','run':f'set -euo pipefail\npython tools/full_math/scripts/generate_audit.py --output {AUDIT}\ngit ls-files --error-unmatch {AUDIT}\ngit diff --exit-code -- {AUDIT}\n'},before)
    once(ln,'Audit whole mathematical plan',{'name':'Audit whole mathematical plan','run':'set -euo pipefail\nmkdir -p work/full-math-lean\n(cd proofs/lean/juris_lean && lake env lean JurisLean/FullMath/CompletionAudit.lean) > work/full-math-lean/environment.log 2>&1\npython tools/full_math/scripts/run.py collect-lean --log work/full-math-lean/environment.log --output work/full-math-lean/compiled.json\n'})
    once(ln,'Upload full mathematics Lean evidence',{'name':'Upload full mathematics Lean evidence','if':'always()','uses':'actions/upload-artifact@ea165f8d65b6e75b540449e92b4886f43607fa02','with':{'name':'full-math-lean-${{ github.run_id }}-${{ github.run_attempt }}','path':'work/full-math-lean'}})
    newjob={
     'needs':['python-gates','lean-full-clean-build'],
     'if':"${{ success() && (github.event_name != 'workflow_dispatch' || inputs.mode == 'full-release') }}",
     'runs-on':'ubuntu-latest','timeout-minutes':15,
     'steps':[
      {'uses':'actions/checkout@34e114876b0b11c390a56381ad16ebd13914f8d5'},
      {'uses':'actions/setup-python@a26af69be951a213d495a4c3e4e4022e16d87065','with':{'python-version':'3.12'}},
      {'uses':'actions/download-artifact@d3f86a106a0bac45b974a628896c90dbdf5c8093','with':{'name':'full-math-python-${{ github.run_id }}-${{ github.run_attempt }}','path':'full-math-evidence/python'}},
      {'uses':'actions/download-artifact@d3f86a106a0bac45b974a628896c90dbdf5c8093','with':{'name':'full-math-lean-${{ github.run_id }}-${{ github.run_attempt }}','path':'full-math-evidence/lean'}},
      {'name':'Require the whole mathematical plan, not a demo','run':'set -euo pipefail\npython tools/full_math/scripts/run.py finalize --compiled full-math-evidence/lean/compiled.json --tests full-math-evidence/python/tests.json --output MATH_COMPLETION.json\npython tools/full_math/scripts/run.py handover --compiled MATH_COMPLETION.json --output EXPORT_CONTRACT.json\n'},
      {'uses':'actions/upload-artifact@ea165f8d65b6e75b540449e92b4886f43607fa02','if':'always()','with':{'name':'full-math-completion-${{ github.run_id }}-${{ github.run_attempt }}','path':'MATH_COMPLETION.json\nEXPORT_CONTRACT.json'}}]}
    if 'mathematics-completion' in jobs and jobs['mathematics-completion']!=newjob:raise ValueError('Existing completion job differs')
    jobs['mathematics-completion']=newjob
    for name in ('release-certificate','final-gate'):
        if 'mathematics-completion' not in jobs[name]['needs']:jobs[name]['needs'].append('mathematics-completion')
    # The retained final script uses an exact required-job set; extend, do not remove it.
    final=jobs['final-gate']['steps'];found=False
    for step in final:
        script=step.get('run','')
        marker="required={'lean-full-clean-build','python-gates','runtime-refinement','seven-axis-acceptance','release-certificate'}"
        changed="required={'lean-full-clean-build','python-gates','runtime-refinement','seven-axis-acceptance','release-certificate','mathematics-completion'}"
        if marker in script:step['run']=script.replace(marker,changed);found=True
        elif changed in script:found=True
    if not found:raise ValueError('Final authority script changed: inspect exact dependency check, do not remove it')
    return data

def main():
    p=argparse.ArgumentParser();p.add_argument('--repo',type=Path,default=Path.cwd());p.add_argument('--apply',action='store_true');a=p.parse_args()
    path=a.repo/'.github/workflows/lean-build.yml';old=path.read_text(encoding='utf-8');obj=yaml.safe_load(old);new=patch(obj)
    text=yaml.safe_dump(new,allow_unicode=True,sort_keys=False,width=120)
    if patch(new)!=new:raise ValueError('patch not semantically idempotent')
    if a.apply:
        backup=path.with_suffix('.yml.before-full-math')
        if not backup.exists():backup.write_text(old,encoding='utf-8')
        path.write_text(text,encoding='utf-8')
        print('APPLIED_EXISTING_AUTHORITY_EXTENSION; incomplete full plan must remain red')
    else:
        preview=a.repo/'work/full-math/lean-build.preview.yml';preview.parent.mkdir(parents=True,exist_ok=True);preview.write_text(text,encoding='utf-8');print(str(preview))
    return 0
if __name__=='__main__':raise SystemExit(main())
