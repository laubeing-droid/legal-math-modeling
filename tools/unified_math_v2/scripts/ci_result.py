#!/usr/bin/env python3
"""Bind exact CI subject and run identity. Not an external legal attestation."""
import argparse,json,os,subprocess
from pathlib import Path

def identity():
    if os.environ.get('GITHUB_ACTIONS')!='true':raise ValueError('This recorder only accepts GitHub Actions')
    actual=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
    if actual!=os.environ.get('GITHUB_SHA'):raise ValueError('CI checkout/subject mismatch')
    return {'subject':actual,'tree':subprocess.check_output(['git','rev-parse','HEAD^{tree}'],text=True).strip(),
            'repository':os.environ['GITHUB_REPOSITORY'],'run_id':os.environ['GITHUB_RUN_ID'],
            'attempt':os.environ['GITHUB_RUN_ATTEMPT']}
def main():
    p=argparse.ArgumentParser();p.add_argument('--report',type=Path);p.add_argument('--aggregate',type=Path)
    p.add_argument('--output',type=Path,required=True);a=p.parse_args();ident=identity()
    if a.report:
        r=json.loads(a.report.read_text());
        if r.get('status')!='PASS':raise ValueError('Non-PASS upstream report')
        r['ci_binding']=ident
    else:
        kinds={'python':'python-result.json','lean':'lean-result.json','jc':'jc-smoke.json'};reports={}
        for kind,name in kinds.items():
            candidates=list(a.aggregate.rglob(name))
            if len(candidates)!=1:raise ValueError('Missing or ambiguous report '+name)
            r=json.loads(candidates[0].read_text())
            if r.get('status')!='PASS' or r.get('ci_binding')!=ident:raise ValueError('Stale/mismatched upstream '+kind)
            reports[kind]={'scope':r['scope'],'status':r['status']}
        r={'status':'PASS','scope':'V21_REFERENCE_CI_NOT_PRODUCTION_RELEASE','ci_binding':ident,
           'upstream':reports,'universal_C07':'NOT_CLOSED_BY_THIS_WORKFLOW',
           'v21_JC_refinement':'NOT_ESTABLISHED','legal_rule_approval':'NOT_ESTABLISHED',
           'empirical_validation':'NOT_ESTABLISHED'}
    a.output.parent.mkdir(parents=True,exist_ok=True)
    a.output.write_text(json.dumps(r,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
if __name__=='__main__':main()
