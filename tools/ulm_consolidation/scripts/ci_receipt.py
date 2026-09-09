#!/usr/bin/env python3
"""Same-run CI evidence binding, no new external trust or release authority."""
import argparse,json,os,subprocess
from pathlib import Path

def identity():
    if os.environ.get('GITHUB_ACTIONS')!='true':raise ValueError('CI binding only available inside GitHub Actions')
    head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
    if head!=os.environ.get('GITHUB_SHA'):raise ValueError('Checkout/subject mismatch')
    return {'subject':head,'tree':subprocess.check_output(['git','rev-parse','HEAD^{tree}'],text=True).strip(),'repository':os.environ['GITHUB_REPOSITORY'],'run_id':os.environ['GITHUB_RUN_ID'],'attempt':os.environ['GITHUB_RUN_ATTEMPT']}

def aggregate(root,ident):
    reports={}
    for kind,name in {'python':'consolidated-python.json','lean':'consolidated-lean.json','jc':'consolidated-jc.json'}.items():
        matches=list(Path(root).rglob(name))
        if len(matches)!=1:raise ValueError('Missing/ambiguous '+name)
        r=json.loads(matches[0].read_text(encoding='utf-8'))
        if r.get('status')!='PASS' or r.get('ci_binding')!=ident:raise ValueError('Stale/failed/mismatched '+name)
        reports[kind]={'status':'PASS','scope':r['scope']}
    return {'status':'PASS','scope':'CONSOLIDATED_REFERENCE_CI_NOT_BUSINESS_ROOT_ACCEPTANCE','ci_binding':ident,'upstream':reports,'root_refinement':'NOT_CLOSED_BY_THIS_WORKFLOW','all_134_business_requirements':'NOT_CLOSED','law_approval':'NOT_ESTABLISHED','empirical_validation':'NOT_ESTABLISHED'}

if __name__=='__main__':
    p=argparse.ArgumentParser();g=p.add_mutually_exclusive_group(required=True);g.add_argument('--report',type=Path);g.add_argument('--aggregate',type=Path);p.add_argument('--output',type=Path,required=True);a=p.parse_args();ident=identity()
    if a.report:
        r=json.loads(a.report.read_text(encoding='utf-8'))
        if r.get('status')!='PASS':raise ValueError('Nonpass report')
        r['ci_binding']=ident
    else:r=aggregate(a.aggregate,ident)
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(r,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
