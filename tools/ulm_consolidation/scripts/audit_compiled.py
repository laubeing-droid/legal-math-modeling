#!/usr/bin/env python3
"""Verify the actual Lean environment report and retained seed coverage.
Only a real CI build can create compile evidence. This scanner never proves the
Python business root, legal applicability, or any empirical property.
"""
import argparse,json
from pathlib import Path
PREFIX='ULM_COMPILED_ENV_JSON='
ALLOWED={'propext','Classical.choice','Quot.sound'}
PREFIXES=('JurisLean.ULM.UnifiedV2.','JurisLean.ULM.UnifiedV21.','JurisLean.BusinessRelations.')

def verify_log(text, expected):
    lines=[l[len(PREFIX):] for l in text.splitlines() if l.startswith(PREFIX)]
    if len(lines)!=1:raise ValueError('Exactly one compiled environment required')
    rows=json.loads(lines[0]);names=set()
    if type(rows) is not list or not rows:raise ValueError('Empty inventory')
    for r in rows:
        if type(r) is not dict:raise ValueError('Bad record')
        name=r.get('name');axioms=r.get('axioms');deps=r.get('proof_dependencies')
        if type(name) is not str or not name.startswith(PREFIXES) or name in names:raise ValueError('Foreign/duplicate/missing theorem')
        if type(axioms) is not list or any(type(x) is not str for x in axioms):raise ValueError('Bad axiom data')
        if set(axioms)-ALLOWED:raise ValueError('Forbidden axiom '+repr(set(axioms)-ALLOWED))
        if type(deps) is not list or any(type(x) is not str for x in deps):raise ValueError('Missing proof dependency list')
        names.add(name)
    required={r['name'] for r in expected['declarations']}
    if required-names:raise ValueError('Uncompiled retained declarations '+repr(sorted(required-names)))
    return {'status':'PASS','scope':'COMPILED_RETAINED_SEEDS_ONLY','theorem_count':len(names),'retained_count':len(required),'records':rows,'finite_business_root':'NOT_ESTABLISHED_BY_INVENTORY','production_refinement':'NOT_ESTABLISHED','legal_approval':'NOT_ESTABLISHED','empirical':'NOT_ESTABLISHED'}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--log',type=Path,required=True);p.add_argument('--expected',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    try:r=verify_log(a.log.read_text(encoding='utf-8'),json.loads(a.expected.read_text(encoding='utf-8')))
    except (ValueError,TypeError,KeyError,OSError) as e:r={'status':'FAIL','error':str(e)}
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(r,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    raise SystemExit(0 if r['status']=='PASS' else 1)
