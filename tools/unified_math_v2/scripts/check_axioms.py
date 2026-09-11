#!/usr/bin/env python3
"""Verify every requested theorem appears in Lean's axiom output, not just a green log."""
from pathlib import Path
import argparse,json,re

def main():
    p=argparse.ArgumentParser();p.add_argument('--inventory',type=Path,required=True)
    p.add_argument('--log',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    names=json.loads(a.inventory.read_text())['names'];text=a.log.read_text()
    allowed={'propext','Classical.choice','Quot.sound'};missing=[];bad=[]
    for name in names:
        pattern=re.escape(name)+r"['’]?\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
        m=re.search(pattern,text,re.S)
        if m is None:missing.append(name);continue
        axioms={x.strip().strip("'\"") for x in (m.group(1) or '').split(',') if x.strip()}
        for x in sorted(axioms-allowed):bad.append({'name':name,'axiom':x})
    result={'scope':'NEW_LEAN_SEEDS_ONLY','status':'PASS' if not missing and not bad else 'FAIL',
            'requested':len(names),'missing':missing,'unapproved_axioms':bad}
    a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
    return 0 if result['status']=='PASS' else 1
if __name__=='__main__':raise SystemExit(main())
