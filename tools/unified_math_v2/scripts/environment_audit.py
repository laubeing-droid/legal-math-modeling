#!/usr/bin/env python3
"""Check Lean's COMPILED environment inventory, not a regex claim of proof.
Input is emitted by JurisLean/UnifiedV21/Audit.lean in GitHub Actions only.
"""
import argparse,json
from pathlib import Path
PREFIX='ULM_ENV_AUDIT_JSON='
ALLOWED={'propext','Classical.choice','Quot.sound'}
REQUIRED={'JurisLean.ULM.UnifiedV21.concrete_root_contract',
          'JurisLean.ULM.UnifiedV21.interval_solver_exact',
          'JurisLean.ULM.UnifiedV21.context_wire_injective'}
def verify_log(text):
    lines=[line[len(PREFIX):] for line in text.splitlines() if line.startswith(PREFIX)]
    if len(lines)!=1:raise ValueError('Exactly one compiled environment inventory is required')
    records=json.loads(lines[0])
    if type(records) is not list or not records:raise ValueError('Empty inventory')
    names=set()
    for item in records:
        if type(item) is not dict:raise ValueError('Bad record')
        name=item.get('name');axs=item.get('axioms');deps=item.get('proof_dependencies')
        if type(name) is not str or name in names:raise ValueError('Missing or repeated theorem')
        if not name.startswith(('JurisLean.ULM.UnifiedV2.','JurisLean.ULM.UnifiedV21.')):
            raise ValueError('Foreign declaration')
        if type(axs) is not list or any(type(a) is not str for a in axs):raise ValueError('Bad axioms')
        if set(axs)-ALLOWED:raise ValueError('Unapproved axiom: '+str(set(axs)-ALLOWED))
        if type(deps) is not list or any(type(a) is not str for a in deps):raise ValueError('Missing dependency record')
        names.add(name)
    if not REQUIRED<=names:raise ValueError('Required concrete roots not compiled: '+str(REQUIRED-names))
    return {'status':'PASS','scope':'COMPILED_SEED_DECLARATIONS_ONLY',
            'theorem_count':len(names),'axioms':sorted({a for r in records for a in r['axioms']}),
            'records':records,'not_proved_by_inventory':'Universal C07/runtime refinement/legal adequacy/calibration'}
def main():
    p=argparse.ArgumentParser();p.add_argument('--log',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();a.output.parent.mkdir(parents=True,exist_ok=True)
    try:report=verify_log(a.log.read_text(encoding='utf-8'))
    except (ValueError,KeyError,TypeError) as ex:report={'status':'FAIL','error':str(ex)}
    a.output.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    if report['status']!='PASS':raise SystemExit(1)
if __name__=='__main__':main()
