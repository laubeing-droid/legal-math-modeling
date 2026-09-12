#!/usr/bin/env python3
"""One full-plan entry. No local Lean, no automatic claim of completed mathematics."""
from pathlib import Path
import argparse,json,sys,os,subprocess
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
import completion as C

def main():
    p=argparse.ArgumentParser();p.add_argument('command',choices=['queue','validate','collect-lean','finalize','handover'])
    p.add_argument('--repo',type=Path,default=Path.cwd());p.add_argument('--log',type=Path);p.add_argument('--compiled',type=Path);p.add_argument('--tests',type=Path);p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();repo=a.repo.resolve();spec=ROOT/'spec';bindings=spec/'BINDINGS.json'
    scope,reqs=C.requirements(spec);bs,missing,errors=C.binding_inventory(bindings,spec,repo)
    if a.command in ('queue','validate'):
        data={'status':'SCOPE_VALID' if not errors else 'INVALID_BINDINGS','terminal_status':'INCOMPLETE' if missing or errors else 'AWAITING_ACTUAL_CI',
              'mandatory_total':217,'bindings_present':len(bs),'missing':missing,'errors':errors,'execution_order':C.read(spec/'EXECUTION_ORDER.json'),
              'instruction':'Continue mathematical implementation and proof for every missing item; a queue report is not completion.'}
        C.dump(a.output,data);print(json.dumps({'status':data['status'],'unbound':len(missing)}));return 1 if errors else 0
    if a.command=='collect-lean':
        if not a.log:raise C.EvidenceError('--log required')
        if missing or errors:raise C.EvidenceError('All bindings must be concretely implemented first')
        text=a.log.read_text(encoding='utf-8');C.parse_compiled(text)
        C.dump(a.output,{'subject':C.identity(repo,True),'log':text,'sources':C.source_manifest(repo,bs,spec)});return 0
    if a.command=='finalize':
        if not a.compiled or not a.tests:raise C.EvidenceError('--compiled and --tests required')
        compiled=C.read(a.compiled);tests=C.read(a.tests)
        verdict=C.evaluate_full_plan(spec,bindings,compiled,tests,compiled.get('sources',[]),C.identity(repo,True),repo)
        C.dump(a.output,verdict);print(json.dumps({'status':verdict['status'],'errors':len(verdict.get('errors',[]))}))
        return 0 if verdict['status']=='MATH_BUILD_COMPLETE' else 2
    if a.command=='handover':
        if not a.compiled:raise C.EvidenceError('--compiled must name actual completion receipt')
        r=C.read(a.compiled)
        if r.get('status')!='MATH_BUILD_COMPLETE':raise C.EvidenceError('no full math completion receipt')
        C.check_identity(r['subject'],C.identity(repo,True))
        C.dump(a.output,{'status':'READY_FOR_LATER_INTEGRATION_DESIGN','mathematics':r,
                         'contract':C.read(spec/'EXPORT_AFTER_MATH.json'),'external':C.read(spec/'DEFERRED_EXTERNAL.json')})
        return 0
    return 1
if __name__=='__main__':
    try:raise SystemExit(main())
    except (C.EvidenceError,OSError,subprocess.SubprocessError) as e:
        print(str(e),file=sys.stderr);raise SystemExit(2)
