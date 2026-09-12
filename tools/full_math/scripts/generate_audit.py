#!/usr/bin/env python3
"""Generate all required Lean type assertions from a complete binding manifest.
This does not generate proofs. Missing bindings cause a failure, not placeholder axioms.
"""
from pathlib import Path
import argparse,json,sys
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from completion import binding_inventory,requirements,EvidenceError

def generate(repo:Path,bindings_path:Path,spec:Path):
    bs,missing,errors=binding_inventory(bindings_path,spec,repo)
    if missing or errors:raise EvidenceError('FULL_MATH_IMPLEMENTATION_REQUIRED: '+json.dumps({'missing':missing,'errors':errors},ensure_ascii=False))
    _,reqs=requirements(spec)
    lines=['import JurisLean.FullMath.Acceptance','import Lean.Util.CollectAxioms','import Lean.Elab.Command','',
      '-- Generated acceptance TYPE checks. This file contains no assumed proof.',
      'open Lean Elab Command Meta','']
    for i,r in enumerate(reqs):
        lines.append(f'theorem full_math_typecheck_{i:03d} : {r["contract"]} := {r["theorem"]}')
    # Compile-time assignments above are stronger than mere name inventory.
    pairs=',\n  '.join('('+json.dumps(r['theorem'])+', '+json.dumps(r['contract'])+')' for r in reqs)
    lines+=['','run_cmd do',f'  let required : List (String × String) := [{pairs}]',
      '  let env ← getEnv','  let mut rows : Array Json := #[]',
      '  for (name, info) in env.constants.toList do',
      '    if name.toString.startsWith "JurisLean." then',
      '      match info with',
      '      | .thmInfo ti =>',
      '        let axs ← Lean.collectAxioms name',
      '        let typ ← liftTermElabM <| Meta.ppExpr ti.type',
      '        let contract := (required.find? (fun p => p.1 == name.toString)).map Prod.snd',
      '        rows := rows.push (Json.mkObj [',
      '          ("name", Json.str name.toString), ("kind", Json.str "theorem"),',
      '          ("type", Json.str typ.pretty),',
      '          ("axioms", Json.arr (axs.map (fun n => Json.str n.toString))),',
      '          ("dependencies", Json.arr (ti.value.getUsedConstants.map (fun n => Json.str n.toString))),',
      '          ("contract", match contract with | some c => Json.str c | none => Json.null),',
      '          ("typecheck", Json.str "LEAN_ASSIGNMENT_ELABORATED"),',
      '          ("proof_form", Json.str "SEE_REQUIRED_CONTRACT_NOT_INFERRED_FROM_NAME")])',
      '      | _ => pure ()',
      '  liftIO <| IO.println ("FULL_MATH_ENV_JSON=" ++ (Json.arr rows).compress)','']
    return '\n'.join(lines)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--repo',type=Path,default=Path.cwd());ap.add_argument('--bindings',type=Path,default=ROOT/'spec/BINDINGS.json');ap.add_argument('--output',type=Path,required=True)
    a=ap.parse_args()
    text=generate(a.repo.resolve(),a.bindings,ROOT/'spec');a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(text,encoding='utf-8')
    print('GENERATED_FULL_SCOPE_TYPECHECKS_NOT_A_PROOF_RECEIPT');return 0
if __name__=='__main__':raise SystemExit(main())
