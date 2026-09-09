import JurisLean.UnifiedV21.All
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command

/- Environment-based inventory, not a regex-based proof claim.
Executed only in GitHub Actions. collectAxioms API checked at Lean v4.30.0. -/
run_cmd do
  let env ← getEnv
  let mut records : Array Json := #[]
  for (name, info) in env.constants.toList do
    let label := name.toString
    if label.startsWith "JurisLean.ULM.UnifiedV2." ||
       label.startsWith "JurisLean.ULM.UnifiedV21." then
      match info with
      | .thmInfo theoremInfo =>
        let axioms ← Lean.collectAxioms name
        records := records.push (Json.mkObj [
          ("name", Json.str label),
          ("axioms", Json.arr (axioms.map fun ax => Json.str ax.toString)),
          ("proof_dependencies", Json.arr
            (theoremInfo.value.getUsedConstants.map fun dep => Json.str dep.toString))])
      | _ => pure ()
  liftIO <| IO.println ("ULM_ENV_AUDIT_JSON=" ++ (Json.arr records).compress)
