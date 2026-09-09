import JurisLean.BusinessRoot.Root
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command

/- GitHub CI compiled-environment inspection for the business root.
No theorem is proved by this inventory; it records the axiom and dependency
environment of the actually compiled `JurisLean.BusinessRoot` theorems. -/
run_cmd do
  let env ← getEnv
  let mut records : Array Json := #[]
  for (name, info) in env.constants.toList do
    let label := name.toString
    if label.startsWith "JurisLean.BusinessRoot." then
      match info with
      | .thmInfo theoremInfo =>
        let axioms ← Lean.collectAxioms name
        records := records.push (Json.mkObj [
          ("name", Json.str label),
          ("axioms", Json.arr (axioms.map fun ax => Json.str ax.toString)),
          ("proof_dependencies", Json.arr
            (theoremInfo.value.getUsedConstants.map fun dep => Json.str dep.toString))])
      | _ => pure ()
  liftIO <| IO.println ("ROOT_COMPILED_ENV_JSON=" ++ (Json.arr records).compress)
