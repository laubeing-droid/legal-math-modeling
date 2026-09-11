import JurisLean.BusinessRoot.SevenAxis
import JurisLean.BusinessRoot.SevenAxisCases
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command

-- Actual compiled environment inspection; not a source-regex proof counter.
run_cmd do
  let env ← getEnv
  let mut records : Array Json := #[]
  for (name, info) in env.constants.toList do
    let label := name.toString
    if label.startsWith "JurisLean.BusinessRoot.SevenAxis." then
      match info with
      | .thmInfo ti =>
        let axioms ← Lean.collectAxioms name
        records := records.push (Json.mkObj [
          ("name", Json.str label),
          ("axioms", Json.arr (axioms.map fun ax => Json.str ax.toString)),
          ("proof_dependencies", Json.arr
            (ti.value.getUsedConstants.map fun d => Json.str d.toString))])
      | _ => pure ()
  liftIO <| IO.println ("SEVEN_AXIS_COMPILED_ENV_JSON=" ++ (Json.arr records).compress)

-- Compile-time type assertion. Required-name presence is not enough if the
-- root theorem's statement is silently weakened.
example (i s : JurisLean.BusinessRoot.SevenAxis.FullInput)
    (d : List JurisLean.BusinessRoot.SevenAxis.DocRow)
    (j : List JurisLean.BusinessRoot.SevenAxis.CalculationRow)
    (h : JurisLean.BusinessRoot.SevenAxis.checkSevenAxisBundle i s d j = true) :
    ∃ W, JurisLean.BusinessRoot.SevenAxis.SevenTaskSat i s W d j :=
  JurisLean.BusinessRoot.SevenAxis.seven_axis_business_root i s d j h
