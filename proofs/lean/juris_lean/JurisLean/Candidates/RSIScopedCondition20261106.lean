import JurisLean.Candidates.Final20261021.RSI

/-!
Original 13.4 L113 needs a shared finite sample filtered into two
scope-specific inputs to the existing estimator, with one unchanged
persistent state. L115 asks for the returned scope and diagnostics.
-/

namespace JurisLean.Candidates.RSIScopedCondition20261106

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.Final20261021.RSI

private structure ScopedRow where
  scope : Bool
  weight : ℚ
  outcome : ℚ
  deriving DecidableEq

private structure ScopedReply where
  scope : Bool
  selected : List ScopedRow
  estimate : Result ℚ
  weightEss : Option ℚ
  uncertainty : Result (ℚ × ℚ)
  deriving DecidableEq

private def estimateInScope (scope : Bool) (rows : List ScopedRow) : ScopedReply :=
  let selected := rows.filter (fun row => row.scope == scope)
  let weights := selected.map ScopedRow.weight
  let estimate := conditionalEstimate weights (selected.map ScopedRow.outcome)
  let weightEss := match estimate with
    | .known _ => some (weights.sum ^ 2 / (weights.map (fun w => w ^ 2)).sum)
    | _ => none
  { scope := scope
    selected := selected
    estimate := estimate
    weightEss := weightEss
    uncertainty := .unknown .missingEvidence }

private def runCondition (s : State) (scope : Bool) (rows : List ScopedRow) :
    ScopedReply × State :=
  (estimateInScope scope rows, prepareUpdate s .condition)

private def sample : List ScopedRow :=
  [⟨false, 2, 1⟩, ⟨true, 3, 0⟩]

theorem scoped_estimates_differ_without_changing_persistent_state (s : State) :
    (runCondition s false sample).1 =
        ⟨false, [⟨false, 2, 1⟩], .known 1, some 1, .unknown .missingEvidence⟩ ∧
    (runCondition s true sample).1 =
        ⟨true, [⟨true, 3, 0⟩], .known 0, some 1, .unknown .missingEvidence⟩ ∧
    (runCondition s false sample).2 = s ∧ (runCondition s true sample).2 = s := by
  refine ⟨?_, ?_, u13_2_condition_does_not_train s, u13_2_condition_does_not_train s⟩
  · change estimateInScope false sample = _
    decide +kernel
  · change estimateInScope true sample = _
    decide +kernel

#check scoped_estimates_differ_without_changing_persistent_state
#print axioms scoped_estimates_differ_without_changing_persistent_state

end JurisLean.Candidates.RSIScopedCondition20261106
