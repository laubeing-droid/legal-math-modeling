import JurisLean.HornAAFContract

/-!
Task-bounded Horn-to-AAF translation witness. Equality with the independently
computed expected sets gives exact omission, spurious-edge, and direction checks.
It does not prove an external compiler correct outside the bound input contract.
-/

namespace JurisLean

/-- Expected and produced directed edges retain identity, endpoints, kind, and input witness. -/
structure WitnessedEdge where
  id : AttackId
  source : ArgumentId
  target : ArgumentId
  kind : AttackKind
  inputWitness : String
deriving DecidableEq, Repr

/-- Exact finite witness for one fixed input language, semantics, and cycle policy. -/
structure TranslationWitness where
  inputDigest : String
  observedInputDigest : String
  expectedArguments : Finset ArgumentId
  producedArguments : Finset ArgumentId
  expectedEdges : Finset WitnessedEdge
  producedEdges : Finset WitnessedEdge
  semanticsId : String
  semanticsVersion : String
  cyclePolicy : String
deriving DecidableEq

/-- Validity is exact set equality plus a bound input and recognized execution contract. -/
def TranslationWitness.Valid (w : TranslationWitness) : Prop :=
  w.inputDigest ≠ "" ∧
    w.inputDigest = w.observedInputDigest ∧
    w.expectedArguments = w.producedArguments ∧
    w.expectedEdges = w.producedEdges ∧
    w.semanticsId = "grounded" ∧
    w.semanticsVersion = "1" ∧
    (w.cyclePolicy = "reject" ∨ w.cyclePolicy = "explicit-undecided")

/-- Executable validity check for the finite translation witness. -/
def checkTranslationWitness (w : TranslationWitness) : Bool :=
  decide w.Valid

/-- A successful executable check recovers the proposition-level witness contract. -/
theorem translation_witness_check_sound
    (w : TranslationWitness)
    (h : checkTranslationWitness w = true) :
    w.Valid := by
  exact of_decide_eq_true h

/-- No expected argument can be omitted from a valid witness. -/
theorem translation_witness_no_argument_omission
    (w : TranslationWitness)
    (hValid : w.Valid)
    {argumentId : ArgumentId}
    (hExpected : argumentId ∈ w.expectedArguments) :
    argumentId ∈ w.producedArguments := by
  rw [← hValid.2.2.1]
  exact hExpected

/-- No produced argument can be spurious in a valid witness. -/
theorem translation_witness_no_spurious_argument
    (w : TranslationWitness)
    (hValid : w.Valid)
    {argumentId : ArgumentId}
    (hProduced : argumentId ∈ w.producedArguments) :
    argumentId ∈ w.expectedArguments := by
  rw [hValid.2.2.1]
  exact hProduced

/-- No expected directed edge can be omitted from a valid witness. -/
theorem translation_witness_no_edge_omission
    (w : TranslationWitness)
    (hValid : w.Valid)
    {edge : WitnessedEdge}
    (hExpected : edge ∈ w.expectedEdges) :
    edge ∈ w.producedEdges := by
  rw [← hValid.2.2.2.1]
  exact hExpected

/-- No produced directed edge can lack an expected input witness. -/
theorem translation_witness_no_spurious_edge
    (w : TranslationWitness)
    (hValid : w.Valid)
    {edge : WitnessedEdge}
    (hProduced : edge ∈ w.producedEdges) :
    edge ∈ w.expectedEdges := by
  rw [hValid.2.2.2.1]
  exact hProduced

/-- Exact edge equality prevents priority direction reversal under the bound contract. -/
theorem translation_witness_priority_direction_preserved
    (w : TranslationWitness)
    (hValid : w.Valid)
    {edge : WitnessedEdge}
    (hExpected : edge ∈ w.expectedEdges)
    (hPriority : edge.kind = AttackKind.priorityDefeat) :
    edge ∈ w.producedEdges ∧ edge.kind = AttackKind.priorityDefeat :=
  ⟨translation_witness_no_edge_omission w hValid hExpected, hPriority⟩

end JurisLean
