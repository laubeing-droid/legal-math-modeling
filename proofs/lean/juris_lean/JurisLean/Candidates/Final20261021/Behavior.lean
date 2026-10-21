import JurisLean.Candidates.Final20261021.Interfaces

namespace JurisLean.Candidates.Final20261021.Behavior

structure CausalModel where
  observedAction : Bool → Bool
  observedOutcome : Bool → Bool
  intervenedOutcome : Bool → Bool → Bool

def m1 : CausalModel := ⟨id, id, fun a _ => a⟩
def m2 : CausalModel := ⟨id, id, fun _ u => u⟩
def indicator (b : Bool) : ℚ := if b then 1 else 0
def interventionMean (m : CausalModel) (a : Bool) : ℚ :=
  (indicator (m.intervenedOutcome a false) + indicator (m.intervenedOutcome a true)) / 2
def ate (m : CausalModel) : ℚ := interventionMean m true - interventionMean m false

theorem u11_1_obs_equiv_models_distinct_ATE :
    (∀ u, (m1.observedAction u, m1.observedOutcome u) =
      (m2.observedAction u, m2.observedOutcome u)) ∧ ate m1 = 1 ∧ ate m2 = 0 := by
  refine ⟨fun _ => rfl, ?_, ?_⟩ <;>
    norm_num [ate, interventionMean, m1, m2, indicator]

structure MeasurementLog where
  unit : MeasurementId
  event : EventId
  record : RecordId
  targetVersion : Nat
  mechanismVersion : Nat
  windowEnd : Instant
  observedAt : Instant
  outcome : Option Bool
  positiveWitness : Option SourceRef
  externalSource : SourceRef
  deriving DecidableEq, Repr

def proposed_measurement (expectedTarget : Nat) (log : MeasurementLog) : Result Bool :=
  if log.targetVersion ≠ expectedTarget then .unknown .targetMismatch
  else match log.outcome with
  | some true => if log.positiveWitness.isSome then .known true else .unknown .missingEvidence
  | some false => if log.windowEnd.ticks ≤ log.observedAt.ticks then .known false
      else .unknown .missingEvidence
  | none => .unknown .missingEvidence

-- An identified value must agree across every supplied compatible model.
-- The completeness of this model family is a separate external obligation.
def proposed_causal_evidence (effects : List ℚ) : Result ℚ :=
  match effects with
  | [] => .unknown .missingEvidence
  | x :: xs => if xs.all (fun y => decide (y = x)) then .known x
      else .unknown .notIdentified

theorem prediction_not_causal_identification :
    proposed_causal_evidence [ate m1, ate m2] = .unknown .notIdentified := by
  norm_num [proposed_causal_evidence, ate, interventionMean, m1, m2, indicator]

theorem transport_composition_changes_effect :
    (4/5 : ℚ)*(3/10) + (1/5)*(-3/10) = 18/100 ∧
    (1/5 : ℚ)*(3/10) + (4/5)*(-3/10) = -18/100 := by norm_num

end JurisLean.Candidates.Final20261021.Behavior
