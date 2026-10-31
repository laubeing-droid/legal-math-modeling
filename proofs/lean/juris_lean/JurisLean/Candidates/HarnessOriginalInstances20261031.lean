import JurisLean.Candidates.LegalActionDomain20261027
import JurisLean.Candidates.Final20261021.Harness

noncomputable section

namespace JurisLean.Candidates.HarnessOriginalInstances20261031

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.Final20261021.Compiler
open JurisLean.Candidates.FiniteLegalValidation20261027
open JurisLean.Candidates.IntervalDecisionConsumer20261027
open JurisLean.Candidates.LegalActionDomain20261027

/-!
Fixed finite instances for original 02.2, 02.3, 02.5 and 02.6.
General trajectory, gate soundness, checker soundness and execution frame
theorems are reused. These instances do not implement exception handling.
-/

def resourceAllowed (s : Fin 3) : Bool := decide (s.val + 1 ≤ 1)

def resourceNext (s t : Fin 3) : Bool := decide (t.val = s.val + 1)

def resourceInvariant (s : Fin 3) : Bool := decide (s.val ≤ 1)

def resourceGate (s : Fin 3) : Bool :=
  Harness.tableSafe (W := Unit) (S := Fin 3) (A := Unit)
    (fun _ => true) (fun _ s _ => resourceAllowed s)
    (fun _ s _ t => resourceNext s t) (fun _ t => resourceInvariant t) s ()

/-- Two checks at state zero cannot certify their consecutive execution. -/
theorem stale_resource_checks_do_not_compose :
    [resourceGate 0, resourceGate 0] = [true, true] ∧
      resourceNext 0 1 = true ∧ resourceNext 1 2 = true ∧
      resourceInvariant 0 = true ∧ resourceInvariant 1 = true ∧
      resourceInvariant 2 = false ∧ resourceGate 1 = false := by
  decide

def hiddenObservation (_ : Bool) : Unit := ()

def hiddenAllowed (state action : Bool) : Prop := action = state

/-- The same two-world object witnesses both observation loss and false blocking. -/
theorem hidden_permissions_force_refusal :
    hiddenObservation false = hiddenObservation true ∧
      (hiddenAllowed false false ∧ hiddenAllowed true true) ∧
      (¬ ∃ a : Bool, hiddenAllowed false a ∧ hiddenAllowed true a) ∧
      ∀ gate : Unit → Bool → Bool,
        (∀ state action, gate (hiddenObservation state) action = true →
          hiddenAllowed state action) →
        ((∀ state action, hiddenAllowed state action →
          gate (hiddenObservation state) action = true) → False) ∧
        gate () false = false ∧ gate () true = false := by
  refine ⟨rfl, ⟨rfl, rfl⟩, by simp [hiddenAllowed], ?_⟩
  intro gate sound
  refine ⟨?_, ?_, ?_⟩
  · intro complete
    exact indistinguishable_permission_prevents_sound_and_complete
      hiddenObservation hiddenAllowed gate false true false rfl rfl (by simp [hiddenAllowed])
      sound complete
  · cases h : gate () false with
    | false => rfl
    | true =>
        have impossible : (false : Bool) = true := sound true false h
        cases impossible
  · cases h : gate () true with
    | false => rfl
    | true =>
        have impossible : (true : Bool) = false := sound false true h
        cases impossible

def premiseRule : Rule Nat := ⟨[0], 1⟩

def falseFactTruth (_ : Nat) : Prop := False

def falseRuleTruth (a : Nat) : Prop := a = 0

/-- A checked derivation is relative to its supplied facts and rules.
The first primitive valuation falsifies the fact; the second satisfies the fact
and falsifies the rule implication. Both falsify the derived conclusion. -/
theorem checked_trace_does_not_supply_primitive_truth :
    checkTrace [premiseRule] [0] [[premiseRule]] = true ∧
      replayTrace [0] [[premiseRule]] = [0, 1] ∧
      Derives (fun a => a ∈ ([0] : List Nat)) (fun r => r ∈ [premiseRule]) 1 ∧
      ¬ falseFactTruth 0 ∧ ¬ falseFactTruth 1 ∧
      falseRuleTruth 0 ∧ ¬ falseRuleTruth 1 ∧
      ¬ Models (fun a => a ∈ ([0] : List Nat))
        (fun r => r ∈ [premiseRule]) falseFactTruth ∧
      ¬ Models (fun a => a ∈ ([0] : List Nat))
        (fun r => r ∈ [premiseRule]) falseRuleTruth := by
  have accepted : checkTrace [premiseRule] [0] [[premiseRule]] = true := by decide
  have derived :
      Derives (fun a => a ∈ ([0] : List Nat)) (fun r => r ∈ [premiseRule]) 1 :=
    checked_trace_certifies_relative_derivation [premiseRule] [0] [[premiseRule]]
      accepted 1 (by decide)
  have badFact :
      ¬ Models (fun a => a ∈ ([0] : List Nat))
        (fun r => r ∈ [premiseRule]) falseFactTruth := by
    intro model
    exact model.1 0 (by simp)
  have badRule :
      ¬ Models (fun a => a ∈ ([0] : List Nat))
        (fun r => r ∈ [premiseRule]) falseRuleTruth := by
    intro model
    have impossible := model.2 premiseRule (by simp) (by
      intro a ha
      simpa [premiseRule, falseRuleTruth] using ha)
    norm_num [premiseRule, falseRuleTruth] at impossible
  exact ⟨accepted, by decide, derived, by simp [falseFactTruth],
    by simp [falseFactTruth], rfl, by simp [falseRuleTruth], badFact, badRule⟩

def finiteGate (proposals : List Bool) : List Bool :=
  Harness.proposed_harness_gate (W := Unit) (S := Unit) (A := Bool)
    (fun _ => true) (fun _ _ a => !a)
    (fun _ _ _ _ => true) (fun _ _ => true) () proposals

/-- Arbitrary proposed actions are filtered by the existing finite gate.
The explicit candidate list has a nonempty accepted result. -/
theorem finite_gate_has_nonempty_safe_instance :
    finiteGate [false, true] = [false] ∧
      ∀ (proposals : List Bool) (a : Bool), a ∈ finiteGate proposals →
        a ∈ proposals ∧ a = false ∧
          Harness.Safe (fun _ : Unit => True)
            (fun (_ : Unit) (_ : Unit) action => action = false)
            (fun (_ : Unit) (_ : Unit) (_ : Bool) (_ : Unit) => True)
            (fun (_ : Unit) (_ : Unit) => True) () a := by
  refine ⟨by decide, ?_⟩
  intro proposals a accepted
  have checked := (Harness.u02_3_finite_gate_enumeration
    (W := Unit) (S := Unit) (A := Bool)
    (fun _ => true) (fun _ _ a => !a)
    (fun _ _ _ _ => true) (fun _ _ => true) () proposals a).mp accepted
  have allowedFalse : a = false := by
    have permitted := (checked.2 () rfl).1
    cases a <;> simpa using permitted
  refine ⟨checked.1, allowedFalse, ?_⟩
  simpa [Harness.Safe, allowedFalse] using checked.2

/-- A mathematical pre-dispatch preparation failure, not a runtime catch. -/
def internalPreparationFailure {m : Nat} : Result (IntervalDecision m) :=
  .unknown .unsupported

/-- Preparation failure has no selected plan and preserves the business handle.
An unknown commit after dispatch still has no certain poststate. -/
theorem preparation_failure_frame_and_unknown_commit {m : Nat}
    (request : DecisionRequest m) (utility : ℚ → ℚ)
    (proposals : List Proposal) (grants : List Authorization.Grant)
    (initial : Ledger.Handle) :
    (executeDecision request utility proposals internalPreparationFailure grants initial).proposal = none ∧
      (executeDecision request utility proposals internalPreparationFailure grants initial).payment.current =
        some initial ∧
      (executeDecision request utility proposals internalPreparationFailure grants initial).payment.outcomes = [] ∧
      (executeDecision request utility proposals internalPreparationFailure grants initial).payment.obligations =
        [.unsupported] ∧
      ∀ (key : PaymentId) (attempt : AttemptId),
        (Ledger.Outcome.unknownCommit key attempt).post initial = none := by
  have noPlan :
      (executeDecision request utility proposals internalPreparationFailure grants initial).proposal = none := rfl
  have frame := no_selected_plan_preserves_all_business_state request utility proposals
    internalPreparationFailure grants initial noPlan
  exact ⟨noPlan, frame.1, frame.2, rfl, fun _ _ => rfl⟩

end JurisLean.Candidates.HarnessOriginalInstances20261031