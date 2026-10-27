import JurisLean.Candidates.TemporalInterpretation20261027
import JurisLean.Candidates.EvidenceWorlds20261027
import JurisLean.Candidates.ProcedureClosure20261027

/-!
Original 08.7/08.8: finite legal validation consumes all extracted source
atoms, the actual selected norm version and an independent procedure policy.
The round trace is executable derivation evidence. A missing requested proof
does not remove a source fact or turn non-derivability into factual falsity.
-/

namespace JurisLean.Candidates.FiniteLegalValidation20261027

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.Final20261021.Compiler
open JurisLean.Candidates.Final20261021.Temporal
open JurisLean.Candidates.Final20261021.EvidenceProcedure


def enabledRules (rules : List (Rule Nat)) (known : List Nat) : List (Rule Nat) :=
  rules.filter fun r => r.premises.all (fun a => decide (a ∈ known))

theorem fired_conclusions_are_enabled_rules (rules : List (Rule Nat)) (known : List Nat) :
    rules.flatMap (fun r => if r.premises.all (fun a => decide (a ∈ known))
      then [r.conclusion] else []) = (enabledRules rules known).map Rule.conclusion := by
  induction rules with
  | nil => rfl
  | cons rule rest ih =>
      cases allowed : rule.premises.all (fun a => decide (a ∈ known)) <;>
        simp [enabledRules, allowed, enabledRules] at ih ⊢ <;> exact ih

theorem advance_is_recorded_round (rules : List (Rule Nat)) (known : List Nat) :
    advance rules known = known ++ (enabledRules rules known).map Rule.conclusion := by
  rw [advance, fired_conclusions_are_enabled_rules]

def traceRounds (rules : List (Rule Nat)) : Nat → List Nat → List (List (Rule Nat))
  | 0, _ => []
  | fuel + 1, known => enabledRules rules known :: traceRounds rules fuel (advance rules known)

def replayTrace : List Nat → List (List (Rule Nat)) → List Nat
  | known, [] => known
  | known, fired :: rest => replayTrace (known ++ fired.map Rule.conclusion) rest

def ValidTrace (rules : List (Rule Nat)) : List Nat → List (List (Rule Nat)) → Prop
  | _, [] => True
  | known, fired :: rest =>
      (∀ r ∈ fired, r ∈ rules ∧ ∀ a ∈ r.premises, a ∈ known) ∧
        ValidTrace rules (known ++ fired.map Rule.conclusion) rest

theorem generated_trace_has_actual_rule_premises (rules : List (Rule Nat))
    (fuel : Nat) (facts : List Nat) : ValidTrace rules facts (traceRounds rules fuel facts) := by
  induction fuel generalizing facts with
  | zero => trivial
  | succ fuel ih =>
      refine ⟨?_, ?_⟩
      · intro r member
        have parts := List.mem_filter.mp member
        exact ⟨parts.1, by simpa only [List.all_eq_true, decide_eq_true_eq] using parts.2⟩
      · rw [← advance_is_recorded_round]
        exact ih (advance rules facts)

theorem replay_generated_trace_is_exact_closure (rules : List (Rule Nat))
    (fuel : Nat) (facts : List Nat) :
    replayTrace facts (traceRounds rules fuel facts) = proposed_rule_input rules fuel facts := by
  induction fuel generalizing facts with
  | zero => rfl
  | succ fuel ih =>
      simp only [traceRounds, replayTrace, proposed_rule_input]
      rw [← advance_is_recorded_round]
      exact ih (advance rules facts)

theorem trace_has_exact_number_of_rounds (rules : List (Rule Nat))
    (fuel : Nat) (facts : List Nat) : (traceRounds rules fuel facts).length = fuel := by
  induction fuel generalizing facts with
  | zero => rfl
  | succ fuel ih => simp [traceRounds, ih]

theorem enabled_count_bounded_by_rule_count (rules : List (Rule Nat)) (facts : List Nat) :
    (enabledRules rules facts).length ≤ rules.length := by
  induction rules with
  | nil => simp [enabledRules]
  | cons rule rest ih =>
      cases allowed : rule.premises.all (fun a => decide (a ∈ facts)) <;>
        simp [enabledRules, allowed] at ih ⊢ <;> omega

theorem closure_list_size_bound (rules : List (Rule Nat)) (fuel : Nat) (facts : List Nat) :
    (proposed_rule_input rules fuel facts).length ≤ facts.length + fuel * rules.length := by
  induction fuel generalizing facts with
  | zero => simp [proposed_rule_input]
  | succ fuel ih =>
      have tailBound := ih (advance rules facts)
      have added := enabled_count_bounded_by_rule_count rules facts
      rw [advance_is_recorded_round] at tailBound
      simp only [List.length_append, List.length_map] at tailBound
      simp only [proposed_rule_input, Nat.succ_mul]
      omega

structure HornReport where
  source : SourceCompilation20261027.ExtractedView
  selectedVersion : Nat
  active : List (Rule Nat)
  fuel : Nat
  trace : List (List (Rule Nat))
  closure : List Nat

def sourceFacts (view : SourceCompilation20261027.ExtractedView) : List Nat := view.decoded.atoms.map SourceCompilation20261027.Quoted.value

def fullHorn (view : SourceCompilation20261027.ExtractedView) (selected : Nat) (rules : List CompilerProvenance20261027.RuleUse)
    (ruleGate : Gamma → CompilerProvenance20261027.RuleUse → Bool) : HornReport :=
  let active := CompilerProvenance20261027.activeRules view.material.gamma rules (TemporalInterpretation20261027.selectedGate selected ruleGate)
  let facts := sourceFacts view
  let fuel := (finiteCarrier active facts).card
  let trace := traceRounds active fuel facts
  ⟨view, selected, active, fuel, trace, replayTrace facts trace⟩

theorem full_horn_consumes_every_source_fact (view : SourceCompilation20261027.ExtractedView) (selected : Nat)
    (rules : List CompilerProvenance20261027.RuleUse) (ruleGate : Gamma → CompilerProvenance20261027.RuleUse → Bool) (a : Nat) :
    a ∈ (fullHorn view selected rules ruleGate).closure ↔
      Derives (· ∈ sourceFacts view)
        (· ∈ CompilerProvenance20261027.activeRules view.material.gamma rules (TemporalInterpretation20261027.selectedGate selected ruleGate)) a := by
  simp only [fullHorn, replay_generated_trace_is_exact_closure]
  exact u03_2_computed_at_carrier_iff _ _ _

theorem full_horn_trace_is_checked (view : SourceCompilation20261027.ExtractedView) (selected : Nat)
    (rules : List CompilerProvenance20261027.RuleUse) (ruleGate : Gamma → CompilerProvenance20261027.RuleUse → Bool) :
    ValidTrace (fullHorn view selected rules ruleGate).active (sourceFacts view)
      (fullHorn view selected rules ruleGate).trace :=
  generated_trace_has_actual_rule_premises _ _ _

end JurisLean.Candidates.FiniteLegalValidation20261027
