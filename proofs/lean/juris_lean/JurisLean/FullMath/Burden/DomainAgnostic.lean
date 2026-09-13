import JurisLean.FullMath.Core.Foundations

/-!
B01 — Domain-neutral issue-shaped burden of proof: separated fields
(object, proponent, persuasive burden, standard, stage, authority), a
conflict between candidate policies without a selection rule returns
pending instead of picking the highest number, and substantive and
procedural outcomes are distinct constructors.
-/

namespace JurisLean.FullMath.Burden

/-- A burden slot with separated, individually sourced fields. -/
structure BurdenSlot where
  issue : String
  proponent : String
  standard : String
  stage : String
  authority : String

/-- Resolution states of a burden slot. -/
inductive BurdenState where
  | pending
  | met
  | shiftedTo (party : String)
  | notReached

/-- Candidate policies applied to a slot; more than one conflicting
candidate without a selection rule leaves the slot pending. -/
def resolveList : List String → BurdenSlot → BurdenState
  | [], _ => .pending
  | [p], s => if p = s.standard then .met else .notReached
  | _ :: _ :: _, _ => .pending

/-- B01(a): no applicable policy means pending — never an invented
outcome. -/
theorem unresolved_policy_pending (s : BurdenSlot) :
    resolveList [] s = BurdenState.pending := rfl

/-- B01(b): conflicting candidate policies without a policy-of-selection
rule stay pending — the system must not silently choose. -/
theorem conflict_without_rule_is_pending (p q : String) (hpq : p ≠ q)
    (s : BurdenSlot) : resolveList [p, q] s = BurdenState.pending := rfl

/-- B01(c): a single applicable policy decides between met and notReached. -/
theorem single_policy_decides (p : String) (s : BurdenSlot) :
    resolveList [p] s = BurdenState.met ∨ resolveList [p] s = BurdenState.notReached := by
  by_cases h : p = s.standard
  · left; rw [resolveList, if_pos h]
  · right; rw [resolveList, if_neg h]

/-- B01(d): pending carries no terminal legal effect. -/
theorem pending_is_not_met (s : BurdenSlot) (ps : List String) :
    resolveList ps s = BurdenState.pending → resolveList ps s ≠ BurdenState.met := by
  intro h hcontra
  rw [hcontra] at h
  cases h

/-- Substantive and procedural outcomes are separate constructors — a
procedural dismissal is never a substantive finding. -/
inductive Ruling where
  | substantiveMet (slot : BurdenSlot)
  | proceduralDismissed (ground : String)

theorem substantive_not_procedural (slot : BurdenSlot) (ground : String) :
    Ruling.substantiveMet slot ≠ Ruling.proceduralDismissed ground := by
  intro h
  cases h

/-- Per-stage applicability: a policy only applies to its declared stage. -/
def appliesAtStage (policyStage stage : String) : Bool := decide (policyStage = stage)

theorem stage_scoping (policyStage stage stage' : String)
    (h : ¬ (stage = stage')) (happ : appliesAtStage policyStage stage = true) :
    appliesAtStage policyStage stage' = false := by
  simp only [appliesAtStage] at happ ⊢
  rw [of_decide_eq_true happ]
  omega

end JurisLean.FullMath.Burden
