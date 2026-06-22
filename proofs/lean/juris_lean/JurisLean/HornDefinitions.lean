import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import JurisLean.FiniteMonotoneIteration

open Finset

/-! Horn Fixpoint Definitions — pure Horn logic operator and instantiation.

The Horn immediate consequence operator T_H takes a set of ground facts
and Horn rules, and produces all derivable conclusions. It is monotone
and stays within a finite universe (initial facts ∪ all rule heads).

This file defines the operator and instantiates FiniteMonotoneSystem.
All proofs are in HornFixedPoint.lean.
-/

/-- A Horn rule: if all premises are satisfied, the conclusion holds. -/
structure HornRule (α : Type) where
  premises : Finset α
  conclusion : α
deriving DecidableEq

/-- A Horn system: initial facts plus rules over a ground atom universe. -/
structure HornSystem (α : Type) [DecidableEq α] where
  universe : Finset α
  initialFacts : Finset α
  rules : Finset (HornRule α)
  initialFacts_subset_universe : initialFacts ⊆ universe
  heads_subset_universe : ∀ r ∈ rules, r.conclusion ∈ universe

namespace HornSystem

variable {α : Type} [DecidableEq α] (sys : HornSystem α)

/-- The Horn immediate consequence operator T_H(S):
    initial facts ∪ {conclusion(r) | premises(r) ⊆ S}. -/
def TH : Finset α → Finset α := λ S =>
  sys.initialFacts ∪ (sys.rules.filter (λ r => r.premises ⊆ S)).image HornRule.conclusion

/-- TH is monotone: if S ⊆ T then TH(S) ⊆ TH(T). -/
theorem TH_monotone {S T : Finset α} (hST : S ⊆ T) : TH sys S ⊆ TH sys T := by
  unfold TH
  apply Finset.union_subset_union (Finset.Subset.refl _)
  apply Finset.image_subset_image
  apply Finset.filter_subset_filter
  intro r hr
  -- hr: r.premises ⊆ S
  -- Need: r.premises ⊆ T
  exact Finset.Subset.trans hr hST

/-- TH always stays within the universe. -/
theorem TH_subset_universe (S : Finset α) : TH sys S ⊆ sys.universe := by
  unfold TH
  apply Finset.union_subset
  · exact sys.initialFacts_subset_universe
  · -- image of rule conclusions
    apply Finset.image_subset_image
    intro r hr
    rcases Finset.mem_filter.mp hr with ⟨hr_rules, _⟩
    exact sys.heads_subset_universe r hr_rules

/-- Instantiate the Horn system as a FiniteMonotoneSystem. -/
def toFiniteMonotoneSystem : FiniteMonotoneSystem α := {
  universe := sys.universe
  step := TH sys
  step_subset_universe := TH_subset_universe sys
  step_monotone := TH_monotone sys
}

end HornSystem