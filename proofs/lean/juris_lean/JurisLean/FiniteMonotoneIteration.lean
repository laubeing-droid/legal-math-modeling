import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

open Finset

/-! Finite Monotone Iteration Kernel.
Shared by AAF and Horn. 0 sorry, 0 axiom, 0 admit.
-/

/-- A finite monotone system: step function stays in universe and is monotone. -/
structure FiniteMonotoneSystem (α : Type) [DecidableEq α] where
  universe : Finset α
  step : Finset α → Finset α
  step_subset_universe : ∀ S, step S ⊆ universe
  step_monotone : ∀ {S T}, S ⊆ T → step S ⊆ step T

namespace FiniteMonotoneSystem

variable {α : Type} [DecidableEq α] (sys : FiniteMonotoneSystem α)

/-- Iterate the step function n times from the empty set. -/
def iter : Nat → Finset α
  | 0 => ∅
  | n + 1 => sys.step (iter n)

-- A. Basic properties ---------------------------------------------------------

@[simp] theorem iter_zero : iter sys 0 = ∅ := rfl

theorem iter_succ (n : Nat) : iter sys (n + 1) = sys.step (iter sys n) := rfl

theorem iter_subset_universe (n : Nat) : iter sys n ⊆ sys.universe := by
  induction n with
  | zero => exact Finset.empty_subset _
  | succ n ih =>
    rw [iter_succ]
    exact sys.step_subset_universe _

theorem iter_mono : ∀ n, iter sys n ⊆ iter sys (n + 1)
  | 0 => Finset.empty_subset _
  | n + 1 => by
    rw [iter_succ, iter_succ]
    apply sys.step_monotone (iter_mono sys n)

theorem iter_stable {n : Nat} (h : iter sys n = iter sys (n + 1)) : ∀ k, iter sys (n + k) = iter sys n := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.add_succ, iter_succ, ← h, ih, iter_succ, h]

-- B. Strict growth and cardinality --------------------------------------------

theorem iter_ssubset_of_ne {n : Nat} (h_ne : iter sys n ≠ iter sys (n + 1)) :
    iter sys n ⊂ iter sys (n + 1) := by
  have h_sub : iter sys n ⊆ iter sys (n + 1) := iter_mono sys n
  have h_not_rev : ¬ iter sys (n + 1) ⊆ iter sys n := by
    intro h_rev
    apply h_ne
    apply Finset.Subset.antisymm h_sub h_rev
  exact ⟨h_sub, h_not_rev⟩

theorem iter_card_lt_of_ne {n : Nat} (h_ne : iter sys n ≠ iter sys (n + 1)) :
    Finset.card (iter sys n) < Finset.card (iter sys (n + 1)) :=
  Finset.card_lt_card (iter_ssubset_of_ne sys h_ne)

theorem iter_card_le_universe (n : Nat) : Finset.card (iter sys n) ≤ Finset.card sys.universe :=
  Finset.card_le_card (iter_subset_universe sys n)

-- C. Finite stabilization ----------------------------------------------------

theorem exists_fixpoint_le_card :
    ∃ k, k ≤ Finset.card sys.universe ∧ iter sys k = iter sys (k + 1) := by
  by_contra! h
  let bound := Finset.card sys.universe
  have h_card_lt : ∀ k, k ≤ bound → Finset.card (iter sys k) < Finset.card (iter sys (k + 1)) := by
    intro k hk
    apply iter_card_lt_of_ne sys (h k hk)
  have h_card_chain : ∀ k, k ≤ bound + 1 → Finset.card (iter sys 0) + k ≤ Finset.card (iter sys k) := by
    intro k hk
    induction k with
    | zero => rfl
    | succ m ih =>
      have hm : m ≤ bound := Nat.le_of_succ_le_succ hk
      have h_lt := h_card_lt m hm
      calc
        Finset.card (iter sys 0) + (m + 1) = (Finset.card (iter sys 0) + m) + 1 := by rw [Nat.add_assoc]
        _ ≤ Finset.card (iter sys m) + 1 := Nat.succ_le_succ ih
        _ ≤ Finset.card (iter sys (m + 1)) := Nat.succ_le_of_lt h_lt
  have h_card_0 : Finset.card (iter sys 0) = 0 := by simp [iter]
  have h_final_chain := h_card_chain (bound + 1) (le_refl _)
  rw [h_card_0] at h_final_chain
  have h_final_bound : Finset.card (iter sys (bound + 1)) ≤ bound :=
    iter_card_le_universe sys (bound + 1)
  have h_contra : 0 + (bound + 1) ≤ bound := le_trans h_final_chain h_final_bound
  have h_bad : bound + 1 ≤ bound := by
    simpa [zero_add] using h_contra
  exact Nat.not_succ_le_self bound h_bad

theorem fixed_at_card : iter sys (Finset.card sys.universe) = iter sys (Finset.card sys.universe + 1) := by
  have h := exists_fixpoint_le_card sys
  rcases h with ⟨k, hk, h_eq⟩
  have h_stable : ∀ m, iter sys (k + m) = iter sys k := iter_stable sys h_eq
  have h1 : Finset.card sys.universe = k + (Finset.card sys.universe - k) :=
    (Nat.add_sub_cancel hk).symm
  have h2 : Finset.card sys.universe + 1 = k + ((Finset.card sys.universe - k) + 1) := by
    rw [h1, Nat.add_assoc]
  rw [h1, h2]
  rw [h_stable (Finset.card sys.universe - k), h_stable ((Finset.card sys.universe - k) + 1)]

end FiniteMonotoneSystem
