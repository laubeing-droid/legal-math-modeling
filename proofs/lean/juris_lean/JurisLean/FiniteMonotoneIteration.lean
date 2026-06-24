import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

open Finset

/-! Finite Monotone Iteration Kernel.
Shared by AAF and Horn. 0 sorry, 0 axiom, 0 admit.
-/

/-- A finite monotone system: step function stays in univ and is monotone. -/
structure FiniteMonotoneSystem (α : Type) [DecidableEq α] where
  univ : Finset α
  step : Finset α → Finset α
  step_subset_univ : ∀ S, step S ⊆ univ
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

theorem iter_subset_univ (n : Nat) : iter sys n ⊆ sys.univ := by
  induction n with
  | zero => exact Finset.empty_subset _
  | succ n ih =>
    rw [iter_succ]
    exact sys.step_subset_univ _

theorem iter_mono : ∀ n, iter sys n ⊆ iter sys (n + 1)
  | 0 => Finset.empty_subset _
  | n + 1 => by
    rw [iter_succ, iter_succ]
    have h_prev : iter sys n ⊆ iter sys (n + 1) := iter_mono n
    exact sys.step_monotone h_prev

theorem iter_stable {n : Nat} (h : iter sys n = iter sys (n + 1)) : ∀ k, iter sys (n + k) = iter sys n := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    calc
      iter sys (n + (k + 1)) = sys.step (iter sys (n + k)) := by
        rw [Nat.add_succ, iter_succ]
      _ = sys.step (iter sys n) := by
        rw [ih]
      _ = iter sys (n + 1) := by
        rw [iter_succ]
      _ = iter sys n := h.symm

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
  Finset.card_lt_card (iter_ssubset_of_ne (sys := sys) h_ne)

theorem iter_card_le_univ (n : Nat) : Finset.card (iter sys n) ≤ Finset.card sys.univ :=
  Finset.card_le_card (iter_subset_univ (sys := sys) n)

-- C. Finite stabilization ----------------------------------------------------

theorem exists_fixpoint_le_card :
    ∃ k, k ≤ Finset.card sys.univ ∧ iter sys k = iter sys (k + 1) := by
  by_contra! h
  let bound := Finset.card sys.univ
  have h_card_lt : ∀ k, k ≤ bound → Finset.card (iter sys k) < Finset.card (iter sys (k + 1)) := by
    intro k hk
    apply iter_card_lt_of_ne (sys := sys) (h k hk)
  have h_card_chain : ∀ k, k ≤ bound + 1 → Finset.card (iter sys 0) + k ≤ Finset.card (iter sys k) := by
    intro k hk
    induction k with
    | zero => rfl
    | succ m ih =>
      have hm : m ≤ bound := by omega
      have h_lt := h_card_lt m hm
      omega
  have h_card_0 : Finset.card (iter sys 0) = 0 := by simp [iter]
  have h_final_chain : bound + 1 ≤ Finset.card (iter sys (bound + 1)) := by
    simpa [h_card_0] using h_card_chain (bound + 1) (le_refl _)
  have h_final_bound : Finset.card (iter sys (bound + 1)) ≤ bound :=
    iter_card_le_univ (sys := sys) (bound + 1)
  have : bound + 1 ≤ bound := le_trans h_final_chain h_final_bound
  omega

theorem fixed_at_card : iter sys (Finset.card sys.univ) = iter sys (Finset.card sys.univ + 1) := by
  have h := exists_fixpoint_le_card (sys := sys)
  rcases h with ⟨k, hk, h_eq⟩
  have h_stable : ∀ m, iter sys (k + m) = iter sys k := iter_stable (sys := sys) h_eq
  have h1 : Finset.card sys.univ = k + (Finset.card sys.univ - k) := by omega
  have h2 : Finset.card sys.univ + 1 = k + ((Finset.card sys.univ - k) + 1) := by omega
  have h_left : iter sys (Finset.card sys.univ) = iter sys k := by
    rw [h1]
    simpa using h_stable (Finset.card sys.univ - k)
  have h_right : iter sys (Finset.card sys.univ + 1) = iter sys k := by
    rw [h2]
    simpa using h_stable ((Finset.card sys.univ - k) + 1)
  exact h_left.trans h_right.symm

end FiniteMonotoneSystem
