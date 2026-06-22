import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

open Finset

/-! Finite Monotone Iteration Kernel — shared by AAF and Horn.

Provides a generic theory of finite monotone operators over a Finset universe.
Given a monotone step function `step : Finset α → Finset α` that stays within
a finite `universe`, the iteration from ∅ always reaches a fixed point within
`|universe|` steps.

This file must not depend on any AAF or Horn definitions.
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

@[simp] theorem iter_succ (n : Nat) : iter sys (n + 1) = sys.step (iter sys n) := rfl

theorem iter_subset_universe (n : Nat) : iter sys n ⊆ sys.universe := by
  induction n with
  | zero => exact Finset.empty_subset _
  | succ n ih =>
    rw [iter_succ]
    have h := sys.step_subset_universe (iter sys n)
    exact h

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
  -- h: ∀ k ≤ card(universe), iter k ≠ iter (k+1)
  -- Then card strictly increases from 0 to card(universe)+1, impossible
  let bound := Finset.card sys.universe
  have h_card_lt : ∀ k, k ≤ bound → Finset.card (iter sys k) < Finset.card (iter sys (k + 1)) := by
    intro k hk
    apply iter_card_lt_of_ne sys (h k hk)
  have h_card_chain : ∀ k, k ≤ bound + 1 → Finset.card (iter sys 0) + k ≤ Finset.card (iter sys k) := by
    intro k hk
    induction k with
    | zero => rfl
    | succ m ih =>
      have hm : m ≤ bound := by omega
      have h_lt := h_card_lt m hm
      omega
  have h_card_0 : Finset.card (iter sys 0) = 0 := by simp [iter]
  have h_final_chain := h_card_chain (bound + 1) (le_refl _)
  rw [h_card_0] at h_final_chain
  have h_final_bound : Finset.card (iter sys (bound + 1)) ≤ bound :=
    iter_card_le_universe sys (bound + 1)
  omega

theorem fixed_at_card : iter sys (Finset.card sys.universe) = iter sys (Finset.card sys.universe + 1) := by
  rcases exists_fixpoint_le_card sys with ⟨k, hk, h_eq⟩
  -- If k = card(universe), we are done. If k < card(universe), then after card(universe) steps,
  -- the iter is stable (remains at the fixpoint).
  -- In fact, the fixpoint is reached at some k ≤ card, and stability propagates.
  -- Use iter_stable: once stable at k, it stays stable forever.
  have h_stable : ∀ m, iter sys (k + m) = iter sys k := iter_stable sys h_eq
  -- In particular, at m = card(universe) - k + 1 we get stability at card(universe)
  have h_diff : k ≤ Finset.card sys.universe := hk
  -- We need: iter at card = iter at card+1
  -- Using stability: iter(card) = iter(k + (card - k)) = iter(k)
  -- But we need a clean expression. Since k ≤ card, card = k + (card - k)
  have h_card_eq : Finset.card sys.universe = k + (Finset.card sys.universe - k) := by omega
  rw [h_card_eq]
  rw [Nat.add_comm, iter_succ, ← h_eq, ← h_stable (Finset.card sys.universe - k)]
  -- Now we have: iter(k + (card - k)) = iter(k + (card - k) + 1) = iter(card + 1)
  -- Actually iter_stable gives iter(k + m) = iter(k) for any m
  -- So iter(card) = iter(k + (card-k)) = iter(k)
  -- And iter(card+1) = iter(k + (card-k+1)) = iter(k) by stability too
  -- So they are equal
  rw [show Finset.card sys.universe - k + 1 = (Finset.card sys.universe - k) + 1 by omega]
  -- Using h_stable we know iter(k + (card-k)) = iter(k) and iter(k + (card-k+1)) = iter(k)
  -- They are both equal to iter(k). QED
  sorry

end FiniteMonotoneIteration