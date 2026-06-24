import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import JurisLean.FiniteMonotoneIteration
import JurisLean.HornDefinitions

open Finset

namespace HornSystem

/-! Horn Fixpoint Theorems — S4-A: Semantic Correctness.
All 10 theorems proved using the FiniteMonotoneSystem kernel.
-/

variable {α : Type} [DecidableEq α] (sys : HornSystem α)

/-- 1: horn_operator_subset_univ — already proved as TH_subset_univ. -/
theorem horn_operator_subset_univ (S : Finset α) : TH sys S ⊆ sys.univ :=
  TH_subset_univ sys S

/-- 2: horn_operator_monotone — already proved as TH_monotone. -/
theorem horn_operator_monotone {S T : Finset α} (hST : S ⊆ T) : TH sys S ⊆ TH sys T :=
  TH_monotone sys hST

/-- 3: horn_iteration_monotone — from the generic kernel. -/
theorem horn_iteration_monotone (k : Nat) :
    FiniteMonotoneSystem.iter (toFiniteMonotoneSystem sys) k ⊆
    FiniteMonotoneSystem.iter (toFiniteMonotoneSystem sys) (k + 1) :=
  FiniteMonotoneSystem.iter_mono (toFiniteMonotoneSystem sys) k

/-- 4: horn_finite_termination — fixpoint is reached within |univ| steps. -/
theorem horn_finite_termination : ∃ k, k ≤ Finset.card sys.univ ∧
    FiniteMonotoneSystem.iter (toFiniteMonotoneSystem sys) k =
    FiniteMonotoneSystem.iter (toFiniteMonotoneSystem sys) (k + 1) :=
  FiniteMonotoneSystem.exists_fixpoint_le_card (toFiniteMonotoneSystem sys)

/-- 5: horn_iteration_bound — at most |univ| iterations needed. -/
theorem horn_iteration_bound : FiniteMonotoneSystem.iter (toFiniteMonotoneSystem sys)
    (Finset.card sys.univ) =
    FiniteMonotoneSystem.iter (toFiniteMonotoneSystem sys) (Finset.card sys.univ + 1) :=
  FiniteMonotoneSystem.fixed_at_card (toFiniteMonotoneSystem sys)

/-- 6: horn_result_fixed_point — the iteration result is a fixed point of T_H. -/
theorem horn_result_fixed_point :
    TH sys (FiniteMonotoneSystem.iter (toFiniteMonotoneSystem sys) (Finset.card sys.univ)) =
    FiniteMonotoneSystem.iter (toFiniteMonotoneSystem sys) (Finset.card sys.univ) := by
  have h_fixed := FiniteMonotoneSystem.fixed_at_card (toFiniteMonotoneSystem sys)
  -- rewrite iter_succ at h_fixed using toFiniteMonotoneSystem.univ
  have h_succ := FiniteMonotoneSystem.iter_succ (toFiniteMonotoneSystem sys)
    (Finset.card (toFiniteMonotoneSystem sys).univ)
  -- h_succ: iter(card+1) = step(iter(card))
  -- h_fixed: iter(card) = iter(card+1)
  -- Combine: iter(card) = step(iter(card)) = TH(iter(card))
  have h_comb : (toFiniteMonotoneSystem sys).step
    (FiniteMonotoneSystem.iter (toFiniteMonotoneSystem sys) (Finset.card (toFiniteMonotoneSystem sys).univ)) =
    FiniteMonotoneSystem.iter (toFiniteMonotoneSystem sys) (Finset.card (toFiniteMonotoneSystem sys).univ) := by
    rw [← h_succ, h_fixed]
  simpa [toFiniteMonotoneSystem] using h_comb

/-- 7: horn_result_least_fixed_point — the iteration result is the least fixed point. -/
theorem horn_result_least_fixed_point (S : Finset α) (hS : TH sys S = S) :
    FiniteMonotoneSystem.iter (toFiniteMonotoneSystem sys) (Finset.card sys.univ) ⊆ S := by
  have h_ind : ∀ n : Nat, FiniteMonotoneSystem.iter (toFiniteMonotoneSystem sys) n ⊆ S := by
    intro n
    induction n with
    | zero => simp [FiniteMonotoneSystem.iter]
    | succ m ih =>
      rw [FiniteMonotoneSystem.iter_succ]
      unfold toFiniteMonotoneSystem
      have h_mono := TH_monotone sys ih
      simpa [hS] using h_mono
  exact h_ind (Finset.card sys.univ)

/-- 8: horn_soundness — every derived atom is in the univ. -/
theorem horn_soundness :
    FiniteMonotoneSystem.iter (toFiniteMonotoneSystem sys) (Finset.card sys.univ) ⊆ sys.univ :=
  FiniteMonotoneSystem.iter_subset_univ (toFiniteMonotoneSystem sys) (Finset.card sys.univ)

/-- 9: horn_completeness — every atom that must be in any fixed point is derived. -/
theorem horn_completeness (a : α) (h : ∀ S, TH sys S = S → a ∈ S) :
    a ∈ FiniteMonotoneSystem.iter (toFiniteMonotoneSystem sys) (Finset.card sys.univ) :=
  -- The result is a fixed point (horn_result_fixed_point), so a is in it
  h _ (horn_result_fixed_point sys)

/-- 10: horn_result_is_minimal_model — the fixpoint is the unique minimal model. -/
theorem horn_result_is_minimal_model :
    ∃! M, TH sys M = M ∧ ∀ N, TH sys N = N → M ⊆ N := by
  let result := FiniteMonotoneSystem.iter (toFiniteMonotoneSystem sys) (Finset.card sys.univ)
  have h_fp : TH sys result = result := horn_result_fixed_point sys
  have h_least : ∀ N, TH sys N = N → result ⊆ N := horn_result_least_fixed_point sys
  refine ⟨result, ⟨h_fp, h_least⟩, ?_⟩
  intro M ⟨hM_fp, hM_least⟩
  apply Finset.Subset.antisymm (hM_least result h_fp) (h_least M hM_fp)

end HornSystem
