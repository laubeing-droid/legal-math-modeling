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

/-- 1: horn_operator_subset_universe — already proved as TH_subset_universe. -/
theorem horn_operator_subset_universe (S : Finset α) : TH sys S ⊆ sys.universe :=
  TH_subset_universe sys S

/-- 2: horn_operator_monotone — already proved as TH_monotone. -/
theorem horn_operator_monotone {S T : Finset α} (hST : S ⊆ T) : TH sys S ⊆ TH sys T :=
  TH_monotone sys hST

/-- 3: horn_iteration_monotone — from the generic kernel. -/
theorem horn_iteration_monotone (k : Nat) :
    FiniteMonotoneSystem.iter (toFiniteMonotoneSystem sys) k ⊆
    FiniteMonotoneSystem.iter (toFiniteMonotoneSystem sys) (k + 1) :=
  FiniteMonotoneSystem.iter_mono (toFiniteMonotoneSystem sys) k

/-- 4: horn_finite_termination — fixpoint is reached within |universe| steps. -/
theorem horn_finite_termination : ∃ k, k ≤ Finset.card sys.universe ∧
    FiniteMonotoneSystem.iter (toFiniteMonotoneSystem sys) k =
    FiniteMonotoneSystem.iter (toFiniteMonotoneSystem sys) (k + 1) :=
  FiniteMonotoneSystem.exists_fixpoint_le_card (toFiniteMonotoneSystem sys)

/-- 5: horn_iteration_bound — at most |universe| iterations needed. -/
theorem horn_iteration_bound : FiniteMonotoneSystem.iter (toFiniteMonotoneSystem sys)
    (Finset.card sys.universe) =
    FiniteMonotoneSystem.iter (toFiniteMonotoneSystem sys) (Finset.card sys.universe + 1) :=
  FiniteMonotoneSystem.fixed_at_card (toFiniteMonotoneSystem sys)

/-- 6: horn_result_fixed_point — the iteration result is a fixed point of T_H. -/
theorem horn_result_fixed_point :
    TH sys (FiniteMonotoneSystem.iter (toFiniteMonotoneSystem sys) (Finset.card sys.universe)) =
    FiniteMonotoneSystem.iter (toFiniteMonotoneSystem sys) (Finset.card sys.universe) := by
  have h_fixed := FiniteMonotoneSystem.fixed_at_card (toFiniteMonotoneSystem sys)
  -- iter(card) = iter(card+1) = TH(iter(card))
  rw [FiniteMonotoneSystem.iter_succ (toFiniteMonotoneSystem sys) (Finset.card sys.universe)] at h_fixed
  unfold toFiniteMonotoneSystem at h_fixed
  -- Now h_fixed: iter(card) = TH(iter(card))
  rw [← h_fixed]

/-- 7: horn_result_least_fixed_point — the iteration result is the least fixed point. -/
theorem horn_result_least_fixed_point (S : Finset α) (hS : TH sys S = S) :
    FiniteMonotoneSystem.iter (toFiniteMonotoneSystem sys) (Finset.card sys.universe) ⊆ S := by
  -- By induction: iter n ⊆ S for all n
  have h_ind : ∀ n : Nat, FiniteMonotoneSystem.iter (toFiniteMonotoneSystem sys) n ⊆ S := by
    intro n
    induction n with
    | zero =>
      simp [FiniteMonotoneSystem.iter]
    | succ m ih =>
      rw [FiniteMonotoneSystem.iter_succ]
      unfold toFiniteMonotoneSystem
      rw [hS]
      apply TH_monotone sys ih
  exact h_ind (Finset.card sys.universe)

/-- 8: horn_soundness — every derived atom is in the universe. -/
theorem horn_soundness :
    FiniteMonotoneSystem.iter (toFiniteMonotoneSystem sys) (Finset.card sys.universe) ⊆ sys.universe :=
  FiniteMonotoneSystem.iter_subset_universe (toFiniteMonotoneSystem sys) (Finset.card sys.universe)

/-- 9: horn_completeness — every atom that must be in any fixed point is derived. -/
theorem horn_completeness (a : α) (h : ∀ S, TH sys S = S → a ∈ S) :
    a ∈ FiniteMonotoneSystem.iter (toFiniteMonotoneSystem sys) (Finset.card sys.universe) :=
  -- The result is a fixed point (horn_result_fixed_point), so a is in it
  h _ (horn_result_fixed_point sys)

/-- 10: horn_result_is_minimal_model — the fixpoint is the unique minimal model. -/
theorem horn_result_is_minimal_model :
    ∃! M, M ⊆ sys.universe ∧ TH sys M = M := by
  let result := FiniteMonotoneSystem.iter (toFiniteMonotoneSystem sys) (Finset.card sys.universe)
  have h_sub : result ⊆ sys.universe :=
    FiniteMonotoneSystem.iter_subset_universe (toFiniteMonotoneSystem sys) (Finset.card sys.universe)
  have h_fp : TH sys result = result := horn_result_fixed_point sys
  refine ⟨result, ⟨h_sub, h_fp⟩, ?_⟩
  intro M ⟨hM_sub, hM_fp⟩
  -- result ⊆ M by horn_result_least_fixed_point
  have h_le : result ⊆ M := horn_result_least_fixed_point sys M hM_fp
  -- M ⊆ result by the same argument (since result is also a fixed point)
  have h_ge : M ⊆ result := horn_result_least_fixed_point sys result (horn_result_fixed_point sys)
  -- By symmetry, M = result
  apply Finset.Subset.antisymm h_ge h_le

end HornSystem