import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-! G9A: Dung Grounded Semantics — B1 formal objects, B2 theorem signatures.
  Proofs marked sorry are pending Lean proof completion. -/

open Finset

abbrev Arg : Type := String

structure DungAAF where
  args : Finset Arg
  attacks : Finset (Arg × Arg)
deriving DecidableEq, Inhabited

namespace DungAAF

def attackers (aaf : DungAAF) (a : Arg) : Finset Arg :=
  aaf.args.filter (fun b => (b, a) ∈ aaf.attacks)

def F (aaf : DungAAF) (S : Finset Arg) : Finset Arg :=
  aaf.args.filter (fun a =>
    ∀ b ∈ attackers aaf a, ((attackers aaf b).filter (fun c => c ∈ S)) ≠ ∅)

def groundedExtension (aaf : DungAAF) : Finset Arg × Bool × Nat :=
  let bound := aaf.args.card + 1
  let rec go (k : Nat) (acc : Finset Arg) : Finset Arg × Bool × Nat :=
    if h : k < bound then
      let next := F aaf acc
      if next = acc then (acc, true, k) else go (k+1) next
    else (acc, false, bound)
  go 0 ∅

def grounded (aaf : DungAAF) : Finset Arg := (groundedExtension aaf).1

def labelling (aaf : DungAAF) : Finset Arg × Finset Arg × Finset Arg :=
  let ge := grounded aaf
  let out := aaf.args.filter (fun a => a ∉ ge ∧ (attackers aaf a).filter (fun b => b ∈ ge) ≠ ∅)
  let undec := aaf.args \ (ge ∪ out)
  (ge, out, undec)


/-- Iterate F k times from the empty set. -/
def iterF (aaf : DungAAF) : Nat → Finset Arg
  | 0 => ∅
  | n+1 => F aaf (iterF aaf n)

/-! 13 Core Theorems (all proofs pending) -/

theorem F_monotone (aaf : DungAAF) (S T : Finset Arg) (hST : S ⊆ T) : F aaf S ⊆ F aaf T := by
  intro a ha
  rw [F, Finset.mem_filter] at ha ⊢
  rcases ha with ⟨ha_args, ha_cond⟩
  refine ⟨ha_args, ?_⟩
  intro b hb
  have h_prev : ((attackers aaf b).filter (fun c => c ∈ S)) ≠ ∅ := ha_cond b hb
  have h_sub : ((attackers aaf b).filter (fun c => c ∈ S)) ⊆ ((attackers aaf b).filter (fun c => c ∈ T)) := by
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hx_att, hx_S⟩
    apply Finset.mem_filter.mpr
    exact ⟨hx_att, hST hx_S⟩
  intro h_empty
  apply h_prev
  have h_sub_empty : ((attackers aaf b).filter (fun c => c ∈ S)) ⊆ (∅ : Finset Arg) := by
    intro x hx
    have hx_T := h_sub hx
    rw [h_empty] at hx_T
    simp at hx_T
  exact Finset.Subset.antisymm h_sub_empty (Finset.empty_subset _)

theorem iteration_monotone (aaf : DungAAF) (k : Nat) : iterF aaf k ⊆ iterF aaf (k+1) := by
  induction k with
  | zero => simp [iterF]
  | succ m ih =>
    simp [iterF]
    apply F_monotone aaf (iterF aaf m) (iterF aaf (m+1)) ih

theorem finite_termination (aaf : DungAAF) : (groundedExtension aaf).2.1 := by
  sorry

theorem iteration_bound (aaf : DungAAF) : (groundedExtension aaf).2.2 ≤ aaf.args.card + 1 := by
  sorry

theorem grounded_is_fixed_point (aaf : DungAAF) : F aaf (grounded aaf) = grounded aaf := by
  sorry

theorem grounded_is_least_fixed_point (aaf : DungAAF) (S : Finset Arg) (hS : F aaf S = S) :
    grounded aaf ⊆ S := by
  sorry

theorem grounded_is_least_complete (aaf : DungAAF) (S : Finset Arg) (hS : F aaf S = S) :
    grounded aaf ⊆ S := by
  sorry

theorem grounded_unique (aaf : DungAAF) : ∃! ge, F aaf ge = ge := by
  sorry

theorem labelling_partition (aaf : DungAAF) :
    (labelling aaf).1 ∩ (labelling aaf).2.1 = ∅ ∧
    (labelling aaf).1 ∩ (labelling aaf).2.2 = ∅ ∧
    (labelling aaf).2.1 ∩ (labelling aaf).2.2 = ∅ ∧
    (labelling aaf).1 ∪ (labelling aaf).2.1 ∪ (labelling aaf).2.2 = aaf.args := by
  unfold labelling
  let ge := grounded aaf
  let out := aaf.args.filter (fun a => a ∉ ge ∧ (attackers aaf a).filter (fun b => b ∈ ge) ≠ ∅)
  let undec := aaf.args \ (ge ∪ out)
  have h1 : ge ∩ out = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro x hx
    rcases Finset.mem_inter.mp hx with ⟨hx_ge, hx_out⟩
    rcases Finset.mem_filter.mp hx_out with ⟨_, ⟨hx_not_ge, _⟩⟩
    exact hx_not_ge hx_ge
  have h2 : out ∩ undec = ∅ := by
    rw [Finset.sdiff_eq_empty_iff_subset]
    apply Finset.subset_union_right
  have h3 : ge ∩ undec = ∅ := by
    rw [Finset.sdiff_eq_empty_iff_subset]
    apply Finset.subset_union_left
  have h4 : ge ∪ out ∪ undec = aaf.args := by
    rw [Finset.union_sdiff_self]
    apply Finset.union_subset ?_ (Finset.filter_subset _ _)
    -- ge = grounded aaf. But we can't prove ge ⊆ aaf.args without iterF lemma
    -- Accept this gap
    sorry
  exact ⟨h1, h3, h2, h4⟩

theorem in_soundness (aaf : DungAAF) (a : Arg) (h : a ∈ grounded aaf) :
    ∀ b ∈ attackers aaf a, ((attackers aaf b).filter (fun c => c ∈ grounded aaf)) ≠ ∅ := by
  sorry

theorem out_soundness (aaf : DungAAF) (a : Arg) (h : a ∈ (labelling aaf).2.1) :
    (attackers aaf a).filter (fun b => b ∈ grounded aaf) ≠ ∅ := by
  unfold labelling at h
  rcases Finset.mem_filter.mp h with ⟨_, ⟨_, h_att⟩⟩
  exact h_att

theorem undecided_characterization (aaf : DungAAF) (a : Arg) :
    a ∈ (labelling aaf).2.2.1 ↔ a ∉ grounded aaf ∧ (attackers aaf a).filter (fun b => b ∈ grounded aaf) = ∅ := by
  sorry

theorem self_attack_undecided (aaf : DungAAF) (a : Arg) (hself : (a, a) ∈ aaf.attacks) (honly : attackers aaf a = {a}) :
    a ∉ grounded aaf := by
  sorry

end DungAAF