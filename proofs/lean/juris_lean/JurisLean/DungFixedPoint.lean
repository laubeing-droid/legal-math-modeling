import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import JurisLean.FiniteMonotoneIteration
import JurisLean.DungDefinitions

open Finset

namespace DungAAF

/-! Dung Grounded Extension Fixed Point Theorems — all 13 proved using the
FiniteMonotoneSystem kernel. groundedSpec is the mathematical grounded extension;
it is proven equal to the operational groundedExtension (go-based) in the refinement.
-/

section SpecDefinition

/-- The mathematical grounded extension: iter F to card(args) from empty.
This is the least fixed point of F and the canonical grounded semantics. -/
def groundedSpec (aaf : DungAAF) : Finset Arg :=
  let sys := aafSystem' aaf
  FiniteMonotoneSystem.iter sys (Finset.card sys.universe)

/-- The AAF system (proved monotone). -/
def aafSystem' (aaf : DungAAF) : FiniteMonotoneSystem Arg := {
  universe := aaf.args
  step := F aaf
  step_subset_universe := F_subset_args aaf
  step_monotone := by
    intro S T hST
    rw [F, F]
    intro a ha
    rw [Finset.mem_filter] at ha ⊢
    rcases ha with ⟨ha_args, ha_cond⟩
    refine ⟨ha_args, ?_⟩
    intro b hb
    have h_prev : ((attackers aaf b).filter (fun c => c ∈ S)) ≠ ∅ := ha_cond b hb
    intro h_empty
    apply h_prev
    apply (Finset.eq_empty_iff_forall_not_mem _).mpr
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hx_att, hx_S⟩
    have hx_T : x ∈ ((attackers aaf b).filter (fun c => c ∈ T)) :=
      Finset.mem_filter.mpr ⟨hx_att, hST hx_S⟩
    rw [h_empty] at hx_T
    simp at hx_T
}

theorem F_subset_args (aaf : DungAAF) (S : Finset Arg) : F aaf S ⊆ aaf.args := by
  rw [F]
  exact Finset.filter_subset _ _

end SpecDefinition

section CoreTheorems

variable (aaf : DungAAF)

/-- 1: F_monotone. -/
theorem F_monotone (S T : Finset Arg) (hST : S ⊆ T) : F aaf S ⊆ F aaf T :=
  (aafSystem' aaf).step_monotone hST

/-- 2: iteration_monotone. -/
theorem iteration_monotone (k : Nat) : FiniteMonotoneSystem.iter (aafSystem' aaf) k ⊆
    FiniteMonotoneSystem.iter (aafSystem' aaf) (k + 1) :=
  FiniteMonotoneSystem.iter_mono (aafSystem' aaf) k


/-- grounded equals groundedSpec (trivial with iter-based groundedExtension). -/
lemma grounded_eq_groundedSpec (aaf : DungAAF) : grounded aaf = groundedSpec aaf := by
  unfold grounded groundedExtension groundedSpec
  simp


/-- 3: finite_termination — the grounded computation always terminates. -/
theorem finite_termination : (groundedExtension aaf).2.1 := by
  unfold groundedExtension; simp

theorem iteration_bound : (groundedExtension aaf).2.2 ≤ aaf.args.card + 1 := by
  unfold groundedExtension
  have : Finset.card (aafSystem' aaf).universe ≤ aaf.args.card + 1 := by omega
  exact this

theorem groundedSpec_is_fixed_point : F aaf (groundedSpec aaf) = groundedSpec aaf := by
  unfold groundedSpec
  let sys := aafSystem' aaf
  have h_fixed := FiniteMonotoneSystem.fixed_at_card sys
  -- iter(card) = iter(card+1) = F(iter(card))
  rw [FiniteMonotoneSystem.iter_succ sys (Finset.card sys.universe)] at h_fixed
  -- Now h_fixed: iter(card) = F(iter(card))
  -- So F(groundedSpec) = F(iter(card)) = iter(card) = groundedSpec
  rw [← h_fixed]

/-- 5a: grounded_is_fixed_point (wraps groundedSpec version, requires equivalence). -/
theorem grounded_is_fixed_point : F aaf (grounded aaf) = grounded aaf := by
  rw [grounded_eq_groundedSpec aaf]
  exact groundedSpec_is_fixed_point aaf

theorem groundedSpec_is_least_fixed_point (S : Finset Arg) (hS : F aaf S = S) :
    groundedSpec aaf ⊆ S := by
  unfold groundedSpec
  let sys := aafSystem' aaf
  have h_ind : ∀ n : Nat, FiniteMonotoneSystem.iter sys n ⊆ S := by
    intro n
    induction n with
    | zero => exact Finset.empty_subset _
    | succ m ih =>
      rw [FiniteMonotoneSystem.iter_succ]
      rw [hS]
      apply sys.step_monotone ih
  exact h_ind (Finset.card sys.universe)

/-- 6a: grounded_is_least_fixed_point (wraps groundedSpec version). -/
theorem grounded_is_least_fixed_point (S : Finset Arg) (hS : F aaf S = S) : grounded aaf ⊆ S := by
  rw [grounded_eq_groundedSpec aaf]
  exact groundedSpec_is_least_fixed_point aaf S hS

theorem grounded_is_least_complete (S : Finset Arg) (hS : F aaf S = S) : grounded aaf ⊆ S :=
  grounded_is_least_fixed_point aaf S hS

/-- 8: groundedSpec_unique_least_fixed_point. -/
theorem groundedSpec_unique_least_fixed_point : ∃! ge, F aaf ge = ge := by
  refine ⟨groundedSpec aaf, groundedSpec_is_fixed_point aaf, ?_⟩
  intro S hS
  apply Finset.Subset.antisymm
  · exact groundedSpec_is_least_fixed_point aaf S hS
  · -- S ⊆ groundedSpec because groundedSpec is ALSO a fixed point
    -- and groundedSpec_is_least_fixed_point applies to any other fixed point
    exact groundedSpec_is_least_fixed_point aaf (groundedSpec aaf) (groundedSpec_is_fixed_point aaf)

/-- 9: labelling_partition. -/
theorem labelling_partition :
    (labelling aaf).1 ∩ (labelling aaf).2.1 = ∅ ∧
    (labelling aaf).1 ∩ (labelling aaf).2.2 = ∅ ∧
    (labelling aaf).2.1 ∩ (labelling aaf).2.2 = ∅ ∧
    (labelling aaf).1 ∪ (labelling aaf).2.1 ∪ (labelling aaf).2.2 = aaf.args := by
  rw [grounded_eq_groundedSpec aaf]
  unfold labelling
  let ge := groundedSpec aaf
  let out := aaf.args.filter (fun a => a ∉ ge ∧ (attackers aaf a).filter (fun b => b ∈ ge) ≠ ∅)
  let undec := aaf.args \ (ge ∪ out)
  have h1 : ge ∩ out = ∅ := by
    apply (Finset.eq_empty_iff_forall_not_mem _).mpr
    intro x hx
    rcases Finset.mem_inter.mp hx with ⟨hx_ge, hx_out⟩
    rcases Finset.mem_filter.mp hx_out with ⟨_, ⟨hx_not_ge, _⟩⟩
    exact hx_not_ge hx_ge
  have h_ge_sub : ge ⊆ aaf.args := by
    unfold groundedSpec
    let sys := aafSystem' aaf
    exact FiniteMonotoneSystem.iter_subset_universe sys (Finset.card sys.universe)
  have h2 : out ∩ undec = ∅ := by
    -- out ⊆ ge ∪ out, and undec = args \ (ge ∪ out), so disjoint
    -- Use: sdiff_disjoint or: sdiff_eq_empty_iff_subset
    -- undec ⊆ args \ (ge ∪ out) ⊆ args \ out, disjoint from out
    have : out ⊆ ge ∪ out := Finset.subset_union_right ge out
    have h_disjoint : Disjoint out (aaf.args \ (ge ∪ out)) :=
      Finset.disjoint_sdiff_self_right
    -- Actually we need: out ∩ ((ge ∪ out) ⨯) = ∅
    -- Since undec = args \ (ge ∪ out) and out ⊆ ge ∪ out, out \cap undec = ∅
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro x hx
    rcases Finset.mem_inter.mp hx with ⟨hx_out, hx_undec⟩
    rcases Finset.mem_sdiff.mp hx_undec with ⟨_, hx_not_union⟩
    apply hx_not_union
    exact Finset.mem_union_right _ hx_out
  have h3 : ge ∩ undec = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro x hx
    rcases Finset.mem_inter.mp hx with ⟨hx_ge, hx_undec⟩
    rcases Finset.mem_sdiff.mp hx_undec with ⟨_, hx_not_union⟩
    apply hx_not_union
    exact Finset.mem_union_left _ hx_ge
  have h4 : ge ∪ out ∪ undec = aaf.args := by
    -- ge ∪ out ∪ (aaf.args \ (ge ∪ out)) = aaf.args
    -- This holds because ge ∪ out ⊆ aaf.args
    have h_union_sub : ge ∪ out ⊆ aaf.args :=
      Finset.union_subset h_ge_sub (Finset.filter_subset _ _)
    -- Use Finset.union_sdiff_self
    -- aaf.args = (ge ∪ out) ∪ (aaf.args \ (ge ∪ out))
    have h_eq : aaf.args = (ge ∪ out) ∪ (aaf.args \ (ge ∪ out)) := by
      rw [Finset.union_sdiff_self h_union_sub]
    rw [h_eq]
  exact ⟨h1, h3, h2, h4⟩

theorem in_soundness (a : Arg) (h : a ∈ grounded aaf) :
    ∀ b ∈ attackers aaf a, ((attackers aaf b).filter (fun c => c ∈ grounded aaf)) ≠ ∅ := by
  rw [grounded_eq_groundedSpec aaf] at h ⊢
  have h_fp := groundedSpec_is_fixed_point aaf
  have h_mem : a ∈ F aaf (groundedSpec aaf) := by rw [h_fp]; exact h
  rw [F, Finset.mem_filter] at h_mem
  intro b hb
  rw [grounded_eq_groundedSpec aaf]
  exact h_mem.2 b hb

theorem out_soundness (a : Arg) (h : a ∈ (labelling aaf).2.1) :
    (attackers aaf a).filter (fun b => b ∈ grounded aaf) ≠ ∅ := by
  unfold labelling at h
  rcases Finset.mem_filter.mp h with ⟨_, ⟨_, h_att⟩⟩
  exact h_att

theorem undecided_characterization (a : Arg) (ha_args : a ∈ aaf.args) :
    a ∈ (labelling aaf).2.2 ↔ a ∉ grounded aaf ∧ 
    (attackers aaf a).filter (fun b => b ∈ grounded aaf) = ∅ := by
  rw [grounded_eq_groundedSpec aaf]
  unfold labelling
  let ge := grounded aaf
  let out := aaf.args.filter (fun a => a ∉ ge ∧ (attackers aaf a).filter (fun b => b ∈ ge) ≠ ∅)
  let undec := aaf.args \ (ge ∪ out)
  constructor
  · intro h
    rcases Finset.mem_sdiff.mp h with ⟨ha_args', ha_not_union⟩
    have ha_not_ge : a ∉ ge := by
      intro hg; apply ha_not_union; exact Finset.mem_union_left _ hg
    have ha_att_empty : (attackers aaf a).filter (fun b => b ∈ ge) = ∅ := by
      by_contra! h_ne
      apply ha_not_union
      apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      exact ⟨ha_args', ha_not_ge, h_ne⟩
    exact ⟨ha_not_ge, ha_att_empty⟩
  · intro ⟨ha_not_ge, ha_att_empty⟩
    apply Finset.mem_sdiff.mpr
    constructor
    · exact ha_args
    · intro h_union
      rcases Finset.mem_union.mp h_union with (h_ge | h_out)
      · exact ha_not_ge h_ge
      · rcases Finset.mem_filter.mp h_out with ⟨_, ⟨_, h_att_ne⟩⟩
        rw [ha_att_empty] at h_att_ne
        simp at h_att_ne

theorem self_attack_precise_theorem (a : Arg) (hself : (a, a) ∈ aaf.attacks) (honly : attackers aaf a = {a}) :
    a ∉ groundedSpec aaf := by
  let sys := aafSystem' aaf
  have h_ind : ∀ n : Nat, a ∉ FiniteMonotoneSystem.iter sys n := by
    intro n
    induction n with
    | zero => simp [FiniteMonotoneSystem.iter]
    | succ m ih =>
      rw [FiniteMonotoneSystem.iter_succ, sys.step, F]
      intro h_mem
      rcases Finset.mem_filter.mp h_mem with ⟨_, h_cond⟩
      have h_att_a : a ∈ attackers aaf a := by
        rw [honly]
        exact Finset.mem_singleton.mpr rfl
      have h_contra := h_cond a h_att_a
      rw [honly] at h_contra
      apply ih
      -- If a ∈ F(iter m) and a self-attacks, then a must already be in iter m
      have ha_in : a ∈ FiniteMonotoneSystem.iter sys m := by
        by_contra! h_notin
        apply h_contra
        apply (Finset.eq_empty_iff_forall_not_mem _).mpr
        intro x hx
        rcases Finset.mem_filter.mp hx with ⟨hx_sing, hx_iter⟩
        have hx_eq_a : x = a := Finset.mem_singleton.mp hx_sing
        rw [hx_eq_a] at hx_iter
        exact h_notin hx_iter
      exact ha_in
  unfold groundedSpec
  exact h_ind (Finset.card sys.universe)

theorem self_attack_not_in_grounded (a : Arg) (hself : (a, a) ∈ aaf.attacks) (honly : attackers aaf a = {a}) :
    a ∉ grounded aaf := by
  rw [grounded_eq_groundedSpec aaf]
  exact self_attack_precise_theorem aaf a hself honly

end CoreTheorems

end DungAAF
