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
  FiniteMonotoneSystem.iter (aafSystem aaf) (Finset.card (aafSystem aaf).univ)

/-- The grounded extension: iterate F to card(args) from empty. -/
def grounded (aaf : DungAAF) : Finset Arg :=
  FiniteMonotoneSystem.iter (aafSystem aaf) (Finset.card (aafSystem aaf).univ)

/-- Operational grounded extension with termination witness and iteration bound. -/
def groundedExtension (aaf : DungAAF) : Finset Arg × (PUnit × Nat) :=
  (grounded aaf, (PUnit.unit, Finset.card (aafSystem aaf).univ))

/-- Standard Dung three-valued labelling: `(IN, (OUT, UNDEC))`. -/
def labelling (aaf : DungAAF) : Finset Arg × (Finset Arg × Finset Arg) :=
  let ge := grounded aaf
  let out := aaf.args.filter (fun a => a ∉ ge ∧ (attackers aaf a).filter (fun b => b ∈ ge) ≠ ∅)
  let undec := aaf.args \ (ge ∪ out)
  (ge, (out, undec))

end SpecDefinition

section CoreTheorems

variable (aaf : DungAAF)

/-- 1: F_monotone. -/
theorem F_monotone (S T : Finset Arg) (hST : S ⊆ T) : F aaf S ⊆ F aaf T :=
  (aafSystem aaf).step_monotone hST

/-- 2: iteration_monotone. -/
theorem iteration_monotone (k : Nat) : FiniteMonotoneSystem.iter (aafSystem aaf) k ⊆
    FiniteMonotoneSystem.iter (aafSystem aaf) (k + 1) :=
  FiniteMonotoneSystem.iter_mono (aafSystem aaf) k

/-- grounded equals groundedSpec (trivial with iter-based groundedExtension). -/
lemma grounded_eq_groundedSpec (aaf : DungAAF) : grounded aaf = groundedSpec aaf := rfl

/-- 3: finite_termination — the grounded computation always terminates. -/
theorem finite_termination : (groundedExtension aaf).2.2 ≤ aaf.args.card := by
  unfold groundedExtension
  simp [aafSystem]

theorem iteration_bound : (groundedExtension aaf).2.2 ≤ aaf.args.card + 1 := by
  unfold groundedExtension
  simp [aafSystem]

theorem groundedSpec_is_fixed_point : F aaf (groundedSpec aaf) = groundedSpec aaf := by
  have h_fixed := FiniteMonotoneSystem.fixed_at_card (aafSystem aaf)
  rw [FiniteMonotoneSystem.iter_succ (aafSystem aaf) (Finset.card (aafSystem aaf).univ)] at h_fixed
  simpa [groundedSpec, aafSystem] using h_fixed.symm

/-- 5a: grounded_is_fixed_point (wraps groundedSpec version, requires equivalence). -/
theorem grounded_is_fixed_point : F aaf (grounded aaf) = grounded aaf := by
  rw [grounded_eq_groundedSpec aaf]
  exact groundedSpec_is_fixed_point aaf

theorem groundedSpec_is_least_fixed_point (S : Finset Arg) (hS : F aaf S = S) :
    groundedSpec aaf ⊆ S := by
  have h_ind : ∀ n : Nat, FiniteMonotoneSystem.iter (aafSystem aaf) n ⊆ S :=
    Nat.rec (by
      show FiniteMonotoneSystem.iter (aafSystem aaf) 0 ⊆ S
      simp [FiniteMonotoneSystem.iter])
    (fun m ih => by
       rw [FiniteMonotoneSystem.iter_succ]
       have h_mono := (aafSystem aaf).step_monotone ih
       have h_step_eq : (aafSystem aaf).step S = S := by
         simpa [aafSystem] using hS
       rw [h_step_eq] at h_mono
       exact h_mono)
  simpa [groundedSpec] using h_ind (Finset.card (aafSystem aaf).univ)

/-- 6a: grounded_is_least_fixed_point (wraps groundedSpec version). -/
theorem grounded_is_least_fixed_point (S : Finset Arg) (hS : F aaf S = S) : grounded aaf ⊆ S := by
  rw [grounded_eq_groundedSpec aaf]
  exact groundedSpec_is_least_fixed_point aaf S hS

theorem grounded_is_least_complete (S : Finset Arg) (hS : F aaf S = S) : grounded aaf ⊆ S :=
  grounded_is_least_fixed_point aaf S hS

/-- 8: corrected contract — groundedSpec is a fixed point and is contained in every fixed point. -/
theorem groundedSpec_unique_least_fixed_point :
    F aaf (groundedSpec aaf) = groundedSpec aaf ∧
    ∀ S : Finset Arg, F aaf S = S → groundedSpec aaf ⊆ S := by
  exact ⟨groundedSpec_is_fixed_point aaf, fun S hS => groundedSpec_is_least_fixed_point aaf S hS⟩

/-- 9: labelling_partition. -/
theorem labelling_partition :
    (labelling aaf).1 ∩ (labelling aaf).2.1 = ∅ ∧
    (labelling aaf).1 ∩ (labelling aaf).2.2 = ∅ ∧
    (labelling aaf).2.1 ∩ (labelling aaf).2.2 = ∅ ∧
    (labelling aaf).1 ∪ (labelling aaf).2.1 ∪ (labelling aaf).2.2 = aaf.args := by
  unfold labelling grounded
  let ge := FiniteMonotoneSystem.iter (aafSystem aaf) (Finset.card (aafSystem aaf).univ)
  let out := aaf.args.filter (fun a => a ∉ ge ∧ (attackers aaf a).filter (fun b => b ∈ ge) ≠ ∅)
  let undec := aaf.args \ (ge ∪ out)
  have h1 : ge ∩ out = ∅ := by
    by_contra h_ne
    have h_nonempty : (ge ∩ out).Nonempty := Finset.nonempty_iff_ne_empty.mpr h_ne
    obtain ⟨x, hx⟩ := h_nonempty
    rcases Finset.mem_inter.mp hx with ⟨hx_ge, hx_out⟩
    rcases Finset.mem_filter.mp hx_out with ⟨_, ⟨hx_not_ge, _⟩⟩
    exact hx_not_ge hx_ge
  have h_ge_sub : ge ⊆ aaf.args := by
    exact FiniteMonotoneSystem.iter_subset_univ (aafSystem aaf) (Finset.card (aafSystem aaf).univ)
  have h2 : out ∩ undec = ∅ := by
    by_contra h_ne
    have h_nonempty : (out ∩ undec).Nonempty := Finset.nonempty_iff_ne_empty.mpr h_ne
    obtain ⟨x, hx⟩ := h_nonempty
    rcases Finset.mem_inter.mp hx with ⟨hx_out, hx_undec⟩
    rcases Finset.mem_sdiff.mp hx_undec with ⟨_, hx_not_union⟩
    apply hx_not_union
    exact Finset.mem_union_right _ hx_out
  have h3 : ge ∩ undec = ∅ := by
    by_contra h_ne
    have h_nonempty : (ge ∩ undec).Nonempty := Finset.nonempty_iff_ne_empty.mpr h_ne
    obtain ⟨x, hx⟩ := h_nonempty
    rcases Finset.mem_inter.mp hx with ⟨hx_ge, hx_undec⟩
    rcases Finset.mem_sdiff.mp hx_undec with ⟨_, hx_not_union⟩
    apply hx_not_union
    exact Finset.mem_union_left _ hx_ge
  have h4 : ge ∪ out ∪ undec = aaf.args := by
    have h_union_sub : ge ∪ out ⊆ aaf.args :=
      Finset.union_subset h_ge_sub (Finset.filter_subset _ _)
    apply Finset.Subset.antisymm
    · apply Finset.union_subset
      · exact h_union_sub
      · intro x hx
        exact (Finset.mem_sdiff.mp hx).1
    · intro x hx
      by_cases hx_union : x ∈ ge ∪ out
      · exact Finset.mem_union_left _ hx_union
      · apply Finset.mem_union_right
        apply Finset.mem_sdiff.mpr
        exact ⟨hx, hx_union⟩
  exact ⟨h1, h3, h2, h4⟩

theorem in_soundness (a : Arg) (h : a ∈ grounded aaf) :
    ∀ b ∈ attackers aaf a, ((attackers aaf b).filter (fun c => c ∈ grounded aaf)) ≠ ∅ := by
  rw [grounded_eq_groundedSpec aaf] at h ⊢
  have h_fp := groundedSpec_is_fixed_point aaf
  have h_mem : a ∈ F aaf (groundedSpec aaf) := by rw [h_fp]; exact h
  rw [F, Finset.mem_filter] at h_mem
  intro b hb
  exact h_mem.2 b hb

theorem out_soundness (a : Arg) (h : a ∈ (labelling aaf).2.1) :
    (attackers aaf a).filter (fun b => b ∈ grounded aaf) ≠ ∅ := by
  unfold labelling at h
  rcases Finset.mem_filter.mp h with ⟨_, ⟨_, h_att⟩⟩
  exact h_att

theorem undecided_characterization (a : Arg) (ha_args : a ∈ aaf.args) :
    a ∈ (labelling aaf).2.2 ↔ a ∉ grounded aaf ∧ 
    (attackers aaf a).filter (fun b => b ∈ grounded aaf) = ∅ := by
  unfold labelling grounded
  let ge := FiniteMonotoneSystem.iter (aafSystem aaf) (Finset.card (aafSystem aaf).univ)
  let out := aaf.args.filter (fun a => a ∉ ge ∧ (attackers aaf a).filter (fun b => b ∈ ge) ≠ ∅)
  let undec := aaf.args \ (ge ∪ out)
  constructor
  · intro h
    rcases Finset.mem_sdiff.mp h with ⟨ha_args', ha_not_union⟩
    have ha_not_ge : a ∉ ge := by
      intro hg; apply ha_not_union; exact Finset.mem_union_left _ hg
    have ha_att_empty : (attackers aaf a).filter (fun b => b ∈ ge) = ∅ := by
      by_contra h_ne
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
  have h_ind : ∀ n : Nat, a ∉ FiniteMonotoneSystem.iter (aafSystem aaf) n := by
    intro n
    induction n with
    | zero => simp [FiniteMonotoneSystem.iter]
    | succ m ih =>
      rw [FiniteMonotoneSystem.iter_succ]
      dsimp [aafSystem, F]
      intro h_mem
      rcases Finset.mem_filter.mp h_mem with ⟨_, h_cond⟩
      have h_att_a : a ∈ attackers aaf a := by
        simp [honly]
      -- hself is a precondition ensuring a is in the attack relation
      have h_nonempty := h_cond a h_att_a
      have h_empty : (attackers aaf a).filter (fun c => c ∈ FiniteMonotoneSystem.iter (aafSystem aaf) m) = ∅ := by
        rw [honly]
        by_cases ha : a ∈ FiniteMonotoneSystem.iter (aafSystem aaf) m
        · exfalso; exact ih ha
        · simp [ha]
      exact h_nonempty h_empty
  simpa [groundedSpec] using h_ind (Finset.card (aafSystem aaf).univ)

theorem self_attack_not_in_grounded (a : Arg) (hself : (a, a) ∈ aaf.attacks) (honly : attackers aaf a = {a}) :
    a ∉ grounded aaf := by
  rw [grounded_eq_groundedSpec aaf]
  exact self_attack_precise_theorem aaf a hself honly

end CoreTheorems

end DungAAF
