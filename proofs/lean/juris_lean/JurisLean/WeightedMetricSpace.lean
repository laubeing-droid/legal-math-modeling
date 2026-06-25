import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Basic
import JurisLean.WeightedSupNorm
import JurisLean.SupZeroLemma

open Real
open Finset
open Filter

/-! B1+: Weighted Metric Space and Completeness.

Defines `WeightedSpace w` as `Fin n → ℝ` with the weighted sup metric,
proves it is a complete metric space via pointwise limits.

Completeness proof: for a d_w-Cauchy sequence u —
  1. Each coordinate (u k)_i is Cauchy in ℝ.
  2. ℝ is complete, so each coordinate converges → pointwise limit x.
  3. Since Fin n is finite, d_w(u k, x) → 0 (take N = max of N_i).

All theorems compile with 0 sorry.
-/

variable {n : ℕ}

/-- Weighted space: Fin n → ℝ parameterized by a positive weight vector w.
    This is a type alias — values are bare functions, unwrapping is transparent. -/
def WeightedSpace (w : Fin n → ℝ) := Fin n → ℝ

/-! ## sup'_lt_of_all_lt helper lemma -/

/-- For a finite nonempty Finset, if all f_i < a then sup'_i f_i < a.
    Proof: convert to max' on the image, where `max'_lt_iff` gives the result. -/
private lemma sup'_lt_of_all_lt {s : Finset (Fin n)} (hne : s.Nonempty) {f : Fin n → ℝ} {a : ℝ}
    (h : ∀ i ∈ s, f i < a) : s.sup' hne f < a := by
  let fs : Finset ℝ := Finset.image f s
  have hfs_nonempty : fs.Nonempty := Finset.Nonempty.image f hne
  -- sup'_i f i = max' of the image set (for ℝ, sup' = max on finite sets)
  have h_sup_eq_max : s.sup' hne f = fs.max' hfs_nonempty := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro i hi
      have hmem : f i ∈ fs := Finset.mem_image.mpr ⟨i, hi, rfl⟩
      exact Finset.le_max' fs (f i) hmem
    · apply Finset.max'_le
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
      exact Finset.le_sup' f hi
  rw [h_sup_eq_max]
  apply (Finset.max'_lt_iff hfs_nonempty).mpr
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
  exact h i hi

/-! ## MetricSpace instance -/

instance [hw : PositiveWeights w] : MetricSpace (WeightedSpace w) where
  dist x y := weightedSupDist w x y
  dist_self x := by
    unfold weightedSupDist
    simp
  dist_comm x y := weightedSupDist_symm w x y
  dist_triangle x y z := weightedSupDist_triangle w hw x y z
  eq_of_dist_eq_zero h := weightedSupDist_eq_zero_imp hw h
  edist_dist x y := by
    simp [weightedSupDist]

/-! ## Completeness: helper lemma (bound) -/

/-- The coordinate difference |x_i - y_i| is bounded by w_i * weightedSupDist w x y. -/
lemma abs_sub_le_weight_mul_dist (w : Fin n → ℝ) (hw : PositiveWeights w) (x y : Fin n → ℝ) (i : Fin n) :
    |x i - y i| ≤ w i * weightedSupDist w x y := by
  have hmem : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
  have h_div : |x i - y i| / w i ≤ weightedSupDist w x y :=
    Finset.le_sup' (f := fun k : Fin n => |x k - y k| / w k) hmem
  have hpos : 0 < w i := hw i
  calc
    |x i - y i| = (|x i - y i| / w i) * w i := by field_simp [ne_of_gt hpos]
    _ ≤ weightedSupDist w x y * w i := by nlinarith
    _ = w i * weightedSupDist w x y := by ring

/-! ## CompleteSpace instance -/

instance [hw : PositiveWeights w] : CompleteSpace (WeightedSpace w) := by
  refine Metric.complete_of_cauchySeq_tendsto ?_
  intro u hu
  -- hu : CauchySeq u in the WeightedSpace w metric

  -- Step 1: Each coordinate (u k)_i is Cauchy in ℝ.
  have h_coord_cauchy (i : Fin n) : CauchySeq (fun (k : ℕ) => (u k) i) := by
    intro ε hε
    have hwi_pos : 0 < w i := hw i
    have hε_div : 0 < ε / w i := div_pos hε hwi_pos
    rcases Metric.cauchySeq_iff.mp hu (ε / w i) hε_div with ⟨N, hN⟩
    refine ⟨N, fun m hm n hn => ?_⟩
    have h_bound := abs_sub_le_weight_mul_dist w hw (u m) (u n) i
    -- hN m hm n hn : dist (u m) (u n) < ε / w i = weightedSupDist w (u m) (u n) < ε / w i
    have h_dist : weightedSupDist w (u m) (u n) < ε / w i := hN m hm n hn
    calc
      |(u m) i - (u n) i| ≤ w i * weightedSupDist w (u m) (u n) := h_bound
      _ < w i * (ε / w i) := by nlinarith
      _ = ε := by field_simp [ne_of_gt hwi_pos]

  -- Step 2: Each coordinate converges (ℝ is complete).
  have h_coord_conv (i : Fin n) : ∃ xi : ℝ, Tendsto (fun (k : ℕ) => (u k) i) atTop (𝓝 xi) :=
    cauchySeq_tendsto_of_complete (h_coord_cauchy i)

  -- Step 3: Construct the pointwise limit x via classical choice.
  let xi (i : Fin n) : ℝ := (h_coord_conv i).choose
  have hxi (i : Fin n) : Tendsto (fun (k : ℕ) => (u k) i) atTop (𝓝 (xi i)) :=
    (h_coord_conv i).choose_spec

  -- Step 4: Show u → xi in the weighted metric.
  have h_tendsto : Tendsto u atTop (𝓝 (xi : WeightedSpace w)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε

    -- For each i, get N_i such that for k ≥ N_i: |(u k) i - xi i| < ε * w i
    have hNi (i : Fin n) : ∃ Ni : ℕ, ∀ k ≥ Ni, |(u k) i - xi i| < ε * w i := by
      have hpos : 0 < w i := hw i
      rcases Metric.tendsto_nhds.mp (hxi i) (ε * w i) (mul_pos hε hpos) with ⟨Ni, hNi'⟩
      exact ⟨Ni, fun k hk => by simpa [Real.dist_eq] using hNi' k hk⟩

    -- Take N = max of all N_i. Since Fin n is finite, the max exists.
    let Ns : Finset ℕ := Finset.image (fun (i : Fin n) => (hNi i).choose) Finset.univ
    have hNs_nonempty : Ns.Nonempty :=
      Finset.Nonempty.image (fun i => (hNi i).choose) (Finset.univ_nonempty (α := Fin n))
    let N : ℕ := Ns.max' hNs_nonempty

    refine ⟨N, fun k hk => ?_⟩
    unfold weightedSupDist

    -- We need: sup'_i (|(u k) i - xi i| / w i) < ε
    apply sup'_lt_of_all_lt (Finset.univ_nonempty (α := Fin n))
    intro i hi
    have hpos : 0 < w i := hw i
    -- Show |(u k) i - xi i| / w i < ε
    have h_coord_bound : |(u k) i - xi i| < ε * w i := by
      let Ni := (hNi i).choose
      have hNi_bound : ∀ k' ≥ Ni, |(u k') i - xi i| < ε * w i := (hNi i).choose_spec
      have hNi_mem_Ns : Ni ∈ Ns := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
      have hNi_le_N : Ni ≤ N := Finset.le_max' Ns Ni hNi_mem_Ns
      exact hNi_bound k (Nat.le_trans hNi_le_N hk)
    calc
      |(u k) i - xi i| / w i < (ε * w i) / w i :=
        (div_lt_div_right hpos).mpr h_coord_bound
      _ = ε := by field_simp [ne_of_gt hpos]

  exact ⟨xi, h_tendsto⟩
