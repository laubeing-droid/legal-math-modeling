/- Frozen U04.4: connect actual mean variance to the finite and zero-variance branches. -/
import JurisLean.Candidates.LearningFiniteClass20261027
import JurisLean.Candidates.LearningDependence20261027
import JurisLean.Candidates.Final20261021.Probability
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace JurisLean.Candidates.EquicorrelatedMean20261030

open LearningFiniteClass20261027
open LearningDependence20261027

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {n : ℕ} {X : Fin n → Ω → ℝ} {v r : ℝ}

/-- The actual mean variance formula and its necessary nonnegative bracket. -/
theorem equicorrelated_mean_variance
    (hn : 2 ≤ n) (hv : 0 < v)
    (hXm : ∀ i, AEMeasurable (X i) μ)
    (hvar : ∀ i, variance (X i) μ = v)
    (hcov : ∀ i j, i ≠ j → covariance (X i) (X j) μ = v * r) :
    variance (empiricalMean X) μ =
        v * (1 + ((n : ℝ) - 1) * r) / (n : ℝ) ∧
      0 ≤ 1 + ((n : ℝ) - 1) * r := by
  classical
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hLp : ∀ i, MemLp (X i) 2 μ := by
    intro i
    apply memLp_two_of_variance_ne_zero
      (μ := μ) (X := X i) (hXm i).aestronglyMeasurable
    rw [hvar i]
    exact ne_of_gt hv
  have hc (i j : Fin n) :
      covariance (X i) (X j) μ = if j = i then v else v * r := by
    by_cases hij : j = i
    · subst j
      simp only [if_pos rfl]
      exact (covariance_self (μ := μ) (X := X i) (hXm i)).trans (hvar i)
    · simp only [if_neg hij]
      exact hcov i j (fun h => hij h.symm)
  have hrow (i : Fin n) :
      (∑ j, covariance (X i) (X j) μ) =
        v + ((n : ℝ) - 1) * (v * r) := by
    calc
      (∑ j, covariance (X i) (X j) μ) =
          ∑ j : Fin n, (v * r + if j = i then v - v * r else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hc i j]
        by_cases hij : j = i <;> simp [hij] <;> ring
      _ = (n : ℝ) * (v * r) + (v - v * r) := by
        simp [Finset.sum_add_distrib, nsmul_eq_mul]
      _ = v + ((n : ℝ) - 1) * (v * r) := by ring
  have hsum :
      (∑ i, ∑ j, covariance (X i) (X j) μ) =
        (n : ℝ) * v * (1 + ((n : ℝ) - 1) * r) := by
    calc
      (∑ i, ∑ j, covariance (X i) (X j) μ) =
          ∑ _i : Fin n, (v + ((n : ℝ) - 1) * (v * r)) := by
        exact Finset.sum_congr rfl (fun i _ => hrow i)
      _ = (n : ℝ) * v * (1 + ((n : ℝ) - 1) * r) := by
        simp [nsmul_eq_mul]
        <;> ring
  have hf :
      variance (empiricalMean X) μ =
        v * (1 + ((n : ℝ) - 1) * r) / (n : ℝ) := by
    calc
      variance (empiricalMean X) μ =
          variance (fun ω => ∑ i, X i ω) μ * ((n : ℝ)⁻¹) ^ 2 := by
        simpa only [empiricalMean, div_eq_mul_inv] using
          variance_mul_const ((n : ℝ)⁻¹) (fun ω => ∑ i, X i ω) μ
      _ = v * (1 + ((n : ℝ) - 1) * r) / (n : ℝ) := by
        rw [variance_fun_sum (μ := μ) (X := X) hLp, hsum]
        field_simp [hn0]
        <;> ring
  refine ⟨hf, ?_⟩
  by_contra h
  have hb : 1 + ((n : ℝ) - 1) * r < 0 := lt_of_not_ge h
  have hneg :
      v * (1 + ((n : ℝ) - 1) * r) / (n : ℝ) < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hv hb) hnpos
  have hnonneg := variance_nonneg (empiricalMean X) μ
  rw [hf] at hnonneg
  linarith

/-- The finite count is used only in the positive branch; the zero branch
connects actual zero variance to the existing rational classifier's tag. -/
theorem equicorrelated_mean_branches
    (hn : 2 ≤ n) (hv : 0 < v)
    (hXm : ∀ i, AEMeasurable (X i) μ)
    (hvar : ∀ i, variance (X i) μ = v)
    (hcov : ∀ i j, i ≠ j → covariance (X i) (X j) μ = v * r) :
    (0 < 1 + ((n : ℝ) - 1) * r →
      0 < (n : ℝ) / (1 + ((n : ℝ) - 1) * r) ∧
      variance (empiricalMean X) μ =
        v / ((n : ℝ) / (1 + ((n : ℝ) - 1) * r))) ∧
    (1 + ((n : ℝ) - 1) * r = 0 →
      variance (empiricalMean X) μ = 0 ∧
      r = (((-1 : ℚ) / ((n : ℚ) - 1) : ℚ) : ℝ) ∧
      Final20261021.Probability.u04_4_variance_equivalent
        n ((-1 : ℚ) / ((n : ℚ) - 1)) =
        Final20261021.Probability.EffectiveCount.degenerateZeroVariance) := by
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hf := (equicorrelated_mean_variance hn hv hXm hvar hcov).1
  constructor
  · intro hb
    have hb0 : 1 + ((n : ℝ) - 1) * r ≠ 0 := ne_of_gt hb
    refine ⟨div_pos hnpos hb, ?_⟩
    rw [hf]
    field_simp [hn0, hb0]
    <;> ring
  · intro hb
    have hn1 : 1 < n := by omega
    have hnR : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hnQ : (1 : ℚ) < (n : ℚ) := by exact_mod_cast hn1
    have hdR : (n : ℝ) - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hnR)
    have hdQ : (n : ℚ) - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hnQ)
    have hr : r = (((-1 : ℚ) / ((n : ℚ) - 1) : ℚ) : ℝ) := by
      push_cast
      apply (eq_div_iff hdR).2
      nlinarith [hb]
    have hzQ :
        1 + ((n : ℚ) - 1) * ((-1 : ℚ) / ((n : ℚ) - 1)) = 0 := by
      field_simp [hdQ]
      <;> ring
    refine ⟨?_, hr, ?_⟩
    · rw [hf, hb]
      simp
    · unfold Final20261021.Probability.u04_4_variance_equivalent
      rw [if_neg (by omega : ¬ n < 2)]
      dsimp
      rw [if_pos hzQ]

/-- The actual fair-coin complement pair has constant mean and zero variance. -/
theorem fair_coin_complement_witness :
    variance (id : ℝ → ℝ) fairCoinMeasure = (1 : ℝ) / 4 ∧
    variance (fun ω : ℝ => 1 - ω) fairCoinMeasure = (1 : ℝ) / 4 ∧
    covariance (id : ℝ → ℝ) (fun ω : ℝ => 1 - ω) fairCoinMeasure =
      -(1 : ℝ) / 4 ∧
    (∀ ω : ℝ,
      empiricalMean (fun (i : Fin 2) (w : ℝ) =>
        if i = 0 then w else 1 - w) ω = (1 : ℝ) / 2) ∧
    variance (empiricalMean (fun (i : Fin 2) (w : ℝ) =>
      if i = 0 then w else 1 - w)) fairCoinMeasure = 0 := by
  have hB : MemLp (id : ℝ → ℝ) 2 fairCoinMeasure :=
    fair_binary_memLp fairCoinMeasure id fair_coin_law
  have hV : variance (id : ℝ → ℝ) fairCoinMeasure = (1 : ℝ) / 4 :=
    fair_binary_variance fairCoinMeasure id fair_coin_law
  have hVc : variance (fun ω : ℝ => 1 - ω) fairCoinMeasure = (1 : ℝ) / 4 := by
    simpa only [id_eq] using
      (variance_const_sub (μ := fairCoinMeasure) (X := id)
        hB.aestronglyMeasurable 1).trans hV
  have hC :
      covariance (id : ℝ → ℝ) (fun ω : ℝ => 1 - ω) fairCoinMeasure =
        -(1 : ℝ) / 4 := by
    calc
      covariance (id : ℝ → ℝ) (fun ω : ℝ => 1 - ω) fairCoinMeasure =
          - covariance (id : ℝ → ℝ) id fairCoinMeasure := by
        simpa only [id_eq] using
          (covariance_const_sub_right (μ := fairCoinMeasure) (X := id) (Y := id)
            (hB.integrable (by norm_num)) 1)
      _ = -(1 : ℝ) / 4 := by
        rw [covariance_self (μ := fairCoinMeasure) (X := id) hB.aemeasurable, hV]
        ring
  have hmean :
      empiricalMean (fun (i : Fin 2) (w : ℝ) =>
        if i = 0 then w else 1 - w) = fun _ => (1 : ℝ) / 2 := by
    funext ω
    norm_num [empiricalMean, Fin.sum_univ_two] <;> ring
  refine ⟨hV, hVc, hC, ?_, ?_⟩
  · intro ω
    exact congrFun hmean ω
  · rw [hmean]
    simp [variance, evariance]

end

end JurisLean.Candidates.EquicorrelatedMean20261030
