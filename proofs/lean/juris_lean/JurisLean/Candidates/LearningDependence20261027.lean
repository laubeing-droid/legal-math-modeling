import JurisLean.Candidates.LearningFiniteClass20261027
import Mathlib.Probability.Distributions.TwoValued
import Mathlib.Probability.Moments.Variance

namespace JurisLean.Candidates.LearningDependence20261027

open MeasureTheory ProbabilityTheory
open JurisLean.Candidates.LearningFiniteClass20261027

noncomputable section

-- This specifies the law, not the variance that is to be proved. No record
-- identifier or grouping policy supplies any of these probability assumptions.
def FairBinary {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) : Prop :=
  Measurable X ∧ (∀ᵐ w ∂μ, X w = 0 ∨ X w = 1) ∧
    μ.real {w | X w = 0} = 1 / 2 ∧ μ.real {w | X w = 1} = 1 / 2

theorem fair_binary_variance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (law : FairBinary μ X) :
    variance X μ = 1 / 4 := by
  rw [variance_of_ae_eq_zero_or_one law.1.aemeasurable law.2.1,
    law.2.2.1, law.2.2.2]
  norm_num

theorem fair_binary_memLp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (law : FairBinary μ X) :
    MemLp X 2 μ := by
  apply MemLp.of_bound law.1.aestronglyMeasurable 1
  filter_upwards [law.2.1] with w hw
  rcases hw with hzero | hone
  · simp [hzero]
  · simp [hone]

-- The random-variable variance is calculated from independence and the laws;
-- it is not an algebraic expression supplied as an assumed second moment.
theorem u01_4_independent_empirical_mean_variance {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ] (hn : 0 < n)
    (X : Fin n → Ω → ℝ) (independent : iIndepFun X μ)
    (law : ∀ i, FairBinary μ (X i)) :
    variance (empiricalMean X) μ = 1 / (4 * (n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have additive : variance (fun w => ∑ i, X i w) μ = ∑ i, variance (X i) μ := by
    have h := IndepFun.variance_sum (s := (Finset.univ : Finset (Fin n)))
      (fun i _ => fair_binary_memLp μ (X i) (law i))
      (fun i _ j _ hij => independent.indepFun hij)
    simpa only [Finset.sum_apply] using h
  change variance (fun w => (∑ i, X i w) / (n : ℝ)) μ = _
  simp_rw [div_eq_mul_inv]
  rw [variance_mul_const, additive]
  simp_rw [fair_binary_variance μ _ (law _)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [ne_of_gt hnR]
  <;> ring

theorem u01_4_copied_empirical_mean_variance {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ] (hn : 0 < n)
    (B : Ω → ℝ) (law : FairBinary μ B) :
    variance (empiricalMean (fun _ : Fin n => B)) μ = 1 / 4 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have meanEqual : empiricalMean (fun _ : Fin n => B) = B := by
    funext w
    simp only [empiricalMean, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp [ne_of_gt hnR]
  rw [meanEqual]
  exact fair_binary_variance μ B law

theorem u01_4_distinct_ids_common_cause_not_independent {Ω : Type*}
    [MeasurableSpace Ω] {n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hn : 1 < n) (B : Ω → ℝ) (law : FairBinary μ B) :
    Function.Injective (fun event : Fin n => event) ∧
      ¬iIndepFun (fun _ : Fin n => B) μ := by
  refine ⟨fun _ _ h => h, ?_⟩
  intro independent
  have hn0 : 0 < n := by omega
  have hi := u01_4_independent_empirical_mean_variance μ hn0
    (fun _ : Fin n => B) independent (fun _ => law)
  have hc := u01_4_copied_empirical_mean_variance (n := n) μ hn0 B law
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have strict : (1 : ℝ) / (4 * (n : ℝ)) < 1 / 4 := by
    apply (div_lt_div_iff₀ (by positivity) (by norm_num)).mpr
    nlinarith
  rw [hc] at hi
  linarith

end
end JurisLean.Candidates.LearningDependence20261027

#print axioms JurisLean.Candidates.LearningDependence20261027.u01_4_independent_empirical_mean_variance
#print axioms JurisLean.Candidates.LearningDependence20261027.u01_4_copied_empirical_mean_variance
#print axioms JurisLean.Candidates.LearningDependence20261027.u01_4_distinct_ids_common_cause_not_independent
