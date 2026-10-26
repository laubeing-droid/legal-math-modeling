import JurisLean.Candidates.LearningRisk20261027
import Mathlib.Probability.IdentDistrib
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FunProp

namespace JurisLean.Candidates.LearningFiniteClass20261027

open MeasureTheory ProbabilityTheory Real
open JurisLean.Candidates.Final20261021.Learning
open JurisLean.Candidates.LearningRisk20261027

noncomputable section

def empiricalMean {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ) (w : Ω) : ℝ :=
  (∑ i, X i w) / (n : ℝ)

def finiteRadius (n M : ℕ) (δ : ℝ) : ℝ :=
  Real.sqrt (Real.log (2 * (M : ℝ) / δ) / (2 * (n : ℝ)))

-- This specializes the already-proved independent bounded SUM theorem to the
-- actual sample mean. The mean assumption is supplied from IdentDistrib below.
theorem row_mean_two_tail {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hn : 0 < n)
    (X : Fin n → Ω → ℝ) (independent : iIndepFun X μ)
    (measurable : ∀ i, AEMeasurable (X i) μ)
    (bounded : ∀ i, ∀ᵐ w ∂μ, X i w ∈ Set.Icc (0 : ℝ) 1)
    (mean : ℝ) (means : ∀ i, ∫ w, X i w ∂μ = mean)
    (ε : ℝ) (hε : 0 < ε) :
    μ.real {w | ε ≤ |empiricalMean X w - mean|} ≤
      2 * Real.exp (-2 * (n : ℝ) * ε ^ 2) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hD : 0 < ∑ i ∈ (Finset.univ : Finset (Fin n)), ((1 : ℝ) - 0) ^ 2 := by
    simpa using hnR
  have bound := u01_0_independent_bounded_two_tail μ X (fun _ => 0) (fun _ => 1)
    Finset.univ independent (fun i _ => measurable i) (fun i _ => bounded i)
    hD ((n : ℝ) * ε) (mul_pos hnR hε)
  have centered (w : Ω) : (∑ i : Fin n, (X i w - ∫ z, X i z ∂μ)) =
      (n : ℝ) * (empiricalMean X w - mean) := by
    simp_rw [means]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    unfold empiricalMean
    field_simp [ne_of_gt hnR]
    <;> ring
  have events : {w | (n : ℝ) * ε ≤ |∑ i : Fin n, (X i w - ∫ z, X i z ∂μ)|} =
      {w | ε ≤ |empiricalMean X w - mean|} := by
    ext w
    change (n : ℝ) * ε ≤ |∑ i : Fin n, (X i w - ∫ z, X i z ∂μ)| ↔
      ε ≤ |empiricalMean X w - mean|
    rw [centered w, abs_mul, abs_of_pos hnR]
    constructor <;> intro hw <;> nlinarith
  have exponent : -2 * ((n : ℝ) * ε) ^ 2 / (n : ℝ) = -2 * (n : ℝ) * ε ^ 2 := by
    field_simp [ne_of_gt hnR]
    <;> ring
  have simplified : μ.real {w | (n : ℝ) * ε ≤ |∑ i : Fin n, (X i w - ∫ z, X i z ∂μ)|} ≤
      2 * Real.exp (-2 * ((n : ℝ) * ε) ^ 2 / (n : ℝ)) := by
    simpa using bound
  rwa [events, exponent] at simplified

theorem finite_class_mean_tail {Ω H : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hn : 0 < n) (models : Finset H)
    (X : H → Fin n → Ω → ℝ) (mean : H → ℝ)
    (independent : ∀ h ∈ models, iIndepFun (X h) μ)
    (measurable : ∀ h ∈ models, ∀ i, AEMeasurable (X h i) μ)
    (bounded : ∀ h ∈ models, ∀ i, ∀ᵐ w ∂μ, X h i w ∈ Set.Icc (0 : ℝ) 1)
    (means : ∀ h ∈ models, ∀ i, ∫ w, X h i w ∂μ = mean h)
    (ε : ℝ) (hε : 0 < ε) :
    μ.real (⋃ h ∈ models, {w | ε ≤ |empiricalMean (X h) w - mean h|}) ≤
      2 * (models.card : ℝ) * Real.exp (-2 * (n : ℝ) * ε ^ 2) := by
  calc
    _ ≤ ∑ h ∈ models, μ.real {w | ε ≤ |empiricalMean (X h) w - mean h|} :=
      measureReal_biUnion_finset_le models _
    _ ≤ ∑ _h ∈ models, 2 * Real.exp (-2 * (n : ℝ) * ε ^ 2) :=
      Finset.sum_le_sum fun h hh => row_mean_two_tail μ hn (X h) (independent h hh)
        (measurable h hh) (bounded h hh) (mean h) (means h hh) ε hε
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

-- The class is fixed before evaluation: one event covers EVERY member,
-- including a member later chosen using these same data.
theorem finite_class_mean_uniform {Ω H : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hn : 0 < n)
    (models : Finset H) (nonempty : models.Nonempty)
    (X : H → Fin n → Ω → ℝ) (mean : H → ℝ)
    (independent : ∀ h ∈ models, iIndepFun (X h) μ)
    (measurable : ∀ h ∈ models, ∀ i, Measurable (X h i))
    (bounded : ∀ h ∈ models, ∀ i, ∀ᵐ w ∂μ, X h i w ∈ Set.Icc (0 : ℝ) 1)
    (means : ∀ h ∈ models, ∀ i, ∫ w, X h i w ∂μ = mean h)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ ≤ μ.real {w | ∀ h ∈ models,
      |empiricalMean (X h) w - mean h| ≤ finiteRadius n models.card δ} := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hm : (1 : ℝ) ≤ models.card := by
    exact_mod_cast (Nat.succ_le_of_lt (Finset.card_pos.mpr nonempty))
  have hmpos : (0 : ℝ) < models.card := by linarith
  have ratio : 1 < 2 * (models.card : ℝ) / δ := by
    apply (lt_div_iff₀ hδ).mpr
    nlinarith
  have logpos := Real.log_pos ratio
  have radpos : 0 < finiteRadius n models.card δ :=
    Real.sqrt_pos.mpr (div_pos logpos (by positivity))
  have radsq : (finiteRadius n models.card δ) ^ 2 =
      Real.log (2 * (models.card : ℝ) / δ) / (2 * (n : ℝ)) :=
    Real.sq_sqrt (le_of_lt (div_pos logpos (by positivity)))
  have exponent : -2 * (n : ℝ) * (finiteRadius n models.card δ) ^ 2 =
      -Real.log (2 * (models.card : ℝ) / δ) := by
    rw [radsq]
    field_simp [ne_of_gt hnR]
    <;> ring
  have bound := finite_class_mean_tail μ hn models X mean independent
    (fun h hh i => (measurable h hh i).aemeasurable) bounded means
    (finiteRadius n models.card δ) radpos
  rw [exponent, Real.exp_neg, Real.exp_log (lt_trans (by norm_num) ratio)] at bound
  have coefficient : 2 * (models.card : ℝ) * (2 * (models.card : ℝ) / δ)⁻¹ = δ := by
    field_simp [ne_of_gt hmpos]
  rw [coefficient] at bound
  have deviation (h : H) (hh : h ∈ models) :
      Measurable (fun w => |empiricalMean (X h) w - mean h|) := by
    have each : ∀ i, Measurable (X h i) := measurable h hh
    unfold empiricalMean
    fun_prop
  have goodMeasurable : MeasurableSet {w | ∀ h ∈ models,
      |empiricalMean (X h) w - mean h| ≤ finiteRadius n models.card δ} := by
    have h := models.measurableSet_biInter
      (f := fun h => {w | |empiricalMean (X h) w - mean h| ≤ finiteRadius n models.card δ})
      (fun h hh =>
      measurableSet_le (deviation h hh) measurable_const)
    convert h using 1 <;> ext w <;> simp
  have failure : {w | ∀ h ∈ models,
      |empiricalMean (X h) w - mean h| ≤ finiteRadius n models.card δ}ᶜ ⊆
      ⋃ h ∈ models, {w | finiteRadius n models.card δ ≤
        |empiricalMean (X h) w - mean h|} := by
    intro w hw
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hw
    push_neg at hw
    obtain ⟨h, hh, bad⟩ := hw
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨h, hh, le_of_lt bad⟩
  have failed := le_trans (measureReal_mono (μ := μ) failure (measure_ne_top μ _)) bound
  rw [measureReal_compl goodMeasurable] at failed
  simpa using (show 1 - δ ≤ μ.real {w | ∀ h ∈ models,
    |empiricalMean (X h) w - mean h| ≤ finiteRadius n models.card δ} by
      have total : μ.real Set.univ = 1 := by simp
      rw [total] at failed
      linarith)

-- Z may be the whole visible-input/label pair. The explicit population law
-- and sample laws supply the means; no target risk is assumed as a tail bound.
theorem u01_1_iid_empirical_risk_uniform {Ω Z H : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Z] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure Z) [IsProbabilityMeasure P]
    (hn : 0 < n) (models : Finset H) (nonempty : models.Nonempty)
    (sample : Fin n → Ω → Z) (sampleMeasurable : ∀ i, Measurable (sample i))
    (independent : iIndepFun sample μ) (law : ∀ i, IdentDistrib (sample i) id μ P)
    (loss : H → Z → ℝ) (lossMeasurable : ∀ h ∈ models, Measurable (loss h))
    (lossRange : ∀ h ∈ models, ∀ z, loss h z ∈ Set.Icc (0 : ℝ) 1)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ ≤ μ.real {w | ∀ h ∈ models,
      |empiricalMean (fun i w => loss h (sample i w)) w - ∫ z, loss h z ∂P| ≤
        finiteRadius n models.card δ} := by
  apply finite_class_mean_uniform μ hn models nonempty
    (fun h i w => loss h (sample i w)) (fun h => ∫ z, loss h z ∂P)
  · intro h hh
    exact independent.comp (fun _ => loss h) (fun _ => lossMeasurable h hh)
  · intro h hh i
    exact (lossMeasurable h hh).comp (sampleMeasurable i)
  · intro h hh i
    exact Filter.Eventually.of_forall (fun w => lossRange h hh (sample i w))
  · intro h hh i
    simpa [Function.comp_def] using ((law i).comp (lossMeasurable h hh)).integral_eq
  · exact hδ
  · exact hδ1

-- This consumes the sample-mean event above for an actual data-dependent
-- selected member. The optimization premise concerns the computed empirical
-- risks; neither the population oracle inequality nor its event is assumed.
theorem u01_1_iid_approximate_erm {Ω Z H : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Z] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure Z) [IsProbabilityMeasure P]
    (hn : 0 < n) (models : Finset H) (nonempty : models.Nonempty)
    (sample : Fin n → Ω → Z) (sampleMeasurable : ∀ i, Measurable (sample i))
    (independent : iIndepFun sample μ) (law : ∀ i, IdentDistrib (sample i) id μ P)
    (loss : H → Z → ℝ) (lossMeasurable : ∀ h ∈ models, Measurable (loss h))
    (lossRange : ∀ h ∈ models, ∀ z, loss h z ∈ Set.Icc (0 : ℝ) 1)
    (chosen : Ω → H) (member : ∀ w, chosen w ∈ models)
    (chosenRiskMeasurable : Measurable (fun w => ∫ z, loss (chosen w) z ∂P))
    (opt : ℝ) (optimization : ∀ w h, h ∈ models →
      empiricalMean (fun i w' => loss (chosen w) (sample i w')) w ≤
        empiricalMean (fun i w' => loss h (sample i w')) w + opt)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    MeasurableSet {w | (∫ z, loss (chosen w) z ∂P) ≤
      riskInf (fun h => ∫ z, loss h z ∂P) (models : Set H) +
        2 * finiteRadius n models.card δ + opt} ∧
    1 - δ ≤ μ.real {w | (∫ z, loss (chosen w) z ∂P) ≤
      riskInf (fun h => ∫ z, loss h z ∂P) (models : Set H) +
        2 * finiteRadius n models.card δ + opt} := by
  refine ⟨measurableSet_le chosenRiskMeasurable measurable_const, ?_⟩
  have uniform := u01_1_iid_empirical_risk_uniform μ P hn models nonempty
    sample sampleMeasurable independent law loss lossMeasurable lossRange δ hδ hδ1
  apply le_trans uniform
  apply measureReal_mono (μ := μ) (h₂ := measure_ne_top μ _)
  intro w hw
  exact u01_1_uniform_event_erm_oracle (fun h => ∫ z, loss h z ∂P)
    (fun h => empiricalMean (fun i w' => loss h (sample i w')) w)
    (models : Set H) (chosen w) (member w) (finiteRadius n models.card δ) opt
    (fun h hh => by simpa [abs_sub_comm] using hw h hh) (optimization w)

end
end JurisLean.Candidates.LearningFiniteClass20261027

#print axioms JurisLean.Candidates.LearningFiniteClass20261027.row_mean_two_tail
#print axioms JurisLean.Candidates.LearningFiniteClass20261027.finite_class_mean_uniform
#print axioms JurisLean.Candidates.LearningFiniteClass20261027.u01_1_iid_empirical_risk_uniform
#print axioms JurisLean.Candidates.LearningFiniteClass20261027.u01_1_iid_approximate_erm
