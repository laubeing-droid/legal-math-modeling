import JurisLean.Candidates.Final20261021.Interfaces
import Mathlib.Probability.Moments.SubGaussian

namespace JurisLean.Candidates.Final20261021.Learning
open MeasureTheory ProbabilityTheory Real
open scoped NNReal

-- Signatures checked in pinned Mathlib c5ea0035, SubGaussian.lean 780/860.
theorem u01_0_bounded_mgf {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (a b : ℝ)
    (measurable : AEMeasurable X μ) (bounded : ∀ᵐ w ∂μ, X w ∈ Set.Icc a b) :
    HasSubgaussianMGF (fun w => X w - ∫ z, X z ∂μ) ((‖b-a‖₊/2)^2) μ :=
  hasSubgaussianMGF_of_mem_Icc measurable bounded

theorem u01_0_independent_bounded_upper_tail {Ω I : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : I → Ω → ℝ)
    (a b : I → ℝ) (s : Finset I) (independent : iIndepFun X μ)
    (measurable : ∀ i ∈ s, AEMeasurable (X i) μ)
    (bounded : ∀ i ∈ s, ∀ᵐ w ∂μ, X i w ∈ Set.Icc (a i) (b i))
    (ε : ℝ) (nonneg : 0 ≤ ε) :
    μ.real {w | ε ≤ ∑ i ∈ s, (X i w - ∫ z, X i z ∂μ)} ≤
      exp (-ε^2 / (2 * ∑ i ∈ s, (((‖b i-a i‖₊/2)^2 : ℝ≥0) : ℝ))) := by
  have hi : iIndepFun (fun i w => X i w - ∫ z, X i z ∂μ) μ :=
    independent.comp (fun i x => x - ∫ z, X i z ∂μ)
      (fun _ => measurable_id.sub measurable_const)
  simpa only [NNReal.coe_sum] using
    HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hi
      (fun i hi => u01_0_bounded_mgf μ (X i) (a i) (b i) (measurable i hi) (bounded i hi)) nonneg

theorem subgaussian_two_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (c : ℝ≥0)
    (h : HasSubgaussianMGF X c μ) (ε : ℝ) (hε : 0 ≤ ε) :
    μ.real {w | ε ≤ |X w|} ≤ 2 * exp (-ε^2 / (2 * (c : ℝ))) := by
  have inclusion : {w | ε ≤ |X w|} ⊆ {w | ε ≤ X w} ∪ {w | ε ≤ -X w} := by
    intro w hw
    simp only [Set.mem_union, Set.mem_setOf_eq]
    rcases le_total 0 (X w) with hp | hn
    · left; simpa [abs_of_nonneg hp] using hw
    · right; simpa [abs_of_nonpos hn] using hw
  have upper := h.measure_ge_le hε
  have lower : μ.real {w | ε ≤ -X w} ≤ exp (-ε^2 / (2 * (c : ℝ))) :=
    h.neg.measure_ge_le hε
  calc
    μ.real {w | ε ≤ |X w|} ≤ μ.real ({w | ε ≤ X w} ∪ {w | ε ≤ -X w}) :=
      measureReal_mono inclusion
    _ ≤ μ.real {w | ε ≤ X w} + μ.real {w | ε ≤ -X w} := measureReal_union_le _ _
    _ ≤ 2 * exp (-ε^2 / (2 * (c : ℝ))) := by linarith

theorem independent_bounded_sum_mgf {Ω I : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : I → Ω → ℝ)
    (a b : I → ℝ) (s : Finset I) (independent : iIndepFun X μ)
    (measurable : ∀ i ∈ s, AEMeasurable (X i) μ)
    (bounded : ∀ i ∈ s, ∀ᵐ w ∂μ, X i w ∈ Set.Icc (a i) (b i)) :
    HasSubgaussianMGF (fun w => ∑ i ∈ s, (X i w - ∫ z, X i z ∂μ))
      (∑ i ∈ s, (‖b i-a i‖₊/2)^2) μ := by
  have hi : iIndepFun (fun i w => X i w - ∫ z, X i z ∂μ) μ :=
    independent.comp (fun i x => x - ∫ z, X i z ∂μ)
      (fun _ => measurable_id.sub measurable_const)
  exact HasSubgaussianMGF.sum_of_iIndepFun hi
    (fun i hi => u01_0_bounded_mgf μ (X i) (a i) (b i) (measurable i hi) (bounded i hi))

theorem bounded_proxy_exact {I : Type*} (a b : I → ℝ) (s : Finset I) :
    ((∑ i ∈ s, (‖b i-a i‖₊/2)^2 : ℝ≥0) : ℝ) =
      (∑ i ∈ s, (b i-a i)^2) / 4 := by
  have point (x : ℝ) : (((‖x‖₊/2)^2 : ℝ≥0) : ℝ) = x^2/4 := by
    norm_num [div_pow, Real.norm_eq_abs, sq_abs]
  simp only [NNReal.coe_sum]
  simp_rw [point]
  rw [Finset.sum_div]

-- Both branches use the manuscript's strictly positive deviation threshold.
-- In the zero-width branch, division by zero is not interpreted as a tail bound.
theorem u01_0_independent_bounded_two_tail {Ω I : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : I → Ω → ℝ)
    (a b : I → ℝ) (s : Finset I) (independent : iIndepFun X μ)
    (measurable : ∀ i ∈ s, AEMeasurable (X i) μ)
    (bounded : ∀ i ∈ s, ∀ᵐ w ∂μ, X i w ∈ Set.Icc (a i) (b i))
    (positiveWidth : 0 < ∑ i ∈ s, (b i-a i)^2) (t : ℝ) (ht : 0 < t) :
    μ.real {w | t ≤ |∑ i ∈ s, (X i w - ∫ z, X i z ∂μ)|} ≤
      2 * exp (-2*t^2 / (∑ i ∈ s, (b i-a i)^2)) := by
  have bound := subgaussian_two_tail μ _ _
    (independent_bounded_sum_mgf μ X a b s independent measurable bounded) t (le_of_lt ht)
  rw [bounded_proxy_exact] at bound
  have exponent : -t^2 / (2*((∑ i ∈ s, (b i-a i)^2)/4)) =
      -2*t^2 / (∑ i ∈ s, (b i-a i)^2) := by
    field_simp [ne_of_gt positiveWidth] <;> ring
  rwa [exponent] at bound

theorem u01_0_zero_width_tail {Ω I : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : I → Ω → ℝ)
    (a b : I → ℝ) (s : Finset I) (independent : iIndepFun X μ)
    (measurable : ∀ i ∈ s, AEMeasurable (X i) μ)
    (bounded : ∀ i ∈ s, ∀ᵐ w ∂μ, X i w ∈ Set.Icc (a i) (b i))
    (zeroWidth : (∑ i ∈ s, (b i-a i)^2) = 0) (t : ℝ) (ht : 0 < t) :
    μ.real {w | t ≤ |∑ i ∈ s, (X i w - ∫ z, X i z ∂μ)|} = 0 := by
  have subG := independent_bounded_sum_mgf μ X a b s independent measurable bounded
  have proxyZero : (∑ i ∈ s, (‖b i-a i‖₊/2)^2 : ℝ≥0) = 0 := by
    exact_mod_cast (show ((∑ i ∈ s, (‖b i-a i‖₊/2)^2 : ℝ≥0) : ℝ) = 0 by
      rw [bounded_proxy_exact, zeroWidth, zero_div])
  rw [proxyZero] at subG
  have zero := subG.ae_eq_zero_of_hasSubgaussianMGF_zero
  have same : {w | t ≤ |∑ i ∈ s, (X i w - ∫ z, X i z ∂μ)|} =ᵐ[μ] (∅ : Set Ω) := by
    filter_upwards [zero] with w hw
    simp only [Pi.zero_apply] at hw
    apply propext
    change (t ≤ |∑ i ∈ s, (X i w - ∫ z, X i z ∂μ)|) ↔ False
    rw [hw, abs_zero]
    exact iff_false_intro (not_le.mpr ht)
  simpa using measureReal_congr same

theorem u01_1_fixed_class_tail {Ω H : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (models : Finset H)
    (centered : H → Ω → ℝ) (c : H → ℝ≥0)
    (mgf : ∀ h ∈ models, HasSubgaussianMGF (centered h) (c h) μ)
    (ε : ℝ) (hε : 0 ≤ ε) :
    μ.real (⋃ h ∈ models, {w | ε ≤ |centered h w|}) ≤
      ∑ h ∈ models, 2 * exp (-ε^2 / (2 * (c h : ℝ))) := by
  exact le_trans (measureReal_biUnion_finset_le models _)
    (Finset.sum_le_sum fun h hh => subgaussian_two_tail μ _ _ (mgf h hh) ε hε)

theorem u01_1_approximate_erm (chosen best empiricalChosen empiricalBest ε opt : ℝ)
    (chosenUpper : chosen ≤ empiricalChosen + ε)
    (bestLower : empiricalBest ≤ best + ε)
    (optimization : empiricalChosen ≤ empiricalBest + opt) :
    chosen ≤ best + 2 * ε + opt := by linarith

def zeroOne {A : Type} [DecidableEq A] (x y : A) : ℚ := if x = y then 0 else 1

theorem u01_2_label_bridge_pointwise {A : Type} [DecidableEq A] (h y truth : A) :
    zeroOne h truth ≤ zeroOne h y + zeroOne y truth := by
  by_cases h1 : h = y <;> by_cases h2 : y = truth <;> by_cases h3 : h = truth <;>
    simp_all [zeroOne]

structure FitContract where
  task : Nat
  target : Nat
  featureVersion : Nat
  modelVersion : Nat
  evidenceVersion : Nat
  windowEnd : Instant
  independentUnit : MeasurementId
  deriving DecidableEq, Repr

def proposed_fit_contract (expected supplied : FitContract) : Result FitContract :=
  if supplied = expected then .known supplied else .unknown .targetMismatch

-- This groups only resolved identities. It supplies no iid certificate.
theorem grouped_unit_not_split {Unit Split : Type} (split : Unit → Split) (u : Unit) :
    ∀ a b, split u = a → split u = b → a = b := by
  intro a b ha hb
  exact ha.symm.trans hb

/-! U01.4 finite counterexamples.
The constant rule fits the training label and misses both the target label and
the deployment label. Independent Bernoulli(1/2) means have variance `1/(4n)`.
Copied coordinates keep variance `1/4`. Copying is not repaired by dropping the
duplicate name: the second moment stays the common-cause moment. -/

def u01_4_rule (_ : Fin 3) : Fin 2 := 0

theorem u01_4_pointwise_train_target_deployment :
    zeroOne (u01_4_rule 0) (0 : Fin 2) = 0 ∧
    zeroOne (u01_4_rule 1) (1 : Fin 2) = 1 ∧
    zeroOne (u01_4_rule 2) (1 : Fin 2) = 1 := by
  decide

theorem u01_4_independent_mean_variance (n : ℕ) (hn : 0 < n) :
    (((n : ℚ) * (1 / 2) + (n : ℚ) * ((n : ℚ) - 1) * (1 / 4) -
        ((n : ℚ) * (1 / 2)) ^ 2) / ((n : ℚ) ^ 2)) = 1 / (4 * (n : ℚ)) := by
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp [hn0] <;> ring

theorem u01_4_copied_mean_variance (n : ℕ) (hn : 0 < n) :
    ((((n : ℚ) ^ 2) * (1 / 2) - ((n : ℚ) * (1 / 2)) ^ 2) / ((n : ℚ) ^ 2)) =
      (1 / 4 : ℚ) := by
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp [hn0] <;> ring

theorem u01_4_copy_is_not_independent (n : ℕ) (hn : 1 < n) :
    1 / (4 * (n : ℚ)) < (1 / 4 : ℚ) := by
  have hn1 : (1 : ℚ) < n := by exact_mod_cast hn
  have hden : (0 : ℚ) < 4 * n := by nlinarith
  rw [div_lt_div_iff₀ hden (by norm_num : (0 : ℚ) < 4)]
  nlinarith

end JurisLean.Candidates.Final20261021.Learning
