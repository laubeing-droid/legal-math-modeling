import JurisLean.Candidates.Final20261021.Trace
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
  have lower := h.neg.measure_ge_le hε
  calc
    μ.real {w | ε ≤ |X w|} ≤ μ.real ({w | ε ≤ X w} ∪ {w | ε ≤ -X w}) :=
      measureReal_mono inclusion
    _ ≤ μ.real {w | ε ≤ X w} + μ.real {w | ε ≤ -X w} := measureReal_union_le _ _
    _ ≤ 2 * exp (-ε^2 / (2 * (c : ℝ))) := by linarith

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

end JurisLean.Candidates.Final20261021.Learning
