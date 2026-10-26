import JurisLean.Candidates.LearningERM20261027
import Mathlib.Data.Finset.Prod

/-!
Original question 05.3: finite, predeclared acceptance rules, with simultaneous
confidence bounds for the actual loss numerator and coverage denominator.
The selector computes exact rational empirical quantities. Its supplied rational
radius must dominate the displayed Hoeffding radius for the probability theorem.
That numerical obligation is explicit; the executable function does not claim to
verify a real sampling design, a population law, or a legal proof standard.

H can index whole predictor/rule pairs. If a predictor or rule is selected using
these calibration labels, it must lie in this predeclared family; counting only
the final selected rule is not justified by the theorem below.
-/

namespace JurisLean.Candidates.SelectiveCalibration20261027

open MeasureTheory ProbabilityTheory
open JurisLean.Candidates.LearningERM20261027
open JurisLean.Candidates.LearningFiniteClass20261027

def coverageLoss {H Z : Type*} (accepts : H → Z → Bool) (h : H) (z : Z) : ℚ :=
  if accepts h z then 1 else 0

def numeratorLoss {H Z : Type*} (loss : H → Z → ℚ)
    (accepts : H → Z → Bool) (h : H) (z : Z) : ℚ :=
  if accepts h z then loss h z else 0

def lowerCoverage {H Z : Type*} {n : ℕ} (accepts : H → Z → Bool)
    (data : Fin n → Z) (radius : ℚ) (h : H) : ℚ :=
  empiricalScore (coverageLoss accepts) data h - radius

def upperNumerator {H Z : Type*} {n : ℕ} (loss : H → Z → ℚ)
    (accepts : H → Z → Bool) (data : Fin n → Z) (radius : ℚ) (h : H) : ℚ :=
  empiricalScore (numeratorLoss loss accepts) data h + radius

def selectPassing {H : Type*} (lower upper : H → ℚ) (target : ℚ) : List H → Option H
  | [] => none
  | h :: rest =>
      if 0 < lower h ∧ upper h / lower h ≤ target then some h
      else selectPassing lower upper target rest

def calibrate {H Z : Type*} {n : ℕ} (loss : H → Z → ℚ)
    (accepts : H → Z → Bool) (models : List H) (data : Fin n → Z)
    (radius target : ℚ) : Option H :=
  if n = 0 ∨ radius < 0 then none
  else selectPassing (lowerCoverage accepts data radius)
    (upperNumerator loss accepts data radius) target models

theorem q05_3_selectPassing_spec {H : Type*} (lower upper : H → ℚ)
    (target : ℚ) (models : List H) (h : H)
    (selected : selectPassing lower upper target models = some h) :
    h ∈ models ∧ 0 < lower h ∧ upper h / lower h ≤ target := by
  induction models with
  | nil => simp [selectPassing] at selected
  | cons first rest ih =>
      by_cases passes : 0 < lower first ∧ upper first / lower first ≤ target
      · simp [selectPassing, passes] at selected
        subst h
        exact ⟨by simp, passes⟩
      · have next : selectPassing lower upper target rest = some h := by
          simpa [selectPassing, passes] using selected
        obtain ⟨member, bound⟩ := ih next
        exact ⟨List.mem_cons_of_mem first member, bound⟩

theorem q05_3_no_result_iff_no_threshold_passes {H : Type*} (lower upper : H → ℚ)
    (target : ℚ) (models : List H) :
    selectPassing lower upper target models = none ↔
      ∀ h ∈ models, ¬ (0 < lower h ∧ upper h / lower h ≤ target) := by
  induction models with
  | nil => simp [selectPassing]
  | cons first rest ih =>
      by_cases passes : 0 < lower first ∧ upper first / lower first ≤ target
      · simp [selectPassing, passes]
      · simp [selectPassing, passes, ih]

theorem q05_3_empty_sample_refused {H Z : Type*} (loss : H → Z → ℚ)
    (accepts : H → Z → Bool) (models : List H) (data : Fin 0 → Z)
    (radius target : ℚ) : calibrate loss accepts models data radius target = none := by
  simp [calibrate]

theorem q05_3_reject_all_has_no_certificate {H Z : Type*} {n : ℕ}
    (loss : H → Z → ℚ) (models : List H) (data : Fin n → Z)
    (radius target : ℚ) (nonnegative : 0 ≤ radius) :
    calibrate loss (fun _ _ => false) models data radius target = none := by
  unfold calibrate
  split
  · rfl
  · apply (q05_3_no_result_iff_no_threshold_passes _ _ _ _).mpr
    intro h _
    simp [lowerCoverage, coverageLoss, empiricalScore, nonnegative]

def jointLoss {H Z : Type*} (loss : H → Z → ℚ)
    (accepts : H → Z → Bool) (pair : H × Bool) (z : Z) : ℚ :=
  if pair.2 then numeratorLoss loss accepts pair.1 z else coverageLoss accepts pair.1 z

theorem q05_3_joint_confidence_event_measurable {Ω Z H : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Z] {n : ℕ}
    (P : Measure Z) (models : Finset H)
    (sample : Fin n → Ω → Z) (sampleMeasurable : ∀ i, Measurable (sample i))
    (loss : H → Z → ℚ) (accepts : H → Z → Bool)
    (numeratorMeasurable : ∀ h ∈ models,
      Measurable (fun z => (numeratorLoss loss accepts h z : ℝ)))
    (coverageMeasurable : ∀ h ∈ models,
      Measurable (fun z => (coverageLoss accepts h z : ℝ))) (radius : ℝ) :
    MeasurableSet {w | ∀ h ∈ models,
      |(empiricalScore (numeratorLoss loss accepts) (fun i => sample i w) h : ℝ) -
        ∫ z, (numeratorLoss loss accepts h z : ℝ) ∂P| ≤ radius ∧
      |(empiricalScore (coverageLoss accepts) (fun i => sample i w) h : ℝ) -
        ∫ z, (coverageLoss accepts h z : ℝ) ∂P| ≤ radius} := by
  have deviations (h : H) (hh : h ∈ models) :
      Measurable (fun w =>
        |(empiricalScore (numeratorLoss loss accepts) (fun i => sample i w) h : ℝ) -
          ∫ z, (numeratorLoss loss accepts h z : ℝ) ∂P|) ∧
      Measurable (fun w =>
        |(empiricalScore (coverageLoss accepts) (fun i => sample i w) h : ℝ) -
          ∫ z, (coverageLoss accepts h z : ℝ) ∂P|) := by
    have hm : ∀ i, Measurable (fun w => (numeratorLoss loss accepts h (sample i w) : ℝ)) :=
      fun i => (numeratorMeasurable h hh).comp (sampleMeasurable i)
    have hc : ∀ i, Measurable (fun w => (coverageLoss accepts h (sample i w) : ℝ)) :=
      fun i => (coverageMeasurable h hh).comp (sampleMeasurable i)
    simp_rw [empiricalScore_cast]
    constructor <;> fun_prop
  have measurable := models.measurableSet_biInter
    (f := fun h => {w |
      |(empiricalScore (numeratorLoss loss accepts) (fun i => sample i w) h : ℝ) -
        ∫ z, (numeratorLoss loss accepts h z : ℝ) ∂P| ≤ radius ∧
      |(empiricalScore (coverageLoss accepts) (fun i => sample i w) h : ℝ) -
        ∫ z, (coverageLoss accepts h z : ℝ) ∂P| ≤ radius})
    (fun h hh => (measurableSet_le (deviations h hh).1 measurable_const).inter
      (measurableSet_le (deviations h hh).2 measurable_const))
  convert measurable using 1 <;> ext w <;> simp

-- There are two bounded statistics for every candidate, hence 2 * |T| in
-- finiteRadius, i.e. sqrt(log(4 * |T| / delta) / (2 * n)).
theorem q05_3_simultaneous_numerator_and_coverage {Ω Z H : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Z] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure Z) [IsProbabilityMeasure P]
    (hn : 0 < n) (models : Finset H) (nonempty : models.Nonempty)
    (sample : Fin n → Ω → Z) (sampleMeasurable : ∀ i, Measurable (sample i))
    (independent : iIndepFun sample μ) (law : ∀ i, IdentDistrib (sample i) id μ P)
    (loss : H → Z → ℚ) (accepts : H → Z → Bool)
    (numeratorMeasurable : ∀ h ∈ models,
      Measurable (fun z => (numeratorLoss loss accepts h z : ℝ)))
    (coverageMeasurable : ∀ h ∈ models,
      Measurable (fun z => (coverageLoss accepts h z : ℝ)))
    (lossRange : ∀ h ∈ models, ∀ z, (loss h z : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ ≤ μ.real {w | ∀ h ∈ models,
      |(empiricalScore (numeratorLoss loss accepts) (fun i => sample i w) h : ℝ) -
        ∫ z, (numeratorLoss loss accepts h z : ℝ) ∂P| ≤
          finiteRadius n (2 * models.card) δ ∧
      |(empiricalScore (coverageLoss accepts) (fun i => sample i w) h : ℝ) -
        ∫ z, (coverageLoss accepts h z : ℝ) ∂P| ≤
          finiteRadius n (2 * models.card) δ} := by
  classical
  let paired := models.product (Finset.univ : Finset Bool)
  have pairedNonempty : paired.Nonempty := by
    obtain ⟨h, hh⟩ := nonempty
    exact ⟨(h, true), by simp [paired, hh]⟩
  have pairedCard : paired.card = 2 * models.card := by
    simp [paired, Finset.card_product, Nat.mul_comm]
  have measurable : ∀ p ∈ paired, Measurable (fun z => (jointLoss loss accepts p z : ℝ)) := by
    intro ⟨h, side⟩ hp
    have hh : h ∈ models := (Finset.mem_product.mp hp).1
    cases side
    · simpa [jointLoss] using coverageMeasurable h hh
    · simpa [jointLoss] using numeratorMeasurable h hh
  have bounded : ∀ p ∈ paired, ∀ z, (jointLoss loss accepts p z : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    intro ⟨h, side⟩ hp z
    have hh : h ∈ models := (Finset.mem_product.mp hp).1
    cases side <;> by_cases ha : accepts h z = true
    · simp [jointLoss, coverageLoss, ha]
    · simp [jointLoss, coverageLoss, ha]
    · simpa [jointLoss, numeratorLoss, ha] using lossRange h hh z
    · simp [jointLoss, numeratorLoss, ha]
  have uniform := u01_1_iid_empirical_risk_uniform μ P hn paired pairedNonempty
    sample sampleMeasurable independent law
    (fun p z => (jointLoss loss accepts p z : ℝ)) measurable bounded δ hδ hδ1
  rw [pairedCard] at uniform
  apply le_trans uniform
  apply measureReal_mono (μ := μ) (h₂ := measure_ne_top μ _)
  intro w hw h hh
  constructor
  · simpa [jointLoss, empiricalScore_cast, empiricalMean] using
      hw (h, true) (by simp [paired, hh])
  · simpa [jointLoss, empiricalScore_cast, empiricalMean] using
      hw (h, false) (by simp [paired, hh])

-- This is the probability guarantee for the threshold actually returned by
-- calibrate, not a population bound supplied as an input to the selector.
theorem q05_3_selected_threshold_has_population_risk_bound {Ω Z H : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Z] [DecidableEq H] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure Z) [IsProbabilityMeasure P]
    (hn : 0 < n) (first : H) (rest : List H)
    (sample : Fin n → Ω → Z) (sampleMeasurable : ∀ i, Measurable (sample i))
    (independent : iIndepFun sample μ) (law : ∀ i, IdentDistrib (sample i) id μ P)
    (loss : H → Z → ℚ) (accepts : H → Z → Bool)
    (numeratorMeasurable : ∀ h ∈ first :: rest,
      Measurable (fun z => (numeratorLoss loss accepts h z : ℝ)))
    (coverageMeasurable : ∀ h ∈ first :: rest,
      Measurable (fun z => (coverageLoss accepts h z : ℝ)))
    (lossRange : ∀ h ∈ first :: rest, ∀ z, (loss h z : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (radius target : ℚ)
    (conservative : finiteRadius n (2 * (first :: rest).toFinset.card) δ ≤ (radius : ℝ)) :
    ∃ confidence : Set Ω, MeasurableSet confidence ∧ 1 - δ ≤ μ.real confidence ∧
      ∀ w ∈ confidence, ∀ h,
        calibrate loss accepts (first :: rest) (fun i => sample i w) radius target = some h →
        0 < ∫ z, (coverageLoss accepts h z : ℝ) ∂P ∧
        (∫ z, (numeratorLoss loss accepts h z : ℝ) ∂P) /
          (∫ z, (coverageLoss accepts h z : ℝ) ∂P) ≤ (target : ℝ) := by
  have uniform := q05_3_simultaneous_numerator_and_coverage μ P hn
    (first :: rest).toFinset ⟨first, by simp⟩ sample sampleMeasurable independent law
    loss accepts (fun h hh => numeratorMeasurable h (List.mem_toFinset.mp hh))
    (fun h hh => coverageMeasurable h (List.mem_toFinset.mp hh))
    (fun h hh => lossRange h (List.mem_toFinset.mp hh)) δ hδ hδ1
  refine ⟨_, q05_3_joint_confidence_event_measurable P (first :: rest).toFinset
    sample sampleMeasurable loss accepts
    (fun h hh => numeratorMeasurable h (List.mem_toFinset.mp hh))
    (fun h hh => coverageMeasurable h (List.mem_toFinset.mp hh)) _, uniform, ?_⟩
  intro w hw h selected
  unfold calibrate at selected
  split at selected
  · cases selected
  · have spec := q05_3_selectPassing_spec _ _ _ _ h selected
    have deviation := hw h (List.mem_toFinset.mpr spec.1)
    have numeratorBound : (∫ z, (numeratorLoss loss accepts h z : ℝ) ∂P) ≤
        (upperNumerator loss accepts (fun i => sample i w) radius h : ℝ) := by
      have lower := (abs_le.mp deviation.1).1
      simp only [upperNumerator, Rat.cast_add]
      linarith
    have coverageBound : (lowerCoverage accepts (fun i => sample i w) radius h : ℝ) ≤
        ∫ z, (coverageLoss accepts h z : ℝ) ∂P := by
      have upper := (abs_le.mp deviation.2).2
      simp only [lowerCoverage, Rat.cast_sub]
      linarith
    have lowerPositive : (0 : ℝ) <
        (lowerCoverage accepts (fun i => sample i w) radius h : ℝ) := by
      exact_mod_cast spec.2.1
    have coveragePositive := lt_of_lt_of_le lowerPositive coverageBound
    have numeratorNonnegative : 0 ≤ ∫ z, (numeratorLoss loss accepts h z : ℝ) ∂P := by
      apply integral_nonneg
      intro z
      by_cases ha : accepts h z = true
      · simpa [numeratorLoss, ha] using (lossRange h spec.1 z).1
      · simp [numeratorLoss, ha]
    have upperNonnegative := le_trans numeratorNonnegative numeratorBound
    have ratio : (∫ z, (numeratorLoss loss accepts h z : ℝ) ∂P) /
        (∫ z, (coverageLoss accepts h z : ℝ) ∂P) ≤
        (upperNumerator loss accepts (fun i => sample i w) radius h : ℝ) /
          (lowerCoverage accepts (fun i => sample i w) radius h : ℝ) := by
      apply (div_le_div_iff₀ coveragePositive lowerPositive).mpr
      nlinarith
    have gate : (upperNumerator loss accepts (fun i => sample i w) radius h : ℝ) /
        (lowerCoverage accepts (fun i => sample i w) radius h : ℝ) ≤ (target : ℝ) := by
      exact_mod_cast spec.2.2
    exact ⟨coveragePositive, le_trans ratio gate⟩

end JurisLean.Candidates.SelectiveCalibration20261027
