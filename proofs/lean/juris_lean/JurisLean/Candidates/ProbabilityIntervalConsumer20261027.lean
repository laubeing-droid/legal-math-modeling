import JurisLean.Candidates.SampleCalibrationConsumer20261027
import JurisLean.Candidates.Final20261021.Probability

/-!
Original 05.2 and edge 01 -> 04/05: the actually fitted table and query score
choose a score bin. Actual calibration labels produce its empirical success
rate and a confidence interval. All predeclared model/query pairs are paid for,
including bins selected using these labels. This is a bin-conditional probability,
not pointwise correctness, exact population calibration, or a causal law.

The iid/common-law theorem concerns the visible feature/label observations.
Real EventId checks and declared protocol equality do not prove those premises.
The supported flag records an external support decision; it is not an OOD proof.
-/

namespace JurisLean.Candidates.ProbabilityIntervalConsumer20261027

open MeasureTheory ProbabilityTheory
open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.LearningConsumer20261027
open JurisLean.Candidates.LearningERM20261027
open JurisLean.Candidates.LearningFiniteClass20261027
open JurisLean.Candidates.SelectiveCalibration20261027
open JurisLean.Candidates.SampleCalibrationConsumer20261027

def scoreBin {m : ℕ} (candidate : List ℚ × Fin m) (row : Fin m × Bool) : Bool :=
  decide (candidate.1.getD row.1.val 0 = candidate.1.getD candidate.2.val 0)

def successLabel {m : ℕ} (_ : List ℚ × Fin m) (row : Fin m × Bool) : ℚ :=
  if row.2 then 1 else 0

def modelBins {m : ℕ} (models : List (List ℚ)) : Finset (List ℚ × Fin m) :=
  models.toFinset.product Finset.univ

structure SampleProbability (m : ℕ) where
  fitted : FittedTable
  query : Fin m
  models : List (List ℚ)
  sampleSize : ℕ
  snapshot : ℕ
  radius : ℚ
  radiusExponent : ℕ
  successMass : ℚ
  coverage : ℚ
  deriving DecidableEq, Repr

def SampleProbability.lower {m : ℕ} (out : SampleProbability m) : ℚ :=
  max 0 ((out.successMass - out.radius) / (out.coverage + out.radius))

def SampleProbability.upper {m : ℕ} (out : SampleProbability m) : ℚ :=
  min 1 ((out.successMass + out.radius) / (out.coverage - out.radius))

def SampleProbability.estimate {m : ℕ} (out : SampleProbability m) : ℚ :=
  out.successMass / out.coverage

def produceInterval {m n : ℕ} (sampleProtocol : LearningProtocol)
    (fitted : FittedTable) (models : List (List ℚ)) (data : Fin n → Fin m × Bool)
    (query : Fin m) (radius : ℚ) (exponent snapshot : ℕ) (supported : Bool) :
    Result (SampleProbability m) :=
  if sampleProtocol ≠ fitted.protocol then .unknown .targetMismatch
  else if fitted.table.length ≠ m ∨ fitted.table ∉ models then .unknown .scopeMismatch
  else if supported = false then .unknown .unsupported
  else if radiusVerified n (modelBins (m := m) models).card
      fitted.protocol.failureBudget radius exponent = false then .unknown .missingEvidence
  else
    let candidate := (fitted.table, query)
    let numerator := empiricalScore (numeratorLoss successLabel scoreBin) data candidate
    let denominator := empiricalScore (coverageLoss scoreBin) data candidate
    if ¬ 0 < denominator - radius then .unknown .missingEvidence
    else .known
      { fitted := fitted, query := query, models := models, sampleSize := n
        snapshot := snapshot, radius := radius, radiusExponent := exponent
        successMass := numerator, coverage := denominator }

def runProbability {m n k : ℕ} (protocol sampleProtocol : LearningProtocol)
    (loss : ℚ → Bool → ℚ) (models : List (List ℚ))
    (training : Fin n → SampleObservation m Bool)
    (calibration : Fin k → SampleObservation m Bool)
    (query : Fin m) (radius : ℚ) (exponent snapshot : ℕ) (supported : Bool) :
    Result (SampleProbability m) :=
  if eventPartitionsValid training calibration = false then .unknown .scopeMismatch
  else
    match fitTable protocol loss models (fun i => ((training i).feature, (training i).label)) with
    | .known fitted => produceInterval sampleProtocol fitted models
        (fun i => ((calibration i).feature, (calibration i).label)) query radius exponent snapshot supported
    | .unknown e => .unknown e
    | .rejected e => .rejected e
    | .conflict a b => .conflict a b

theorem actual_fitted_score_selects_the_bin {m : ℕ} (table : List ℚ) (query : Fin m)
    (row : Fin m × Bool) :
    scoreBin (table, query) row = true ↔ table.getD row.1.val 0 = table.getD query.val 0 := by
  simp [scoreBin]

theorem full_model_bin_family_is_counted {m : ℕ} (models : List (List ℚ)) :
    (modelBins (m := m) models).card = models.toFinset.card * m := by
  simp [modelBins, Finset.card_product]

theorem changed_probability_scope_refused {m n : ℕ} (sampleProtocol : LearningProtocol)
    (fitted : FittedTable) (models : List (List ℚ)) (data : Fin n → Fin m × Bool)
    (query : Fin m) (radius : ℚ) (exponent snapshot : ℕ) (supported : Bool)
    (changed : sampleProtocol ≠ fitted.protocol) :
    produceInterval sampleProtocol fitted models data query radius exponent snapshot supported =
      .unknown .targetMismatch := by
  simp [produceInterval, changed]

theorem actual_samples_determine_probability {m n : ℕ} (sampleProtocol : LearningProtocol)
    (fitted : FittedTable) (models : List (List ℚ)) (data : Fin n → Fin m × Bool)
    (query : Fin m) (radius : ℚ) (exponent snapshot : ℕ) (supported : Bool)
    (out : SampleProbability m)
    (accepted : produceInterval sampleProtocol fitted models data query radius exponent snapshot supported =
      .known out) :
    out =
      { fitted := fitted
        query := query
        models := models
        sampleSize := n
        snapshot := snapshot
        radius := radius
        radiusExponent := exponent
        successMass := empiricalScore (numeratorLoss successLabel scoreBin) data (fitted.table, query)
        coverage := empiricalScore (coverageLoss scoreBin) data (fitted.table, query) } ∧
    sampleProtocol = fitted.protocol ∧ fitted.table ∈ models ∧
    radiusVerified n (modelBins (m := m) models).card fitted.protocol.failureBudget radius exponent = true ∧
    0 < empiricalScore (coverageLoss scoreBin) data (fitted.table, query) - radius := by
  unfold produceInterval at accepted
  split at accepted
  · cases accepted
  · rename_i scope
    split at accepted
    · cases accepted
    · rename_i member
      split at accepted
      · cases accepted
      · split at accepted
        · cases accepted
        · rename_i verified
          split at accepted
          · cases accepted
          · rename_i positive
            cases accepted
            exact ⟨rfl, by simpa using scope, by simp_all,
              by simpa using verified, by simpa using positive⟩

theorem empirical_success_bounded_by_coverage {m n : ℕ} (data : Fin n → Fin m × Bool)
    (candidate : List ℚ × Fin m) :
    0 ≤ empiricalScore (numeratorLoss successLabel scoreBin) data candidate ∧
    empiricalScore (numeratorLoss successLabel scoreBin) data candidate ≤
      empiricalScore (coverageLoss scoreBin) data candidate := by
  constructor
  · apply div_nonneg _ (Nat.cast_nonneg n)
    apply Finset.sum_nonneg
    intro i _
    by_cases h : scoreBin candidate (data i) = true <;> cases hy : (data i).2 <;>
      simp [numeratorLoss, successLabel, h, hy]
  · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    apply Finset.sum_le_sum
    intro i _
    by_cases h : scoreBin candidate (data i) = true <;> cases hy : (data i).2 <;>
      simp [numeratorLoss, coverageLoss, successLabel, h, hy]

theorem actual_interval_contains_empirical_probability {m n : ℕ}
    (sampleProtocol : LearningProtocol) (fitted : FittedTable) (models : List (List ℚ))
    (data : Fin n → Fin m × Bool) (query : Fin m) (radius : ℚ)
    (exponent snapshot : ℕ) (supported : Bool) (out : SampleProbability m)
    (accepted : produceInterval sampleProtocol fitted models data query radius exponent snapshot supported =
      .known out) :
    0 ≤ out.lower ∧ out.lower ≤ out.estimate ∧ out.estimate ≤ out.upper ∧ out.upper ≤ 1 := by
  obtain ⟨rfl, _, _, verified, positive⟩ := actual_samples_determine_probability
    sampleProtocol fitted models data query radius exponent snapshot supported out accepted
  have checks : 0 < n ∧ 0 < (modelBins (m := m) models).card ∧
      0 < fitted.protocol.failureBudget ∧ fitted.protocol.failureBudget < 1 ∧ 0 ≤ radius ∧
      4 * ((modelBins (m := m) models).card : ℚ) ≤ fitted.protocol.failureBudget * 2 ^ exponent ∧
      (exponent : ℚ) ≤ 2 * (n : ℚ) * radius ^ 2 := by
    simpa only [radiusVerified, decide_eq_true_eq] using verified
  have hr := checks.2.2.2.2.1
  obtain ⟨hn, hnc⟩ := empirical_success_bounded_by_coverage data (fitted.table, query)
  let N := empiricalScore (numeratorLoss successLabel scoreBin) data (fitted.table, query)
  let C := empiricalScore (coverageLoss scoreBin) data (fitted.table, query)
  have hnr : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn
  have hncr : (N : ℝ) ≤ (C : ℝ) := by exact_mod_cast hnc
  have hrr : (0 : ℝ) ≤ (radius : ℝ) := by exact_mod_cast hr
  have hpos : (0 : ℝ) < (C : ℝ) - (radius : ℝ) := by exact_mod_cast positive
  have enclosure := Probability.u04_2_enclosed_propagation (N : ℝ) (C : ℝ)
    ((N : ℝ) - radius) ((N : ℝ) + radius) ((C : ℝ) - radius) ((C : ℝ) + radius)
    hnr hncr (by linarith) (by linarith) hpos (by linarith) (by linarith)
  have rational : max 0 ((N - radius) / (C + radius)) ≤ N / C ∧
      N / C ≤ min 1 ((N + radius) / (C - radius)) := by exact_mod_cast enclosure
  exact ⟨le_max_left _ _, rational.1, rational.2, min_le_left _ _⟩

theorem pipeline_consumes_actual_fit_and_sample {m n k : ℕ}
    (protocol sampleProtocol : LearningProtocol) (loss : ℚ → Bool → ℚ) (models : List (List ℚ))
    (training : Fin n → SampleObservation m Bool) (calibration : Fin k → SampleObservation m Bool)
    (query : Fin m) (radius : ℚ) (exponent snapshot : ℕ) (supported : Bool)
    (out : SampleProbability m)
    (accepted : runProbability protocol sampleProtocol loss models training calibration
      query radius exponent snapshot supported = .known out) :
    eventPartitionsValid training calibration = true ∧
    ∃ fitted, fitTable protocol loss models (fun i => ((training i).feature, (training i).label)) =
        .known fitted ∧
      produceInterval sampleProtocol fitted models
        (fun i => ((calibration i).feature, (calibration i).label))
        query radius exponent snapshot supported = .known out := by
  unfold runProbability at accepted
  split at accepted
  · cases accepted
  · rename_i events
    cases fitted : fitTable protocol loss models
      (fun i => ((training i).feature, (training i).label)) with
    | known value => exact ⟨by simpa using events, value, rfl, by simpa [fitted] using accepted⟩
    | unknown e => simp [fitted] at accepted
    | rejected e => simp [fitted] at accepted
    | conflict a b => simp [fitted] at accepted

-- Identifies the integral ratio with the actual probability of success within
-- the selected score bin; a positive denominator is established below.
theorem population_bin_integrals {m : ℕ} [MeasurableSpace (Fin m × Bool)]
    [MeasurableSingletonClass (Fin m × Bool)] (P : Measure (Fin m × Bool))
    (candidate : List ℚ × Fin m) :
    (∫ z, (numeratorLoss successLabel scoreBin candidate z : ℝ) ∂P) =
      P.real {z | scoreBin candidate z = true ∧ z.2 = true} ∧
    (∫ z, (coverageLoss scoreBin candidate z : ℝ) ∂P) =
      P.real {z | scoreBin candidate z = true} := by
  have numerator : (fun z => (numeratorLoss successLabel scoreBin candidate z : ℝ)) =
      ({z | scoreBin candidate z = true ∧ z.2 = true} : Set (Fin m × Bool)).indicator 1 := by
    funext z
    by_cases h : scoreBin candidate z = true <;> cases hy : z.2 <;>
      simp [numeratorLoss, successLabel, h, hy, Set.indicator]
  have denominator : (fun z => (coverageLoss scoreBin candidate z : ℝ)) =
      ({z | scoreBin candidate z = true} : Set (Fin m × Bool)).indicator 1 := by
    funext z
    by_cases h : scoreBin candidate z = true <;> simp [coverageLoss, h, Set.indicator]
  constructor
  · rw [numerator, integral_indicator_one (Set.to_countable _).measurableSet]
  · rw [denominator, integral_indicator_one (Set.to_countable _).measurableSet]

theorem whole_pipeline_bin_probability_confidence {Ω : Type*} {m n k : ℕ}
    [MeasurableSpace Ω] [MeasurableSpace (Fin m × Bool)]
    [MeasurableSingletonClass (Fin m × Bool)]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Measure (Fin m × Bool)) [IsProbabilityMeasure P] (hm : 0 < m) (hn : 0 < n)
    (protocol : LearningProtocol) (loss : ℚ → Bool → ℚ)
    (first : List ℚ) (rest : List (List ℚ))
    (sample : Fin n → Ω → Fin m × Bool) (sampleMeasurable : ∀ i, Measurable (sample i))
    (independent : iIndepFun sample μ) (law : ∀ i, IdentDistrib (sample i) id μ P)
    (hδ : 0 < protocol.failureBudget) (hδ1 : protocol.failureBudget < 1) :
    ∃ confidence : Set Ω, MeasurableSet confidence ∧
      1 - (protocol.failureBudget : ℝ) ≤ μ.real confidence ∧
      ∀ w ∈ confidence, ∀ (training : Fin k → SampleObservation m Bool)
        (events : Fin n → EventId) (query : Fin m) (radius : ℚ)
        (exponent snapshot : ℕ) (supported : Bool) (out : SampleProbability m),
        runProbability protocol protocol loss (first :: rest) training
          (fun i => ⟨events i, (sample i w).1, (sample i w).2⟩)
          query radius exponent snapshot supported = .known out →
        0 < P.real {z | scoreBin (out.fitted.table, out.query) z = true} ∧
        (out.lower : ℝ) ≤
          P.real {z | scoreBin (out.fitted.table, out.query) z = true ∧ z.2 = true} /
            P.real {z | scoreBin (out.fitted.table, out.query) z = true} ∧
        P.real {z | scoreBin (out.fitted.table, out.query) z = true ∧ z.2 = true} /
            P.real {z | scoreBin (out.fitted.table, out.query) z = true} ≤ (out.upper : ℝ) := by
  let bins := modelBins (m := m) (first :: rest)
  have nonempty : bins.Nonempty := ⟨(first, ⟨0, hm⟩), by simp [bins, modelBins]⟩
  have numeratorMeasurable : ∀ c ∈ bins,
      Measurable (fun z => (numeratorLoss successLabel scoreBin c z : ℝ)) :=
    fun _ _ => measurable_of_finite _
  have denominatorMeasurable : ∀ c ∈ bins,
      Measurable (fun z => (coverageLoss scoreBin c z : ℝ)) :=
    fun _ _ => measurable_of_finite _
  have bounded : ∀ c ∈ bins, ∀ z, (successLabel c z : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    intro c _ z
    cases hy : z.2 <;> simp [successLabel, hy]
  have hd : (0 : ℝ) < (protocol.failureBudget : ℝ) := by exact_mod_cast hδ
  have hd1 : (protocol.failureBudget : ℝ) < 1 := by exact_mod_cast hδ1
  have uniform := q05_3_simultaneous_numerator_and_coverage μ P hn bins nonempty
    sample sampleMeasurable independent law successLabel scoreBin
    numeratorMeasurable denominatorMeasurable bounded (protocol.failureBudget : ℝ) hd hd1
  refine ⟨_, q05_3_joint_confidence_event_measurable P bins sample sampleMeasurable
    successLabel scoreBin numeratorMeasurable denominatorMeasurable _, uniform, ?_⟩
  intro w hw training events query radius exponent snapshot supported out accepted
  obtain ⟨_, fitted, fit, produced⟩ := pipeline_consumes_actual_fit_and_sample
    protocol protocol loss (first :: rest) training _ query radius exponent snapshot supported out accepted
  obtain ⟨rfl, scope, member, verified, positive⟩ := actual_samples_determine_probability
    protocol fitted (first :: rest) (fun i => sample i w) query radius exponent snapshot supported out produced
  have candidateMember : (fitted.table, query) ∈ bins := by simp [bins, modelBins, member]
  have deviation := hw (fitted.table, query) candidateMember
  have conservative := radius_verification_sound n bins.card
    fitted.protocol.failureBudget radius exponent verified
  rw [← scope] at conservative
  let N := ∫ z, (numeratorLoss successLabel scoreBin (fitted.table, query) z : ℝ) ∂P
  let C := ∫ z, (coverageLoss scoreBin (fitted.table, query) z : ℝ) ∂P
  let nh := empiricalScore (numeratorLoss successLabel scoreBin) (fun i => sample i w) (fitted.table, query)
  let ch := empiricalScore (coverageLoss scoreBin) (fun i => sample i w) (fitted.table, query)
  have hnL : (nh : ℝ) - radius ≤ N := by have h := (abs_le.mp deviation.1).2; dsimp [N, nh]; linarith
  have hnU : N ≤ (nh : ℝ) + radius := by have h := (abs_le.mp deviation.1).1; dsimp [N, nh]; linarith
  have hcL : (ch : ℝ) - radius ≤ C := by have h := (abs_le.mp deviation.2).2; dsimp [C, ch]; linarith
  have hcU : C ≤ (ch : ℝ) + radius := by have h := (abs_le.mp deviation.2).1; dsimp [C, ch]; linarith
  have hpos : (0 : ℝ) < (ch : ℝ) - radius := by exact_mod_cast positive
  have integrals := population_bin_integrals P (fitted.table, query)
  have nNonnegative : 0 ≤ N := by rw [show N = _ from integrals.1]; exact measureReal_nonneg
  have nBelowC : N ≤ C := by
    rw [show N = _ from integrals.1, show C = _ from integrals.2]
    exact measureReal_mono (h₂ := measure_ne_top P _) (fun _ h => h.1)
  have enclosed := Probability.u04_2_enclosed_propagation N C
    ((nh : ℝ) - radius) ((nh : ℝ) + radius) ((ch : ℝ) - radius) ((ch : ℝ) + radius)
    nNonnegative nBelowC hnL hnU hpos hcL hcU
  have coveragePositive : 0 < C := lt_of_lt_of_le hpos hcL
  rw [show N = _ from integrals.1, show C = _ from integrals.2] at enclosed
  rw [show C = _ from integrals.2] at coveragePositive
  exact ⟨coveragePositive, by simpa [SampleProbability.lower, nh, ch] using enclosed.1,
    by simpa [SampleProbability.upper, nh, ch] using enclosed.2⟩

end JurisLean.Candidates.ProbabilityIntervalConsumer20261027
