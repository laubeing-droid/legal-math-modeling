import JurisLean.Candidates.LearningConsumer20261027
import JurisLean.Candidates.SelectiveCalibration20261027

/-!
Actual fitting -> sample calibration -> selective score consumption for original
01/05 and the corresponding U00 edge. The score remains a score, not a proved
probability. Population selective-risk guarantees use the explicit iid/common-law
and bounded-loss hypotheses; the identity checks below do not manufacture them.

The legacy FitContract.independentUnit has type MeasurementId. Actual grouping
here uses the separate real EventId carried by every row, not that legacy field.
-/

namespace JurisLean.Candidates.SampleCalibrationConsumer20261027

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.LearningConsumer20261027
open JurisLean.Candidates.LearningERM20261027
open JurisLean.Candidates.SelectiveCalibration20261027

structure SampleObservation (m : ℕ) (Y : Type) where
  event : EventId
  feature : Fin m
  label : Y
  deriving DecidableEq, Repr

def sampleLoss {m : ℕ} {Y : Type} (fitted : FittedTable) (loss : ℚ → Y → ℚ)
    (_cutoff : ℚ) (row : SampleObservation m Y) : ℚ :=
  tableLoss loss fitted.table (row.feature, row.label)

def tableAcceptance {m : ℕ} {Y : Type} (fitted : FittedTable)
    (cutoff : ℚ) (row : Fin m × Y) : Bool :=
  decide (cutoff ≤ fitted.table.getD row.1.val 0)

def sampleAcceptance {m : ℕ} {Y : Type} (fitted : FittedTable)
    (cutoff : ℚ) (row : SampleObservation m Y) : Bool :=
  tableAcceptance fitted cutoff (row.feature, row.label)

def eventPartitionsValid {m n k : ℕ} {Y : Type}
    (training : Fin n → SampleObservation m Y)
    (calibration : Fin k → SampleObservation m Y) : Bool :=
  decide (Function.Injective (fun i => (calibration i).event) ∧
    ∀ i j, (training i).event ≠ (calibration j).event)

structure SampleCalibration where
  fitted : FittedTable
  cutoff : ℚ
  radius : ℚ
  calibrationRows : Nat
  candidateCutoffs : List ℚ
  certificate : TableCalibration
  deriving DecidableEq, Repr

def produceCalibration {m n : ℕ} {Y : Type} (sampleProtocol : LearningProtocol)
    (fitted : FittedTable) (loss : ℚ → Y → ℚ) (cutoffs : List ℚ)
    (rows : Fin n → SampleObservation m Y) (radius target : ℚ)
    (snapshot calibrationProtocol : Nat) : Result SampleCalibration :=
  if sampleProtocol ≠ fitted.protocol then .unknown .targetMismatch
  else if fitted.table.length ≠ m then .unknown .scopeMismatch
  else if ¬ (0 < fitted.protocol.failureBudget ∧ fitted.protocol.failureBudget < 1) then
    .unknown .unsupported
  else if ¬ (∀ i, 0 ≤ sampleLoss fitted loss 0 (rows i) ∧
      sampleLoss fitted loss 0 (rows i) ≤ 1) then .unknown .unsupported
  else
    match calibrate (sampleLoss fitted loss) (sampleAcceptance fitted) cutoffs rows radius target with
    | none => .unknown .missingEvidence
    | some cutoff =>
        let low := lowerCoverage (sampleAcceptance fitted) rows radius cutoff
        let upper := upperNumerator (sampleLoss fitted loss) (sampleAcceptance fitted) rows radius cutoff
        .known
          { fitted := fitted
            cutoff := cutoff
            radius := radius
            calibrationRows := n
            candidateCutoffs := cutoffs
            certificate :=
              { protocol := fitted.protocol
                table := fitted.table
                bounds :=
                  { contract := fitted.protocol.fit
                    lowerCoverage := low
                    upperRisk := upper / low
                    protocol := calibrationProtocol
                    validationSnapshot := snapshot
                    protectedGroups := [] } } }

def predictCalibrated {m : ℕ} (expected : LearningProtocol) (calibrated : SampleCalibration)
    (query : Fin m) (target : ℚ) (supported : Bool) : Result TaskScore :=
  if ¬ calibrated.cutoff ≤ calibrated.fitted.table.getD query.val 0 then .unknown .unsupported
  else consumeCalibration expected calibrated.fitted query calibrated.certificate target supported

def runSamples {m n k : ℕ} {Y : Type} (protocol sampleProtocol : LearningProtocol)
    (loss : ℚ → Y → ℚ) (models : List (List ℚ)) (cutoffs : List ℚ)
    (training : Fin n → SampleObservation m Y)
    (calibration : Fin k → SampleObservation m Y) (query : Fin m)
    (radius target : ℚ) (snapshot calibrationProtocol : Nat) (supported : Bool) :
    Result (SampleCalibration × TaskScore) :=
  if eventPartitionsValid training calibration = false then .unknown .scopeMismatch
  else
    match fitTable protocol loss models (fun i => ((training i).feature, (training i).label)) with
    | .known fitted =>
        match produceCalibration sampleProtocol fitted loss cutoffs calibration radius target
          snapshot calibrationProtocol with
        | .known calibrated =>
            match predictCalibrated protocol calibrated query target supported with
            | .known score => .known (calibrated, score)
            | .unknown e => .unknown e
            | .rejected e => .rejected e
            | .conflict a b => .conflict a b
        | .unknown e => .unknown e
        | .rejected e => .rejected e
        | .conflict a b => .conflict a b
    | .unknown e => .unknown e
    | .rejected e => .rejected e
    | .conflict a b => .conflict a b

theorem event_guard_uses_real_identity {m n k : ℕ} {Y : Type}
    (training : Fin n → SampleObservation m Y) (calibration : Fin k → SampleObservation m Y) :
    eventPartitionsValid training calibration = true ↔
      Function.Injective (fun i => (calibration i).event) ∧
        ∀ i j, (training i).event ≠ (calibration j).event := by
  simp [eventPartitionsValid]

theorem changed_sample_scope_refused {m n : ℕ} {Y : Type} (sampleProtocol : LearningProtocol)
    (fitted : FittedTable) (loss : ℚ → Y → ℚ) (cutoffs : List ℚ)
    (rows : Fin n → SampleObservation m Y) (radius target : ℚ) (snapshot calibrationProtocol : Nat)
    (changed : sampleProtocol ≠ fitted.protocol) :
    produceCalibration sampleProtocol fitted loss cutoffs rows radius target snapshot calibrationProtocol =
      .unknown .targetMismatch := by
  simp [produceCalibration, changed]

theorem actual_sample_produces_the_certificate {m n : ℕ} {Y : Type}
    (sampleProtocol : LearningProtocol) (fitted : FittedTable) (loss : ℚ → Y → ℚ)
    (cutoffs : List ℚ) (rows : Fin n → SampleObservation m Y) (radius target : ℚ)
    (snapshot calibrationProtocol : Nat) (out : SampleCalibration)
    (accepted : produceCalibration sampleProtocol fitted loss cutoffs rows radius target
      snapshot calibrationProtocol = .known out) :
    out.fitted = fitted ∧ out.radius = radius ∧ out.calibrationRows = n ∧
    out.candidateCutoffs = cutoffs ∧ out.certificate.protocol = fitted.protocol ∧
    out.certificate.table = fitted.table ∧
    out.certificate.bounds.lowerCoverage = lowerCoverage (sampleAcceptance fitted) rows radius out.cutoff ∧
    out.certificate.bounds.upperRisk =
      upperNumerator (sampleLoss fitted loss) (sampleAcceptance fitted) rows radius out.cutoff /
        lowerCoverage (sampleAcceptance fitted) rows radius out.cutoff ∧
    calibrate (sampleLoss fitted loss) (sampleAcceptance fitted) cutoffs rows radius target = some out.cutoff := by
  unfold produceCalibration at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · cases accepted
    · split at accepted
      · cases accepted
      · split at accepted
        · cases accepted
        · cases selected : calibrate (sampleLoss fitted loss) (sampleAcceptance fitted)
            cutoffs rows radius target with
          | none => simp [selected] at accepted
          | some cutoff =>
              simp only [selected] at accepted
              cases accepted
              exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, selected⟩

theorem query_outside_selected_rule_refused {m : ℕ} (expected : LearningProtocol)
    (calibrated : SampleCalibration) (query : Fin m) (target : ℚ) (supported : Bool)
    (outside : ¬ calibrated.cutoff ≤ calibrated.fitted.table.getD query.val 0) :
    predictCalibrated expected calibrated query target supported = .unknown .unsupported := by
  unfold predictCalibrated
  rw [if_pos outside]

theorem prediction_reads_actual_fitted_table {m : ℕ} (expected : LearningProtocol)
    (calibrated : SampleCalibration) (query : Fin m) (target : ℚ) (supported : Bool)
    (out : TaskScore) (accepted : predictCalibrated expected calibrated query target supported = .known out) :
    out.protocol = calibrated.fitted.protocol ∧
    out.value = calibrated.fitted.table.getD query.val 0 ∧
    out.bounds = calibrated.certificate.bounds ∧ calibrated.cutoff ≤ out.value := by
  unfold predictCalibrated at accepted
  split at accepted
  · cases accepted
  · rename_i selected
    have eligible := not_not.mp selected
    unfold consumeCalibration at accepted
    split at accepted
    · cases accepted
    · split at accepted
      · cases accepted
      · cases gate : Calibration.proposed_calibration_support_gate calibrated.fitted.protocol.fit
            calibrated.certificate.bounds target supported with
        | unknown e => simp [gate] at accepted
        | rejected e => simp [gate] at accepted
        | conflict a b => simp [gate] at accepted
        | known bounds =>
            simp only [gate] at accepted
            cases accepted
            have sameBounds : bounds = calibrated.certificate.bounds := by
              unfold Calibration.proposed_calibration_support_gate at gate
              split at gate
              · cases gate
              · split at gate
                · cases gate
                · split at gate
                  · cases gate
                    rfl
                  · cases gate
            exact ⟨rfl, rfl, sameBounds, eligible⟩

theorem pipeline_consumes_the_actual_empirical_minimizer {m n k : ℕ} {Y : Type}
    (protocol sampleProtocol : LearningProtocol) (loss : ℚ → Y → ℚ)
    (models : List (List ℚ)) (cutoffs : List ℚ)
    (training : Fin n → SampleObservation m Y) (calibration : Fin k → SampleObservation m Y)
    (query : Fin m) (radius target : ℚ) (snapshot calibrationProtocol : Nat) (supported : Bool)
    (out : SampleCalibration × TaskScore)
    (accepted : runSamples protocol sampleProtocol loss models cutoffs training calibration query
      radius target snapshot calibrationProtocol supported = .known out) :
    Function.Injective (fun i => (calibration i).event) ∧
    (∀ i j, (training i).event ≠ (calibration j).event) ∧
    out.1.fitted.table ∈ models ∧
    out.2.value = out.1.fitted.table.getD query.val 0 ∧
    (∀ table ∈ models,
      empiricalScore (tableLoss loss) (fun i => ((training i).feature, (training i).label)) out.1.fitted.table ≤
        empiricalScore (tableLoss loss) (fun i => ((training i).feature, (training i).label)) table) := by
  unfold runSamples at accepted
  split at accepted
  · cases accepted
  · rename_i valid
    have checked : eventPartitionsValid training calibration = true := by
      cases h : eventPartitionsValid training calibration <;> simp_all
    have identities := (event_guard_uses_real_identity training calibration).mp checked
    cases fittedResult : fitTable protocol loss models
        (fun i => ((training i).feature, (training i).label)) with
    | unknown e => simp [fittedResult] at accepted
    | rejected e => simp [fittedResult] at accepted
    | conflict a b => simp [fittedResult] at accepted
    | known fitted =>
        simp only [fittedResult] at accepted
        cases calibratedResult : produceCalibration sampleProtocol fitted loss cutoffs calibration
            radius target snapshot calibrationProtocol with
        | unknown e => simp [calibratedResult] at accepted
        | rejected e => simp [calibratedResult] at accepted
        | conflict a b => simp [calibratedResult] at accepted
        | known calibrated =>
            simp only [calibratedResult] at accepted
            cases prediction : predictCalibrated protocol calibrated query target supported with
            | unknown e => simp [prediction] at accepted
            | rejected e => simp [prediction] at accepted
            | conflict a b => simp [prediction] at accepted
            | known score =>
                simp only [prediction] at accepted
                cases accepted
                have best := u01_6_fit_card_minimizes_actual_sample protocol loss models
                  (fun i => ((training i).feature, (training i).label)) fitted fittedResult
                have bound := actual_sample_produces_the_certificate sampleProtocol fitted loss cutoffs
                  calibration radius target snapshot calibrationProtocol calibrated calibratedResult
                have consumed := prediction_reads_actual_fitted_table protocol calibrated query target
                  supported score prediction
                refine ⟨identities.1, identities.2, ?_, consumed.2.1, ?_⟩
                · simpa only [bound.1] using best.2.2.2.1
                · simpa only [bound.1] using best.2.2.2.2.2

open MeasureTheory ProbabilityTheory
open JurisLean.Candidates.LearningFiniteClass20261027

-- Fixed fitted contents and family: when fitted is random, the iid law here
-- must hold conditionally on its training history or for a jointly fixed family.
-- This law concerns visible feature/label pairs. Event IDs are separate metadata
-- and may be assigned deterministically; they are not required to be iid.
theorem actual_certificate_consumes_population_risk_bound {Ω : Type*} [MeasurableSpace Ω]
    {m n : ℕ} {Y : Type} [MeasurableSpace (Fin m × Y)]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Measure (Fin m × Y)) [IsProbabilityMeasure P]
    (hn : 0 < n) (sampleProtocol : LearningProtocol) (fitted : FittedTable)
    (first : ℚ) (rest : List ℚ) (sample : Fin n → Ω → Fin m × Y)
    (events : Fin n → Ω → EventId)
    (sampleMeasurable : ∀ i, Measurable (sample i))
    (independent : iIndepFun sample μ) (law : ∀ i, IdentDistrib (sample i) id μ P)
    (loss : ℚ → Y → ℚ)
    (numeratorMeasurable : ∀ h ∈ first :: rest,
      Measurable (fun z : Fin m × Y =>
        (numeratorLoss (fun _ z => tableLoss loss fitted.table z) (tableAcceptance fitted) h z : ℝ)))
    (coverageMeasurable : ∀ h ∈ first :: rest,
      Measurable (fun z : Fin m × Y => (coverageLoss (tableAcceptance fitted) h z : ℝ)))
    (lossRange : ∀ z : Fin m × Y, (tableLoss loss fitted.table z : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (hδ : 0 < (fitted.protocol.failureBudget : ℝ))
    (hδ1 : (fitted.protocol.failureBudget : ℝ) < 1) (radius target : ℚ)
    (conservative : finiteRadius n (2 * (first :: rest).toFinset.card)
      (fitted.protocol.failureBudget : ℝ) ≤ (radius : ℝ)) (snapshot calibrationProtocol : Nat) :
    ∃ confidence : Set Ω, MeasurableSet confidence ∧
      1 - (fitted.protocol.failureBudget : ℝ) ≤ μ.real confidence ∧
      ∀ w ∈ confidence, ∀ out,
        produceCalibration sampleProtocol fitted loss (first :: rest)
          (fun i => ⟨events i w, (sample i w).1, (sample i w).2⟩)
          radius target snapshot calibrationProtocol = .known out →
        0 < ∫ z, (coverageLoss (tableAcceptance out.fitted) out.cutoff z : ℝ) ∂P ∧
        (∫ z, (numeratorLoss (fun _ z => tableLoss loss out.fitted.table z)
          (tableAcceptance out.fitted) out.cutoff z : ℝ) ∂P) /
          (∫ z, (coverageLoss (tableAcceptance out.fitted) out.cutoff z : ℝ) ∂P) ≤ (target : ℝ) := by
  obtain ⟨confidence, measurable, probability, safe⟩ :=
    q05_3_selected_threshold_has_population_risk_bound μ P hn first rest sample sampleMeasurable
      independent law (fun _ z => tableLoss loss fitted.table z) (tableAcceptance fitted) numeratorMeasurable
      coverageMeasurable (fun _ _ z => lossRange z) (fitted.protocol.failureBudget : ℝ)
      hδ hδ1 radius target conservative
  refine ⟨confidence, measurable, probability, ?_⟩
  intro w hw out accepted
  have source := actual_sample_produces_the_certificate sampleProtocol fitted loss (first :: rest)
    (fun i => ⟨events i w, (sample i w).1, (sample i w).2⟩)
    radius target snapshot calibrationProtocol out accepted
  have selected : calibrate (fun _ z => tableLoss loss fitted.table z) (tableAcceptance fitted)
      (first :: rest) (fun i => sample i w) radius target = some out.cutoff :=
    source.2.2.2.2.2.2.2.2
  simpa only [source.1] using safe w hw out.cutoff selected

end JurisLean.Candidates.SampleCalibrationConsumer20261027
