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
open JurisLean.Candidates.LearningFiniteClass20261027

-- An exact rational certificate for the logarithmic radius. The natural witness
-- is checked, not trusted; log (4M / delta) <= log (2^exponent) <= exponent.
def radiusVerified (n M : ℕ) (delta radius : ℚ) (exponent : ℕ) : Bool :=
  decide (0 < n ∧ 0 < M ∧ 0 < delta ∧ delta < 1 ∧ 0 ≤ radius ∧
    4 * (M : ℚ) ≤ delta * (2 : ℚ) ^ exponent ∧
    (exponent : ℚ) ≤ 2 * (n : ℚ) * radius ^ 2)

theorem radius_verification_sound (n M : ℕ) (delta radius : ℚ) (exponent : ℕ)
    (verified : radiusVerified n M delta radius exponent = true) :
    finiteRadius n (2 * M) (delta : ℝ) ≤ (radius : ℝ) := by
  have checks : 0 < n ∧ 0 < M ∧ 0 < delta ∧ delta < 1 ∧ 0 ≤ radius ∧
      4 * (M : ℚ) ≤ delta * (2 : ℚ) ^ exponent ∧
      (exponent : ℚ) ≤ 2 * (n : ℚ) * radius ^ 2 := by
    simpa only [radiusVerified, decide_eq_true_eq] using verified
  obtain ⟨hn, hM, hd, hd1, hr, hsize, hwidth⟩ := checks
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hM1 : 1 ≤ M := by omega
  have hM1R : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hdR : (0 : ℝ) < (delta : ℝ) := by exact_mod_cast hd
  have hd1R : (delta : ℝ) < 1 := by exact_mod_cast hd1
  have hrR : (0 : ℝ) ≤ (radius : ℝ) := by exact_mod_cast hr
  have hsizeR : 4 * (M : ℝ) ≤ (delta : ℝ) * (2 : ℝ) ^ exponent := by
    exact_mod_cast hsize
  have hwidthR : (exponent : ℝ) ≤ 2 * (n : ℝ) * (radius : ℝ) ^ 2 := by
    exact_mod_cast hwidth
  have argumentPositive : 0 < 4 * (M : ℝ) / (delta : ℝ) :=
    div_pos (by linarith) hdR
  have argumentOne : 1 ≤ 4 * (M : ℝ) / (delta : ℝ) :=
    (le_div_iff₀ hdR).mpr (by nlinarith)
  have argumentBound : 4 * (M : ℝ) / (delta : ℝ) ≤ (2 : ℝ) ^ exponent :=
    (div_le_iff₀ hdR).mpr (by simpa only [mul_comm] using hsizeR)
  have logTwo : Real.log 2 ≤ 1 := by
    have bound := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have logarithmBound : Real.log (4 * (M : ℝ) / (delta : ℝ)) ≤ (exponent : ℝ) := by
    calc
      _ ≤ Real.log ((2 : ℝ) ^ exponent) := Real.log_le_log argumentPositive argumentBound
      _ = (exponent : ℝ) * Real.log 2 := Real.log_pow _ _
      _ ≤ (exponent : ℝ) * 1 := mul_le_mul_of_nonneg_left logTwo (by positivity)
      _ = _ := mul_one _
  have quotientNonnegative : 0 ≤ Real.log (4 * (M : ℝ) / (delta : ℝ)) / (2 * (n : ℝ)) :=
    div_nonneg (Real.log_nonneg argumentOne) (by positivity)
  have quotientBound : Real.log (4 * (M : ℝ) / (delta : ℝ)) / (2 * (n : ℝ)) ≤
      (radius : ℝ) ^ 2 :=
    (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (n : ℝ))).mpr (by nlinarith)
  have squared := Real.sq_sqrt quotientNonnegative
  have rootBound : Real.sqrt (Real.log (4 * (M : ℝ) / (delta : ℝ)) / (2 * (n : ℝ))) ≤
      (radius : ℝ) := by
    nlinarith [Real.sqrt_nonneg (Real.log (4 * (M : ℝ) / (delta : ℝ)) / (2 * (n : ℝ)))]
  have normalize : 2 * ((2 * M : ℕ) : ℝ) = 4 * (M : ℝ) := by
    push_cast
    ring
  simpa only [finiteRadius, normalize] using rootBound

structure SampleObservation (m : ℕ) (Y : Type) where
  event : EventId
  feature : Fin m
  label : Y
  deriving DecidableEq, Repr

def candidateLoss {m : ℕ} {Y : Type} (loss : ℚ → Y → ℚ)
    (candidate : List ℚ × ℚ) (row : Fin m × Y) : ℚ :=
  tableLoss loss candidate.1 row

def candidateAcceptance {m : ℕ} {Y : Type} (candidate : List ℚ × ℚ)
    (row : Fin m × Y) : Bool :=
  decide (candidate.2 ≤ candidate.1.getD row.1.val 0)

def sampleLoss {m : ℕ} {Y : Type} (fitted : FittedTable) (loss : ℚ → Y → ℚ)
    (cutoff : ℚ) (row : SampleObservation m Y) : ℚ :=
  candidateLoss loss (fitted.table, cutoff) (row.feature, row.label)

def tableAcceptance {m : ℕ} {Y : Type} (fitted : FittedTable)
    (cutoff : ℚ) (row : Fin m × Y) : Bool :=
  candidateAcceptance (fitted.table, cutoff) row

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
  radiusExponent : Nat
  calibrationRows : Nat
  candidateCutoffs : List ℚ
  certificate : TableCalibration
  deriving DecidableEq, Repr

def produceCalibration {m n : ℕ} {Y : Type} (sampleProtocol : LearningProtocol)
    (fitted : FittedTable) (loss : ℚ → Y → ℚ) (cutoffs : List ℚ)
    (rows : Fin n → SampleObservation m Y) (radius target : ℚ)
    (snapshot calibrationProtocol radiusExponent : Nat) : Result SampleCalibration :=
  if sampleProtocol ≠ fitted.protocol then .unknown .targetMismatch
  else if fitted.table.length ≠ m then .unknown .scopeMismatch
  else if ¬ (0 < fitted.protocol.failureBudget ∧ fitted.protocol.failureBudget < 1) then
    .unknown .unsupported
  else if ¬ (∀ i, 0 ≤ sampleLoss fitted loss 0 (rows i) ∧
      sampleLoss fitted loss 0 (rows i) ≤ 1) then .unknown .unsupported
  else if radiusVerified n cutoffs.toFinset.card fitted.protocol.failureBudget radius radiusExponent = false then
    .unknown .missingEvidence
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
            radiusExponent := radiusExponent
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
    (radius target : ℚ) (snapshot calibrationProtocol radiusExponent : Nat) (supported : Bool) :
    Result (SampleCalibration × TaskScore) :=
  if eventPartitionsValid training calibration = false then .unknown .scopeMismatch
  else if radiusVerified k (models.toFinset.product cutoffs.toFinset).card
      protocol.failureBudget radius radiusExponent = false then .unknown .missingEvidence
  else
    match fitTable protocol loss models (fun i => ((training i).feature, (training i).label)) with
    | .known fitted =>
        match produceCalibration sampleProtocol fitted loss cutoffs calibration radius target
          snapshot calibrationProtocol radiusExponent with
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
    (rows : Fin n → SampleObservation m Y) (radius target : ℚ) (snapshot calibrationProtocol radiusExponent : Nat)
    (changed : sampleProtocol ≠ fitted.protocol) :
    produceCalibration sampleProtocol fitted loss cutoffs rows radius target snapshot calibrationProtocol radiusExponent =
      .unknown .targetMismatch := by
  simp [produceCalibration, changed]

theorem actual_sample_produces_the_certificate {m n : ℕ} {Y : Type}
    (sampleProtocol : LearningProtocol) (fitted : FittedTable) (loss : ℚ → Y → ℚ)
    (cutoffs : List ℚ) (rows : Fin n → SampleObservation m Y) (radius target : ℚ)
    (snapshot calibrationProtocol radiusExponent : Nat) (out : SampleCalibration)
    (accepted : produceCalibration sampleProtocol fitted loss cutoffs rows radius target
      snapshot calibrationProtocol radiusExponent = .known out) :
    out.fitted = fitted ∧ out.radius = radius ∧ out.calibrationRows = n ∧
    out.candidateCutoffs = cutoffs ∧ out.certificate.protocol = fitted.protocol ∧
    out.certificate.table = fitted.table ∧
    out.certificate.bounds.lowerCoverage = lowerCoverage (sampleAcceptance fitted) rows radius out.cutoff ∧
    out.certificate.bounds.upperRisk =
      upperNumerator (sampleLoss fitted loss) (sampleAcceptance fitted) rows radius out.cutoff /
        lowerCoverage (sampleAcceptance fitted) rows radius out.cutoff ∧
    calibrate (sampleLoss fitted loss) (sampleAcceptance fitted) cutoffs rows radius target = some out.cutoff ∧
    out.radiusExponent = radiusExponent := by
  unfold produceCalibration at accepted
  split at accepted
  · cases accepted
  · split at accepted
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
                exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

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
    (query : Fin m) (radius target : ℚ) (snapshot calibrationProtocol radiusExponent : Nat) (supported : Bool)
    (out : SampleCalibration × TaskScore)
    (accepted : runSamples protocol sampleProtocol loss models cutoffs training calibration query
      radius target snapshot calibrationProtocol radiusExponent supported = .known out) :
    Function.Injective (fun i => (calibration i).event) ∧
    (∀ i j, (training i).event ≠ (calibration j).event) ∧
    out.1.fitted.protocol = protocol ∧
    out.1.fitted.table ∈ models ∧
    out.2.value = out.1.fitted.table.getD query.val 0 ∧
    (∀ table ∈ models,
      empiricalScore (tableLoss loss) (fun i => ((training i).feature, (training i).label)) out.1.fitted.table ≤
        empiricalScore (tableLoss loss) (fun i => ((training i).feature, (training i).label)) table) ∧
    produceCalibration sampleProtocol out.1.fitted loss cutoffs calibration radius target
      snapshot calibrationProtocol radiusExponent = .known out.1 := by
  unfold runSamples at accepted
  split at accepted
  · cases accepted
  · rename_i valid
    have checked : eventPartitionsValid training calibration = true := by
      cases h : eventPartitionsValid training calibration <;> simp_all
    have identities := (event_guard_uses_real_identity training calibration).mp checked
    split at accepted
    · cases accepted
    · cases fittedResult : fitTable protocol loss models
          (fun i => ((training i).feature, (training i).label)) with
      | unknown e => simp [fittedResult] at accepted
      | rejected e => simp [fittedResult] at accepted
      | conflict a b => simp [fittedResult] at accepted
      | known fitted =>
          simp only [fittedResult] at accepted
          cases calibratedResult : produceCalibration sampleProtocol fitted loss cutoffs calibration
              radius target snapshot calibrationProtocol radiusExponent with
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
                    calibration radius target snapshot calibrationProtocol radiusExponent calibrated calibratedResult
                  have consumed := prediction_reads_actual_fitted_table protocol calibrated query target
                    supported score prediction
                  refine ⟨identities.1, identities.2, ?_, ?_, consumed.2.1, ?_, ?_⟩
                  · simpa only [bound.1] using best.1
                  · simpa only [bound.1] using best.2.2.2.1
                  · simpa only [bound.1] using best.2.2.2.2.2
                  · simpa only [bound.1] using calibratedResult

theorem pipeline_checks_joint_radius {m n k : ℕ} {Y : Type}
    (protocol sampleProtocol : LearningProtocol) (loss : ℚ → Y → ℚ)
    (models : List (List ℚ)) (cutoffs : List ℚ)
    (training : Fin n → SampleObservation m Y) (calibration : Fin k → SampleObservation m Y)
    (query : Fin m) (radius target : ℚ) (snapshot calibrationProtocol radiusExponent : Nat)
    (supported : Bool) (out : SampleCalibration × TaskScore)
    (accepted : runSamples protocol sampleProtocol loss models cutoffs training calibration query
      radius target snapshot calibrationProtocol radiusExponent supported = .known out) :
    radiusVerified k (models.toFinset.product cutoffs.toFinset).card
      protocol.failureBudget radius radiusExponent = true := by
  unfold runSamples at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · cases accepted
    · rename_i valid
      cases checked : radiusVerified k (models.toFinset.product cutoffs.toFinset).card
          protocol.failureBudget radius radiusExponent <;> simp_all

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
      (fitted.protocol.failureBudget : ℝ) ≤ (radius : ℝ)) (snapshot calibrationProtocol radiusExponent : Nat) :
    ∃ confidence : Set Ω, MeasurableSet confidence ∧
      1 - (fitted.protocol.failureBudget : ℝ) ≤ μ.real confidence ∧
      ∀ w ∈ confidence, ∀ out,
        produceCalibration sampleProtocol fitted loss (first :: rest)
          (fun i => ⟨events i w, (sample i w).1, (sample i w).2⟩)
          radius target snapshot calibrationProtocol radiusExponent = .known out →
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
    radius target snapshot calibrationProtocol radiusExponent out accepted
  have selected : calibrate (fun _ z => tableLoss loss fitted.table z) (tableAcceptance fitted)
      (first :: rest) (fun i => sample i w) radius target = some out.cutoff :=
    source.2.2.2.2.2.2.2.2.1
  simpa only [source.1] using safe w hw out.cutoff selected

-- The entire fixed model/rule family is controlled before either is selected.
-- Training may depend on the same random history; no independence of training
-- from calibration is needed here because every model/rule pair is covered.
-- The larger radius pays for BOTH model and rule selection, not only the rule.
theorem whole_pipeline_joint_family_risk_bound {Ω : Type*} [MeasurableSpace Ω]
    {m n trainN : ℕ} {Y : Type} [MeasurableSpace (Fin m × Y)]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Measure (Fin m × Y)) [IsProbabilityMeasure P]
    (hn : 0 < n) (protocol sampleProtocol : LearningProtocol)
    (firstModel : List ℚ) (restModels : List (List ℚ))
    (firstCutoff : ℚ) (restCutoffs : List ℚ)
    (training : Fin trainN → Ω → SampleObservation m Y)
    (sample : Fin n → Ω → Fin m × Y) (events : Fin n → Ω → EventId)
    (sampleMeasurable : ∀ i, Measurable (sample i))
    (independent : iIndepFun sample μ) (law : ∀ i, IdentDistrib (sample i) id μ P)
    (loss : ℚ → Y → ℚ)
    (numeratorMeasurable : ∀ h ∈
        (firstModel :: restModels).toFinset.product (firstCutoff :: restCutoffs).toFinset,
      Measurable (fun z : Fin m × Y => (numeratorLoss (candidateLoss loss) candidateAcceptance h z : ℝ)))
    (coverageMeasurable : ∀ h ∈
        (firstModel :: restModels).toFinset.product (firstCutoff :: restCutoffs).toFinset,
      Measurable (fun z : Fin m × Y => (coverageLoss candidateAcceptance h z : ℝ)))
    (lossRange : ∀ table ∈ firstModel :: restModels, ∀ z : Fin m × Y,
      (tableLoss loss table z : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (hδ : 0 < (protocol.failureBudget : ℝ)) (hδ1 : (protocol.failureBudget : ℝ) < 1)
    (query : Fin m) (radius target : ℚ)
    (snapshot calibrationProtocol radiusExponent : Nat) (supported : Bool) :
    ∃ confidence : Set Ω, MeasurableSet confidence ∧
      1 - (protocol.failureBudget : ℝ) ≤ μ.real confidence ∧
      ∀ w ∈ confidence, ∀ out,
        runSamples protocol sampleProtocol loss (firstModel :: restModels) (firstCutoff :: restCutoffs)
          (fun i => training i w) (fun i => ⟨events i w, (sample i w).1, (sample i w).2⟩)
          query radius target snapshot calibrationProtocol radiusExponent supported = .known out →
        0 < ∫ z, (coverageLoss candidateAcceptance (out.1.fitted.table, out.1.cutoff) z : ℝ) ∂P ∧
        (∫ z, (numeratorLoss (candidateLoss loss) candidateAcceptance
          (out.1.fitted.table, out.1.cutoff) z : ℝ) ∂P) /
          (∫ z, (coverageLoss candidateAcceptance (out.1.fitted.table, out.1.cutoff) z : ℝ) ∂P) ≤
            (target : ℝ) := by
  let family := (firstModel :: restModels).toFinset.product (firstCutoff :: restCutoffs).toFinset
  have familyNonempty : family.Nonempty := ⟨(firstModel, firstCutoff), by simp [family]⟩
  have pairRange : ∀ candidate ∈ family, ∀ z : Fin m × Y,
      (candidateLoss loss candidate z : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    intro candidate member z
    exact lossRange candidate.1 (List.mem_toFinset.mp (Finset.mem_product.mp member).1) z
  have uniform := q05_3_simultaneous_numerator_and_coverage μ P hn family familyNonempty
    sample sampleMeasurable independent law (candidateLoss loss) candidateAcceptance
    numeratorMeasurable coverageMeasurable pairRange (protocol.failureBudget : ℝ) hδ hδ1
  refine ⟨_, q05_3_joint_confidence_event_measurable P family sample sampleMeasurable
    (candidateLoss loss) candidateAcceptance numeratorMeasurable coverageMeasurable _, uniform, ?_⟩
  intro w hw out accepted
  have radiusChecked := pipeline_checks_joint_radius protocol sampleProtocol loss
    (firstModel :: restModels) (firstCutoff :: restCutoffs) (fun i => training i w)
    (fun i => ⟨events i w, (sample i w).1, (sample i w).2⟩)
    query radius target snapshot calibrationProtocol radiusExponent supported out accepted
  have conservative := radius_verification_sound n family.card protocol.failureBudget radius
    radiusExponent radiusChecked
  obtain ⟨_, _, _, modelMember, _, _, produced⟩ := pipeline_consumes_the_actual_empirical_minimizer
    protocol sampleProtocol loss (firstModel :: restModels) (firstCutoff :: restCutoffs)
    (fun i => training i w) (fun i => ⟨events i w, (sample i w).1, (sample i w).2⟩)
    query radius target snapshot calibrationProtocol radiusExponent supported out accepted
  have receipt := actual_sample_produces_the_certificate sampleProtocol out.1.fitted loss
    (firstCutoff :: restCutoffs) (fun i => ⟨events i w, (sample i w).1, (sample i w).2⟩)
    radius target snapshot calibrationProtocol radiusExponent out.1 produced
  have selected := receipt.2.2.2.2.2.2.2.2.1
  unfold calibrate at selected
  split at selected
  · cases selected
  · have pass := q05_3_selectPassing_spec _ _ _ _ out.1.cutoff selected
    let chosen := (out.1.fitted.table, out.1.cutoff)
    have member : chosen ∈ family := Finset.mem_product.mpr
      ⟨List.mem_toFinset.mpr modelMember, List.mem_toFinset.mpr pass.1⟩
    have deviation := hw chosen member
    have lowerPositiveQ : 0 < lowerCoverage candidateAcceptance (fun i => sample i w) radius chosen :=
      pass.2.1
    have gateQ : upperNumerator (candidateLoss loss) candidateAcceptance (fun i => sample i w) radius chosen /
        lowerCoverage candidateAcceptance (fun i => sample i w) radius chosen ≤ target := pass.2.2
    have numeratorBound : (∫ z, (numeratorLoss (candidateLoss loss) candidateAcceptance chosen z : ℝ) ∂P) ≤
        (upperNumerator (candidateLoss loss) candidateAcceptance (fun i => sample i w) radius chosen : ℝ) := by
      have lower := (abs_le.mp deviation.1).1
      simp only [upperNumerator, Rat.cast_add]
      linarith
    have coverageBound : (lowerCoverage candidateAcceptance (fun i => sample i w) radius chosen : ℝ) ≤
        ∫ z, (coverageLoss candidateAcceptance chosen z : ℝ) ∂P := by
      have upper := (abs_le.mp deviation.2).2
      simp only [lowerCoverage, Rat.cast_sub]
      linarith
    have lowerPositive : (0 : ℝ) <
        (lowerCoverage candidateAcceptance (fun i => sample i w) radius chosen : ℝ) := by
      exact_mod_cast lowerPositiveQ
    have coveragePositive := lt_of_lt_of_le lowerPositive coverageBound
    have numeratorNonnegative : 0 ≤ ∫ z, (numeratorLoss (candidateLoss loss) candidateAcceptance chosen z : ℝ) ∂P := by
      apply integral_nonneg
      intro z
      by_cases h : candidateAcceptance chosen z = true
      · simpa [numeratorLoss, h] using (pairRange chosen member z).1
      · simp [numeratorLoss, h]
    have upperNonnegative := le_trans numeratorNonnegative numeratorBound
    have ratio : (∫ z, (numeratorLoss (candidateLoss loss) candidateAcceptance chosen z : ℝ) ∂P) /
        (∫ z, (coverageLoss candidateAcceptance chosen z : ℝ) ∂P) ≤
        (upperNumerator (candidateLoss loss) candidateAcceptance (fun i => sample i w) radius chosen : ℝ) /
          (lowerCoverage candidateAcceptance (fun i => sample i w) radius chosen : ℝ) := by
      apply (div_le_div_iff₀ coveragePositive lowerPositive).mpr
      nlinarith
    have gate : (upperNumerator (candidateLoss loss) candidateAcceptance (fun i => sample i w) radius chosen : ℝ) /
        (lowerCoverage candidateAcceptance (fun i => sample i w) radius chosen : ℝ) ≤ (target : ℝ) := by
      exact_mod_cast gateQ
    exact ⟨coveragePositive, le_trans ratio gate⟩

end JurisLean.Candidates.SampleCalibrationConsumer20261027
