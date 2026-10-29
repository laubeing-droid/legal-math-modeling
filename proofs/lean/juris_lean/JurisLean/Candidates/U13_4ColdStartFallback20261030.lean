import JurisLean.Candidates.Final20261021.RSI
import JurisLean.Candidates.LearningBoundary20261027
import JurisLean.Candidates.SampleCalibrationConsumer20261027
import JurisLean.Candidates.PolicyEvaluation20261027

open scoped BigOperators

namespace JurisLean.Candidates.U13_4ColdStartFallback20261030

open MeasureTheory ProbabilityTheory
open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.LearningConsumer20261027
open JurisLean.Candidates.LearningFiniteClass20261027
open JurisLean.Candidates.SampleCalibrationConsumer20261027
open JurisLean.Candidates.PolicyEvaluation20261027

/-!
CI_NOT_RUN. Frozen U13.4, original question 13.3 only.
Source references and the supplied applicability judgment are retained evidence
inputs, not proofs of physical applicability, iid sampling, or population risk.
The statistical conclusions below keep the existing theorems' actual sample/law
premises. This file neither loads checkpoint bytes nor extends the whole Pipeline.
-/

structure Query (m : Nat) where
  request : RSI.PredictionRequest
  protocol : LearningProtocol
  point : Fin m
  asOf : Instant
  riskLimit : ℚ

/-- Source-specific inputs retain the declared query, target population and
independent applicability basis. Population sources need not have this person's id. -/
structure ScopeBasis (m : Nat) where
  context : RSI.PredictionRequest
  point : Fin m
  population : Nat
  source : SourceRef
  applicability : Applicable
  applicabilitySource : SourceRef

def basisMatches {m : Nat} (q : Query m) (b : ScopeBasis m) : Bool :=
  decide (b.context.task = q.request.task ∧ b.context.target = q.request.target ∧
    b.context.feature = q.request.feature ∧ b.context.ruleVersion = q.request.ruleVersion ∧
    b.context.mechanism = q.request.mechanism ∧ b.context.scope = q.request.scope ∧
    b.point = q.point ∧ b.population = q.protocol.population ∧ b.applicability = .yes)

def queryCompatible {m : Nat} (q : Query m) : Bool :=
  decide (q.protocol.fit.task = q.request.task ∧ q.protocol.fit.target = q.request.target ∧
    q.protocol.fit.featureVersion = q.request.feature ∧
    q.protocol.effectiveDomain = q.request.scope)

/-- U13.4 blocker: a population/personal model must use actual calibration inputs,
not an approved flag or an uninspected file. Sampling/measurement references do
not replace the mathematical sampling and measurement premises below. -/
structure ModelSource (m : Nat) where
  basis : ScopeBasis m
  samplingSource : SourceRef
  measurementSource : SourceRef
  sampleProtocol : LearningProtocol
  fitted : FittedTable
  n : Nat
  rows : Fin n → SampleObservation m Bool
  loss : ℚ → Bool → ℚ
  firstCutoff : ℚ
  otherCutoffs : List ℚ
  radius : ℚ
  radiusExponent : Nat
  snapshot : Nat
  calibrationProtocol : Nat

/-- The declared Bernoulli predictive probability is an additional model
condition. Its source and conditions survive the service result. -/
structure PriorSource (m : Nat) where
  basis : ScopeBasis m
  probability : ℚ
  conditionSources : List SourceRef

/-- An explicitly declared batch is checked as a whole. Passing these checks
never proves that selection preserved iid sampling or target representativeness. -/
structure DataSource (m : Nat) where
  basis : ScopeBasis m
  samplingSource : SourceRef
  measurementSource : SourceRef
  n : Nat
  rows : Fin n → Behavior.MeasurementLog
  labels : Fin n → Bool
  radius : ℚ
  radiusExponent : Nat

inductive Prediction (m : Nat) where
  | audited (personal : Option RSI.Checkpoint) (input : ModelSource m)
      (calibrated : SampleCalibration) (score : TaskScore)
  | declaredPrior (input : PriorSource m)
  | sampled (input : DataSource m) (value : ℚ)

def predictionValue {m : Nat} : Prediction m → ℚ
  | .audited _ _ _ score => score.value
  | .declaredPrior input => input.probability
  | .sampled _ value => value

structure Description (m : Nat) where
  input : DataSource m
  frequency : ℚ

structure Output (m : Nat) where
  query : Query m
  normative : Result ℚ
  description : Result (Description m)
  prediction : Result (Prediction m)

def auditProduction {m : Nat} (q : Query m) (a : ModelSource m) : Result SampleCalibration :=
  produceCalibration a.sampleProtocol a.fitted a.loss
    (a.firstCutoff :: a.otherCutoffs) a.rows a.radius q.riskLimit
    a.snapshot a.calibrationProtocol a.radiusExponent

def auditedReady {m : Nat} (q : Query m) (personal : Option RSI.Checkpoint)
    (a : ModelSource m) : Prop :=
  basisMatches q a.basis = true ∧ queryCompatible q = true ∧
    match personal with
    | none => True
    | some c => RSI.checkpointMatches q.request c = true ∧
        c.version = q.protocol.fit.modelVersion

def auditedPrediction {m : Nat} (q : Query m) (personal : Option RSI.Checkpoint)
    (a : ModelSource m) : Result (Prediction m) := by
  letI : Decidable (auditedReady q personal a) := by
    unfold auditedReady
    cases personal <;> infer_instance
  exact if auditedReady q personal a then
    match auditProduction q a with
    | .known calibrated =>
        match predictCalibrated q.protocol calibrated q.point q.riskLimit
            (decide (a.basis.applicability = .yes)) with
        | .known score =>
            letI : Decidable
                (match personal with | none => True | some c => c.prediction = score.value) := by
              cases personal <;> infer_instance
            if 0 ≤ score.value ∧ score.value ≤ 1 ∧
                (match personal with | none => True | some c => c.prediction = score.value) then
              .known (.audited personal a calibrated score)
            else .unknown .unsupported
        | _ => .unknown .missingEvidence
    | _ => .unknown .missingEvidence
  else .unknown .scopeMismatch

def priorPrediction {m : Nat} (q : Query m) (p : PriorSource m) : Result (Prediction m) :=
  if basisMatches q p.basis = true ∧ queryCompatible q = true ∧
      0 ≤ p.probability ∧ p.probability ≤ 1 then .known (.declaredPrior p)
  else .unknown .missingEvidence

def dataReady {m : Nat} (q : Query m) (d : DataSource m) : Bool :=
  basisMatches q d.basis && queryCompatible q && decide (∀ i : Fin d.n,
    (d.rows i).targetVersion = q.request.target ∧
    (d.rows i).mechanismVersion = q.request.mechanism ∧
    (d.rows i).windowEnd.ticks ≤ q.asOf.ticks ∧
    (d.rows i).observedAt.ticks ≤ q.asOf.ticks ∧
    Behavior.proposed_measurement q.request.target (d.rows i) = .known (d.labels i))

def dataValues {m : Nat} (d : DataSource m) : List ℚ :=
  List.ofFn (fun i : Fin d.n => Behavior.indicator (d.labels i))

def descriptionService {m : Nat} (q : Query m) (d : DataSource m) : Result (Description m) :=
  if dataReady q d = true then
    match RSI.conditionalEstimate ((dataValues d).map (fun _ => (1 : ℚ))) (dataValues d) with
    | .known value => .known ⟨d, value⟩
    | _ => .unknown .missingEvidence
  else .unknown .scopeMismatch

def samplePrediction {m : Nat} (q : Query m) (d : DataSource m) : Result (Prediction m) :=
  if radiusVerified d.n 1 q.protocol.failureBudget d.radius d.radiusExponent = true then
    match descriptionService q d with
    | .known described => .known (.sampled d described.frequency)
    | _ => .unknown .missingEvidence
  else .unknown .missingEvidence

private def attemptOption {A B : Type} (f : A → Result B) : Option A → Result B
  | none => .unknown .missingEvidence
  | some a => f a

private def firstKnown {A : Type} : List (Result A) → Result A
  | [] => .unknown .missingEvidence
  | .known a :: _ => .known a
  | _ :: rest => firstKnown rest

def sourceAttempts {m : Nat} (q : Query m)
    (personal : Option (RSI.Checkpoint × ModelSource m))
    (population : Option (ModelSource m)) (prior : Option (PriorSource m))
    (data : Option (DataSource m)) : List (Result (Prediction m)) :=
  [attemptOption (fun p => auditedPrediction q (some p.1) p.2) personal,
    attemptOption (auditedPrediction q none) population,
    attemptOption (priorPrediction q) prior,
    attemptOption (samplePrediction q) data]

def forecastService {m : Nat} (q : Query m)
    (personal : Option (RSI.Checkpoint × ModelSource m))
    (population : Option (ModelSource m)) (prior : Option (PriorSource m))
    (data : Option (DataSource m)) : Result (Prediction m) :=
  firstKnown (sourceAttempts q personal population prior data)

def normativeService {X : Type} (G : X → Option ℚ) (x : X) : Result ℚ :=
  match G x with | some value => .known value | none => .unknown .notApplicable

def service {X : Type} {m : Nat} (G : X → Option ℚ) (x : X) (q : Query m)
    (personal : Option (RSI.Checkpoint × ModelSource m))
    (population : Option (ModelSource m)) (prior : Option (PriorSource m))
    (data : Option (DataSource m)) : Output m :=
  ⟨q, normativeService G x, attemptOption (descriptionService q) data,
    forecastService q personal population prior data⟩

/-- Blocker: successful audited forecasts must read the executed producer and
consumer, with the same actual input objects. No population-risk premise is a
constructor field or inferred from a source reference. -/
theorem audited_success_reads_actual_inputs {m : Nat} (q : Query m)
    (personal : Option RSI.Checkpoint) (a : ModelSource m) (out : Prediction m)
    (accepted : auditedPrediction q personal a = .known out) :
    ∃ calibrated score, auditedReady q personal a ∧
      auditProduction q a = .known calibrated ∧
      predictCalibrated q.protocol calibrated q.point q.riskLimit
        (decide (a.basis.applicability = .yes)) = .known score ∧
      out = .audited personal a calibrated score := by
  classical
  unfold auditedPrediction at accepted
  dsimp only at accepted
  split at accepted
  · rename_i ready
    cases produced : auditProduction q a with
    | known calibrated =>
        rw [produced] at accepted
        dsimp only at accepted
        cases predicted : predictCalibrated q.protocol calibrated q.point q.riskLimit
            (decide (a.basis.applicability = .yes)) with
        | known score =>
            rw [predicted] at accepted
            dsimp only at accepted
            split at accepted
            · exact ⟨calibrated, score, ready, rfl, predicted,
                (Result.known.inj accepted).symm⟩
            · cases accepted
        | unknown e => simp [predicted] at accepted
        | rejected e => simp [predicted] at accepted
        | conflict a b => simp [predicted] at accepted
    | unknown e => simp [produced] at accepted
    | rejected e => simp [produced] at accepted
    | conflict a b => simp [produced] at accepted
  · cases accepted

theorem prior_success_is_declared {m : Nat} (q : Query m) (p : PriorSource m)
    (out : Prediction m) (accepted : priorPrediction q p = .known out) :
    (basisMatches q p.basis = true ∧ queryCompatible q = true ∧
      0 ≤ p.probability ∧ p.probability ≤ 1) ∧ out = .declaredPrior p := by
  unfold priorPrediction at accepted
  split at accepted
  · rename_i ready
    exact ⟨ready, (Result.known.inj accepted).symm⟩
  · cases accepted

private theorem equal_weight_estimate (ys : List ℚ) (positive : 0 < (ys.length : ℚ)) :
    RSI.conditionalEstimate (ys.map (fun _ => (1 : ℚ))) ys =
      .known (ys.sum / (ys.length : ℚ)) := by
  have zipped : List.zipWith (fun x y : ℚ => x * y)
      (ys.map (fun _ => (1 : ℚ))) ys = ys := by
    clear positive
    induction ys with
    | nil => rfl
    | cons y ys ih =>
        change (1 : ℚ) * y :: List.zipWith (fun x y : ℚ => x * y)
          (ys.map (fun _ => (1 : ℚ))) ys = y :: ys
        rw [one_mul, ih]
  have total : (ys.map (fun _ => (1 : ℚ))).sum = (ys.length : ℚ) := by
    clear positive
    induction ys with
    | nil => simp
    | cons y ys ih =>
        change (1 : ℚ) + (ys.map (fun _ => (1 : ℚ))).sum = ((ys.length + 1 : ℕ) : ℚ)
        rw [ih, Nat.cast_add, Nat.cast_one]
        ring
  have negatives : (ys.map (fun _ => (1 : ℚ))).any (fun w => decide (w < 0)) = false := by
    clear positive
    induction ys with
    | nil => rfl
    | cons y ys ih =>
        change (decide ((1 : ℚ) < 0) ||
          (ys.map (fun _ => (1 : ℚ))).any (fun w => decide (w < 0))) = false
        rw [ih]
        norm_num
  have valid : ¬ ((ys.map (fun _ => (1 : ℚ))).length ≠ ys.length ∨
      (ys.map (fun _ => (1 : ℚ))).any (fun w => decide (w < 0)) = true) := by
    rw [List.length_map, negatives]
    simp
  unfold RSI.conditionalEstimate
  rw [if_neg valid, total, if_pos positive, zipped]

private theorem data_estimate_is_actual_mean {m : Nat} (d : DataSource m) (hn : 0 < d.n) :
    RSI.conditionalEstimate ((dataValues d).map (fun _ => (1 : ℚ))) (dataValues d) =
      .known ((∑ i : Fin d.n, Behavior.indicator (d.labels i)) / (d.n : ℚ)) := by
  have positive : (0 : ℚ) < ((dataValues d).length : ℚ) := by
    have hnQ : (0 : ℚ) < d.n := by exact_mod_cast hn
    simpa only [dataValues, List.length_ofFn] using hnQ
  simpa only [dataValues, List.length_ofFn, List.sum_ofFn] using
    equal_weight_estimate (dataValues d) positive

theorem description_success_reads_measurements {m : Nat} (q : Query m)
    (d : DataSource m) (out : Description m)
    (accepted : descriptionService q d = .known out) :
    dataReady q d = true ∧ out.input = d ∧
      RSI.conditionalEstimate ((dataValues d).map (fun _ => (1 : ℚ))) (dataValues d) =
        .known out.frequency := by
  unfold descriptionService at accepted
  split at accepted
  · rename_i ready
    cases estimated : RSI.conditionalEstimate
        ((dataValues d).map (fun _ => (1 : ℚ))) (dataValues d) with
    | known value =>
        rw [estimated] at accepted
        dsimp only at accepted
        have same := Result.known.inj accepted
        subst out
        exact ⟨ready, rfl, rfl⟩
    | unknown e =>
        rw [estimated] at accepted
        dsimp only at accepted
        cases accepted
    | rejected e =>
        rw [estimated] at accepted
        dsimp only at accepted
        cases accepted
    | conflict a b =>
        rw [estimated] at accepted
        dsimp only at accepted
        cases accepted
  · cases accepted

theorem sample_success_reads_actual_mean {m : Nat} (q : Query m)
    (d : DataSource m) (out : Prediction m)
    (accepted : samplePrediction q d = .known out) :
    ∃ value, out = .sampled d value ∧ dataReady q d = true ∧
      radiusVerified d.n 1 q.protocol.failureBudget d.radius d.radiusExponent = true ∧
      value = (∑ i : Fin d.n, Behavior.indicator (d.labels i)) / (d.n : ℚ) := by
  unfold samplePrediction at accepted
  split at accepted
  · rename_i verified
    cases described : descriptionService q d with
    | known description =>
        rw [described] at accepted
        obtain ⟨ready, _, estimated⟩ :=
          description_success_reads_measurements q d description described
        have checks := verified
        simp only [radiusVerified, decide_eq_true_eq] at checks
        rw [data_estimate_is_actual_mean d checks.1] at estimated
        exact ⟨description.frequency, (Result.known.inj accepted).symm,
          ready, verified, (Result.known.inj estimated).symm⟩
    | unknown e => simp [described] at accepted
    | rejected e => simp [described] at accepted
    | conflict a b => simp [described] at accepted
  · cases accepted

private theorem firstKnown_success_mem {A : Type} (xs : List (Result A)) (out : A)
    (accepted : firstKnown xs = .known out) : Result.known out ∈ xs := by
  revert accepted
  induction xs with
  | nil => intro accepted; cases accepted
  | cons head rest ih =>
      intro accepted
      cases head with
      | known value =>
          have same : value = out := Result.known.inj accepted
          subst out
          simp
      | unknown e => exact List.mem_cons_of_mem _ (ih accepted)
      | rejected e => exact List.mem_cons_of_mem _ (ih accepted)
      | conflict a b => exact List.mem_cons_of_mem _ (ih accepted)

private theorem firstKnown_no_success {A : Type} (xs : List (Result A))
    (absent : ∀ out, Result.known out ∉ xs) : firstKnown xs = .unknown .missingEvidence := by
  revert absent
  induction xs with
  | nil => intro _; rfl
  | cons head rest ih =>
      intro absent
      have tail : ∀ out, Result.known out ∉ rest := by
        intro out member
        exact absent out (List.mem_cons_of_mem _ member)
      cases head with
      | known value => exact False.elim (absent value (by simp))
      | unknown e => exact ih tail
      | rejected e => exact ih tail
      | conflict a b => exact ih tail

theorem selected_prediction_has_executed_source {m : Nat} (q : Query m)
    (personal : Option (RSI.Checkpoint × ModelSource m))
    (population : Option (ModelSource m)) (prior : Option (PriorSource m))
    (data : Option (DataSource m)) (out : Prediction m)
    (accepted : forecastService q personal population prior data = .known out) :
    Result.known out ∈ sourceAttempts q personal population prior data :=
  firstKnown_success_mem _ out accepted

theorem missing_personal_preserves_fallbacks {m : Nat} (q : Query m)
    (laterPrior : Option (PriorSource m)) (laterData : Option (DataSource m)) :
    (∀ a out, auditedPrediction q none a = .known out →
      forecastService q none (some a) laterPrior laterData = .known out) ∧
    (∀ p out, priorPrediction q p = .known out →
      forecastService q none none (some p) laterData = .known out) ∧
    (∀ d out, samplePrediction q d = .known out →
      forecastService q none none none (some d) = .known out) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a out accepted
    simp [forecastService, sourceAttempts, attemptOption, firstKnown, accepted]
  · intro p out accepted
    simp [forecastService, sourceAttempts, attemptOption, firstKnown, accepted]
  · intro d out accepted
    simp [forecastService, sourceAttempts, attemptOption, firstKnown, accepted]

theorem no_valid_source_unknown {m : Nat} (q : Query m)
    (personal : Option (RSI.Checkpoint × ModelSource m))
    (population : Option (ModelSource m)) (prior : Option (PriorSource m))
    (data : Option (DataSource m))
    (absent : ∀ out, Result.known out ∉ sourceAttempts q personal population prior data) :
    forecastService q personal population prior data = .unknown .missingEvidence :=
  firstKnown_no_success _ absent

theorem normative_query_uses_only_G {X : Type} {m : Nat}
    (G : X → Option ℚ) (x : X) (q : Query m)
    (personal : Option (RSI.Checkpoint × ModelSource m))
    (population : Option (ModelSource m)) (prior : Option (PriorSource m))
    (data : Option (DataSource m)) :
    (service G x q personal population prior data).normative = normativeService G x := rfl

theorem audited_prediction_risk_under_existing_conditions
    {Ω : Type*} [MeasurableSpace Ω] {m : Nat}
    [MeasurableSpace (Fin m × Bool)]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Measure (Fin m × Bool)) [IsProbabilityMeasure P]
    (q : Query m) (personal : Option RSI.Checkpoint) (a : ModelSource m)
    (hn : 0 < a.n) (sample : Fin a.n → Ω → Fin m × Bool)
    (events : Fin a.n → Ω → EventId)
    (sampleMeasurable : ∀ i, Measurable (sample i))
    (independent : iIndepFun sample μ) (law : ∀ i, IdentDistrib (sample i) id μ P)
    (numeratorMeasurable : ∀ h ∈ a.firstCutoff :: a.otherCutoffs,
      Measurable (fun z : Fin m × Bool =>
        (SelectiveCalibration20261027.numeratorLoss
          (fun _ z => tableLoss a.loss a.fitted.table z)
          (tableAcceptance a.fitted) h z : ℝ)))
    (coverageMeasurable : ∀ h ∈ a.firstCutoff :: a.otherCutoffs,
      Measurable (fun z : Fin m × Bool =>
        (SelectiveCalibration20261027.coverageLoss (tableAcceptance a.fitted) h z : ℝ)))
    (lossRange : ∀ z : Fin m × Bool,
      (tableLoss a.loss a.fitted.table z : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (hδ : 0 < (a.fitted.protocol.failureBudget : ℝ))
    (hδ1 : (a.fitted.protocol.failureBudget : ℝ) < 1)
    (conservative : finiteRadius a.n (2 * (a.firstCutoff :: a.otherCutoffs).toFinset.card)
      (a.fitted.protocol.failureBudget : ℝ) ≤ (a.radius : ℝ)) :
    ∃ confidence : Set Ω, MeasurableSet confidence ∧
      1 - (a.fitted.protocol.failureBudget : ℝ) ≤ μ.real confidence ∧
      ∀ w ∈ confidence, ∀ out,
        auditedPrediction q personal
          { a with rows := fun i => ⟨events i w, (sample i w).1, (sample i w).2⟩ } = .known out →
        ∃ calibrated score,
          out = .audited personal
            { a with rows := fun i => ⟨events i w, (sample i w).1, (sample i w).2⟩ }
            calibrated score ∧
          0 < ∫ z, (SelectiveCalibration20261027.coverageLoss
            (tableAcceptance calibrated.fitted) calibrated.cutoff z : ℝ) ∂P ∧
          (∫ z, (SelectiveCalibration20261027.numeratorLoss
            (fun _ z => tableLoss a.loss calibrated.fitted.table z)
            (tableAcceptance calibrated.fitted) calibrated.cutoff z : ℝ) ∂P) /
            (∫ z, (SelectiveCalibration20261027.coverageLoss
              (tableAcceptance calibrated.fitted) calibrated.cutoff z : ℝ) ∂P) ≤ (q.riskLimit : ℝ) := by
  obtain ⟨confidence, measurable, probability, safe⟩ :=
    actual_certificate_consumes_population_risk_bound μ P hn a.sampleProtocol a.fitted
      a.firstCutoff a.otherCutoffs sample events sampleMeasurable independent law
      a.loss numeratorMeasurable coverageMeasurable lossRange hδ hδ1
      a.radius q.riskLimit conservative a.snapshot a.calibrationProtocol a.radiusExponent
  refine ⟨confidence, measurable, probability, ?_⟩
  intro w hw out accepted
  obtain ⟨calibrated, score, _, produced, _, same⟩ :=
    audited_success_reads_actual_inputs q personal _ out accepted
  refine ⟨calibrated, score, same, ?_⟩
  apply safe w hw calibrated
  simpa only [auditProduction] using produced

theorem sample_prediction_error_under_existing_conditions
    {Ω : Type*} [MeasurableSpace Ω] {m : Nat}
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Measure Bool) [IsProbabilityMeasure P]
    (q : Query m) (d : DataSource m) (hn : 0 < d.n)
    (sample : Fin d.n → Ω → Bool)
    (rows : Fin d.n → Ω → Behavior.MeasurementLog)
    (sampleMeasurable : ∀ i, Measurable (sample i))
    (independent : iIndepFun sample μ) (law : ∀ i, IdentDistrib (sample i) id μ P)
    (hδ : 0 < (q.protocol.failureBudget : ℝ))
    (hδ1 : (q.protocol.failureBudget : ℝ) < 1) :
    ∃ confidence : Set Ω, MeasurableSet confidence ∧
      1 - (q.protocol.failureBudget : ℝ) ≤ μ.real confidence ∧
      ∀ w ∈ confidence, ∀ out,
        samplePrediction q { d with rows := (fun i => rows i w),
          labels := (fun i => sample i w) } = .known out →
        ∃ value, out = .sampled
            { d with rows := (fun i => rows i w), labels := (fun i => sample i w) } value ∧
          |(value : ℝ) - ∫ y, (Behavior.indicator y : ℝ) ∂P| ≤ (d.radius : ℝ) := by
  let mean : Ω → ℝ := fun w =>
    empiricalMean (fun i w' => (Behavior.indicator (sample i w') : ℝ)) w
  let target : ℝ := ∫ y, (Behavior.indicator y : ℝ) ∂P
  let confidence : Set Ω := {w | |mean w - target| ≤
    finiteRadius d.n 2 (q.protocol.failureBudget : ℝ)}
  have each (i : Fin d.n) :
      Measurable (fun w => (Behavior.indicator (sample i w) : ℝ)) :=
    (measurable_of_finite (fun y : Bool => (Behavior.indicator y : ℝ))).comp (sampleMeasurable i)
  have meanMeasurable : Measurable mean := by
    unfold mean empiricalMean
    fun_prop
  have confidenceMeasurable : MeasurableSet confidence :=
    measurableSet_le ((meanMeasurable.sub measurable_const).abs) measurable_const
  have uniform := bounded_policy_score_uniform μ P hn (Finset.univ : Finset Bool)
    (by simp) sample sampleMeasurable independent law
    (fun (_ : Bool) y => (Behavior.indicator y : ℝ))
    (fun _ _ => measurable_of_finite _) 1 (by norm_num)
    (by intro _ _ y; cases y <;> norm_num [Behavior.indicator])
    (q.protocol.failureBudget : ℝ) hδ hδ1
  have probability : 1 - (q.protocol.failureBudget : ℝ) ≤ μ.real confidence := by
    norm_num only
    apply le_trans uniform
    apply measureReal_mono (μ := μ) (h₂ := measure_ne_top μ _)
    intro w hw
    have one := hw false (by simp)
    simpa [confidence, mean, target] using one
  refine ⟨confidence, confidenceMeasurable, probability, ?_⟩
  intro w hw out accepted
  obtain ⟨value, same, _, verified, actualMean⟩ :=
    sample_success_reads_actual_mean q _ out accepted
  have radiusBound := radius_verification_sound d.n 1 q.protocol.failureBudget
    d.radius d.radiusExponent verified
  have castMean : (value : ℝ) = mean w := by
    simpa [mean, empiricalMean] using congrArg (fun x : ℚ => (x : ℝ)) actualMean
  refine ⟨value, same, ?_⟩
  rw [castMean]
  exact le_trans hw radiusBound

theorem original_fee_service_example {m : Nat} (q : Query m) :
    (service (fun principal : ℚ =>
      if 0 ≤ principal then some (principal + 20) else none)
      100 q none none none none).normative = .known 120 ∧
    (service (fun principal : ℚ =>
      if 0 ≤ principal then some (principal + 20) else none)
      100 q none none none none).prediction = .unknown .missingEvidence := by
  constructor
  · norm_num [service, normativeService]
  · rfl

theorem original_unknown_win_rate_service_example {m : Nat} (q : Query m) :
    (service (fun _ : Unit => (none : Option ℚ)) () q none none none none).prediction =
      .unknown .missingEvidence := rfl

end JurisLean.Candidates.U13_4ColdStartFallback20261030