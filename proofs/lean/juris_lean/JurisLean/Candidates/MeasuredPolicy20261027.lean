import JurisLean.Candidates.BusinessMeasurement20261027
import JurisLean.Candidates.PolicyEvaluation20261027
import JurisLean.Candidates.AdaptiveRoundLedger20261027

/-!
Original 04 edges 11--13, S12's independently admissible policy update, E11/E12.
The empirical score reads the actual measured label, pre-treatment feature and
recorded assignment. Finite support and weight bounds are checked over the
whole declared class, including the parent, rather than just observed actions.
The safe selector consumes actual values and a verified simultaneous radius.
Its conditional population guarantee is proved on a measurable iid event.

External design, source, completeness, causal identification and legal registry
claims retain their explicit interpretations. A successful field comparison
does not prove those claims. The feedback consumer writes the actual external
label to the existing event journal and then invokes the actual next learner;
it does not reinterpret a numeric policy estimate as a checkpoint weight.
-/

namespace JurisLean.Candidates.MeasuredPolicy20261027

open MeasureTheory ProbabilityTheory
open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.BusinessMeasurement20261027
open JurisLean.Candidates.LearningConsumer20261027
open JurisLean.Candidates.LearningERM20261027
open JurisLean.Candidates.LearningFiniteClass20261027
open JurisLean.Candidates.SampleCalibrationConsumer20261027
open JurisLean.Candidates.EventFeedbackConsumer20261027
open JurisLean.Candidates.ProtectedFeedback20261027
open JurisLean.Candidates.AdaptiveRoundLedger20261027

inductive ConstructFamily where
  | procedure | filing | performance | reviewedDefect
  deriving DecidableEq, Repr

def constructFamily : BehaviorConstruct → ConstructFamily
  | .procedureChoice _ _ => .procedure
  | .timelyFiling _ => .filing
  | .timelyPerformance _ _ _ _ => .performance
  | .reviewedDefect => .reviewedDefect

structure PolicyEnvironment where
  dataScope : DataScope
  jurisdiction : String
  interpretation : Nat
  treatmentVersion : Nat
  responseVersion : Nat
  loggingVersion : Nat
  windowLength : Int
  timezone : String
  clockVersion : Nat
  construct : ConstructFamily
  deriving DecidableEq, Repr

structure TreatmentRecord (m : Nat) where
  environment : PolicyEnvironment
  dictionary : MeasurementDictionary
  feature : Fin m
  baselineAt : Instant
  baselineSource : SourceRef
  action : Bool
  actionAt : Instant
  outcomeSource : SourceRef
  evidence : SourceRef
  deriving DecidableEq, Repr

structure PolicyObservation (m : Nat) where
  measured : BehaviorMeasurement
  treatment : TreatmentRecord m
  deriving DecidableEq

def treatmentMatches {m : Nat} (env : PolicyEnvironment) (measured : BehaviorMeasurement)
    (row : TreatmentRecord m) (catalog : List (TreatmentRecord m)) : Bool :=
  let d := measured.dictionary
  decide (row ∈ catalog ∧ row.environment = env ∧ row.dictionary = d ∧
    measured.actualPost.gamma = d.context ∧
    d.context.jurisdiction = env.jurisdiction ∧ d.context.interpretation = env.interpretation ∧
    d.context.normVersion = env.dataScope.ruleVersion ∧
    d.context.mechanismVersion = env.dataScope.mechanismVersion ∧
    d.targetVersion = env.dataScope.target ∧
    d.windowEnd.ticks - d.windowStart.ticks = env.windowLength ∧
    d.timezone = env.timezone ∧ d.clockVersion = env.clockVersion ∧
    constructFamily d.construct = env.construct ∧
    row.baselineAt.ticks < row.actionAt.ticks ∧ row.actionAt.ticks ≤ d.windowStart.ticks)

def consumeMeasurement {m : Nat} (env : PolicyEnvironment) (measurement : MeasurementResult)
    (treatment : TreatmentRecord m) (catalog : List (TreatmentRecord m)) : Result (PolicyObservation m) :=
  match measurement with
  | .unknown _ => .unknown .missingEvidence
  | .measured measured =>
      if treatmentMatches env measured treatment catalog then .known ⟨measured, treatment⟩
      else .unknown .scopeMismatch

structure MeasuredPolicyRun (m : Nat) where
  business : MeasuredTrajectory
  observation : Result (PolicyObservation m)
  deriving DecidableEq

def runMeasurementPolicy {m : Nat} (grants : List Authorization.Grant) (initial : Ledger.Handle)
    (steps : List DecisionTrajectoryConsumer20261027.Instruction) (dictionary : MeasurementDictionary)
    (now : Instant) (sourceCatalog : List ObservationAttestation) (closures : List WindowClosure)
    (rows : List MeasurementRow) (env : PolicyEnvironment) (treatment : TreatmentRecord m)
    (treatmentCatalog : List (TreatmentRecord m)) : MeasuredPolicyRun m :=
  let actual := measureTrajectory grants initial steps dictionary now sourceCatalog closures rows
  ⟨actual, consumeMeasurement env actual.measurement treatment treatmentCatalog⟩

theorem measured_policy_row_preserves_actual_output {m : Nat} (env : PolicyEnvironment)
    (measurement : MeasurementResult) (treatment : TreatmentRecord m)
    (catalog : List (TreatmentRecord m)) (out : PolicyObservation m)
    (accepted : consumeMeasurement env measurement treatment catalog = .known out) :
    measurement = .measured out.measured ∧ out.treatment = treatment ∧
    treatmentMatches env out.measured treatment catalog = true := by
  cases measurement with
  | unknown reason => simp [consumeMeasurement] at accepted
  | measured value =>
      simp only [consumeMeasurement] at accepted
      split at accepted
      · rename_i matching
        cases accepted
        exact ⟨rfl, rfl, matching⟩
      · simp at accepted

theorem measured_policy_pipeline_reads_actual_measurement {m : Nat}
    (grants : List Authorization.Grant) (initial : Ledger.Handle)
    (steps : List DecisionTrajectoryConsumer20261027.Instruction) (dictionary : MeasurementDictionary)
    (now : Instant) (sources : List ObservationAttestation) (closures : List WindowClosure)
    (rows : List MeasurementRow) (env : PolicyEnvironment) (treatment : TreatmentRecord m)
    (catalog : List (TreatmentRecord m)) (out : PolicyObservation m)
    (accepted : (runMeasurementPolicy grants initial steps dictionary now sources closures rows
      env treatment catalog).observation = .known out) :
    (measureTrajectory grants initial steps dictionary now sources closures rows).measurement =
      .measured out.measured :=
  (measured_policy_row_preserves_actual_output env _ treatment catalog out accepted).1

abbrev PolicyDatum (m : Nat) := Fin m × Bool × Bool

def observationDatum {m : Nat} (row : PolicyObservation m) : PolicyDatum m :=
  (row.treatment.feature, row.treatment.action, row.measured.label)

def policyProbability {m : Nat} (table : List ℚ) (x : Fin m) (action : Bool) : ℚ :=
  if action then table.getD x.val 0 else 1 - table.getD x.val 0

def policyScore {m : Nat} (logging table : List ℚ) (z : PolicyDatum m) : ℚ :=
  policyProbability table z.1 z.2.1 / policyProbability logging z.1 z.2.1 * Behavior.indicator z.2.2

structure PolicyPlan where
  environment : PolicyEnvironment
  logging : List ℚ
  family : List (List ℚ)
  parent : List ℚ
  weightBound : ℚ
  delta : ℚ
  radius : ℚ
  exponent : Nat
  tolerance : ℚ
  frozenAt : Instant
  deriving DecidableEq, Repr

def policyClassSupported (m : Nat) (plan : PolicyPlan) : Bool :=
  decide (0 < plan.weightBound ∧ plan.logging.length = m ∧
    (∀ x : Fin m, 0 ≤ plan.logging.getD x.val 0 ∧ plan.logging.getD x.val 0 ≤ 1) ∧
    ∀ table ∈ plan.family, table.length = m ∧ ∀ (x : Fin m) (a : Bool),
      0 ≤ policyProbability table x a ∧ policyProbability table x a ≤ 1 ∧
      (policyProbability table x a ≠ 0 → policyProbability plan.logging x a ≠ 0) ∧
      0 ≤ policyProbability table x a / policyProbability plan.logging x a ∧
      policyProbability table x a / policyProbability plan.logging x a ≤ plan.weightBound)

def policyNumericsValid (m n : Nat) (plan : PolicyPlan) : Bool :=
  (policyClassSupported m plan && decide (plan.parent ∈ plan.family ∧ 0 ≤ plan.tolerance)) &&
  radiusVerified n plan.family.toFinset.card plan.delta (plan.radius / plan.weightBound) plan.exponent

-- Order is the declared preference order, not an implicit optimality claim.
-- Every returned policy satisfies the same conservative non-degradation test.
def choosePolicy {m n : Nat} (plan : PolicyPlan) (data : Fin n → PolicyDatum m)
    (allowed : List (List ℚ)) : Option (List ℚ) :=
  if policyNumericsValid m n plan then
    plan.family.find? fun candidate => decide (candidate ∈ allowed ∧
      empiricalScore (policyScore plan.logging) data plan.parent + plan.radius - plan.tolerance ≤
        empiricalScore (policyScore plan.logging) data candidate - plan.radius)
  else none

theorem selected_policy_reads_numeric_bounds_and_permission {m n : Nat}
    (plan : PolicyPlan) (data : Fin n → PolicyDatum m) (allowed : List (List ℚ))
    (chosen : List ℚ) (selected : choosePolicy plan data allowed = some chosen) :
    policyNumericsValid m n plan = true ∧ plan.parent ∈ plan.family ∧
    chosen ∈ plan.family ∧ chosen ∈ allowed ∧
    empiricalScore (policyScore plan.logging) data plan.parent + plan.radius - plan.tolerance ≤
      empiricalScore (policyScore plan.logging) data chosen - plan.radius := by
  unfold choosePolicy at selected
  split at selected
  · rename_i verified
    have checks := verified
    simp only [policyNumericsValid, Bool.and_eq_true, decide_eq_true_eq] at checks
    have matched := List.find?_some selected
    have eligible := of_decide_eq_true matched
    exact ⟨verified, checks.1.2.1, List.mem_of_find?_eq_some selected, eligible.1, eligible.2⟩
  · simp at selected

theorem supported_scores_are_bounded {m : Nat} (plan : PolicyPlan)
    (supported : policyClassSupported m plan = true) (table : List ℚ)
    (member : table ∈ plan.family) (z : PolicyDatum m) :
    (policyScore plan.logging table z : ℝ) ∈ Set.Icc (0 : ℝ) plan.weightBound := by
  have checks := of_decide_eq_true supported
  have weight := (checks.2.2.2 table member).2 z.1 z.2.1
  have bound : (0 : ℚ) ≤ policyScore plan.logging table z ∧
      policyScore plan.logging table z ≤ plan.weightBound := by
    cases truth : z.2.2 <;> simp [policyScore, Behavior.indicator, truth]
    · exact checks.1.le
    · exact ⟨weight.2.2.2.1, weight.2.2.2.2⟩
  constructor
  · exact_mod_cast bound.1
  · exact_mod_cast bound.2

theorem scaled_policy_score_mean {m n : Nat} (plan : PolicyPlan)
    (data : Fin n → PolicyDatum m) (table : List ℚ) :
    empiricalScore (fun h z => policyScore plan.logging h z / plan.weightBound) data table =
      empiricalScore (policyScore plan.logging) data table / plan.weightBound := by
  simp only [empiricalScore, ← Finset.sum_div]
  ring

-- The event and population guarantee are derived from a common iid experiment.
-- Any actual successful selector on these data inherits it; no second supplied
-- list of estimates is used, and the selected value need not be postulated
-- measurable because the theorem exhibits the measurable simultaneous event.
theorem actual_policy_advice_confidence {Ω : Type*} {m n : Nat}
    [MeasurableSpace Ω] [MeasurableSpace (PolicyDatum m)]
    [MeasurableSingletonClass (PolicyDatum m)]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure (PolicyDatum m)) [IsProbabilityMeasure P]
    (plan : PolicyPlan) (supported : policyClassSupported m plan = true)
    (nonempty : plan.family.toFinset.Nonempty) (positive : 0 < n)
    (sample : Fin n → Ω → PolicyDatum m) (measurable : ∀ i, Measurable (sample i))
    (independent : iIndepFun sample μ) (law : ∀ i, IdentDistrib (sample i) id μ P)
    (deltaPositive : 0 < plan.delta) (deltaBelowOne : plan.delta < 1) :
    ∃ confidence : Set Ω, MeasurableSet confidence ∧ 1 - (plan.delta : ℝ) ≤ μ.real confidence ∧
      ∀ w ∈ confidence, ∀ allowed chosen,
        choosePolicy plan (fun i => sample i w) allowed = some chosen →
        (∫ z, (policyScore plan.logging plan.parent z : ℝ) ∂P) ≤
          (∫ z, (policyScore plan.logging chosen z : ℝ) ∂P) + plan.tolerance := by
  have supportedFacts := of_decide_eq_true supported
  have weightPositiveQ : 0 < plan.weightBound := supportedFacts.1
  have weightPositive : (0 : ℝ) < plan.weightBound := by exact_mod_cast weightPositiveQ
  let scaled : List ℚ → PolicyDatum m → ℚ :=
    fun h z => policyScore plan.logging h z / plan.weightBound
  have joint := protected_iid_joint_event (G := Unit) μ (fun _ => P) (fun _ => n)
    (fun _ => positive) plan.family.toFinset nonempty (fun _ => sample)
    (fun _ => measurable) (fun _ => independent) (fun _ => law) scaled
    (fun _ _ => measurable_of_finite _) (fun h hh z => by
      have bound := supported_scores_are_bounded plan supported h (List.mem_toFinset.mp hh) z
      dsimp [scaled]
      push_cast
      exact ⟨div_nonneg bound.1 weightPositive.le, (div_le_one weightPositive).mpr bound.2⟩)
    (fun _ => (plan.delta : ℝ))
    (fun _ => by exact_mod_cast deltaPositive) (fun _ => by exact_mod_cast deltaBelowOne)
  refine ⟨_, joint.1, ?_, ?_⟩
  · simpa using joint.2
  · intro w hw allowed chosen selected
    obtain ⟨checks, parentMember, chosenMember, _, gate⟩ :=
      selected_policy_reads_numeric_bounds_and_permission plan _ allowed chosen selected
    have checked := checks
    simp only [policyNumericsValid, Bool.and_eq_true, decide_eq_true_eq] at checked
    have radius := verified_radius_covers_fixed_class _ _ _ _ _ checked.2
    have rawBound (table : List ℚ) (member : table ∈ plan.family) :
        |(empiricalScore (policyScore plan.logging) (fun i => sample i w) table : ℝ) -
          ∫ z, (policyScore plan.logging table z : ℝ) ∂P| ≤ (plan.radius : ℝ) := by
      have scaledBound := hw () table (List.mem_toFinset.mpr member)
      change |(empiricalScore (fun h z => policyScore plan.logging h z / plan.weightBound)
        (fun i => sample i w) table : ℝ) -
        ∫ z, ((policyScore plan.logging table z / plan.weightBound : ℚ) : ℝ) ∂P| ≤ _ at scaledBound
      simp only [scaled_policy_score_mean, Rat.cast_div, integral_div, ← sub_div,
        abs_div, abs_of_pos weightPositive] at scaledBound
      calc
        _ ≤ finiteRadius n plan.family.toFinset.card (plan.delta : ℝ) * (plan.weightBound : ℝ) :=
          (div_le_iff₀ weightPositive).mp scaledBound
        _ ≤ (plan.radius / plan.weightBound : ℚ) * (plan.weightBound : ℝ) :=
          mul_le_mul_of_nonneg_right radius weightPositive.le
        _ = (plan.radius : ℝ) := by push_cast; field_simp
    have parentBound := (abs_le.mp (rawBound plan.parent parentMember)).1
    have chosenBound := (abs_le.mp (rawBound chosen chosenMember)).2
    have numeric :
        (empiricalScore (policyScore plan.logging) (fun i => sample i w) plan.parent : ℝ) +
          plan.radius - plan.tolerance ≤
        (empiricalScore (policyScore plan.logging) (fun i => sample i w) chosen : ℝ) - plan.radius := by
      exact_mod_cast gate
    linarith

structure PolicyDesignReceipt (m : Nat) where
  plan : PolicyPlan
  observations : List (PolicyObservation m)
  acquiredAt : Instant
  consistency : SourceRef
  exchangeability : SourceRef
  selectionAndSampling : SourceRef
  noInterference : SourceRef
  measurementBridge : SourceRef
  deriving DecidableEq

structure PolicyPermission where
  context : Gamma
  environment : PolicyEnvironment
  policies : List (List ℚ)
  authority : SourceRef
  deriving DecidableEq, Repr

structure PolicyAdvice (m : Nat) where
  plan : PolicyPlan
  observations : List (PolicyObservation m)
  currentContext : Gamma
  permitted : PolicyPermission
  chosen : List ℚ
  oldEstimate : ℚ
  newEstimate : ℚ
  deriving DecidableEq

def observedPolicyData {m : Nat} (rows : List (PolicyObservation m)) :
    Fin rows.length → PolicyDatum m := fun i => observationDatum (rows.get i)

def adviseMeasured {m : Nat} (context : Gamma) (plan : PolicyPlan)
    (rows : List (PolicyObservation m)) (design : PolicyDesignReceipt m)
    (designCatalog : List (PolicyDesignReceipt m)) (permission : PolicyPermission)
    (permissionCatalog : List PolicyPermission) : Result (PolicyAdvice m) :=
  if context.jurisdiction ≠ plan.environment.jurisdiction ∨
      context.interpretation ≠ plan.environment.interpretation ∨
      context.normVersion ≠ plan.environment.dataScope.ruleVersion ∨
      context.mechanismVersion ≠ plan.environment.dataScope.mechanismVersion ∨
      ¬ rows.Pairwise (fun a b => a.measured.dictionary.event ≠ b.measured.dictionary.event) ∨
      rows.any (fun row => decide (row.treatment.environment ≠ plan.environment)) then
    .unknown .scopeMismatch
  else if design ∉ designCatalog ∨ design.plan ≠ plan ∨ design.observations ≠ rows ∨
      ¬ plan.frozenAt.ticks < design.acquiredAt.ticks then .unknown .notIdentified
  else if permission ∉ permissionCatalog ∨ permission.context ≠ context ∨
      permission.environment ≠ plan.environment then .unknown .authorityUnresolved
  else match choosePolicy plan (observedPolicyData rows) permission.policies with
    | none => .unknown .notIdentified
    | some chosen => .known ⟨plan, rows, context, permission, chosen,
        empiricalScore (policyScore plan.logging) (observedPolicyData rows) plan.parent,
        empiricalScore (policyScore plan.logging) (observedPolicyData rows) chosen⟩

theorem advice_consumes_actual_measured_values_and_allowed_policy {m : Nat}
    (context : Gamma) (plan : PolicyPlan) (rows : List (PolicyObservation m))
    (design : PolicyDesignReceipt m) (catalog : List (PolicyDesignReceipt m))
    (permission : PolicyPermission) (permissions : List PolicyPermission) (out : PolicyAdvice m)
    (accepted : adviseMeasured context plan rows design catalog permission permissions = .known out) :
    out.plan = plan ∧ out.observations = rows ∧ out.chosen ∈ permission.policies ∧
    out.oldEstimate = empiricalScore (policyScore plan.logging) (observedPolicyData rows) plan.parent ∧
    out.newEstimate = empiricalScore (policyScore plan.logging) (observedPolicyData rows) out.chosen ∧
    permission ∈ permissions ∧ permission.context = context := by
  unfold adviseMeasured at accepted
  split at accepted
  · simp at accepted
  · split at accepted
    · simp at accepted
    · split at accepted
      · simp at accepted
      · rename_i authorized
        have auth : permission ∈ permissions ∧ permission.context = context ∧
            permission.environment = plan.environment := by simpa only [not_or, not_not] using authorized
        cases choice : choosePolicy plan (observedPolicyData rows) permission.policies with
        | none => simp [choice] at accepted
        | some chosen =>
            simp only [choice, Result.known.injEq] at accepted
            subst out
            have selected := selected_policy_reads_numeric_bounds_and_permission plan _ _ chosen choice
            exact ⟨rfl, rfl, selected.2.2.2.1, rfl, rfl, auth.1, auth.2.1⟩

def measuredFeedback {m : Nat} (row : PolicyObservation m) : Observation m :=
  { scope := row.treatment.environment.dataScope
    caseId := row.measured.dictionary.context.caseId
    event := row.measured.dictionary.event
    measurement := row.measured.dictionary.unit
    record := row.measured.dictionary.resultRecord
    feature := row.treatment.feature
    label := row.measured.label
    source := row.treatment.outcomeSource
    origin := .external
    observedAt := row.measured.observedAt }

-- Experience may enter the data domain even if a policy recommendation remains
-- unidentified. Existing source confirmation, conflict and correction gates are
-- still used by beginAdaptiveRound/prepareNext. This function grants no load.
def beginMeasuredRound {m : Nat} (state : RoundState m) (now : Instant)
    (row : PolicyObservation m) (correctionPermits : List (CorrectionPermit m))
    (protocol : LearningProtocol) (validation : ValidationPlan) : RoundState m :=
  if state.service.gamma ≠ row.measured.actualPost.gamma ∨
      state.service.journal.scope ≠ row.treatment.environment.dataScope then state
  else beginAdaptiveRound state now correctionPermits (.observed (measuredFeedback row)) protocol validation

theorem feedback_reads_actual_external_label {m : Nat} (row : PolicyObservation m) :
    (measuredFeedback row).label = row.measured.label ∧
    (measuredFeedback row).event = row.measured.dictionary.event ∧
    (measuredFeedback row).feature = row.treatment.feature := ⟨rfl, rfl, rfl⟩

theorem measured_feedback_enters_actual_next_learner {m : Nat} (state : RoundState m)
    (now : Instant) (row : PolicyObservation m) (permits : List (CorrectionPermit m))
    (protocol : LearningProtocol) (validation : ValidationPlan)
    (context : state.service.gamma = row.measured.actualPost.gamma)
    (scope : state.service.journal.scope = row.treatment.environment.dataScope) :
    beginMeasuredRound state now row permits protocol validation =
      beginAdaptiveRound state now permits (.observed (measuredFeedback row)) protocol validation := by
  simp [beginMeasuredRound, context, scope]

theorem measured_feedback_prepares_from_actual_loaded_and_journal {m : Nat}
    (state : RoundState m) (now : Instant) (row : PolicyObservation m)
    (permits : List (CorrectionPermit m)) (protocol : LearningProtocol) (validation : ValidationPlan)
    (context : state.service.gamma = row.measured.actualPost.gamma)
    (scope : state.service.journal.scope = row.treatment.environment.dataScope)
    (free : state.pending = none) (room : state.records.length < state.horizon) :
    (beginMeasuredRound state now row permits protocol validation).service.journal =
      (applyChange now permits state.service.journal (.observed (measuredFeedback row))).post ∧
    (beginMeasuredRound state now row permits protocol validation).pending =
      some ⟨state.learner, now, state.records.length,
        ValidatedFeedbackLoad20261027.prepareNext state.service now permits
          (.observed (measuredFeedback row)) protocol state.learner.proposals,
        { validation with models := state.service.loaded.fitted.table :: state.learner.proposals }⟩ := by
  rw [measured_feedback_enters_actual_next_learner state now row permits protocol validation context scope]
  have used := generation_uses_actual_loaded_and_learner state now permits
    (.observed (measuredFeedback row)) protocol validation free room
  exact ⟨used.2.1, used.1⟩

theorem measured_data_update_keeps_rules_loaded_and_budget {m : Nat}
    (state : RoundState m) (now : Instant) (row : PolicyObservation m)
    (permits : List (CorrectionPermit m)) (protocol : LearningProtocol) (validation : ValidationPlan) :
    (beginMeasuredRound state now row permits protocol validation).service.gamma = state.service.gamma ∧
    (beginMeasuredRound state now row permits protocol validation).service.loaded = state.service.loaded ∧
    (beginMeasuredRound state now row permits protocol validation).learner = state.learner ∧
    (beginMeasuredRound state now row permits protocol validation).checker = state.checker ∧
    (beginMeasuredRound state now row permits protocol validation).records = state.records := by
  unfold beginMeasuredRound
  split
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · unfold beginAdaptiveRound
    split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end JurisLean.Candidates.MeasuredPolicy20261027
