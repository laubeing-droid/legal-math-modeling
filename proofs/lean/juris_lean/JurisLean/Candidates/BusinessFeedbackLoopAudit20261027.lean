import JurisLean.Candidates.BusinessFeedbackLoop20261027
import JurisLean.Candidates.LoadedLegalConsumerAudit20261027
import JurisLean.Candidates.MeasuredPolicyAudit20261027

#check JurisLean.Candidates.BusinessFeedbackLoop20261027.measurement_reads_the_reported_post_only
#print axioms JurisLean.Candidates.BusinessFeedbackLoop20261027.measurement_reads_the_reported_post_only
#check JurisLean.Candidates.BusinessFeedbackLoop20261027.unknown_commit_cannot_generate_a_measurement
#print axioms JurisLean.Candidates.BusinessFeedbackLoop20261027.unknown_commit_cannot_generate_a_measurement
#check JurisLean.Candidates.BusinessFeedbackLoop20261027.semantic_replay_does_not_enqueue_another_round
#print axioms JurisLean.Candidates.BusinessFeedbackLoop20261027.semantic_replay_does_not_enqueue_another_round
#check JurisLean.Candidates.BusinessFeedbackLoop20261027.distinct_observation_retains_full_evidence_and_queue
#print axioms JurisLean.Candidates.BusinessFeedbackLoop20261027.distinct_observation_retains_full_evidence_and_queue
#check JurisLean.Candidates.BusinessFeedbackLoop20261027.semantic_replay_does_not_append_a_policy_sample
#print axioms JurisLean.Candidates.BusinessFeedbackLoop20261027.semantic_replay_does_not_append_a_policy_sample
#check JurisLean.Candidates.BusinessFeedbackLoop20261027.conflicting_measurement_does_not_become_a_policy_sample
#print axioms JurisLean.Candidates.BusinessFeedbackLoop20261027.conflicting_measurement_does_not_become_a_policy_sample
#check JurisLean.Candidates.BusinessFeedbackLoop20261027.known_advice_reads_recorded_data_within_cutoffs
#print axioms JurisLean.Candidates.BusinessFeedbackLoop20261027.known_advice_reads_recorded_data_within_cutoffs
#check JurisLean.Candidates.BusinessFeedbackLoop20261027.deferred_feedback_preserves_actual_learner
#print axioms JurisLean.Candidates.BusinessFeedbackLoop20261027.deferred_feedback_preserves_actual_learner
#check JurisLean.Candidates.BusinessFeedbackLoop20261027.prepared_feedback_uses_actual_observation
#print axioms JurisLean.Candidates.BusinessFeedbackLoop20261027.prepared_feedback_uses_actual_observation
#check JurisLean.Candidates.BusinessFeedbackLoop20261027.preparing_observation_keeps_risk_budget
#print axioms JurisLean.Candidates.BusinessFeedbackLoop20261027.preparing_observation_keeps_risk_budget
#check JurisLean.Candidates.BusinessFeedbackLoop20261027.unconfirmed_observation_remains_available_for_retry
#print axioms JurisLean.Candidates.BusinessFeedbackLoop20261027.unconfirmed_observation_remains_available_for_retry
#check JurisLean.Candidates.BusinessFeedbackLoop20261027.deferred_queue_keeps_every_unprocessed_row
#print axioms JurisLean.Candidates.BusinessFeedbackLoop20261027.deferred_queue_keeps_every_unprocessed_row
#check JurisLean.Candidates.BusinessFeedbackLoop20261027.preparing_queue_keeps_risk_budget
#print axioms JurisLean.Candidates.BusinessFeedbackLoop20261027.preparing_queue_keeps_risk_budget
#check JurisLean.Candidates.BusinessFeedbackLoop20261027.continuation_does_not_repeat_business_execution
#print axioms JurisLean.Candidates.BusinessFeedbackLoop20261027.continuation_does_not_repeat_business_execution
#check JurisLean.Candidates.BusinessFeedbackLoop20261027.continuation_feedback_is_the_actual_measured_result
#print axioms JurisLean.Candidates.BusinessFeedbackLoop20261027.continuation_feedback_is_the_actual_measured_result
#check JurisLean.Candidates.BusinessFeedbackLoop20261027.assessment_passes_actual_post_to_next_model
#print axioms JurisLean.Candidates.BusinessFeedbackLoop20261027.assessment_passes_actual_post_to_next_model
#check JurisLean.Candidates.BusinessFeedbackLoop20261027.unresolved_business_has_no_new_action
#print axioms JurisLean.Candidates.BusinessFeedbackLoop20261027.unresolved_business_has_no_new_action
#check JurisLean.Candidates.BusinessFeedbackLoop20261027.actual_action_reads_current_handle_and_loaded_state
#print axioms JurisLean.Candidates.BusinessFeedbackLoop20261027.actual_action_reads_current_handle_and_loaded_state
#check JurisLean.Candidates.BusinessFeedbackLoop20261027.next_action_reads_actual_assessment_post
#print axioms JurisLean.Candidates.BusinessFeedbackLoop20261027.next_action_reads_actual_assessment_post
#check JurisLean.Candidates.BusinessFeedbackLoop20261027.action_preserves_every_reported_business_state
#print axioms JurisLean.Candidates.BusinessFeedbackLoop20261027.action_preserves_every_reported_business_state
#check JurisLean.Candidates.BusinessFeedbackLoop20261027.episode_consumes_actual_output_and_keeps_invariants
#print axioms JurisLean.Candidates.BusinessFeedbackLoop20261027.episode_consumes_actual_output_and_keeps_invariants
#check JurisLean.Candidates.BusinessFeedbackLoop20261027.each_command_preserves_known_business_and_learning_budget
#print axioms JurisLean.Candidates.BusinessFeedbackLoop20261027.each_command_preserves_known_business_and_learning_budget
#check JurisLean.Candidates.BusinessFeedbackLoop20261027.arbitrary_finite_commands_consume_actual_posts
#print axioms JurisLean.Candidates.BusinessFeedbackLoop20261027.arbitrary_finite_commands_consume_actual_posts

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.LearningConsumer20261027
open JurisLean.Candidates.SampleCalibrationConsumer20261027
open JurisLean.Candidates.IntervalDecisionConsumer20261027
open JurisLean.Candidates.DecisionTrajectoryConsumer20261027
open JurisLean.Candidates.EventFeedbackConsumer20261027
open JurisLean.Candidates.ProtectedFeedback20261027
open JurisLean.Candidates.ValidatedFeedbackLoad20261027
open JurisLean.Candidates.AdaptiveRoundLedger20261027
open JurisLean.Candidates.LegalActionDomain20261027
open JurisLean.Candidates.LoadedLegalConsumer20261027
open JurisLean.Candidates.BusinessMeasurement20261027
open JurisLean.Candidates.MeasuredPolicy20261027
open JurisLean.Candidates.BusinessFeedbackLoop20261027

namespace JurisLean.Candidates.BusinessFeedbackLoop20261027.Audit

def dictionary (id : Nat) : MeasurementDictionary :=
  {performanceDictionary with
    context := LoadedLegalConsumer20261027.Audit.gamma
    event := ⟨100 + id⟩, unit := ⟨200 + id⟩, resultRecord := ⟨300 + id⟩
    opportunity := 1 + id, targetVersion := 2}

def environment : PolicyEnvironment :=
  {MeasuredPolicyFixture.environment with construct := .performance}

def treatment (id : Nat) : TreatmentRecord 2 :=
  ⟨environment, dictionary id, 1, ⟨-2⟩, ⟨40⟩, true, ⟨-1⟩, ⟨50⟩, ⟨60⟩⟩

def measurement (id : Nat) : MeasurementInput 2 :=
  let d := dictionary id
  let rows := [measurementStamp d 1 1 (.payment ⟨1⟩), measurementStamp d 2 2 (.payment ⟨2⟩)]
  ⟨d, ⟨20⟩, attestRows rows, closeWindow d rows, rows, environment, treatment id, [treatment id]⟩

-- A synthetic independent source statement, declared in full before execution.
def confirmation (id : Nat) : ExternalConfirmation 2 :=
  ⟨⟨ValidatedFeedbackLoadFixture.scope, LoadedLegalConsumer20261027.Audit.gamma.caseId,
    ⟨100 + id⟩, ⟨200 + id⟩, ⟨300 + id⟩, 1, true, ⟨50⟩, .external, ⟨20⟩⟩, ⟨90⟩⟩

def initial (service : Service 2) : State 2 :=
  let confirmedJournal := {service.journal with
    confirmations := (List.range 3).map confirmation ++ service.journal.confirmations}
  let actual := {service with
    gamma := LoadedLegalConsumer20261027.Audit.gamma
    journal := confirmedJournal}
  ⟨⟨.success, some LoadedLegalConsumer20261027.Audit.opening, [], []⟩,
    AdaptiveRoundLedgerFixture.base actual, .known [], .unknown .missingEvidence, [], []⟩

def feedback : FeedbackInput 2 :=
  ⟨⟨20⟩, [], {ValidatedFeedbackLoadFixture.protocol with fit :=
    {ValidatedFeedbackLoadFixture.protocol.fit with modelVersion := 6}}, ValidatedFeedbackLoadFixture.plan⟩

def policy : PolicyInput 2 :=
  let plan := {MeasuredPolicyFixture.plan with environment := environment}
  let design : PolicyDesignReceipt 2 := ⟨plan, [], ⟨20⟩, ⟨70⟩, ⟨71⟩, ⟨72⟩, ⟨73⟩, ⟨74⟩⟩
  let permission : PolicyPermission :=
    ⟨LoadedLegalConsumer20261027.Audit.gamma, environment, [[0, 0], [1, 1]], ⟨80⟩⟩
  ⟨plan, design, [design], permission, [permission]⟩

def action (state : State 2) : ActionInput (List Nat) 2 :=
  let p := {LoadedLegalConsumer20261027.Audit.packet state.learning with modelAvailableAt := ⟨30⟩}
  ⟨LoadedLegalConsumer20261027.Audit.legalInput, LoadedLegalConsumer20261027.Audit.actionModel,
    LoadedLegalConsumer20261027.Audit.proposals, LoadedLegalConsumer20261027.Audit.request state.learning,
    p, [p], 1/10, 8, id, LoadedLegalConsumer20261027.Audit.grants⟩

def first (service : Service 2) : Episode (List Nat) 2 :=
  let state := initial service
  episode state (action state) (measurement 0) policy feedback

def assessRequest (state : State 2) (fallback : Evaluation 2) : RoundRequest 2 :=
  AdaptiveRoundLedgerFixture.request state.learning fallback fallback.blocks

def assessed (state : State 2) (fallback : Evaluation 2) : State 2 :=
  let r := assessRequest state fallback
  assess state r [r.sampling] [r.permit]

/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service _ =>
  let out := first service
  match out.action.run, out.continuation.measurement, out.continuation.observation with
  | some run, .measured measured, .known row => decide (
      out.continuation.post.business = out.action.post.business ∧
      out.action.post.business = run.execution.payment ∧
      out.action.post.business.current = some measured.actualPost ∧
      measured.actualPost.state.paid = 14 ∧ measured.actualPost.state.allocated = 10 ∧
      measured.actualPost.state.surplus = 4 ∧ measured.actualPost.state.receipts.length = 2 ∧
      measured.measuredTotal = 10 ∧ measured.label = true ∧ row.measured = measured ∧
      out.continuation.post.learning.pending.isSome ∧ out.continuation.post.feedbackQueue = [] ∧
      (lookup out.continuation.post.learning.service.journal ⟨100⟩).map (fun cell => cell.state) =
        some (.active 1 true) ∧ out.continuation.post.observationHistory = [row])
  | _, _, _ => false)

-- The policy recommendation is unidentified with one row; genuine experience
-- still reaches the learner. Its candidate is not yet the production model.
/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service _ =>
  let out := (first service).continuation
  decide (out.advice = .unknown .notIdentified ∧
    (readLoaded out.post.learning.service).fitted.table = [0, 0] ∧
    roundSpent out.post.learning = 0 ∧ out.post.learning.records = []))

/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service evaluation =>
  let measured := (first service).continuation.post
  let loaded := assessed measured evaluation
  let next := act loaded {action loaded with request :=
    {LoadedLegalConsumer20261027.Audit.request loaded.learning with riskLimit := 2/5}}
  match next.run, next.post.business.current with
  | some run, some post => match run.decision with
    | .known selected => decide (loaded.business = measured.business ∧
        roundSpent loaded.learning = 1/10 ∧ loaded.learning.records.length = 1 ∧
        (readLoaded loaded.learning.service).fitted.table = [0, 1] ∧
        selected.probability.fitted = (readLoaded loaded.learning.service).fitted ∧
        selected.probability.estimate = 1 ∧ selected.nominal.action.id = 1 ∧
        post.state.paid = 14 ∧ post.state.receipts.length = 2 ∧
        next.post.business.current = loaded.business.current)
    | _ => false
  | _, _ => false)

/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service evaluation =>
  let before := (first service).continuation.post
  let r := assessRequest before evaluation
  let loaded := assess before r [r.sampling] [r.permit]
  decide (assess loaded r [r.sampling] [r.permit] = loaded ∧
    assess loaded {r with checker := 999} [r.sampling] [r.permit] = loaded))

/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service evaluation =>
  let before := (first service).continuation.post
  let r := assessRequest before evaluation
  let refused := assess before r [r.sampling] []
  decide ((readLoaded refused.learning.service).fitted.table = [0, 0] ∧
    roundSpent refused.learning = 1/10 ∧ refused.business = before.business))

-- An old calibration packet cannot be reused after the real loaded state changes.
/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service evaluation =>
  let before := (first service).continuation.post
  let loaded := assessed before evaluation
  let next := act loaded {action loaded with
    calibration := (action before).calibration
    calibrationCatalog := (action before).calibrationCatalog}
  match next.run with
  | some run => decide (run.probability = .unknown .scopeMismatch ∧
      next.post.business.current = loaded.business.current ∧ next.post.business.outcomes = [])
  | none => false)

-- A real ambiguous payment result, including its prior successful outcome, is
-- retained. No next action or measured label is synthesized from the old handle.
/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service _ =>
  let business := runTrajectory LoadedLegalConsumer20261027.Audit.grants
    LoadedLegalConsumer20261027.Audit.opening
    [.pay (trajectoryRequest 1) .submit, .pay (trajectoryRequest 2) .unknownCommit]
  let state := {initial service with business := business}
  let out := episode state (action state) (measurement 0) policy feedback
  decide (business.current = none ∧ business.outcomes.length = 2 ∧ out.action.run.isNone ∧
    out.continuation.measurement = .unknown .unknownCommit ∧
    out.continuation.post.business = business ∧ out.continuation.post.learning = state.learning ∧
    out.continuation.post.policyRows = .known []))

/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service _ =>
  let state := initial service
  let out := continueBusiness state (measurement 0) policy feedback
  decide (out.measurement = .unknown .measurementBridgeMissing ∧
    out.post.business = state.business ∧ out.post.learning = state.learning ∧
    out.post.observationHistory = [] ∧ out.post.feedbackQueue = []))

-- Re-reading the same immutable event at a later time is not a second sample.
/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service evaluation =>
  let state := assessed (first service).continuation.post evaluation
  let out := continueBusiness state {measurement 0 with now := ⟨25⟩} policy feedback
  decide (out.post.learning = state.learning ∧ out.post.business = state.business ∧
    out.post.policyRows = state.policyRows ∧ out.post.observationHistory = state.observationHistory ∧
    out.post.feedbackQueue = []))

-- Busy preparation retains each later observation and retries the actual head.
/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service evaluation =>
  let state := (first service).continuation.post
  let second := continueBusiness state (measurement 1) policy feedback
  let third := continueBusiness second.post (measurement 2) policy feedback
  let released := assessed third.post evaluation
  let retried := retryFeedback released feedback
  decide (second.preparation = .unknown .openMissingOpportunity ∧
    third.post.feedbackQueue.length = 2 ∧ third.post.observationHistory.length = 3 ∧
    retried.feedbackQueue.map (fun row => row.measured.dictionary.event) = [⟨102⟩] ∧
    retried.learning.pending.isSome ∧ retried.business = third.post.business ∧
    (lookup retried.learning.service.journal ⟨101⟩).map (fun cell => cell.state) = some (.active 1 true)))

/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service _ =>
  let state := (first service).continuation.post
  let queued := (continueBusiness state (measurement 1) policy feedback).post
  let out := continueBusiness queued {measurement 2 with sources := []} policy feedback
  decide (out.post.feedbackQueue = queued.feedbackQueue ∧ out.post.learning = queued.learning ∧
    out.post.observationHistory = queued.observationHistory))

-- Conflicting full observations remain available; neither policy selection nor
-- an implicit overwrite turns them into an accepted training label.
/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service _ =>
  let state := (first service).continuation.post
  let m := measurement 0
  let rows := m.rows.take 1
  let conflicting := {m with
    rows := rows, sources := attestRows rows
    closures := closeWindow m.dictionary rows}
  let out := continueBusiness state conflicting policy feedback
  match out.post.observationHistory with
  | [old, changed] => decide (old.measured.label = true ∧ changed.measured.label = false ∧
      old.measured.measuredTotal = 10 ∧ changed.measured.measuredTotal = 7 ∧
      out.post.policyRows = .conflict 300 300 ∧ out.advice = .conflict 300 300 ∧
      out.post.feedbackQueue = [changed] ∧ out.post.learning = state.learning)
  | _ => false)

/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service _ =>
  let state := initial service
  let denied := {action state with grants := []}
  let out := episode state denied (measurement 0) policy feedback
  decide (out.action.post.business.exit = .rejected ∧
    out.continuation.measurement = .unknown .measurementBridgeMissing ∧
    out.continuation.post.learning = state.learning))

/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service _ =>
  let state := (first service).continuation.post
  let mismatch := {state with learning := {state.learning with
    pending := none
    service := {state.learning.service with gamma :=
      {state.learning.service.gamma with evidenceVersion := 99}}}}
  let out := continueBusiness mismatch (measurement 1) policy feedback
  decide (out.preparation = .unknown .scopeMismatch ∧ out.post.learning = mismatch.learning ∧
    out.post.feedbackQueue.length = 1 ∧ out.post.business = mismatch.business))

/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service _ =>
  let state := (first service).continuation.post
  let exhausted := {state with learning := {state.learning with pending := none, horizon := 0}}
  let out := continueBusiness exhausted (measurement 1) policy feedback
  decide (out.preparation = .rejected .unsupported ∧ out.post.learning = exhausted.learning ∧
    out.post.feedbackQueue.length = 1))

-- A measured label without its independent confirmation is not silently added
-- to the fitted dataset, even though the business measurement itself succeeded.
/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service _ =>
  let state := initial service
  let unconfirmed := {state with learning := {state.learning with service :=
    {state.learning.service with journal := {state.learning.service.journal with
      confirmations := service.journal.confirmations}}}}
  let out := episode unconfirmed (action unconfirmed) (measurement 0) policy feedback
  decide (lookup out.continuation.post.learning.service.journal ⟨100⟩ = none ∧
    out.continuation.post.learning.service.journal = unconfirmed.learning.service.journal ∧
    out.continuation.post.learning.service.loaded = unconfirmed.learning.service.loaded ∧
    out.continuation.post.observationHistory.length = 1 ∧ out.continuation.post.feedbackQueue.length = 1))

/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service evaluation =>
  let state := initial service
  let unconfirmed := {state with learning := {state.learning with service :=
    {state.learning.service with journal := {state.learning.service.journal with
      confirmations := service.journal.confirmations}}}}
  let observed := (episode unconfirmed (action unconfirmed) (measurement 0) policy feedback).continuation.post
  let finished := assessed observed evaluation
  -- An independently supplied source catalog now includes the exact same row.
  let confirmed := {finished with learning := {finished.learning with service :=
    {finished.learning.service with journal := {finished.learning.service.journal with
      confirmations := confirmation 0 :: finished.learning.service.journal.confirmations}}}}
  let retried := retryFeedback confirmed feedback
  decide (finished.feedbackQueue.length = 1 ∧ roundSpent finished.learning = 0 ∧
    retried.feedbackQueue = [] ∧ retried.learning.pending.isSome ∧
    (lookup retried.learning.service.journal ⟨100⟩).map (fun cell => cell.state) = some (.active 1 true) ∧
    retried.business = finished.business))

def procedureMeasurement (id : Nat) : MeasurementInput 2 :=
  let d := {MeasuredPolicyFixture.dictionary id with context := LoadedLegalConsumer20261027.Audit.gamma}
  let raw := [measurementStamp d (500 + id) 1
    (.procedureChoice ⟨8⟩ (if id % 2 = 0 then 4 else 5))]
  let treatment := {MeasuredPolicyFixture.treatment id with dictionary := d}
  ⟨d, ⟨20⟩, attestRows raw, closeWindow d raw, raw, MeasuredPolicyFixture.environment,
    treatment, [treatment]⟩

-- Existing policy rows also come from the real measurement consumer on this
-- reported business state. The last row is appended by continueBusiness itself.
def procedureRows (business : Pipeline.PaymentRun) : List (PolicyObservation 2) :=
  (List.range 400).filterMap fun id =>
    let m := procedureMeasurement id
    match consumeMeasurement m.environment (measureReported business m) m.treatment m.treatments with
    | .known row => some row
    | _ => none

def procedurePolicy (business : Pipeline.PaymentRun) : PolicyInput 2 :=
  let design : PolicyDesignReceipt 2 := ⟨MeasuredPolicyFixture.plan, procedureRows business,
    ⟨20⟩, ⟨70⟩, ⟨71⟩, ⟨72⟩, ⟨73⟩, ⟨74⟩⟩
  let permission := {MeasuredPolicyFixture.permission with context := LoadedLegalConsumer20261027.Audit.gamma}
  ⟨MeasuredPolicyFixture.plan, design, [design], permission, [permission]⟩

def policyState (service : Service 2) : State 2 :=
  let state := (act (initial service) (action (initial service))).post
  let past := (procedureRows state.business).take 399
  {state with
    learning := {state.learning with horizon := 0}
    policyRows := .known past
    observationHistory := past}

/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service _ =>
  let state := policyState service
  let out := continueBusiness state (procedureMeasurement 399) (procedurePolicy state.business) feedback
  match out.advice with
  | .known selected => decide (selected.observations.length = 400 ∧
      out.post.policyRows = .known selected.observations ∧ selected.chosen = [1, 1] ∧
      selected.oldEstimate = 0 ∧ selected.newEstimate = 1 ∧
      out.post.business = state.business ∧ out.post.learning.service.loaded = state.learning.service.loaded ∧
      out.post.feedbackQueue.length = 1)
  | _ => false)

/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service _ =>
  let state := policyState service
  let p := procedurePolicy state.business
  let out := continueBusiness state (procedureMeasurement 399) {p with designs := []} feedback
  decide (out.advice = .unknown .notIdentified ∧ out.post.policyRows = .known p.design.observations))

/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service _ =>
  let state := policyState service
  let p := procedurePolicy state.business
  let out := continueBusiness state (procedureMeasurement 399) {p with permissions := []} feedback
  decide (out.advice = .unknown .authorityUnresolved ∧ out.post.learning.service.loaded = state.learning.service.loaded))

/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service _ =>
  let state := policyState service
  let p := procedurePolicy state.business
  let late := {p.design with acquiredAt := ⟨101⟩}
  let out := continueBusiness state (procedureMeasurement 399) {p with design := late, designs := [late]} feedback
  decide (out.advice = .unknown .scopeMismatch))

/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service _ =>
  let state := policyState service
  let p := procedurePolicy state.business
  let future := p.design.observations.map fun row =>
    {row with measured := {row.measured with observedAt := ⟨101⟩}}
  let late := {p.design with observations := future}
  decide (adviseRecorded LoadedLegalConsumer20261027.Audit.gamma
    {p with design := late, designs := [late]} (.known future) = .unknown .scopeMismatch))

end JurisLean.Candidates.BusinessFeedbackLoop20261027.Audit
