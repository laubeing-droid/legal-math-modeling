import JurisLean.Candidates.LoadedLegalConsumer20261027
import JurisLean.Candidates.MeasuredPolicy20261027

/-!
Actual business output -> measurement -> policy/experience -> candidate ->
independently validated activation -> next production decision. The controller
retains the complete client payment result, so an unknown commit cannot be
replaced by its previous handle. Measurement never reexecutes the business plan.

The commands form a finite mathematical consumer protocol. Source and causal
catalogs remain external premises. A busy learner reports deferred feedback;
every unprocessed observation stays queued for an explicit retry after assessment.
Context changes are not authorization to relabel or load an old model.
-/

namespace JurisLean.Candidates.BusinessFeedbackLoop20261027

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

structure State (m : Nat) where
  business : Pipeline.PaymentRun
  learning : RoundState m
  policyRows : Result (List (PolicyObservation m))
  lastObservation : Result (PolicyObservation m)
  observationHistory : List (PolicyObservation m)
  feedbackQueue : List (PolicyObservation m)
  deriving DecidableEq

structure MeasurementInput (m : Nat) where
  dictionary : MeasurementDictionary
  now : Instant
  sources : List ObservationAttestation
  closures : List WindowClosure
  rows : List MeasurementRow
  environment : PolicyEnvironment
  treatment : TreatmentRecord m
  treatments : List (TreatmentRecord m)

structure PolicyInput (m : Nat) where
  plan : PolicyPlan
  design : PolicyDesignReceipt m
  designs : List (PolicyDesignReceipt m)
  permission : PolicyPermission
  permissions : List PolicyPermission

structure FeedbackInput (m : Nat) where
  now : Instant
  corrections : List (CorrectionPermit m)
  protocol : LearningProtocol
  validation : ValidationPlan

def measureReported {m : Nat} (business : Pipeline.PaymentRun) (input : MeasurementInput m) :
    MeasurementResult :=
  match business.current with
  | none => .unknown .unknownCommit
  | some post => measureBusiness post input.dictionary input.now input.sources input.closures input.rows

theorem measurement_reads_the_reported_post_only {m : Nat}
    (business : Pipeline.PaymentRun) (input : MeasurementInput m) (out : BehaviorMeasurement)
    (measured : measureReported business input = .measured out) :
    ∃ post, business.current = some post ∧ out.actualPost = post ∧
      out.dictionary = input.dictionary ∧ out.rows = input.rows := by
  cases reported : business.current with
  | none => simp [measureReported, reported] at measured
  | some post =>
      have actual : measureBusiness post input.dictionary input.now input.sources input.closures
          input.rows = .measured out := by simpa [measureReported, reported] using measured
      have bound := measurement_reads_actual_state_and_rows post input.dictionary input.now
        input.sources input.closures input.rows out actual
      exact ⟨post, rfl, bound.1, bound.2.1, bound.2.2.1⟩

theorem unknown_commit_cannot_generate_a_measurement {m : Nat}
    (business : Pipeline.PaymentRun) (input : MeasurementInput m) (unknown : business.current = none) :
    measureReported business input = .unknown .unknownCommit := by
  simp [measureReported, unknown]

-- Receipt time and the later handle from which an immutable event is reread do
-- not change its semantic observation. Changed values, sources or definitions do.
def sameObservation {m : Nat} (a b : PolicyObservation m) : Bool :=
  decide (a.treatment = b.treatment ∧ a.measured.dictionary = b.measured.dictionary ∧
    a.measured.rows = b.measured.rows ∧ a.measured.measuredTotal = b.measured.measuredTotal ∧
    a.measured.label = b.measured.label)

-- Retain full conflicting observations, while semantic replays add neither a
-- new sample nor a new learning round. A busy learner does not lose later rows.
def enqueueObserved {m : Nat} (history queue : List (PolicyObservation m))
    (observed : Result (PolicyObservation m)) :
    List (PolicyObservation m) × List (PolicyObservation m) :=
  match observed with
  | .known row =>
      if history.any (fun old => sameObservation old row) then (history, queue)
      else (history ++ [row], queue ++ [row])
  | _ => (history, queue)

theorem semantic_replay_does_not_enqueue_another_round {m : Nat}
    (history queue : List (PolicyObservation m)) (row : PolicyObservation m)
    (seen : history.any (fun old => sameObservation old row) = true) :
    enqueueObserved history queue (.known row) = (history, queue) := by
  simp [enqueueObserved, seen]

theorem distinct_observation_retains_full_evidence_and_queue {m : Nat}
    (history queue : List (PolicyObservation m)) (row : PolicyObservation m)
    (fresh : history.any (fun old => sameObservation old row) = false) :
    enqueueObserved history queue (.known row) = (history ++ [row], queue ++ [row]) := by
  simp [enqueueObserved, fresh]

def recordObservation {m : Nat} (past : Result (List (PolicyObservation m)))
    (observed : Result (PolicyObservation m)) : Result (List (PolicyObservation m)) :=
  match past, observed with
  | .known rows, .known row =>
      match rows.find? (fun old => decide (old.measured.dictionary.event = row.measured.dictionary.event)) with
      | none => .known (rows ++ [row])
      | some old =>
          if sameObservation old row then .known rows
          else .conflict old.measured.dictionary.resultRecord.value row.measured.dictionary.resultRecord.value
  | .known rows, _ => .known rows
  | .unknown e, _ => .unknown e
  | .rejected e, _ => .rejected e
  | .conflict a b, _ => .conflict a b

theorem semantic_replay_does_not_append_a_policy_sample {m : Nat}
    (rows : List (PolicyObservation m)) (old row : PolicyObservation m)
    (found : rows.find? (fun prior => decide (prior.measured.dictionary.event = row.measured.dictionary.event)) = some old)
    (same : sameObservation old row = true) :
    recordObservation (.known rows) (.known row) = .known rows := by
  simp [recordObservation, found, same]

theorem conflicting_measurement_does_not_become_a_policy_sample {m : Nat}
    (rows : List (PolicyObservation m)) (old row : PolicyObservation m)
    (found : rows.find? (fun prior => decide (prior.measured.dictionary.event = row.measured.dictionary.event)) = some old)
    (different : sameObservation old row = false) :
    recordObservation (.known rows) (.known row) =
      .conflict old.measured.dictionary.resultRecord.value row.measured.dictionary.resultRecord.value := by
  simp [recordObservation, found, different]

def adviseRecorded {m : Nat} (context : Gamma) (input : PolicyInput m)
    (rows : Result (List (PolicyObservation m))) : Result (PolicyAdvice m) :=
  match rows with
  | .known actual =>
      if input.design.acquiredAt.ticks ≤ context.knowledgeCutoff.ticks ∧
          input.design.acquiredAt.ticks ≤ context.recordCutoff.ticks ∧
          (∀ row ∈ actual, row.measured.observedAt.ticks ≤ context.knowledgeCutoff.ticks ∧
            row.measured.observedAt.ticks ≤ context.recordCutoff.ticks) then
        adviseMeasured context input.plan actual input.design input.designs input.permission input.permissions
      else .unknown .scopeMismatch
  | .unknown e => .unknown e
  | .rejected e => .rejected e
  | .conflict a b => .conflict a b

theorem known_advice_reads_recorded_data_within_cutoffs {m : Nat}
    (context : Gamma) (input : PolicyInput m) (rows : Result (List (PolicyObservation m)))
    (out : PolicyAdvice m) (accepted : adviseRecorded context input rows = .known out) :
    ∃ actual, rows = .known actual ∧ out.observations = actual ∧
      input.design.acquiredAt.ticks ≤ context.knowledgeCutoff.ticks ∧
      input.design.acquiredAt.ticks ≤ context.recordCutoff.ticks ∧
      (∀ row ∈ actual, row.measured.observedAt.ticks ≤ context.knowledgeCutoff.ticks ∧
        row.measured.observedAt.ticks ≤ context.recordCutoff.ticks) := by
  cases rows with
  | unknown e => cases accepted
  | rejected e => cases accepted
  | conflict a b => cases accepted
  | known actual =>
      simp only [adviseRecorded] at accepted
      split at accepted
      · rename_i timely
        have source := advice_consumes_actual_measured_values_and_allowed_policy context input.plan
          actual input.design input.designs input.permission input.permissions out accepted
        exact ⟨actual, rfl, source.2.1, timely.1, timely.2.1, timely.2.2⟩
      · cases accepted

def prepareObserved {m : Nat} (state : RoundState m) (input : FeedbackInput m)
    (observed : Result (PolicyObservation m)) : Result (RoundState m) :=
  match observed with
  | .known row =>
      if state.pending.isSome then .unknown .openMissingOpportunity
      else if state.horizon ≤ state.records.length then .rejected .unsupported
      else if state.service.gamma ≠ row.measured.actualPost.gamma ∨
          state.service.journal.scope ≠ row.treatment.environment.dataScope then .unknown .scopeMismatch
      else .known (beginMeasuredRound state input.now row input.corrections input.protocol input.validation)
  | .unknown e => .unknown e
  | .rejected e => .rejected e
  | .conflict a b => .conflict a b

def preparedState {m : Nat} (before : RoundState m) (result : Result (RoundState m)) : RoundState m :=
  match result with | .known after => after | _ => before

theorem deferred_feedback_preserves_actual_learner {m : Nat}
    (state : RoundState m) (input : FeedbackInput m) (row : PolicyObservation m)
    (busy : state.pending.isSome = true) :
    prepareObserved state input (.known row) = .unknown .openMissingOpportunity ∧
    preparedState state (prepareObserved state input (.known row)) = state := by
  simp [prepareObserved, preparedState, busy]

theorem prepared_feedback_uses_actual_observation {m : Nat}
    (state : RoundState m) (input : FeedbackInput m) (observed : Result (PolicyObservation m))
    (out : RoundState m) (prepared : prepareObserved state input observed = .known out) :
    ∃ row, observed = .known row ∧
      state.service.gamma = row.measured.actualPost.gamma ∧
      state.service.journal.scope = row.treatment.environment.dataScope ∧
      out = beginAdaptiveRound state input.now input.corrections (.observed (measuredFeedback row))
        input.protocol input.validation := by
  cases observed with
  | unknown e => cases prepared
  | rejected e => cases prepared
  | conflict a b => cases prepared
  | known row =>
      unfold prepareObserved at prepared
      split at prepared
      · cases prepared
      · split at prepared
        · cases prepared
        · split at prepared
          · cases prepared
          · rename_i same
            have binding : state.service.gamma = row.measured.actualPost.gamma ∧
                state.service.journal.scope = row.treatment.environment.dataScope := by
              simpa only [not_or, not_not] using same
            cases prepared
            exact ⟨row, rfl, binding.1, binding.2,
              measured_feedback_enters_actual_next_learner state input.now row input.corrections
                input.protocol input.validation binding.1 binding.2⟩

theorem preparing_observation_keeps_risk_budget {m : Nat}
    (state : RoundState m) (input : FeedbackInput m) (observed : Result (PolicyObservation m)) :
    (preparedState state (prepareObserved state input observed)).limit = state.limit ∧
    (preparedState state (prepareObserved state input observed)).records = state.records := by
  cases observed with
  | unknown e => exact ⟨rfl, rfl⟩
  | rejected e => exact ⟨rfl, rfl⟩
  | conflict a b => exact ⟨rfl, rfl⟩
  | known row =>
      simp only [prepareObserved]
      split_ifs <;> try exact ⟨rfl, rfl⟩
      simp only [preparedState]
      unfold beginMeasuredRound
      split <;> try exact ⟨rfl, rfl⟩
      unfold beginAdaptiveRound
      split <;> exact ⟨rfl, rfl⟩

def prepareQueued {m : Nat} (state : RoundState m) (input : FeedbackInput m)
    (queue : List (PolicyObservation m)) : Result (RoundState m) :=
  match queue with
  | [] => .unknown .missingEvidence
  | row :: _ => prepareObserved state input (.known row)

def unpreparedQueue {m : Nat} (queue : List (PolicyObservation m))
    (prepared : Result (RoundState m)) : List (PolicyObservation m) :=
  match prepared with | .known _ => queue.tail | _ => queue

theorem deferred_queue_keeps_every_unprocessed_row {m : Nat}
    (state : RoundState m) (input : FeedbackInput m) (row : PolicyObservation m)
    (rest : List (PolicyObservation m)) (busy : state.pending.isSome = true) :
    unpreparedQueue (row :: rest) (prepareQueued state input (row :: rest)) = row :: rest := by
  simp [prepareQueued, unpreparedQueue, prepareObserved, busy]

theorem preparing_queue_keeps_risk_budget {m : Nat}
    (state : RoundState m) (input : FeedbackInput m) (queue : List (PolicyObservation m)) :
    (preparedState state (prepareQueued state input queue)).limit = state.limit ∧
    (preparedState state (prepareQueued state input queue)).records = state.records := by
  cases queue with
  | nil => exact ⟨rfl, rfl⟩
  | cons row rest => exact preparing_observation_keeps_risk_budget state input (.known row)

structure Continuation (m : Nat) where
  measurement : MeasurementResult
  observation : Result (PolicyObservation m)
  advice : Result (PolicyAdvice m)
  preparation : Result (RoundState m)
  post : State m

def continueBusiness {m : Nat} (state : State m) (measurement : MeasurementInput m)
    (policy : PolicyInput m) (feedback : FeedbackInput m) : Continuation m :=
  let measured := measureReported state.business measurement
  let observed := consumeMeasurement measurement.environment measured measurement.treatment measurement.treatments
  let rows := recordObservation state.policyRows observed
  let advice := adviseRecorded measurement.dictionary.context policy rows
  let queued := enqueueObserved state.observationHistory state.feedbackQueue observed
  let prepared := prepareQueued state.learning feedback queued.2
  ⟨measured, observed, advice, prepared,
    {state with
      learning := preparedState state.learning prepared
      policyRows := rows
      lastObservation := observed
      observationHistory := queued.1
      feedbackQueue := unpreparedQueue queued.2 prepared}⟩

theorem continuation_does_not_repeat_business_execution {m : Nat} (state : State m)
    (measurement : MeasurementInput m) (policy : PolicyInput m) (feedback : FeedbackInput m) :
    (continueBusiness state measurement policy feedback).post.business = state.business := rfl

theorem continuation_feedback_is_the_actual_measured_result {m : Nat} (state : State m)
    (measurement : MeasurementInput m) (policy : PolicyInput m) (feedback : FeedbackInput m)
    (row : PolicyObservation m)
    (observed : (continueBusiness state measurement policy feedback).observation = .known row) :
    ∃ post, state.business.current = some post ∧ row.measured.actualPost = post ∧
      row.measured.dictionary = measurement.dictionary ∧ row.measured.rows = measurement.rows := by
  have actual := measured_policy_row_preserves_actual_output measurement.environment
    (measureReported state.business measurement) measurement.treatment measurement.treatments row observed
  exact measurement_reads_the_reported_post_only state.business measurement row.measured actual.1

def retryFeedback {m : Nat} (state : State m) (input : FeedbackInput m) : State m :=
  let prepared := prepareQueued state.learning input state.feedbackQueue
  {state with
    learning := preparedState state.learning prepared
    feedbackQueue := unpreparedQueue state.feedbackQueue prepared}

def assess {m : Nat} (state : State m) (request : RoundRequest m)
    (samples : List (SamplingReceipt m)) (permits : List (LoadPermit m)) : State m :=
  {state with learning := (finishAdaptiveRound state.learning request samples permits).post}

theorem assessment_passes_actual_post_to_next_model {m : Nat}
    (state : State m) (request : RoundRequest m) (samples : List (SamplingReceipt m))
    (permits : List (LoadPermit m)) :
    (assess state request samples permits).learning =
      (finishAdaptiveRound state.learning request samples permits).post ∧
    (assess state request samples permits).business = state.business := ⟨rfl, rfl⟩

structure ActionInput (W : Type) (m : Nat) where
  legal : LegalInput W
  model : ActionModel W Ledger.Handle
  proposals : List Proposal
  request : DecisionRequest m
  calibration : CalibrationPacket m
  calibrationCatalog : List (CalibrationPacket m)
  radius : ℚ
  exponent : Nat
  utility : ℚ → ℚ
  grants : List Authorization.Grant

structure ActionOutput (W : Type) (m : Nat) where
  run : Option (LoadedRun W m)
  post : State m

def act {W : Type} {m : Nat} (state : State m) (input : ActionInput W m) : ActionOutput W m :=
  match state.business.current with
  | none => ⟨none, state⟩
  | some initial =>
      let actual := runLoaded input.legal input.model input.proposals state.learning input.request
        input.calibration input.calibrationCatalog input.radius input.exponent input.utility input.grants initial
      ⟨some actual, {state with business := actual.execution.payment}⟩

theorem unresolved_business_has_no_new_action {W : Type} {m : Nat}
    (state : State m) (input : ActionInput W m) (unknown : state.business.current = none) :
    (act state input).run = none ∧ (act state input).post = state := by
  simp [act, unknown]

theorem actual_action_reads_current_handle_and_loaded_state {W : Type} {m : Nat}
    (state : State m) (input : ActionInput W m) (out : LoadedRun W m)
    (called : (act state input).run = some out) :
    ∃ initial, state.business.current = some initial ∧
      out = runLoaded input.legal input.model input.proposals state.learning input.request
        input.calibration input.calibrationCatalog input.radius input.exponent input.utility input.grants initial ∧
      (act state input).post.business = out.execution.payment := by
  cases actual : state.business.current with
  | none => simp [act, actual] at called
  | some initial =>
      simp only [act, actual, Option.some.injEq] at called
      subst out
      exact ⟨initial, rfl, rfl, by simp [act, actual]⟩

theorem next_action_reads_actual_assessment_post {W : Type} {m : Nat}
    (state : State m) (round : RoundRequest m) (samples : List (SamplingReceipt m))
    (permits : List (LoadPermit m)) (input : ActionInput W m) (out : LoadedRun W m)
    (selected : IntervalDecision m)
    (called : (act (assess state round samples permits) input).run = some out)
    (chosen : out.decision = .known selected) :
    selected.probability.fitted =
      (readLoaded (finishAdaptiveRound state.learning round samples permits).post.service).fitted := by
  obtain ⟨initial, _, exactRun, _⟩ := actual_action_reads_current_handle_and_loaded_state
    (assess state round samples permits) input out called
  rw [exactRun] at chosen
  exact (loaded_run_choice_uses_current_model input.legal input.model input.proposals
    (assess state round samples permits).learning input.request input.calibration input.calibrationCatalog
    input.radius input.exponent input.utility input.grants initial selected chosen).1

structure Episode (W : Type) (m : Nat) where
  action : ActionOutput W m
  continuation : Continuation m

def episode {W : Type} {m : Nat} (state : State m) (action : ActionInput W m)
    (measurement : MeasurementInput m) (policy : PolicyInput m) (feedback : FeedbackInput m) : Episode W m :=
  let actual := act state action
  ⟨actual, continueBusiness actual.post measurement policy feedback⟩

def KnownBusinessInvariant {m : Nat} (state : State m) : Prop :=
  ∀ post, state.business.current = some post → Trace.Invariant post

theorem action_preserves_every_reported_business_state {W : Type} {m : Nat}
    (state : State m) (input : ActionInput W m) (valid : KnownBusinessInvariant state) :
    KnownBusinessInvariant (act state input).post := by
  intro final reported
  cases actual : state.business.current with
  | none => simp [act, actual] at reported
  | some initial =>
      have accepted : (runLoaded input.legal input.model input.proposals state.learning input.request
          input.calibration input.calibrationCatalog input.radius input.exponent input.utility input.grants
          initial).execution.payment.current = some final := by simpa [act, actual] using reported
      exact loaded_run_preserves_reported_business_invariant input.legal input.model input.proposals
        state.learning input.request input.calibration input.calibrationCatalog input.radius input.exponent
        input.utility input.grants initial final (valid initial actual) accepted

theorem episode_consumes_actual_output_and_keeps_invariants {W : Type} {m : Nat}
    (state : State m) (action : ActionInput W m) (measurement : MeasurementInput m)
    (policy : PolicyInput m) (feedback : FeedbackInput m) (valid : KnownBusinessInvariant state) :
    KnownBusinessInvariant (episode state action measurement policy feedback).continuation.post ∧
    (episode state action measurement policy feedback).continuation.post.learning.limit = state.learning.limit ∧
    (episode state action measurement policy feedback).continuation.post.learning.records = state.learning.records := by
  have business := action_preserves_every_reported_business_state state action valid
  have budget := preparing_queue_keeps_risk_budget (act state action).post.learning feedback
    (enqueueObserved (act state action).post.observationHistory (act state action).post.feedbackQueue
      (continueBusiness (act state action).post measurement policy feedback).observation).2
  have learner : (act state action).post.learning = state.learning := by
    cases actual : state.business.current <;> simp [act, actual]
  exact ⟨business, budget.1.trans (congrArg RoundState.limit learner),
    budget.2.trans (congrArg RoundState.records learner)⟩

inductive Command (W : Type) (m : Nat) where
  | episode (action : ActionInput W m) (measurement : MeasurementInput m)
      (policy : PolicyInput m) (feedback : FeedbackInput m)
  | assess (request : RoundRequest m) (samples : List (SamplingReceipt m)) (permits : List (LoadPermit m))
  | retry (input : FeedbackInput m)
  | learner (next : RoundLearner) (catalog : List LearnerPermit) (permit : LearnerPermit)

def step {W : Type} {m : Nat} (state : State m) : Command W m → State m
  | .episode action measurement policy feedback => (episode state action measurement policy feedback).continuation.post
  | .assess request samples permits => assess state request samples permits
  | .retry input => retryFeedback state input
  | .learner next catalog permit => {state with learning := changeRoundLearner state.learning next catalog permit}

theorem each_command_preserves_known_business_and_learning_budget {W : Type} {m : Nat}
    (state : State m) (command : Command W m) (valid : KnownBusinessInvariant state)
    (bounded : roundSpent state.learning ≤ state.learning.limit) :
    KnownBusinessInvariant (step state command) ∧
    (step state command).learning.limit = state.learning.limit ∧
    roundSpent (step state command).learning ≤ state.learning.limit := by
  cases command with
  | episode action measurement policy feedback =>
      have result := episode_consumes_actual_output_and_keeps_invariants state action measurement policy feedback valid
      exact ⟨result.1, result.2.1, by simpa only [step, roundSpent, result.2.2] using bounded⟩
  | assess request samples permits =>
      have result := every_round_action_keeps_budget_bound state.learning (.assess request samples permits) bounded
      exact ⟨valid, result.1, result.2⟩
  | retry input =>
      have result := preparing_queue_keeps_risk_budget state.learning input state.feedbackQueue
      exact ⟨valid, result.1, by simpa only [step, retryFeedback, roundSpent, result.2] using bounded⟩
  | learner next catalog permit =>
      have result := every_round_action_keeps_budget_bound state.learning (.learner next catalog permit) bounded
      exact ⟨valid, result.1, result.2⟩

theorem arbitrary_finite_commands_consume_actual_posts {W : Type} {m : Nat}
    (commands : List (Command W m)) (state : State m) (valid : KnownBusinessInvariant state)
    (bounded : roundSpent state.learning ≤ state.learning.limit) :
    KnownBusinessInvariant (commands.foldl step state) ∧
    (commands.foldl step state).learning.limit = state.learning.limit ∧
    roundSpent (commands.foldl step state).learning ≤ state.learning.limit := by
  induction commands generalizing state with
  | nil => exact ⟨valid, rfl, bounded⟩
  | cons command rest ih =>
      have one := each_command_preserves_known_business_and_learning_budget state command valid bounded
      have tail := ih (step state command) one.1 (by simpa only [one.2.1] using one.2.2)
      simpa only [List.foldl_cons, one.2.1] using tail

end JurisLean.Candidates.BusinessFeedbackLoop20261027
