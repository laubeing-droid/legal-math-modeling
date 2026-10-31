import JurisLean.Candidates.BusinessFeedbackLoop20261027
import JurisLean.Candidates.U00RSICandidateBridge20261031

noncomputable section

namespace JurisLean.Candidates.U00MeasuredRSIEntry20261031

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.LearningConsumer20261027
open JurisLean.Candidates.EventFeedbackConsumer20261027
open JurisLean.Candidates.ProtectedFeedback20261027
open JurisLean.Candidates.AdaptiveRoundLedger20261027
open JurisLean.Candidates.BusinessMeasurement20261027
open JurisLean.Candidates.MeasuredPolicy20261027
open JurisLean.Candidates.BusinessFeedbackLoop20261027

open JurisLean.Candidates.U00RSICandidateBridge20261031

/-!
U00 L756/L758/L759, edges 12--13. This entry observes an already reported
business result. It does not run the payment instructions again. The source
catalogs and their real-world interpretation retain their original contracts.
-/

def policyLog {m : Nat} (row : PolicyObservation m) : Behavior.MeasurementLog :=
  { unit := row.measured.dictionary.unit
    event := row.measured.dictionary.event
    record := row.measured.dictionary.resultRecord
    targetVersion := row.measured.dictionary.targetVersion
    mechanismVersion := row.measured.dictionary.context.mechanismVersion
    windowEnd := row.measured.dictionary.windowEnd
    observedAt := row.measured.observedAt
    outcome := some row.measured.label
    positiveWitness := if row.measured.label then some row.treatment.outcomeSource else none
    externalSource := row.treatment.outcomeSource }

def policyMeaning {m : Nat} (row : PolicyObservation m) : LogMeaning m :=
  { log := policyLog row
    caseId := row.measured.dictionary.context.caseId
    feature := row.treatment.feature }

private theorem accepted_log_checks {m : Nat}
    (business : Pipeline.PaymentRun) (input : MeasurementInput m)
    (row : PolicyObservation m)
    (accepted : consumeMeasurement input.environment (measureReported business input)
      input.treatment input.treatments = .known row) :
    (policyLog row).targetVersion = row.treatment.environment.dataScope.target ∧
      (policyLog row).mechanismVersion =
        row.treatment.environment.dataScope.mechanismVersion ∧
      Behavior.proposed_measurement row.treatment.environment.dataScope.target
        (policyLog row) = .known row.measured.label := by
  have actual := measured_policy_row_preserves_actual_output input.environment
    (measureReported business input) input.treatment input.treatments row accepted
  have matched : treatmentMatches input.environment row.measured row.treatment
      input.treatments = true := by
    simpa only [actual.2.1] using actual.2.2
  have checks := of_decide_eq_true matched
  rcases checks with
    ⟨_, environment, _, _, _, _, _, mechanism, target, _⟩
  have ht : row.measured.dictionary.targetVersion =
      row.treatment.environment.dataScope.target := by
    simpa only [environment] using target
  have hm : row.measured.dictionary.context.mechanismVersion =
      row.treatment.environment.dataScope.mechanismVersion := by
    simpa only [environment] using mechanism
  refine ⟨ht, hm, ?_⟩
  cases label : row.measured.label with
  | true =>
      simp [policyLog, Behavior.proposed_measurement, ht, label]
  | false =>
      obtain ⟨post, reported, _⟩ :=
        measurement_reads_the_reported_post_only business input row.measured actual.1
      have measured : measureBusiness post input.dictionary input.now input.sources
          input.closures input.rows = .measured row.measured := by
        simpa only [measureReported, reported] using actual.1
      have bound := measurement_reads_actual_state_and_rows post input.dictionary
        input.now input.sources input.closures input.rows row.measured measured
      have closed := negative_requires_complete_closed_window post input.dictionary
        input.now input.sources input.closures input.rows row.measured measured label
      have time : row.measured.dictionary.windowEnd.ticks ≤ row.measured.observedAt.ticks := by
        simpa only [bound.2.1, bound.2.2.2.1] using closed.2.1
      simp [policyLog, Behavior.proposed_measurement, ht, label, time]

/-- Edges 12--13: the actual accepted measurement produces a log whose unique
whole-log interpretation is exactly the existing complete feedback observation.
A negative is justified by the original closed-window theorem. -/
theorem actual_policy_log_recovers_full_observation {m : Nat}
    (business : Pipeline.PaymentRun) (input : MeasurementInput m)
    (row : PolicyObservation m)
    (accepted : consumeMeasurement input.environment (measureReported business input)
      input.treatment input.treatments = .known row) :
    Behavior.proposed_measurement row.treatment.environment.dataScope.target
        (policyLog row) = .known row.measured.label ∧
      interpretLog row.treatment.environment.dataScope [policyMeaning row]
        (policyLog row) = .known (measuredFeedback row) ∧
      ∀ (meanings : List (LogMeaning m)) (out : Observation m),
        interpretLog row.treatment.environment.dataScope
          (meanings ++ [policyMeaning row]) (policyLog row) = .known out →
        out = measuredFeedback row := by
  have checks := accepted_log_checks business input row accepted
  have sameMechanism := not_ne_iff.mpr checks.2.1
  refine ⟨checks.2.2, ?_, ?_⟩
  · simp only [interpretLog, checks.2.2]
    rw [if_neg sameMechanism]
    simp [policyMeaning, measuredFeedback, policyLog]
  · intro meanings out known
    have single :
        ([policyMeaning row].filter
          (fun entry => decide (entry.log = policyLog row))) = [policyMeaning row] := by
      simp [policyMeaning]
    simp only [interpretLog, checks.2.2, if_neg sameMechanism,
      List.filter_append, single] at known
    cases found : meanings.filter (fun entry => decide (entry.log = policyLog row)) with
    | nil =>
        simp only [found, List.nil_append] at known
        simpa only [Result.known.injEq, policyMeaning, measuredFeedback, policyLog] using known.symm
    | cons entry rest =>
        cases rest <;> simp [found] at known

private theorem interpreted_append_last {m : Nat} (scope : DataScope)
    (meanings : List (LogMeaning m)) (logs : List Behavior.MeasurementLog)
    (lastLog : Behavior.MeasurementLog) (rows : List (Observation m))
    (known : interpretLogs scope meanings (logs ++ [lastLog]) = .known rows) :
    ∃ preceding : List (Observation m), ∃ out : Observation m,
      rows = preceding ++ [out] ∧ interpretLog scope meanings lastLog = .known out := by
  induction logs generalizing rows with
  | nil =>
      cases value : interpretLog scope meanings lastLog with
      | unknown e => simp [interpretLogs, value] at known
      | rejected e => simp [interpretLogs, value] at known
      | conflict a b => simp [interpretLogs, value] at known
      | known out =>
          have same : [out] = rows := by simpa [interpretLogs, value] using known
          exact ⟨[], out, same.symm, rfl⟩
  | cons log logs ih =>
      cases first : interpretLog scope meanings log with
      | unknown e => simp [interpretLogs, first] at known
      | rejected e => simp [interpretLogs, first] at known
      | conflict a b => simp [interpretLogs, first] at known
      | known head =>
          cases tail : interpretLogs scope meanings (logs ++ [lastLog]) with
          | unknown e => simp [interpretLogs, first, tail] at known
          | rejected e => simp [interpretLogs, first, tail] at known
          | conflict a b => simp [interpretLogs, first, tail] at known
          | known middle =>
              have same : head :: middle = rows := by
                simpa [interpretLogs, first, tail] using known
              obtain ⟨preceding, out, ordered, actual⟩ := ih middle tail
              refine ⟨head :: preceding, out, ?_, actual⟩
              rw [← same, ordered]
              rfl

structure PersonalPreparation (m : Nat) where
  rsi : RSI.State
  result : Result (RoundState m)

def failedPreparation {m : Nat} (before : RSI.State)
    (result : Result (RoundState m)) : PersonalPreparation m :=
  ⟨before, result⟩

/-- This private entry processes the current accepted row, never an unproved
old queue head. Existing meanings remain subject to the original unique lookup. -/
private def prepareCurrent {m : Nat} (round : RoundState m) (before : RSI.State)
    (query : Fin m) (evidence : SourceRef) (request : RSI.PredictionRequest)
    (now : Instant) (meanings : List (LogMeaning m)) (plan : ValidationPlan)
    (row : PolicyObservation m) : PersonalPreparation m :=
  let appended := RSI.appendData before (policyLog row)
  let result : Result (RoundState m) :=
    if round.pending ≠ none then .unknown .openMissingOpportunity
    else if ¬ round.records.length < round.horizon then .rejected .unsupported
    else if round.service.gamma ≠ row.measured.actualPost.gamma ∨
        round.service.journal.scope ≠ row.treatment.environment.dataScope then
      .unknown .scopeMismatch
    else
      let exchange : PersonalExchange m := ⟨round, appended, query, evidence⟩
      startPersonalRound exchange request now (meanings ++ [policyMeaning row]) plan
  ⟨appended, result⟩

private theorem prepared_current_reads_actual_entry {m : Nat}
    (round : RoundState m) (before : RSI.State) (query : Fin m)
    (evidence : SourceRef) (request : RSI.PredictionRequest) (now : Instant)
    (meanings : List (LogMeaning m)) (plan : ValidationPlan)
    (row : PolicyObservation m) (native : RoundState m)
    (known : (prepareCurrent round before query evidence request now meanings plan row).result =
      .known native) :
    round.pending = none ∧ round.records.length < round.horizon ∧
      round.service.gamma = row.measured.actualPost.gamma ∧
      round.service.journal.scope = row.treatment.environment.dataScope ∧
      startPersonalRound
        (⟨round, RSI.appendData before (policyLog row), query, evidence⟩ :
          PersonalExchange m)
        request now (meanings ++ [policyMeaning row]) plan = .known native := by
  dsimp only [prepareCurrent] at known
  split at known
  · cases known
  · rename_i notBusy
    have free : round.pending = none := by simpa only [not_not] using notBusy
    split at known
    · cases known
    · rename_i notFull
      have room : round.records.length < round.horizon := by
        simpa only [not_not] using notFull
      split at known
      · cases known
      · rename_i same
        have binding : round.service.gamma = row.measured.actualPost.gamma ∧
            round.service.journal.scope = row.treatment.environment.dataScope := by
          simpa only [not_or, not_not] using same
        exact ⟨free, room, binding.1, binding.2, known⟩

private def currentProcessed {m : Nat} (result : Result (RoundState m)) : Bool :=
  match result with
  | .known native =>
      match native.pending with
      | none => false
      | some declared =>
          decide (declared.prepared.observation.disposition = .inserted ∨
            declared.prepared.observation.disposition = .replay)
  | _ => false

private def remainingCurrent {m : Nat} (row : PolicyObservation m)
    (result : Result (RoundState m)) : List (PolicyObservation m) :=
  if currentProcessed result then [] else [row]

structure PersonalContinuation (m : Nat) where
  measurement : MeasurementResult
  observation : Result (PolicyObservation m)
  advice : Result (PolicyAdvice m)
  preparation : Result (RoundState m)
  rsi : RSI.State
  post : State m

/-- This continuation processes only its current actual accepted observation.
Semantic replays do not start a round. Old queued rows are retained unchanged;
an unprocessed current row is appended, while a processed current row is removed
only by an actual inserted/replay observation receipt, independently of fitting. -/
def continuePersonalBusiness {m : Nat} (state : State m) (before : RSI.State)
    (query : Fin m) (evidence : SourceRef) (measurement : MeasurementInput m)
    (policy : PolicyInput m) (request : RSI.PredictionRequest) (now : Instant)
    (meanings : List (LogMeaning m)) (plan : ValidationPlan) :
    PersonalContinuation m :=
  let measured := measureReported state.business measurement
  let observed := consumeMeasurement measurement.environment measured
    measurement.treatment measurement.treatments
  let rows := recordObservation state.policyRows observed
  let advice := adviseRecorded measurement.dictionary.context policy rows
  let queued := enqueueObserved state.observationHistory state.feedbackQueue observed
  let prepared := match observed with
    | .known row =>
        if state.observationHistory.any (fun old => sameObservation old row) then
          failedPreparation before (.unknown .missingEvidence)
        else prepareCurrent state.learning before query evidence request now meanings plan row
    | .unknown e => failedPreparation before (.unknown e)
    | .rejected e => failedPreparation before (.rejected e)
    | .conflict a b => failedPreparation before (.conflict a b)
  let retained := match observed with
    | .known _ =>
        if currentProcessed prepared.result then state.feedbackQueue else queued.2
    | _ => state.feedbackQueue
  ⟨measured, observed, advice, prepared.result, prepared.rsi,
    { state with
      learning := preparedState state.learning prepared.result
      policyRows := rows
      lastObservation := observed
      observationHistory := queued.1
      feedbackQueue := retained }⟩

/-- Edges 12--13: a successful actual entry processes the current accepted
measurement itself. The append, complete interpretation and native input share
that one row; no truth premise about an old typed queue head is used. -/
theorem actual_continuation_binds_accepted_row_and_native_entry {m : Nat}
    (state : State m) (before : RSI.State) (query : Fin m)
    (evidence : SourceRef) (measurement : MeasurementInput m) (policy : PolicyInput m)
    (request : RSI.PredictionRequest) (now : Instant)
    (meanings : List (LogMeaning m)) (plan : ValidationPlan) (native : RoundState m)
    (known : (continuePersonalBusiness state before query evidence measurement
      policy request now meanings plan).preparation = .known native) :
    ∃ row : PolicyObservation m,
      consumeMeasurement measurement.environment (measureReported state.business measurement)
        measurement.treatment measurement.treatments = .known row ∧
      (continuePersonalBusiness state before query evidence measurement
        policy request now meanings plan).observation = .known row ∧
      state.observationHistory.any (fun old => sameObservation old row) = false ∧
      (continuePersonalBusiness state before query evidence measurement
        policy request now meanings plan).rsi = RSI.appendData before (policyLog row) ∧
      startPersonalRound
        (⟨state.learning, RSI.appendData before (policyLog row), query, evidence⟩ :
          PersonalExchange m)
        request now (meanings ++ [policyMeaning row]) plan = .known native ∧
      interpretLog state.learning.service.journal.scope
        (meanings ++ [policyMeaning row]) (policyLog row) =
          .known (measuredFeedback row) ∧
      (∃ input : NativeInput m,
        prepareNativeInput
          (⟨state.learning, RSI.appendData before (policyLog row), query, evidence⟩ :
            PersonalExchange m)
          request now (meanings ++ [policyMeaning row]) = .known input ∧
        input.last = measuredFeedback row ∧
        native = nativeBegin
          (⟨state.learning, RSI.appendData before (policyLog row), query, evidence⟩ :
            PersonalExchange m) input now plan) ∧
      (continuePersonalBusiness state before query evidence measurement
        policy request now meanings plan).post.feedbackQueue =
          state.feedbackQueue ++ remainingCurrent row (.known native) := by
  have selected :
      ∃ row : PolicyObservation m,
        consumeMeasurement measurement.environment (measureReported state.business measurement)
          measurement.treatment measurement.treatments = .known row ∧
        state.observationHistory.any (fun old => sameObservation old row) = false ∧
        (prepareCurrent state.learning before query evidence request now meanings plan row).result =
          .known native := by
    cases observed : consumeMeasurement measurement.environment
        (measureReported state.business measurement) measurement.treatment measurement.treatments with
    | unknown e => simp [continuePersonalBusiness, observed, failedPreparation] at known
    | rejected e => simp [continuePersonalBusiness, observed, failedPreparation] at known
    | conflict a b => simp [continuePersonalBusiness, observed, failedPreparation] at known
    | known row =>
        cases seen : state.observationHistory.any (fun old => sameObservation old row) with
        | true => simp [continuePersonalBusiness, observed, seen, failedPreparation] at known
        | false =>
            exact ⟨row, rfl, seen, by
              simpa [continuePersonalBusiness, observed, seen] using known⟩
  obtain ⟨row, observed, fresh, prepared⟩ := selected
  have entry := prepared_current_reads_actual_entry state.learning before query evidence
    request now meanings plan row native prepared
  have full := actual_policy_log_recovers_full_observation state.business measurement row observed
  let exchange : PersonalExchange m :=
    ⟨state.learning, RSI.appendData before (policyLog row), query, evidence⟩
  have actual := actual_personal_round_uses_native_entry exchange request now
    (meanings ++ [policyMeaning row]) plan native entry.2.2.2.2
  rcases actual with
    ⟨input, _, _, inputKnown, nativeSame, _, _, _, _, interpreted, reversed, _⟩
  have ordered : interpretLogs state.learning.service.journal.scope
      (meanings ++ [policyMeaning row]) (before.data ++ [policyLog row]) =
        .known input.rows := by
    simpa only [exchange, RSI.appendData] using interpreted
  obtain ⟨preceding, out, rowOrder, logKnown⟩ :=
    interpreted_append_last state.learning.service.journal.scope
      (meanings ++ [policyMeaning row]) before.data (policyLog row) input.rows ordered
  have outSame : out = measuredFeedback row := by
    apply full.2.2 meanings out
    simpa only [entry.2.2.2.1] using logKnown
  have lastSame : input.last = measuredFeedback row := by
    rw [rowOrder, List.reverse_append] at reversed
    simp only [List.reverse_singleton, List.singleton_append] at reversed
    exact (List.cons.inj reversed).1.symm.trans outSame
  refine ⟨row, observed, ?_, fresh, ?_, entry.2.2.2.2, ?_,
    ⟨input, inputKnown, lastSame, nativeSame⟩, ?_⟩
  · exact observed
  · simp [continuePersonalBusiness, observed, fresh, prepareCurrent,
      entry.1, entry.2.1, entry.2.2.1, entry.2.2.2.1]
  · simpa only [outSame] using logKnown
  · cases processed : currentProcessed (.known native) <;>
      simp [continuePersonalBusiness, observed, fresh, prepared, enqueueObserved,
        remainingCurrent, processed]

/-- U00 L756/L758/L759: this entry reads the same actual observation projection
as the existing continuation and retains the already reported business result.
An unknown commit generates neither a new label nor an RSI data append. -/
theorem personal_continuation_observes_without_reexecuting {m : Nat}
    (state : State m) (before : RSI.State) (query : Fin m)
    (evidence : SourceRef) (measurement : MeasurementInput m) (policy : PolicyInput m)
    (request : RSI.PredictionRequest) (now : Instant)
    (meanings : List (LogMeaning m)) (plan : ValidationPlan)
    (feedback : FeedbackInput m) :
    let actual := continuePersonalBusiness state before query evidence measurement
      policy request now meanings plan
    actual.observation = (continueBusiness state measurement policy feedback).observation ∧
      actual.post.business = state.business ∧
      (∀ row : PolicyObservation m,
        consumeMeasurement measurement.environment (measureReported state.business measurement)
          measurement.treatment measurement.treatments = .known row →
        state.observationHistory.any (fun old => sameObservation old row) = false →
        actual.rsi = RSI.appendData before (policyLog row)) ∧
      (∀ row : PolicyObservation m,
        consumeMeasurement measurement.environment (measureReported state.business measurement)
          measurement.treatment measurement.treatments = .known row →
        state.observationHistory.any (fun old => sameObservation old row) = true →
        actual.rsi = before ∧ actual.preparation = .unknown .missingEvidence ∧
          actual.post.feedbackQueue = state.feedbackQueue) ∧
      (state.business.current = none →
        actual.observation = .unknown .missingEvidence ∧
        actual.preparation = .unknown .missingEvidence ∧
        actual.rsi = before ∧
        actual.post.learning = state.learning ∧
        actual.post.observationHistory = state.observationHistory ∧
        actual.post.feedbackQueue = state.feedbackQueue) := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · intro row accepted fresh
    simp [continuePersonalBusiness, accepted, fresh, prepareCurrent]
  · intro row accepted replay
    simp [continuePersonalBusiness, accepted, replay, failedPreparation,
      currentProcessed, enqueueObserved]
  · intro unknown
    simp [continuePersonalBusiness, measureReported, unknown, consumeMeasurement,
      failedPreparation, enqueueObserved, preparedState, currentProcessed]

end JurisLean.Candidates.U00MeasuredRSIEntry20261031
