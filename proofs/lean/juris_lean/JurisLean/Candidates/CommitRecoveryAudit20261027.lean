import JurisLean.Candidates.CommitRecovery20261027
import JurisLean.Candidates.SourceActionAudit20261027

#check JurisLean.Candidates.PendingCommit20261027.unknown_outcome_keeps_request_identity
#print axioms JurisLean.Candidates.PendingCommit20261027.unknown_outcome_keeps_request_identity
#check JurisLean.Candidates.PendingCommit20261027.captured_pending_has_actual_prefix_and_stopped_result
#print axioms JurisLean.Candidates.PendingCommit20261027.captured_pending_has_actual_prefix_and_stopped_result
#check JurisLean.Candidates.PendingCommit20261027.stopped_interpreter_always_has_pending
#print axioms JurisLean.Candidates.PendingCommit20261027.stopped_interpreter_always_has_pending
#check JurisLean.Candidates.PendingCommit20261027.captured_prestate_inherits_full_invariant
#print axioms JurisLean.Candidates.PendingCommit20261027.captured_prestate_inherits_full_invariant
#check JurisLean.Candidates.CommitReadback20261027.checked_post_is_exact_commit_or_fenced_absence
#print axioms JurisLean.Candidates.CommitReadback20261027.checked_post_is_exact_commit_or_fenced_absence
#check JurisLean.Candidates.CommitReadback20261027.resolved_readback_binds_catalog_full_request_and_actual_unknown
#print axioms JurisLean.Candidates.CommitReadback20261027.resolved_readback_binds_catalog_full_request_and_actual_unknown
#check JurisLean.Candidates.CommitReadback20261027.resolved_readback_is_reported_state_and_step_or_frame
#print axioms JurisLean.Candidates.CommitReadback20261027.resolved_readback_is_reported_state_and_step_or_frame
#check JurisLean.Candidates.CommitReadback20261027.recovered_actual_pending_preserves_full_invariant
#print axioms JurisLean.Candidates.CommitReadback20261027.recovered_actual_pending_preserves_full_invariant
#check JurisLean.Candidates.CommitRecovery20261027.pending_for_retains_actual_plan
#print axioms JurisLean.Candidates.CommitRecovery20261027.pending_for_retains_actual_plan
#check JurisLean.Candidates.CommitRecovery20261027.unknown_selected_execution_is_actual_trajectory
#print axioms JurisLean.Candidates.CommitRecovery20261027.unknown_selected_execution_is_actual_trajectory
#check JurisLean.Candidates.CommitRecovery20261027.captured_pending_comes_from_actual_action_trajectory
#print axioms JurisLean.Candidates.CommitRecovery20261027.captured_pending_comes_from_actual_action_trajectory
#check JurisLean.Candidates.CommitRecovery20261027.actual_unknown_action_always_has_capture
#print axioms JurisLean.Candidates.CommitRecovery20261027.actual_unknown_action_always_has_capture
#check JurisLean.Candidates.CommitRecovery20261027.known_resolution_matches_current_capture
#print axioms JurisLean.Candidates.CommitRecovery20261027.known_resolution_matches_current_capture
#check JurisLean.Candidates.CommitRecovery20261027.stale_resolution_cannot_replace_later_state
#print axioms JurisLean.Candidates.CommitRecovery20261027.stale_resolution_cannot_replace_later_state
#check JurisLean.Candidates.CommitRecovery20261027.refusal_preserves_complete_current_state
#print axioms JurisLean.Candidates.CommitRecovery20261027.refusal_preserves_complete_current_state
#check JurisLean.Candidates.CommitRecovery20261027.recovery_keeps_learning_observations_and_original_outcomes
#print axioms JurisLean.Candidates.CommitRecovery20261027.recovery_keeps_learning_observations_and_original_outcomes
#check JurisLean.Candidates.CommitRecovery20261027.recovery_preserves_known_business_invariant
#print axioms JurisLean.Candidates.CommitRecovery20261027.recovery_preserves_known_business_invariant
#check JurisLean.Candidates.CommitRecovery20261027.finite_continuation_consumes_recovered_actual_state
#print axioms JurisLean.Candidates.CommitRecovery20261027.finite_continuation_consumes_recovered_actual_state

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.IntervalDecisionConsumer20261027
open JurisLean.Candidates.DecisionTrajectoryConsumer20261027
open JurisLean.Candidates.ValidatedFeedbackLoad20261027
open JurisLean.Candidates.AdaptiveRoundLedger20261027
open JurisLean.Candidates.LegalActionDomain20261027
open JurisLean.Candidates.LoadedLegalConsumer20261027
open JurisLean.Candidates.BusinessFeedbackLoop20261027
open JurisLean.Candidates.SourceOpening20261027
open JurisLean.Candidates.SourceAction20261027
open JurisLean.Candidates.PendingCommit20261027
open JurisLean.Candidates.CommitReadback20261027
open JurisLean.Candidates.CommitRecovery20261027

namespace JurisLean.Candidates.CommitRecovery20261027.Audit

def first : PaymentRequest :=
  ⟨⟨10⟩, ⟨1000⟩, SourceAction20261027.Audit.payload 10, .yes, some ⟨10⟩⟩

def second : PaymentRequest :=
  ⟨⟨11⟩, ⟨1001⟩, SourceAction20261027.Audit.payload 11, .yes, some ⟨11⟩⟩

def unknownSteps : List Instruction := [.pay first .submit, .pay second .unknownCommit]

def unknownPlans : List PlanSpec := SourceAction20261027.Audit.specs.map fun spec =>
  {spec with calls := [⟨.first, ⟨1000⟩, .submit⟩, ⟨.second, ⟨1001⟩, .unknownCommit⟩]}

-- Hypothetical successful action effects remain nonempty despite the client's
-- unknown receipt. These are independently supplied legal-model meanings, not
-- an assertion that the external server has actually committed.
def unknownModel : ActionModel (List Nat) Ledger.Handle :=
  {SourceAction20261027.Audit.model with
    meanings := unknownPlans.map (fun spec => LegalActionDomain20261027.Audit.meaning
      SourceAction20261027.Audit.gamma ⟨spec.quote, unknownSteps⟩ 2) ++
      unknownPlans.map (fun spec => LegalActionDomain20261027.Audit.meaning
        {SourceAction20261027.Audit.gamma with interpretation := 2} ⟨spec.quote, unknownSteps⟩ 5)
    successors := fun _ _ before _ =>
      match (runTrajectory SourceAction20261027.Audit.grants before
        SourceAction20261027.Audit.independentSteps).current with
      | some after => [after]
      | none => []}

def fixture (service : Service 2) : Option (Captured (List Nat) 2 × Readback) :=
  let learning := (BusinessFeedbackLoop20261027.Audit.initial service).learning
  match openingFor SourceAction20261027.Audit.legalInput with
  | .known opening => match initialState opening learning with
      | .known initial =>
          let settings := {SourceAction20261027.Audit.settings learning with
            model := unknownModel, plans := unknownPlans}
          let ticket := capture initial (actionInput SourceAction20261027.Audit.legalInput settings
            (planResults opening unknownPlans))
          -- The external fixture is declared from the independent full requests,
          -- not copied from ticket.pending or from the resolver's output.
          let before := (Ledger.commitPayment opening.handle first).2
          let committed := Ledger.commitPayment before second
          some (ticket, ⟨⟨9001⟩, before, second, committed.2, .committed committed.1⟩)
      | _ => none
  | _ => none

def check (test : Captured (List Nat) 2 → Readback → Bool) : Bool :=
  ValidatedFeedbackLoadFixture.check fun service _ =>
    match fixture service with | some (ticket, report) => test ticket report | none => false

def absent (report : Readback) : Readback :=
  {report with source := ⟨9002⟩, after := report.before, disposition := .fencedAbsent ⟨9003⟩}

def nextInput (state : State 2) : Option (ActionInput (List Nat) 2) :=
  match openingFor SourceAction20261027.Audit.legalInput with
  | .known opening =>
      let settings := SourceAction20261027.Audit.settings state.learning
      some (actionInput SourceAction20261027.Audit.legalInput settings
        (planResults opening settings.plans))
  | _ => none

/-- info: true -/
#guard_msgs in
#eval check fun ticket report => match ticket.pending, ticket.actual.run with
  | some pending, some actual => decide (
      ticket.actual.post.business.current = none ∧
      actual.execution.proposal.map (fun p => p.steps) = some unknownSteps ∧
      pending.before = report.before ∧ pending.request = second ∧ pending.mode = Ledger.Submission.unknownCommit ∧
      pending.before.state.paid = 7 ∧ pending.before.state.allocated = 7 ∧
      pending.remaining = [] ∧ ticket.actual.post.business.outcomes.length = 2 ∧
      ticket.actual.post.business.outcomes.getLast? = some (Ledger.Outcome.unknownCommit ⟨11⟩ ⟨1001⟩))
  | _, _ => false

/-- info: true -/
#guard_msgs in
#eval check fun ticket report =>
  let result := resume ticket ticket.actual.post [report] report
  decide (result.decision = Result.known report.after ∧ result.post.business.current = some report.after ∧
    report.after.state.paid = 14 ∧ report.after.state.allocated = 10 ∧ report.after.state.surplus = 4 ∧
    report.after.state.receipts.length = 2 ∧ result.post.business.outcomes = ticket.actual.post.business.outcomes ∧
    result.post.learning = ticket.actual.post.learning)

/-- info: true -/
#guard_msgs in
#eval check fun ticket report =>
  let firstRecovery := resume ticket ticket.actual.post [report] report
  let repeated := resume ticket firstRecovery.post [report] report
  decide (repeated.decision = Result.rejected Error.prestateRequired ∧ repeated.post = firstRecovery.post)

/-- info: true -/
#guard_msgs in
#eval check fun ticket report =>
  let result := resume ticket ticket.actual.post [] report
  decide (result.decision = Result.unknown Error.missingEvidence ∧ result.post = ticket.actual.post)

/-- info: true -/
#guard_msgs in
#eval check fun ticket report =>
  let wrong := {report with request := {report.request with attempt := ⟨1002⟩}}
  let result := resume ticket ticket.actual.post [wrong] wrong
  decide (result.decision = Result.unknown Error.missingEvidence ∧ result.post = ticket.actual.post)

/-- info: true -/
#guard_msgs in
#eval check fun ticket report =>
  let wrong := {report with request := {report.request with key := ⟨12⟩}}
  decide ((resume ticket ticket.actual.post [wrong] wrong).decision = Result.unknown Error.missingEvidence)

/-- info: true -/
#guard_msgs in
#eval check fun ticket report =>
  let wrong := {report with request := {report.request with
    payload := {report.request.payload with amount := ⟨8, report.request.payload.amount.tag⟩}}}
  decide ((resume ticket ticket.actual.post [wrong] wrong).decision = Result.unknown Error.missingEvidence)

/-- info: true -/
#guard_msgs in
#eval check fun ticket report =>
  let wrong := {report with before := {report.before with
    gamma := {report.before.gamma with caseRevision := report.before.gamma.caseRevision + 1}}}
  decide ((resume ticket ticket.actual.post [wrong] wrong).decision = Result.unknown Error.missingEvidence)

/-- info: true -/
#guard_msgs in
#eval check fun ticket report =>
  let later := {report with after := {report.after with revision := report.after.revision + 1}}
  let result := resume ticket ticket.actual.post [later] later
  decide (result.decision = Result.rejected Error.stageFrameMismatch ∧ result.post = ticket.actual.post)

/-- info: true -/
#guard_msgs in
#eval check fun ticket report =>
  let wrong := {report with after := {report.after with state := {report.after.state with receipts := []}}}
  decide ((resume ticket ticket.actual.post [wrong] wrong).decision = Result.rejected Error.stageFrameMismatch)

/-- info: true -/
#guard_msgs in
#eval check fun ticket report =>
  let noncommit := absent report
  let result := resume ticket ticket.actual.post [noncommit] noncommit
  decide (result.decision = Result.known report.before ∧ result.post.business.current = some report.before ∧
    report.before.state.paid = 7 ∧ (⟨10⟩ : PaymentId) ∈ report.before.state.used ∧
    (⟨11⟩ : PaymentId) ∉ report.before.state.used ∧ result.post.learning = ticket.actual.post.learning)

/-- info: true -/
#guard_msgs in
#eval check fun ticket report =>
  let wrong := {absent report with after := report.after}
  decide ((resume ticket ticket.actual.post [wrong] wrong).decision = Result.rejected Error.stageFrameMismatch)

/-- info: true -/
#guard_msgs in
#eval check fun ticket report =>
  let limited := capture ticket.before {ticket.input with grants := [trajectoryGrant
    SourceAction20261027.Audit.gamma (SourceAction20261027.Audit.payload 10)]}
  let result := resume limited limited.actual.post [report] report
  decide (limited.pending.isSome ∧ result.decision = Result.unknown Error.notIdentified ∧
    result.post = limited.actual.post)

/-- info: true -/
#guard_msgs in
#eval check fun ticket report =>
  let wrong := {report with request := {report.request with
    payload := {report.request.payload with normVersion := report.request.payload.normVersion + 1}}}
  decide ((resume ticket ticket.actual.post [wrong] wrong).decision = Result.unknown Error.missingEvidence)

/-- info: true -/
#guard_msgs in
#eval check fun ticket _ =>
  let measured := continueBusiness ticket.actual.post SourceAction20261027.Audit.measurement
    BusinessFeedbackLoop20261027.Audit.policy BusinessFeedbackLoop20261027.Audit.feedback
  decide ((act ticket.actual.post ticket.input).run.isNone ∧
    measured.post.business.current = none ∧ measured.post.learning = ticket.actual.post.learning)

/-- info: true -/
#guard_msgs in
#eval check fun ticket report =>
  let result := resume ticket ticket.actual.post [report] report
  let measured := continueBusiness result.post SourceAction20261027.Audit.measurement
    BusinessFeedbackLoop20261027.Audit.policy BusinessFeedbackLoop20261027.Audit.feedback
  match measured.observation with
  | .known observed => decide (observed.measured.actualPost = report.after ∧
      observed.measured.measuredTotal = 10 ∧ observed.measured.label = true ∧
      measured.post.learning.pending.isSome)
  | _ => false

/-- info: true -/
#guard_msgs in
#eval check fun ticket report =>
  let result := resume ticket ticket.actual.post [report] report
  match nextInput result.post with
  | some input =>
      let next := act result.post input
      match next.post.business.current with
      | some after => decide (after.state.paid = 14 ∧ after.state.receipts.length = 2 ∧
          next.post.business.outcomes.all (fun out => match out with | .replay _ => true | _ => false))
      | none => false
  | none => false

/-- info: true -/
#guard_msgs in
#eval check fun ticket report =>
  let noncommit := absent report
  let result := resume ticket ticket.actual.post [noncommit] noncommit
  match nextInput result.post with
  | some input =>
      let next := act result.post input
      match next.post.business.current with
      | some after => decide (after.state.paid = 14 ∧ after.state.receipts.length = 2 ∧
          next.post.business.outcomes.length = 2 ∧
          next.post.business.outcomes.any (fun out => match out with | .committed _ _ => true | _ => false))
      | none => false
  | none => false

/-- info: true -/
#guard_msgs in
#eval check fun ticket report =>
  let changed := {ticket.actual.post with learning :=
    {ticket.actual.post.learning with limit := ticket.actual.post.learning.limit + 1}}
  let result := resume ticket changed [report] report
  decide (result.decision = Result.rejected Error.prestateRequired ∧ result.post = changed)

/-- info: true -/
#guard_msgs in
#eval check fun ticket report =>
  let unlisted := {report with source := ⟨9010⟩}
  decide ((resume ticket ticket.actual.post [report] unlisted).decision = Result.unknown Error.missingEvidence)

/-- info: true -/
#guard_msgs in
#eval check fun ticket report => match ticket.before.business.current with
  | some initial =>
      match locate ticket.input.grants initial (unknownSteps ++ [.pay first .submit]) with
      | some pending => decide (pending.before = report.before ∧
          pending.remaining = [.pay first .submit] ∧ pending.request = second)
      | none => false
  | none => false

end JurisLean.Candidates.CommitRecovery20261027.Audit

