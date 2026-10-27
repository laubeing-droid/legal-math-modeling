import JurisLean.Candidates.CommitReadback20261027

/-!
Capture the existing loaded-model action once, then reconcile its actual unknown
payment without executing the old tail. The erased equalities in Captured bind
stored output to that computation; they do not assert safety or external truth.
The public constructor supplies them by computation. Recovery only publishes a
verified readback into the still-current captured output. It preserves learning,
observation and original unknown-result evidence. A later action must call the
ordinary legal/probability/authorization consumer again with its current state.
-/

namespace JurisLean.Candidates.CommitRecovery20261027

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.IntervalDecisionConsumer20261027
open JurisLean.Candidates.DecisionTrajectoryConsumer20261027
open JurisLean.Candidates.LegalActionDomain20261027
open JurisLean.Candidates.LoadedLegalConsumer20261027
open JurisLean.Candidates.AdaptiveRoundLedger20261027
open JurisLean.Candidates.BusinessFeedbackLoop20261027
open JurisLean.Candidates.PendingCommit20261027
open JurisLean.Candidates.CommitReadback20261027

def pendingFor {W : Type} {m : Nat} (before : State m) (input : ActionInput W m)
    (actual : ActionOutput W m) : Option Pending :=
  if actual.post.business.current = none then
    match before.business.current, actual.run with
    | some initial, some execution => match execution.execution.proposal with
        | some proposal => locate input.grants initial proposal.steps
        | none => none
    | _, _ => none
  else none

structure Captured (W : Type) (m : Nat) where
  before : State m
  input : ActionInput W m
  actual : ActionOutput W m
  pending : Option Pending
  actualComputation : actual = act before input
  pendingComputation : pending = pendingFor before input actual

def capture {W : Type} {m : Nat} (before : State m) (input : ActionInput W m) : Captured W m :=
  let actual := act before input
  ⟨before, input, actual, pendingFor before input actual, rfl, rfl⟩

theorem pending_for_retains_actual_plan {W : Type} {m : Nat}
    (before : State m) (input : ActionInput W m) (actual : ActionOutput W m)
    (pending : Pending) (found : pendingFor before input actual = some pending) :
    ∃ initial execution proposal,
      before.business.current = some initial ∧ actual.run = some execution ∧
      execution.execution.proposal = some proposal ∧
      locate input.grants initial proposal.steps = some pending ∧ actual.post.business.current = none := by
  unfold pendingFor at found
  split at found
  · rename_i stopped
    cases current : before.business.current with
    | none => simp [current] at found
    | some initial =>
        cases ran : actual.run with
        | none => simp [current, ran] at found
        | some execution =>
            cases selected : execution.execution.proposal with
            | none => simp [current, ran, selected] at found
            | some proposal =>
                exact ⟨initial, execution, proposal, current, ran, selected,
                  by simpa only [current, ran, selected] using found, stopped⟩
  · cases found

theorem unknown_selected_execution_is_actual_trajectory {m : Nat}
    (selected : IntervalDecision m) (grants : List Authorization.Grant)
    (initial : Ledger.Handle) (steps : List Instruction)
    (stopped : (executeSelected selected grants initial steps).current = none) :
    executeSelected selected grants initial steps = runTrajectory grants initial steps := by
  by_cases context : initial.gamma ≠ selected.nominal.gamma
  · simp [executeSelected, context] at stopped
  · by_cases payloads : paymentPayloads steps ≠ selected.nominal.action.execution
    · simp [executeSelected, context, payloads] at stopped
    · simp only [executeSelected, if_neg context, if_neg payloads]

theorem captured_pending_comes_from_actual_action_trajectory {W : Type} {m : Nat}
    (ticket : Captured W m) (pending : Pending) (found : ticket.pending = some pending) :
    ∃ initial execution proposal,
      ticket.before.business.current = some initial ∧ ticket.actual.run = some execution ∧
      execution.execution.proposal = some proposal ∧
      execution.execution.payment = runTrajectory ticket.input.grants initial proposal.steps ∧
      locate ticket.input.grants initial proposal.steps = some pending ∧
      ticket.actual.post.business.current = none := by
  have located : pendingFor ticket.before ticket.input ticket.actual = some pending :=
    ticket.pendingComputation.symm.trans found
  obtain ⟨initial, execution, proposal, reported, ran, selected, captured, stopped⟩ :=
    pending_for_retains_actual_plan ticket.before ticket.input ticket.actual pending located
  have called : (act ticket.before ticket.input).run = some execution := by
    rw [← ticket.actualComputation]
    exact ran
  obtain ⟨start, started, actualRun, actualPayment⟩ :=
    actual_action_reads_current_handle_and_loaded_state ticket.before ticket.input execution called
  have same : start = initial := Option.some.inj (started.symm.trans reported)
  subst start
  have paymentFrame : ticket.actual.post.business = execution.execution.payment := by
    simpa only [ticket.actualComputation] using actualPayment
  have unknown : execution.execution.payment.current = none := by
    rw [← paymentFrame]
    exact stopped
  have linked := chosen_execution_uses_the_entire_approved_instruction_list ticket.input.request
    ticket.input.utility (review ticket.input.legal ticket.input.model initial ticket.input.proposals).allowed
    (runLoaded ticket.input.legal ticket.input.model ticket.input.proposals ticket.before.learning
      ticket.input.request ticket.input.calibration ticket.input.calibrationCatalog ticket.input.radius
      ticket.input.exponent ticket.input.utility ticket.input.grants initial).decision
    ticket.input.grants initial proposal (by simpa only [actualRun, runLoaded] using selected)
  obtain ⟨decision, _, _, _, payment⟩ := linked
  have exactPayment : execution.execution.payment =
      executeSelected decision ticket.input.grants initial proposal.steps := by
    simpa only [actualRun, runLoaded] using payment
  have executed := unknown_selected_execution_is_actual_trajectory decision ticket.input.grants initial
    proposal.steps (by simpa only [exactPayment] using unknown)
  exact ⟨initial, execution, proposal, reported, ran, selected, exactPayment.trans executed, captured, stopped⟩

def resolution {W : Type} {m : Nat} (ticket : Captured W m) (current : State m)
    (catalog : List Readback) (report : Readback) : Result Ledger.Handle :=
  if current = ticket.actual.post then
    match ticket.pending with
    | some pending => resolve pending catalog report
    | none => .unknown .notIdentified
  else .rejected .prestateRequired

theorem known_resolution_matches_current_capture {W : Type} {m : Nat}
    (ticket : Captured W m) (current : State m) (catalog : List Readback)
    (report : Readback) (after : Ledger.Handle)
    (accepted : resolution ticket current catalog report = .known after) :
    current = ticket.actual.post ∧
      ∃ pending, ticket.pending = some pending ∧ resolve pending catalog report = .known after := by
  unfold resolution at accepted
  split at accepted
  · rename_i same
    cases located : ticket.pending with
    | none => simp [located] at accepted
    | some pending => exact ⟨same, pending, located, by simpa only [located] using accepted⟩
  · cases accepted

theorem stale_resolution_cannot_replace_later_state {W : Type} {m : Nat}
    (ticket : Captured W m) (current : State m) (catalog : List Readback) (report : Readback)
    (changed : current ≠ ticket.actual.post) :
    resolution ticket current catalog report = .rejected .prestateRequired := by
  simp only [resolution, if_neg changed]

def publish {m : Nat} (current : State m) (after : Ledger.Handle) : State m :=
  {current with business := {current.business with exit := .undecided, current := some after}}

structure Recovery (m : Nat) where
  report : Readback
  decision : Result Ledger.Handle
  post : State m

def resume {W : Type} {m : Nat} (ticket : Captured W m) (current : State m)
    (catalog : List Readback) (report : Readback) : Recovery m :=
  let decision := resolution ticket current catalog report
  ⟨report, decision, match decision with
    | .known after => publish current after
    | _ => current⟩

theorem refusal_preserves_complete_current_state {W : Type} {m : Nat}
    (ticket : Captured W m) (current : State m) (catalog : List Readback) (report : Readback)
    (unresolved : ∀ after, resolution ticket current catalog report ≠ .known after) :
    (resume ticket current catalog report).post = current := by
  cases decided : resolution ticket current catalog report with
  | known after => exact False.elim (unresolved after decided)
  | unknown error => simp only [resume, decided]
  | rejected error => simp only [resume, decided]
  | conflict left right => simp only [resume, decided]

theorem recovery_keeps_learning_observations_and_original_outcomes {W : Type} {m : Nat}
    (ticket : Captured W m) (current : State m) (catalog : List Readback) (report : Readback) :
    let recovered := resume ticket current catalog report
    recovered.report = report ∧ recovered.post.learning = current.learning ∧
      recovered.post.policyRows = current.policyRows ∧
      recovered.post.lastObservation = current.lastObservation ∧
      recovered.post.observationHistory = current.observationHistory ∧
      recovered.post.feedbackQueue = current.feedbackQueue ∧
      recovered.post.business.outcomes = current.business.outcomes ∧
      recovered.post.business.obligations = current.business.obligations := by
  cases decided : resolution ticket current catalog report <;> simp [resume, decided, publish]

theorem recovery_preserves_known_business_invariant {W : Type} {m : Nat}
    (ticket : Captured W m) (current : State m) (catalog : List Readback) (report : Readback)
    (originalValid : KnownBusinessInvariant ticket.before) (currentValid : KnownBusinessInvariant current) :
    KnownBusinessInvariant (resume ticket current catalog report).post := by
  intro final reported
  cases decided : resolution ticket current catalog report with
  | known after =>
      have same : after = final := by simpa only [resume, decided, publish, Option.some.injEq] using reported
      subst final
      obtain ⟨_, pending, found, accepted⟩ :=
        known_resolution_matches_current_capture ticket current catalog report after decided
      obtain ⟨initial, execution, proposal, initialReported, _, _, _, located, _⟩ :=
        captured_pending_comes_from_actual_action_trajectory ticket pending found
      exact recovered_actual_pending_preserves_full_invariant ticket.input.grants proposal.steps initial
        pending catalog report after (originalValid initial initialReported) located accepted
  | unknown error => exact currentValid final (by simpa only [resume, decided] using reported)
  | rejected error => exact currentValid final (by simpa only [resume, decided] using reported)
  | conflict left right => exact currentValid final (by simpa only [resume, decided] using reported)

theorem finite_continuation_consumes_recovered_actual_state {W : Type} {m : Nat}
    (ticket : Captured W m) (current : State m) (catalog : List Readback) (report : Readback)
    (commands : List (Command W m)) (originalValid : KnownBusinessInvariant ticket.before)
    (currentValid : KnownBusinessInvariant current) (bounded : roundSpent current.learning ≤ current.learning.limit) :
    KnownBusinessInvariant (commands.foldl step (resume ticket current catalog report).post) ∧
      (commands.foldl step (resume ticket current catalog report).post).learning.limit = current.learning.limit ∧
      roundSpent (commands.foldl step (resume ticket current catalog report).post).learning ≤ current.learning.limit := by
  have frame := (recovery_keeps_learning_observations_and_original_outcomes ticket current catalog report).2.1
  have continued := arbitrary_finite_commands_consume_actual_posts commands
    (resume ticket current catalog report).post
    (recovery_preserves_known_business_invariant ticket current catalog report originalValid currentValid)
    (by simpa only [frame] using bounded)
  simpa only [frame] using continued

end JurisLean.Candidates.CommitRecovery20261027
