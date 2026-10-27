import JurisLean.Candidates.SourceAction20261027

/-!
Capture the actual first unknown payment in the existing finite interpreter.
The locator is pure: it reconstructs the same mathematical transitions, never
resubmits an external payment. A captured prestate is reached through actual
committed or authorized-refresh outputs, not a caller's invented checkpoint.
The remaining instructions are retained as evidence, not executed on recovery.
-/

namespace JurisLean.Candidates.PendingCommit20261027

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.DecisionTrajectoryConsumer20261027

structure Pending where
  grants : List Authorization.Grant
  before : Ledger.Handle
  request : PaymentRequest
  mode : Ledger.Submission
  remaining : List Instruction
  deriving DecidableEq

def permission (grants : List Authorization.Grant) (before : Ledger.Handle)
    (request : PaymentRequest) : Bool :=
  Authorization.authorized grants before.gamma request.payload.payer 0
    request.payload.normVersion (.relation request.payload.relation) (some request.payload)

def locate (grants : List Authorization.Grant) (before : Ledger.Handle) :
    List Instruction → Option Pending
  | [] => none
  | .pay request mode :: rest =>
      match Ledger.consume_ext before before request (permission grants before request) mode with
      | .committed _ after => locate grants after rest
      | .replay _ => locate grants before rest
      | .unknownCommit _ _ => some ⟨grants, before, request, mode, rest⟩
      | _ => none
  | .refresh change :: rest =>
      match Pipeline.refresh grants before change with
      | .known after => locate grants after rest
      | _ => none

theorem unknown_outcome_keeps_request_identity (before : Ledger.Handle)
    (request : PaymentRequest) (allowed : Bool) (mode : Ledger.Submission)
    (key : PaymentId) (attempt : AttemptId)
    (unknown : Ledger.consume_ext before before request allowed mode = .unknownCommit key attempt) :
    key = request.key ∧ attempt = request.attempt := by
  cases receipt : Ledger.lookupReceipt before.state request.key with
  | some registered =>
      simp only [Ledger.consume_ext, receipt] at unknown
      split at unknown <;> cases unknown
  | none =>
      cases mode with
      | unknownCommit =>
          simpa only [Ledger.consume_ext, receipt, Ledger.Outcome.unknownCommit.injEq,
            eq_comm] using unknown
      | rejectedBeforeSubmit => simp [Ledger.consume_ext, receipt] at unknown
      | submit =>
          cases checked : Ledger.validationError before before request allowed with
          | none => simp [Ledger.consume_ext, receipt, checked] at unknown
          | some error => cases error <;> simp [Ledger.consume_ext, receipt, checked] at unknown

theorem captured_pending_has_actual_prefix_and_stopped_result
    (grants : List Authorization.Grant) (steps : List Instruction)
    (initial : Ledger.Handle) (pending : Pending) (found : locate grants initial steps = some pending) :
    pending.grants = grants ∧ Trace.Path initial pending.before ∧
      Ledger.consume_ext pending.before pending.before pending.request
        (permission pending.grants pending.before pending.request) pending.mode =
        .unknownCommit pending.request.key pending.request.attempt ∧
      (runTrajectory grants initial steps).current = none ∧
      Ledger.Outcome.unknownCommit pending.request.key pending.request.attempt ∈
        (runTrajectory grants initial steps).outcomes := by
  induction steps generalizing initial with
  | nil => simp [locate] at found
  | cons instruction rest ih =>
      cases instruction with
      | pay request mode =>
          cases executed : Ledger.consume_ext initial initial request
              (permission grants initial request) mode with
          | committed receipt after =>
              have tail := ih after (by simpa only [locate, executed] using found)
              dsimp only [permission] at executed
              refine ⟨tail.1, .cons (Trace.u10_2_committed_executor_is_step
                initial initial request _ mode receipt after executed) tail.2.1,
                tail.2.2.1, ?_, ?_⟩
              · simpa only [runTrajectory, executed] using tail.2.2.2.1
              · simpa only [runTrajectory, executed, List.mem_cons] using
                  (Or.inr tail.2.2.2.2 :
                    Ledger.Outcome.unknownCommit pending.request.key pending.request.attempt =
                        Ledger.Outcome.committed receipt after ∨
                      Ledger.Outcome.unknownCommit pending.request.key pending.request.attempt ∈
                        (runTrajectory grants after rest).outcomes)
          | replay receipt =>
              have tail := ih initial (by simpa only [locate, executed] using found)
              dsimp only [permission] at executed
              refine ⟨tail.1, tail.2.1, tail.2.2.1, ?_, ?_⟩
              · simpa only [runTrajectory, executed] using tail.2.2.2.1
              · simpa only [runTrajectory, executed, List.mem_cons] using
                  (Or.inr tail.2.2.2.2 :
                    Ledger.Outcome.unknownCommit pending.request.key pending.request.attempt =
                        Ledger.Outcome.replay receipt ∨
                      Ledger.Outcome.unknownCommit pending.request.key pending.request.attempt ∈
                        (runTrajectory grants initial rest).outcomes)
          | unknownCommit key attempt =>
              obtain ⟨key_eq, attempt_eq⟩ := unknown_outcome_keeps_request_identity initial request _ mode key attempt executed
              subst key
              subst attempt
              simp only [locate, executed, Option.some.injEq] at found
              subst pending
              dsimp only [permission] at executed
              exact ⟨rfl, .nil initial, executed,
                by simp [runTrajectory, executed, Pipeline.finishPayment],
                by simp [runTrajectory, executed, Pipeline.finishPayment]⟩
          | rejectedNoCommit attempt error => simp [locate, executed] at found
          | conflict registered requested => simp [locate, executed] at found
          | pending error => simp [locate, executed] at found
      | refresh change =>
          cases refreshed : Pipeline.refresh grants initial change with
          | known after =>
              have tail := ih after (by simpa only [locate, refreshed] using found)
              exact ⟨tail.1, .cons
                (Pipeline.u10_1_authorized_refresh_is_step grants initial after change refreshed)
                tail.2.1, tail.2.2.1,
                by simpa only [runTrajectory, refreshed] using tail.2.2.2.1,
                by simpa only [runTrajectory, refreshed] using tail.2.2.2.2⟩
          | unknown error => simp [locate, refreshed] at found
          | rejected error => simp [locate, refreshed] at found
          | conflict left right => simp [locate, refreshed] at found

theorem stopped_interpreter_always_has_pending (grants : List Authorization.Grant)
    (steps : List Instruction) (initial : Ledger.Handle)
    (stopped : (runTrajectory grants initial steps).current = none) :
    ∃ pending, locate grants initial steps = some pending := by
  induction steps generalizing initial with
  | nil => simp [runTrajectory] at stopped
  | cons instruction rest ih =>
      cases instruction with
      | pay request mode =>
          cases executed : Ledger.consume_ext initial initial request
              (Authorization.authorized grants initial.gamma request.payload.payer 0
                request.payload.normVersion (.relation request.payload.relation) (some request.payload)) mode with
          | committed receipt after =>
              obtain ⟨pending, found⟩ := ih after (by simpa only [runTrajectory, executed] using stopped)
              exact ⟨pending, by simpa only [locate, permission, executed] using found⟩
          | replay receipt =>
              obtain ⟨pending, found⟩ := ih initial (by simpa only [runTrajectory, executed] using stopped)
              exact ⟨pending, by simpa only [locate, permission, executed] using found⟩
          | unknownCommit key attempt =>
              exact ⟨⟨grants, initial, request, mode, rest⟩, by simp only [locate, permission, executed]⟩
          | rejectedNoCommit attempt error => simp [runTrajectory, executed, Pipeline.finishPayment] at stopped
          | conflict registered requested => simp [runTrajectory, executed, Pipeline.finishPayment] at stopped
          | pending error => simp [runTrajectory, executed, Pipeline.finishPayment] at stopped
      | refresh change =>
          cases refreshed : Pipeline.refresh grants initial change with
          | known after =>
              obtain ⟨pending, found⟩ := ih after (by simpa only [runTrajectory, refreshed] using stopped)
              exact ⟨pending, by simpa only [locate, refreshed] using found⟩
          | unknown error => simp [runTrajectory, refreshed] at stopped
          | rejected error => simp [runTrajectory, refreshed] at stopped
          | conflict left right => simp [runTrajectory, refreshed] at stopped

theorem captured_prestate_inherits_full_invariant (grants : List Authorization.Grant)
    (steps : List Instruction) (initial : Ledger.Handle) (pending : Pending)
    (valid : Trace.Invariant initial) (found : locate grants initial steps = some pending) :
    Trace.Invariant pending.before :=
  Trace.u10_2_finite_trace_composition
    (captured_pending_has_actual_prefix_and_stopped_result grants steps initial pending found).2.1 valid

end JurisLean.Candidates.PendingCommit20261027
