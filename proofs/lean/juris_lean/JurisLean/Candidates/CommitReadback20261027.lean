import JurisLean.Candidates.PendingCommit20261027

/-!
Finite reconciliation against an independent full readback catalog. Membership
is an external authority premise; this module does not prove a bank's effect or
a server fence. A committed statement must equal the existing validated kernel
transition. An absent statement must certify both noncommit and exclusion of
later execution of that attempt, with the exact prior state. A missing receipt
alone supplies neither statement. Later concurrent transitions need a separate
verified history and are not accepted by this exact-step adapter.
-/

namespace JurisLean.Candidates.CommitReadback20261027

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.DecisionTrajectoryConsumer20261027
open JurisLean.Candidates.PendingCommit20261027

inductive Disposition where
  | committed (receipt : Ledger.Receipt)
  | fencedAbsent (fence : SourceRef)
  deriving DecidableEq

structure Readback where
  source : SourceRef
  before : Ledger.Handle
  request : PaymentRequest
  after : Ledger.Handle
  disposition : Disposition
  deriving DecidableEq

def checkedPost (pending : Pending) (report : Readback) : Result Ledger.Handle :=
  match report.disposition with
  | .committed reported =>
      match Ledger.consume_ext pending.before pending.before pending.request
          (permission pending.grants pending.before pending.request) .submit with
      | .committed receipt after =>
          if receipt = reported ∧ after = report.after then .known report.after
          else .rejected .stageFrameMismatch
      | _ => .unknown .notIdentified
  | .fencedAbsent _ =>
      if report.after = pending.before then .known report.after
      else .rejected .stageFrameMismatch

theorem checked_post_is_exact_commit_or_fenced_absence (pending : Pending)
    (report : Readback) (after : Ledger.Handle) (accepted : checkedPost pending report = .known after) :
    after = report.after ∧
      ((∃ receipt, report.disposition = .committed receipt ∧
        Ledger.consume_ext pending.before pending.before pending.request
          (permission pending.grants pending.before pending.request) .submit = .committed receipt after) ∨
       (∃ fence, report.disposition = .fencedAbsent fence ∧ after = pending.before)) := by
  cases disposition : report.disposition with
  | committed reported =>
      cases executed : Ledger.consume_ext pending.before pending.before pending.request
          (permission pending.grants pending.before pending.request) .submit with
      | committed receipt post =>
          simp only [checkedPost, disposition, executed] at accepted
          split at accepted
          · rename_i same
            cases accepted
            exact ⟨rfl, Or.inl ⟨reported, disposition,
              by simpa only [same.1, same.2] using executed⟩⟩
          · cases accepted
      | replay receipt => simp [checkedPost, disposition, executed] at accepted
      | rejectedNoCommit attempt error => simp [checkedPost, disposition, executed] at accepted
      | conflict registered requested => simp [checkedPost, disposition, executed] at accepted
      | unknownCommit key attempt => simp [checkedPost, disposition, executed] at accepted
      | pending error => simp [checkedPost, disposition, executed] at accepted
  | fencedAbsent fence =>
      simp only [checkedPost, disposition] at accepted
      split at accepted
      · rename_i same
        cases accepted
        exact ⟨rfl, Or.inr ⟨fence, disposition, same⟩⟩
      · cases accepted

def resolve (pending : Pending) (catalog : List Readback) (report : Readback) : Result Ledger.Handle :=
  if report ∈ catalog ∧ report.before = pending.before ∧ report.request = pending.request ∧
      Ledger.consume_ext pending.before pending.before pending.request
        (permission pending.grants pending.before pending.request) pending.mode =
        .unknownCommit pending.request.key pending.request.attempt then checkedPost pending report
  else .unknown .missingEvidence

theorem resolved_readback_binds_catalog_full_request_and_actual_unknown
    (pending : Pending) (catalog : List Readback) (report : Readback) (after : Ledger.Handle)
    (accepted : resolve pending catalog report = .known after) :
    report ∈ catalog ∧ report.before = pending.before ∧ report.request = pending.request ∧
      Ledger.consume_ext pending.before pending.before pending.request
        (permission pending.grants pending.before pending.request) pending.mode =
        .unknownCommit pending.request.key pending.request.attempt ∧
      checkedPost pending report = .known after := by
  unfold resolve at accepted
  split at accepted
  · rename_i bound
    exact ⟨bound.1, bound.2.1, bound.2.2.1, bound.2.2.2, accepted⟩
  · cases accepted

theorem resolved_readback_is_reported_state_and_step_or_frame
    (pending : Pending) (catalog : List Readback) (report : Readback) (after : Ledger.Handle)
    (accepted : resolve pending catalog report = .known after) :
    after = report.after ∧ (Trace.Step pending.before after ∨ after = pending.before) := by
  have bound := resolved_readback_binds_catalog_full_request_and_actual_unknown pending catalog report after accepted
  have exactPost := checked_post_is_exact_commit_or_fenced_absence pending report after bound.2.2.2.2
  refine ⟨exactPost.1, ?_⟩
  rcases exactPost.2 with committed | absent
  · obtain ⟨receipt, _, executed⟩ := committed
    exact Or.inl (Trace.u10_2_committed_executor_is_step pending.before pending.before pending.request
      _ .submit receipt after executed)
  · obtain ⟨_, _, same⟩ := absent
    exact Or.inr same

theorem recovered_actual_pending_preserves_full_invariant
    (grants : List Authorization.Grant) (steps : List Instruction)
    (initial : Ledger.Handle) (pending : Pending) (catalog : List Readback)
    (report : Readback) (after : Ledger.Handle) (valid : Trace.Invariant initial)
    (found : locate grants initial steps = some pending)
    (accepted : resolve pending catalog report = .known after) : Trace.Invariant after := by
  have before := captured_prestate_inherits_full_invariant grants steps initial pending valid found
  rcases (resolved_readback_is_reported_state_and_step_or_frame pending catalog report after accepted).2 with
      step | same
  · exact Trace.step_preserves step before
  · simpa only [same] using before

end JurisLean.Candidates.CommitReadback20261027
