import JurisLean.Candidates.FinalizeReadClosureAudit20261105
import JurisLean.Candidates.SourcePaymentIdentityAudit20261103

/-!
Frozen 10.4, L125/L127/L129: a concrete local contract for the existing
payment executor, its returned-state frame, and a current-context retry.
The frozen L/Q/N interfaces are not redefined: this module's whole Handle
frame preserves its relation/quantity/norm fields and every fixed view of
that Handle. It does not identify a Relation with an internal identifier.
UnknownCommit has no returned poststate; no server-state claim follows.
-/
namespace JurisLean.Candidates.PartialStepGateAudit20261105

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.Final20261021.Acceptance
open JurisLean.Candidates.AuthorizationClosureAudit20261104

-- L125 requires concrete Pre_i/Step_i/Post_i/Frame_i. These definitions use
-- the real validation and executor, rather than a separate success oracle.
def Pre_i (before previousOutput : Ledger.Handle) (req : PaymentRequest)
    (permission : Bool) (mode : Ledger.Submission) : Prop :=
  mode = .submit ∧ Ledger.lookupReceipt before.state req.key = none ∧
    Ledger.validationError before previousOutput req permission = none

abbrev Step_i := Ledger.consume_ext

def Post_i (before : Ledger.Handle) (req : PaymentRequest)
    (receipt : Ledger.Receipt) (after : Ledger.Handle) : Prop :=
  receipt = (Ledger.commitPayment before req).1 ∧
    after = (Ledger.commitPayment before req).2 ∧ req.key ∈ after.state.used

-- A frame on a returned state only. UnknownCommit returns none, not before.
def Frame_i (before : Ledger.Handle) (outcome : Ledger.Outcome) : Prop :=
  ∀ after, outcome.post before = some after → after = before

-- L125/L129: connect the actual successful call to the named contract,
-- positive applicability/identity, current output, and unused-key witnesses.
theorem actual_committed_step_satisfies_local_contract
    (before previousOutput : Ledger.Handle) (req : PaymentRequest)
    (permission : Bool) (mode : Ledger.Submission)
    (receipt : Ledger.Receipt) (after : Ledger.Handle)
    (success : Step_i before previousOutput req permission mode =
      .committed receipt after) :
    Pre_i before previousOutput req permission mode ∧
      Post_i before req receipt after ∧ req.applicable = .yes ∧
      req.interpretedPayment = some req.key ∧
      previousOutput = before ∧ req.key ∉ before.state.used := by
  obtain ⟨submitted, fresh, ready, hr, hp⟩ :=
    Ledger.consume_committed_origin before previousOutput req permission mode
      receipt after success
  obtain ⟨positive, identity, used⟩ :=
    Ledger.consume_success_is_gated before previousOutput req permission mode
      receipt after success
  have current := Ledger.ready_requires_actual_output before previousOutput req permission ready
  have unused := Ledger.ready_requires_unused before previousOutput req permission ready
  exact ⟨⟨submitted, fresh, ready⟩, ⟨hr, hp, used⟩, positive, identity, current, unused⟩

-- L127: a missing returned-state frame cannot be replaced by the narrower
-- used-marker theorem. Every noncommitted returned Handle is exactly before.
theorem noncommit_returned_state_has_full_frame
    (before : Ledger.Handle) (outcome : Ledger.Outcome)
    (noncommit : ∀ receipt after, outcome ≠ .committed receipt after) :
    Frame_i before outcome := by
  cases outcome with
  | committed receipt after => exact False.elim (noncommit receipt after rfl)
  | replay receipt =>
      intro after same
      exact (Option.some.inj same).symm
  | rejectedNoCommit attempt reason =>
      intro after same
      exact (Option.some.inj same).symm
  | conflict registered requested =>
      intro after same
      exact (Option.some.inj same).symm
  | unknownCommit key attempt =>
      intro after same
      cases same
  | pending reason =>
      intro after same
      exact (Option.some.inj same).symm

def unknownRequest : PaymentRequest := { request 1 with applicable := .unknown }
def negativeRequest : PaymentRequest := { request 1 with applicable := .no }
def unknownOutcome : Ledger.Outcome :=
  Step_i opening opening unknownRequest true .submit
def negativeOutcome : Ledger.Outcome :=
  Step_i opening opening negativeRequest true .submit
-- This is the executor's actual registered/requested payload-conflict branch.
def conflictingOutcome : Ledger.Outcome :=
  Step_i post1 post1 (request 1 8) true .submit

-- The intentionally bad gate treats absence of a negative as permission.
def unsafeNotNegative : Ledger.State :=
  if unknownRequest.applicable = .no then opening.state
  else Ledger.performance opening.state unknownRequest.payload

-- L125/L127: the frozen 10-to-3 counterexample and the three distinct actual
-- outcomes, each with its correct returned-state frame, were not yet joined.
theorem unknown_negative_and_conflict_are_distinct_framed_outcomes :
    unknownRequest.applicable ≠ .no ∧ unknownRequest.applicable ≠ .yes ∧
    Ledger.balance opening.state = 10 ∧ Ledger.balance unsafeNotNegative = 3 ∧
    unknownOutcome = .pending .applicabilityUnknown ∧
    unknownOutcome.post opening = some opening ∧
    negativeOutcome = .rejectedNoCommit ⟨1⟩ .notApplicable ∧
    negativeOutcome.post opening = some opening ∧
    conflictingOutcome = .conflict (payload 1) (payload 1 8) ∧
    conflictingOutcome.post post1 = some post1 ∧
    unknownOutcome ≠ negativeOutcome ∧ unknownOutcome ≠ conflictingOutcome ∧
    negativeOutcome ≠ conflictingOutcome := by
  decide +kernel

-- L127: indeterminate submission is not an unchanged-server-state theorem.
theorem unknown_commit_has_no_returned_post
    (before : Ledger.Handle) (key : PaymentId) (attempt : AttemptId) :
    (Ledger.Outcome.unknownCommit key attempt).post before = none ∧
      (Ledger.Outcome.unknownCommit key attempt).acknowledgedUsed before =
        before.state.used := by
  exact ⟨rfl, rfl⟩

-- New evidence is represented by the explicit current context input. The
-- newly positive applicability witness is also an input, not inferred here.
def retryCurrent : Ledger.Handle :=
  { opening with gamma :=
      { opening.gamma with evidenceVersion := opening.gamma.evidenceVersion + 1 } }
def retryRequest : PaymentRequest := { request 1 with attempt := ⟨2⟩ }
def retryReceipt : Ledger.Receipt := (Ledger.commitPayment retryCurrent retryRequest).1
def retryPost : Ledger.Handle := (Ledger.commitPayment retryCurrent retryRequest).2

-- L129: reuse of the same supplied event identity after a known pending branch
-- needs the current Handle. A successful retry then records that same key;
-- changing only attempt does not consume it a second time.
theorem retry_matches_current_context_and_consumes_the_given_key_once :
    unknownOutcome = .pending .applicabilityUnknown ∧
    unknownOutcome.acknowledgedUsed opening = opening.state.used ∧
    retryCurrent.gamma ≠ opening.gamma ∧
    retryRequest.key = unknownRequest.key ∧
    retryRequest.payload.cashId = unknownRequest.payload.cashId ∧
    retryRequest.interpretedPayment = some unknownRequest.key ∧
    Step_i retryCurrent opening retryRequest true .submit =
      .rejectedNoCommit ⟨2⟩ .prestateRequired ∧
    Step_i retryCurrent retryCurrent retryRequest true .submit =
      .committed retryReceipt retryPost ∧
    retryRequest.key ∈ retryPost.state.used ∧
    Step_i retryPost retryPost { retryRequest with attempt := ⟨3⟩ } true .submit =
      .replay retryReceipt ∧
    (Step_i retryPost retryPost { retryRequest with attempt := ⟨3⟩ } true .submit).post
      retryPost = some retryPost := by
  decide +kernel

-- L129: exactly the query parameters used by Pipeline.executePayments.
def paymentQuery (before : Ledger.Handle) (req : PaymentRequest) : Query :=
  { gamma := before.gamma, subject := req.payload.payer, action := 0,
    version := req.payload.normVersion, object := .relation req.payload.relation,
    payload := some req.payload, nextContext := none }

-- L125/L129: the missing connection is that an actual new commit with the
-- Pipeline's computed permission exposes a Grant checked in this context.
-- The catalog is an explicit input; this does not establish its real issuance.
theorem checked_payment_commit_exposes_a_current_grant
    (catalog : List Authorization.Grant) (before previousOutput : Ledger.Handle)
    (req : PaymentRequest) (mode : Ledger.Submission)
    (receipt : Ledger.Receipt) (after : Ledger.Handle)
    (success : Step_i before previousOutput req
      (permits catalog (paymentQuery before req)) mode = .committed receipt after) :
    ∃ a ∈ catalog, check (paymentQuery before req) a = true := by
  obtain ⟨_, _, ready, _, _⟩ :=
    Ledger.consume_committed_origin before previousOutput req
      (permits catalog (paymentQuery before req)) mode receipt after success
  have granted : permits catalog (paymentQuery before req) = true := by
    cases permissionCase : permits catalog (paymentQuery before req) with
    | true => rfl
    | false =>
        simp only [permissionCase] at ready
        unfold Ledger.validationError at ready
        simp only [if_pos (show (false : Bool) = false from rfl)] at ready
        split_ifs at ready <;> cases ready
  exact (permits_exact_current_witness catalog (paymentQuery before req)).mp granted

-- Both grants below are explicitly synthetic catalog inputs. The fresh
-- positive witness is supplied; no model rule creates authority by editing Γ.
def oldPaymentGrant : Authorization.Grant := grant (payload 1)
def currentPaymentGrant : Authorization.Grant :=
  { oldPaymentGrant with evidence := ⟨91⟩, context := retryCurrent.gamma }
def pendingPaymentRun : Pipeline.PaymentRun :=
  Pipeline.executePayments opening unknownRequest retryRequest
    [oldPaymentGrant] .submit none
def staleWitnessPaymentRun : Pipeline.PaymentRun :=
  Pipeline.executePayments retryCurrent retryRequest
    { retryRequest with attempt := ⟨3⟩ } [oldPaymentGrant] .submit none
def currentWitnessPaymentRun : Pipeline.PaymentRun :=
  Pipeline.executePayments retryCurrent retryRequest
    { retryRequest with attempt := ⟨3⟩ } [currentPaymentGrant] .submit none

-- L129: Handle freshness alone is insufficient. The actual Pipeline rejects
-- the old-context grant, admits the supplied current-context grant, and then
-- replays the same event identity without a second committed business effect.
theorem actual_pipeline_retry_rechecks_witness_and_prevents_double_effect :
    check (paymentQuery opening (request 1)) oldPaymentGrant = true ∧
    check (paymentQuery retryCurrent retryRequest) oldPaymentGrant = false ∧
    check (paymentQuery retryCurrent retryRequest) currentPaymentGrant = true ∧
    pendingPaymentRun.exit = .undecided ∧
    pendingPaymentRun.current = some opening ∧
    pendingPaymentRun.outcomes = [.pending .applicabilityUnknown] ∧
    staleWitnessPaymentRun.exit = .rejected ∧
    staleWitnessPaymentRun.current = some retryCurrent ∧
    staleWitnessPaymentRun.outcomes =
      [.rejectedNoCommit ⟨2⟩ .authorityUnresolved] ∧
    currentWitnessPaymentRun.exit = .success ∧
    currentWitnessPaymentRun.current = some retryPost ∧
    currentWitnessPaymentRun.outcomes =
      [.committed retryReceipt retryPost, .replay retryReceipt] := by
  decide +kernel

#check actual_committed_step_satisfies_local_contract
#print axioms actual_committed_step_satisfies_local_contract
#check noncommit_returned_state_has_full_frame
#print axioms noncommit_returned_state_has_full_frame
#check unknown_negative_and_conflict_are_distinct_framed_outcomes
#print axioms unknown_negative_and_conflict_are_distinct_framed_outcomes
#check unknown_commit_has_no_returned_post
#print axioms unknown_commit_has_no_returned_post
#check retry_matches_current_context_and_consumes_the_given_key_once
#print axioms retry_matches_current_context_and_consumes_the_given_key_once
#check Ledger.consume_committed_origin
#print axioms Ledger.consume_committed_origin
#check Ledger.consume_success_is_gated
#print axioms Ledger.consume_success_is_gated
#check Ledger.ready_requires_actual_output
#print axioms Ledger.ready_requires_actual_output
#check Ledger.ready_requires_unused
#print axioms Ledger.ready_requires_unused
#check Ledger.consume_committed_receipts
#print axioms Ledger.consume_committed_receipts
#check JurisLean.Candidates.SourcePaymentIdentity20261103.sourced_calls_with_same_payment_id_are_at_most_once
#print axioms JurisLean.Candidates.SourcePaymentIdentity20261103.sourced_calls_with_same_payment_id_are_at_most_once
#check JurisLean.Candidates.SourcePaymentIdentity20261103.finite_payment_identity_and_retry_outcomes
#print axioms JurisLean.Candidates.SourcePaymentIdentity20261103.finite_payment_identity_and_retry_outcomes
#check JurisLean.Candidates.FinalizeReadClosureAudit20261105.mismatched_request_is_rejected
#print axioms JurisLean.Candidates.FinalizeReadClosureAudit20261105.mismatched_request_is_rejected
#check JurisLean.Candidates.AuthorizationClosureAudit20261104.evidence_reuse_exact_current_condition
#print axioms JurisLean.Candidates.AuthorizationClosureAudit20261104.evidence_reuse_exact_current_condition

#check checked_payment_commit_exposes_a_current_grant
#print axioms checked_payment_commit_exposes_a_current_grant
#check actual_pipeline_retry_rechecks_witness_and_prevents_double_effect
#print axioms actual_pipeline_retry_rechecks_witness_and_prevents_double_effect
#check permits_exact_current_witness
#print axioms permits_exact_current_witness
#check Pipeline.u00_pipeline_wires_handles
#print axioms Pipeline.u00_pipeline_wires_handles
#check Pipeline.finishPayment_current
#print axioms Pipeline.finishPayment_current

end JurisLean.Candidates.PartialStepGateAudit20261105