import JurisLean.Candidates.SourceAction20261027
import JurisLean.Candidates.Final20261021.Acceptance

/-!
Frozen 09.3, lines 157 and 159: instantiate the existing source-key bridge and
single-use trace theorem, then retain three finite outcomes: a mismatched key
is pending, a reused cash event is rejected, and a changed-attempt replay does
not commit again. These statements rely on the identity contract stated in
the frozen text as an external premise; they do not identify real aliases.
-/

namespace JurisLean.Candidates.SourcePaymentIdentity20261103

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.Final20261021.Acceptance
open JurisLean.Candidates.SourceAction20261027
open JurisLean.Candidates.SourceStages20261027

-- A finite, explicitly synthetic contract from payment tokens to PaymentIds.
-- It is a test fixture, not a source-recognition function or legal μ.
def syntheticPaymentId (token : Bool) : PaymentId := if token then ⟨2⟩ else ⟨1⟩

-- L157: under the external identity-contract premise fixed by the frozen
-- statement, two source calls with the same PaymentId produce actual
-- SourceAction requests with that key; the trace theorem excludes a second
-- committed effect. This proof does not establish the external contract.
theorem sourced_calls_with_same_payment_id_are_at_most_once {W : Type}
    (opening : SharedOpening W) (firstCall nextCall : PaymentCall)
    (before previousOutput after later laterOutput : Ledger.Handle)
    (permission permissionNext : Bool)
    (mode modeNext : Ledger.Submission) (receipt : Ledger.Receipt)
    (samePaymentId :
      (boundRow opening.anchor.frame nextCall.slot).payment.value.key =
        (boundRow opening.anchor.frame firstCall.slot).payment.value.key)
    (committed : Ledger.consume_ext before previousOutput
      (paymentRequest opening firstCall) permission mode =
        .committed receipt after)
    (intervening : Trace.Path after later) :
    ∀ nextReceipt nextPost,
      Ledger.consume_ext later laterOutput (paymentRequest opening nextCall)
        permissionNext modeNext ≠ .committed nextReceipt nextPost := by
  have firstSourceKey :=
    (source_request_keeps_actual_key_payload_and_identity opening firstCall).1
  have nextSourceKey :=
    (source_request_keeps_actual_key_payload_and_identity opening nextCall).1
  have sameKey : (paymentRequest opening nextCall).key =
      (paymentRequest opening firstCall).key := by
    calc
      (paymentRequest opening nextCall).key =
          (boundRow opening.anchor.frame nextCall.slot).payment.value.key := by
            simpa using nextSourceKey
      _ = (boundRow opening.anchor.frame firstCall.slot).payment.value.key := samePaymentId
      _ = (paymentRequest opening firstCall).key := by
            simpa using firstSourceKey.symm
  exact Trace.u09_1_actual_trace_at_most_once before previousOutput after later
    laterOutput (paymentRequest opening firstCall) (paymentRequest opening nextCall)
    permission permissionNext mode modeNext receipt committed intervening sameKey

-- L159: the finite examples below are about the model's explicit key fields.
-- A key mismatch is not treated as a second real payment or as consumed.
theorem finite_payment_identity_and_retry_outcomes :
    (syntheticPaymentId false = ⟨1⟩ ∧
      (request 1).key = syntheticPaymentId false ∧
      Ledger.consume_ext opening opening (request 1) true .submit =
        .committed (Ledger.commitPayment opening (request 1)).1
          (Ledger.commitPayment opening (request 1)).2) ∧
    (syntheticPaymentId false = ⟨1⟩ ∧
      (syntheticPaymentId true : PaymentId) = ⟨2⟩ ∧
      syntheticPaymentId true ≠ syntheticPaymentId false ∧
      ({ request 1 with key := syntheticPaymentId true }).interpretedPayment =
        some (syntheticPaymentId false) ∧
      Ledger.consume_ext post1 post1
        { request 1 with key := syntheticPaymentId true } true .submit =
          .pending .identityUnknown ∧
      Ledger.Outcome.post post1
        (Ledger.consume_ext post1 post1
          { request 1 with key := syntheticPaymentId true } true .submit) =
          some post1 ∧
      Ledger.Outcome.acknowledgedUsed post1
        (Ledger.consume_ext post1 post1
          { request 1 with key := syntheticPaymentId true } true .submit) =
            post1.state.used) ∧
    (syntheticPaymentId false ≠ syntheticPaymentId true ∧
      ({ request 1 with key := syntheticPaymentId false }).key ≠
        ({ request 2 with key := syntheticPaymentId true }).key ∧
      ({ request 1 with key := syntheticPaymentId false }).payload.cashId =
        ({ request 2 with key := syntheticPaymentId true,
          payload := { payload 2 with cashId := (request 1).payload.cashId } }).payload.cashId ∧
      Ledger.consume_ext post1 post1
        { request 2 with key := syntheticPaymentId true,
          payload := { payload 2 with cashId := (request 1).payload.cashId } } true .submit =
          .rejectedNoCommit ⟨2⟩ .duplicateCash ∧
      Ledger.Outcome.post post1
        (Ledger.consume_ext post1 post1
          { request 2 with key := syntheticPaymentId true,
            payload := { payload 2 with cashId := (request 1).payload.cashId } } true .submit) =
            some post1 ∧
      Ledger.Outcome.acknowledgedUsed post1
        (Ledger.consume_ext post1 post1
          { request 2 with key := syntheticPaymentId true,
            payload := { payload 2 with cashId := (request 1).payload.cashId } } true .submit) =
            post1.state.used) ∧
    (({ request 1 with key := syntheticPaymentId false, attempt := ⟨2⟩ }).key =
        (request 1).key ∧
      ({ request 1 with key := syntheticPaymentId false, attempt := ⟨2⟩ }).attempt ≠
        (request 1).attempt ∧
      ({ request 1 with key := syntheticPaymentId false, attempt := ⟨2⟩ }).payload =
        (request 1).payload ∧
      Ledger.consume_ext post1 post1
        { request 1 with key := syntheticPaymentId false, attempt := ⟨2⟩ } true .submit =
        .replay (Ledger.commitPayment opening (request 1)).1 ∧
      Ledger.Outcome.post post1
        (Ledger.consume_ext post1 post1
          { request 1 with key := syntheticPaymentId false, attempt := ⟨2⟩ } true .submit) =
          some post1 ∧
      Ledger.Outcome.acknowledgedUsed post1
        (Ledger.consume_ext post1 post1
          { request 1 with key := syntheticPaymentId false, attempt := ⟨2⟩ } true .submit) =
          post1.state.used) := by
  decide +kernel

end JurisLean.Candidates.SourcePaymentIdentity20261103

#check JurisLean.Candidates.SourcePaymentIdentity20261103.sourced_calls_with_same_payment_id_are_at_most_once
#print axioms JurisLean.Candidates.SourcePaymentIdentity20261103.sourced_calls_with_same_payment_id_are_at_most_once
#check JurisLean.Candidates.SourcePaymentIdentity20261103.finite_payment_identity_and_retry_outcomes
#print axioms JurisLean.Candidates.SourcePaymentIdentity20261103.finite_payment_identity_and_retry_outcomes

#check JurisLean.Candidates.SourceAction20261027.source_request_keeps_actual_key_payload_and_identity
#print axioms JurisLean.Candidates.SourceAction20261027.source_request_keeps_actual_key_payload_and_identity
#check JurisLean.Candidates.Final20261021.Trace.u09_1_actual_trace_at_most_once
#print axioms JurisLean.Candidates.Final20261021.Trace.u09_1_actual_trace_at_most_once
#check JurisLean.Candidates.Final20261021.Ledger.noncommit_does_not_write_U
#print axioms JurisLean.Candidates.Final20261021.Ledger.noncommit_does_not_write_U
#check JurisLean.Candidates.Final20261021.Ledger.u09_writeU_on_committed_applicable
#print axioms JurisLean.Candidates.Final20261021.Ledger.u09_writeU_on_committed_applicable
#check JurisLean.Candidates.Final20261021.Ledger.ready_requires_unused
#print axioms JurisLean.Candidates.Final20261021.Ledger.ready_requires_unused
#check JurisLean.Candidates.Final20261021.Ledger.consume_committed_origin
#print axioms JurisLean.Candidates.Final20261021.Ledger.consume_committed_origin
#check JurisLean.Candidates.Final20261021.Ledger.consume_success_is_gated
#print axioms JurisLean.Candidates.Final20261021.Ledger.consume_success_is_gated
#check JurisLean.Candidates.Final20261021.Trace.used_monotone_path
#print axioms JurisLean.Candidates.Final20261021.Trace.used_monotone_path
#check JurisLean.Candidates.SourceStages20261027.accepted_view_binds_both_actual_payments
#print axioms JurisLean.Candidates.SourceStages20261027.accepted_view_binds_both_actual_payments
#check JurisLean.Candidates.SourceAction20261027.applicable_request_requires_actual_environment_and_all_versions
#print axioms JurisLean.Candidates.SourceAction20261027.applicable_request_requires_actual_environment_and_all_versions
#check JurisLean.Candidates.Final20261021.Acceptance.n_unknown_does_not_burn_U
#print axioms JurisLean.Candidates.Final20261021.Acceptance.n_unknown_does_not_burn_U
#check JurisLean.Candidates.Final20261021.Acceptance.n_identity_unknown_no_U
#print axioms JurisLean.Candidates.Final20261021.Acceptance.n_identity_unknown_no_U
#check JurisLean.Candidates.Final20261021.Acceptance.n_applicability_unknown_no_U
#print axioms JurisLean.Candidates.Final20261021.Acceptance.n_applicability_unknown_no_U
#check JurisLean.Candidates.Final20261021.Acceptance.n09_1_replay_original_receipt
#print axioms JurisLean.Candidates.Final20261021.Acceptance.n09_1_replay_original_receipt
#check JurisLean.Candidates.Final20261021.Acceptance.n09_1_payload_conflict
#print axioms JurisLean.Candidates.Final20261021.Acceptance.n09_1_payload_conflict
