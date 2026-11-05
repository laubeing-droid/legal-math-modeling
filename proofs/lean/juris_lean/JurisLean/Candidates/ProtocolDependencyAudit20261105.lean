import JurisLean.Candidates.FiniteTraceInvariantAudit20261105
import JurisLean.Candidates.SourceFinalBridgeAudit20261102
import JurisLean.Candidates.SemanticIndependenceAudit20261104
import JurisLean.Candidates.ProcedureClosureAudit20261027
import JurisLean.Candidates.Final20261021.Progress

/-!
Frozen original 10.6 L141/L143/L145. The two declarations below connect
existing results: the actual CaseRecord codec does not determine an external
reference interpretation, and the actual rejecting trace edge is a zero-change
loop. Positive protocol edges and conditional rank bounds are quoted below.
The external interpretation is an explicit input; this fixture does not certify
the origin of real material. No universal business termination is asserted.
-/

namespace JurisLean.Candidates.ProtocolDependencyAudit20261105

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.SourceCompilation20261027
open JurisLean.Candidates.SourceStages20261027
open JurisLean.Candidates.U07_2JointObject20261029

-- Same accepted source output and actual record codec, but an unbound external mu.
theorem actual_record_roundtrip_does_not_supply_external_reference :
    ∃ out,
      sourceModel JurisLean.Seams.UnifiedInstance.instanceM
        stageMaterial 0 [⟨stageMaterial, 0, stageView⟩] = .ok out ∧
      JurisLean.Seams.UnifiedNeedlesS0S1.caseFragment.dec
          (JurisLean.Seams.UnifiedNeedlesS0S1.caseFragment.enc (recordOf out.1.source)) =
        recordOf out.1.source ∧
      (fun _ : SourceRef => (none : Option LegalObject))
          out.1.source.decoded.observed.value.1 ≠
        some (.relation out.1.source.decoded.observed.value.2) := by
  obtain ⟨out, _mu, accepted, _faithful, _joint, missing⟩ :=
    SourceFinalBridge20261102.source_model_joint_bridge_nonempty_and_faithfulness_needed
  exact ⟨out, accepted,
    JurisLean.Seams.UnifiedNeedlesS0S1.caseFragment_roundTrip (recordOf out.1.source),
    missing⟩

-- This is a counterexample to applying a strict rank to every actual Trace.Step.
theorem actual_rejection_blocks_unconditional_strict_rank
    (rank : Ledger.Handle → Nat) :
    ¬ (∀ before after, Trace.Step before after → rank after < rank before) := by
  exact ProcedureClosure20261027.self_loop_has_no_strict_natural_rank
    rank Trace.Step Acceptance.opening (Trace.Step.reject Acceptance.opening)

#check actual_record_roundtrip_does_not_supply_external_reference
#print axioms actual_record_roundtrip_does_not_supply_external_reference
#check actual_rejection_blocks_unconditional_strict_rank
#print axioms actual_rejection_blocks_unconditional_strict_rank

#check JurisLean.Seams.UnifiedNeedlesS0S1.caseFragment_roundTrip
#print axioms JurisLean.Seams.UnifiedNeedlesS0S1.caseFragment_roundTrip
#check SourceFinalBridge20261102.source_model_joint_semantic_quantity
#print axioms SourceFinalBridge20261102.source_model_joint_semantic_quantity
#check SourceFinalBridge20261102.source_model_joint_bridge_nonempty_and_faithfulness_needed
#print axioms SourceFinalBridge20261102.source_model_joint_bridge_nonempty_and_faithfulness_needed
#check SemanticIndependenceAudit20261104.same_received_pay6_document_different_obligation
#print axioms SemanticIndependenceAudit20261104.same_received_pay6_document_different_obligation
#check FiniteTraceInvariantAudit20261105.forms_do_not_determine_quantity
#print axioms FiniteTraceInvariantAudit20261105.forms_do_not_determine_quantity
#check PartialStepGateAudit20261105.actual_committed_step_satisfies_local_contract
#print axioms PartialStepGateAudit20261105.actual_committed_step_satisfies_local_contract
#check PartialStepGateAudit20261105.noncommit_returned_state_has_full_frame
#print axioms PartialStepGateAudit20261105.noncommit_returned_state_has_full_frame
#check PartialStepGateAudit20261105.actual_pipeline_retry_rechecks_witness_and_prevents_double_effect
#print axioms PartialStepGateAudit20261105.actual_pipeline_retry_rechecks_witness_and_prevents_double_effect
#check AuthorizationClosureAudit20261104.actual_refresh_requires_old_authority
#print axioms AuthorizationClosureAudit20261104.actual_refresh_requires_old_authority
#check U10_1RefreshRuleProtocol20261030.internal_refresh_rechecks_before_continuation
#print axioms U10_1RefreshRuleProtocol20261030.internal_refresh_rechecks_before_continuation
#check U10_1RefreshRuleProtocol20261030.continued_protocol_refines_actual_calls
#print axioms U10_1RefreshRuleProtocol20261030.continued_protocol_refines_actual_calls
#check U10_1RefreshRuleProtocol20261030.reported_protocol_post_has_actual_path
#print axioms U10_1RefreshRuleProtocol20261030.reported_protocol_post_has_actual_path
#check FiniteTraceInvariantAudit20261105.actual_reported_protocol_post_i
#print axioms FiniteTraceInvariantAudit20261105.actual_reported_protocol_post_i
#check Trace.u10_2_finite_trace_composition
#print axioms Trace.u10_2_finite_trace_composition
#check ProcedureClosure20261027.strict_rank_bounds_finite_transition_count
#print axioms ProcedureClosure20261027.strict_rank_bounds_finite_transition_count
#check ProcedureClosure20261027.strict_rank_excludes_infinite_execution
#print axioms ProcedureClosure20261027.strict_rank_excludes_infinite_execution
#check ProcedureClosure20261027.self_loop_has_no_strict_natural_rank
#print axioms ProcedureClosure20261027.self_loop_has_no_strict_natural_rank
#check ProcedureClosure20261027.Audit.finite_inspection_does_not_end_retry_execution
#print axioms ProcedureClosure20261027.Audit.finite_inspection_does_not_end_retry_execution
#check SourcePaymentIdentity20261103.sourced_calls_with_same_payment_id_are_at_most_once
#print axioms SourcePaymentIdentity20261103.sourced_calls_with_same_payment_id_are_at_most_once
#check Ledger.ready_requires_identity_and_applicability
#print axioms Ledger.ready_requires_identity_and_applicability

#check Progress.u10_3_rank_bounds_steps
#print axioms Progress.u10_3_rank_bounds_steps
#check Progress.u10_3_simulation_length
#print axioms Progress.u10_3_simulation_length
#check Progress.multistep_simulation_not_one_step
#print axioms Progress.multistep_simulation_not_one_step
#check Progress.two_cycle_has_no_strict_rank
#print axioms Progress.two_cycle_has_no_strict_rank
#check ProcedureClosure20261027.lawful_closed_iff_local_checks
#print axioms ProcedureClosure20261027.lawful_closed_iff_local_checks
#check ProcedureClosure20261027.checked_closed_iff_valid_and_exhausted
#print axioms ProcedureClosure20261027.checked_closed_iff_valid_and_exhausted
end JurisLean.Candidates.ProtocolDependencyAudit20261105