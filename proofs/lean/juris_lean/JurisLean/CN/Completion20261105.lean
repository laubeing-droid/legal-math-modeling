import JurisLean.CN.World
import JurisLean.CN.Completion20261105.Checkpoint1
import JurisLean.CN.Completion20261105.Acceptance

/-!
Scoped aggregate, added only after Acceptance run 41933733392 passed.
All three ZCode baselines and the preserved 42 v4 results remain unchanged.
The proof/source/consumer map is docs/cn-unification/EVIDENCE-20261105.json.
This is changed-module acceptance of the original represented scope, never
full-release, main acceptance, deployment, or all Chinese-law coverage.
-/

#check JurisLean.CN.Completion20261105.executeCommand
#check JurisLean.CN.Completion20261105.runProgram
#check JurisLean.CN.Completion20261105.Runtime.serveLine

#print axioms JurisLean.CN.Completion20261105.legalWorldCheck_sound
#print axioms JurisLean.CN.Completion20261105.shared_actual_reduction
#print axioms JurisLean.CN.Completion20261105.legalDispatch_success_nonempty
#print axioms JurisLean.CN.Completion20261105.ready_refines_all_supported_worlds
#print axioms JurisLean.CN.Completion20261105.first_admission_narrows_semantic_K
#print axioms JurisLean.CN.Completion20261105.EffectIR.adjust_append
#print axioms JurisLean.CN.Completion20261105.actual_assignments_commute
#print axioms JurisLean.CN.Completion20261105.commute_true_actual_calls
#print axioms JurisLean.CN.Completion20261105.cross_read_counterexample
#print axioms JurisLean.CN.Completion20261105.program_bind_assoc
#print axioms JurisLean.CN.Completion20261105.program_has_actual_history
#print axioms JurisLean.CN.Completion20261105.money_measure_has_matching_tags
#print axioms JurisLean.CN.Completion20261105.Examples.lifecycle_actual
#print axioms JurisLean.CN.Completion20261105.Examples.revoke_without_fictitious_formed
#print axioms JurisLean.CN.Completion20261105.Examples.agency_actual
#print axioms JurisLean.CN.Completion20261105.Examples.apparent_actual_attribution
#print axioms JurisLean.CN.Completion20261105.Examples.jurisdiction_actual
#print axioms JurisLean.CN.Completion20261105.Examples.evidence_actual
#print axioms JurisLean.CN.Completion20261105.Examples.acquisition_actual
#print axioms JurisLean.CN.Completion20261105.Acceptance.actual_shared_event_different_charges
#print axioms JurisLean.CN.Completion20261105.Examples.bankruptcy_actual
#print axioms JurisLean.CN.Completion20261105.Examples.compensation_actual
#print axioms JurisLean.CN.Completion20261105.Examples.rights_actual
#print axioms JurisLean.CN.Completion20261105.Examples.interpretation_actual
#print axioms JurisLean.CN.Completion20261105.Examples.resJudicata_actual
#print axioms JurisLean.CN.Completion20261105.Examples.proposal_actual
#print axioms JurisLean.CN.Completion20261105.fit_uses_actual_sample
#print axioms JurisLean.CN.Completion20261105.probability_uses_actual_posterior
#print axioms JurisLean.CN.Completion20261105.causal_actual_identified_value
#print axioms JurisLean.CN.Completion20261105.bargain_actual_allowed_maximum
#print axioms JurisLean.CN.Completion20261105.performance_success_conserves
#print axioms JurisLean.CN.Completion20261105.exact_native_meaning
#print axioms JurisLean.CN.Completion20261105.behavior_model_does_not_filter_illegal_action
#print axioms JurisLean.CN.Completion20261105.rsi_actual_post_budget
#print axioms JurisLean.CN.Completion20261105.reduction_source_conserves
#print axioms JurisLean.CN.Completion20261105.legal_success_operational_pre
#print axioms JurisLean.CN.Completion20261105.legal_success_ready_contract
#print axioms JurisLean.CN.Completion20261105.permissionDispatch_success_ready
#print axioms JurisLean.CN.Completion20261105.Law.gateFor_success_ready
#print axioms JurisLean.CN.Completion20261105.actual_legal_step_semantic_ready
#print axioms JurisLean.CN.Completion20261105.Runtime.decoded_call_refines
#print axioms JurisLean.CN.Completion20261105.Runtime.decoded_value_is_actual
#print axioms JurisLean.CN.Completion20261105.Runtime.malformed_keeps_state
#print axioms JurisLean.CN.Completion20261105.Acceptance.three_unknown_exits_are_actual
#print axioms JurisLean.CN.Completion20261105.Acceptance.actual_conflict_is_suspended
#print axioms JurisLean.CN.Completion20261105.Acceptance.three_other_sources_stay_separate
#print axioms JurisLean.CN.Completion20261105.Examples.no_source_no_model_judgment
#print axioms JurisLean.CN.Completion20261105.no_authority_no_legal_change
#print axioms JurisLean.CN.Completion20261105.FiveHistory.no_new_decision_binding
#print axioms JurisLean.CN.Revision20261101.no_grants_no_authority
#print axioms JurisLean.CN.Revision20261101.lawyer_cannot_add_template
#print axioms JurisLean.CN.Revision20261101.court_name_alone_insufficient
#print axioms JurisLean.CN.Revision20261101.false_conjunct_decisive
#print axioms JurisLean.CN.Revision20261101.unknown_not_false
#print axioms JurisLean.CN.Revision20261101.unresolved_ne_selected
#print axioms JurisLean.CN.Revision20261101.article105_routes_differ
#print axioms JurisLean.CN.Revision20261101.no_causal_permit_no_bridge
#print axioms JurisLean.CN.Revision20261101.request_maps_to_claim
#print axioms JurisLean.CN.Revision20261101.formation_maps_to_power
#print axioms JurisLean.CN.Revision20261101.defense_not_noRight
#print axioms JurisLean.CN.Revision20261101.domination_contains_privilege
#print axioms JurisLean.CN.Revision20261101.counterpart_preserves_scope
#print axioms JurisLean.CN.Revision20261101.counterpart_twice
#print axioms JurisLean.CN.Revision20261101.revocable_and_effective
#print axioms JurisLean.CN.Revision20261101.revocation_keeps_establishment
#print axioms JurisLean.CN.Revision20261101.delegation_keeps_principal_capacity
#print axioms JurisLean.CN.Revision20261101.proven_bad_faith_fails
#print axioms JurisLean.CN.Revision20261101.unchecked_good_faith_stays_unknown
#print axioms JurisLean.CN.Revision20261101.ordinary_needs_no_agreement
#print axioms JurisLean.CN.Revision20261101.appearance_cannot_override_exclusive
#print axioms JurisLean.CN.Revision20261101.limitation_preserves_claim
#print axioms JurisLean.CN.Revision20261101.limitation_does_not_raise
#print axioms JurisLean.CN.Revision20261101.buckets_disjoint
#print axioms JurisLean.CN.Revision20261101.admitted_implies_raw
#print axioms JurisLean.CN.Revision20261101.absent_not_admitted
#print axioms JurisLean.CN.Revision20261101.excluded_keeps_raw
#print axioms JurisLean.CN.Revision20261101.no_authority_no_creation
#print axioms JurisLean.CN.Revision20261101.confirmatory_preserves_relations
#print axioms JurisLean.CN.Revision20261101.refused_automated_step
#print axioms JurisLean.CN.Revision20261101.propose_frame
#print axioms JurisLean.CN.Revision20261101.learn_frame
#print axioms JurisLean.CN.Revision20261101.admission_frame
#print axioms JurisLean.CN.Revision20261101.withdrawal_preserves_reality
#print axioms JurisLean.CN.Revision20261101.append_keeps_history_length
#print axioms JurisLean.CN.Revision20261101.prepared_has_compatible_world
#print axioms JurisLean.CN.Revision20261101.nonjudicial_formation_exists
#print axioms JurisLean.CN.Revision20261101.no_receipt_no_guard_support
#print axioms JurisLean.CN.Revision20261101.admitted_guard_has_support
#print axioms JurisLean.CN.Revision20261101.withdrawal_removes_support
#print axioms JurisLean.CN.Revision20261101.withdrawal_keeps_excluded_and_raw
#print axioms JurisLean.CN.Revision20261101.proposal_is_not_learning
#print axioms JurisLean.Candidates.LearningConsumer20261027.u01_6_fit_card_minimizes_actual_sample
#print axioms JurisLean.Candidates.Final20261021.Probability.posterior_mass
#print axioms JurisLean.Candidates.CausalSelection20261027.selected_weight_recovery
#print axioms JurisLean.Candidates.Final20261021.Decision.legal_best_sound
#print axioms JurisLean.Candidates.Final20261021.Ledger.u09_1_quantity_conservation
#print axioms JurisLean.Candidates.Final20261021.Ledger.performance_cash_consistent
#print axioms JurisLean.Candidates.Final20261021.Ledger.writeoff_conserves
#print axioms JurisLean.Candidates.Final20261021.Decision.u06_3_eval_exists
#print axioms JurisLean.Candidates.Final20261021.Decision.u06_3_eval_unique
#print axioms JurisLean.Candidates.PolicyResponse20261027.finite_response_payoffs
#print axioms JurisLean.Candidates.AdaptiveRoundLedger20261027.finish_round_preserves_budget
#print axioms JurisLean.Candidates.AdaptiveRoundLedger20261027.assessed_load_comes_from_actual_activation
#print axioms JurisLean.Candidates.AdaptiveRoundLedger20261027.recorded_load_is_actual_next_service

/- Exercise the same IO entrypoints through this actual aggregate. -/
#eval do
  JurisLean.CN.Completion20261105.Runtime.checkIO
  JurisLean.CN.Completion20261105.EngineExamples.checkIO
  JurisLean.CN.Completion20261105.Acceptance.ioChecks
  IO.println "CN_FINAL_SCOPE_ACCEPTANCE_PASS"
