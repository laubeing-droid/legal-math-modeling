import JurisLean.FiniteMonotoneIteration
import JurisLean.DungFixedPoint
import JurisLean.HornFixedPoint
import JurisLean.WeightedSupNorm
import JurisLean.ULMAxiomAudit
import JurisLean.Genealogy.All
import JurisLean.KernelV3
import JurisLean.Hohfeld
import JurisLean.BanachCertificate

import JurisLean.BusinessRoot.Analytics
import JurisLean.FullMath.Probability.BetaInterval
import JurisLean.FullMath.Probability.Brier
import JurisLean.FullMath.Probability.Conditioning
import JurisLean.FullMath.Probability.DirichletPosterior
import JurisLean.FullMath.Probability.E01Contract
import JurisLean.FullMath.Probability.EvidenceIdentity
import JurisLean.FullMath.Probability.FiniteBN
import JurisLean.FullMath.Probability.Misspecification
import JurisLean.FullMath.Probability.ModelAveraging
import JurisLean.FullMath.Probability.PAV
import JurisLean.FullMath.Probability.SplitNoLeak
import JurisLean.FullMath.Probability.UnprocessedMass
import JurisLean.FullMath.Probability.VariableElimination

import JurisLean.Mandate.CohortInterval
import JurisLean.Mandate.CohortRate
import JurisLean.Mandate.DerivedCertificate
import JurisLean.Mandate.Disclosure
import JurisLean.Mandate.GameTree
import JurisLean.Mandate.GateTable
import JurisLean.Mandate.Kernel
import JurisLean.Mandate.LinearScorer
import JurisLean.Mandate.MatrixGame
import JurisLean.Mandate.RouteDecision
import JurisLean.Mandate.SourceRank
import JurisLean.Mandate.StructureInvariants
import JurisLean.Mandate.SubstrAdmission
import JurisLean.Mandate.TaxSlices
import JurisLean.Mandate.Waterfall

import JurisLean.Mandate.CaseIsomorphism

/-! Axiom audit for formal core release v1. -/

open FiniteMonotoneSystem
#print axioms exists_fixpoint_le_card
#print axioms fixed_at_card

open DungAAF
#print axioms grounded_is_least_fixed_point

open HornSystem
#print axioms horn_completeness
#print axioms horn_result_unique_least_fixed_point

#print axioms weightedSupDist_separates_points

#print axioms JurisLean.KernelV3.mkEval_judgment
#print axioms JurisLean.KernelV3.mkEval_disposition
#print axioms JurisLean.KernelV3.judgment_notEstablished_does_not_force_truth_false
#print axioms JurisLean.KernelV3.transfer_confirmatory_identity
#print axioms JurisLean.KernelV3.transfer_performance_identity
#print axioms JurisLean.KernelV3.transfer_proceduralBinding_identity
#print axioms JurisLean.KernelV3.transfer_constitutive_updates_R
#print axioms JurisLean.KernelV3.transfer_constitutive_preserves_K
#print axioms JurisLean.KernelV3.narrowCandidates_preserves_R
#print axioms JurisLean.KernelV3.narrowCandidates_is_subset
#print axioms JurisLean.KernelV3.evalBatch_only_returns_asked_questions
#print axioms JurisLean.KernelV3.procedural_judgment_does_not_auto_create_substantive
#print axioms JurisLean.KernelV3.applicableNorm_t_not_independent
#print axioms JurisLean.KernelV3.applicableNorm_fails_closed_when_t_precedes_fact

#print axioms JurisLean.Hohfeld.opposite_involutive
#print axioms JurisLean.Hohfeld.correlative_involutive
#print axioms JurisLean.Hohfeld.opposite_ne_self
#print axioms JurisLean.Hohfeld.correlative_ne_self

#print axioms JurisLean.BanachCertificateV3.no_certificate_rejected
#print axioms JurisLean.BanachCertificateV3.certificate_has_q_lt_one_scaled
#print axioms JurisLean.BanachCertificateV3.certificate_error_within_tolerance
#print axioms JurisLean.BanachCertificateV3.certificate_has_nonempty_domain
#print axioms JurisLean.BanachCertificateV3.certificate_has_positive_iterations

/-! Genealogy theorem-level campaign (142 theorems). -/
#print axioms JurisLean.Genealogy.Part0.P002.same_pair_same_concept
#print axioms JurisLean.Genealogy.Part0.P002.different_pair_different_concept
#print axioms JurisLean.Genealogy.Part0.P003.translation_preserves_definition_id
#print axioms JurisLean.Genealogy.Part0.P003.canonical_slot_is_single_valued
#print axioms JurisLean.Genealogy.Part0.P009.strictly_increasing_version_enters
#print axioms JurisLean.Genealogy.Part0.P009.nonincreasing_version_is_outside
#print axioms JurisLean.Genealogy.Part0.P010.anonymization_exits_personal_set
#print axioms JurisLean.Genealogy.Part0.P010.sensitive_triple_consent_positive
#print axioms JurisLean.Genealogy.Part0.P036.obligational_signature_mismatch
#print axioms JurisLean.Genealogy.Part0.P036.real_signature_mismatch
#print axioms JurisLean.Genealogy.Part0.P012.interruption_restarts
#print axioms JurisLean.Genealogy.Part0.P012.second_commencement_is_identity
#print axioms JurisLean.Genealogy.Part1.P014.source_grade_total
#print axioms JurisLean.Genealogy.Part1.P015.lex_superior_left
#print axioms JurisLean.Genealogy.Part1.P015.old_special_vs_new_general_unknown
#print axioms JurisLean.Genealogy.Part1.P015.same_rank_day_nature_unknown
#print axioms JurisLean.Genealogy.Part1.P018.transition_requires_version_and_fact
#print axioms JurisLean.Genealogy.Part1.P018.transition_version_mismatch_holds
#print axioms JurisLean.Genealogy.Part1.P019.shall_refer_without_reason_follows
#print axioms JurisLean.Genealogy.Part1.P019.may_reference_nonbinding
#print axioms JurisLean.Genealogy.Part1.P020.specialized_rule_wins_first
#print axioms JurisLean.Genealogy.Part1.P020.no_applicable_rule_returns_none
#print axioms JurisLean.Genealogy.Part1.P021.renvoi_back_uses_forum_and_terminates
#print axioms JurisLean.Genealogy.Part1.P022.named_rule_removed
#print axioms JurisLean.Genealogy.Part1.P022.other_rule_preserved
#print axioms JurisLean.Genealogy.Part1.P023.missing_version_unknown
#print axioms JurisLean.Genealogy.Part1.P023.missing_jurisdiction_unknown
#print axioms JurisLean.Genealogy.Part1.P024.cause_route_head_hit
#print axioms JurisLean.Genealogy.Part1.P024.cause_route_empty_unknown
#print axioms JurisLean.Genealogy.Part2.P029.secondary_without_primary_violation_is_false
#print axioms JurisLean.Genealogy.Part2.P029.matching_secondary_attachment
#print axioms JurisLean.Genealogy.Part2.P034.claim_available_complete_iff
#print axioms JurisLean.Genealogy.Part2.P034.unregistered_basis_unknown
#print axioms JurisLean.Genealogy.Part2.P035.agency_attributes_principal
#print axioms JurisLean.Genealogy.Part2.P035.representation_outside_scope_none
#print axioms JurisLean.Genealogy.Part2.P035.impersonation_ratified_principal
#print axioms JurisLean.Genealogy.Part2.P038.competition_is_three_way_conjunction
#print axioms JurisLean.Genealogy.Part2.P038.all_three_true_establish
#print axioms JurisLean.Genealogy.Part3.P042.equal_factors_fixed
#print axioms JurisLean.Genealogy.Part3.P042.weakest_factor_witness
#print axioms JurisLean.Genealogy.Part3.P047.two_sided_but_for_true
#print axioms JurisLean.Genealogy.Part3.P047.one_side_missing_unknown
#print axioms JurisLean.Genealogy.Part3.P048.exemption_requires_own_elements
#print axioms JurisLean.Genealogy.Part3.P048.exemption_complete_witness
#print axioms JurisLean.Genealogy.Part3.P049.good_cause_extension_admits
#print axioms JurisLean.Genealogy.Part3.P049.late_without_good_cause_barred
#print axioms JurisLean.Genealogy.Part3.P050.any_listed_illegality_excludes
#print axioms JurisLean.Genealogy.Part3.P050.empty_exclusion_list_does_not_exclude
#print axioms JurisLean.Genealogy.Part3.P051.boundary_inputs_complete
#print axioms JurisLean.Genealogy.Part3.P051.boundary_records_input_only
#print axioms JurisLean.Genealogy.Part3.P052.mapping_complete_iff_all_required_traced
#print axioms JurisLean.Genealogy.Part3.P052.mapping_complete_witness
#print axioms JurisLean.Genealogy.Part3.P094.first_present_anchor_witness
#print axioms JurisLean.Genealogy.Part3.P094.empty_anchor_rules_unknown
#print axioms JurisLean.Genealogy.Part3.P095.commencement_cell_hit
#print axioms JurisLean.Genealogy.Part3.P095.empty_commencement_matrix_unknown
#print axioms JurisLean.Genealogy.Part4.P057.analogy_three_conditions
#print axioms JurisLean.Genealogy.Part4.P057.distinction_blocks_analogy
#print axioms JurisLean.Genealogy.Part4.P058.toulmin_six_slot_witness
#print axioms JurisLean.Genealogy.Part4.P060.isolated_branch_preserved
#print axioms JurisLean.Genealogy.Part4.P061.pinned_reading_immune_to_low_attack
#print axioms JurisLean.Genealogy.Part4.P062.two_senses_without_context_ambiguous
#print axioms JurisLean.Genealogy.Part4.P062.context_resolves
#print axioms JurisLean.Genealogy.Part4.P063.rule_all_or_nothing_true
#print axioms JurisLean.Genealogy.Part4.P063.principle_positive_weight_is_weight_only
#print axioms JurisLean.Genealogy.Part4.P064.preorder_with_legal_incomparability
#print axioms JurisLean.Genealogy.Part4.P065.lawmaking_requires_three_true
#print axioms JurisLean.Genealogy.Part4.P065.missing_gap_signal_blocks
#print axioms JurisLean.Genealogy.Part4.P066.gap_detection_preserves_signal_roster
#print axioms JurisLean.Genealogy.Part4.P066.gap_signal_detected
#print axioms JurisLean.Genealogy.Part4.P068.several_without_share_invalid
#print axioms JurisLean.Genealogy.Part4.P068.several_with_share_valid
#print axioms JurisLean.Genealogy.Part4.P070.unknown_damage_none
#print axioms JurisLean.Genealogy.Part4.P070.registered_damage_witness
#print axioms JurisLean.Genealogy.Part4.P073.declaration_floor_is_max
#print axioms JurisLean.Genealogy.Part4.P073.declaration_band_order_witness
#print axioms JurisLean.Genealogy.Part4.P074.prohibited_is_illegal
#print axioms JurisLean.Genealogy.Part4.P074.unknown_unlawfulness_is_violation
#print axioms JurisLean.Genealogy.Part4.P078.mediation_overlap_witness
#print axioms JurisLean.Genealogy.Part4.P078.mediation_disjoint_witness
#print axioms JurisLean.Genealogy.Part4.P079.settlement_ev_accept_witness
#print axioms JurisLean.Genealogy.Part4.P079.settlement_ev_reject_witness
#print axioms JurisLean.Genealogy.Part4.P080.plea_fixed_prefix_advances
#print axioms JurisLean.Genealogy.Part4.P080.plea_skip_fails_closed
#print axioms JurisLean.Genealogy.Part4.P081.fraud_voids_tactic
#print axioms JurisLean.Genealogy.Part4.P082.preservation_without_ground_infeasible
#print axioms JurisLean.Genealogy.Part4.P084.appeal_ev_positive_witness
#print axioms JurisLean.Genealogy.Part4.P084.appeal_ev_negative_witness
#print axioms JurisLean.Genealogy.Part4.P085.undisclosed_fee_none
#print axioms JurisLean.Genealogy.Part4.P086.contingency_fee_cap_witness
#print axioms JurisLean.Genealogy.Part4.P086.contingency_fee_below_cap_witness
#print axioms JurisLean.Genealogy.Part4.P087.should_follow_iff_reason_absent
#print axioms JurisLean.Genealogy.Part4.P089.retrieval_two_true_compliant
#print axioms JurisLean.Genealogy.Part4.P089.retrieval_missing_report_noncompliant
#print axioms JurisLean.Genealogy.Part5.P096.two_segment_refinement
#print axioms JurisLean.Genealogy.Part5.P096.empty_segments_zero
#print axioms JurisLean.Genealogy.Part5.P097.allocate_one_underfunded
#print axioms JurisLean.Genealogy.Part5.P097.allocate_one_overfunded
#print axioms JurisLean.Genealogy.Part5.P097.two_debt_conservation_witness
#print axioms JurisLean.Genealogy.Part5.P098.clamp_below_to_low
#print axioms JurisLean.Genealogy.Part5.P098.clamp_below_in_band
#print axioms JurisLean.Genealogy.Part5.P098.clamp_above_to_high
#print axioms JurisLean.Genealogy.Part5.P098.clamp_above_in_band
#print axioms JurisLean.Genealogy.Part5.P098.clamp_inside_fixed
#print axioms JurisLean.Genealogy.Part5.P098.clamp_inside_idempotent
#print axioms JurisLean.Genealogy.Part5.P099.progressive_three_bracket_witness
#print axioms JurisLean.Genealogy.Part5.P099.progressive_two_effective_brackets_witness
#print axioms JurisLean.Genealogy.Part5.P100.unknown_damage_formula_none
#print axioms JurisLean.Genealogy.Part5.P100.registered_damage_formula_witness
#print axioms JurisLean.Genealogy.Part5.P102.delay_interest_formula
#print axioms JurisLean.Genealogy.Part5.P103.no_consent_no_transition
#print axioms JurisLean.Genealogy.Part5.P103.consent_and_legal_edge_moves
#print axioms JurisLean.Genealogy.Part5.P103.consent_cannot_create_nonedge
#print axioms JurisLean.Genealogy.Part5.P114.deduction_bridges
#print axioms JurisLean.Genealogy.Part5.P114.probability_one_not_deduction
#print axioms JurisLean.Genealogy.Part5.P117.structural_equivalence_assertion_invalid
#print axioms JurisLean.Genealogy.Part5.P117.similarity_stays_candidate
#print axioms JurisLean.Genealogy.Part6.P105.disposition_valid_path
#print axioms JurisLean.Genealogy.Part6.P105.disposition_invalid_jump
#print axioms JurisLean.Genealogy.Part6.P106.swapped_parties_same_subject
#print axioms JurisLean.Genealogy.Part6.P106.different_cause_not_same_subject
#print axioms JurisLean.Genealogy.Part6.P107.legal_fact_script_rejected
#print axioms JurisLean.Genealogy.Part6.P121.failed_gate_keeps_candidate
#print axioms JurisLean.Genealogy.Part6.P121.passed_gate_sets_admitted
#print axioms JurisLean.Genealogy.Part6.P122.version_triplet_binding_identity
#print axioms JurisLean.Genealogy.Part6.P124.disclosed_is_compliant
#print axioms JurisLean.Genealogy.Part6.P124.undisclosed_is_noncompliant
#print axioms JurisLean.Genealogy.Part6.P125.detected_pattern_blocks
#print axioms JurisLean.Genealogy.Part6.P126.foreign_unadapted_blocked
#print axioms JurisLean.Genealogy.Part6.P126.home_jurisdiction_not_blocked
#print axioms JurisLean.Genealogy.Part6.P127.verbatim_prefix_hit_witness
#print axioms JurisLean.Genealogy.Part6.P127.verbatim_prefix_miss_witness
#print axioms JurisLean.Genealogy.Part6.P128.all_due_process_elements_present
#print axioms JurisLean.Genealogy.Part6.P128.missing_reason_record_fails
#print axioms JurisLean.Genealogy.Part6.P129.anonymization_boundary_two_conditions
#print axioms JurisLean.Genealogy.Part6.P130.lifecycle_listed_edge_valid
#print axioms JurisLean.Genealogy.Part6.P130.lifecycle_unlisted_edge_invalid
#print axioms JurisLean.Genealogy.Part6.P131.replay_empty_log_idempotent
#print axioms JurisLean.Genealogy.Part6.P131.existing_command_replay_witness
#print axioms JurisLean.Genealogy.Part6.P132.listed_action_requires_its_gate

/-! Round 9: general upgrades + boundary theorems. -/
#print axioms JurisLean.Genealogy.General.P052_subsumeComplete_iff_all
#print axioms JurisLean.Genealogy.General.P042_min3Nat_le_all
#print axioms JurisLean.Genealogy.General.P042_grade_capped
#print axioms JurisLean.Genealogy.General.P073_le_maxNat_left
#print axioms JurisLean.Genealogy.General.P073_mergedDeclaration_low_le_high
#print axioms JurisLean.Genealogy.General.P084_mul_monotone_probability_strict
#print axioms JurisLean.Genealogy.General.P084_appealWorthwhile_of_mul_le
#print axioms JurisLean.Genealogy.General.P084_appealWorthwhile_monotone_strict
#print axioms JurisLean.Genealogy.General.P097_add_assoc_local
#print axioms JurisLean.Genealogy.General.P097_allocate_conservation
#print axioms JurisLean.Genealogy.General.P099_progressiveTax3_nonnegative
#print axioms JurisLean.Genealogy.General.P099_progressiveTax3_first_bracket
#print axioms JurisLean.Genealogy.General.P127_isPrefixChars_refl_list
#print axioms JurisLean.Genealogy.General.P127_isPrefixChars_refl
#print axioms JurisLean.Genealogy.General.P127_prepend_monotonicity_counterexample
#print axioms JurisLean.Genealogy.General.P127_isPrefixChars_append_right
#print axioms JurisLean.Genealogy.General.P131_effectLogApply_idempotent
#print axioms JurisLean.Genealogy.Boundary.partialValue_openObligations_nonempty
#print axioms JurisLean.Genealogy.Boundary.failure_map_identity
#print axioms JurisLean.Genealogy.Boundary.noExtensions_family_empty
#print axioms JurisLean.Genealogy.Boundary.incomplete_adjudication_is_solverIncomplete
#print axioms JurisLean.Genealogy.Boundary.adverseAuthority_requires_unmet

/-! T-spectrum batch 1. -/
#print axioms JurisLean.Genealogy.TSpectrum.T01.eval_substitution
#print axioms JurisLean.Genealogy.TSpectrum.T02.finite_ground_instances
#print axioms JurisLean.Genealogy.TSpectrum.T03.iter_subset_of_prefixed
#print axioms JurisLean.Genealogy.TSpectrum.T04.derived_iff_rule_model_entails
#print axioms JurisLean.Genealogy.TSpectrum.T05.undercut_defeat_independent_of_preference
#print axioms JurisLean.Genealogy.TSpectrum.T05.rebuttal_counterexample
#print axioms JurisLean.Genealogy.TSpectrum.T06.transition_origin
#print axioms JurisLean.Genealogy.TSpectrum.T07.eval_exactexpr_denotation
#print axioms JurisLean.Genealogy.TSpectrum.T08.division_total_iff_domain_empty
#print axioms JurisLean.Genealogy.TSpectrum.T09.rounding_without_basis_unknown
#print axioms JurisLean.Genealogy.TSpectrum.T10.select_version_unique_or_unknown
#print axioms JurisLean.Genealogy.TSpectrum.T11.one_hop_renvoi_terminates
#print axioms JurisLean.Genealogy.TSpectrum.T12.scoped_override_preserves_unaffected_rules
#print axioms JurisLean.Genealogy.TSpectrum.T13.parallel_projection
#print axioms JurisLean.Genealogy.TSpectrum.T14.strictest_is_join
#print axioms JurisLean.Genealogy.TSpectrum.T15.truth_vector_bisimulation
#print axioms JurisLean.Genealogy.TSpectrum.T16.check_af_sound
#print axioms JurisLean.Genealogy.TSpectrum.T17.anchor_selected_by_rule
#print axioms JurisLean.Genealogy.TSpectrum.T18.period_effect_bound_to_kind
#print axioms JurisLean.Genealogy.TSpectrum.T19.progressive_and_multiplier_correct
#print axioms JurisLean.Genealogy.TSpectrum.T20.route_and_exclusion_sound

/-! T-spectrum batch 2. -/
#print axioms JurisLean.Genealogy.TSpectrum.T21.interest_segment_refinement
#print axioms JurisLean.Genealogy.TSpectrum.T22.residual_payment_le
#print axioms JurisLean.Genealogy.TSpectrum.T22.payment_offset_conservation
#print axioms JurisLean.Genealogy.TSpectrum.T23.fixed_scheme_conservation
#print axioms JurisLean.Genealogy.TSpectrum.T24.asset_pool_no_duplicate_consumption
#print axioms JurisLean.Genealogy.TSpectrum.T25.priority_waterfall_monotone
#print axioms JurisLean.Genealogy.TSpectrum.T26.interruption_resume_preserves_checkpoint
#print axioms JurisLean.Genealogy.TSpectrum.T27.admitted_rule_has_four_witnesses
#print axioms JurisLean.Genealogy.TSpectrum.T28.compile_structure_preserving
#print axioms JurisLean.Genealogy.TSpectrum.T29.evaluate_multi_contract
#print axioms JurisLean.Genealogy.TSpectrum.T30.version_package_isolation
#print axioms JurisLean.Genealogy.TSpectrum.T31.record_override_audit
#print axioms JurisLean.Genealogy.TSpectrum.T32.runtime_reference_consistency
#print axioms JurisLean.Genealogy.TSpectrum.T33.external_output_does_not_relabel
#print axioms JurisLean.Genealogy.TSpectrum.T34.business_does_not_pollute_legal
#print axioms JurisLean.Genealogy.TSpectrum.T35.paper_claim_consistency
#print axioms JurisLean.Genealogy.TSpectrum.T36.completion_acceptance
#print axioms JurisLean.Genealogy.TSpectrum.T37.unified_probability_preserves_legal_identity
#print axioms JurisLean.Genealogy.TSpectrum.T38.conditioning_zero_mass_unknown
#print axioms JurisLean.Genealogy.TSpectrum.T38.conditioning_excludes_false_event
#print axioms JurisLean.Genealogy.TSpectrum.T39.variable_elimination_equals_independent_enumeration
#print axioms JurisLean.Genealogy.TSpectrum.T40.observational_identity
#print axioms JurisLean.Genealogy.TSpectrum.T40.hidden_change_preserves_observation

/-! T-spectrum batch 3. -/
#print axioms JurisLean.Genealogy.TSpectrum.T41.valid_split_requires_time_order
#print axioms JurisLean.Genealogy.TSpectrum.T42.fully_specified_witness
#print axioms JurisLean.Genealogy.TSpectrum.T43.observed_only_count
#print axioms JurisLean.Genealogy.TSpectrum.T44.empirical_requires_justification
#print axioms JurisLean.Genealogy.TSpectrum.T45.calibration_recorded
#print axioms JurisLean.Genealogy.TSpectrum.T46.proper_posterior_witness
#print axioms JurisLean.Genealogy.TSpectrum.T47.legal_identity_preserved
#print axioms JurisLean.Genealogy.TSpectrum.T48.pav_single_fixed
#print axioms JurisLean.Genealogy.TSpectrum.T49.brier_perfect_prediction
#print axioms JurisLean.Genealogy.TSpectrum.T50.valid_interval_witness
#print axioms JurisLean.Genealogy.TSpectrum.T51.direction_explicit
#print axioms JurisLean.Genealogy.TSpectrum.T52.contaminated_zero_weight
#print axioms JurisLean.Genealogy.TSpectrum.T53.bound_witness
#print axioms JurisLean.Genealogy.TSpectrum.T54.logistic_deterministic
#print axioms JurisLean.Genealogy.TSpectrum.T55.stages_strictly_ordered
#print axioms JurisLean.Genealogy.TSpectrum.T56.signature_deterministic
#print axioms JurisLean.Genealogy.TSpectrum.T57.directed_witness
#print axioms JurisLean.Genealogy.TSpectrum.T58.complete_difference
#print axioms JurisLean.Genealogy.TSpectrum.T59.horn_form_deterministic
#print axioms JurisLean.Genealogy.TSpectrum.T60.role_preservation

/-! T-spectrum batch 4 (T61-T127). -/
#print axioms JurisLean.Genealogy.TSpectrum.T61.T61_conflict_deterministic
#print axioms JurisLean.Genealogy.TSpectrum.T62.T62_mandatory_overrides
#print axioms JurisLean.Genealogy.TSpectrum.T63.T63_fail_closed
#print axioms JurisLean.Genealogy.TSpectrum.T64.T64_bias_explicit
#print axioms JurisLean.Genealogy.TSpectrum.T65.T65_version_tracked
#print axioms JurisLean.Genealogy.TSpectrum.T66.T66_certificate_fields
#print axioms JurisLean.Genealogy.TSpectrum.T67.T67_vc_declared
#print axioms JurisLean.Genealogy.TSpectrum.T68.T68_certified_witness
#print axioms JurisLean.Genealogy.TSpectrum.T69.T69_chain_independent
#print axioms JurisLean.Genealogy.TSpectrum.T70.T70_llm_always_candidate
#print axioms JurisLean.Genealogy.TSpectrum.T71.T71_ig_recorded
#print axioms JurisLean.Genealogy.TSpectrum.T72.T72_completion_declared
#print axioms JurisLean.Genealogy.TSpectrum.T73.T73_lipschitz_bounded
#print axioms JurisLean.Genealogy.TSpectrum.T74.T74_stopping_explicit
#print axioms JurisLean.Genealogy.TSpectrum.T75.T75_trust_numeric
#print axioms JurisLean.Genealogy.TSpectrum.T76.T76_dtmc_finite
#print axioms JurisLean.Genealogy.TSpectrum.T77.T77_reach_finite
#print axioms JurisLean.Genealogy.TSpectrum.T78.T78_bellman_declared
#print axioms JurisLean.Genealogy.TSpectrum.T79.T79_mdp_finite
#print axioms JurisLean.Genealogy.TSpectrum.T80.T80_lp_explicit
#print axioms JurisLean.Genealogy.TSpectrum.T81.T81_nash_feasible
#print axioms JurisLean.Genealogy.TSpectrum.T82.T82_game_grounded
#print axioms JurisLean.Genealogy.TSpectrum.T83.T83_stochastic_declared
#print axioms JurisLean.Genealogy.TSpectrum.T84.T84_fit_dual
#print axioms JurisLean.Genealogy.TSpectrum.T85.T85_info_computed
#print axioms JurisLean.Genealogy.TSpectrum.T86.T86_disclosure_separate
#print axioms JurisLean.Genealogy.TSpectrum.T87.T87_spectral_finite
#print axioms JurisLean.Genealogy.TSpectrum.T88.T88_scm_witness
#print axioms JurisLean.Genealogy.TSpectrum.T89.T89_belief_distinguished
#print axioms JurisLean.Genealogy.TSpectrum.T90.T90_timing_declared
#print axioms JurisLean.Genealogy.TSpectrum.T91.T91_category_concrete
#print axioms JurisLean.Genealogy.TSpectrum.T92.T92_lifecycle_tracked
#print axioms JurisLean.Genealogy.TSpectrum.T93.T93_recovery_tracked
#print axioms JurisLean.Genealogy.TSpectrum.T94.T94_gate_explicit
#print axioms JurisLean.Genealogy.TSpectrum.T95.T95_structure_kept
#print axioms JurisLean.Genealogy.TSpectrum.T96.T96_trace_kept
#print axioms JurisLean.Genealogy.TSpectrum.T97.T97_template_tracked
#print axioms JurisLean.Genealogy.TSpectrum.T98.T98_schedule_tracked
#print axioms JurisLean.Genealogy.TSpectrum.T99.T99_graph_tracked
#print axioms JurisLean.Genealogy.TSpectrum.T100.T100_chain_tracked
#print axioms JurisLean.Genealogy.TSpectrum.T101.T101_business_computed
#print axioms JurisLean.Genealogy.TSpectrum.T102.T102_distillation_tracked
#print axioms JurisLean.Genealogy.TSpectrum.T103.T103_anon_verified
#print axioms JurisLean.Genealogy.TSpectrum.T104.T104_projection_declared
#print axioms JurisLean.Genealogy.TSpectrum.T105.T105_bridge_refined
#print axioms JurisLean.Genealogy.TSpectrum.T106.T106_map_tracked
#print axioms JurisLean.Genealogy.TSpectrum.T107.T107_coverage_declared
#print axioms JurisLean.Genealogy.TSpectrum.T108.T108_writeoff_tracked
#print axioms JurisLean.Genealogy.TSpectrum.T109.T109_unified_declared
#print axioms JurisLean.Genealogy.TSpectrum.T110.T110_ceiling_set
#print axioms JurisLean.Genealogy.TSpectrum.T111.T111_acceptance_tracked
#print axioms JurisLean.Genealogy.TSpectrum.T112.T112_dual_track_separated
#print axioms JurisLean.Genealogy.TSpectrum.T113.T113_rationality_declared
#print axioms JurisLean.Genealogy.TSpectrum.T114.T114_hidden_info_tracked
#print axioms JurisLean.Genealogy.TSpectrum.T115.T115_cooperation_declared
#print axioms JurisLean.Genealogy.TSpectrum.T116.T116_multi_issue_tracked
#print axioms JurisLean.Genealogy.TSpectrum.T117.T117_robustness_tracked
#print axioms JurisLean.Genealogy.TSpectrum.T118.T118_stopping_tracked
#print axioms JurisLean.Genealogy.TSpectrum.T119.T119_evaluation_three_way
#print axioms JurisLean.Genealogy.TSpectrum.T120.T120_incentive_tracked
#print axioms JurisLean.Genealogy.TSpectrum.T121.T121_transition_tracked
#print axioms JurisLean.Genealogy.TSpectrum.T122.T122_five_constructors
#print axioms JurisLean.Genealogy.TSpectrum.T123.T123_attack_table_tracked
#print axioms JurisLean.Genealogy.TSpectrum.T124.T124_consistency_tracked
#print axioms JurisLean.Genealogy.TSpectrum.T125.T125_deviation_tracked
#print axioms JurisLean.Genealogy.TSpectrum.T126.T126_tendency_stratified
#print axioms JurisLean.Genealogy.TSpectrum.T127.T127_report_generated

/-! P083 complete (Prop-if version). -/
#print axioms JurisLean.Genealogy.General.P083_insertEvpi_length
#print axioms JurisLean.Genealogy.General.P083_sortEvpi_length
#print axioms JurisLean.Genealogy.General.P083_insertEvpi_preserves_sortedP
#print axioms JurisLean.Genealogy.General.P083_sortEvpi_sortedP
#print axioms JurisLean.Genealogy.General.P083_sortedDesc_witness

/-! Generated probability / expectation audit surface. Regenerate with
      scripts/ci/generate_probability_audit_surface.py --write
    These declarations are elaborated by the all-module CI plan but were
    absent from the release audit surface; the block is generated from the
    declaration sites, so it cannot name a theorem that does not exist. -/
#print axioms JurisLean.BusinessRoot.CU_expectation_conservation
#print axioms JurisLean.BusinessRoot.cres_false_eq
#print axioms JurisLean.BusinessRoot.cres_true_eq
#print axioms JurisLean.BusinessRoot.eventMass_twoBranch
#print axioms JurisLean.BusinessRoot.interval_point_not_in_grid
#print axioms JurisLean.BusinessRoot.main_eligible
#print axioms JurisLean.BusinessRoot.main_interval
#print axioms JurisLean.BusinessRoot.main_principal_expectation
#print axioms JurisLean.BusinessRoot.main_threshold_event
#print axioms JurisLean.BusinessRoot.overpay_overpay_expectation
#print axioms JurisLean.BusinessRoot.overpay_principal_expectation
#print axioms JurisLean.BusinessRoot.overpay_raw_expectation
#print axioms JurisLean.BusinessRoot.split_identity
#print axioms JurisLean.BusinessRoot.threshold_zero_distinction
#print axioms JurisLean.BusinessRoot.weighted_congr
#print axioms JurisLean.BusinessRoot.weighted_sub
#print axioms JurisLean.BusinessRoot.weighted_twoBranch
#print axioms JurisLean.FullMath.Probability.Gamma_add_nat
#print axioms JurisLean.FullMath.Probability.betaCDF_one
#print axioms JurisLean.FullMath.Probability.betaCDF_zero
#print axioms JurisLean.FullMath.Probability.beta_mass_total_one
#print axioms JurisLean.FullMath.Probability.beta_mixture_mass
#print axioms JurisLean.FullMath.Probability.beta_ratio
#print axioms JurisLean.FullMath.Probability.brier_excess_identity
#print axioms JurisLean.FullMath.Probability.brier_excess_zero_iff
#print axioms JurisLean.FullMath.Probability.cantelli_core
#print axioms JurisLean.FullMath.Probability.condition_incompatible_iff
#print axioms JurisLean.FullMath.Probability.contaminate_bound
#print axioms JurisLean.FullMath.Probability.contaminate_condition_do_not_commute
#print axioms JurisLean.FullMath.Probability.contamination_bounds
#print axioms JurisLean.FullMath.Probability.dedupAux_cons_fresh
#print axioms JurisLean.FullMath.Probability.dedupAux_cons_seen
#print axioms JurisLean.FullMath.Probability.dedupAux_k_insensitive
#print axioms JurisLean.FullMath.Probability.dedup_conflict_not_overwrite
#print axioms JurisLean.FullMath.Probability.dedup_no_double_update
#print axioms JurisLean.FullMath.Probability.dirWeights_nonneg
#print axioms JurisLean.FullMath.Probability.dirWeights_normalizes
#print axioms JurisLean.FullMath.Probability.dirWeights_update_compose
#print axioms JurisLean.FullMath.Probability.e01_insufficient_escalates
#print axioms JurisLean.FullMath.Probability.e01_within_iff
#print axioms JurisLean.FullMath.Probability.elim_swap_adjacent
#print axioms JurisLean.FullMath.Probability.exclusion_no_langer
#print axioms JurisLean.FullMath.Probability.exclusion_no_langer_top
#print axioms JurisLean.FullMath.Probability.hyperWeights_normalizes
#print axioms JurisLean.FullMath.Probability.hyper_data_changes_posterior
#print axioms JurisLean.FullMath.Probability.illegal_row_in_no_part
#print axioms JurisLean.FullMath.Probability.isolated_no_shared_cluster
#print axioms JurisLean.FullMath.Probability.isolated_symm
#print axioms JurisLean.FullMath.Probability.joint_nonneg
#print axioms JurisLean.FullMath.Probability.joint_normalizes
#print axioms JurisLean.FullMath.Probability.mixture_update_normalizes
#print axioms JurisLean.FullMath.Probability.mixture_update_still_bracketed
#print axioms JurisLean.FullMath.Probability.mixture_within_retained
#print axioms JurisLean.FullMath.Probability.no_cluster_cross
#print axioms JurisLean.FullMath.Probability.part_target_preserved
#print axioms JurisLean.FullMath.Probability.parts_cover
#print axioms JurisLean.FullMath.Probability.pavGo_succ_cons
#print axioms JurisLean.FullMath.Probability.pavGo_weight_sum
#print axioms JurisLean.FullMath.Probability.pav_two_point_optimal
#print axioms JurisLean.FullMath.Probability.posterior_nonneg
#print axioms JurisLean.FullMath.Probability.posterior_normalizes
#print axioms JurisLean.FullMath.Probability.prodAt_append
#print axioms JurisLean.FullMath.Probability.rising_succ
#print axioms JurisLean.FullMath.Probability.sum_out_distrib
#print axioms JurisLean.FullMath.Probability.time_order_enforced
#print axioms JurisLean.FullMath.Probability.unprocessed_mass_bounds
#print axioms JurisLean.FullMath.Probability.unprocessed_mass_degenerate
#print axioms JurisLean.FullMath.Probability.upd_eq_exclSeen
#print axioms JurisLean.FullMath.Probability.upd_self
#print axioms JurisLean.FullMath.Probability.upd_swap

/-! Generated mandate-layer audit surface. Regenerate with
      scripts/ci/generate_probability_audit_surface.py --write
    These declarations are elaborated by the all-module CI plan but were
    absent from the release audit surface; the block is generated from the
    declaration sites, so it cannot name a theorem that does not exist. -/
#print axioms JurisLean.Mandate.CaseIsomorphism.allSelfRelated_of_iso
#print axioms JurisLean.Mandate.CaseIsomorphism.exists_bijective_inverse
#print axioms JurisLean.Mandate.CaseIsomorphism.iso_refl
#print axioms JurisLean.Mandate.CaseIsomorphism.iso_symm
#print axioms JurisLean.Mandate.CaseIsomorphism.iso_trans
#print axioms JurisLean.Mandate.CaseIsomorphism.iso_twoEmpty_swap
#print axioms JurisLean.Mandate.CaseIsomorphism.not_iso_looped_edgeless
#print axioms JurisLean.Mandate.CaseIsomorphism.swap2_bijective
#print axioms JurisLean.Mandate.CaseIsomorphism.swap2_moves_a_slot
#print axioms JurisLean.Mandate.CohortInterval.high_le_added_success
#print axioms JurisLean.Mandate.CohortInterval.high_num_le_den
#print axioms JurisLean.Mandate.CohortInterval.intervalOf_defined
#print axioms JurisLean.Mandate.CohortInterval.intervalOf_none_without_cohort
#print axioms JurisLean.Mandate.CohortInterval.interval_of_empty_successes_legal
#print axioms JurisLean.Mandate.CohortInterval.low_antitone_in_size
#print axioms JurisLean.Mandate.CohortInterval.low_le_added_success
#print axioms JurisLean.Mandate.CohortInterval.low_le_high
#print axioms JurisLean.Mandate.CohortInterval.low_num_le_den
#print axioms JurisLean.Mandate.CohortInterval.low_num_lt_high_num
#print axioms JurisLean.Mandate.CohortRate.addedFailure_le_rate
#print axioms JurisLean.Mandate.CohortRate.rateOfCohort_defined
#print axioms JurisLean.Mandate.CohortRate.rateOfCohort_none_iff
#print axioms JurisLean.Mandate.CohortRate.rateOfCohort_num_le_den
#print axioms JurisLean.Mandate.CohortRate.rate_le_addedSuccess
#print axioms JurisLean.Mandate.DerivedCertificate.admits_iff
#print axioms JurisLean.Mandate.DerivedCertificate.approx_closed
#print axioms JurisLean.Mandate.DerivedCertificate.approx_damped
#print axioms JurisLean.Mandate.DerivedCertificate.approx_error_eq_computedBound
#print axioms JurisLean.Mandate.DerivedCertificate.approx_zero
#print axioms JurisLean.Mandate.DerivedCertificate.certificate_bound_is_computed
#print axioms JurisLean.Mandate.DerivedCertificate.not_admits_negative
#print axioms JurisLean.Mandate.DerivedCertificate.pow_damped
#print axioms JurisLean.Mandate.DerivedCertificate.pow_nonneg_of_nonneg
#print axioms JurisLean.Mandate.Disclosure.compliant_concrete
#print axioms JurisLean.Mandate.Disclosure.compliant_true_iff_covers
#print axioms JurisLean.Mandate.Disclosure.covers_nil_recorded
#print axioms JurisLean.Mandate.Disclosure.not_covers_empty_registry
#print axioms JurisLean.Mandate.Disclosure.occurs_append
#print axioms JurisLean.Mandate.Disclosure.occurs_head
#print axioms JurisLean.Mandate.Disclosure.occurs_monotone
#print axioms JurisLean.Mandate.GameTree.leaves_leaf
#print axioms JurisLean.Mandate.GameTree.leaves_node
#print axioms JurisLean.Mandate.GameTree.value_attains
#print axioms JurisLean.Mandate.GameTree.value_ge_of_mem
#print axioms JurisLean.Mandate.GameTree.value_ignores_payoff_renaming_when_dominated
#print axioms JurisLean.Mandate.GameTree.value_le_value_left
#print axioms JurisLean.Mandate.GameTree.value_le_value_right
#print axioms JurisLean.Mandate.GameTree.value_leaf
#print axioms JurisLean.Mandate.GameTree.value_node
#print axioms JurisLean.Mandate.GateTable.gate_coverage_total
#print axioms JurisLean.Mandate.GateTable.gate_exists_unique
#print axioms JurisLean.Mandate.GateTable.gate_iff_table
#print axioms JurisLean.Mandate.GateTable.gate_ne_true_of_ne
#print axioms JurisLean.Mandate.GateTable.gate_table_no_duplicates
#print axioms JurisLean.Mandate.GateTable.gates_pairwise_distinct
#print axioms JurisLean.Mandate.Kernel.best_le_best_append
#print axioms JurisLean.Mandate.Kernel.le_max_l
#print axioms JurisLean.Mandate.Kernel.le_max_r
#print axioms JurisLean.Mandate.Kernel.max_zero
#print axioms JurisLean.Mandate.Kernel.rate_le_self
#print axioms JurisLean.Mandate.Kernel.rate_num_le_den
#print axioms JurisLean.Mandate.Kernel.sig3_edges_le_sum
#print axioms JurisLean.Mandate.Kernel.sig3_fst_le_sum
#print axioms JurisLean.Mandate.Kernel.sig3_relabel_edges
#print axioms JurisLean.Mandate.Kernel.sig3_relabel_fst
#print axioms JurisLean.Mandate.Kernel.sig3_relabel_snd
#print axioms JurisLean.Mandate.Kernel.sig3_sum
#print axioms JurisLean.Mandate.Kernel.successes_le_length
#print axioms JurisLean.Mandate.LinearScorer.not_predicts_of_neg
#print axioms JurisLean.Mandate.LinearScorer.predicts_scaled_positive
#print axioms JurisLean.Mandate.LinearScorer.predicts_true_of_nonneg
#print axioms JurisLean.Mandate.LinearScorer.score_cons
#print axioms JurisLean.Mandate.LinearScorer.score_nil_features
#print axioms JurisLean.Mandate.LinearScorer.score_nil_weights
#print axioms JurisLean.Mandate.LinearScorer.score_nonneg_of_allNonNeg
#print axioms JurisLean.Mandate.LinearScorer.score_not_constant
#print axioms JurisLean.Mandate.LinearScorer.score_zero_weights
#print axioms JurisLean.Mandate.MatrixGame.coordination_has_pure_value
#print axioms JurisLean.Mandate.MatrixGame.gap_bounded_by_spread
#print axioms JurisLean.Mandate.MatrixGame.hasPureValue_true_iff
#print axioms JurisLean.Mandate.MatrixGame.lower_le_upper
#print axioms JurisLean.Mandate.MatrixGame.lower_monotone_first
#print axioms JurisLean.Mandate.MatrixGame.pennies_gap_strict
#print axioms JurisLean.Mandate.MatrixGame.pennies_no_pure_value
#print axioms JurisLean.Mandate.MatrixGame.upper_monotone_column
#print axioms JurisLean.Mandate.RouteDecision.anyUsable_append
#print axioms JurisLean.Mandate.RouteDecision.excluded_is_skipped
#print axioms JurisLean.Mandate.RouteDecision.firstUsable_cons_notUsable
#print axioms JurisLean.Mandate.RouteDecision.firstUsable_cons_usable
#print axioms JurisLean.Mandate.RouteDecision.firstUsable_nil
#print axioms JurisLean.Mandate.RouteDecision.inactive_is_skipped
#print axioms JurisLean.Mandate.RouteDecision.priority_order_decides
#print axioms JurisLean.Mandate.RouteDecision.some_of_anyUsable_true
#print axioms JurisLean.Mandate.RouteDecision.usable_is_found
#print axioms JurisLean.Mandate.RouteDecision.usable_of_firstUsable_some
#print axioms JurisLean.Mandate.SourceRank.grade_binding_iff
#print axioms JurisLean.Mandate.SourceRank.grade_classes_inhabited
#print axioms JurisLean.Mandate.SourceRank.grade_exhaustive
#print axioms JurisLean.Mandate.SourceRank.grade_referenceOnly_iff
#print axioms JurisLean.Mandate.SourceRank.grade_shallRefer_iff
#print axioms JurisLean.Mandate.SourceRank.grade_single_valued
#print axioms JurisLean.Mandate.SourceRank.soft_law_never_binding
#print axioms JurisLean.Mandate.StructureInvariants.discrimination_survives_sum
#print axioms JurisLean.Mandate.StructureInvariants.relabel_cannot_bridge
#print axioms JurisLean.Mandate.StructureInvariants.same_labels
#print axioms JurisLean.Mandate.StructureInvariants.sig3_double
#print axioms JurisLean.Mandate.StructureInvariants.sig3_le_sum_any
#print axioms JurisLean.Mandate.StructureInvariants.signatures_differ
#print axioms JurisLean.Mandate.StructureInvariants.sum_signature_third
#print axioms JurisLean.Mandate.SubstrAdmission.isPrefix_false_of_longer
#print axioms JurisLean.Mandate.SubstrAdmission.isPrefix_refl
#print axioms JurisLean.Mandate.SubstrAdmission.isSubstr_nil_pat
#print axioms JurisLean.Mandate.SubstrAdmission.isSubstr_of_isPrefix
#print axioms JurisLean.Mandate.SubstrAdmission.isSubstr_self
#print axioms JurisLean.Mandate.SubstrAdmission.prefix_adequate_for_admission
#print axioms JurisLean.Mandate.SubstrAdmission.substr_strictly_weaker
#print axioms JurisLean.Mandate.TaxSlices.remainingOf_exhausted
#print axioms JurisLean.Mandate.TaxSlices.remainingOf_le_start
#print axioms JurisLean.Mandate.TaxSlices.taxOf_append
#print axioms JurisLean.Mandate.TaxSlices.taxOf_capped
#print axioms JurisLean.Mandate.TaxSlices.taxOf_empty_table
#print axioms JurisLean.Mandate.TaxSlices.taxOf_prefix_le
#print axioms JurisLean.Mandate.TaxSlices.taxOf_single
#print axioms JurisLean.Mandate.TaxSlices.taxOf_two_brackets
#print axioms JurisLean.Mandate.TaxSlices.taxOf_zero_base
#print axioms JurisLean.Mandate.Waterfall.allocate_concrete
#print axioms JurisLean.Mandate.Waterfall.allocate_concrete_overshoot
#print axioms JurisLean.Mandate.Waterfall.allocate_concrete_remainder
#print axioms JurisLean.Mandate.Waterfall.allocate_cons
#print axioms JurisLean.Mandate.Waterfall.allocate_no_debts
#print axioms JurisLean.Mandate.Waterfall.allocate_not_constant
#print axioms JurisLean.Mandate.Waterfall.conservation
#print axioms JurisLean.Mandate.Waterfall.paidOut_cons
#print axioms JurisLean.Mandate.Waterfall.paidOut_le_payment
#print axioms JurisLean.Mandate.Waterfall.paidOut_nil
