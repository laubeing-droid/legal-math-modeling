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
import JurisLean.Mandate.ReLUApprox
import JurisLean.Mandate.MixedPennies
import JurisLean.Mandate.ZeroSumSion
import JurisLean.Mandate.SequentialGames

import JurisLean.Mandate.OneShotDeviation
import JurisLean.Mandate.PureNash
import JurisLean.Mandate.ZeroSumValue

import JurisLean.External.FixedPointTheorems.apply_cubical_sperner
import JurisLean.External.FixedPointTheorems.brouwer
import JurisLean.External.FixedPointTheorems.convex_homeos
import JurisLean.External.FixedPointTheorems.cubical_sperner
import JurisLean.External.FixedPointTheorems.cubical_sperner_prep
import JurisLean.External.FixedPointTheorems.kakutani
import JurisLean.External.GameTheory.Concepts.ConstantSum
import JurisLean.External.GameTheory.Concepts.Deviation
import JurisLean.External.GameTheory.Concepts.Minimax
import JurisLean.External.GameTheory.Concepts.MixedExtension
import JurisLean.External.GameTheory.Concepts.ProductSimplexBrouwer
import JurisLean.External.GameTheory.Concepts.SecurityStrategy
import JurisLean.External.GameTheory.Concepts.SolutionConcepts
import JurisLean.External.GameTheory.Concepts.ZeroSum
import JurisLean.External.GameTheory.Concepts.ZeroSumNash
import JurisLean.External.GameTheory.Core.GameForm
import JurisLean.External.GameTheory.Core.GameProperties
import JurisLean.External.GameTheory.Core.KernelGame
import JurisLean.External.GameTheory.Languages.EFG.Refinements
import JurisLean.External.GameTheory.Languages.EFG.Syntax
import JurisLean.External.GameTheory.Math.Coupling
import JurisLean.External.GameTheory.Math.OptimizationLocalGlobal
import JurisLean.External.GameTheory.Math.PMFProduct
import JurisLean.External.GameTheory.Math.ParameterizedChain
import JurisLean.External.GameTheory.Math.Probability
import JurisLean.External.GameTheory.Math.ProbabilityMassFunction
import JurisLean.External.GameTheory.Math.TraceRun
import JurisLean.External.GameTheory.Semantics.DSMachine
import JurisLean.External.GameTheory.Semantics.TransitionTrace
import JurisLean.External.GameTheory.Theorems.Kuhn
import JurisLean.External.GameTheory.Theorems.Kuhn.BehavioralToMixed
import JurisLean.External.GameTheory.Theorems.Kuhn.BehavioralToMixedCore
import JurisLean.External.GameTheory.Theorems.Kuhn.CorrelatedRealization
import JurisLean.External.GameTheory.Theorems.Kuhn.KuhnModel
import JurisLean.External.GameTheory.Theorems.Kuhn.MixedToBehavioralCore
import JurisLean.External.GameTheory.Theorems.Kuhn.ObsModel
import JurisLean.External.GameTheory.Theorems.Minimax
import JurisLean.External.GameTheory.Theorems.NashExistenceMixed
import JurisLean.External.GameTheory.Theorems.OneShotDeviation

import JurisLean.External.NeuralNetworkProofs.ForMathlib.ConvolutionDegreeBound
import JurisLean.External.NeuralNetworkProofs.ForMathlib.ConvolutionIteratedDeriv
import JurisLean.External.NeuralNetworkProofs.ForMathlib.ConvolutionPolynomial
import JurisLean.External.NeuralNetworkProofs.ForMathlib.IteratedDerivPolynomial
import JurisLean.External.NeuralNetworkProofs.ForMathlib.PolynomialDistribution
import JurisLean.External.NeuralNetworkProofs.ForMathlib.RidgePowersSpan
import JurisLean.External.NeuralNetworkProofs.ForMathlib.SmoothCompactAntideriv
import JurisLean.External.NeuralNetworkProofs.ForMathlib.UniformRiemannConvolution
import JurisLean.External.NeuralNetworkProofs.UniversalApproximation.Leshno
import JurisLean.External.NeuralNetworkProofs.UniversalApproximation.Leshno.ClassM
import JurisLean.External.NeuralNetworkProofs.UniversalApproximation.Leshno.Converse
import JurisLean.External.NeuralNetworkProofs.UniversalApproximation.Leshno.Family
import JurisLean.External.NeuralNetworkProofs.UniversalApproximation.Leshno.Mollify
import JurisLean.External.NeuralNetworkProofs.UniversalApproximation.Leshno.MollifyDef
import JurisLean.External.NeuralNetworkProofs.UniversalApproximation.Leshno.Ridge
import JurisLean.External.NeuralNetworkProofs.UniversalApproximation.Leshno.SmoothEngine
import JurisLean.External.NeuralNetworkProofs.UniversalApproximation.Leshno.Theorem

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
#print axioms JurisLean.Mandate.CaseIsomorphism.bool_beq_true
#print axioms JurisLean.Mandate.CaseIsomorphism.exists_bijective_inverse
#print axioms JurisLean.Mandate.CaseIsomorphism.isoRel3_allLoops_noRelation
#print axioms JurisLean.Mandate.CaseIsomorphism.isoRel3_allLoops_self
#print axioms JurisLean.Mandate.CaseIsomorphism.isoRel3_iff
#print axioms JurisLean.Mandate.CaseIsomorphism.iso_refl
#print axioms JurisLean.Mandate.CaseIsomorphism.iso_symm
#print axioms JurisLean.Mandate.CaseIsomorphism.iso_trans
#print axioms JurisLean.Mandate.CaseIsomorphism.iso_twoEmpty_swap
#print axioms JurisLean.Mandate.CaseIsomorphism.noRelation_ne_allLoops
#print axioms JurisLean.Mandate.CaseIsomorphism.not_Rel3Iso_allLoops_noRelation
#print axioms JurisLean.Mandate.CaseIsomorphism.not_iso_looped_edgeless
#print axioms JurisLean.Mandate.CaseIsomorphism.pairs3_all_mem
#print axioms JurisLean.Mandate.CaseIsomorphism.preservesR_iff
#print axioms JurisLean.Mandate.CaseIsomorphism.rel3Iso_allLoops_symm_self
#print axioms JurisLean.Mandate.CaseIsomorphism.rel3Iso_iff_by_list
#print axioms JurisLean.Mandate.CaseIsomorphism.rel3Iso_of_preserves
#print axioms JurisLean.Mandate.CaseIsomorphism.swap2_bijective
#print axioms JurisLean.Mandate.CaseIsomorphism.swap2_moves_a_slot
#print axioms JurisLean.Mandate.CaseIsomorphism.triedRenames_complete
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
#print axioms JurisLean.Mandate.GameTree.value_le_value_ofList_cons
#print axioms JurisLean.Mandate.GameTree.value_le_value_right
#print axioms JurisLean.Mandate.GameTree.value_leaf
#print axioms JurisLean.Mandate.GameTree.value_node
#print axioms JurisLean.Mandate.GameTree.value_ofList_append_le
#print axioms JurisLean.Mandate.GameTree.value_ofList_concrete
#print axioms JurisLean.Mandate.GameTree.value_ofList_cons
#print axioms JurisLean.Mandate.GameTree.value_ofList_nil
#print axioms JurisLean.Mandate.GameTree.value_ofList_singleton
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
#print axioms JurisLean.Mandate.MixedPennies.agreed_second_moves
#print axioms JurisLean.Mandate.MixedPennies.col_guaranteed
#print axioms JurisLean.Mandate.MixedPennies.four_half
#print axioms JurisLean.Mandate.MixedPennies.mixedNash_uniform
#print axioms JurisLean.Mandate.MixedPennies.no_pure_pair_is_equilibrium
#print axioms JurisLean.Mandate.MixedPennies.payoff_symm
#print axioms JurisLean.Mandate.MixedPennies.row_held
#print axioms JurisLean.Mandate.MixedPennies.two_half
#print axioms JurisLean.Mandate.MixedPennies.u_eq
#print axioms JurisLean.Mandate.MixedPennies.uniform_is_a_mixture
#print axioms JurisLean.Mandate.MixedPennies.value_at_uniform
#print axioms JurisLean.Mandate.OneShotDeviation.atPath_cons_left
#print axioms JurisLean.Mandate.OneShotDeviation.atPath_cons_right
#print axioms JurisLean.Mandate.OneShotDeviation.atPath_cons_terminal
#print axioms JurisLean.Mandate.OneShotDeviation.atPath_nil
#print axioms JurisLean.Mandate.OneShotDeviation.brute_at_root
#print axioms JurisLean.Mandate.OneShotDeviation.brute_cons_left
#print axioms JurisLean.Mandate.OneShotDeviation.brute_cons_right
#print axioms JurisLean.Mandate.OneShotDeviation.deviate_agree_off
#print axioms JurisLean.Mandate.OneShotDeviation.go_bound
#print axioms JurisLean.Mandate.OneShotDeviation.go_exact
#print axioms JurisLean.Mandate.OneShotDeviation.go_terminal
#print axioms JurisLean.Mandate.OneShotDeviation.go_turn_apply
#print axioms JurisLean.Mandate.OneShotDeviation.one_shot_deviation
#print axioms JurisLean.Mandate.OneShotDeviation.one_shot_deviation_le_brute
#print axioms JurisLean.Mandate.OneShotDeviation.outcome_eq_of_le
#print axioms JurisLean.Mandate.OneShotDeviation.outcome_eq_of_not_le
#print axioms JurisLean.Mandate.OneShotDeviation.play_brute
#print axioms JurisLean.Mandate.OneShotDeviation.play_terminal
#print axioms JurisLean.Mandate.OneShotDeviation.play_turn_follows
#print axioms JurisLean.Mandate.OneShotDeviation.tree_brute_root_is_left
#print axioms JurisLean.Mandate.OneShotDeviation.tree_deviation_strictly_worse
#print axioms JurisLean.Mandate.OneShotDeviation.tree_play_brute_actor
#print axioms JurisLean.Mandate.OneShotDeviation.tree_play_brute_second
#print axioms JurisLean.Mandate.OneShotDeviation.tree_play_brute_third
#print axioms JurisLean.Mandate.OneShotDeviation.tree_play_deviation_actor
#print axioms JurisLean.Mandate.PureNash.coordPay_table
#print axioms JurisLean.Mandate.PureNash.coordination_diagonal_is_nash
#print axioms JurisLean.Mandate.PureNash.coordination_label_true
#print axioms JurisLean.Mandate.PureNash.coordination_offdiag_not_nash
#print axioms JurisLean.Mandate.PureNash.isNashPure_fst
#print axioms JurisLean.Mandate.PureNash.isNashPure_of_bestResponses
#print axioms JurisLean.Mandate.PureNash.isNashPure_snd
#print axioms JurisLean.Mandate.PureNash.isNashPure_swap
#print axioms JurisLean.Mandate.PureNash.isNashPure_swap_swap
#print axioms JurisLean.Mandate.PureNash.matchingPennies_no_pure_equilibrium
#print axioms JurisLean.Mandate.PureNash.nashPureExists_false_iff
#print axioms JurisLean.Mandate.PureNash.nashPureExists_swap
#print axioms JurisLean.Mandate.PureNash.nashPureExists_true_iff
#print axioms JurisLean.Mandate.PureNash.nashPure_of_dominant
#print axioms JurisLean.Mandate.PureNash.not_isNashPure_of_col_deviation
#print axioms JurisLean.Mandate.PureNash.not_isNashPure_of_row_deviation
#print axioms JurisLean.Mandate.PureNash.penniesRow_table
#print axioms JurisLean.Mandate.PureNash.pennies_col_dev_00
#print axioms JurisLean.Mandate.PureNash.pennies_col_dev_11
#print axioms JurisLean.Mandate.PureNash.pennies_label_false
#print axioms JurisLean.Mandate.PureNash.pennies_not_nash_00
#print axioms JurisLean.Mandate.PureNash.pennies_not_nash_01
#print axioms JurisLean.Mandate.PureNash.pennies_not_nash_10
#print axioms JurisLean.Mandate.PureNash.pennies_not_nash_11
#print axioms JurisLean.Mandate.PureNash.pennies_row_dev_01
#print axioms JurisLean.Mandate.PureNash.pennies_row_dev_10
#print axioms JurisLean.Mandate.PureNash.pure_labels_discriminate
#print axioms JurisLean.Mandate.ReLUApprox.h1_between
#print axioms JurisLean.Mandate.ReLUApprox.h2_between
#print axioms JurisLean.Mandate.ReLUApprox.lip_eq
#print axioms JurisLean.Mandate.ReLUApprox.lip_pos
#print axioms JurisLean.Mandate.ReLUApprox.out_at_one
#print axioms JurisLean.Mandate.ReLUApprox.out_not_constant
#print axioms JurisLean.Mandate.ReLUApprox.out_origin
#print axioms JurisLean.Mandate.ReLUApprox.out_stable
#print axioms JurisLean.Mandate.ReLUApprox.relu_between
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
#print axioms JurisLean.Mandate.SequentialGames.actor_gets_her_best
#print axioms JurisLean.Mandate.SequentialGames.choose_apply
#print axioms JurisLean.Mandate.SequentialGames.non_actor_may_be_sacrificed
#print axioms JurisLean.Mandate.SequentialGames.outcome_terminal
#print axioms JurisLean.Mandate.SequentialGames.outcome_turn_apply
#print axioms JurisLean.Mandate.SequentialGames.turn_ge_left
#print axioms JurisLean.Mandate.SequentialGames.turn_ge_right
#print axioms JurisLean.Mandate.SequentialGames.turn_monotone
#print axioms JurisLean.Mandate.SequentialGames.two_player_take_better
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
#print axioms JurisLean.Mandate.ZeroSumSion.bestResponse_left_forall
#print axioms JurisLean.Mandate.ZeroSumSion.bestResponse_right_forall
#print axioms JurisLean.Mandate.ZeroSumSion.combo_nonneg
#print axioms JurisLean.Mandate.ZeroSumSion.exists_bestResponse_left
#print axioms JurisLean.Mandate.ZeroSumSion.exists_bestResponse_right
#print axioms JurisLean.Mandate.ZeroSumSion.exists_saddlePoint
#print axioms JurisLean.Mandate.ZeroSumSion.lsc_payoff_left
#print axioms JurisLean.Mandate.ZeroSumSion.mixLeft_convex
#print axioms JurisLean.Mandate.ZeroSumSion.mixLeft_isCompact
#print axioms JurisLean.Mandate.ZeroSumSion.mixLeft_nonempty
#print axioms JurisLean.Mandate.ZeroSumSion.mixRight_convex
#print axioms JurisLean.Mandate.ZeroSumSion.mixRight_isCompact
#print axioms JurisLean.Mandate.ZeroSumSion.mixRight_nonempty
#print axioms JurisLean.Mandate.ZeroSumSion.payoff_comb_left
#print axioms JurisLean.Mandate.ZeroSumSion.payoff_comb_right
#print axioms JurisLean.Mandate.ZeroSumSion.quasiconcaveOn_payoff_right
#print axioms JurisLean.Mandate.ZeroSumSion.quasiconvexOn_payoff_left
#print axioms JurisLean.Mandate.ZeroSumSion.usc_payoff_right
#print axioms JurisLean.Mandate.ZeroSumValue.bddAbove_payoff_left
#print axioms JurisLean.Mandate.ZeroSumValue.bddAbove_payoff_right
#print axioms JurisLean.Mandate.ZeroSumValue.bddBelow_payoff_left
#print axioms JurisLean.Mandate.ZeroSumValue.bddBelow_payoff_right
#print axioms JurisLean.Mandate.ZeroSumValue.ciInf_payoff_col_eq
#print axioms JurisLean.Mandate.ZeroSumValue.ciSup_payoff_row_eq
#print axioms JurisLean.Mandate.ZeroSumValue.continuous_payoff_left
#print axioms JurisLean.Mandate.ZeroSumValue.continuous_payoff_right
#print axioms JurisLean.Mandate.ZeroSumValue.exists_value
#print axioms JurisLean.Mandate.ZeroSumValue.lowerValue_eq_payoff
#print axioms JurisLean.Mandate.ZeroSumValue.lowerValue_le_upperValue
#print axioms JurisLean.Mandate.ZeroSumValue.upperValue_eq_payoff
#print axioms JurisLean.Mandate.ZeroSumValue.upperValue_le_lowerValue
#print axioms JurisLean.Mandate.ZeroSumValue.value_eq
#print axioms JurisLean.Mandate.ZeroSumValue.weakDuality

/-! Generated external-port audit surface. Regenerate with
      scripts/ci/generate_probability_audit_surface.py --write
    These declarations are elaborated by the all-module CI plan but were
    absent from the release audit surface; the block is generated from the
    declaration sites, so it cannot name a theorem that does not exist. -/
#print axioms ConvolutionDegreeBound.conv_left_comm_mul
#print axioms ConvolutionDegreeBound.exists_uniform_degree_bound
#print axioms ConvolutionIteratedDeriv.iteratedDeriv_convolution_left
#print axioms ConvolutionPolynomial.convolutionExists_left_mul
#print axioms ConvolutionPolynomial.convolutionExists_right_mul
#print axioms ConvolutionPolynomial.convolution_comm_mul
#print axioms ConvolutionPolynomial.monomial_conv_isPoly
#print axioms ConvolutionPolynomial.natDegree_poly_conv_eq
#print axioms ConvolutionPolynomial.poly_conv_isPoly
#print axioms EFG.DecisionNodeIn_chance_inv
#print axioms EFG.DecisionNodeIn_decision_inv
#print axioms EFG.DecisionNodeIn_terminal_false
#print axioms EFG.IsPerfectInfo_subtree
#print axioms EFG.PerfectRecall_single_infoSet
#print axioms EFG.PerfectRecall_terminal
#print axioms EFG.ReachBy.action
#print axioms EFG.ReachBy.chance
#print axioms EFG.ReachBy.here
#print axioms EFG.ReachBy_append
#print axioms EFG.ReachBy_chance_inv'
#print axioms EFG.ReachBy_decision_inv
#print axioms EFG.ReachBy_split
#print axioms EFG.ReachBy_terminal_absurd
#print axioms EFG.decisionNodeIn_of_reachBy
#print axioms EFG.decisionNodeIn_reachBy
#print axioms EFG.entryNash_isNash
#print axioms EFG.entryNash_not_spe
#print axioms EFG.entrySPE_isNash
#print axioms EFG.entrySPE_isSPE
#print axioms EFG.entry_nash_eu_p0
#print axioms EFG.entry_perfectRecall
#print axioms EFG.entry_spe_eu_p0
#print axioms EFG.evalDist_chance
#print axioms EFG.evalDist_decision
#print axioms EFG.evalDist_eq_of_agree
#print axioms EFG.evalDist_pureToBehavioral_eq_pure
#print axioms EFG.evalDist_terminal
#print axioms EFG.evalPure_decision
#print axioms EFG.evalPure_terminal
#print axioms EFG.hasNoOneShotDeviation_spe
#print axioms EFG.hasNoOneShotDeviation_spe_of_bounded
#print axioms EFG.isSubgame_root
#print axioms EFG.isSubgame_terminal
#print axioms EFG.nash_of_noOSD
#print axioms EFG.nash_of_noOSD_of_bounded
#print axioms EFG.oneShotDeviation_iff_spe
#print axioms EFG.oneShotDeviation_iff_spe_of_bounded
#print axioms EFG.perfectInfo_implies_perfectRecall
#print axioms EFG.perfectInfo_isSubgame_decision
#print axioms EFG.perfectInfo_root_not_in_subtree
#print axioms EFG.playerHistory_append
#print axioms EFG.pureToBehavioral_update
#print axioms EFG.reachBy_deterministic
#print axioms EFG.spe_hasNoOneShotDeviation
#print axioms EFG.spe_implies_isNash
#print axioms EFG.spe_implies_nash
#print axioms EFG.swap_chance_decision
#print axioms EFG.swap_chances
#print axioms EFG.swap_decisions
#print axioms EFG.terminal_isNashFor_euPref
#print axioms EFG.toStrategicKernelGame_outcomeKernel
#print axioms EFG.toStrategicKernelGame_udist
#print axioms GameTheory.GameForm.IsCorrelatedEqFor.toCoarseCorrelatedEqFor
#print axioms GameTheory.GameForm.IsDominantFor.isBestResponseFor
#print axioms GameTheory.GameForm.IsDominantFor.mono
#print axioms GameTheory.GameForm.IsDominantFor.weaklyDominatesFor
#print axioms GameTheory.GameForm.IsNashFor.mono
#print axioms GameTheory.GameForm.IsStrictNashFor.isNashFor
#print axioms GameTheory.GameForm.ParetoDominatesFor.asymm
#print axioms GameTheory.GameForm.ParetoDominatesFor.irrefl
#print axioms GameTheory.GameForm.ProtocolMap.comp_assoc
#print axioms GameTheory.GameForm.ProtocolMap.comp_id
#print axioms GameTheory.GameForm.ProtocolMap.comp_outcomeMap
#print axioms GameTheory.GameForm.ProtocolMap.comp_stratMap
#print axioms GameTheory.GameForm.ProtocolMap.id_comp
#print axioms GameTheory.GameForm.ProtocolMap.id_outcomeMap
#print axioms GameTheory.GameForm.ProtocolMap.id_stratMap
#print axioms GameTheory.GameForm.StrictlyDominatesFor.toWeaklyDominatesFor
#print axioms GameTheory.GameForm.WeaklyDominatesFor.refl
#print axioms GameTheory.GameForm.WeaklyDominatesFor.trans
#print axioms GameTheory.GameForm.constDeviateDistributionFn_pure
#print axioms GameTheory.GameForm.constantDeviationProfileFamily_deviate
#print axioms GameTheory.GameForm.correlatedOutcome_constDeviateDistributionFn_pure
#print axioms GameTheory.GameForm.correlatedOutcome_pure
#print axioms GameTheory.GameForm.deviateDistributionFn_id
#print axioms GameTheory.GameForm.deviateOutcome_same
#print axioms GameTheory.GameForm.deviateProfile_same
#print axioms GameTheory.GameForm.dominant_is_nash_for
#print axioms GameTheory.GameForm.isCoarseCorrelatedEqFor_iff
#print axioms GameTheory.GameForm.isCorrelatedEqFor_iff
#print axioms GameTheory.GameForm.isNashFor_iff
#print axioms GameTheory.GameForm.isNashFor_iff_bestResponseFor
#print axioms GameTheory.GameForm.map_Outcome
#print axioms GameTheory.GameForm.map_Strategy
#print axioms GameTheory.GameForm.map_comp
#print axioms GameTheory.GameForm.map_id
#print axioms GameTheory.GameForm.map_outcomeKernel
#print axioms GameTheory.GameForm.noProfitableDeviationFor_iff
#print axioms GameTheory.GameForm.noProfitableProfileDeviationFor_iff
#print axioms GameTheory.GameForm.product_Outcome
#print axioms GameTheory.GameForm.product_map_fst
#print axioms GameTheory.GameForm.product_map_snd
#print axioms GameTheory.GameForm.recommendationDeviationFamily_deviate
#print axioms GameTheory.GameForm.withUtility_Outcome
#print axioms GameTheory.GameForm.withUtility_Strategy
#print axioms GameTheory.GameForm.withUtility_outcomeKernel
#print axioms GameTheory.GameForm.withUtility_toGameForm
#print axioms GameTheory.GameForm.withUtility_utility
#print axioms GameTheory.KernelGame.Guarantees.mono
#print axioms GameTheory.KernelGame.IsBestResponse_iff_IsBestResponseFor_eu
#print axioms GameTheory.KernelGame.IsCoarseCorrelatedEq_iff_IsCoarseCorrelatedEqFor_eu
#print axioms GameTheory.KernelGame.IsConstantSum.eu_determined
#print axioms GameTheory.KernelGame.IsConstantSum.eu_determined_of_bounded
#print axioms GameTheory.KernelGame.IsConstantSum.nash_eu_eq
#print axioms GameTheory.KernelGame.IsConstantSum.nash_eu_eq_of_bounded
#print axioms GameTheory.KernelGame.IsConstantSum.nash_eu_sum
#print axioms GameTheory.KernelGame.IsConstantSum.nash_eu_sum_of_bounded
#print axioms GameTheory.KernelGame.IsConstantSum.socialWelfare_eq
#print axioms GameTheory.KernelGame.IsConstantSum.socialWelfare_eq_of_bounded
#print axioms GameTheory.KernelGame.IsCorrelatedEq_iff_IsCorrelatedEqFor_eu
#print axioms GameTheory.KernelGame.IsDominant.eu_ge_securityLevel
#print axioms GameTheory.KernelGame.IsDominant.eu_ge_securityLevelSup
#print axioms GameTheory.KernelGame.IsDominant_iff_IsDominantFor_eu
#print axioms GameTheory.KernelGame.IsNash_iff_IsNashFor_eu
#print axioms GameTheory.KernelGame.IsStrictDominant_iff_IsStrictDominantFor_eu
#print axioms GameTheory.KernelGame.IsStrictNash_iff_IsStrictNashFor_eu
#print axioms GameTheory.KernelGame.IsZeroSum.deviation_eu_neg
#print axioms GameTheory.KernelGame.IsZeroSum.deviation_eu_neg_of_bounded
#print axioms GameTheory.KernelGame.IsZeroSum.eu_neg
#print axioms GameTheory.KernelGame.IsZeroSum.eu_neg_of_bounded
#print axioms GameTheory.KernelGame.IsZeroSum.eu_nonneg_iff_nonpos
#print axioms GameTheory.KernelGame.IsZeroSum.eu_nonneg_iff_nonpos_of_bounded
#print axioms GameTheory.KernelGame.IsZeroSum.isConstantSum_zero
#print axioms GameTheory.KernelGame.IsZeroSum.nash_eu_eq
#print axioms GameTheory.KernelGame.IsZeroSum.nash_eu_eq_of_bounded
#print axioms GameTheory.KernelGame.IsZeroSum.nash_eu_sum_zero
#print axioms GameTheory.KernelGame.IsZeroSum.nash_eu_sum_zero_of_bounded
#print axioms GameTheory.KernelGame.IsZeroSum.nash_interchangeable
#print axioms GameTheory.KernelGame.IsZeroSum.nash_interchangeable_of_bounded
#print axioms GameTheory.KernelGame.IsZeroSum.nash_p0_optimal
#print axioms GameTheory.KernelGame.IsZeroSum.nash_p0_optimal_of_bounded
#print axioms GameTheory.KernelGame.IsZeroSum.socialWelfare_eq_zero
#print axioms GameTheory.KernelGame.IsZeroSum.socialWelfare_eq_zero_of_bounded
#print axioms GameTheory.KernelGame.ParetoDominates_iff_ParetoDominatesFor_eu
#print axioms GameTheory.KernelGame.StrictlyDominates_iff_StrictlyDominatesFor_eu
#print axioms GameTheory.KernelGame.WeaklyDominates_iff_WeaklyDominatesFor_eu
#print axioms GameTheory.KernelGame.continuous_mixedExtension_eu_profileFromMixedSimplex
#print axioms GameTheory.KernelGame.continuous_mixedExtension_eu_profileFromMixedSimplex_of_bounded
#print axioms GameTheory.KernelGame.continuous_mixedExtension_eu_update_profileFromMixedSimplex
#print axioms GameTheory.KernelGame.continuous_mixedExtension_eu_update_profileFromMixedSimplex_of_bounded
#print axioms GameTheory.KernelGame.continuous_mixedGainOnMixedSimplex_of_continuous_mixedEu
#print axioms GameTheory.KernelGame.continuous_nashMapOnMixedSimplex
#print axioms GameTheory.KernelGame.continuous_nashMapOnMixedSimplex_of_bounded
#print axioms GameTheory.KernelGame.continuous_nashMapOnMixedSimplex_of_continuous_mixedEu
#print axioms GameTheory.KernelGame.continuous_nashMapOnMixedSimplex_of_continuous_mixedEu_deviation
#print axioms GameTheory.KernelGame.continuous_nashMapOnMixedSimplex_of_continuous_mixedGainOnMixedSimplex
#print axioms GameTheory.KernelGame.continuous_pospart
#print axioms GameTheory.KernelGame.correlatedOutcome_pure
#print axioms GameTheory.KernelGame.deviationDistribution_apply
#print axioms GameTheory.KernelGame.deviationDistribution_id
#print axioms GameTheory.KernelGame.dominant_is_nash
#print axioms GameTheory.KernelGame.dominant_is_nash_for
#print axioms GameTheory.KernelGame.eu_abs_le_of_bounded
#print axioms GameTheory.KernelGame.eu_ofEU
#print axioms GameTheory.KernelGame.exists_securityStrategy
#print axioms GameTheory.KernelGame.gainSumOnMixedSimplex_nonneg
#print axioms GameTheory.KernelGame.gainSum_nonneg
#print axioms GameTheory.KernelGame.guarantees_iff_worstCaseEUInf_ge
#print axioms GameTheory.KernelGame.guarantees_iff_worstCaseEU_ge
#print axioms GameTheory.KernelGame.isNash_iff_gains_nonpos
#print axioms GameTheory.KernelGame.isNash_iff_gains_nonpos_of_bounded
#print axioms GameTheory.KernelGame.isSaddlePoint_iff_isNash
#print axioms GameTheory.KernelGame.le_securityLevelSup_of_forall_eu_ge
#print axioms GameTheory.KernelGame.le_securityLevel_of_forall_eu_ge
#print axioms GameTheory.KernelGame.mixedExtension_Strategy
#print axioms GameTheory.KernelGame.mixedExtension_eu
#print axioms GameTheory.KernelGame.mixedExtension_eu_of_bounded
#print axioms GameTheory.KernelGame.mixedExtension_eu_update
#print axioms GameTheory.KernelGame.mixedExtension_eu_update_of_bounded
#print axioms GameTheory.KernelGame.mixedExtension_isZeroSum
#print axioms GameTheory.KernelGame.mixed_nash_exists
#print axioms GameTheory.KernelGame.mixed_nash_exists_of_bounded
#print axioms GameTheory.KernelGame.mixed_nash_exists_of_nashMapOnMixedSimplex_approx
#print axioms GameTheory.KernelGame.mixed_nash_exists_of_nashMapOnMixedSimplex_approxOnly
#print axioms GameTheory.KernelGame.mixed_nash_exists_of_nashMapOnMixedSimplex_approxOnly_of_bounded
#print axioms GameTheory.KernelGame.mixed_nash_exists_of_nashMapOnMixedSimplex_approx_of_bounded
#print axioms GameTheory.KernelGame.mixed_nash_exists_of_nashMapOnMixedSimplex_fixed_point
#print axioms GameTheory.KernelGame.mixed_nash_exists_of_nashMapOnMixedSimplex_fixed_point_of_bounded
#print axioms GameTheory.KernelGame.nashMapOnMixedSimplex_apply
#print axioms GameTheory.KernelGame.nashMap_fp_identity
#print axioms GameTheory.KernelGame.nashMap_nonneg
#print axioms GameTheory.KernelGame.nashMap_sum_one
#print axioms GameTheory.KernelGame.nashMap_weightFixedPoint_of_mixedSimplexFixedPoint
#print axioms GameTheory.KernelGame.nashMap_weightFixedPoint_of_nashMapOnMixedSimplex_approx
#print axioms GameTheory.KernelGame.nashMap_weightFixedPoint_of_nashMapOnMixedSimplex_approxOnly
#print axioms GameTheory.KernelGame.nash_eu_ge_securityLevel
#print axioms GameTheory.KernelGame.nash_eu_ge_securityLevelSup
#print axioms GameTheory.KernelGame.nash_fp_is_nash
#print axioms GameTheory.KernelGame.nash_fp_is_nash_of_bounded
#print axioms GameTheory.KernelGame.nash_p0_cap
#print axioms GameTheory.KernelGame.ofEU_Strategy
#print axioms GameTheory.KernelGame.pospart_eq_zero_iff
#print axioms GameTheory.KernelGame.pospart_mul_self
#print axioms GameTheory.KernelGame.pospart_nonneg
#print axioms GameTheory.KernelGame.realToPmf_apply
#print axioms GameTheory.KernelGame.realToPmf_toReal
#print axioms GameTheory.KernelGame.toGameForm_Outcome
#print axioms GameTheory.KernelGame.toGameForm_Strategy
#print axioms GameTheory.KernelGame.toGameForm_outcomeKernel
#print axioms GameTheory.KernelGame.toGameForm_withUtility
#print axioms GameTheory.KernelGame.udistPlayer_eq_udist_bind
#print axioms GameTheory.KernelGame.udistPlayer_pure
#print axioms GameTheory.KernelGame.udist_pure
#print axioms GameTheory.KernelGame.von_neumann_minimax
#print axioms GameTheory.KernelGame.von_neumann_minimax_of_bounded
#print axioms GameTheory.KernelGame.weighted_gain_sum_zero
#print axioms GameTheory.KernelGame.weighted_gain_sum_zero_of_bounded
#print axioms GameTheory.KernelGame.worstCaseEUInf_guarantees
#print axioms GameTheory.KernelGame.worstCaseEUInf_le
#print axioms GameTheory.KernelGame.worstCaseEU_guarantees
#print axioms GameTheory.KernelGame.worstCaseEU_le
#print axioms GameTheory.brouwer_mixedSimplex
#print axioms GameTheory.continuous_fromMixedSet
#print axioms GameTheory.continuous_toMixedSet
#print axioms GameTheory.convex_mixedSimplexAsSet
#print axioms GameTheory.exists_fixedPoint_of_approx_on_compact
#print axioms GameTheory.exists_fixedPoint_of_approx_on_mixedSimplex
#print axioms GameTheory.fromMixedSet_toMixedSet
#print axioms GameTheory.isCompact_mixedSimplexAsSet
#print axioms GameTheory.nonempty_mixedSimplexAsSet
#print axioms GameTheory.toMixedSet_fromMixedSet
#print axioms InfoStateCore.identity_Carrier
#print axioms InfoStateCore.identity_current
#print axioms InfoStateCore.identity_push
#print axioms InfoStateCore.identity_start
#print axioms IteratedDerivPolynomial.exists_antideriv
#print axioms IteratedDerivPolynomial.iteratedDeriv_eq_zero_imp_poly
#print axioms IteratedDerivPolynomial.iteratedDeriv_eval
#print axioms IteratedDerivPolynomial.iteratedDeriv_succ_eq_zero_of_natDegree_le
#print axioms Math.Coupling.hasCoupling_proj_iff_map_eq
#print axioms Math.Optimization.LocalGlobal.all_nonpos_of_weighted_pospart_fixedPoint
#print axioms Math.Optimization.LocalGlobal.isFixedPoint_of_eq
#print axioms Math.Optimization.LocalGlobal.locallyOptimal_add
#print axioms Math.Optimization.LocalGlobal.locallyOptimal_of_global_on_set
#print axioms Math.Optimization.LocalGlobal.locallyOptimal_of_move_family
#print axioms Math.Optimization.LocalGlobal.locallyOptimal_smul_nonneg
#print axioms Math.Optimization.LocalGlobal.max_mul_self_eq_sq
#print axioms Math.Optimization.LocalGlobal.noImprovement_add
#print axioms Math.Optimization.LocalGlobal.noImprovement_at_of_fixed
#print axioms Math.Optimization.LocalGlobal.noImprovement_of_move_family
#print axioms Math.Optimization.LocalGlobal.noImprovement_smul_nonneg
#print axioms Math.PMFProduct.ENNReal_tsum_pi
#print axioms Math.PMFProduct.ENNReal_tsum_pi_fin
#print axioms Math.PMFProduct.IgnoresP_and
#print axioms Math.PMFProduct.IgnoresP_iff
#print axioms Math.PMFProduct.IgnoresP_imp
#print axioms Math.PMFProduct.IgnoresP_not
#print axioms Math.PMFProduct.IgnoresP_of_Ignores
#print axioms Math.PMFProduct.IgnoresP_or
#print axioms Math.PMFProduct.Ignores_app2
#print axioms Math.PMFProduct.Ignores_comp
#print axioms Math.PMFProduct.Ignores_const
#print axioms Math.PMFProduct.Ignores_coord_eq
#print axioms Math.PMFProduct.Ignores_coord_pred
#print axioms Math.PMFProduct.Ignores_finset_prod
#print axioms Math.PMFProduct.Ignores_fst
#print axioms Math.PMFProduct.Ignores_ite
#print axioms Math.PMFProduct.Ignores_of_IgnoresP
#print axioms Math.PMFProduct.Ignores_of_pointwise
#print axioms Math.PMFProduct.Ignores_prod_mk
#print axioms Math.PMFProduct.Ignores_snd
#print axioms Math.PMFProduct.Ignores₂_of_pointwise
#print axioms Math.PMFProduct.foldl_update_family_eq_of_nodup
#print axioms Math.PMFProduct.ignores_replaceOn_eq
#print axioms Math.PMFProduct.pmfMass_pmfPi_coord
#print axioms Math.PMFProduct.pmfMass_pmfPi_forall
#print axioms Math.PMFProduct.pmfPiMass_le_one
#print axioms Math.PMFProduct.pmfPiMass_ne_top
#print axioms Math.PMFProduct.pmfPiMass_true
#print axioms Math.PMFProduct.pmfPi_apply
#print axioms Math.PMFProduct.pmfPi_apply_update_family
#print axioms Math.PMFProduct.pmfPi_bind_comm_fresh
#print axioms Math.PMFProduct.pmfPi_bind_comm_fresh_support
#print axioms Math.PMFProduct.pmfPi_bind_eq_of_forall_ignores
#print axioms Math.PMFProduct.pmfPi_bind_eval
#print axioms Math.PMFProduct.pmfPi_bind_factor
#print axioms Math.PMFProduct.pmfPi_bind_ignores_coord
#print axioms Math.PMFProduct.pmfPi_bind_ignores_coord_finset
#print axioms Math.PMFProduct.pmfPi_bind_ignores_coord_list
#print axioms Math.PMFProduct.pmfPi_bind_indep
#print axioms Math.PMFProduct.pmfPi_bind_pmfPi_of_disjoint_coords
#print axioms Math.PMFProduct.pmfPi_bind_update_map
#print axioms Math.PMFProduct.pmfPi_bind_update_pure
#print axioms Math.PMFProduct.pmfPi_cond_coord
#print axioms Math.PMFProduct.pmfPi_cond_coord_other_marginal
#print axioms Math.PMFProduct.pmfPi_cond_coord_push_other
#print axioms Math.PMFProduct.pmfPi_cond_prob_invariant_of_ignores
#print axioms Math.PMFProduct.pmfPi_coord_mass
#print axioms Math.PMFProduct.pmfPi_coord_mass_tsum
#print axioms Math.PMFProduct.pmfPi_event_ratio_invariant_of_ignores
#print axioms Math.PMFProduct.pmfPi_expect_indep
#print axioms Math.PMFProduct.pmfPi_map_bind
#print axioms Math.PMFProduct.pmfPi_mass_invariant_of_ignores
#print axioms Math.PMFProduct.pmfPi_pure
#print axioms Math.PMFProduct.pmfPi_push_coord
#print axioms Math.PMFProduct.pmfPi_push_coordwise
#print axioms Math.PMFProduct.pmfPi_update_bind
#print axioms Math.PMFProduct.pmfPi_update_family_mul
#print axioms Math.PMFProduct.pmf_bind_disintegrate
#print axioms Math.PMFProduct.prod_erase_update_eq
#print axioms Math.PMFProduct.prod_factor_erase
#print axioms Math.PMFProduct.pushforward_support_fibre
#print axioms Math.PMFProduct.replaceOn_apply
#print axioms Math.PMFProduct.replaceOn_empty
#print axioms Math.PMFProduct.replaceOn_insert
#print axioms Math.PMFProduct.replaceOn_univ_diff
#print axioms Math.PMFProduct.replaceOn_univ_snd
#print axioms Math.PMFProduct.sum_pmfPi_factor
#print axioms Math.PMFProduct.sum_univ_eq_sum_univ_of_involutive
#print axioms Math.PMFProduct.swapJA_involutive
#print axioms Math.PMFProduct.tsum_eq_tsum_of_involutive
#print axioms Math.PMFProduct.tsum_pmfPi_factor
#print axioms Math.PMFProduct.update_family_other
#print axioms Math.PMFProduct.update_family_same
#print axioms Math.PMFProduct.update_ne
#print axioms Math.PMFProduct.update_self
#print axioms Math.PMFProduct.update_update_comm
#print axioms Math.PMFProduct.update_update_same
#print axioms Math.ParameterizedChain.append_singleton_inj
#print axioms Math.ParameterizedChain.condRun_eq_mixedRun
#print axioms Math.ParameterizedChain.condStep_step_eq
#print axioms Math.ParameterizedChain.condStep_weighted_eq
#print axioms Math.ParameterizedChain.exists_realizing_steps
#print axioms Math.ParameterizedChain.exists_realizing_steps_outcome
#print axioms Math.ParameterizedChain.pureRun_length
#print axioms Math.ParameterizedChain.pureRun_step_nonzero
#print axioms Math.ParameterizedChain.pureRun_succ_append
#print axioms Math.ParameterizedChain.pureRun_succ_nil
#print axioms Math.ParameterizedChain.pureRun_take_nonzero
#print axioms Math.ParameterizedChain.reweightPMF_apply
#print axioms Math.ParameterizedChain.reweightPMF_degenerate
#print axioms Math.ParameterizedChain.reweightPMF_eq_of_cross_mul
#print axioms Math.ParameterizedChain.reweightPMF_fallback
#print axioms Math.ParameterizedChain.reweightPMF_pmfPi
#print axioms Math.ParameterizedChain.reweightPMF_pmfPi_push_coord_of_ignores
#print axioms Math.ParameterizedChain.reweightPMF_pmfPi_push_coord_of_ignores'
#print axioms Math.ParameterizedChain.reweightPMF_scale
#print axioms Math.ParameterizedChain.reweightPMF_support_subset
#print axioms Math.Probability.Kernel.comp_apply
#print axioms Math.Probability.Kernel.comp_assoc
#print axioms Math.Probability.Kernel.comp_id_left
#print axioms Math.Probability.Kernel.comp_id_right
#print axioms Math.Probability.Kernel.pushforward_apply
#print axioms Math.Probability.Kernel.pushforward_comp
#print axioms Math.Probability.Kernel.pushforward_ofFun
#print axioms Math.Probability.exists_abs_bound_of_finite
#print axioms Math.Probability.expect_bind
#print axioms Math.Probability.expect_bind_of_bounded
#print axioms Math.Probability.expect_bind_summable_of_bounded
#print axioms Math.Probability.expect_const
#print axioms Math.Probability.expect_eq_sum
#print axioms Math.Probability.expect_map_fintype_source
#print axioms Math.Probability.expect_map_fintype_target
#print axioms Math.Probability.expect_pure
#print axioms Math.Probability.expect_summable_of_bounded
#print axioms Math.Probability.pmf_toReal_sum_one
#print axioms Math.Probability.pmf_toReal_summable
#print axioms Math.Probability.pmf_toReal_tsum_one
#print axioms Math.ProbabilityMassFunction.allEvents_append_singleton
#print axioms Math.ProbabilityMassFunction.allEvents_cons
#print axioms Math.ProbabilityMassFunction.allEvents_nil
#print axioms Math.ProbabilityMassFunction.bind_apply_eq_sum_sum_fiber
#print axioms Math.ProbabilityMassFunction.bind_assoc
#print axioms Math.ProbabilityMassFunction.bind_congr_of_ne_zero
#print axioms Math.ProbabilityMassFunction.bind_congr_on_support
#print axioms Math.ProbabilityMassFunction.bind_heq
#print axioms Math.ProbabilityMassFunction.bind_pure_eq_pushforward
#print axioms Math.ProbabilityMassFunction.bind_pushforward_condOn
#print axioms Math.ProbabilityMassFunction.condOn_apply
#print axioms Math.ProbabilityMassFunction.eq_zero_of_expect_eq_zero_of_nonpos_of_pos
#print axioms Math.ProbabilityMassFunction.eq_zero_of_pushforward_eq_zero
#print axioms Math.ProbabilityMassFunction.expect_bind_congr_on_support
#print axioms Math.ProbabilityMassFunction.expect_congr_of_ne_zero
#print axioms Math.ProbabilityMassFunction.expect_congr_on_support
#print axioms Math.ProbabilityMassFunction.expect_mono_of_pointwise
#print axioms Math.ProbabilityMassFunction.expect_mono_of_pointwise_bounded
#print axioms Math.ProbabilityMassFunction.expect_mono_of_pointwise_summable
#print axioms Math.ProbabilityMassFunction.expect_pushforward
#print axioms Math.ProbabilityMassFunction.expect_pushforward_of_bounded
#print axioms Math.ProbabilityMassFunction.expect_pushforward_of_bounded_on_source
#print axioms Math.ProbabilityMassFunction.foldl_bind_append
#print axioms Math.ProbabilityMassFunction.foldl_bind_congr
#print axioms Math.ProbabilityMassFunction.foldl_bind_eq_bind_foldl_pure
#print axioms Math.ProbabilityMassFunction.le_pushforward_apply
#print axioms Math.ProbabilityMassFunction.pmfCond_apply
#print axioms Math.ProbabilityMassFunction.pmfCond_ne_zero_implies
#print axioms Math.ProbabilityMassFunction.pmfMass_and_eq_mul_cond
#print axioms Math.ProbabilityMassFunction.pmfMass_and_eq_zero_of_left_zero
#print axioms Math.ProbabilityMassFunction.pmfMass_eq_toOuterMeasure
#print axioms Math.ProbabilityMassFunction.pmfMass_event_chain
#print axioms Math.ProbabilityMassFunction.pmfMass_event_chain_aux
#print axioms Math.ProbabilityMassFunction.pmfMass_mono
#print axioms Math.ProbabilityMassFunction.pmfMass_ne_top
#print axioms Math.ProbabilityMassFunction.pmfMass_pushforward
#print axioms Math.ProbabilityMassFunction.pmfMass_true
#print axioms Math.ProbabilityMassFunction.pure_heq
#print axioms Math.ProbabilityMassFunction.pushforward_apply_eq_pmfMass
#print axioms Math.ProbabilityMassFunction.pushforward_bind
#print axioms Math.ProbabilityMassFunction.pushforward_comp
#print axioms Math.ProbabilityMassFunction.pushforward_id
#print axioms Math.ProbabilityMassFunction.pushforward_pure
#print axioms Math.ProbabilityMassFunction.pushforward_pushforward
#print axioms Math.ProbabilityMassFunction.pushforward_support_fibre
#print axioms Math.TraceRun.append_singleton_inj
#print axioms Math.TraceRun.traceRun_length
#print axioms Math.TraceRun.traceRun_map_of_hom
#print axioms Math.TraceRun.traceRun_step_nonzero
#print axioms Math.TraceRun.traceRun_succ
#print axioms Math.TraceRun.traceRun_succ_append
#print axioms Math.TraceRun.traceRun_succ_nil
#print axioms Math.TraceRun.traceRun_zero
#print axioms ObsModel.PerStepActionRecall.toStepActionDeterminism
#print axioms ObsModel.PerStepPlayerRecall.action_eq
#print axioms ObsModel.PerStepPlayerRecall.toAction
#print axioms ObsModel.PlayerStepRecall.action_eq
#print axioms ObsModel.PlayerStepRecall.toReachable
#print axioms ObsModel.PlayerStepRecall.toTrace
#print axioms ObsModel.ReachablePlayerStepRecall.action_eq
#print axioms ObsModel.TracePlayerStepRecall.action_eq
#print axioms ObsModel.actionPosteriorLocal_toCore
#print axioms ObsModel.action_component_unique_of_pspr
#print axioms ObsModel.action_unique_of_psar
#print axioms ObsModel.cast_eq_of_subsingleton
#print axioms ObsModel.conditioning_preserves_product
#print axioms ObsModel.correlated_realization
#print axioms ObsModel.currentObs_projectStates
#print axioms ObsModel.currentObs_projectStatesFrom
#print axioms ObsModel.horizonSeparation_toCore
#print axioms ObsModel.jointActionDist_obs_heq
#print axioms ObsModel.kuhn_behavioral_to_mixed
#print axioms ObsModel.kuhn_mixed_to_behavioral_decomposed
#print axioms ObsModel.kuhn_mixed_to_behavioral_pspr
#print axioms ObsModel.kuhn_mixed_to_behavioral_semantic
#print axioms ObsModel.kuhn_mixed_to_behavioral_trace
#print axioms ObsModel.mediator_product_of_product
#print axioms ObsModel.mediator_step_eq_condStep
#print axioms ObsModel.mixedToMediator_obs_heq
#print axioms ObsModel.noNontrivialInfoStateRepeat_toCore
#print axioms ObsModel.obsEq_of_projectStates_append
#print axioms ObsModel.obsEq_of_projectStates_getLast
#print axioms ObsModel.obsLocalFeasibilityFull_of_tracePlayerStepRecall
#print axioms ObsModel.obsLocalFeasibilityFull_toCore
#print axioms ObsModel.obsLocalFeasibility_of_playerStepRecall
#print axioms ObsModel.obsLocalFeasibility_of_pspr
#print axioms ObsModel.obsLocalFeasibility_of_reachablePlayerStepRecall
#print axioms ObsModel.obsLocalFeasibility_of_tracePlayerStepRecall
#print axioms ObsModel.obsLocalFeasibility_toCore
#print axioms ObsModel.obs_correlated_realization
#print axioms ObsModel.perStepPlayerRecall_iff_forall
#print axioms ObsModel.projectStates_eq_length
#print axioms ObsModel.projectStates_prefix_of_append
#print axioms ObsModel.pureRun_const_of_psar
#print axioms ObsModel.pureRun_cross_mul_product
#print axioms ObsModel.pureRun_eq_const_mul_indicator
#print axioms ObsModel.pureRun_nonzero_iff_action_eq
#print axioms ObsModel.pureRun_nonzero_iff_update
#print axioms ObsModel.pureRun_nonzero_last_stepReachable
#print axioms ObsModel.pureRun_nonzero_to_reachActionTrace
#print axioms ObsModel.pureRun_pairwise_cross_of_psar
#print axioms ObsModel.pureRun_succ_nonzero_iff
#print axioms ObsModel.pureRun_update_obs_local
#print axioms ObsModel.pureRun_update_obs_local_of
#print axioms ObsModel.pureRun_update_obs_local_player
#print axioms ObsModel.pureRun_update_obs_local_pspr
#print axioms ObsModel.pureRun_update_obs_local_trace
#print axioms ObsModel.pureStep_action_eq_of_psar
#print axioms ObsModel.pureStep_component_eq_of_playerRecall
#print axioms ObsModel.pureStep_component_eq_of_pspr
#print axioms ObsModel.pureStep_component_eq_of_reachablePlayerRecall
#print axioms ObsModel.pureStep_component_eq_of_tracePlayerRecall
#print axioms ObsModel.pureStep_cross_ratio
#print axioms ObsModel.pureStep_eq
#print axioms ObsModel.pureStep_eq_of_action_eq
#print axioms ObsModel.pureStep_eq_of_nonzero_same
#print axioms ObsModel.pureStep_nonzero_iff_action_eq
#print axioms ObsModel.pureStep_nonzero_iff_forall_player
#print axioms ObsModel.reweightPMF_pureRun_obs_invariant
#print axioms ObsModel.reweightPMF_update_obs_local
#print axioms ObsModel.reweightPMF_update_obs_local_of
#print axioms ObsModel.reweightPMF_update_obs_local_player
#print axioms ObsModel.reweightPMF_update_obs_local_pspr
#print axioms ObsModel.reweightPMF_update_obs_local_trace
#print axioms ObsModel.runDistPure_eq_pureRun
#print axioms ObsModel.runDist_eq_of_corrProduct
#print axioms ObsModel.runDist_eq_of_stepIndependence
#print axioms ObsModel.stateDepth_projectStates
#print axioms ObsModel.stateSnapshot_projectStates
#print axioms ObsModel.stateSnapshot_projectStatesFrom
#print axioms ObsModel.stepDistCorr_eq_stepDist_of_product
#print axioms ObsModel.stepReachable_init
#print axioms ObsModel.stepReachable_step
#print axioms ObsModel.sum_mul_pmf_ne_top
#print axioms ObsModelCore.PerStepActionRecall.toStepActionDeterminism
#print axioms ObsModelCore.StepActionDeterminism.toMassInvariant
#print axioms ObsModelCore.StepActionDeterminism.toSupportFactorization
#print axioms ObsModelCore.StepSupportFactorization.toRunSupportFactorization
#print axioms ObsModelCore.actionPosteriorLocal_of_obsLocalFeasibility
#print axioms ObsModelCore.correlated_realization
#print axioms ObsModelCore.currentInfoState_subsingleton_of_repeated_on_reachable_trace
#print axioms ObsModelCore.currentObs_projectStates
#print axioms ObsModelCore.currentObs_projectStatesFrom
#print axioms ObsModelCore.jointActionDist_pureToBehavioral
#print axioms ObsModelCore.jointActionDist_pureToBehavioral_m2b
#print axioms ObsModelCore.kuhn_behavioral_to_mixed
#print axioms ObsModelCore.kuhn_mixed_to_behavioral_of_obsLocal
#print axioms ObsModelCore.kuhn_mixed_to_behavioral_of_runSupport
#print axioms ObsModelCore.kuhn_mixed_to_behavioral_semantic
#print axioms ObsModelCore.lastState_append_singleton
#print axioms ObsModelCore.marginal_stepDist
#print axioms ObsModelCore.mediator_step_eq_condStep
#print axioms ObsModelCore.mixedToBehavioralProfileWithFallback_eq_factorAt
#print axioms ObsModelCore.mixedToBehavioralProfileWithFallback_runDist
#print axioms ObsModelCore.mixedToMediator_eq_pmfPi_factor
#print axioms ObsModelCore.mixedToMediator_eq_pmfPi_factor_of_run
#print axioms ObsModelCore.obsLocalFeasibilityFull_of_localSupportSignatureFull
#print axioms ObsModelCore.obsLocalFeasibilityFull_toRunSupportFactorization
#print axioms ObsModelCore.obsLocalFeasibility_of_localSupportSignature
#print axioms ObsModelCore.pureRun_const_of_support
#print axioms ObsModelCore.pureRun_cross_mul_product
#print axioms ObsModelCore.pureRun_cross_mul_product_of_run
#print axioms ObsModelCore.pureRun_nonzero_iff_update
#print axioms ObsModelCore.pureRun_succ_nonzero_iff
#print axioms ObsModelCore.pureStep_eq
#print axioms ObsModelCore.pureStep_eq_of_nonzero_same
#print axioms ObsModelCore.pureStep_nonzero_iff_action_eq
#print axioms ObsModelCore.pureStep_nonzero_iff_forall_player
#print axioms ObsModelCore.reachableInfoStateWithin_mono
#print axioms ObsModelCore.reachableInfoStateWithin_projectStates
#print axioms ObsModelCore.reweightPMF_update_obs_local_of
#print axioms ObsModelCore.runDistPure_congr_of_agree_within
#print axioms ObsModelCore.runDistPure_congr_on_trace
#print axioms ObsModelCore.runDistPure_eq_pureRun
#print axioms ObsModelCore.runDistPure_support_length
#print axioms ObsModelCore.runDist_bind_interp
#print axioms ObsModelCore.runDist_congr
#print axioms ObsModelCore.runDist_eq_of_correlatedStepIndependence
#print axioms ObsModelCore.runDist_eq_of_stepIndependence
#print axioms ObsModelCore.scalar_indep
#print axioms ObsModelCore.stepDistCorr_eq_stepDist_of_product
#print axioms ObsModelCore.stepDist_pureToBehavioral
#print axioms ObsModelCore.stepDist_pureToBehavioral_congr
#print axioms ObsModelCore.stepDist_pureToBehavioral_m2b
#print axioms ObsModelCore.stepIndependence_bridge
#print axioms ObsModelCore.sum_mul_pmf_ne_top
#print axioms ObsModelCore.swapBy_weight_eq
#print axioms ObsModelCore.swapProfileBy_involutive
#print axioms PolynomialDistribution.aePolynomial_of_annihilates_moment_vanishing
#print axioms RidgePowersSpan.ridgePow_span
#print axioms Semantics.Transition.exists_reachBy_iff_reaches
#print axioms Semantics.Transition.exists_reachBy_of_reaches
#print axioms Semantics.Transition.obs_eq_of_reachBy
#print axioms Semantics.Transition.obs_eq_of_reaches
#print axioms Semantics.Transition.reachBy_append
#print axioms Semantics.Transition.reachBy_append_singleton
#print axioms Semantics.Transition.reachBy_map_labels
#print axioms Semantics.Transition.reachBy_map_states
#print axioms Semantics.Transition.reachBy_nil
#print axioms Semantics.Transition.reachBy_singleton
#print axioms Semantics.Transition.reachBy_split
#print axioms Semantics.Transition.reaches_map_states
#print axioms Semantics.Transition.reaches_of_reachBy
#print axioms SmoothCompactAntideriv.exists_iteratedDeriv_eq_of_moments_zero
#print axioms UniformRiemannConvolution.tendstoUniformly_riemannSum_aeContinuous
#print axioms UniformRiemannConvolution.tendstoUniformly_riemannSum_continuous
#print axioms UniversalApproximation.Leshno.AEPolyOn.add
#print axioms UniversalApproximation.Leshno.AEPolyOn.smul
#print axioms UniversalApproximation.Leshno.ApproxByGen.add
#print axioms UniversalApproximation.Leshno.ApproxByGen.smul
#print axioms UniversalApproximation.Leshno.ClassM.aestronglyMeasurable
#print axioms UniversalApproximation.Leshno.ClassM.locallyIntegrable
#print axioms UniversalApproximation.Leshno.ClassM.of_continuous
#print axioms UniversalApproximation.Leshno.Pd_isClosed
#print axioms UniversalApproximation.Leshno.T_isClosed
#print axioms UniversalApproximation.Leshno.aeEq_poly_of_affine
#print axioms UniversalApproximation.Leshno.aePolyOn_genFun
#print axioms UniversalApproximation.Leshno.aePolyOn_of_mem_genSpan
#print axioms UniversalApproximation.Leshno.aePolyOn_zero
#print axioms UniversalApproximation.Leshno.aePolynomial_not_dense
#print axioms UniversalApproximation.Leshno.approxByGen_ridge_of_compact_image
#print axioms UniversalApproximation.Leshno.approxByGen_zero
#print axioms UniversalApproximation.Leshno.contDiff_mollify
#print axioms UniversalApproximation.Leshno.continuous_cvec
#print axioms UniversalApproximation.Leshno.cvec_apply
#print axioms UniversalApproximation.Leshno.cvec_mem_Kset
#print axioms UniversalApproximation.Leshno.denselyApproximates_of_forall_T_eq_top
#print axioms UniversalApproximation.Leshno.deriv_pow_mem
#print axioms UniversalApproximation.Leshno.exists_deriv_ne
#print axioms UniversalApproximation.Leshno.exists_nonpoly_mollify
#print axioms UniversalApproximation.Leshno.genFun_reparam_mem
#print axioms UniversalApproximation.Leshno.isCompact_Kset
#print axioms UniversalApproximation.Leshno.isPolynomialFun_of_continuous_of_aePolynomial
#print axioms UniversalApproximation.Leshno.leshno_dense
#print axioms UniversalApproximation.Leshno.leshno_dense_iff
#print axioms UniversalApproximation.Leshno.mem_T_iff_mem_Tplain
#print axioms UniversalApproximation.Leshno.mollify_eq_convolution
#print axioms UniversalApproximation.Leshno.mollify_ridge_mem_T
#print axioms UniversalApproximation.Leshno.monomial_notMem_Pd
#print axioms UniversalApproximation.Leshno.quasiMeasurePreserving_affine
#print axioms UniversalApproximation.Leshno.restrictLM_apply
#print axioms UniversalApproximation.Leshno.restrictLM_mem_Pd
#print axioms UniversalApproximation.Leshno.ridge_density
#print axioms UniversalApproximation.Leshno.ridge_mem_T
#print axioms UniversalApproximation.Leshno.smooth_engine
#print axioms UniversalApproximation.Leshno.subset_of_ae_restrict_mem
#print axioms UniversalApproximation.Leshno.univariate_density
#print axioms almost_surjective_of_insert_index
#print axioms boundary_is_A_or_B
#print axioms brouwer_fixedPoints_nonempty
#print axioms brouwer_fixed_point
#print axioms brouwer_fixed_point_isFixedPt
#print axioms caratheodory_1
#print axioms case_ABC_count_disj
#print axioms case_AC_ex_unique
#print axioms case_A_not_zero
#print axioms case_A_parent_count
#print axioms case_BC_ex_unique
#print axioms case_B_boundary
#print axioms case_B_not_last
#print axioms case_B_parent_count
#print axioms case_C_parent_count
#print axioms case_D_iff_not_end_1
#print axioms case_D_iff_not_end_2
#print axioms case_D_parent_count
#print axioms ccc_add
#print axioms ccc_fun_case_D_iff
#print axioms ccc_fun_is_insert_index
#print axioms ccc_fun_strict_mono
#print axioms ccc_pos
#print axioms char_complete_face
#print axioms child_map_applied
#print axioms child_map_inj
#print axioms child_map_last
#print axioms child_map_surj_on
#print axioms child_simplex_char
#print axioms complete_boundary_face_last
#print axioms complete_child_uniq
#print axioms complete_simplex_iff
#print axioms delete_vertex_ccc_fun_match
#print axioms delete_vertex_inj
#print axioms delete_vertex_is_face
#print axioms delete_vertex_simplex
#print axioms dist_discrete_map
#print axioms fixed_point_unit_cube
#print axioms fixed_point_unit_cube_isFixedPt
#print axioms handshake_1
#print axioms handshake_2
#print axioms handshake_3
#print axioms homeo_of_finrank_eq
#print axioms homeo_unit_ball
#print axioms homeo_unit_cube_of_convex_compact
#print axioms incomplete_childs
#print axioms induction_start
#print axioms insert_index_inj
#print axioms insert_index_ne
#print axioms insert_index_strict_mono
#print axioms insert_vertex
#print axioms is_id_of_strict_mono
#print axioms is_insert_index_of_strict_mono
#print axioms kakutani_fixed_point
#print axioms last_eq_first_add_one
#print axioms last_of_simplex
#print axioms le_add_one_of_simplex
#print axioms mem_of_convex_comb
#print axioms monotone_1_of_simplex
#print axioms monotone_2_of_simplex
#print axioms nearby_points
#print axioms odd_of_boundary_faces
#print axioms one_of_ABCD
#print axioms p_ne_zero_of_cube
#print axioms parent_count
#print axioms parent_injective
#print axioms parent_simplex_case_AC
#print axioms parent_simplex_case_BC
#print axioms parent_simplex_case_D
#print axioms reduced_label_props_1
#print axioms reduced_label_props_2
#print axioms reduced_label_props_3
#print axioms rl_inj_of_complete
#print axioms same_delete_index_eq_iff
#print axioms set_valued_map_approx_fixed_point
#print axioms strong_cubical_sperner
#print axioms sub_ICC_of_convex_comb
#print axioms surround_index
#print axioms unique_const_ABC
#print axioms unit_cube_homeo_unit_ball
#print axioms weaker_cubical_sperner
#print axioms zero_ne_last
