import JurisLean.FullMath.Contracts

/-! Generated acceptances: each is discharged by the mapped module
theorem (definitional equality on binder annotations). -/

open JurisLean.FullMath.Core
open JurisLean.FullMath.Logic
open JurisLean.FullMath.Evidence
open JurisLean.FullMath.Probability
open JurisLean.FullMath.Numeric
open JurisLean.FullMath.Burden
open JurisLean.FullMath.Action
open JurisLean.FullMath.Composition
open JurisLean.FullMath.Representation
open JurisLean.FullMath.Causal
open JurisLean.FullMath.Document
open JurisLean.FullMath.Roots
open JurisLean.FullMath.Gaps
open JurisLean.FullMath.Numeric.Iv

namespace JurisLean.FullMath.Acceptance

theorem target_F01 : Contracts.target_F01 := JurisLean.FullMath.Core.phi_iff_components

theorem target_F02 : Contracts.target_F02 := JurisLean.FullMath.Core.migrate_main_key

theorem target_F03 : Contracts.target_F03 := JurisLean.FullMath.Core.composable_projections

theorem target_F04 : Contracts.target_F04 := JurisLean.FullMath.Evidence.deps_complete

theorem target_F05 : Contracts.target_F05 := JurisLean.FullMath.Logic.cl_mono

theorem target_F06 : Contracts.target_F06 := JurisLean.FullMath.Logic.generate_complete

theorem target_F07 : Contracts.target_F07 := JurisLean.FullMath.Logic.rooted_same_conclusion_different_identity

theorem target_F08 : Contracts.target_F08 := JurisLean.FullMath.Logic.edgeFuel_iff

theorem target_F09 : Contracts.target_F09 := JurisLean.FullMath.Logic.pending_edges_bound

theorem target_F10 : Contracts.target_F10 := JurisLean.FullMath.Logic.grounded_least

theorem target_F11 : Contracts.target_F11 := JurisLean.FullMath.Logic.incomplete_not_universal

theorem target_F12 : Contracts.target_F12 := JurisLean.FullMath.Evidence.verified_requires_source_authority

theorem target_F13 : Contracts.target_F13 := JurisLean.FullMath.Evidence.add_only_reuse

theorem target_F14 : Contracts.target_F14 := JurisLean.FullMath.Evidence.addOnly_matches_full_recompute

theorem target_P01 : Contracts.target_P01 := JurisLean.FullMath.Probability.joint_normalizes

theorem target_P02 : Contracts.target_P02 := JurisLean.FullMath.Probability.posterior_normalizes

theorem target_P03 : Contracts.target_P03 := JurisLean.FullMath.Probability.sum_out_distrib

theorem target_P04 : Contracts.target_P04 := JurisLean.FullMath.Probability.dedup_no_double_update

theorem target_P05 : Contracts.target_P05 := JurisLean.FullMath.Probability.dirWeights_update_compose

theorem target_P06 : Contracts.target_P06 := JurisLean.FullMath.Probability.hyper_data_changes_posterior

theorem target_P07 : Contracts.target_P07 := JurisLean.FullMath.Probability.mixture_within_retained

theorem target_P08 : Contracts.target_P08 := JurisLean.FullMath.Probability.contamination_bounds

theorem target_P09 : Contracts.target_P09 := JurisLean.FullMath.Probability.unprocessed_mass_bounds

theorem target_P10 : Contracts.target_P10 := JurisLean.FullMath.Probability.beta_mixture_mass

theorem target_P11 : Contracts.target_P11 := JurisLean.FullMath.Probability.time_order_enforced

theorem target_P12 : Contracts.target_P12 := JurisLean.FullMath.Probability.brier_excess_identity

theorem target_P13 : Contracts.target_P13 := JurisLean.FullMath.Probability.pav_two_point_optimal

theorem target_E01 : Contracts.target_E01 := JurisLean.FullMath.Probability.e01_within_iff

theorem target_N01 : Contracts.target_N01 := JurisLean.FullMath.Numeric.conservation

theorem target_N02 : Contracts.target_N02 := JurisLean.FullMath.Numeric.mul_sound

theorem target_N03 : Contracts.target_N03 := JurisLean.FullMath.Numeric.weak_duality

theorem target_N04 : Contracts.target_N04 := JurisLean.FullMath.Numeric.seen_span_not_global_bound

theorem target_N05 : Contracts.target_N05 := JurisLean.FullMath.Numeric.equal_objectives_certify

theorem target_N06 : Contracts.target_N06 := JurisLean.FullMath.Numeric.kkt1_sufficient

theorem target_N07 : Contracts.target_N07 := JurisLean.FullMath.Numeric.branch_cover

theorem target_N08 : Contracts.target_N08 := JurisLean.FullMath.Numeric.T_contraction

theorem target_N09 : Contracts.target_N09 := JurisLean.FullMath.Numeric.T_fixed_point

theorem target_N10 : Contracts.target_N10 := JurisLean.FullMath.Numeric.T_fixed_interior

theorem target_B01 : Contracts.target_B01 := JurisLean.FullMath.Burden.conflict_without_rule_is_pending

theorem target_B02 : Contracts.target_B02 := JurisLean.FullMath.Burden.no_terminal_when_incomplete

theorem target_B03 : Contracts.target_B03 := JurisLean.FullMath.Burden.gate_established_iff

theorem target_B04 : Contracts.target_B04 := JurisLean.FullMath.Burden.civil_allocation_complete

theorem target_B05 : Contracts.target_B05 := JurisLean.FullMath.Burden.criminal_allocation_complete

theorem target_B06 : Contracts.target_B06 := JurisLean.FullMath.Burden.admin_allocation_complete

theorem target_B07 : Contracts.target_B07 := JurisLean.FullMath.Burden.version_change_invalidates

theorem target_G01 : Contracts.target_G01 := JurisLean.FullMath.Numeric.vf_dominates

theorem target_G02 : Contracts.target_G02 := JurisLean.FullMath.Action.gross_voi_nonneg

theorem target_G03 : Contracts.target_G03 := JurisLean.FullMath.Action.admissible_settlement_bounds

theorem target_G04 : Contracts.target_G04 := JurisLean.FullMath.Action.dsic_of_label

theorem target_G05 : Contracts.target_G05 := JurisLean.FullMath.Action.rectangle_lower_bound

theorem target_C01 : Contracts.target_C01 := JurisLean.FullMath.Composition.relComp_assoc

theorem target_C02 : Contracts.target_C02 := JurisLean.FullMath.Composition.outer_two_step

theorem target_C03 : Contracts.target_C03 := JurisLean.FullMath.Composition.scenario_bridge

theorem target_C04 : Contracts.target_C04 := JurisLean.FullMath.Composition.joint_instance

theorem target_C05 : Contracts.target_C05 := JurisLean.FullMath.Composition.chain_carries_ids

theorem target_C06 : Contracts.target_C06 := JurisLean.FullMath.Composition.checker_correspondence

theorem target_C07 : Contracts.target_C07 := ⟨JurisLean.FullMath.Roots.root_GENERIC_FINITE, JurisLean.FullMath.Roots.root_SYMBOLIC_EXACT_box, JurisLean.FullMath.Roots.root_STATISTICAL_COMPOSITION, JurisLean.FullMath.Roots.root_CIVIL, JurisLean.FullMath.Roots.root_CRIMINAL, JurisLean.FullMath.Roots.root_ADMINISTRATIVE, JurisLean.FullMath.Roots.root_DOCUMENT_DELIVERY⟩

theorem target_EXT01 : Contracts.target_EXT01 := JurisLean.FullMath.Representation.certificate_implies_mode

theorem target_EXT02 : Contracts.target_EXT02 := JurisLean.FullMath.Core.carries_binds_identity

theorem target_EXT03 : Contracts.target_EXT03 := JurisLean.FullMath.Logic.grounded_fixpoint

theorem target_EXT04 : Contracts.target_EXT04 := JurisLean.FullMath.Representation.splitBox_cover

theorem target_EXT05 : Contracts.target_EXT05 := JurisLean.FullMath.Evidence.invalidated_of_retired_used

theorem target_EXT06 : Contracts.target_EXT06 := JurisLean.FullMath.Probability.parts_cover

theorem target_EXT07 : Contracts.target_EXT07 := JurisLean.FullMath.Causal.sup_not_attained

theorem target_EXT08 : Contracts.target_EXT08 := JurisLean.FullMath.Action.shared_theta_total_identity

theorem target_EXT09 : Contracts.target_EXT09 := JurisLean.FullMath.Roots.ext09_domainComposition

theorem demand_D001 : Contracts.demand_D001 := JurisLean.FullMath.Core.locator_not_identity

theorem demand_D002 : Contracts.demand_D002 := JurisLean.FullMath.Core.locator_not_identity

theorem demand_D003 : Contracts.demand_D003 := JurisLean.FullMath.Core.locator_not_identity

theorem demand_D004 : Contracts.demand_D004 := JurisLean.FullMath.Core.locator_not_identity

theorem demand_D005 : Contracts.demand_D005 := JurisLean.FullMath.Core.locator_not_identity

theorem demand_D006 : Contracts.demand_D006 := JurisLean.FullMath.Core.locator_not_identity

theorem demand_D007 : Contracts.demand_D007 := JurisLean.FullMath.Core.locator_not_identity

theorem demand_D008 : Contracts.demand_D008 := JurisLean.FullMath.Core.locator_not_identity

theorem demand_D009 : Contracts.demand_D009 := JurisLean.FullMath.Burden.unknown_is_pending

theorem demand_D010 : Contracts.demand_D010 := JurisLean.FullMath.Burden.unknown_is_pending

theorem demand_D011 : Contracts.demand_D011 := JurisLean.FullMath.Burden.unknown_is_pending

theorem demand_D012 : Contracts.demand_D012 := JurisLean.FullMath.Burden.unknown_is_pending

theorem demand_D013 : Contracts.demand_D013 := JurisLean.FullMath.Burden.unknown_is_pending

theorem demand_D014 : Contracts.demand_D014 := JurisLean.FullMath.Burden.unknown_is_pending

theorem demand_D015 : Contracts.demand_D015 := JurisLean.FullMath.Burden.unknown_is_pending

theorem demand_D016 : Contracts.demand_D016 := JurisLean.FullMath.Burden.unknown_is_pending

theorem demand_D017 : Contracts.demand_D017 := JurisLean.FullMath.Burden.unknown_is_pending

theorem demand_D018 : Contracts.demand_D018 := JurisLean.FullMath.Burden.unknown_is_pending

theorem demand_D019 : Contracts.demand_D019 := JurisLean.FullMath.Probability.dedup_conflict_not_overwrite

theorem demand_D020 : Contracts.demand_D020 := JurisLean.FullMath.Probability.dedup_conflict_not_overwrite

theorem demand_D021 : Contracts.demand_D021 := JurisLean.FullMath.Probability.dedup_conflict_not_overwrite

theorem demand_D022 : Contracts.demand_D022 := JurisLean.FullMath.Probability.dedup_conflict_not_overwrite

theorem demand_D023 : Contracts.demand_D023 := JurisLean.FullMath.Probability.dedup_conflict_not_overwrite

theorem demand_D024 : Contracts.demand_D024 := JurisLean.FullMath.Probability.dedup_conflict_not_overwrite

theorem demand_D025 : Contracts.demand_D025 := JurisLean.FullMath.Probability.dedup_conflict_not_overwrite

theorem demand_D026 : Contracts.demand_D026 := JurisLean.FullMath.Probability.dedup_conflict_not_overwrite

theorem demand_D027 : Contracts.demand_D027 := JurisLean.FullMath.Probability.dedup_conflict_not_overwrite

theorem demand_D028 : Contracts.demand_D028 := JurisLean.FullMath.Probability.dedup_conflict_not_overwrite

theorem demand_D029 : Contracts.demand_D029 := JurisLean.FullMath.Logic.generate_sound

theorem demand_D030 : Contracts.demand_D030 := JurisLean.FullMath.Logic.generate_sound

theorem demand_D031 : Contracts.demand_D031 := JurisLean.FullMath.Logic.generate_sound

theorem demand_D032 : Contracts.demand_D032 := JurisLean.FullMath.Logic.generate_sound

theorem demand_D033 : Contracts.demand_D033 := JurisLean.FullMath.Logic.generate_sound

theorem demand_D034 : Contracts.demand_D034 := JurisLean.FullMath.Logic.generate_sound

theorem demand_D035 : Contracts.demand_D035 := JurisLean.FullMath.Logic.generate_sound

theorem demand_D036 : Contracts.demand_D036 := JurisLean.FullMath.Logic.generate_sound

theorem demand_D037 : Contracts.demand_D037 := JurisLean.FullMath.Burden.perPerson_slots_distinct

theorem demand_D038 : Contracts.demand_D038 := JurisLean.FullMath.Burden.perPerson_slots_distinct

theorem demand_D039 : Contracts.demand_D039 := JurisLean.FullMath.Burden.perPerson_slots_distinct

theorem demand_D040 : Contracts.demand_D040 := JurisLean.FullMath.Burden.perPerson_slots_distinct

theorem demand_D041 : Contracts.demand_D041 := JurisLean.FullMath.Burden.perPerson_slots_distinct

theorem demand_D042 : Contracts.demand_D042 := JurisLean.FullMath.Burden.perPerson_slots_distinct

theorem demand_D043 : Contracts.demand_D043 := JurisLean.FullMath.Burden.perPerson_slots_distinct

theorem demand_D044 : Contracts.demand_D044 := JurisLean.FullMath.Burden.perPerson_slots_distinct

theorem demand_D045 : Contracts.demand_D045 := JurisLean.FullMath.Burden.perPerson_slots_distinct

theorem demand_D046 : Contracts.demand_D046 := JurisLean.FullMath.Burden.perPerson_slots_distinct

theorem demand_D047 : Contracts.demand_D047 := JurisLean.FullMath.Numeric.parts_nonneg

theorem demand_D048 : Contracts.demand_D048 := JurisLean.FullMath.Numeric.parts_nonneg

theorem demand_D049 : Contracts.demand_D049 := JurisLean.FullMath.Numeric.parts_nonneg

theorem demand_D050 : Contracts.demand_D050 := JurisLean.FullMath.Numeric.parts_nonneg

theorem demand_D051 : Contracts.demand_D051 := JurisLean.FullMath.Numeric.parts_nonneg

theorem demand_D052 : Contracts.demand_D052 := JurisLean.FullMath.Numeric.parts_nonneg

theorem demand_D053 : Contracts.demand_D053 := JurisLean.FullMath.Numeric.parts_nonneg

theorem demand_D054 : Contracts.demand_D054 := JurisLean.FullMath.Numeric.parts_nonneg

theorem demand_D055 : Contracts.demand_D055 := JurisLean.FullMath.Numeric.parts_nonneg

theorem demand_D056 : Contracts.demand_D056 := JurisLean.FullMath.Numeric.parts_nonneg

theorem demand_D057 : Contracts.demand_D057 := JurisLean.FullMath.Numeric.fixed_y_bounds

theorem demand_D058 : Contracts.demand_D058 := JurisLean.FullMath.Numeric.fixed_y_bounds

theorem demand_D059 : Contracts.demand_D059 := JurisLean.FullMath.Numeric.fixed_y_bounds

theorem demand_D060 : Contracts.demand_D060 := JurisLean.FullMath.Numeric.fixed_y_bounds

theorem demand_D061 : Contracts.demand_D061 := JurisLean.FullMath.Numeric.fixed_y_bounds

theorem demand_D062 : Contracts.demand_D062 := JurisLean.FullMath.Numeric.fixed_y_bounds

theorem demand_D063 : Contracts.demand_D063 := JurisLean.FullMath.Numeric.fixed_y_bounds

theorem demand_D064 : Contracts.demand_D064 := JurisLean.FullMath.Numeric.fixed_y_bounds

theorem demand_D065 : Contracts.demand_D065 := JurisLean.FullMath.Document.docPut_docPut

theorem demand_D066 : Contracts.demand_D066 := JurisLean.FullMath.Document.docPut_docPut

theorem demand_D067 : Contracts.demand_D067 := JurisLean.FullMath.Document.docPut_docPut

theorem demand_D068 : Contracts.demand_D068 := JurisLean.FullMath.Document.docPut_docPut

theorem demand_D069 : Contracts.demand_D069 := JurisLean.FullMath.Document.docPut_docPut

theorem demand_D070 : Contracts.demand_D070 := JurisLean.FullMath.Document.docPut_docPut

theorem demand_D071 : Contracts.demand_D071 := JurisLean.FullMath.Document.docPut_docPut

theorem demand_D072 : Contracts.demand_D072 := JurisLean.FullMath.Document.docPut_docPut

theorem demand_D073 : Contracts.demand_D073 := JurisLean.FullMath.Document.docPut_docPut

theorem demand_D074 : Contracts.demand_D074 := JurisLean.FullMath.Document.docPut_docPut

theorem demand_D075 : Contracts.demand_D075 := JurisLean.FullMath.Document.docPut_docPut

theorem demand_D076 : Contracts.demand_D076 := JurisLean.FullMath.Document.docPut_docPut

theorem demand_D077 : Contracts.demand_D077 := JurisLean.FullMath.Logic.cl_least_iterate

theorem demand_D078 : Contracts.demand_D078 := JurisLean.FullMath.Logic.cl_least_iterate

theorem demand_D079 : Contracts.demand_D079 := JurisLean.FullMath.Logic.cl_least_iterate

theorem demand_D080 : Contracts.demand_D080 := JurisLean.FullMath.Logic.cl_least_iterate

theorem demand_D081 : Contracts.demand_D081 := JurisLean.FullMath.Logic.cl_least_iterate

theorem demand_D082 : Contracts.demand_D082 := JurisLean.FullMath.Logic.cl_least_iterate

theorem demand_D083 : Contracts.demand_D083 := JurisLean.FullMath.Logic.cl_least_iterate

theorem demand_D084 : Contracts.demand_D084 := JurisLean.FullMath.Logic.cl_least_iterate

theorem demand_D085 : Contracts.demand_D085 := JurisLean.FullMath.Logic.cl_least_iterate

theorem demand_D086 : Contracts.demand_D086 := JurisLean.FullMath.Logic.cl_least_iterate

theorem demand_D087 : Contracts.demand_D087 := JurisLean.FullMath.Logic.exists_extension_witnessed

theorem demand_D088 : Contracts.demand_D088 := JurisLean.FullMath.Logic.exists_extension_witnessed

theorem demand_D089 : Contracts.demand_D089 := JurisLean.FullMath.Logic.exists_extension_witnessed

theorem demand_D090 : Contracts.demand_D090 := JurisLean.FullMath.Logic.exists_extension_witnessed

theorem demand_D091 : Contracts.demand_D091 := JurisLean.FullMath.Logic.exists_extension_witnessed

theorem demand_D092 : Contracts.demand_D092 := JurisLean.FullMath.Logic.exists_extension_witnessed

theorem demand_D093 : Contracts.demand_D093 := JurisLean.FullMath.Logic.exists_extension_witnessed

theorem demand_D094 : Contracts.demand_D094 := JurisLean.FullMath.Logic.exists_extension_witnessed

theorem demand_D095 : Contracts.demand_D095 := JurisLean.FullMath.Numeric.succDay_ordinal_mono

theorem demand_D096 : Contracts.demand_D096 := JurisLean.FullMath.Numeric.succDay_ordinal_mono

theorem demand_D097 : Contracts.demand_D097 := JurisLean.FullMath.Numeric.succDay_ordinal_mono

theorem demand_D098 : Contracts.demand_D098 := JurisLean.FullMath.Numeric.succDay_ordinal_mono

theorem demand_D099 : Contracts.demand_D099 := JurisLean.FullMath.Numeric.succDay_ordinal_mono

theorem demand_D100 : Contracts.demand_D100 := JurisLean.FullMath.Numeric.succDay_ordinal_mono

theorem demand_D101 : Contracts.demand_D101 := JurisLean.FullMath.Numeric.succDay_ordinal_mono

theorem demand_D102 : Contracts.demand_D102 := JurisLean.FullMath.Numeric.succDay_ordinal_mono

theorem demand_D103 : Contracts.demand_D103 := JurisLean.FullMath.Numeric.succDay_ordinal_mono

theorem demand_D104 : Contracts.demand_D104 := JurisLean.FullMath.Document.parse_render_roundtrip

theorem demand_D105 : Contracts.demand_D105 := JurisLean.FullMath.Document.parse_render_roundtrip

theorem demand_D106 : Contracts.demand_D106 := JurisLean.FullMath.Document.parse_render_roundtrip

theorem demand_D107 : Contracts.demand_D107 := JurisLean.FullMath.Document.parse_render_roundtrip

theorem demand_D108 : Contracts.demand_D108 := JurisLean.FullMath.Document.parse_render_roundtrip

theorem demand_D109 : Contracts.demand_D109 := JurisLean.FullMath.Document.parse_render_roundtrip

theorem demand_D110 : Contracts.demand_D110 := JurisLean.FullMath.Document.parse_render_roundtrip

theorem demand_D111 : Contracts.demand_D111 := JurisLean.FullMath.Document.parse_render_roundtrip

theorem demand_D112 : Contracts.demand_D112 := JurisLean.FullMath.Document.parse_render_roundtrip

theorem demand_D113 : Contracts.demand_D113 := JurisLean.FullMath.Document.parse_render_roundtrip

theorem demand_D114 : Contracts.demand_D114 := JurisLean.FullMath.Document.parse_render_roundtrip

theorem demand_D115 : Contracts.demand_D115 := JurisLean.FullMath.Document.parse_render_roundtrip

theorem demand_D116 : Contracts.demand_D116 := JurisLean.FullMath.Numeric.bellman_onesided

theorem demand_D117 : Contracts.demand_D117 := JurisLean.FullMath.Numeric.bellman_onesided

theorem demand_D118 : Contracts.demand_D118 := JurisLean.FullMath.Numeric.bellman_onesided

theorem demand_D119 : Contracts.demand_D119 := JurisLean.FullMath.Numeric.bellman_onesided

theorem demand_D120 : Contracts.demand_D120 := JurisLean.FullMath.Numeric.bellman_onesided

theorem demand_D121 : Contracts.demand_D121 := JurisLean.FullMath.Numeric.bellman_onesided

theorem demand_D122 : Contracts.demand_D122 := JurisLean.FullMath.Numeric.bellman_onesided

theorem demand_D123 : Contracts.demand_D123 := JurisLean.FullMath.Numeric.bellman_onesided

theorem demand_D124 : Contracts.demand_D124 := JurisLean.FullMath.Evidence.step_rules_mono

theorem demand_D125 : Contracts.demand_D125 := JurisLean.FullMath.Evidence.step_rules_mono

theorem demand_D126 : Contracts.demand_D126 := JurisLean.FullMath.Evidence.step_rules_mono

theorem demand_D127 : Contracts.demand_D127 := JurisLean.FullMath.Evidence.step_rules_mono

theorem demand_D128 : Contracts.demand_D128 := JurisLean.FullMath.Evidence.step_rules_mono

theorem demand_D129 : Contracts.demand_D129 := JurisLean.FullMath.Evidence.step_rules_mono

theorem demand_D130 : Contracts.demand_D130 := JurisLean.FullMath.Evidence.step_rules_mono

theorem demand_D131 : Contracts.demand_D131 := JurisLean.FullMath.Probability.condition_incompatible_iff

theorem demand_D132 : Contracts.demand_D132 := JurisLean.FullMath.Probability.condition_incompatible_iff

theorem demand_D133 : Contracts.demand_D133 := JurisLean.FullMath.Probability.condition_incompatible_iff

theorem demand_D134 : Contracts.demand_D134 := JurisLean.FullMath.Probability.condition_incompatible_iff

theorem gap_X01 : Contracts.gap_X01 := JurisLean.FullMath.Gaps.gap_X01

theorem gap_X02 : Contracts.gap_X02 := JurisLean.FullMath.Gaps.gap_X02

theorem gap_X03 : Contracts.gap_X03 := JurisLean.FullMath.Gaps.gap_X03

theorem gap_X04 : Contracts.gap_X04 := JurisLean.FullMath.Gaps.gap_X04

theorem gap_X05 : Contracts.gap_X05 := JurisLean.FullMath.Gaps.gap_X05

theorem gap_X06 : Contracts.gap_X06 := JurisLean.FullMath.Gaps.gap_X06

theorem gap_X07 : Contracts.gap_X07 := JurisLean.FullMath.Gaps.gap_X07

theorem gap_X08 : Contracts.gap_X08 := JurisLean.FullMath.Gaps.gap_X08

theorem gap_X09 : Contracts.gap_X09 := JurisLean.FullMath.Gaps.gap_X09

theorem gap_X10 : Contracts.gap_X10 := JurisLean.FullMath.Gaps.gap_X10

theorem root_GENERIC_FINITE : Contracts.root_GENERIC_FINITE := JurisLean.FullMath.Roots.root_GENERIC_FINITE

theorem root_SYMBOLIC_EXACT : Contracts.root_SYMBOLIC_EXACT := JurisLean.FullMath.Roots.root_SYMBOLIC_EXACT_box

theorem root_STATISTICAL_COMPOSITION : Contracts.root_STATISTICAL_COMPOSITION := JurisLean.FullMath.Roots.root_STATISTICAL_COMPOSITION

theorem root_CIVIL : Contracts.root_CIVIL := JurisLean.FullMath.Roots.root_CIVIL

theorem root_CRIMINAL : Contracts.root_CRIMINAL := JurisLean.FullMath.Roots.root_CRIMINAL

theorem root_ADMINISTRATIVE : Contracts.root_ADMINISTRATIVE := JurisLean.FullMath.Roots.root_ADMINISTRATIVE

theorem root_DOCUMENT_DELIVERY : Contracts.root_DOCUMENT_DELIVERY := JurisLean.FullMath.Roots.root_DOCUMENT_DELIVERY

end JurisLean.FullMath.Acceptance
