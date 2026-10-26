"""The archive-gap close layer stays fail-closed after the CAND7 wiring close.

The live pin is subject 21862d9b / run 40274167574 / job 121413235107.
CAND5, CAND5bis, and CAND6 remain CLOSED_BY_WIRING historically.
This round closes CAND7 (U07.1/U02.3/U04.3/U05.2/U06.3) by wiring:
close_admitted=true, UNWIRED empty, SCOPE_REVIEW present.
closed_this_round=5, OPEN_FORMAL_TAIL=20, CLOSED_BY_WIRING=22,
blocked_rows=20, candidate_rows=0.
discharges stays false; math_flip stays false; step 2 stays open.
The expand receipt ci-tip-21862d9b stays named_count=61, closes_debt=false,
and closed increment 0. Historical ci-tip-1c72e444 stays named_count=49.
"""

from __future__ import annotations

import importlib.util
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TOOL = ROOT / "scripts" / "ci" / "check_archive_gap_close.py"
# archive_gap_dispositions.py is the path table imported by the checker above.
DISPOSITIONS = ROOT / "scripts" / "ci" / "archive_gap_dispositions.py"

_spec = importlib.util.spec_from_file_location("check_archive_gap_close", TOOL)
checker = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(checker)


def test_close_layer_matches_the_pack_and_keeps_discharges_false() -> None:
    proc = subprocess.run(
        [sys.executable, str(TOOL)],
        cwd=ROOT,
        capture_output=True,
        text=True,
        encoding="utf-8",
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "narrow 8" in proc.stdout
    assert "wiring 22" in proc.stdout
    assert "open_formal_tail 20" in proc.stdout
    assert "discharges false" in proc.stdout
    assert "40274167574" in proc.stdout
    assert "formal_tail_closed_this_round 5" in proc.stdout
    assert "step_2_closed false" in proc.stdout


def test_u04_3_existence_stays_unproved_and_u02_4_u10_1_carry_non_goals() -> None:
    errors, ledger = checker.check(write=False)
    assert errors == []
    by_clause = {row["clause"]: row for row in ledger["rows"]}
    penalized = by_clause["U04.3"]
    assert penalized["archive_gap_status"] == "CLOSED_BY_WIRING"
    assert penalized["suggested_close_path"] == "证"
    assert penalized["unwired_formal_obligations"] == []
    assert "本条关项范围＝FormalTail 覆盖的形式义务" in penalized["scope_review"]
    assert any("校准" in item for item in penalized["non_goals"])
    assert "校准" in penalized["scope_review"]
    tower = by_clause["U02.4"]
    assert tower["archive_gap_status"] == "CLOSED_BY_NARROW"
    assert any("general filtration/random-budget tower" in item for item in tower["non_goals"])
    authority = by_clause["U10.1"]
    assert authority["suggested_close_path"] == "证"
    assert any("真实授权合法性" in item for item in authority["non_goals"])
    assert any("protocol refinement" in item for item in authority["unwired_formal_obligations"])
    assert ledger["discharges_archived_manuscript_gaps"] is False
    assert ledger["math_flip_authorized"] is False
    assert ledger["counts"]["放弃"] == 0
    assert ledger["formal_tail_criteria_pack"] == (
        "/home/box/shared/legal-math-reviewer/formal_tail_判据包_20261024/"
    )
    summary = ledger["formal_tail_round"]
    assert summary["step_2_closed"] is False
    assert summary["closed_this_round"] == 5
    assert summary["open_formal_tail_remaining"] == 20
    assert summary["candidate_rows"] == 0
    assert summary["blocked_rows"] == 20
    assert summary["discharges_archived_manuscript_gaps"] is False
    assert summary["math_flip_authorized"] is False
    assert summary["step_2_closed"] is False
    assert summary["close_pack"] == (
        "/home/box/shared/legal-math-reviewer/formal_tail_关≥1_CAND7_20261026/"
    )
    assert summary["tip_pin_not_retargeted"] is False
    assert summary["tip_pin"]["subject"] == "21862d9bdd94bfa15e5da39079538b5eb30ff235"
    assert summary["tip_pin"]["run_id"] == 40274167574
    assert summary["tip_pin"]["job_id"] == 121413235107
    assert summary["tip_pin"]["verification"] == "evidence/ci-tip-21862d9b/verification.json"
    assert summary["formal_tail_expand_audit"]["verification"] == (
        "evidence/ci-tip-21862d9b/verification.json"
    )
    assert summary["formal_tail_expand_audit"]["tip_authority_run_id"] == 40274167574
    assert summary["formal_tail_expand_audit"]["live_tip_pin_retarget"] == "BOUND"
    assert summary["formal_tail_expand_audit"]["tip_authority_run_status"] == "SUCCESS"
    assert summary["formal_tail_expand_audit"]["job_id"] == 121413235107
    assert summary["formal_tail_expand_audit"]["criteria_pack"] == "tip_pin_扩审计_CAND7_20261026"
    assert ledger["tip_pin_not_retargeted"] is False
    assert ledger["counts"]["OPEN_FORMAL_TAIL"] == 20
    assert ledger["counts"]["CLOSED_BY_WIRING"] == 22
    assert summary["later_tip_gate_not_a_close"]["run_id"] == 40063377178
    assert summary["later_tip_gate_not_a_close"]["closes_debt"] is False
    assert summary["later_tip_gate_not_a_close"]["retargets_tip_pin"] is False
    assert summary["narrow_not_reopened"] == [
        "U02.4", "U09.2", "U01.4", "U04.1", "U04.4", "U05.1", "U06.5", "U00",
    ]
    assert summary["wiring_not_reopened"] == [
        "U02.2", "U01.0", "U06.4", "U08.1", "U10.3", "U12.2", "U14.2",
        "U08.2", "U09.3", "U13.1", "U15.1", "U15.2",
        "U08.3", "U15.3", "U13.2", "U09.1", "U10.2",
        "U07.1", "U02.3", "U04.3", "U05.2", "U06.3",
    ]
    # CAND5 remain CLOSED_BY_WIRING (historical).
    cand5 = ("U06.4", "U08.1", "U10.3", "U12.2", "U14.2")
    for clause in cand5:
        row = by_clause[clause]
        assert row["archive_gap_status"] == "CLOSED_BY_WIRING"
        assert row["unwired_formal_obligations"] == []
        assert str(row["scope_review"]).strip()
        assert row["formal_tail_prove"]["in_this_round"] is False
        assert row["formal_tail_prove"]["not_reopened"] is True
        assert row["formal_tail_prove"]["archive_gap_status"] == "CLOSED_BY_WIRING"
        assert row["formal_tail_prove"]["close_admitted"] is True
        assert row["formal_tail_prove"]["step_2_closed"] is False
        assert row["formal_tail_prove"]["discharges_archived_manuscript_gaps"] is False
        # FormalTail module / short names must not appear in wired_declarations
        # (Final20261021 tip-pin u06_4_threshold_* etc. remain allowed).
        formal_tail_shorts = {
            "u06_4_increasing_threshold_above_one_excludes",
            "u06_4_increasing_threshold_at_most_zero_includes",
            "u06_4_decreasing_threshold_below_zero_excludes",
            "u06_4_decreasing_threshold_at_least_one_includes",
            "u06_4_increasing_unit_interval_above_one_is_empty",
            "u06_4_increasing_unit_interval_at_most_zero_is_full",
            "u06_4_decreasing_unit_interval_below_zero_is_empty",
            "u06_4_decreasing_unit_interval_at_least_one_is_full",
            "u08_1_recorded_after_cutoff_not_visible",
            "u08_1_late_append_uses_selection_stable",
            "u08_1_late_record_disguised_as_then_known_changes_applicability",
            "u08_1_mutable_current_status_disagrees_with_cutoff",
            "u10_3_zero_step_ranked_path_is_identity",
            "u10_3_zero_step_prohibits_strict_progress",
            "u10_3_business_observation_faithful",
            "u10_3_zero_observation_is_not_progress",
            "u10_3_one_real_step_zero_abstract_is_not_progress",
            "u12_2_halving_damps_toward_zero",
            "u12_2_negation_orbit_oscillates",
            "u12_2_one_minus_theta_oscillates",
            "u12_2_shift_has_no_fixed_point",
            "u12_2_cubic_reaches_zero_but_expands",
            "u14_2_zero_N_rejects_positive_hypothesis",
            "u14_2_endogenous_equal_sizes_are_not_the_fixed_witness",
            "u14_2_common_cause_copy_exceeds_independent_variance",
        }
        for item in row["wired_declarations"]:
            assert "FormalTail20261024" not in item["name"]
            assert item["name"].split(".")[-1] not in formal_tail_shorts
    same_row = by_clause["U10.3"]
    assert any("公平" in item for item in same_row["non_goals"])
    assert "公平" in same_row["companion_scope_notes"] or any(
        "公平" in item for item in same_row["non_goals"]
    )
    assert any("另证" in item for item in same_row["non_goals"])
    blocked = [
        "U01.1", "U01.2", "U01.3", "U02.1", "U03.1", "U03.2",
        "U04.2", "U04.5", "U06.1", "U06.2",
        "U07.2", "U07.3",
        "U10.1", "U11.1", "U12.1", "U12.3", "U12.4",
        "U13.3", "U13.4", "U14.1",
    ]
    assert len(blocked) == 20
    cand6_shorts = [
        "u08_3_four_states_do_not_exhaust_dependency_policies",
        "u08_3_judgment_not_compatibility_world_classification",
        "u08_3_opposition_preserves_support_not_full_reflection",
        "u15_3_two_point_risks_do_not_complete_five_evidence_levels",
        "u15_3_second_round_consumer_is_not_evidence_ladder",
        "u13_2_frames_do_not_imply_authorized_rule_load",
        "u13_2_condition_does_not_train_not_persistent_storage_refinement",
        "u09_1_conservation_not_receipt_revision_order",
        "u09_1_receipt_coherent_not_cash_uniqueness",
        "u09_1_at_most_once_not_product_protocol_refinement",
        "u10_2_executor_and_trace_not_full_mixed_operation_coverage",
        "u10_2_post_invariant_not_gamma_frame_or_service_refinement",
    ]
    formal_tail_text = (
        ROOT / "proofs/lean/juris_lean/JurisLean/Candidates/FormalTail20261024.lean"
    ).read_text(encoding="utf-8")
    cand7_shorts = [
        "u07_1_retraction_not_full_observation_decoding_acceptance",
        "u07_1_separation_monotone_not_history_decoding",
        "u07_1_encode_nonsurjective_not_full_decode_acceptance",
        "u02_3_finite_enumeration_not_generator_support_coverage",
        "u02_3_common_idle_and_zero_coverage_not_support_coverage",
        "u04_3_unpenalized_positive_not_penalized_minimizer_existence",
        "u04_3_unpenalized_improves_not_uniqueness",
        "u04_3_arbitrarily_small_not_intercept_coordinate_solved",
        "u05_2_bernoulli_brier_not_conditional_expectation_decomposition",
        "u05_2_selected_risk_not_simultaneous_threshold_or_rare_group",
        "u06_3_eval_exists_unique_not_interval_multiplication_enclosure",
        "u06_3_decision_respects_allowed_not_general_uncertainty_comparison",
    ]
    cand8_shorts = [
        "u03_1_relative_soundness_not_provenance_dag_to_finite_closure",
        "u03_1_computed_sound_not_dag_connected_to_executable_closure",
        "u03_1_robust_countermodel_not_connected_to_finite_closure",
        "u03_2_relative_completeness_not_verified_fuel_bound",
        "u03_2_checked_closure_complete_not_list_carrier_bound",
        "u03_2_incomplete_fuel_not_carrier_fuel_bound",
        "u07_2_common_fiber_not_semantic_compatibility",
        "u07_2_incompatible_fiber_not_layer_compatibility",
        "u01_1_fixed_class_tail_not_iid_sample_mean_specialization",
        "u01_1_approximate_erm_not_representation_risk_decomposition",
        "u01_2_label_bridge_pointwise_not_general_measurable_integration",
        "u01_2_finite_label_bridge_not_joint_bridge_budget",
    ]
    assert (
        formal_tail_text.count("theorem ")
        >= 37 + len(cand6_shorts) + len(cand7_shorts) + len(cand8_shorts)
    )
    for short in cand6_shorts:
        assert f"theorem {short}" in formal_tail_text
    import archive_gap_dispositions as disp

    prove_names = {name for names in disp.PROVE_CANDIDATES.values() for name in names}
    for short in cand7_shorts:
        assert f"theorem {short}" in formal_tail_text
        assert short in prove_names
    for short in cand8_shorts:
        assert f"theorem {short}" in formal_tail_text
        assert short not in prove_names
    for clause in ("U03.1", "U03.2", "U07.2", "U01.1", "U01.2"):
        row = by_clause[clause]
        assert row["archive_gap_status"] == "OPEN_FORMAL_TAIL"
        assert row["formal_tail_prove"]["disposition"] == "BLOCKED_NOT_IN_TIP_PIN_AUDIT"
        assert row["formal_tail_prove"]["candidate_theorems"] == []
    for clause in blocked:
        row = by_clause[clause]
        assert row["archive_gap_status"] == "OPEN_FORMAL_TAIL"
        assert row["formal_tail_prove"]["disposition"] == "BLOCKED_NOT_IN_TIP_PIN_AUDIT"
        assert row["formal_tail_prove"]["candidate_theorems"] == []
        assert row["formal_tail_prove"]["close_admitted"] is False
        assert "close_blocked_reason" not in row["formal_tail_prove"]
    cand5bis = ("U08.2", "U09.3", "U13.1", "U15.1", "U15.2")
    cand5bis_shorts = {
        "u08_2_current_singleton_does_not_exhaust_reachable",
        "u08_2_nonempty_observation_preserves_chosen_answer",
        "u09_3_greedy_prefix_misses_second_claim",
        "u09_3_same_institution_accrual_is_not_cash_effect",
        "u13_1_lawful_stat_input_change_changes_estimate",
        "u13_1_personal_update_preserves_rule_service",
        "u15_1_finite_state_strict_improve_length_bound",
        "u15_1_no_parameter_successor_has_no_fixed_point",
        "u15_1_telescoping_consumes_cumulative_improvement",
        "u15_2_key_point_regression_changes_exact_risk",
        "u15_2_finite_obs_agree_not_global",
        "u15_2_full_agreement_preserves_risk",
    }
    for clause in cand5bis:
        row = by_clause[clause]
        assert row["archive_gap_status"] == "CLOSED_BY_WIRING"
        assert row["unwired_formal_obligations"] == []
        assert str(row["scope_review"]).strip()
        assert row["formal_tail_prove"]["in_this_round"] is False
        assert row["formal_tail_prove"]["not_reopened"] is True
        assert row["formal_tail_prove"]["archive_gap_status"] == "CLOSED_BY_WIRING"
        assert row["formal_tail_prove"]["close_admitted"] is True
        assert row["formal_tail_prove"]["step_2_closed"] is False
        assert row["formal_tail_prove"]["discharges_archived_manuscript_gaps"] is False
        assert "disposition" not in row["formal_tail_prove"]
        for item in row["wired_declarations"]:
            assert "FormalTail20261024" not in item["name"]
            assert item["name"].startswith("JurisLean.Candidates.Final20261021.")
            assert item["name"].split(".")[-1] not in cand5bis_shorts
    cand6 = ("U08.3", "U15.3", "U13.2", "U09.1", "U10.2")
    for clause in cand6:
        row = by_clause[clause]
        prove = row["formal_tail_prove"]
        assert row["archive_gap_status"] == "CLOSED_BY_WIRING"
        assert row["unwired_formal_obligations"] == []
        assert "本条关项范围＝FormalTail 覆盖的形式义务" in row["scope_review"]
        assert "FormalTail20261024" in row["scope_review"]
        assert prove["in_this_round"] is False
        assert prove["not_reopened"] is True
        assert prove["archive_gap_status"] == "CLOSED_BY_WIRING"
        assert prove["close_admitted"] is True
        assert prove["step_2_closed"] is False
        assert prove["discharges_archived_manuscript_gaps"] is False
        assert "disposition" not in prove
        assert "candidate_theorems" not in prove
        for item in row["wired_declarations"]:
            assert "FormalTail20261024" not in item["name"]
            assert item["name"].startswith("JurisLean.Candidates.Final20261021.")
            assert item["name"].split(".")[-1] not in cand6_shorts
    cand7 = ("U07.1", "U02.3", "U04.3", "U05.2", "U06.3")
    for clause in cand7:
        row = by_clause[clause]
        prove = row["formal_tail_prove"]
        assert row["archive_gap_status"] == "CLOSED_BY_WIRING"
        assert row["unwired_formal_obligations"] == []
        assert "本条关项范围＝FormalTail 覆盖的形式义务" in row["scope_review"]
        assert "FormalTail20261024" in row["scope_review"]
        assert prove["in_this_round"] is False
        assert prove["not_reopened"] is True
        assert prove["archive_gap_status"] == "CLOSED_BY_WIRING"
        assert prove["close_admitted"] is True
        assert prove["step_2_closed"] is False
        assert prove["discharges_archived_manuscript_gaps"] is False
        assert "disposition" not in prove
        assert "candidate_theorems" not in prove
        for item in row["wired_declarations"]:
            assert "FormalTail20261024" not in item["name"]
            assert item["name"].startswith("JurisLean.Candidates.Final20261021.")
            assert item["name"].split(".")[-1] not in cand7_shorts
    u08_3 = by_clause["U08.3"]
    assert any("现实真值" in item for item in u08_3["non_goals"])
    assert "现实真值" in u08_3["companion_scope_notes"]
    assert "现实真值" in u08_3["scope_review"]
    u15_3 = by_clause["U15.3"]
    assert any("readback" in item for item in u15_3["non_goals"])
    assert "readback" in u15_3["companion_scope_notes"]
    assert "readback" in u15_3["scope_review"]
    u09_1 = by_clause["U09.1"]
    assert any("legal allocation" in item or "法律分配" in item for item in u09_1["non_goals"])
    assert any("法律关系" in item for item in u09_1["non_goals"])
    assert "法律关系" in u09_1["companion_scope_notes"]
    assert "法律分配" in u09_1["scope_review"] and "法律关系" in u09_1["scope_review"]
    u04_3 = by_clause["U04.3"]
    assert any("校准" in item for item in u04_3["non_goals"])
    # Live expand receipt is ci-tip-21862d9b (named_count=61). 1c72e444 stays 49.
    assert summary["formal_tail_expand_audit"]["verification"] == (
        "evidence/ci-tip-21862d9b/verification.json"
    )
    # U13.1 authority integration stays a non-goal / companion on the same row.
    u13 = by_clause["U13.1"]
    assert any("Authority integration" in item and "另证" in item for item in u13["non_goals"])
    assert "集成" in u13["companion_scope_notes"] and "另证" in u13["companion_scope_notes"]
    assert all(row["discharges_archived_manuscript_gaps"] is False for row in ledger["rows"])
    assert all(row["formal_tail_prove"]["step_2_closed"] is False for row in ledger["rows"])
    admitted = set(cand5) | set(cand5bis) | set(cand6) | set(cand7)
    assert all(
        row["formal_tail_prove"]["close_admitted"] is (row["clause"] in admitted)
        for row in ledger["rows"]
    )
    assert "OPEN_FORMAL_TAIL=20" in summary["candidate_module_quarantine"]
    assert "does not close debt" in summary["candidate_module_quarantine"]
    assert "named_count=61" in summary["candidate_module_quarantine"]
