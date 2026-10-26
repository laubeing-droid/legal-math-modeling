"""The archive-gap close layer stays fail-closed after the CAND6 tip-pin expand.

The live pin is subject 1c72e444 / run 40257646857 / job 121362851074.
CAND5 and CAND5bis remain CLOSED_BY_WIRING historically (closed_this_round=5).
CAND6 (U08.3/U15.3/U13.2/U09.1/U10.2) is expand-audit only:
candidate_in_tip_pin_audit=true, disposition=CANDIDATE_NOT_AUDITED,
close_admitted=false, this expand's closed increment=0.
OPEN_FORMAL_TAIL=30, CLOSED_BY_WIRING=12, blocked_rows=25, candidate_rows=5.
discharges stays false; step 2 stays open. Historical dc7b7430 stays named_count=37.
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
    assert "wiring 12" in proc.stdout
    assert "open_formal_tail 30" in proc.stdout
    assert "discharges false" in proc.stdout
    assert "40257646857" in proc.stdout
    assert "formal_tail_closed_this_round 5" in proc.stdout
    assert "step_2_closed false" in proc.stdout


def test_u04_3_existence_stays_unproved_and_u02_4_u10_1_carry_non_goals() -> None:
    errors, ledger = checker.check(write=False)
    assert errors == []
    by_clause = {row["clause"]: row for row in ledger["rows"]}
    penalized = by_clause["U04.3"]
    assert penalized["archive_gap_status"] == "OPEN_FORMAL_TAIL"
    assert penalized["suggested_close_path"] == "证"
    assert any("UNPROVED" in item and "existence" in item.lower() for item in penalized["unwired_formal_obligations"])
    assert any("校准" in item for item in penalized["non_goals"])
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
    assert summary["open_formal_tail_remaining"] == 30
    assert summary["candidate_rows"] == 5
    assert summary["blocked_rows"] == 25
    assert summary["discharges_archived_manuscript_gaps"] is False
    assert summary["math_flip_authorized"] is False
    assert summary["close_pack"] == (
        "/home/box/shared/legal-math-reviewer/formal_tail_关≥1_CAND5bis_20261025/"
    )
    assert summary["tip_pin_not_retargeted"] is False
    assert summary["tip_pin"]["subject"] == "1c72e444ab79ff255af201f100aa6a93bdc0e5c7"
    assert summary["tip_pin"]["run_id"] == 40257646857
    assert summary["tip_pin"]["job_id"] == 121362851074
    assert summary["tip_pin"]["verification"] == "evidence/ci-tip-1c72e444/verification.json"
    assert summary["formal_tail_expand_audit"]["verification"] == (
        "evidence/ci-tip-1c72e444/verification.json"
    )
    assert summary["formal_tail_expand_audit"]["tip_authority_run_id"] == 40257646857
    assert summary["formal_tail_expand_audit"]["live_tip_pin_retarget"] == "BOUND"
    assert summary["formal_tail_expand_audit"]["tip_authority_run_status"] == "SUCCESS"
    assert summary["formal_tail_expand_audit"]["job_id"] == 121362851074
    assert summary["formal_tail_expand_audit"]["criteria_pack"] == "tip_pin_扩审计_CAND6_20261026"
    assert ledger["tip_pin_not_retargeted"] is False
    assert ledger["counts"]["OPEN_FORMAL_TAIL"] == 30
    assert ledger["counts"]["CLOSED_BY_WIRING"] == 12
    assert summary["later_tip_gate_not_a_close"]["run_id"] == 40063377178
    assert summary["later_tip_gate_not_a_close"]["closes_debt"] is False
    assert summary["later_tip_gate_not_a_close"]["retargets_tip_pin"] is False
    assert summary["narrow_not_reopened"] == [
        "U02.4", "U09.2", "U01.4", "U04.1", "U04.4", "U05.1", "U06.5", "U00",
    ]
    assert summary["wiring_not_reopened"] == [
        "U02.2", "U01.0", "U06.4", "U08.1", "U10.3", "U12.2", "U14.2",
        "U08.2", "U09.3", "U13.1", "U15.1", "U15.2",
    ]
    pure = by_clause["U07.1"]
    assert pure["formal_tail_prove"]["disposition"] == "BLOCKED_NOT_IN_TIP_PIN_AUDIT"
    assert pure["formal_tail_prove"]["candidate_theorems"] == []
    assert pure["formal_tail_prove"]["non_goals_same_row"] == []
    assert pure["formal_tail_prove"]["close_admitted"] is False
    # CAND5 remain CLOSED_BY_WIRING (historical). This knife closes CAND5bis.
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
        "U01.1", "U01.2", "U01.3", "U02.1", "U02.3", "U03.1", "U03.2",
        "U04.2", "U04.3", "U04.5", "U05.2", "U06.1", "U06.2", "U06.3",
        "U07.1", "U07.2", "U07.3",
        "U10.1", "U11.1", "U12.1", "U12.3", "U12.4",
        "U13.3", "U13.4", "U14.1",
    ]
    assert len(blocked) == 25
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
    assert formal_tail_text.count("theorem ") >= 37 + len(cand6_shorts)
    for short in cand6_shorts:
        assert f"theorem {short}" in formal_tail_text
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
    cand6_by_clause = {
        "U08.3": [
            "u08_3_four_states_do_not_exhaust_dependency_policies",
            "u08_3_judgment_not_compatibility_world_classification",
            "u08_3_opposition_preserves_support_not_full_reflection",
        ],
        "U15.3": [
            "u15_3_two_point_risks_do_not_complete_five_evidence_levels",
            "u15_3_second_round_consumer_is_not_evidence_ladder",
        ],
        "U13.2": [
            "u13_2_frames_do_not_imply_authorized_rule_load",
            "u13_2_condition_does_not_train_not_persistent_storage_refinement",
        ],
        "U09.1": [
            "u09_1_conservation_not_receipt_revision_order",
            "u09_1_receipt_coherent_not_cash_uniqueness",
            "u09_1_at_most_once_not_product_protocol_refinement",
        ],
        "U10.2": [
            "u10_2_executor_and_trace_not_full_mixed_operation_coverage",
            "u10_2_post_invariant_not_gamma_frame_or_service_refinement",
        ],
    }
    for clause in cand6:
        row = by_clause[clause]
        prove = row["formal_tail_prove"]
        assert row["archive_gap_status"] == "OPEN_FORMAL_TAIL"
        assert prove["disposition"] == "CANDIDATE_NOT_AUDITED"
        assert prove["candidate_in_tip_pin_audit"] is True
        assert prove["candidate_theorems"] == cand6_by_clause[clause]
        assert prove["close_admitted"] is False
        assert prove["step_2_closed"] is False
        assert prove["discharges_archived_manuscript_gaps"] is False
        assert prove["tip_pin_expand_audit"]["criteria_pack"] == "tip_pin_扩审计_CAND6_20261026"
        assert "CLOSED" not in prove["disposition"]
        for item in row["wired_declarations"]:
            assert "FormalTail20261024" not in item["name"]
            assert item["name"].split(".")[-1] not in cand6_shorts
    # Live expand receipt is ci-tip-1c72e444 (named_count=49). dc7b7430 stays 37.
    assert summary["formal_tail_expand_audit"]["verification"] == (
        "evidence/ci-tip-1c72e444/verification.json"
    )
    # U13.1 authority integration stays a non-goal / companion on the same row.
    u13 = by_clause["U13.1"]
    assert any("Authority integration" in item and "另证" in item for item in u13["non_goals"])
    assert "集成" in u13["companion_scope_notes"] and "另证" in u13["companion_scope_notes"]
    assert all(row["discharges_archived_manuscript_gaps"] is False for row in ledger["rows"])
    assert all(row["formal_tail_prove"]["step_2_closed"] is False for row in ledger["rows"])
    admitted = set(cand5) | set(cand5bis)
    assert all(
        row["formal_tail_prove"]["close_admitted"] is (row["clause"] in admitted)
        for row in ledger["rows"]
    )
