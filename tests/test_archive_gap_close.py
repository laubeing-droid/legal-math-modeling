"""The archive-gap close layer stays fail-closed after the authorized tip-pin retarget.

The live pin is subject dc7b7430 / run 40190504653 / job 121160299567.
CAND5 (U06.4/U08.1/U10.3/U12.2/U14.2) remain CLOSED_BY_WIRING historically.
CAND5bis tip-pin expand (U08.2/U09.3/U13.1/U15.1/U15.2) under pack
tip_pin_扩审计_CAND5bis_20261025: closed_this_round=0, OPEN_FORMAL_TAIL=35,
candidate_rows=5 (audit=true, NOT CLOSED), blocked_rows=30. discharges stays false; step 2 stays open.
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
    assert "wiring 7" in proc.stdout
    assert "open_formal_tail 35" in proc.stdout
    assert "discharges false" in proc.stdout
    assert "40190504653" in proc.stdout
    assert "formal_tail_closed_this_round 0" in proc.stdout
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
    assert summary["closed_this_round"] == 0
    assert summary["open_formal_tail_remaining"] == 35
    assert summary["candidate_rows"] == 5
    assert summary["blocked_rows"] == 30
    assert summary["tip_pin_not_retargeted"] is False
    assert summary["tip_pin"]["subject"] == "dc7b7430198fa221b5d72d55fc6065a928209dc4"
    assert summary["tip_pin"]["run_id"] == 40190504653
    assert summary["tip_pin"]["job_id"] == 121160299567
    assert summary["tip_pin"]["verification"] == "evidence/ci-tip-dc7b7430/verification.json"
    assert summary["formal_tail_expand_audit"]["verification"] == (
        "evidence/ci-tip-dc7b7430/verification.json"
    )
    assert summary["formal_tail_expand_audit"]["tip_authority_run_id"] == 40190504653
    assert summary["formal_tail_expand_audit"]["live_tip_pin_retarget"] == "BOUND"
    assert summary["formal_tail_expand_audit"]["tip_authority_run_status"] == "SUCCESS"
    assert summary["formal_tail_expand_audit"]["job_id"] == 121160299567
    assert ledger["tip_pin_not_retargeted"] is False
    assert ledger["counts"]["OPEN_FORMAL_TAIL"] == 35
    assert ledger["counts"]["CLOSED_BY_WIRING"] == 7
    assert summary["later_tip_gate_not_a_close"]["run_id"] == 40063377178
    assert summary["later_tip_gate_not_a_close"]["closes_debt"] is False
    assert summary["later_tip_gate_not_a_close"]["retargets_tip_pin"] is False
    assert summary["narrow_not_reopened"] == [
        "U02.4", "U09.2", "U01.4", "U04.1", "U04.4", "U05.1", "U06.5", "U00",
    ]
    assert summary["wiring_not_reopened"] == [
        "U02.2", "U01.0", "U06.4", "U08.1", "U10.3", "U12.2", "U14.2",
    ]
    pure = by_clause["U07.1"]
    assert pure["formal_tail_prove"]["disposition"] == "BLOCKED_NOT_IN_TIP_PIN_AUDIT"
    assert pure["formal_tail_prove"]["candidate_theorems"] == []
    assert pure["formal_tail_prove"]["non_goals_same_row"] == []
    assert pure["formal_tail_prove"]["close_admitted"] is False
    # CAND5 remain CLOSED_BY_WIRING (historical); this knife closed_this_round=0.
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
        "U07.1", "U07.2", "U07.3", "U08.3", "U09.1",
        "U10.1", "U10.2", "U11.1", "U12.1", "U12.3", "U12.4",
        "U13.2", "U13.3", "U13.4", "U14.1", "U15.3",
    ]
    assert len(blocked) == 30
    for clause in blocked:
        row = by_clause[clause]
        assert row["archive_gap_status"] == "OPEN_FORMAL_TAIL"
        assert row["formal_tail_prove"]["disposition"] == "BLOCKED_NOT_IN_TIP_PIN_AUDIT"
        assert row["formal_tail_prove"]["candidate_theorems"] == []
        assert row["formal_tail_prove"]["close_admitted"] is False
        assert "close_blocked_reason" not in row["formal_tail_prove"]
    cand5bis = ("U08.2", "U09.3", "U13.1", "U15.1", "U15.2")
    for clause in cand5bis:
        row = by_clause[clause]
        assert row["archive_gap_status"] == "OPEN_FORMAL_TAIL"
        assert row["formal_tail_prove"]["disposition"] == "CANDIDATE_NOT_AUDITED"
        assert row["formal_tail_prove"]["candidate_in_tip_pin_audit"] is True
        assert row["formal_tail_prove"]["candidate_theorems"]
        assert row["formal_tail_prove"]["close_admitted"] is False
        assert row["formal_tail_prove"]["tip_pin_expand_audit"]["verification"] == "evidence/ci-tip-dc7b7430/verification.json"
        assert row["formal_tail_prove"]["tip_pin_expand_audit"]["tip_authority_run_id"] == 40190504653
        assert "close_blocked_reason" in row["formal_tail_prove"]
        assert "dc7b7430" in row["formal_tail_prove"]["blocker"]
        assert "named_count=37" in row["formal_tail_prove"]["blocker"]
    # Live expand receipt is CAND5+CAND5bis; historical f85ebe44 stays CAND5-only on disk
    assert summary["formal_tail_expand_audit"]["verification"] == (
        "evidence/ci-tip-dc7b7430/verification.json"
    )
    # U13.1 authority integration NON_GOAL on the same row
    assert any("Authority integration" in item for item in by_clause["U13.1"]["formal_tail_prove"]["non_goals_same_row"])
    assert all(row["discharges_archived_manuscript_gaps"] is False for row in ledger["rows"])
    assert all(row["formal_tail_prove"]["step_2_closed"] is False for row in ledger["rows"])
    cand5_set = {"U06.4", "U08.1", "U10.3", "U12.2", "U14.2"}
    assert all(
        row["formal_tail_prove"]["close_admitted"] is (row["clause"] in cand5_set)
        for row in ledger["rows"]
    )
