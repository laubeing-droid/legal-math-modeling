"""The archive-gap close layer stays fail-closed after the authorized tip-pin retarget.

The live pin is subject 27849d3f / run 40079130550 / job 120828801547.
Retargeting that pin does not close debt: discharges stays false,
OPEN_FORMAL_TAIL stays 40, and step 2 stays open.
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
    assert "wiring 2" in proc.stdout
    assert "open_formal_tail 40" in proc.stdout
    assert "discharges false" in proc.stdout
    assert "40079130550" in proc.stdout
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
    assert summary["open_formal_tail_remaining"] == 40
    assert summary["tip_pin_not_retargeted"] is False
    assert summary["tip_pin"]["subject"] == "27849d3f228ec3665da16a6aa0b801672421dca2"
    assert summary["tip_pin"]["run_id"] == 40079130550
    assert summary["tip_pin"]["job_id"] == 120828801547
    assert summary["tip_pin"]["verification"] == "evidence/ci-tip-27849d3f/verification.json"
    assert summary["formal_tail_expand_audit"]["verification"] == (
        "evidence/ci-tip-f85ebe44/verification.json"
    )
    assert summary["formal_tail_expand_audit"]["tip_authority_run_id"] == 40115638107
    assert summary["formal_tail_expand_audit"]["live_tip_pin_retarget"] == (
        "TODO_BIND_WHEN_40115638107_SUCCESS"
    )
    assert ledger["tip_pin_not_retargeted"] is False
    assert ledger["counts"]["OPEN_FORMAL_TAIL"] == 40
    assert summary["later_tip_gate_not_a_close"]["run_id"] == 40063377178
    assert summary["later_tip_gate_not_a_close"]["closes_debt"] is False
    assert summary["later_tip_gate_not_a_close"]["retargets_tip_pin"] is False
    assert summary["narrow_not_reopened"] == [
        "U02.4", "U09.2", "U01.4", "U04.1", "U04.4", "U05.1", "U06.5", "U00",
    ]
    assert summary["wiring_not_reopened"] == ["U02.2", "U01.0"]
    pure = by_clause["U07.1"]
    assert pure["formal_tail_prove"]["disposition"] == "BLOCKED_NOT_IN_TIP_PIN_AUDIT"
    assert pure["formal_tail_prove"]["candidate_theorems"] == []
    assert pure["formal_tail_prove"]["non_goals_same_row"] == []
    assert pure["formal_tail_prove"]["close_admitted"] is False
    audited_but_open = by_clause["U06.4"]
    assert audited_but_open["archive_gap_status"] == "OPEN_FORMAL_TAIL"
    assert audited_but_open["formal_tail_prove"]["disposition"] == "CANDIDATE_NOT_AUDITED"
    assert "u06_4_increasing_threshold_above_one_excludes" in (
        audited_but_open["formal_tail_prove"]["candidate_theorems"]
    )
    assert "u06_4_increasing_unit_interval_above_one_is_empty" in (
        audited_but_open["formal_tail_prove"]["candidate_theorems"]
    )
    assert audited_but_open["formal_tail_prove"]["candidate_in_tip_pin_audit"] is True
    assert audited_but_open["formal_tail_prove"]["tip_pin_expand_audit"]["verification"] == (
        "evidence/ci-tip-f85ebe44/verification.json"
    )
    assert audited_but_open["formal_tail_prove"]["close_admitted"] is False
    assert any("audited declaration" in item for item in audited_but_open["unwired_formal_obligations"])
    assert "u06_4_threshold_increasing" in "".join(
        audited_but_open["formal_tail_prove"]["uses_audited_declarations"]
    )
    late = by_clause["U08.1"]
    assert late["archive_gap_status"] == "OPEN_FORMAL_TAIL"
    assert "u08_1_mutable_current_status_disagrees_with_cutoff" in (
        late["formal_tail_prove"]["candidate_theorems"]
    )
    assert "u08_1_late_record_disguised_as_then_known_changes_applicability" in (
        late["formal_tail_prove"]["candidate_theorems"]
    )
    assert late["formal_tail_prove"]["close_admitted"] is False
    same_row = by_clause["U10.3"]
    assert same_row["archive_gap_status"] == "OPEN_FORMAL_TAIL"
    assert same_row["formal_tail_prove"]["companion_required"] is True
    assert any("公平" in item for item in same_row["formal_tail_prove"]["non_goals_same_row"])
    assert "另证" in same_row["formal_tail_prove"]["candidate_covers_only"]
    assert "公平" in same_row["formal_tail_prove"]["candidate_covers_only"]
    assert any("zero-step" in item for item in same_row["unwired_formal_obligations"])
    assert "u10_3_business_observation_faithful" in same_row["formal_tail_prove"]["candidate_theorems"]
    assert "u10_3_zero_step_prohibits_strict_progress" in (
        same_row["formal_tail_prove"]["candidate_theorems"]
    )
    assert same_row["formal_tail_prove"]["close_admitted"] is False
    damping = by_clause["U12.2"]
    assert damping["archive_gap_status"] == "OPEN_FORMAL_TAIL"
    assert "u12_2_cubic_reaches_zero_but_expands" in damping["formal_tail_prove"]["candidate_theorems"]
    assert "u12_2_one_minus_theta_oscillates" in damping["formal_tail_prove"]["candidate_theorems"]
    assert "unproved" in damping["unwired_formal_obligations"][0]
    assert damping["formal_tail_prove"]["close_admitted"] is False
    clusters = by_clause["U14.2"]
    assert clusters["archive_gap_status"] == "OPEN_FORMAL_TAIL"
    assert "u14_2_endogenous_equal_sizes_are_not_the_fixed_witness" in (
        clusters["formal_tail_prove"]["candidate_theorems"]
    )
    assert "u14_2_common_cause_copy_exceeds_independent_variance" in (
        clusters["formal_tail_prove"]["candidate_theorems"]
    )
    assert "unproved" in clusters["unwired_formal_obligations"][0]
    assert clusters["formal_tail_prove"]["close_admitted"] is False
    blocked = [
        "U01.1", "U01.2", "U01.3", "U02.1", "U02.3", "U03.1", "U03.2",
        "U04.2", "U04.3", "U04.5", "U05.2", "U06.1", "U06.2", "U06.3",
        "U07.1", "U07.2", "U07.3", "U08.2", "U08.3", "U09.1", "U09.3",
        "U10.1", "U10.2", "U11.1", "U12.1", "U12.3", "U12.4", "U13.1",
        "U13.2", "U13.3", "U13.4", "U14.1", "U15.1", "U15.2", "U15.3",
    ]
    assert len(blocked) == 35
    for clause in blocked:
        row = by_clause[clause]
        assert row["archive_gap_status"] == "OPEN_FORMAL_TAIL"
        assert row["formal_tail_prove"]["disposition"] == "BLOCKED_NOT_IN_TIP_PIN_AUDIT"
        assert row["formal_tail_prove"]["candidate_theorems"] == []
        assert row["formal_tail_prove"]["close_admitted"] is False
        assert "close_blocked_reason" not in row["formal_tail_prove"]
    assert all(row["discharges_archived_manuscript_gaps"] is False for row in ledger["rows"])
    assert all(row["formal_tail_prove"]["step_2_closed"] is False for row in ledger["rows"])
    assert all(row["formal_tail_prove"]["close_admitted"] is False for row in ledger["rows"])
