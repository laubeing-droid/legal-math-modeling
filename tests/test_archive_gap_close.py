"""The archive-gap close layer stays fail-closed after the CAND7 wiring close.

The live pin is subject 21862d9b / run 40274167574 / job 121413235107.
CAND5, CAND5bis, and CAND6 remain CLOSED_BY_WIRING historically.
This round closes CAND7 (U07.1/U02.3/U04.3/U05.2/U06.3) by wiring:
close_admitted=true, UNWIRED empty, SCOPE_REVIEW present.
The independent U03 closure retains two original residuals; the later U01
package closes three more; U04.5 closes one further original residual; the
U14.1 package names existing independent statistical validation, adaptive
conditional budgets and service-load proofs for its residual. The U07.2 and U07.3 packages bind their source-model residuals; U06.2 now binds
its mixed-payoff and fixed-tree residual to a successful changed-module audit.
CAND8's negative U07.2 declarations remain intact.
U12.3 independently binds its finite policy-learning, MAR, and sequential residual.
U11.1 independently binds the named causal bridge, original instances, and reused measurement/selection evidence.
closed_this_round=1, OPEN_FORMAL_TAIL=2, CLOSED_BY_WIRING=40, blocked_rows=2.
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
    assert "wiring 40" in proc.stdout
    assert "open_formal_tail 2" in proc.stdout
    assert "discharges false" in proc.stdout
    assert "40274167574" in proc.stdout
    assert "formal_tail_closed_this_round 1" in proc.stdout
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
    assert summary["closed_this_round"] == 1
    assert summary["open_formal_tail_remaining"] == 2
    assert summary["candidate_rows"] == 0
    assert summary["blocked_rows"] == 2
    assert summary["discharges_archived_manuscript_gaps"] is False
    assert summary["math_flip_authorized"] is False
    assert summary["step_2_closed"] is False
    assert summary["close_pack"] == checker.disp.CURRENT_CLOSE_PACK
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
    assert ledger["counts"]["OPEN_FORMAL_TAIL"] == 2
    assert ledger["counts"]["CLOSED_BY_WIRING"] == 40
    assert summary["later_tip_gate_not_a_close"]["run_id"] == 40063377178
    assert summary["later_tip_gate_not_a_close"]["closes_debt"] is False
    assert summary["later_tip_gate_not_a_close"]["retargets_tip_pin"] is False
    assert summary["narrow_not_reopened"] == [
        "U02.4", "U09.2", "U01.4", "U04.1", "U04.4", "U05.1", "U06.5", "U00",
    ]
    assert summary["wiring_not_reopened"] == [
        "U13.3",
        "U12.4",
        "U14.1",
        "U04.5",
        "U01.1", "U01.2", "U01.3",
        "U03.1", "U03.2",
        "U02.2", "U01.0", "U06.4", "U08.1", "U10.3", "U12.2", "U14.2",
        "U08.2", "U09.3", "U13.1", "U15.1", "U15.2",
        "U08.3", "U15.3", "U13.2", "U09.1", "U10.2",
        "U07.1", "U02.3", "U04.3", "U05.2", "U06.3",
        "U07.2",
        "U07.3",
        "U02.1",
        "U04.2",
        "U06.1",
        "U06.2",
        "U12.3",
        "U13.4",
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
        "U10.1", "U12.1",
    ]
    assert len(blocked) == 2
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
    # The positive U07.2 source-model close is independent of historical CAND8.
    u07 = by_clause["U07.2"]
    assert u07["archive_gap_status"] == "CLOSED_BY_WIRING"
    assert u07["independent_closure"]["receipt"] == checker.disp.U07_2_RECEIPT
    assert u07["formal_tail_prove"]["close_admitted"] is True
    assert "disposition" not in u07["formal_tail_prove"]
    assert "U07.2" not in disp.PROVE_CANDIDATES
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
    admitted = set(cand5) | set(cand5bis) | set(cand6) | set(cand7) | {"U03.1", "U03.2", "U01.1", "U01.2", "U01.3", "U04.5", "U14.1", "U13.3", "U12.4", "U07.2", "U07.3", "U02.1", "U04.2", "U06.1", "U06.2", "U12.3", "U13.4", "U11.1"}
    assert all(
        row["formal_tail_prove"]["close_admitted"] is (row["clause"] in admitted)
        for row in ledger["rows"]
    )
    assert "OPEN_FORMAL_TAIL=20" in summary["candidate_module_quarantine"]
    assert "does not close debt" in summary["candidate_module_quarantine"]
    assert "named_count=61" in summary["candidate_module_quarantine"]


def test_u03_closure_covers_only_original_residuals_with_independent_proofs():
    errors, ledger = checker.check(write=False)
    assert errors == []
    rows = {r["clause"]: r for r in ledger["rows"]}
    for clause in ("U03.1", "U03.2"):
        row = rows[clause]
        assert row["archive_gap_status"] == "CLOSED_BY_WIRING"
        assert row["unwired_formal_obligations"] == []
        assert row["formal_tail_prove"]["close_admitted"] is True
        assert row["independent_closure"]["named_theorems_full"] == checker.disp.POST_PIN_NAMES[clause]
        assert row["independent_closure"]["receipt"] == checker.disp.POST_PIN_RECEIPT
    assert ledger["formal_tail_round"]["historical_cand7_closed"] == 5
    assert ledger["formal_tail_round"]["independent_closed_ids"] == ["U03.1", "U03.2", "U01.1", "U01.2", "U01.3", "U04.5", "U14.1", "U13.3", "U12.4", "U07.2", "U07.3", "U02.1", "U04.2", "U06.1", "U06.2", "U12.3", "U13.4", "U11.1"]
    assert ledger["formal_tail_round"]["historical_u03_closed"] == 2


def test_u03_close_rejects_missing_proof_changed_scope_and_changed_sources():
    import copy
    receipt = checker.load_json(ROOT / checker.disp.POST_PIN_RECEIPT)
    raw = (ROOT / checker.disp.POST_PIN_CLOSE_PACK / "axiom-audit.raw.txt").read_text(encoding="utf-8")
    assert checker.independent_close_errors(receipt, raw) == []
    mutations = [
        lambda r: r["closed_ids"].append("U07.2"),
        lambda r: r["names_by_clause"]["U03.2"].pop(),
        lambda r: r["original_residuals"].update({"U03.2": "a weaker replacement"}),
        lambda r: r["sources"][0].update({"sha256": "0" * 64}),
        lambda r: r["sources"].pop(),
        lambda r: r.update(job_conclusion="failure"),
        lambda r: r["tip_pin"].update({"subject": "0" * 40}),
    ]
    for mutate in mutations:
        changed = copy.deepcopy(receipt)
        mutate(changed)
        assert checker.independent_close_errors(changed, raw)
    assert checker.independent_close_errors(receipt, raw.replace("depends on axioms", "audit omitted", 1))


def test_u01_close_uses_general_theorems_and_keeps_u03_evidence():
    errors, ledger = checker.check(write=False)
    assert errors == []
    rows = {r["clause"]: r for r in ledger["rows"]}
    for clause in ("U01.1", "U01.2", "U01.3"):
        row = rows[clause]
        assert row["archive_gap_status"] == "CLOSED_BY_WIRING"
        assert row["unwired_formal_obligations"] == []
        assert row["formal_tail_prove"]["close_admitted"] is True
        assert row["independent_closure"] == {
            "receipt": checker.disp.U01_RECEIPT,
            "named_theorems_full": checker.disp.U01_NAMES[clause],
        }
    summary = ledger["formal_tail_round"]
    assert summary["independent_closed_total"] == 18
    assert summary["independent_receipts"] == [checker.disp.POST_PIN_RECEIPT, checker.disp.U01_RECEIPT, checker.disp.U04_5_RECEIPT, checker.disp.U14_1_RECEIPT, checker.disp.U13_3_RECEIPT, checker.disp.U12_4_RECEIPT, checker.disp.U07_2_RECEIPT, checker.disp.U07_3_RECEIPT, checker.disp.U02_1_RECEIPT, checker.disp.U04_2_RECEIPT, checker.disp.U06_1_RECEIPT, checker.disp.U06_2_RECEIPT, checker.disp.U12_3_RECEIPT, checker.disp.U13_4_RECEIPT, checker.disp.U11_1_RECEIPT]
    import copy
    pack = checker.disp.INDEPENDENT_CLOSE_PACKS[1]
    receipt = checker.load_json(ROOT / pack["receipt"])
    raw = (ROOT / pack["pack"] / "axiom-audit.raw.txt").read_text(encoding="utf-8")
    assert checker.independent_close_errors(receipt, raw, pack) == []
    for mutate in (
        lambda r: r["closed_ids"].append("U07.2"),
        lambda r: r["names_by_clause"]["U01.3"].pop(),
        lambda r: r["original_residuals"].update({"U01.3": "finite support only"}),
        lambda r: r["sources"][0].update({"sha256": "0" * 64}),
        lambda r: r["sources"].pop(),
        lambda r: r.update(open_before=20),
        lambda r: r.update(job_conclusion="failure"),
        lambda r: r["tip_pin"].update({"subject": "0" * 40}),
    ):
        changed = copy.deepcopy(receipt)
        mutate(changed)
        assert checker.independent_close_errors(changed, raw, pack)
    assert checker.independent_close_errors(receipt, raw.replace("depends on axioms", "audit omitted", 1), pack)


def test_u14_1_close_names_validation_budget_and_load_proofs():
    import copy
    errors, ledger = checker.check(write=False)
    assert errors == []
    row = next(r for r in ledger["rows"] if r["clause"] == "U14.1")
    assert row["archive_gap_status"] == "CLOSED_BY_WIRING"
    assert row["independent_closure"] == {
        "receipt": checker.disp.U14_1_RECEIPT,
        "named_theorems_full": checker.disp.U14_1_NAMES["U14.1"],
    }
    assert row["remaining_after_close"] == "WIRED_TO_INDEPENDENT_U14_1_PROOFS"
    pack = checker.disp.INDEPENDENT_CLOSE_PACKS[3]
    receipt = checker.load_json(ROOT / pack["receipt"])
    raw = (ROOT / pack["pack"] / "axiom-audit.raw.txt").read_text(encoding="utf-8")
    assert checker.independent_close_errors(receipt, raw, pack) == []
    assert receipt["named_count"] == 15
    assert (receipt["open_before"], receipt["open_after"]) == (14, 13)
    for mutate in (
        lambda r: r["closed_ids"].append("U07.2"),
        lambda r: r["original_residuals"].update({"U14.1": "acceptance algebra only"}),
        lambda r: r["names_by_clause"]["U14.1"].pop(),
        lambda r: r["sources"][0].update({"sha256": "0" * 64}),
        lambda r: r.update(job_conclusion="failure"),
        lambda r: r["tip_pin"].update({"subject": "0" * 40}),
    ):
        changed = copy.deepcopy(receipt)
        mutate(changed)
        assert checker.independent_close_errors(changed, raw, pack)
    assert checker.independent_close_errors(receipt, raw.replace("depends on axioms", "audit omitted", 1), pack)


def test_u13_3_close_binds_exact_ci_receipt_and_preserves_other_open_rows():
    import copy
    errors, ledger = checker.check(write=False)
    assert errors == []
    row = next(r for r in ledger["rows"] if r["clause"] == "U13.3")
    assert row["archive_gap_status"] == "CLOSED_BY_WIRING"
    assert row["independent_closure"] == {
        "receipt": checker.disp.U13_3_RECEIPT,
        "named_theorems_full": checker.disp.U13_3_NAMES["U13.3"],
    }
    assert row["remaining_after_close"].startswith("WIRED_TO_INDEPENDENT_U13_3_PROOFS")
    assert row["formal_tail_prove"]["step_2_closed"] is False
    assert row["formal_tail_prove"]["discharges_archived_manuscript_gaps"] is False
    pack = checker.disp.INDEPENDENT_CLOSE_PACKS[4]
    receipt = checker.load_json(ROOT / pack["receipt"])
    raw = (ROOT / pack["pack"] / "axiom-audit.raw.txt").read_text(encoding="utf-8")
    assert checker.independent_close_errors(receipt, raw, pack) == []
    assert receipt["named_count"] == 6
    assert receipt["subject"] == "c4baf6d1dcf81a53cbf1e58abf87e18e4c500711"
    assert (receipt["open_before"], receipt["open_after"]) == (13, 12)
    assert receipt["axiom_audit"]["audited_targets"] == 6
    assert ledger["discharges_archived_manuscript_gaps"] is False
    assert ledger["formal_tail_round"]["step_2_closed"] is False
    for mutate in (
        lambda r: r["closed_ids"].append("U07.2"),
        lambda r: r["original_residuals"].update({"U13.3": "risk identity only"}),
        lambda r: r["names_by_clause"]["U13.3"].pop(),
        lambda r: r["sources"].pop(),
        lambda r: r.update(open_after=13),
        lambda r: r.update(job_conclusion="failure"),
        lambda r: r["tip_pin"].update({"subject": "0" * 40}),
    ):
        changed = copy.deepcopy(receipt)
        mutate(changed)
        assert checker.independent_close_errors(changed, raw, pack)
    assert checker.independent_close_errors(receipt, raw.replace("depends on axioms", "audit omitted", 1), pack)


def test_u12_4_close_binds_full_frozen_audit_model_acceptance():
    import copy
    errors, ledger = checker.check(write=False)
    assert errors == []
    row = next(r for r in ledger["rows"] if r["clause"] == "U12.4")
    assert row["archive_gap_status"] == "CLOSED_BY_WIRING"
    assert row["independent_closure"] == {
        "receipt": checker.disp.U12_4_RECEIPT,
        "named_theorems_full": checker.disp.U12_4_NAMES["U12.4"],
    }
    assert row["remaining_after_close"].startswith("WIRED_TO_INDEPENDENT_U12_4_PROOFS")
    assert any("真实成本" in item and "偏好" in item and "审计合法性" in item for item in row["non_goals"])
    assert row["formal_tail_prove"]["close_admitted"] is True
    pack = checker.disp.INDEPENDENT_CLOSE_PACKS[5]
    receipt = checker.load_json(ROOT / pack["receipt"])
    raw = (ROOT / pack["pack"] / "axiom-audit.raw.txt").read_text(encoding="utf-8")
    assert checker.independent_close_errors(receipt, raw, pack) == []
    assert receipt["named_count"] == 5
    assert (receipt["open_before"], receipt["open_after"]) == (12, 11)
    assert receipt["subject"] == "845163f918573c17d89be3def6eff2bfd316a18f"
    assert receipt["axiom_audit"]["audited_targets"] == 5
    assert receipt["original_residuals"]["U12.4"] == (
        "Two incentive inequalities and distinguishability counterexample present; verify full frozen model acceptance in CI."
    )
    assert ledger["discharges_archived_manuscript_gaps"] is False
    assert ledger["math_flip_authorized"] is False
    assert ledger["formal_tail_round"]["step_2_closed"] is False
    for mutate in (
        lambda r: r["closed_ids"].append("U07.2"),
        lambda r: r["original_residuals"].update({"U12.4": "inequalities only"}),
        lambda r: r["names_by_clause"]["U12.4"].pop(),
        lambda r: r["sources"].pop(),
        lambda r: r.update(open_after=12),
        lambda r: r.update(job_conclusion="failure"),
        lambda r: r["tip_pin"].update({"subject": "0" * 40}),
    ):
        changed = copy.deepcopy(receipt)
        mutate(changed)
        assert checker.independent_close_errors(changed, raw, pack)
    assert checker.independent_close_errors(receipt, raw.replace("depends on axioms", "audit omitted", 1), pack)


def test_u07_2_positive_joint_object_close_is_separate_from_cand8_negatives():
    import copy
    errors, ledger = checker.check(write=False)
    assert errors == []
    row = next(r for r in ledger["rows"] if r["clause"] == "U07.2")
    assert row["archive_gap_status"] == "CLOSED_BY_WIRING"
    assert row["unwired_formal_obligations"] == []
    assert row["independent_closure"] == {
        "receipt": checker.disp.U07_2_RECEIPT,
        "named_theorems_full": checker.disp.U07_2_NAMES["U07.2"],
    }
    assert row["remaining_after_close"].startswith("WIRED_TO_INDEPENDENT_U07_2_PROOFS")
    assert any("conditional" in item and "real-source" in item for item in row["non_goals"])
    assert "for an actually accepted sourceModel output" in row["scope_review"]
    assert row["formal_tail_prove"]["close_admitted"] is True
    assert "candidate_theorems" not in row["formal_tail_prove"]
    pack = checker.disp.INDEPENDENT_CLOSE_PACKS[6]
    receipt = checker.load_json(ROOT / pack["receipt"])
    raw = (ROOT / pack["pack"] / "axiom-audit.raw.txt").read_text(encoding="utf-8")
    assert checker.independent_close_errors(receipt, raw, pack) == []
    assert receipt["named_count"] == 7
    assert receipt["subject"] == "0d1146372e5b7101b192eb21a1eaf2a9ee2792ad"
    assert receipt["run_id"] == 40743855261
    assert receipt["job_id"] == 123012322952
    assert (receipt["open_before"], receipt["open_after"]) == (11, 10)
    assert receipt["axiom_audit"]["audited_targets"] == 7
    assert receipt["axiom_audit"]["targets_with_sorryAx"] == {}
    assert receipt["axiom_audit"]["targets_outside_standard_axioms"] == {}
    assert receipt["original_residuals"]["U07.2"] == (
        "Fresh CI and actual semantic compatibility of supplied layers remain separate."
    )
    assert "u07_2_common_fiber_not_semantic_compatibility" not in {
        name for names in checker.disp.PROVE_CANDIDATES.values() for name in names
    }
    assert "u07_2_incompatible_fiber_not_layer_compatibility" not in {
        name for names in checker.disp.PROVE_CANDIDATES.values() for name in names
    }
    assert checker.disp.FORMAL_TAIL_CAND8_PACK
    assert ledger["formal_tail_round"]["independent_closed_total"] == 18
    assert ledger["formal_tail_round"]["open_formal_tail_remaining"] == 2
    assert ledger["discharges_archived_manuscript_gaps"] is False
    assert ledger["math_flip_authorized"] is False
    assert ledger["formal_tail_round"]["step_2_closed"] is False
    for mutate in (
        lambda r: r["original_residuals"].update({"U07.2": "arbitrary layers are compatible"}),
        lambda r: r["names_by_clause"]["U07.2"].pop(),
        lambda r: r["sources"].pop(),
        lambda r: r.update(open_after=11),
        lambda r: r.update(job_conclusion="failure"),
        lambda r: r["tip_pin"].update({"subject": "0" * 40}),
    ):
        changed = copy.deepcopy(receipt)
        mutate(changed)
        assert checker.independent_close_errors(changed, raw, pack)
    assert checker.independent_close_errors(receipt, raw.replace("depends on axioms", "audit omitted", 1), pack)


def test_u07_3_selected_row_semantics_close_keeps_o05_and_pipeline_open():
    import copy

    errors, ledger = checker.check(write=False)
    assert errors == []
    row = next(r for r in ledger["rows"] if r["clause"] == "U07.3")
    assert row["archive_gap_status"] == "CLOSED_BY_WIRING"
    assert row["unwired_formal_obligations"] == []
    assert row["independent_closure"] == {
        "receipt": checker.disp.U07_3_RECEIPT,
        "named_theorems_full": checker.disp.U07_3_NAMES["U07.3"],
    }
    assert row["remaining_after_close"].startswith("WIRED_TO_INDEPENDENT_U07_3_PROOFS")
    assert row["formal_tail_prove"]["close_admitted"] is True
    assert any("O05" in item and "raw material" in item for item in row["non_goals"])
    assert "does not quantify" in row["scope_review"]
    assert "old Final20261021.Pipeline" in row["scope_review"]
    assert row["scope_review"]

    pack = checker.disp.INDEPENDENT_CLOSE_PACKS[7]
    receipt = checker.load_json(ROOT / pack["receipt"])
    raw = (ROOT / pack["pack"] / "axiom-audit.raw.txt").read_text(encoding="utf-8")
    assert checker.independent_close_errors(receipt, raw, pack) == []
    assert receipt["named_count"] == 12
    assert receipt["subject"] == "4b88591bb4f48712adb54c1b40557f0ebcd0c23b"
    assert receipt["run_id"] == 40771310113
    assert receipt["job_id"] == 123108948361
    assert receipt["artifact_id"] == 12853086110
    assert receipt["artifact_sha256"] == "49f4af9fc0a0614dc4a1a05f4157eee3ac000342ff20006e213590b392a735cc"
    assert (receipt["open_before"], receipt["open_after"]) == (10, 9)
    assert receipt["axiom_audit"]["audited_targets"] == 12
    assert receipt["axiom_audit"]["targets_with_sorryAx"] == {}
    assert receipt["axiom_audit"]["targets_outside_standard_axioms"] == {}
    assert receipt["original_residuals"]["U07.3"] == (
        "Fresh CI; source truth and arbitrary extractor fidelity are not proved by the fixed-history construction."
    )
    assert len(receipt["sources"]) == 5
    assert ledger["formal_tail_round"]["independent_closed_total"] == 18
    assert ledger["formal_tail_round"]["open_formal_tail_remaining"] == 2
    assert ledger["discharges_archived_manuscript_gaps"] is False
    assert ledger["math_flip_authorized"] is False
    assert ledger["formal_tail_round"]["step_2_closed"] is False
    for mutate in (
        lambda r: r["original_residuals"].update({"U07.3": "fixed binding only"}),
        lambda r: r["names_by_clause"]["U07.3"].pop(),
        lambda r: r["sources"].pop(),
        lambda r: r.update(open_after=10),
        lambda r: r.update(job_conclusion="failure"),
        lambda r: r["tip_pin"].update({"subject": "0" * 40}),
    ):
        changed = copy.deepcopy(receipt)
        mutate(changed)
        assert checker.independent_close_errors(changed, raw, pack)
    assert checker.independent_close_errors(receipt, raw.replace("depends on axioms", "audit omitted", 1), pack)



def test_u02_1_close_binds_actual_pipeline_refinement_and_preserves_scope():
    import copy

    errors, ledger = checker.check(write=False)
    assert errors == []
    row = next(r for r in ledger["rows"] if r["clause"] == "U02.1")
    assert row["archive_gap_status"] == "CLOSED_BY_WIRING"
    assert row["unwired_formal_obligations"] == []
    assert row["independent_closure"] == {
        "receipt": checker.disp.U02_1_RECEIPT,
        "named_theorems_full": checker.disp.U02_1_NAMES["U02.1"],
    }
    assert row["remaining_after_close"].startswith("WIRED_TO_INDEPENDENT_U02_1_PROOFS")
    assert row["formal_tail_prove"]["close_admitted"] is True
    assert "d0" in row["scope_review"]
    assert "real-world permission domain" in row["scope_review"]
    assert ledger["discharges_archived_manuscript_gaps"] is False
    assert ledger["math_flip_authorized"] is False
    assert ledger["formal_tail_round"]["step_2_closed"] is False
    assert ledger["formal_tail_round"]["independent_closed_total"] == 18
    assert ledger["formal_tail_round"]["open_formal_tail_remaining"] == 2

    pack = next(p for p in checker.disp.INDEPENDENT_CLOSE_PACKS if p["pack"] == checker.disp.U02_1_CLOSE_PACK)
    receipt = checker.load_json(ROOT / pack["receipt"])
    raw = (ROOT / pack["pack"] / "axiom-audit.raw.txt").read_text(encoding="utf-8")
    assert checker.independent_close_errors(receipt, raw, pack) == []
    assert receipt["named_count"] == 12
    assert receipt["subject"] == "1bd8db47b728249fe240312fc5e570ce7290b62a"
    assert receipt["run_id"] == 40791067212
    assert receipt["job_id"] == 123176137083
    assert receipt["artifact_id"] == 12861283251
    assert receipt["artifact_sha256"] == "20cbbe172c3bc787c6daf13f479612eb010bc006fb3148e87b2fdc9b603f2152"
    assert (receipt["open_before"], receipt["open_after"]) == (9, 8)
    assert receipt["axiom_audit"]["targets_with_sorryAx"] == {}
    assert receipt["axiom_audit"]["targets_outside_standard_axioms"] == {}
    assert receipt["original_residuals"]["U02.1"] == (
        "Actual-world and actual-successor refinement of the concrete pipeline table remains unproved."
    )
    assert len(receipt["sources"]) == 5

    for mutate in (
        lambda r: r.update(open_after=9),
        lambda r: r["names_by_clause"]["U02.1"].pop(),
        lambda r: r["original_residuals"].update({"U02.1": "real legal permission is proved"}),
        lambda r: r["sources"].pop(),
        lambda r: r["axiom_audit"].update({"targets_with_sorryAx": {"fake": ["sorryAx"]}}),
    ):
        changed = copy.deepcopy(receipt)
        mutate(changed)
        assert checker.independent_close_errors(changed, raw, pack)
    assert checker.independent_close_errors(receipt, raw.replace("depends on axioms", "audit omitted", 1), pack)


def test_u04_5_close_requires_general_likelihood_and_copy_information():
    import copy
    errors, ledger = checker.check(write=False)
    assert errors == []
    row = next(r for r in ledger["rows"] if r["clause"] == "U04.5")
    assert row["archive_gap_status"] == "CLOSED_BY_WIRING"
    assert row["independent_closure"] == {
        "receipt": checker.disp.U04_5_RECEIPT,
        "named_theorems_full": checker.disp.U04_5_NAMES["U04.5"],
    }
    pack = checker.disp.INDEPENDENT_CLOSE_PACKS[2]
    receipt = checker.load_json(ROOT / pack["receipt"])
    raw = (ROOT / pack["pack"] / "axiom-audit.raw.txt").read_text(encoding="utf-8")
    assert checker.independent_close_errors(receipt, raw, pack) == []
    assert receipt["named_count"] == 9
    assert (receipt["open_before"], receipt["open_after"]) == (15, 14)
    changed = copy.deepcopy(receipt)
    changed["original_residuals"]["U04.5"] = "LR16/LR4 arithmetic only"
    assert checker.independent_close_errors(changed, raw, pack)
    changed = copy.deepcopy(receipt)
    changed["names_by_clause"]["U04.5"].pop()
    assert checker.independent_close_errors(changed, raw, pack)



def test_u04_2_close_binds_frozen_probability_residual_and_keeps_adjacent_scope():
    import copy

    errors, ledger = checker.check(write=False)
    assert errors == []
    row = next(r for r in ledger["rows"] if r["clause"] == "U04.2")
    assert row["archive_gap_status"] == "CLOSED_BY_WIRING"
    assert row["unwired_formal_obligations"] == []
    assert row["independent_closure"] == {
        "receipt": checker.disp.U04_2_RECEIPT,
        "named_theorems_full": checker.disp.U04_2_NAMES["U04.2"],
    }
    assert row["remaining_after_close"].startswith("WIRED_TO_INDEPENDENT_U04_2_PROOFS")
    assert "04.4" in row["scope_review"]
    assert "U11.1" in row["scope_review"]
    assert "edge 6" in row["scope_review"]
    assert ledger["counts"]["OPEN_FORMAL_TAIL"] == 2
    assert ledger["counts"]["CLOSED_BY_WIRING"] == 40
    assert ledger["discharges_archived_manuscript_gaps"] is False
    assert ledger["math_flip_authorized"] is False
    assert ledger["formal_tail_round"]["step_2_closed"] is False
    assert ledger["formal_tail_round"]["independent_closed_total"] == 18
    assert ledger["formal_tail_round"]["open_formal_tail_remaining"] == 2

    pack = next(p for p in checker.disp.INDEPENDENT_CLOSE_PACKS if p["pack"] == checker.disp.U04_2_CLOSE_PACK)
    receipt = checker.load_json(ROOT / pack["receipt"])
    raw = (ROOT / pack["pack"] / "axiom-audit.raw.txt").read_text(encoding="utf-8")
    assert checker.independent_close_errors(receipt, raw, pack) == []
    assert receipt["named_count"] == 15
    assert receipt["subject"] == "5c8cf787c1d545a0ab1e037fa793d8f6417b886e"
    assert receipt["run_id"] == 40879691794
    assert receipt["job_id"] == 123467594841
    assert receipt["artifact_id"] == 12899702798
    assert receipt["artifact_sha256"] == "1187cd23da95b79f3ffbdf90c64f99588063009dace4b6bf886ab273621c1cc2"
    assert (receipt["open_before"], receipt["open_after"]) == (8, 7)
    assert receipt["axiom_audit"]["targets_with_sorryAx"] == {}
    assert receipt["axiom_audit"]["targets_outside_standard_axioms"] == {}
    assert receipt["original_residuals"]["U04.2"] == (
        "Real ratio enclosure present; width, beta integrals, three-event sharp identified set and contamination subclaims remain."
    )
    assert len(receipt["sources"]) == 3

    for mutate in (
        lambda r: r.update(open_after=8),
        lambda r: r["names_by_clause"]["U04.2"].pop(),
        lambda r: r["original_residuals"].update({"U04.2": "all original questions are closed"}),
        lambda r: r["sources"].pop(),
        lambda r: r["axiom_audit"].update({"targets_with_sorryAx": {"fake": ["sorryAx"]}}),
        lambda r: r.update(run_id=r["run_id"] + 1),
        lambda r: r.update(artifact_sha256="0" * 64),
    ):
        changed = copy.deepcopy(receipt)
        mutate(changed)
        assert checker.independent_close_errors(changed, raw, pack)
    assert checker.independent_close_errors(receipt, raw.replace("depends on axioms", "audit omitted", 1), pack)
    assert checker.independent_close_errors(receipt, raw.replace(
        "JurisLean.Candidates.U04_2SharpConditioning20261029.beta_two_three_half",
        "beta_two_three_half", 1), pack)


def test_u06_1_close_binds_finite_bellman_and_actual_trajectory_evidence():
    import copy

    errors, ledger = checker.check(write=False)
    assert errors == []
    row = next(r for r in ledger["rows"] if r["clause"] == "U06.1")
    assert row["archive_gap_status"] == "CLOSED_BY_WIRING"
    assert row["unwired_formal_obligations"] == []
    assert row["independent_closure"] == {
        "receipt": checker.disp.U06_1_RECEIPT,
        "named_theorems_full": checker.disp.U06_1_NAMES["U06.1"],
    }
    assert row["remaining_after_close"].startswith("WIRED_TO_INDEPENDENT_U06_1_PROOFS")
    assert "common feasible" in row["scope_review"]
    assert "old Pipeline" in row["scope_review"]
    assert "terminal branch with value g(s)" in row["scope_review"]
    assert ledger["counts"]["CLOSED_BY_NARROW"] == 8
    assert ledger["counts"]["CLOSED_BY_WIRING"] == 40
    assert ledger["counts"]["OPEN_FORMAL_TAIL"] == 2
    assert ledger["discharges_archived_manuscript_gaps"] is False
    assert ledger["math_flip_authorized"] is False
    assert ledger["formal_tail_round"]["step_2_closed"] is False
    assert ledger["formal_tail_round"]["independent_closed_total"] == 18
    assert ledger["formal_tail_round"]["open_formal_tail_remaining"] == 2
    assert ledger["formal_tail_round"]["tip_pin"] == checker.disp.TIP_PIN

    pack = next(p for p in checker.disp.INDEPENDENT_CLOSE_PACKS if p["pack"] == checker.disp.U06_1_CLOSE_PACK)
    receipt = checker.load_json(ROOT / pack["receipt"])
    raw = (ROOT / pack["pack"] / "axiom-audit.raw.txt").read_text(encoding="utf-8")
    assert checker.independent_close_errors(receipt, raw, pack) == []
    assert receipt["named_count"] == 14
    assert receipt["subject"] == "8340ffa6d88138b89ec9083253414d8b69e96803"
    assert receipt["run_id"] == 40919387762
    assert receipt["job_id"] == 123608188128
    assert receipt["artifact_id"] == 12917367581
    assert receipt["artifact_sha256"] == "aaf0f038397ded7d503a055245d4921d686af680d9bf7751418ad18af0b553b8"
    assert (receipt["open_before"], receipt["open_after"]) == (7, 6)
    assert receipt["axiom_audit"]["audited_targets"] == 14
    assert receipt["axiom_audit"]["targets_with_sorryAx"] == {}
    assert receipt["axiom_audit"]["targets_outside_standard_axioms"] == {}
    assert receipt["original_residuals"]["U06.1"] == (
        "Finite free-information comparison present; full Bellman optimum, blocked terminal convention and nonrectangular counterexample remain."
    )
    assert len(receipt["sources"]) == 2
    for mutate in (
        lambda r: r.update(run_id=40918716098),
        lambda r: r.update(artifact_sha256="0" * 64),
        lambda r: r["names_by_clause"]["U06.1"].pop(),
        lambda r: r.update(open_after=7),
        lambda r: r["sources"].pop(),
        lambda r: r["axiom_audit"].update({"targets_with_sorryAx": {"fake": ["sorryAx"]}}),
    ):
        changed = copy.deepcopy(receipt)
        mutate(changed)
        assert checker.independent_close_errors(changed, raw, pack)
    assert checker.independent_close_errors(receipt, raw.replace("depends on axioms", "audit omitted", 1), pack)


def test_u06_2_close_binds_mixed_transfer_and_fixed_tree_bridge():
    import copy

    errors, ledger = checker.check(write=False)
    assert errors == []
    row = next(r for r in ledger["rows"] if r["clause"] == "U06.2")
    assert row["archive_gap_status"] == "CLOSED_BY_WIRING"
    assert row["unwired_formal_obligations"] == []
    assert row["independent_closure"] == {
        "receipt": checker.disp.U06_2_RECEIPT,
        "named_theorems_full": checker.disp.U06_2_NAMES["U06.2"],
    }
    assert row["remaining_after_close"].startswith("WIRED_TO_INDEPENDENT_U06_2_PROOFS")
    assert "general mixed-equilibrium existence" in row["scope_review"]
    assert "06.7" in row["scope_review"]
    assert ledger["counts"]["CLOSED_BY_NARROW"] == 8
    assert ledger["counts"]["CLOSED_BY_WIRING"] == 40
    assert ledger["counts"]["OPEN_FORMAL_TAIL"] == 2
    assert ledger["discharges_archived_manuscript_gaps"] is False
    assert ledger["math_flip_authorized"] is False
    assert ledger["formal_tail_round"]["step_2_closed"] is False
    assert ledger["formal_tail_round"]["independent_closed_total"] == 18
    assert ledger["formal_tail_round"]["open_formal_tail_remaining"] == 2

    pack = next(p for p in checker.disp.INDEPENDENT_CLOSE_PACKS if p["pack"] == checker.disp.U06_2_CLOSE_PACK)
    receipt = checker.load_json(ROOT / pack["receipt"])
    raw = (ROOT / pack["pack"] / "axiom-audit.raw.txt").read_text(encoding="utf-8")
    assert checker.independent_close_errors(receipt, raw, pack) == []
    assert receipt["named_count"] == 32
    assert receipt["subject"] == "fe9e4b689d317e75d91415ea65d701583a205929"
    assert receipt["run_id"] == 40939134896
    assert receipt["job_id"] == 123677528713
    assert receipt["artifact_id"] == 12925329796
    assert receipt["artifact_sha256"] == "46591a17cd3591eccbd2ffc912718b10b538f159a9c05f32bea2762905bd820e"
    assert (receipt["open_before"], receipt["open_after"]) == (6, 5)
    assert receipt["axiom_audit"]["audited_targets"] == 32
    assert receipt["axiom_audit"]["targets_with_sorryAx"] == {}
    assert receipt["axiom_audit"]["targets_outside_standard_axioms"] == {}
    assert receipt["original_residuals"]["U06.2"] == (
        "Universal allowed-deviation real payoff transfer present; mixed expectations and explicit strategy/tree bridge remain."
    )
    assert len(receipt["sources"]) == 4
    for mutate in (
        lambda r: r.update(run_id=40934394264),
        lambda r: r.update(artifact_sha256="0" * 64),
        lambda r: r["names_by_clause"]["U06.2"].pop(),
        lambda r: r.update(open_after=6),
        lambda r: r["sources"].pop(),
        lambda r: r["axiom_audit"].update({"targets_with_sorryAx": {"fake": ["sorryAx"]}}),
    ):
        changed = copy.deepcopy(receipt)
        mutate(changed)
        assert checker.independent_close_errors(changed, raw, pack)
    assert checker.independent_close_errors(receipt, raw.replace("depends on axioms", "audit omitted", 1), pack)


def test_u12_3_close_binds_policy_learning_mar_and_finite_sequential_transport():
    import copy

    errors, ledger = checker.check(write=False)
    assert errors == []
    row = next(r for r in ledger["rows"] if r["clause"] == "U12.3")
    assert row["archive_gap_status"] == "CLOSED_BY_WIRING"
    assert row["unwired_formal_obligations"] == []
    assert row["independent_closure"] == {
        "receipt": checker.disp.U12_3_RECEIPT,
        "named_theorems_full": checker.disp.U12_3_NAMES["U12.3"],
    }
    assert row["remaining_after_close"].startswith("WIRED_TO_INDEPENDENT_U12_3_PROOFS")
    assert "None is abstention" in row["scope_review"]
    assert "old Pipeline numeric consumer" in row["scope_review"]
    assert "not an infinite-horizon RL theorem" in row["scope_review"]
    assert ledger["counts"]["CLOSED_BY_NARROW"] == 8
    assert ledger["counts"]["CLOSED_BY_WIRING"] == 40
    assert ledger["counts"]["OPEN_FORMAL_TAIL"] == 2
    assert ledger["discharges_archived_manuscript_gaps"] is False
    assert ledger["math_flip_authorized"] is False
    assert ledger["formal_tail_round"]["step_2_closed"] is False
    assert ledger["formal_tail_round"]["independent_closed_total"] == 18
    assert ledger["formal_tail_round"]["open_formal_tail_remaining"] == 2
    assert ledger["formal_tail_round"]["tip_pin"] == checker.disp.TIP_PIN

    pack = next(p for p in checker.disp.INDEPENDENT_CLOSE_PACKS if p["pack"] == checker.disp.U12_3_CLOSE_PACK)
    receipt = checker.load_json(ROOT / pack["receipt"])
    raw = (ROOT / pack["pack"] / "axiom-audit.raw.txt").read_text(encoding="utf-8")
    assert checker.independent_close_errors(receipt, raw, pack) == []
    assert receipt["named_count"] == 34
    assert receipt["subject"] == "935b1bd8420c9433c9918d53d935b0948bf51089"
    assert receipt["run_id"] == 40964036223
    assert receipt["job_id"] == 123763838851
    assert receipt["artifact_id"] == 12937870526
    assert receipt["artifact_sha256"] == "dd8a379bec390cfc92478ea5a652f57e4ffb42f049a41d94758fa16bab82a77e"
    assert (receipt["open_before"], receipt["open_after"]) == (5, 4)
    assert receipt["axiom_audit"]["audited_targets"] == 34
    assert receipt["axiom_audit"]["targets_with_sorryAx"] == {}
    assert receipt["axiom_audit"]["targets_outside_standard_axioms"] == {}
    assert "JurisLean.Candidates.U12_3MeasuredPolicyBridge20261030.zero_bound_policy_scores_and_regret" in receipt["names_by_clause"]["U12.3"]
    assert receipt["original_residuals"]["U12.3"] == (
        "Clipping identity only; weighted uniform selection, MAR and full sequential-kernel likelihood-ratio theorem remain UNPROVED."
    )
    assert len(receipt["sources"]) == 10
    for mutate in (
        lambda r: r.update(run_id=40955915098),
        lambda r: r.update(artifact_sha256="0" * 64),
        lambda r: r["names_by_clause"]["U12.3"].pop(),
        lambda r: r.update(open_after=5),
        lambda r: r["sources"].pop(),
        lambda r: r["axiom_audit"].update({"targets_with_sorryAx": {"fake": ["sorryAx"]}}),
    ):
        changed = copy.deepcopy(receipt)
        mutate(changed)
        assert checker.independent_close_errors(changed, raw, pack)
    assert checker.independent_close_errors(receipt, raw.replace("depends on axioms", "audit omitted", 1), pack)


def test_u13_4_close_binds_fallback_selection_and_conditional_risk():
    errors, ledger = checker.check(write=False)
    assert errors == []
    row = next(r for r in ledger["rows"] if r["clause"] == "U13.4")
    assert row["archive_gap_status"] == "CLOSED_BY_WIRING"
    assert row["unwired_formal_obligations"] == []
    assert row["independent_closure"] == {
        "receipt": checker.disp.U13_4_RECEIPT,
        "named_theorems_full": checker.disp.U13_4_NAMES["U13.4"],
    }
    assert "conditional population-risk bound" in row["scope_review"]
    assert "not a per-case win-rate guarantee" in row["scope_review"]
    assert "do not prove source authenticity" in row["scope_review"]
    assert ledger["counts"]["CLOSED_BY_WIRING"] == 40
    assert ledger["counts"]["OPEN_FORMAL_TAIL"] == 2
    assert ledger["formal_tail_round"]["independent_closed_total"] == 18
    assert ledger["formal_tail_round"]["wiring_not_reopened"][-1] == "U13.4"

    pack = checker.disp.INDEPENDENT_CLOSE_PACKS[-2]
    receipt = checker.load_json(ROOT / pack["receipt"])
    raw = (ROOT / pack["pack"] / "axiom-audit.raw.txt").read_text(encoding="utf-8")
    assert checker.independent_close_errors(receipt, raw, pack) == []
    assert receipt["named_count"] == 19
    assert len(receipt["object_checks"]) == 23
    assert receipt["axiom_audit"]["axiom_vocabulary"] == {
        "Classical.choice": 16, "Quot.sound": 18, "propext": 18,
    }
    assert receipt["axiom_audit"]["targets_with_sorryAx"] == {}
    assert receipt["original_residuals"]["U13.4"] == (
        "Absent personal/population/prior/retrieval branching present; validate distinct provenance/scope policies for the fallback sources and nonidentification witnesses."
    )
    assert receipt["historical_reuse"]["audited_target"] is False
    assert receipt["historical_reuse"]["run_id"] == 40714963358
    for mutate in (
        lambda r: r.update(run_id=40972822214),
        lambda r: r.update(artifact_sha256="0" * 64),
        lambda r: r["names_by_clause"]["U13.4"].pop(),
        lambda r: r.update(open_after=4),
        lambda r: r["sources"].pop(),
    ):
        import copy
        changed = copy.deepcopy(receipt)
        mutate(changed)
        assert checker.independent_close_errors(changed, raw, pack)
    assert checker.independent_close_errors(receipt, raw.replace("depends on axioms", "audit omitted", 1), pack)


def test_u11_1_close_binds_causal_bridge_and_original_instances():
    errors, ledger = checker.check(write=False)
    assert errors == []
    row = next(r for r in ledger["rows"] if r["clause"] == "U11.1")
    assert row["archive_gap_status"] == "CLOSED_BY_WIRING"
    assert row["unwired_formal_obligations"] == []
    assert row["remaining_after_close"] == "WIRED_TO_INDEPENDENT_U11_1_PROOFS"
    assert row["independent_closure"] == {
        "receipt": checker.disp.U11_1_RECEIPT,
        "named_theorems_full": checker.disp.U11_1_NAMES["U11.1"],
    }
    assert ledger["counts"]["CLOSED_BY_WIRING"] == 40
    assert ledger["counts"]["OPEN_FORMAL_TAIL"] == 2
    assert ledger["formal_tail_round"]["independent_closed_total"] == 18
    pack = checker.disp.INDEPENDENT_CLOSE_PACKS[-1]
    receipt = checker.load_json(ROOT / pack["receipt"])
    raw = (ROOT / pack["pack"] / "axiom-audit.raw.txt").read_text(encoding="utf-8")
    assert checker.independent_close_errors(receipt, raw, pack) == []
    assert receipt["named_count"] == 31
    assert len(receipt["object_checks"]) == 21
    assert len(receipt["sources"]) == 11
    assert receipt["original_residuals"]["U11.1"] == (
        "Observational-equivalence/ATE countermodel and transport arithmetic present; "
        "g formula, K1/K2 selection, sharp support gaps and measurement bridges remain."
    )
