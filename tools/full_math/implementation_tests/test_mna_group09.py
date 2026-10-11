"""W2-A batch B09 acceptance tests: D077-D086, group 09 并购与交割条件.

Six pieces per demand (docs/full-math/W2B_CLASSIFICATION.md §5.4):

1. Lean contract  — Contracts.demand_D077..D086 restated as this item's own
   semantics (verified by CI; the registration-format tests live in
   test_registration_bindings.py).
2. Python entry   — tools/full_math/implementation/mna_ref.py per-item
   entries computing the intermediate result from real structured input.
3. Independent checker — mna_check.py re-derives the contract inline;
   no witness callbacks, no expectations from the main implementation.
4. Downstream consumption — unified.pipeline run_case / step_event /
   run_trace consume the M&A results through the adapters in mna_ref
   (build_case_input / build_environment / mna_trace_events).
5. Positive and adverse cases — the ALL_134 counterexample field of each
   demand is executed with per-item expectations.
6. Synthetic receipt — completion.validate_binding rows for DEMAND:D077-D086
   (the ``_binding_row`` template below is ready for the controller to
   back-fill BINDINGS.json).
"""
import json
import sys
from fractions import Fraction
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
SPEC = REPO / 'tools/full_math/spec'
sys.path.insert(0, str(REPO))
sys.path.insert(0, str(REPO / 'tools/full_math'))
sys.path.insert(0, str(REPO / 'tools/unified_math_v2'))

# Shared bare module names (`reference`, `unified`, ...) exist in several
# tool trees.  Evict cached copies ONLY when the loaded copy is from a
# foreign tree: an earlier suite may already have imported the right
# tools/unified_math_v2 modules, and a blind re-import would create a
# second enum identity that fails `kind is LegalEventKind...` dispatch.
_existing_unified = sys.modules.get('unified')
if _existing_unified is None or \
        'unified_math_v2' not in str(getattr(_existing_unified, '__file__', '')):
    for _shared in ("reference", "unified", "unified_v21"):
        for _name in [m for m in sys.modules
                      if m == _shared or m.startswith(_shared + ".")]:
            del sys.modules[_name]

from tools.full_math.implementation import mna_check as K  # noqa: E402
from tools.full_math.implementation import mna_ref as R  # noqa: E402
import completion as C  # noqa: E402

# Pipeline-facing names are imported INSIDE the downstream test, not at
# module level: other suites in this directory re-resolve the shared bare
# `unified` tree at their own import time, and call-time imports are the
# only bindings that always match the lazy in-function imports inside
# unified.pipeline/process (mna_ref's adapters already import lazily).

DEMANDS = ("D077", "D078", "D079", "D080", "D081", "D082", "D083", "D084",
           "D085", "D086")

_REP_ROWS = (("cap-table", "flat", True, False),
             ("litigation", "flat", True, True))
_SCHED_ROWS = (("target-co", "2026", "tax-affairs", None),
               ("target-co", "2026", "cap-table", True))


# ---------------------------------------------------------------------------
# 2/3/5 — entry + independent checker, positive and adverse (per item)
# ---------------------------------------------------------------------------


def _run_D077():
    """签约时真实不自动证明交割时真实（ALL_134 反例字段）."""
    out = R.rep_bringdown(_REP_ROWS, (R.TIME_SIGNING, R.TIME_BRINGDOWN))
    ok, reasons = K.check_D077(_REP_ROWS, (0, 1), out)
    return ok, reasons, out


def _run_D078():
    """除外事件无论怎样影响都排除，丢失修饰条款（ALL_134 反例字段）."""
    out = R.mae_evaluation("scope-mae", "scope-mae", True, True)
    ok, reasons = K.check_D078("scope-mae", "scope-mae", True, True, out)
    return ok, reasons, out


def _run_D079():
    """一员工知道不自动等于定义中的管理层知道（ALL_134 反例字段）."""
    rows = (("employee", R.KN_ACTUAL, True),)
    out = R.knowledge_standards(rows)
    ok, reasons = K.check_D079(rows, out)
    return ok, reasons, out


def _run_D080():
    """一般禁止不能抹去明确例外，例外也不能取消全部限制
    （ALL_134 反例字段）."""
    acts = (("contact-bidder-B", True, True),
            ("contact-bidder-C", False, True),
            ("contact-bidder-D", True, False))
    out = R.noshop_actions(acts)
    ok, reasons = K.check_D080(acts, out)
    return ok, reasons, out


def _run_D081():
    """在匹配期届满前自动生成已可终止状态（ALL_134 反例字段）."""
    out = R.matching_window(91, 40, 90, True, False)
    inside = R.matching_window(90, 40, 90, True, False)
    ok, r1 = K.check_D081(91, 40, 90, True, False, out)
    ok2, r2 = K.check_D081(90, 40, 90, True, False, inside)
    return ok and ok2, r1 + r2, (out, inside)


def _run_D082():
    """所有新报价都算介入事件导致错误权利触发（ALL_134 反例字段）."""
    out = R.offer_qualification(Fraction(110), Fraction(100), False)
    ok, reasons = K.check_D082(Fraction(110), Fraction(100), False, out)
    return ok, reasons, out


def _run_D083():
    """一个同意回执不得豁免其他独立禁止事项（ALL_134 反例字段）."""
    rows = (("hire-consultant", False, True, False),
            ("sell-facility", False, True, True))
    out = R.interim_gates(rows)
    ok, reasons = K.check_D083(rows, out)
    return ok, reasons, out


def _run_D084():
    """相互排斥救济无条件同时列为最终可得（ALL_134 反例字段）."""
    out = R.remedy_compatibility()
    ok, reasons = K.check_D084(out)
    return ok, reasons, out


def _run_D085():
    """未发生第二触发仍支付全部双触发补偿（ALL_134 反例字段）."""
    records = (("option", True, True, Fraction(7, 4)),
               ("rsu", True, False, Fraction(7, 4)))
    out = R.equity_double_trigger(records)
    ok, reasons = K.check_D085(records, out)
    return ok, reasons, out


def _run_D086():
    """披露表的未知条目被视为保证完全真实（ALL_134 反例字段）."""
    out = R.schedule_diff(_SCHED_ROWS, "target-co", "2026", "tax-affairs",
                          True)
    ok, reasons = K.check_D086(_SCHED_ROWS, "target-co", "2026",
                               "tax-affairs", True, out)
    return ok, reasons, out


_POSITIVE = {"D077": _run_D077, "D078": _run_D078, "D079": _run_D079,
             "D080": _run_D080, "D081": _run_D081, "D082": _run_D082,
             "D083": _run_D083, "D084": _run_D084, "D085": _run_D085,
             "D086": _run_D086}


@pytest.mark.parametrize("dem", DEMANDS)
def test_demand_positive(dem):
    """Entry computes the intermediate result; the independent checker
    re-derives the contract from the same input and passes."""
    ok, reasons, _out = _POSITIVE[dem]()
    assert ok, f"{dem} contract violated: {reasons}"


@pytest.mark.parametrize("dem", DEMANDS)
def test_demand_counterexample(dem):
    """The ALL_134 counterexample field of each demand is distinguishable
    in the entry output with per-item expectations."""
    _ok, _reasons, out = _POSITIVE[dem]()
    if dem == "D077":
        bringdown = out
        # 签约真、交割假：两时点结论分立；bring-down 标准是行自有字段
        assert bringdown["adverse_split"] == (True, False)
        assert bringdown["signing_true_proves_nothing"] is True
        assert bringdown["verdicts"][("cap-table", 0)] is True
        assert bringdown["verdicts"][("cap-table", 1)] is False
        assert bringdown["standards"]["cap-table"] == "flat"
    elif dem == "D078":
        mae = out
        # 作用域内例外：无不成比例影响→排除(false)；有→放回主定义(true)；
        # 修饰条款载荷性为真
        assert mae["in_scope_exception"] is False
        assert mae["in_scope_dispro"] is True
        assert mae["out_of_scope"] is True
        assert mae["modifier_load_bearing"] is True
    elif dem == "D079":
        knowledge = out
        # 三标准互异；员工实际知道≠管理层调查后知道（查表为空）
        assert knowledge["pairwise_distinct"] is True
        assert knowledge["employee_actual"] is True
        assert knowledge["management_investigated"] is None
        assert knowledge["employee_is_not_management"] is True
    elif dem == "D080":
        noshop = out
        # 只有（例外真，前提真）合法；无例外行与缺前行都不进合法集
        assert noshop["truth_table"] == {(False, False): False,
                                         (False, True): False,
                                         (True, False): False,
                                         (True, True): True}
        assert noshop["legal"] == (("contact-bidder-B", True, True),)
        assert noshop["ban_not_erased"] is True
        assert noshop["exception_needs_precond"] is True
    elif dem == "D081":
        window, inside = out
        # 窗满前不可终止（通知已到、推荐已变都无效）；边界日不可终止；
        # 窗满未匹配才可终止
        assert inside["terminable"] is False
        assert inside["boundary_day_not_terminable"] is True
        assert window["terminable"] is True
        assert window["after_window_matched"] is False
    elif dem == "D082":
        offer = out
        # 110 对 100 界内成立 SuperiorOffer、界外不成立；同等价新报价
        # 非更优不成立；不可预见过界内才成立介入事件
        assert offer["superior_in_window"] is True
        assert offer["superior_out_window"] is False
        assert offer["equal_price_not_superior"] is True
        assert offer["intervening_in_window"] is False
    elif dem == "D083":
        gates = out
        # 同意取得且无禁止→可行；有独立禁止→同意不豁免
        assert gates["decisions"][0]["allowed"] is True
        assert gates["decisions"][1]["allowed"] is False
        assert gates["consent_never_exempts_prohibition"] is True
    elif dem == "D084":
        remedies = out
        # 交割存活双请求→仅 SP+赔偿；交割已死双请求→仅终止+赔偿；
        # 互斥永不同列
        assert remedies["alive_both"] == ("specific-performance", "damages")
        assert remedies["dead_both"] == ("termination", "damages")
        assert remedies["mutually_exclusive"] is True
        assert remedies["damages_compatible"] is True
    elif dem == "D085":
        equity = out
        # 双触发齐备→恰付价格；未触发第二扳机→恰为 0
        assert equity["witness_paid"] == Fraction(7, 4)
        assert equity["witness_no_second_trigger"] == Fraction(0)
        assert equity["no_second_trigger_zero"] is True
        assert equity["fields_are_one_record"] is True
    elif dem == "D086":
        sched = out
        # 结构面 some true 对披露面 none：见证非空；未知不等于保证为真
        assert sched["witness"] == ("entity/period",)
        assert sched["unknown_not_warranted"] is True
        assert sched["same_key_agrees"] is True


@pytest.mark.parametrize("dem", DEMANDS)
def test_checker_rejects_tampered(dem):
    """The independent checker must fail a tampered intermediate result
    (the checker, not the entry, is the judge of the contract)."""
    ok, _reasons, out = _POSITIVE[dem]()
    assert ok  # sanity: the honest result passes its own checker
    if dem == "D077":
        tampered = dict(out)
        tampered["verdicts"] = dict(out["verdicts"])
        tampered["verdicts"][("cap-table", 1)] = True  # signing proves it
        bad, reasons = K.check_D077(_REP_ROWS, (0, 1), tampered)
    elif dem == "D078":
        tampered = dict(out)
        tampered["in_scope_exception"] = True  # proviso lost: excluded
        bad, reasons = K.check_D078("scope-mae", "scope-mae", True, True,
                                    tampered)
    elif dem == "D079":
        tampered = dict(out)
        tampered["management_investigated"] = True  # employee = management
        bad, reasons = K.check_D079((("employee", R.KN_ACTUAL, True),),
                                    tampered)
    elif dem == "D080":
        tampered = dict(out)
        tampered["legal"] = (("contact-bidder-C", False, True),
                             ("contact-bidder-B", True, True))  # ban erased
        bad, reasons = K.check_D080((("contact-bidder-B", True, True),
                                     ("contact-bidder-C", False, True),
                                     ("contact-bidder-D", True, False)),
                                    tampered)
    elif dem == "D081":
        window, _inside = out
        tampered = dict(window)
        tampered["terminable_before_expiry"] = True  # premature state
        tampered["boundary_day_not_terminable"] = False
        bad, reasons = K.check_D081(91, 40, 90, True, False, tampered)
    elif dem == "D082":
        tampered = dict(out)
        tampered["intervening_in_window"] = True  # every new offer counts
        bad, reasons = K.check_D082(Fraction(110), Fraction(100), False,
                                    tampered)
    elif dem == "D083":
        gates = out
        tampered = dict(gates)
        tampered["decisions"] = (dict(gates["decisions"][0]),
                                 dict(gates["decisions"][1]))
        tampered["decisions"][1]["allowed"] = True  # consent exempted
        bad, reasons = K.check_D083((("hire-consultant", False, True, False),
                                     ("sell-facility", False, True, True)),
                                    tampered)
    elif dem == "D084":
        tampered = dict(out)
        tampered["combos"] = dict(out["combos"])
        tampered["combos"][(True, True, True)] = \
            ("specific-performance", "termination", "damages")  # both
        bad, reasons = K.check_D084(tampered)
    elif dem == "D085":
        equity = out
        tampered = dict(equity)
        tampered["witness_no_second_trigger"] = Fraction(7, 4)  # full pay
        tampered["no_second_trigger_zero"] = False
        bad, reasons = K.check_D085((("option", True, True, Fraction(7, 4)),
                                     ("rsu", True, False, Fraction(7, 4))),
                                    tampered)
    elif dem == "D086":
        sched = out
        tampered = dict(sched)
        tampered["disclosure"] = True  # unknown read as warranted true
        tampered["witness"] = ()
        bad, reasons = K.check_D086(_SCHED_ROWS, "target-co", "2026",
                                    "tax-affairs", True, tampered)
    assert not bad, f"{dem} checker accepted a tampered result: {reasons}"


# ---------------------------------------------------------------------------
# per-demand adverse specifics beyond the shared parametrized set
# ---------------------------------------------------------------------------


def test_D077_every_time_point_gets_its_own_verdict():
    """每时点分别求值：三个时点三行结论，行/时对逐项独立."""
    out = R.rep_bringdown(_REP_ROWS, (0, 1))
    assert len(out["per_row_per_time"]) == 4
    assert out["verdicts"][("litigation", 0)] is True
    assert out["verdicts"][("litigation", 1)] is True


def test_D078_out_of_scope_exception_changes_nothing():
    """作用域外例外不改结果（无论有无不成比例影响都为主定义真）."""
    out = R.mae_evaluation("scope-mae", "scope-mae", True, False)
    assert out["out_of_scope"] is True
    assert R.mae_hit("other", "scope-mae", True, True) is True


def test_D079_constructive_tag_is_distinct_in_lookups():
    """推定知道标准独立成行：只有 constructive 行时 actual 查询为空."""
    rows = (("employee", R.KN_CONSTRUCTIVE, False),)
    out = R.knowledge_standards(rows)
    assert R.kn_of(rows, "employee", R.KN_ACTUAL) is None
    assert R.kn_of(rows, "employee", R.KN_CONSTRUCTIVE) is False
    ok, reasons = K.check_D079(rows, out)
    assert ok, reasons


def test_D080_legal_set_is_exact_two_gate_filter():
    """合法集=双门过滤原表：逐行回指、无凭空行动."""
    acts = (("a", True, True), ("b", True, True), ("c", False, False))
    out = R.noshop_actions(acts)
    assert out["legal"] == (("a", True, True), ("b", True, True))
    ok, reasons = K.check_D080(acts, out)
    assert ok, reasons


def test_D081_window_order_needs_notice_first():
    """报价通知先于评估日的事件次序是输入前提；倒序被如实记录."""
    out = R.matching_window(91, 40, 90, True, False)
    assert out["notice_order_ok"] is True
    out_late = R.matching_window(30, 40, 90, True, False)
    assert out_late["notice_order_ok"] is False
    ok, reasons = K.check_D081(30, 40, 90, True, False, out_late)
    assert ok, reasons


def test_D082_unforeseeable_event_qualifies_as_intervening():
    """不可预见事件在界内成立介入事件；报价再高也不替代不可预见性."""
    out = R.offer_qualification(Fraction(90), Fraction(100), True)
    assert out["superior_in_window"] is False
    assert out["intervening_in_window"] is True
    ok, reasons = K.check_D082(Fraction(90), Fraction(100), True, out)
    assert ok, reasons


def test_D083_ordinary_course_needs_no_consent():
    """通常经营行动无需同意也可行（ordinary 门独立成立）."""
    out = R.interim_gates((("pay-payroll", True, False, False),))
    assert out["decisions"][0]["allowed"] is True
    ok, reasons = K.check_D083((("pay-payroll", True, False, False),), out)
    assert ok, reasons


def test_D085_unvested_award_pays_zero_even_when_separated():
    """未归属+已离职：仍为 0（归属门独立）."""
    assert R.double_trigger_payout(False, True, Fraction(9, 2)) == 0
    out = R.equity_double_trigger((("rsu", False, True, Fraction(9, 2)),))
    ok, reasons = K.check_D085((("rsu", False, True, Fraction(9, 2)),), out)
    assert ok, reasons


def test_D086_known_disclosure_row_compares_without_witness():
    """披露表已知行与结构面一致时无见证（同键一致）."""
    out = R.schedule_diff(_SCHED_ROWS, "target-co", "2026", "cap-table",
                          True)
    assert out["witness"] == ()
    ok, reasons = K.check_D086(_SCHED_ROWS, "target-co", "2026",
                               "cap-table", True, out)
    assert ok, reasons


# ---------------------------------------------------------------------------
# 4 — downstream consumption: run_case / step_event / run_trace
# ---------------------------------------------------------------------------


def test_downstream_pipeline_consumes_mna():
    """run_case consumes the CaseInput assembled from the M&A results
    (the failed bring-down and the qualified superior offer supply the
    issue, the scoped-MAE proposition stays a defense — never a written
    fact, the D078 evaluation stays awaiting, and the only quantities
    are the paid equity award 7/4 plus the zero no-second-trigger award);
    run_trace consumes the disclosure difference witness as an evidence
    event plus the exact equity installment."""
    # call-time imports: always the same unified copies the pipeline's own
    # lazy in-function imports resolve to (see module docstring note).
    # Call-time PATH re-assertion first: test_registration_bindings inserts
    # tools/full_math at sys.path[0] at its own import time, which happens
    # AFTER this module's import (e < r), and tools/full_math carries a
    # competing bare `reference` package (without unified_reference) that
    # would shadow tools/unified_math_v2 at the lazy-import moment.
    _v2 = str(REPO / 'tools/unified_math_v2')
    while _v2 in sys.path:
        sys.path.remove(_v2)
    sys.path.insert(0, _v2)
    from theory.spec.canonical_v2.case import RunStatus
    from theory.spec.canonical_v2.kernel import Judgment
    from unified.pipeline import run_case, run_trace, step_event
    from unified.process import gross_of

    intake = R.build_mna_intake()
    case = R.build_case_input(intake)
    env = R.build_environment(intake)

    # the assembled carriers are exactly the mna outputs
    assert case.issues == ("MAE_CLOSING",)
    assert case.claims[0].claimant == "buyer"
    assert case.claims[0].respondent == "target"
    # D078: the scoped-MAE proposition is a defense, and the mae
    # proposition stays awaiting — never written
    assert case.defenses[0].defense_id == "def-mae"
    assert case.defenses[0].basis == "mae_exception_scoped"
    assert case.defenses[0].target_claims == ("c0",)
    standings = {(f.proposition.predicate, f.standing.name)
                 for f in case.fact_records}
    assert ("bringdown-failed", "ADMITTED_POSITIVE") in standings
    assert ("offer-qualified", "ADMITTED_POSITIVE") in standings
    assert ("mae-established", "AWAITING_ADMISSION") in standings
    # D085: the only quantities are the paid award and the zero award
    assert [q.value for q in case.quantities] == [Fraction(7, 4),
                                                  Fraction(0)]

    run = run_case(case, env)
    assert run.status is RunStatus.COMPLETE
    assert run.failures == ()
    judgments = run.judgments_of("c0")
    assert judgments and Judgment.ESTABLISHED in judgments

    # trace: the disclosure difference witness becomes an evidence event;
    # the vested award lands as one exact installment (7/4)
    events = R.mna_trace_events(intake)
    assert [e.event.event_id for e in events[:1]] == ["ev-schedule-diff"]
    final, notes = run_trace(case.initial_state, events, env)
    assert "ev:ev-schedule-diff" in [e.evidence_id for e in final.evidence]
    event_ids = [e.event_id for e in final.events]
    assert "pay-equity-7/4" in event_ids
    assert gross_of(final, "EQUITY_PAYOUT") == Fraction(7, 4)
    allocated = [e for e in final.ledger
                 if e.kind.name == "GROSS_ALLOCATED"
                 and e.basis_key == "EQUITY_PAYOUT"]
    assert sorted(e.amount for e in allocated) == [Fraction(7, 4)]
    assert notes  # the step relation actually produced observations

    # step_event alone: one step, exactly the event's own semantics
    one = step_event(case.initial_state, events[0], env)
    assert [e.evidence_id for e in one.next_state.evidence] == \
        ["ev:ev-schedule-diff"]
    assert one.next_env is env

    # the mna decisions stay on the bundle: the bring-down failed at
    # closing (D077), the modifier stayed load-bearing (D078), the
    # employee was not the management (D079), the two-gate contact set
    # kept its shape (D080), nothing terminated inside the window
    # (D081), the offer was superior but not intervening (D082), consent
    # did not exempt the prohibition (D083), the remedies stayed
    # mutually exclusive (D084), the second award paid zero (D085), and
    # the unknown disclosure kept its witness (D086)
    assert intake["bringdown"]["signing_true_proves_nothing"] is True
    assert intake["mae"]["modifier_load_bearing"] is True
    assert intake["knowledge"]["employee_is_not_management"] is True
    assert intake["noshop"]["legal"] == (("contact-bidder-B", True, True),)
    assert intake["window_inside"]["terminable"] is False
    assert intake["offer"]["superior_in_window"] is True
    assert intake["offer"]["intervening_in_window"] is False
    assert intake["gates"]["consent_never_exempts_prohibition"] is True
    assert intake["remedies"]["mutually_exclusive"] is True
    assert intake["equity"]["no_second_trigger_zero"] is True
    assert intake["sched"]["witness"] == ("entity/period",)


# ---------------------------------------------------------------------------
# 6 — synthetic receipts through completion.validate_binding
# ---------------------------------------------------------------------------

_REQUIREMENTS = {
    r["id"]: r
    for r in json.loads((SPEC / 'REQUIREMENTS.json').read_text(encoding='utf-8'))
}

_SEMANTICS = {
    "D077": "every representation row carries its own bring-down standard "
            "with a separate accuracy status per evaluation time; each "
            "declared closing time is tested separately, and a row true "
            "at signing and false at closing yields two different "
            "verdicts — true at signing never proves true at closing.",
    "D078": "the MAE clause evaluates with scoped expressions: an "
            "in-scope exception takes the event out of MAE, but the "
            "disproportionate-impact proviso puts an exception that "
            "disproportionately harms the target back inside the main "
            "definition; an out-of-scope exception never changes the "
            "outcome, and the modifier is load-bearing.",
    "D079": "actual knowledge, constructive knowledge and "
            "knowledge-after-investigation are three distinct typed tags "
            "(never one boolean field); knowledge rows are keyed by "
            "(holder group, standard tag), so an employee row never "
            "answers a management query.",
    "D080": "the legal action set is the candidate contact actions "
            "filtered through both gates (a declared exception AND its "
            "own exercise precondition); a no-exception action never "
            "enters (the general ban is not erased) and an exception "
            "without its precondition never enters (the exception "
            "cancels no restriction).",
    "D081": "the termination right after an unmatched superior offer is "
            "exercisable only once the matching window has expired: "
            "before the window ends no earlier event (offer notice, "
            "recommendation change) makes the deal terminable, the "
            "boundary day itself is still inside the window, and only "
            "after it does an unmatched deal become terminable.",
    "D082": "SuperiorOffer and InterveningEvent are matched against "
            "their own definitions and time bounds: strictly better "
            "consideration inside the window qualifies as superior "
            "(outside it never does), an unforeseeable event inside the "
            "window qualifies as intervening, and a mere new offer is "
            "never one.",
    "D083": "an interim-operating action passes all of its own necessary "
            "gates at once: it must clear every declared prohibition AND "
            "stay inside the ordinary-course covenant or carry buyer "
            "consent; the three inputs are separate record fields and "
            "one consent receipt never exempts an independent "
            "prohibition.",
    "D084": "the joint remedy result under the compatibility policy: "
            "after closing specific performance (with damages) is "
            "available and termination is not; once the deal is off, "
            "termination (with damages) is available and specific "
            "performance is not — mutually exclusive remedies are never "
            "jointly listed, while damages stay compatible with either.",
    "D085": "the equity-award record computes every payout field jointly: "
            "the double-trigger compensation pays out only when the "
            "award is vested AND the second trigger (the separation) "
            "has fired; without the second trigger the payout is "
            "exactly zero, and vesting and service status remain "
            "independent record fields.",
    "D086": "structure-side and disclosure-side statuses are looked up "
            "under one (entity, period) key and compared: differing "
            "statuses yield a named difference witness, agreeing "
            "carriers yield none, and an unknown disclosure entry "
            "(no row) is never read as a warranted-true row.",
}

_ENTRY = {
    "D077": "rep_verdict/rep_bringdown",
    "D078": "mae_hit/mae_evaluation",
    "D079": "kn_of/knowledge_standards",
    "D080": "contact_legal/legal_contacts/noshop_actions",
    "D081": "can_term/matching_window",
    "D082": "is_superior_offer/is_intervening_event/offer_qualification",
    "D083": "action_allowed/interim_gates",
    "D084": "closing_remedies/remedy_compatibility",
    "D085": "double_trigger_payout/equity_double_trigger",
    "D086": "sched_status/diff_witness/schedule_diff",
}


def _binding_row(dem, required):
    """Template for the controller's BINDINGS.json back-fill
    (DEMAND:D077–D086 rows).  Passes completion.validate_binding as-is."""
    return {
        "id": f"DEMAND:{dem}",
        "theorem": required["theorem"],
        "contract": required["contract"],
        "proof_mode": "KERNEL_CONTRACT_PROOF",
        "formal_scope": "Group-09 M&A-closing demand instance in the "
                        "shared semantic framework: this item's own "
                        "contract semantics plus the registered Horn "
                        "fixpoint component (every closure iterate is "
                        "contained in every pre-fixed point — the "
                        "least-closure discipline behind "
                        "closing-condition evaluation), with its adverse "
                        "case executed as a negative test.",
        "independent_semantics": _SEMANTICS[dem],
        "algorithm": f"tools/full_math/implementation/mna_ref.py "
                     f"{_ENTRY[dem]} computes the intermediate result from "
                     f"structured input; mna_check.check_{dem} "
                     f"re-derives the contract independently.",
        "observation_contract": "Inputs are the declared structures "
                                "(representation rows with per-time "
                                "accuracy statuses and bring-down "
                                "standards, scoped MAE keys with "
                                "exception and disproportionate-impact "
                                "flags, relation-keyed knowledge rows "
                                "over three typed standards, candidate "
                                "contact actions with exception and "
                                "precondition gates, matching-window "
                                "day/notice/expiry/order records, offer "
                                "qualifications with prices and time "
                                "bounds, interim-action gate records "
                                "with ordinary-course, consent and "
                                "prohibition flags, remedy-request "
                                "triples under the closing state, "
                                "equity-award records with vesting, "
                                "service status and exact prices, and "
                                "disclosure-schedule rows keyed by "
                                "entity and period); outputs are exactly "
                                "the contract quantities (per-time "
                                "verdicts with the adverse split "
                                "witness, the scoped MAE hit with the "
                                "load-bearing modifier, the keyed "
                                "knowledge lookups, the two-gate legal "
                                "action set with the truth table, the "
                                "window-ordered termination feasibility, "
                                "the separately matched offer and "
                                "intervening qualifications, the "
                                "all-gates decision record, the joint "
                                "remedy lists with the mutual-exclusion "
                                "check, the double-trigger payouts with "
                                "the zero witness, and the same-key "
                                "comparison with its difference "
                                "witness).",
        "external_assumptions": "The adopted deal interpretation, "
                                "materiality and disproportionate-impact "
                                "judgments, knowledge attribution and "
                                "investigation scope, fiduciary-out "
                                "determinations, board strategy "
                                "evaluations, offer superiority and "
                                "foreseeability, ordinary-course "
                                "reasonableness, remedy availability and "
                                "court discretion, equity plan terms and "
                                "separation facts, and disclosure "
                                "adequacy remain external validation "
                                "obligations, not part of this "
                                "registration.",
        "proof_sources": [
            "proofs/lean/juris_lean/JurisLean/FullMath/Contracts.lean",
            "proofs/lean/juris_lean/JurisLean/FullMath/Acceptance.lean",
        ],
        "implementation_sources": [
            "tools/full_math/implementation/mna_ref.py",
            "tools/full_math/implementation/mna_check.py",
        ],
        "test_ids": [
            "tools/full_math/implementation_tests::"
            "test_mna_group09.py::"
            f"test_demand_positive[{dem}]",
            "tools/full_math/implementation_tests::"
            "test_mna_group09.py::"
            f"test_demand_counterexample[{dem}]",
            "tools/full_math/implementation_tests::"
            "test_mna_group09.py::"
            "test_downstream_pipeline_consumes_mna",
        ],
        "negative_test_ids": [
            "tools/full_math/implementation_tests::"
            "test_mna_group09.py::"
            f"test_checker_rejects_tampered[{dem}]",
        ],
        "semantic_links": [
            "JurisLean.FullMath.Logic.cl_least_iterate",
        ],
    }


@pytest.mark.parametrize("dem", DEMANDS)
def test_b09_binding_receipt(dem):
    """Synthetic receipt: the binding row for DEMAND:D0XX passes
    completion.validate_binding against the real repository files."""
    required = _REQUIREMENTS[f"DEMAND:{dem}"]
    C.validate_binding(_binding_row(dem, required), required, repo=REPO)


@pytest.mark.parametrize("dem", DEMANDS)
def test_b09_binding_receipt_negative(dem):
    """A tampered receipt (swapped theorem) is rejected."""
    required = _REQUIREMENTS[f"DEMAND:{dem}"]
    row = dict(_binding_row(dem, required))
    row["theorem"] = "JurisLean.FullMath.Acceptance.nonexistent_demand"
    with pytest.raises(C.EvidenceError):
        C.validate_binding(row, required, repo=REPO)
