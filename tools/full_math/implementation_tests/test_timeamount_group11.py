"""W2-A batch B11 acceptance tests: D095-D103, group 11 金额、时间和
经济敞口.

Six pieces per demand (docs/full-math/W2B_CLASSIFICATION.md §5.4):

1. Lean contract  — Contracts.demand_D095..D103 restated as this item's own
   semantics (verified by CI; the registration-format tests live in
   test_registration_bindings.py).
2. Python entry   — tools/full_math/implementation/timeamount_ref.py per-item
   entries computing the intermediate result from real structured input
   (calendar surface consumed from calendar_ref, the mirror of
   JurisLean.Seams.UnifiedCalendar).
3. Independent checker — timeamount_check.py re-derives the contract inline
   against the stdlib datetime oracle; no witness callbacks, no
   expectations from the main implementation.
4. Downstream consumption — unified.pipeline run_case / step_event /
   run_trace consume the money-time results through the adapters in
   timeamount_ref (build_case_input / build_environment /
   timeamount_trace_events).
5. Positive and adverse cases — the ALL_134 counterexample field of each
   demand is executed with per-item expectations.
6. Synthetic receipt — completion.validate_binding rows for
   DEMAND:D095-D103 (the ``_binding_row`` template below is ready for
   the controller to back-fill BINDINGS.json).
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

from tools.full_math.implementation import timeamount_check as K  # noqa: E402
from tools.full_math.implementation import timeamount_ref as R  # noqa: E402
import completion as C  # noqa: E402

# Pipeline-facing names are imported INSIDE the downstream test, not at
# module level (same rationale as test_drafting_group12).

DEMANDS = ("D095", "D096", "D097", "D098", "D099", "D100", "D101",
           "D102", "D103")


# ---------------------------------------------------------------------------
# 2/3/5 — entry + independent checker, positive and adverse (per item)
# ---------------------------------------------------------------------------


def _run_D095():
    """还款后仍用旧本金累计全部期间利息（ALL_134 反例字段）."""
    out = R.debt_statement(Fraction(100000), Fraction(1, 1000),
                           (2024, 1, 15), (2024, 2, 1), (2024, 3, 10),
                           Fraction(40000))
    ok, reasons = K.check_D095(Fraction(100000), Fraction(1, 1000),
                               (2024, 1, 15), (2024, 2, 1), (2024, 3, 10),
                               Fraction(40000), out)
    return ok, reasons, out


def _run_D096():
    """用当前LPR倒填所有历史借款期间（ALL_134 反例字段）."""
    out = R.rate_scenario(Fraction(4))
    ok, reasons = K.check_D096(Fraction(4), out)
    return ok, reasons, out


def _run_D097():
    """按股计价格与总价混用使倍率相差股份数（ALL_134 反例字段）."""
    out = R.consideration_split()
    ok, reasons = K.check_D097(out)
    return ok, reasons, out


def _run_D098():
    """2%溢价计在原授信额度而非应清偿余额（ALL_134 反例字段）."""
    out = R.prepay_quote()
    ok, reasons = K.check_D098(Fraction(1000000), Fraction(400000),
                               Fraction(2, 100), out)
    return ok, reasons, out


def _run_D099():
    """60日补正期未到，仅因30日通知期到便认定终止（ALL_134 反例字段）."""
    out = R.notice_vs_cure()
    ok, reasons = K.check_D099(out)
    return ok, reasons, out


def _run_D100():
    """倒排某项日期在过去，不能仍输出可执行完整计划（ALL_134 反例字段）."""
    out = R.back_plan()
    ok, reasons = K.check_D100(out)
    return ok, reasons, out


def _run_D101():
    """将收入风险当已实现损失并与原收入重复相加（ALL_134 反例字段）."""
    out = R.exposure_mixing()
    ok, reasons = K.check_D101(out)
    return ok, reasons, out


def _run_D102():
    """删除终止前已发生的应付款或已产生责任（ALL_134 反例字段）."""
    out = R.termination_closeout()
    ok, reasons = K.check_D102(out)
    return ok, reasons, out


def _run_D103():
    """目标与期末使用不同科目范围仍报告精确差额（ALL_134 反例字段）."""
    out = R.wc_adjustment()
    ok, reasons = K.check_D103(out)
    return ok, reasons, out


_POSITIVE = {"D095": _run_D095, "D096": _run_D096, "D097": _run_D097,
             "D098": _run_D098, "D099": _run_D099, "D100": _run_D100,
             "D101": _run_D101, "D102": _run_D102, "D103": _run_D103}


@pytest.mark.parametrize("dem", DEMANDS)
def test_demand_positive(dem):
    """Entry computes the intermediate result; the independent checker
    re-derives the contract from the same input (stdlib datetime oracle)
    and passes."""
    ok, reasons, _out = _POSITIVE[dem]()
    assert ok, f"{dem} contract violated: {reasons}"


@pytest.mark.parametrize("dem", DEMANDS)
def test_demand_counterexample(dem):
    """The ALL_134 counterexample field of each demand is distinguishable
    in the entry output with per-item expectations."""
    _ok, _reasons, out = _POSITIVE[dem]()
    if dem == "D095":
        debt = out
        # 分段守恒；旧本金全期计息高于残余本金分段计息
        assert debt["split_conserved"] is True
        assert debt["correct_total"] == Fraction(3980)
        assert debt["old_principal_total"] == Fraction(5500)
        assert debt["old_principal_overstates"] is True
        assert debt["impute_conserved"] is True
        assert debt["impute_within"] is True
    elif dem == "D096":
        rate = out
        # 历史期间在事件日前；倒填发散；未确认基准直通
        assert rate["historical_before_event"] is True
        assert rate["correct_applied"] == Fraction(71, 500)
        assert rate["backfilled_applied"] == Fraction(69, 500)
        assert rate["backfill_diverges"] is True
        assert rate["unconfirmed_passes_through"] is True
    elif dem == "D097":
        cons = out
        # 维度敏感；汇率一致；两阶段舍入不同
        assert cons["exact_total"] == Fraction(2)
        assert cons["late_round"] == Fraction(2)
        assert cons["early_round"] == Fraction(1)
        assert cons["stages_differ"] is True
        assert cons["dimension_sensitive"] is True
        assert cons["fx_consistent"] is True
    elif dem == "D098":
        prepay = out
        # 触发日为月算术；早还零溢价、晚还按余额计；按授信额度计发散
        assert prepay["trigger"] == (2024, 9, 15)
        assert prepay["early_triggered"] is False
        assert prepay["late_triggered"] is True
        assert prepay["premium_early"] == Fraction(0)
        assert prepay["premium_late"] == Fraction(8000)
        assert prepay["premium_on_facility"] == Fraction(20000)
        assert prepay["facility_misbase_visible"] is True
        assert prepay["accounts_separate"] is True
    elif dem == "D099":
        periods = out
        # 基础期限严格序；顺延幂等；通知到而补正未到；证据缺失不产生权利
        assert periods["base_strictly_ordered"] is True
        assert periods["notice_base"] == 739042
        assert periods["cure_base"] == 739072
        assert periods["roll_idempotent"] is True
        assert periods["notice_arrived"] is True
        assert periods["cure_arrived"] is False
        assert periods["right_from_notice_only"] is True
        assert periods["cure_right_arises"] is False
        assert periods["unevidenced_blocks"] is True
    elif dem == "D100":
        plan = out
        # 可行往返成立；过去底界冲突；可行底界出计划
        assert plan["start"] == (2024, 3, 1)
        assert plan["roundtrip"] is True
        assert plan["past_floor_conflict"] is True
        assert plan["ok_floor_plan"] == (2024, 3, 1)
        assert plan["start_before_past_floor"] is True
    elif dem == "D101":
        exposure = out
        # 四类互异；风险折价；直加/重复加都高于声明聚合；天数差精确
        assert exposure["kinds_pairwise_distinct"] is True
        assert exposure["risk_discounts"] is True
        assert exposure["declared_total"] == Fraction(6500)
        assert exposure["risk_as_realized"] == Fraction(8000)
        assert exposure["risk_double_counted"] == Fraction(8500)
        assert exposure["mixing_overstates"] is True
        assert exposure["double_counts"] is True
        assert exposure["leap_q1_days"] == 90
        assert exposure["flat_q1_days"] == 89
    elif dem == "D102":
        closeout = out
        # 已发生应付款存续；未来服务义务熄灭；一并清空可分辨；射线律
        assert closeout["accrued_amount"] == Fraction(8000)
        assert closeout["accrued_survives"] is True
        assert closeout["future_amount"] == Fraction(0)
        assert closeout["future_extinguished"] is True
        assert closeout["blanket_clear_deletes_accrued"] is True
        assert closeout["ray_law_start"] is True
        assert closeout["period_after_term_iff_start"] is True
    elif dem == "D103":
        wc = out
        # 排除项中性；同一口径差额精确；混入现金科目发散
        assert wc["exclusion_neutral"] is True
        assert wc["target"] == Fraction(6000)
        assert wc["closing"] == Fraction(6200)
        assert wc["adjustment"] == Fraction(200)
        assert wc["mixed_scope_adjustment"] == Fraction(1200)
        assert wc["scope_mix_diverges"] is True


@pytest.mark.parametrize("dem", DEMANDS)
def test_checker_rejects_tampered(dem):
    """The independent checker must fail a tampered intermediate result
    (the checker, not the entry, is the judge of the contract)."""
    ok, _reasons, out = _POSITIVE[dem]()
    assert ok  # sanity: the honest result passes its own checker
    if dem == "D095":
        tampered = dict(out)
        tampered["old_principal_overstates"] = False  # old base accepted
        bad, reasons = K.check_D095(Fraction(100000), Fraction(1, 1000),
                                    (2024, 1, 15), (2024, 2, 1),
                                    (2024, 3, 10), Fraction(40000),
                                    tampered)
    elif dem == "D096":
        tampered = dict(out)
        tampered["backfill_diverges"] = False  # backfill silenced
        bad, reasons = K.check_D096(Fraction(4), tampered)
    elif dem == "D097":
        tampered = dict(out)
        tampered["stages_differ"] = False  # rounding stage not explicit
        bad, reasons = K.check_D097(tampered)
    elif dem == "D098":
        tampered = dict(out)
        tampered["facility_misbase_visible"] = False  # facility conflated
        bad, reasons = K.check_D098(Fraction(1000000), Fraction(400000),
                                    Fraction(2, 100), tampered)
    elif dem == "D099":
        tampered = dict(out)
        tampered["cure_arrived"] = True  # cure read as arrived via notice
        bad, reasons = K.check_D099(tampered)
    elif dem == "D100":
        tampered = dict(out)
        tampered["past_floor_conflict"] = False  # past start executable
        bad, reasons = K.check_D100(tampered)
    elif dem == "D101":
        tampered = dict(out)
        tampered["mixing_overstates"] = False  # risk as realized accepted
        bad, reasons = K.check_D101(tampered)
    elif dem == "D102":
        tampered = dict(out)
        tampered["blanket_clear_deletes_accrued"] = False  # deletion OK
        bad, reasons = K.check_D102(tampered)
    elif dem == "D103":
        tampered = dict(out)
        tampered["scope_mix_diverges"] = False  # scope mixing silenced
        bad, reasons = K.check_D103(tampered)
    assert not bad, f"{dem} checker accepted a tampered result: {reasons}"


# ---------------------------------------------------------------------------
# per-demand adverse specifics beyond the shared parametrized set
# ---------------------------------------------------------------------------


def test_D095_segment_kernel_and_waterfall_boundaries():
    """段利息＝基数×日率×精确天数；瀑布在付款不足时恰全额分配."""
    seg = R.interest_seg(Fraction(100), Fraction(1, 10),
                         (2024, 1, 1), (2024, 1, 11))
    assert seg == Fraction(100)  # 100 × 1/10 × 10 days
    assert R.impute_all(Fraction(50), (Fraction(30), Fraction(40))) == \
        (Fraction(30), Fraction(20))
    allocs = R.impute_all(Fraction(100), (Fraction(30), Fraction(90)))
    assert sum(allocs, Fraction(0)) == Fraction(100)
    over = R.impute_all(Fraction(1000), (Fraction(30), Fraction(90)))
    assert sum(over, Fraction(0)) == Fraction(120)


def test_D096_step_rate_boundary_days():
    """事件日当天用新基准、前一天用旧基准（边界含事件日本身）."""
    e = 738885  # toordinal(2024-01-01)
    old, new = Fraction(3), Fraction(4)
    assert R.step_rate(e, old, new, e) == new
    assert R.step_rate(e, old, new, e - 1) == old
    assert R.step_rate(e, old, new, e + 100) == new


def test_D097_rounding_is_floor_and_fx_total():
    """取整＝向下取整；汇率折算总价＝股份数×(单价×汇率)."""
    assert R.round_units(Fraction(7, 3)) == Fraction(2)
    total = R.consideration(Fraction(1), Fraction(3),
                            Fraction(2) * Fraction(7, 5))
    assert total == Fraction(1) + Fraction(3) * Fraction(2) * Fraction(7, 5)


def test_D098_trigger_boundary_same_day_counts():
    """触发日当天即视为到达（含端点）."""
    assert R.triggered((2024, 9, 15), (2024, 9, 15)) is True
    assert R.triggered((2024, 9, 15), (2024, 9, 14)) is False
    assert R.make_whole(False, Fraction(999), Fraction(1)) == Fraction(0)


def test_D099_right_arises_truth_table_and_later_day():
    """权利＝到期∧有证据；补正期过后才产生（更晚的日子）."""
    assert R.right_arises(True, True) is True
    assert R.right_arises(True, False) is False
    assert R.right_arises(False, True) is False
    later = R.notice_vs_cure(day=739100)
    assert later["cure_arrived"] is True
    assert later["cure_right_arises"] is True


def test_D100_floor_equal_to_start_is_feasible():
    """底界＝起算日时可执行（含端点，仅严格过去才冲突）."""
    assert R.back_item((2024, 3, 1), (2024, 3, 31), 30) == (2024, 3, 1)
    assert R.back_item((2024, 3, 2), (2024, 3, 31), 30) is None


def test_D101_empty_contingent_and_declared_function_only():
    """无或有项时聚合＝本金＋成本；聚合只经声明风险函数."""
    assert R.aggregate(Fraction(5), Fraction(6), (), Fraction(1, 2)) == \
        Fraction(11)
    assert R.aggregate(Fraction(5), Fraction(6), (Fraction(4),),
                       Fraction(1, 4)) == Fraction(12)


def test_D102_boundary_end_equals_term_survives():
    """主履行义务恰在终止日完结仍按原额计入（更新而非清空）."""
    term = R.to_epoch_day((2024, 6, 30))
    same_day = R.to_epoch_day((2024, 6, 30))
    assert R.survival_update(1, Fraction(9000), same_day, term) == \
        Fraction(9000)
    assert R.survival_update(1, Fraction(9000), term + 1, term) == \
        Fraction(0)


def test_D103_exclusions_remove_exactly_named_rows():
    """排除项按名称精确剔除；异名账户保留."""
    rows = (("cash", Fraction(10)), ("receivables", Fraction(5)))
    assert R.working_capital(rows, ("cash",)) == Fraction(5)
    assert R.working_capital(rows, ("cash-x",)) == Fraction(15)


# ---------------------------------------------------------------------------
# 4 — downstream consumption: run_case / step_event / run_trace
# ---------------------------------------------------------------------------


def test_downstream_pipeline_consumes_timeamount():
    """run_case consumes the CaseInput assembled from the money-time
    results (the segmented accrual and the surviving payable supply the
    issue, the old-principal proposition stays awaiting — never written,
    and the only quantities are the residual principal and the
    make-whole premium — two separate accounts that are never merged);
    run_trace consumes the waterfall repayment (one exact 40000-fen
    payment across fees/interest/penalty/principal on the payable basis)
    plus the surviving 8000-fen accrued installment."""
    # call-time imports: always the same unified copies the pipeline's own
    # lazy in-function imports resolve to (see module docstring note).
    _v2 = str(REPO / 'tools/unified_math_v2')
    while _v2 in sys.path:
        sys.path.remove(_v2)
    sys.path.insert(0, _v2)
    from theory.spec.canonical_v2.case import RunStatus
    from theory.spec.canonical_v2.kernel import Judgment
    from unified.pipeline import run_case, run_trace, step_event
    from unified.process import gross_of

    intake = R.build_timeamount_intake()
    case = R.build_case_input(intake)
    env = R.build_environment(intake)

    # the assembled carriers are exactly the money-time outputs
    assert case.issues == ("TIME_AMOUNT",)
    assert case.claims[0].claimant == "client"
    assert case.claims[0].respondent == "counterparty"
    # D100: the back-schedule conflict defense rides on the case; the
    # old-principal proposition stays awaiting — never written
    assert case.defenses[0].defense_id == "def-back-conflict"
    assert case.defenses[0].basis == "back_schedule_conflict"
    assert case.defenses[0].target_claims == ("c0",)
    standings = {(f.proposition.predicate, f.standing.name)
                 for f in case.fact_records}
    assert ("interest-segmented", "ADMITTED_POSITIVE") in standings
    assert ("payable-survives", "ADMITTED_POSITIVE") in standings
    assert ("old-principal-accrual", "AWAITING_ADMISSION") in standings
    # D095/D098: the only quantities are the residual principal (60000)
    # and the make-whole premium (8000) — separate accounts, never merged
    assert [q.value for q in case.quantities] == [Fraction(60000),
                                                  Fraction(8000)]
    assert {q.basis_kind for q in case.quantities} == \
        {"principal-residual", "make-whole-premium"}

    run = run_case(case, env)
    assert run.status is RunStatus.COMPLETE
    assert run.failures == ()
    judgments = run.judgments_of("c0")
    assert judgments and Judgment.ESTABLISHED in judgments

    # trace: the waterfall repayment lands on the payable basis (exactly
    # the D095 allocation sum 40000 fen) and the surviving accrued
    # payable lands as its own 8000-fen installment
    events = R.timeamount_trace_events(intake)
    assert [e.event.event_id for e in events[:1]] == ["pay-waterfall"]
    final, notes = run_trace(case.initial_state, events, env)
    event_ids = [e.event_id for e in final.events]
    assert "pay-waterfall" in event_ids
    assert "pay-accrued-8000" in event_ids
    assert gross_of(final, "PAYABLE_AMOUNT") == Fraction(40000)
    assert gross_of(final, "ACCRUED_PAYABLE") == Fraction(8000)
    allocated = [e for e in final.ledger
                 if e.kind.name == "GROSS_ALLOCATED"
                 and e.basis_key == "ACCRUED_PAYABLE"]
    assert sorted(e.amount for e in allocated) == [Fraction(8000)]
    assert notes  # the step relation actually produced observations

    # step_event alone: one step, exactly the event's own semantics
    one = step_event(case.initial_state, events[0], env)
    assert one.next_env is env

    # the money-time decisions stay on the bundle: the segmented debt
    # statement (D095), the as-of benchmark (D096), the dimensional
    # consideration with its explicit rounding stage (D097), the
    # separated prepayment quote (D098), the notice/cure periods (D099),
    # the conflict-reporting back plan (D100), the declared risk
    # aggregation (D101), the survival closeout (D102) and the
    # same-definition adjustment (D103)
    assert intake["debt"]["old_principal_overstates"] is True
    assert intake["rate"]["backfill_diverges"] is True
    assert intake["consideration"]["stages_differ"] is True
    assert intake["prepay"]["facility_misbase_visible"] is True
    assert intake["periods"]["cure_right_arises"] is False
    assert intake["plan"]["past_floor_conflict"] is True
    assert intake["exposure"]["mixing_overstates"] is True
    assert intake["closeout"]["blanket_clear_deletes_accrued"] is True
    assert intake["wc"]["scope_mix_diverges"] is True


# ---------------------------------------------------------------------------
# 6 — synthetic receipts through completion.validate_binding
# ---------------------------------------------------------------------------

_REQUIREMENTS = {
    r["id"]: r
    for r in json.loads((SPEC / 'REQUIREMENTS.json').read_text(encoding='utf-8'))
}

_SEMANTICS = {
    "D095": "principal, interest, penalty and fees are computed on "
            "independent bases, periods and combination rules with "
            "conservative imputation: a period split at a midpoint gives "
            "two exact day counts summing to the whole (the unified "
            "calendar's integer days, never a 30-day average), the "
            "waterfall imputation never double-spends or loses a "
            "payment, and after a repayment the interest accrues on the "
            "residual base — using the old principal over the full "
            "period overstates the debt.",
    "D096": "the benchmark value is decided by the event date and the "
            "legal policy (from the event day the new benchmark "
            "applies, before it the old one), and the interest-rate "
            "multiple acts only on a confirmed benchmark — an "
            "unconfirmed base passes through unchanged, so backfilling "
            "the current benchmark into a historical loan period yields "
            "a visibly different applied rate.",
    "D097": "cash, share count, per-share price, fx and exchange ratio "
            "derive by dimension (share × per-share = total; fx "
            "commutes with the share multiplication) and rounding is "
            "applied once at the declared final stage — rounding "
            "mid-derivation gives a different total, so the stage is "
            "explicit, and per-share and total prices are never mixed.",
    "D098": "the prepaid principal balance and the make-whole premium "
            "are separate accounts: the premium ratio applies to the "
            "balance being repaid (never the original facility) and "
            "only when the month-arithmetic trigger date is reached — "
            "trigger day and applicable ratio verified jointly.",
    "D099": "each period carries anchor, length, calendar and "
            "deadline_effect (the business-day roll is idempotent — a "
            "rolled deadline rolled again does not move) plus an "
            "evidence status; the termination right arises only when "
            "the deadline has arrived AND the arrival is evidenced — "
            "the 30-day notice expiring never substitutes for the "
            "60-day cure period.",
    "D100": "a back-scheduled start satisfies the precedence constraint "
            "exactly (adding the lead days forward returns the "
            "deadline) and satisfies the calendar constraint (epoch-"
            "bounded backward steps); a start before the floor date "
            "(for example today) is reported as a conflict, never "
            "silently clamped into an executable plan.",
    "D101": "debt principal, accrued cost, income risk and contingent "
            "compensation are distinct kinds with distinct conditions; "
            "contingent items enter the total only through the declared "
            "risk function (probability-weighted), so treating a risk "
            "figure as a realized loss or double-adding it overstates "
            "the exposure; exposure periods keep exact integer day "
            "counts.",
    "D102": "post-termination obligations are updated by the survival "
            "rules, not cleared together with the main performance: an "
            "accrued payable survives verbatim, a wholly-future "
            "performance obligation is extinguished, and the ordering "
            "of a closed period after the termination day is decided by "
            "its start (the survival ray law).",
    "D103": "the price adjustment is computed from one working-capital "
            "definition, one reference-date equivalence, one exclusion "
            "list and the reconciliation difference: the same scope at "
            "target and closing gives the exact adjustment, excluded "
            "accounts never enter, and letting an extra account into "
            "one side only is a different-scope difference, not this "
            "definition's reconciliation.",
}

_ENTRY = {
    "D095": "interest_seg/impute_all/debt_statement",
    "D096": "step_rate/capped_mult/rate_scenario",
    "D097": "consideration/round_units/consideration_split",
    "D098": "triggered/make_whole/prepay_quote",
    "D099": "deadline_arrived/right_arises/notice_vs_cure",
    "D100": "back_item/back_plan",
    "D101": "aggregate/exposure_mixing",
    "D102": "survival_update/termination_closeout",
    "D103": "working_capital/adjustment/wc_adjustment",
}

_SEMANTIC_LINKS = {
    "D095": ["JurisLean.FullMath.Numeric.succDay_ordinal_mono",
             "JurisLean.Seams.UnifiedCalendar.daysDiff_split"],
    "D096": ["JurisLean.FullMath.Numeric.succDay_ordinal_mono",
             "JurisLean.Seams.UnifiedCalendar.epoch_le_iff_lex"],
    "D097": ["JurisLean.FullMath.Numeric.succDay_ordinal_mono",
             "JurisLean.Seams.UnifiedCalendar.epoch_le_iff_lex"],
    "D098": ["JurisLean.FullMath.Numeric.succDay_ordinal_mono",
             "JurisLean.Seams.UnifiedCalendar.addCalMonths_valid"],
    "D099": ["JurisLean.FullMath.Numeric.succDay_ordinal_mono",
             "JurisLean.Seams.UnifiedCalendar.PeriodSpec.base_strict_order"],
    "D100": ["JurisLean.FullMath.Numeric.succDay_ordinal_mono",
             "JurisLean.Seams.UnifiedCalendar.backSchedule_some_addBack"],
    "D101": ["JurisLean.FullMath.Numeric.succDay_ordinal_mono",
             "JurisLean.Seams.UnifiedCalendar.daysDiff_split"],
    "D102": ["JurisLean.FullMath.Numeric.succDay_ordinal_mono",
             "JurisLean.Seams.UnifiedCalendar.interval_in_ray_iff"],
    "D103": ["JurisLean.FullMath.Numeric.succDay_ordinal_mono",
             "JurisLean.Seams.UnifiedCalendar.toEpochDay_inj"],
}


def _binding_row(dem, required):
    """Template for the controller's BINDINGS.json back-fill
    (DEMAND:D095–D103 rows).  Passes completion.validate_binding as-is."""
    return {
        "id": f"DEMAND:{dem}",
        "theorem": required["theorem"],
        "contract": required["contract"],
        "proof_mode": "KERNEL_CONTRACT_PROOF",
        "formal_scope": "Group-11 money/time demand instance in the "
                        "shared semantic framework: this item's own "
                        "contract semantics plus the registered "
                        "calendar component (month-ordinal monotonicity "
                        "under same-month succession — integer day "
                        "order, leap years and month lengths from the "
                        "unified calendar), with its adverse case "
                        "executed as a negative test.",
        "independent_semantics": _SEMANTICS[dem],
        "algorithm": "tools/full_math/implementation/timeamount_ref.py "
                     f"{_ENTRY[dem]} computes the intermediate result "
                     f"from structured input (calendar surface consumed "
                     f"from calendar_ref, the mirror of "
                     f"JurisLean.Seams.UnifiedCalendar); "
                     f"timeamount_check.check_{dem} re-derives the "
                     f"contract independently against the stdlib "
                     f"datetime oracle.",
        "observation_contract": "Inputs are the declared structures "
                                "(calendar dates with exact integer day "
                                "counts, Fraction bases/rates/ratios "
                                "and amounts, one-step benchmark policy "
                                "tables, cash+stock consideration legs "
                                "with per-share prices and fx rates, "
                                "prepayment quotes with facility, "
                                "balance, ratio and trigger dates, "
                                "period specifications with anchor, "
                                "length, holiday table and roll fuel, "
                                "back-schedule deadlines with lead days "
                                "and floor dates, exposure rows with "
                                "four distinct kinds and a declared "
                                "risk function, obligation rows with "
                                "survival kinds and day periods, and "
                                "account rows with names, exact values "
                                "and exclusion lists); outputs are "
                                "exactly the contract quantities (the "
                                "segment interest values with the split "
                                "conservation and the waterfall "
                                "allocations, the as-of benchmark and "
                                "the confirmed-multiple applications "
                                "with the backfill divergence, the "
                                "dimensional consideration totals with "
                                "both rounding stages, the separated "
                                "prepayment quote with the "
                                "jointly-verified premium, the period "
                                "deadlines with the idempotent roll "
                                "and evidence-gated right, the "
                                "back-scheduled plans with the conflict "
                                "reports, the declared aggregation "
                                "against the mixed and double-counted "
                                "totals, the survival updates with the "
                                "ray-law verdicts, and the same-"
                                "definition adjustment against the "
                                "mixed-scope difference).",
        "external_assumptions": "Actual debt and expense documentation, "
                                "real benchmark publication data, price "
                                "sources and employee-identity facts, "
                                "repayment balances and projected "
                                "closing dates, arrival/knowledge/"
                                "performance event verification, "
                                "third-party processing durations and "
                                "availability, relevance/probability "
                                "and economic-loss evaluation, "
                                "subsequent performance and payment "
                                "facts, and statement truth, earnings "
                                "quality and audit judgment remain "
                                "external validation obligations, not "
                                "part of this registration.",
        "proof_sources": [
            "proofs/lean/juris_lean/JurisLean/FullMath/Contracts.lean",
            "proofs/lean/juris_lean/JurisLean/FullMath/Acceptance.lean",
        ],
        "implementation_sources": [
            "tools/full_math/implementation/timeamount_ref.py",
            "tools/full_math/implementation/timeamount_check.py",
        ],
        "test_ids": [
            "tools/full_math/implementation_tests::"
            "test_timeamount_group11.py::"
            f"test_demand_positive[{dem}]",
            "tools/full_math/implementation_tests::"
            "test_timeamount_group11.py::"
            f"test_demand_counterexample[{dem}]",
            "tools/full_math/implementation_tests::"
            "test_timeamount_group11.py::"
            "test_downstream_pipeline_consumes_timeamount",
        ],
        "negative_test_ids": [
            "tools/full_math/implementation_tests::"
            "test_timeamount_group11.py::"
            f"test_checker_rejects_tampered[{dem}]",
        ],
        "semantic_links": _SEMANTIC_LINKS[dem],
    }


@pytest.mark.parametrize("dem", DEMANDS)
def test_b11_binding_receipt(dem):
    """Synthetic receipt: the binding row for DEMAND:D1XX passes
    completion.validate_binding against the real repository files."""
    required = _REQUIREMENTS[f"DEMAND:{dem}"]
    C.validate_binding(_binding_row(dem, required), required, repo=REPO)


@pytest.mark.parametrize("dem", DEMANDS)
def test_b11_binding_receipt_negative(dem):
    """A tampered receipt (swapped theorem) is rejected."""
    required = _REQUIREMENTS[f"DEMAND:{dem}"]
    row = dict(_binding_row(dem, required))
    row["theorem"] = "JurisLean.FullMath.Acceptance.nonexistent_demand"
    with pytest.raises(C.EvidenceError):
        C.validate_binding(row, required, repo=REPO)
