"""W2-A batch B10 acceptance tests: D087-D094, group 10 企业调查、诉讼
与执行数据.

Six pieces per demand (docs/full-math/W2B_CLASSIFICATION.md §5.4):

1. Lean contract  — Contracts.demand_D087..D094 restated as this item's own
   semantics (verified by CI; the registration-format tests live in
   test_registration_bindings.py).
2. Python entry   — tools/full_math/implementation/data_ref.py per-item
   entries computing the intermediate result from real structured input.
3. Independent checker — data_check.py re-derives the contract inline;
   no witness callbacks, no expectations from the main implementation.
4. Downstream consumption — unified.pipeline run_case / step_event /
   run_trace consume the enterprise-data results through the adapters
   in data_ref (build_case_input / build_environment /
   data_trace_events).
5. Positive and adverse cases — the ALL_134 counterexample field of each
   demand is executed with per-item expectations.
6. Synthetic receipt — completion.validate_binding rows for
   DEMAND:D087-D094 (the ``_binding_row`` template below is ready for
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

from tools.full_math.implementation import data_check as K  # noqa: E402
from tools.full_math.implementation import data_ref as R  # noqa: E402
import completion as C  # noqa: E402

# Pipeline-facing names are imported INSIDE the downstream test, not at
# module level: other suites in this directory re-resolve the shared bare
# `unified` tree at their own import time, and call-time imports are the
# only bindings that always match the lazy in-function imports inside
# unified.pipeline/process (data_ref's adapters already import lazily).

DEMANDS = ("D087", "D088", "D089", "D090", "D091", "D092", "D093", "D094")

_LIT_ROWS = (("acme-co", "case-1", "defendant", Fraction(900, 1),
              "judgment-text-1"),
             ("acme-co", "case-1", "defendant", Fraction(900, 1),
              "judgment-text-1-bis"),
             ("acme-co", "case-2", "plaintiff", Fraction(400, 1),
              "judgment-text-2"))


# ---------------------------------------------------------------------------
# 2/3/5 — entry + independent checker, positive and adverse (per item)
# ---------------------------------------------------------------------------


def _run_D087():
    """混用更名前名称和另一同名公司的资本（ALL_134 反例字段）."""
    out = R.registry_join((), "acme-co", "capital")
    ok, reasons = K.check_D087((), "acme-co", "capital", out)
    return ok, reasons, out


def _run_D088():
    """循环持股反复乘加产生虚假权益（ALL_134 反例字段）."""
    out = R.penetration(Fraction(3, 5), Fraction(1, 2))
    ok, reasons = K.check_D088(Fraction(3, 5), Fraction(1, 2), out)
    return ok, reasons, out


def _run_D089():
    """同一案件不同文书重复算作多案（ALL_134 反例字段）."""
    out = R.litigation_join(_LIT_ROWS, "acme-co")
    ok, reasons = K.check_D089(_LIT_ROWS, "acme-co", out)
    return ok, reasons, out


def _run_D090():
    """终本不自动等于永久失信或债务消灭（ALL_134 反例字段）."""
    out = R.enforcement_statuses("acme-co")
    ok, reasons = K.check_D090("acme-co", out)
    return ok, reasons, out


def _run_D091():
    """把未履行额与执行标的加成总债务（ALL_134 反例字段）."""
    out = R.execution_amounts(Fraction(9, 2), Fraction(11, 2),
                              Fraction(7, 2))
    ok, reasons = K.check_D091(Fraction(9, 2), Fraction(11, 2),
                               Fraction(7, 2), out)
    return ok, reasons, out


def _run_D092():
    """已撤销处罚继续标为当前有效违法结论（ALL_134 反例字段）."""
    out = R.penalty_records()
    ok, reasons = K.check_D092(out)
    return ok, reasons, out


def _run_D093():
    """区划改名不得制造两个不同法院或错用旧送达地址（ALL_134 反例字段）."""
    out = R.court_directory()
    ok, reasons = K.check_D093(out)
    return ok, reasons, out


def _run_D094():
    """服务某上市公司不能推出代理该公司全部案件（ALL_134 反例字段）."""
    out = R.law_firm_query()
    ok, reasons = K.check_D094(out)
    return ok, reasons, out


_POSITIVE = {"D087": _run_D087, "D088": _run_D088, "D089": _run_D089,
             "D090": _run_D090, "D091": _run_D091, "D092": _run_D092,
             "D093": _run_D093, "D094": _run_D094}


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
    if dem == "D087":
        registry = out
        # 双键 join：同键同时点命中；更名键/同名他公司键/异时点皆 none；
        # 两时点快照值不同即不同记录
        assert registry["hit_t0"] == "1000-fen"
        assert registry["hit_t1"] == "2000-fen"
        assert registry["renamed_key_miss"] is None
        assert registry["namesake_key_miss"] is None
        assert registry["other_time_miss"] is None
        assert registry["different_times_different_records"] is True
    elif dem == "D088":
        pen = out
        # 边类型分立：holding 连接、service 不连接；链复合 3/10；闭环 0；
        # 控制独立（3/10 无控制）
        assert pen["holding_hop"] is True
        assert pen["service_hop_miss"] is False
        assert pen["chain_stake"] == Fraction(3, 10)
        assert pen["empty_chain"] == Fraction(1)
        assert pen["cyclic_stake"] == Fraction(0)
        assert pen["control_half"] is True
        assert pen["control_quarter"] is False
        assert pen["control_of_chain"] is False
        assert pen["chain_and_control_separate"] is True
    elif dem == "D089":
        lit = out
        # 键连接保留原文；同案双文书只入一次；异案/异企业查询为 none
        assert lit["keyed_case_1"] == ("defendant", Fraction(900, 1),
                                       "judgment-text-1")
        assert lit["case_keys"] == ("case-2", "case-1")
        assert lit["case_keys"].count("case-1") == 1
        assert lit["other_case_miss"] is None
        assert lit["other_ent_miss"] is None
        assert lit["docs_are_distinct_records"] is True
    elif dem == "D090":
        enf = out
        # 四类互异；终本行只答终本查询；失信/限高/债务消灭皆 none
        assert enf["pairwise_distinct"] is True
        assert enf["terminated_hit"] is True
        assert enf["dishonest_miss"] is None
        assert enf["restrict_miss"] is None
        assert enf["debt_cleared_miss"] is None
        assert enf["kind_changes_record"] is True
    elif dem == "D091":
        amt = out
        # 四金额类互异；target=11/2 不含 unpaid=9/2；跨类和 10 不是任何
        # 单类聚合输出
        assert amt["tags_pairwise_distinct"] is True
        assert amt["unpaid_total"] == Fraction(9, 2)
        assert amt["target_total"] == Fraction(11, 2)
        assert amt["other_debt_never_merges"] is True
        assert amt["cross_kind_sum"] == Fraction(10, 1)
        assert amt["cross_sum_is_no_kind_total"] is True
    elif dem == "D092":
        pen = out
        # 已撤销恒不当前有效；溯源链四字段同记录；当前集不含撤销行
        assert pen["revoked_current"] is False
        assert pen["effective_current"] is True
        assert pen["revoked_provenance"] == ("mkt-auth", "acme-co",
                                             "false-ad", 20260101)
        assert pen["current_of_acme"] == (pen["effective"],)
        assert pen["tags_distinct"] is True
    elif dem == "D093":
        directory = out
        # 各时点命中各自版本行；改名一法院两版本；旧地址不越窗；异代码/
        # 窗外为 none
        assert directory["at_5"] == directory["old"]
        assert directory["at_15"] == directory["new"]
        assert directory["old_not_at_15"] is True
        assert directory["other_code_miss"] is None
        assert directory["after_window_miss"] is None
        assert directory["old_only_miss"] is None
        assert directory["one_court_two_versions"] is True
    elif dem == "D094":
        firm = out
        # 两表各自回答；交叉喂入皆 false；逆向推断只过 case-1 边
        assert firm["rep_hit"] is True
        assert firm["service_table_does_not_answer_rep"] is False
        assert firm["service_hit"] is True
        assert firm["rep_table_does_not_answer_service"] is False
        assert firm["inferred_case_1"] is True
        assert firm["not_inferred_case_2"] is False
        assert firm["not_inferred_case_3"] is False


@pytest.mark.parametrize("dem", DEMANDS)
def test_checker_rejects_tampered(dem):
    """The independent checker must fail a tampered intermediate result
    (the checker, not the entry, is the judge of the contract)."""
    ok, _reasons, out = _POSITIVE[dem]()
    assert ok  # sanity: the honest result passes its own checker
    if dem == "D087":
        tampered = dict(out)
        tampered["renamed_key_miss"] = "1000-fen"  # pre-rename name mixed
        bad, reasons = K.check_D087((), "acme-co", "capital", tampered)
    elif dem == "D088":
        tampered = dict(out)
        tampered["cyclic_stake"] = Fraction(3, 10)  # phantom equity
        bad, reasons = K.check_D088(Fraction(3, 5), Fraction(1, 2),
                                    tampered)
    elif dem == "D089":
        tampered = dict(out)
        tampered["case_keys"] = ("case-2", "case-1", "case-1")  # 2 cases
        bad, reasons = K.check_D089(_LIT_ROWS, "acme-co", tampered)
    elif dem == "D090":
        tampered = dict(out)
        tampered["dishonest_miss"] = True  # termination implies dishonesty
        bad, reasons = K.check_D090("acme-co", tampered)
    elif dem == "D091":
        tampered = dict(out)
        tampered["target_total"] = Fraction(10, 1)  # unpaid added in
        bad, reasons = K.check_D091(Fraction(9, 2), Fraction(11, 2),
                                    Fraction(7, 2), tampered)
    elif dem == "D092":
        pen = out
        tampered = dict(pen)
        tampered["current_of_acme"] = (pen["effective"], pen["revoked"])
        bad, reasons = K.check_D092(tampered)
    elif dem == "D093":
        directory = out
        tampered = dict(directory)
        tampered["at_15"] = directory["old"]  # old address after window
        bad, reasons = K.check_D093(tampered)
    elif dem == "D094":
        tampered = dict(out)
        tampered["not_inferred_case_2"] = True  # service implies all
        bad, reasons = K.check_D094(tampered)
    assert not bad, f"{dem} checker accepted a tampered result: {reasons}"


# ---------------------------------------------------------------------------
# per-demand adverse specifics beyond the shared parametrized set
# ---------------------------------------------------------------------------


def test_D087_declared_rows_join_under_their_own_keys():
    """声明输入行也按键联接：他公司行不为 acme-co 键作答."""
    rows = (("beta-co", "capital", 0, "3000-fen"),)
    out = R.registry_join(rows, "acme-co", "capital")
    assert out["hit_t0"] == "1000-fen"
    assert out["hit_t1"] == "2000-fen"
    ok, reasons = K.check_D087(rows, "acme-co", "capital", out)
    assert ok, reasons


def test_D088_control_boundary_and_service_edges():
    """控制判决恰以 1/2 为界；service 边表自身在 holding 查询下不连接."""
    edges = (("sub-co", "mid-co", "service"),)
    assert R.pen_hop(edges, "sub-co", "mid-co", "holding") is False
    assert R.pen_hop(edges, "sub-co", "mid-co", "service") is True
    assert R.control_of(Fraction(1, 2)) is True
    assert R.control_of(Fraction(2, 5)) is False
    assert R.chain_stake("sub-co", (("sub-co", "top-co", Fraction(3, 5)),)) \
        == Fraction(3, 5)


def test_D089_two_distinct_cases_both_collected():
    """不同案件各自入册（去重只对同案多文书，不吞不同案）."""
    out = R.litigation_join(_LIT_ROWS, "acme-co")
    assert "case-1" in out["case_keys"]
    assert "case-2" in out["case_keys"]
    assert out["keyed_case_1"][2].startswith("judgment-text-1")
    ok, reasons = K.check_D089(_LIT_ROWS, "acme-co", out)
    assert ok, reasons


def test_D090_records_compose_by_kind():
    """补一行失信记录后失信查询命中（按类存放，不混读）."""
    rows = (("acme-co", R.EC_TERMINATED, True),
            ("acme-co", R.EC_DISHONEST, True))
    assert R.ec_of(rows, "acme-co", R.EC_DISHONEST) is True
    assert R.ec_of(rows, "acme-co", R.EC_RESTRICT_HIGH) is None
    assert R.ec_of(rows, "beta-co", R.EC_TERMINATED) is None


def test_D091_paid_kind_totals_its_own_rows():
    """已付额类只累计已付行；无已付行时该类总额为 0."""
    rows = (("debt-1", R.AMT_UNPAID, Fraction(9, 2)),
            ("debt-1", R.AMT_PAID, Fraction(5, 2)))
    assert R.amt_total_of(rows, "debt-1", R.AMT_PAID) == Fraction(5, 2)
    assert R.amt_total_of(rows, "debt-1", R.AMT_UNPAID) == Fraction(9, 2)
    assert R.amt_total_of(rows, "debt-1", R.AMT_CASE) == Fraction(0)


def test_D092_effective_row_provenance_rides_along():
    """生效行的溯源链读自身字段（机关/主体/行为/日期）."""
    out = R.penalty_records()
    assert R.penalty_provenance(out["effective"]) \
        == ("mkt-auth", "acme-co", "price-fraud", 20260202)
    assert R.current_penalties(out["rows"], "beta-co") == ()


def test_D093_returned_row_carries_the_whole_witness():
    """命中行携带机关/地址/区划与窗口两端（中间见证不丢）."""
    out = R.court_directory()
    row = out["at_15"]
    assert row[1] == "court-0101"
    assert row[2] == "addr-new-1"
    assert row[3] == "chaoyang-district"
    assert (row[4], row[5]) == (11, 20)
    assert out["at_5"][4:6] == (0, 10)


def test_D094_partial_key_matches_do_not_answer():
    """案件键或律所键单侧匹配都不作答（双字段键全匹配才命中）."""
    rep_rows = (("acme-case-2", "law-b"),)
    assert R.rep_edge_of(rep_rows, "acme-case-1", "law-a") is False
    assert R.rep_edge_of(rep_rows, "acme-case-2", "law-a") is False
    assert R.rep_edge_of(rep_rows, "acme-case-2", "law-b") is True
    service_rows = (("law-b", "beta-co"),)
    assert R.served_by(service_rows, "law-a", "beta-co") is False
    assert R.served_by(service_rows, "law-b", "acme-co") is False
    assert R.served_by(service_rows, "law-b", "beta-co") is True


# ---------------------------------------------------------------------------
# 4 — downstream consumption: run_case / step_event / run_trace
# ---------------------------------------------------------------------------


def test_downstream_pipeline_consumes_data():
    """run_case consumes the CaseInput assembled from the enterprise-data
    results (the unpaid execution amount and the currently effective
    penalty supply the issue, the perpetual-dishonesty proposition stays
    awaiting — never written, and the only quantities are the unpaid and
    target totals as two distinct kinds that never merge); run_trace
    consumes the versioned court-directory witness as an evidence event
    plus the exact execution installment."""
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

    intake = R.build_data_intake()
    case = R.build_case_input(intake)
    env = R.build_environment(intake)

    # the assembled carriers are exactly the data outputs
    assert case.issues == ("ENTERPRISE_DILIGENCE",)
    assert case.claims[0].claimant == "creditor"
    assert case.claims[0].respondent == "acme-co"
    # D092: the revoked penalty is a defense, and the perpetual-dishonesty
    # proposition stays awaiting — never written
    assert case.defenses[0].defense_id == "def-revoked"
    assert case.defenses[0].basis == "penalty_revoked"
    assert case.defenses[0].target_claims == ("c0",)
    standings = {(f.proposition.predicate, f.standing.name)
                 for f in case.fact_records}
    assert ("execution-unpaid", "ADMITTED_POSITIVE") in standings
    assert ("penalty-current", "ADMITTED_POSITIVE") in standings
    assert ("perpetual-dishonesty", "AWAITING_ADMISSION") in standings
    # D091: the only quantities are the unpaid and target totals — two
    # distinct kinds, never one merged 'total debt'
    assert [q.value for q in case.quantities] == [Fraction(9, 2),
                                                  Fraction(11, 2)]
    assert {q.basis_kind for q in case.quantities} == {"execution-unpaid",
                                                       "execution-target"}

    run = run_case(case, env)
    assert run.status is RunStatus.COMPLETE
    assert run.failures == ()
    judgments = run.judgments_of("c0")
    assert judgments and Judgment.ESTABLISHED in judgments

    # trace: the versioned court-directory witness becomes an evidence
    # event; the execution payment lands as one exact installment (9/2)
    events = R.data_trace_events(intake)
    assert [e.event.event_id for e in events[:1]] == ["ev-court-version"]
    final, notes = run_trace(case.initial_state, events, env)
    assert "ev:ev-court-version" in [e.evidence_id for e in final.evidence]
    event_ids = [e.event_id for e in final.events]
    assert "pay-execution-9/2" in event_ids
    assert gross_of(final, "EXECUTION_UNPAID") == Fraction(9, 2)
    assert gross_of(final, "EXECUTION_TARGET") == Fraction(0)
    allocated = [e for e in final.ledger
                 if e.kind.name == "GROSS_ALLOCATED"
                 and e.basis_key == "EXECUTION_UNPAID"]
    assert sorted(e.amount for e in allocated) == [Fraction(9, 2)]
    assert notes  # the step relation actually produced observations

    # step_event alone: one step, exactly the event's own semantics
    one = step_event(case.initial_state, events[0], env)
    assert [e.evidence_id for e in one.next_state.evidence] == \
        ["ev:ev-court-version"]
    assert one.next_env is env

    # the data decisions stay on the bundle: the registry snapshot split
    # (D087), the cycle-guarded penetration (D088), the deduplicated
    # case roster (D089), the termination inferring no dishonesty (D090),
    # the kind-segregated amounts (D091), the revoked penalty staying
    # non-current (D092), the versioned directory (D093), and the
    # service-not-representation verdict (D094)
    assert intake["registry"]["different_times_different_records"] is True
    assert intake["penetration"]["cyclic_stake"] == Fraction(0)
    assert intake["litigation"]["case_keys"] == ("case-2", "case-1")
    assert intake["enforcement"]["dishonest_miss"] is None
    assert intake["amounts"]["target_excludes_unpaid"] is True
    assert intake["penalties"]["revoked_current"] is False
    assert intake["directory"]["one_court_two_versions"] is True
    assert intake["firm"]["not_inferred_case_2"] is False


# ---------------------------------------------------------------------------
# 6 — synthetic receipts through completion.validate_binding
# ---------------------------------------------------------------------------

_REQUIREMENTS = {
    r["id"]: r
    for r in json.loads((SPEC / 'REQUIREMENTS.json').read_text(encoding='utf-8'))
}

_SEMANTICS = {
    "D087": "the multi-table registry join is keyed on the (subject "
            "key, valid time) pair: a same-key same-time lookup hits "
            "the row's own value; a renamed key, a same-name other "
            "company's key or a different validity time never answers, "
            "and different snapshot values are different records.",
    "D088": "penetration is a typed-edge graph query: a holding edge "
            "connects the two parties while the same parties under a "
            "service edge type never connect; the holding chain "
            "compounds its own edge ratios (empty chain = the entity "
            "itself, 1) with a cycle guard — a chain whose last edge "
            "re-enters the start compounds to exactly 0 — and control "
            "is a separate boolean verdict on the compounded stake.",
    "D089": "enterprise, case, role, amount and the original text are "
            "read from one keyed row: the (enterprise, case) double-key "
            "lookup carries the row's own text verbatim and rows of "
            "another case or another enterprise never answer; case keys "
            "are deduplicated per enterprise so the same case under two "
            "documents is one case, while different documents remain "
            "different records.",
    "D090": "restriction on high consumption, dishonesty listing, "
            "termination of this execution round and debt extinction "
            "are four distinct typed procedure tags; records are keyed "
            "by (subject, kind), so a termination row never answers a "
            "dishonesty, restriction or debt-extinction query — the "
            "statuses never implicitly infer one another.",
    "D091": "case amount, execution target, unfulfilled amount and "
            "paid amount are distinct typed quantity kinds; the "
            "aggregation is keyed on (debt-item key, amount kind), "
            "rows of other keys or other kinds never enter, and the "
            "cross-kind sum is not the output of any single-kind "
            "aggregation.",
    "D092": "an administrative-penalty record carries authority, "
            "subject, conduct, date and its status tag on one record: "
            "the current-validity verdict reads the record's own "
            "status (a revoked decision never reads as a current "
            "violation conclusion), and the subject's currently "
            "effective penalties never include revoked rows.",
    "D093": "the code-organ-address-district join is versioned: rows "
            "match on the court code AND the query time inside the "
            "row's validity window, returning the whole matched row "
            "(no intermediate witness lost); a district rename keeps "
            "one court with two versioned rows, and an out-of-window "
            "time or another code never answers.",
    "D094": "case-representation edges and law-firm service records "
            "cite their own original tables (feeding one table to the "
            "other's query misses), and the reverse inference passes "
            "only through an original representation edge for the very "
            "case — serving a client never implies representing that "
            "client's other cases.",
}

_ENTRY = {
    "D087": "reg_snapshot/registry_join",
    "D088": "pen_hop/chain_stake/control_of/penetration",
    "D089": "case_row_of/key_seen/case_keys_of/litigation_join",
    "D090": "ec_of/enforcement_statuses",
    "D091": "amt_total_of/execution_amounts",
    "D092": "penalty_current/penalty_provenance/current_penalties/"
            "penalty_records",
    "D093": "organ_row_at/court_directory",
    "D094": "rep_edge_of/served_by/infers_all_cases/law_firm_query",
}


def _binding_row(dem, required):
    """Template for the controller's BINDINGS.json back-fill
    (DEMAND:D087–D094 rows).  Passes completion.validate_binding as-is."""
    return {
        "id": f"DEMAND:{dem}",
        "theorem": required["theorem"],
        "contract": required["contract"],
        "proof_mode": "KERNEL_CONTRACT_PROOF",
        "formal_scope": "Group-10 enterprise-data demand instance in the "
                        "shared semantic framework: this item's own "
                        "contract semantics plus the registered query "
                        "aggregation component (existential answers "
                        "are witnessed by membership — every query "
                        "result carries its source-row witness), with "
                        "its adverse case executed as a negative test.",
        "independent_semantics": _SEMANTICS[dem],
        "algorithm": f"tools/full_math/implementation/data_ref.py "
                     f"{_ENTRY[dem]} computes the intermediate result "
                     f"from structured input; data_check.check_{dem} "
                     f"re-derives the contract independently.",
        "observation_contract": "Inputs are the declared structures "
                                "(registry snapshot rows keyed by "
                                "subject and valid time, typed "
                                "penetration edges with holding ratios, "
                                "litigation rows keyed by enterprise "
                                "and case with roles, exact amounts and "
                                "original texts, enforcement-procedure "
                                "records keyed by subject and typed "
                                "kind, execution-amount rows keyed by "
                                "debt item and typed amount kind, "
                                "penalty records with authority, "
                                "conduct, date and status tags, "
                                "versioned court-directory rows with "
                                "validity windows, and representation/"
                                "service relation tables); outputs are "
                                "exactly the contract quantities (the "
                                "keyed snapshot join with its miss "
                                "witnesses, the typed hop and the "
                                "cycle-guarded compounded stake with "
                                "its separate control verdict, the "
                                "keyed case row with verbatim text and "
                                "the deduplicated case roster, the "
                                "kind-keyed procedure lookups, the "
                                "kind-and-debt-keyed amount totals "
                                "with the cross-kind-sum witness, the "
                                "status-tagged penalty verdicts with "
                                "their provenance chains, the "
                                "whole-row versioned directory lookups, "
                                "and the table-citing representation "
                                "and service verdicts with the "
                                "reverse-inference witnesses).",
        "external_assumptions": "The registry data's truth and "
                                "timeliness, beneficial-owner and "
                                "nominee-holder investigations, court "
                                "record coverage and name-relation "
                                "verification, enforcement-record "
                                "updates and releases, official "
                                "penalty verification and appeal "
                                "status, current court addresses and "
                                "office moves, and representation "
                                "authenticity and privacy permissions "
                                "remain external validation "
                                "obligations, not part of this "
                                "registration.",
        "proof_sources": [
            "proofs/lean/juris_lean/JurisLean/FullMath/Contracts.lean",
            "proofs/lean/juris_lean/JurisLean/FullMath/Acceptance.lean",
        ],
        "implementation_sources": [
            "tools/full_math/implementation/data_ref.py",
            "tools/full_math/implementation/data_check.py",
        ],
        "test_ids": [
            "tools/full_math/implementation_tests::"
            "test_data_group10.py::"
            f"test_demand_positive[{dem}]",
            "tools/full_math/implementation_tests::"
            "test_data_group10.py::"
            f"test_demand_counterexample[{dem}]",
            "tools/full_math/implementation_tests::"
            "test_data_group10.py::"
            "test_downstream_pipeline_consumes_data",
        ],
        "negative_test_ids": [
            "tools/full_math/implementation_tests::"
            "test_data_group10.py::"
            f"test_checker_rejects_tampered[{dem}]",
        ],
        "semantic_links": [
            "JurisLean.FullMath.Logic.exists_extension_witnessed",
        ],
    }


@pytest.mark.parametrize("dem", DEMANDS)
def test_b10_binding_receipt(dem):
    """Synthetic receipt: the binding row for DEMAND:D0XX passes
    completion.validate_binding against the real repository files."""
    required = _REQUIREMENTS[f"DEMAND:{dem}"]
    C.validate_binding(_binding_row(dem, required), required, repo=REPO)


@pytest.mark.parametrize("dem", DEMANDS)
def test_b10_binding_receipt_negative(dem):
    """A tampered receipt (swapped theorem) is rejected."""
    required = _REQUIREMENTS[f"DEMAND:{dem}"]
    row = dict(_binding_row(dem, required))
    row["theorem"] = "JurisLean.FullMath.Acceptance.nonexistent_demand"
    with pytest.raises(C.EvidenceError):
        C.validate_binding(row, required, repo=REPO)
