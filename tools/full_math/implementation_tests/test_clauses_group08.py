"""W2-A batch B08 acceptance tests: D065-D076, group 08 合同条款与权利义务审核.

Six pieces per demand (docs/full-math/W2B_CLASSIFICATION.md §5.4):

1. Lean contract  — Contracts.demand_D065..D076 restated as this item's own
   semantics (verified by CI; the registration-format tests live in
   test_registration_bindings.py).
2. Python entry   — tools/full_math/implementation/clauses_ref.py per-item
   entries computing the intermediate result from real structured input.
3. Independent checker — clauses_check.py re-derives the contract inline;
   no witness callbacks, no expectations from the main implementation.
4. Downstream consumption — unified.pipeline run_case / step_event /
   run_trace consume the clause results through the adapters in
   clauses_ref (build_case_input / build_environment /
   clauses_trace_events).
5. Positive and adverse cases — the ALL_134 counterexample field of each
   demand is executed with per-item expectations.
6. Synthetic receipt — completion.validate_binding rows for DEMAND:D065-D076
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

from tools.full_math.implementation import clauses_check as K  # noqa: E402
from tools.full_math.implementation import clauses_ref as R  # noqa: E402
import completion as C  # noqa: E402

# Pipeline-facing names are imported INSIDE the downstream test, not at
# module level: other suites in this directory re-resolve the shared bare
# `unified` tree at their own import time, and call-time imports are the
# only bindings that always match the lazy in-function imports inside
# unified.pipeline/process (clauses_ref's adapters already import lazily).

DEMANDS = ("D065", "D066", "D067", "D068", "D069", "D070", "D071", "D072",
           "D073", "D074", "D075", "D076")


# ---------------------------------------------------------------------------
# 2/3/5 — entry + independent checker, positive and adverse (per item)
# ---------------------------------------------------------------------------


def _run_D065():
    """签订日不自动等于生效日；到期不自动抹去存续义务（ALL_134 反例字段）."""
    out = R.contract_state_events(True, False, False,
                                  ("settlement", "confidentiality"))
    expired = R.contract_state_events(True, True, True, ("settlement",))
    draft = R.contract_state_events(False, False, False, ())
    ok, r1 = K.check_D065(True, False, False, ("settlement",
                                               "confidentiality"), out)
    ok2, r2 = K.check_D065(True, True, True, ("settlement",), expired)
    ok3, r3 = K.check_D065(False, False, False, (), draft)
    return ok and ok2 and ok3, r1 + r2 + r3, (out, expired, draft)


def _run_D066():
    """当事人在某州设立不自动推定该州法管全部合同（ALL_134 反例字段）."""
    out = R.governing_law((("NY-law", False), ("DE-law", True)), "NY-law")
    ok_path = R.governing_law((("DE-law", True),), "DE-law")
    ok, r1 = K.check_D066((("NY-law", False), ("DE-law", True)), "NY-law",
                          out)
    ok2, r2 = K.check_D066((("DE-law", True),), "DE-law", ok_path)
    return ok and ok2, r1 + r2, (out, ok_path)


def _run_D067():
    """排他义务不是自动转让排他知识产权（ALL_134 反例字段）."""
    rows = (("licensee", "sublicense", "EU", "2026-01-01", "consent",
             R.EFFECT_EXCLUSIVE_OBLIGATION),)
    out = R.restriction_rows(rows, "licensee", "sublicense", "EU",
                             "2026-01-01", "consent")
    ok, reasons = K.check_D067(rows, "licensee", "sublicense", "EU",
                               "2026-01-01", "consent", out)
    return ok, reasons, out


def _run_D068():
    """正向主条款命中后不得跳过后文除外事项（ALL_134 反例字段）."""
    out = R.priority_scope_eval(True, True, False, "cl-9", "cl-7", 0)
    in_scope = R.priority_scope_eval(True, True, False, "cl-7", "cl-7", 0)
    ok, r1 = K.check_D068(True, True, False, "cl-9", "cl-7", 0, out)
    ok2, r2 = K.check_D068(True, True, False, "cl-7", "cl-7", 0, in_scope)
    return ok and ok2, r1 + r2, (out, in_scope)


def _run_D069():
    """发出停止续展通知不能直接终止当前履行期（ALL_134 反例字段）."""
    out = R.termination_event_chain((False, False, False, False),
                                    (R.EV_EXERCISE, R.EV_NOTICE,
                                     R.EV_NONRENEW))
    ok, reasons = K.check_D069((False, False, False, False),
                               (R.EV_EXERCISE, R.EV_NOTICE,
                                R.EV_NONRENEW), out)
    return ok, reasons, out


def _run_D070():
    """同一交易事实不可用统一阈值覆盖全部合同（ALL_134 反例字段）."""
    out = R.change_of_control(Fraction(60))
    ok, reasons = K.check_D070(Fraction(60), R.COC_CONTRACTS, out)
    return ok, reasons, out


def _run_D071():
    """只失去排他性时删除全部使用许可，应拦截（ALL_134 反例字段）."""
    out = R.license_conversion("grant-2024")
    ok, reasons = K.check_D071("grant-2024", out)
    return ok, reasons, out


def _run_D072():
    """有许可不等于成为权利人；关联方不因集团标签自动获许可
    （ALL_134 反例字段）."""
    out = R.ip_relations(((R.REL_LIC, "grant-2024"),), "grant-2024")
    ok, reasons = K.check_D072(((R.REL_LIC, "grant-2024"),), "grant-2024",
                               out)
    return ok, reasons, out


def _run_D073():
    """永久许可不自动等于不可撤销且无限量（ALL_134 反例字段）."""
    out = R.license_attributes(True, True, False, 1000)
    ok, reasons = K.check_D073(True, True, False, 1000, out)
    return ok, reasons, out


def _run_D074():
    """销售额分成误用利润基数或跨期重复汇总（ALL_134 反例字段）."""
    out = R.fee_lines()
    ok, reasons = K.check_D074(Fraction(1, 10),
                               ("2026-Q1", "CNY", Fraction(3000)),
                               ("2026-Q2", "CNY", Fraction(5000)), out)
    return ok, reasons, out


def _run_D075():
    """对保密例外也机械套一般cap，或将保险限额当责任上限（ALL_134 反例
    字段）."""
    items = (("confidentiality", True, Fraction(1500000)),
             ("general", False, Fraction(1500000)))
    out = R.indemnity_classification(items)
    ok, reasons = K.check_D075(items, Fraction(1000000), out)
    return ok, reasons, out


def _run_D076():
    """合同状态终止不得全量删除结算清理等存续效果（ALL_134 反例字段）."""
    rows = (("settlement", "net out open orders", True),
            ("audit", "books for 2y", True),
            ("escrow", "source escrow", True),
            ("third-party", "beneficiary rights", True),
            ("terminating", "the termination itself", False))
    out = R.survival_rules(rows)
    ok, reasons = K.check_D076(rows, out)
    return ok, reasons, out


_POSITIVE = {"D065": _run_D065, "D066": _run_D066, "D067": _run_D067,
             "D068": _run_D068, "D069": _run_D069, "D070": _run_D070,
             "D071": _run_D071, "D072": _run_D072, "D073": _run_D073,
             "D074": _run_D074, "D075": _run_D075, "D076": _run_D076}


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
    if dem == "D065":
        state, expired, _draft = out
        # 签订而未生效是自己的状态，不等于生效态；到期后存续义务原样保留
        assert state["state"] == 1
        assert state["state"] != state["state_codes"]["effective"]
        assert expired["state"] == 3
        assert expired["surviving"] == ("settlement",)
        assert expired["carrier"][1] == ("settlement",)
    elif dem == "D066":
        governing, ok_path = out
        # 候选行冲突路径未声明 → 无最终判断；路径已声明 → 判断给出；
        # 候选表与判断分立两个载体
        assert governing["row"] == ("NY-law", False)
        assert governing["final"] is None
        assert ok_path["final"] == "DE-law"
        assert governing["candidate_carrier"] != governing["final_carrier"]
    elif dem == "D067":
        restrictions = out
        # 六轴逐字段保真；排他义务效力码 ≠ 排他知产转让效力码
        assert restrictions["readback"]["effect"] == "exclusive-obligation"
        assert restrictions["readback"]["effect"] != "exclusive-ip-transfer"
        assert restrictions["effect_codes_distinct"] is True
    elif dem == "D068":
        priority, in_scope = out
        # 主条款命中、例外在后 → 取例外层（1），不跳过；作用域外不改结果
        assert priority["priority"] == 1
        assert priority["priority"] != 0
        assert priority["scoped"] == 0      # cl-9 scope: no-op
        assert in_scope["scoped"] == 1      # cl-7 scope: exception applies
    elif dem == "D069":
        chain = out
        # 行使+通知+停止续展之后：终止生效仍为 False——当前履行期未终止
        assert chain["final"] == (True, True, False, True)
        assert chain["final"][2] is False
        assert chain["adverse_notice_only"] == (True, True, False, True)
    elif dem == "D070":
        coc = out
        # 同一事实 60：过 C-1(50)、不过 C-2(80)——统一阈值被拒绝
        assert coc["triggers"] == {"C-1": True, "C-2": False}
        assert coc["uniform_threshold_rejected"] is True
    elif dem == "D071":
        conversion = out
        # 转换后方式=非排他、许可原样；非排他≠终止；删除被拦截
        assert conversion["mode_out"] == "license_nonexclusive"
        assert conversion["grant_out"] == "grant-2024"
        assert conversion["nonexclusive_is_not_terminated"] is True
        assert conversion["deletion_intercepted"] is True
    elif dem == "D072":
        relations = out
        # 有许可行但无所有权行 → 有许可≠权利人；无关联方行 → 无授权
        assert relations["lic_grant"] == "grant-2024"
        assert relations["own_grant"] is None
        assert relations["aff_grant"] is None
        assert relations["license_is_not_ownership"] is True
        assert relations["pairwise_distinct"] is True
    elif dem == "D073":
        attributes = out
        # 永久且可撤销且限量 ≠ 永久且不可撤销且无限量
        assert attributes["record"] == (True, True, False, 1000)
        assert attributes["perpetual_not_irrevocable_unlimited"] is True
        assert attributes["cap_is_present"] is True
    elif dem == "D074":
        fees = out
        # 基数 100000 与误用利润基数 20000 按 1/10 给 10000 vs 2000；
        # 两期精确相加 8000，期间不同行不同
        assert fees["share_revenue_base"] == Fraction(10000)
        assert fees["share_profit_base"] == Fraction(2000)
        assert fees["base_misuse_detected"] is True
        assert fees["periods_distinct"] is True
        assert fees["exact_sum"] == Fraction(8000)
    elif dem == "D075":
        indemnity = out
        # 同一金额与cap下：carve-out 全通过 1500000，capped 截在 1000000；
        # 保险限额 5000000 不是责任上限 1000000
        assert indemnity["witness_carve"] == Fraction(1500000)
        assert indemnity["witness_capped"] == Fraction(1000000)
        assert indemnity["classification_detectable"] is True
        assert indemnity["insurance_is_not_the_cap"] is True
    elif dem == "D076":
        survival = out
        # 终止后存续载体=全部四类声明存续行；terminating 行不进入
        assert survival["survivors"] == ("settlement", "audit", "escrow",
                                         "third-party")
        assert survival["carrier_after_termination"] == \
            survival["survivors"]
        assert survival["not_bulk_deleted"] is True
        assert "terminating" not in survival["survivors"]


@pytest.mark.parametrize("dem", DEMANDS)
def test_checker_rejects_tampered(dem):
    """The independent checker must fail a tampered intermediate result
    (the checker, not the entry, is the judge of the contract)."""
    ok, _reasons, out = _POSITIVE[dem]()
    assert ok  # sanity: the honest result passes its own checker
    if dem == "D065":
        state, _expired, _draft = out
        tampered = dict(state)
        tampered["state"] = state["state_codes"]["effective"]
        bad, reasons = K.check_D065(True, False, False,
                                    ("settlement", "confidentiality"),
                                    tampered)
    elif dem == "D066":
        governing, _ok_path = out
        tampered = dict(governing)
        tampered["final"] = governing["chosen"]  # venue auto-decided
        bad, reasons = K.check_D066((("NY-law", False), ("DE-law", True)),
                                    "NY-law", tampered)
    elif dem == "D067":
        restrictions = out
        tampered = dict(restrictions)
        tampered["readback"] = dict(restrictions["readback"],
                                    effect="exclusive-ip-transfer")
        bad, reasons = K.check_D067(
            (("licensee", "sublicense", "EU", "2026-01-01", "consent",
              R.EFFECT_EXCLUSIVE_OBLIGATION),),
            "licensee", "sublicense", "EU", "2026-01-01", "consent",
            tampered)
    elif dem == "D068":
        priority, _in_scope = out
        tampered = dict(priority)
        tampered["priority"] = 0  # the later exception was skipped
        bad, reasons = K.check_D068(True, True, False, "cl-9", "cl-7", 0,
                                    tampered)
    elif dem == "D069":
        chain = out
        tampered = dict(chain)
        tampered["adverse_notice_only"] = (True, True, True, True)
        bad, reasons = K.check_D069((False, False, False, False),
                                    (R.EV_EXERCISE, R.EV_NOTICE,
                                     R.EV_NONRENEW), tampered)
    elif dem == "D070":
        coc = out
        tampered = dict(coc)
        tampered["triggers"] = {"C-1": True, "C-2": True}  # uniform
        bad, reasons = K.check_D070(Fraction(60), R.COC_CONTRACTS, tampered)
    elif dem == "D071":
        conversion = out
        tampered = dict(conversion)
        tampered["grant_out"] = ""  # the whole usage grant deleted
        tampered["grant_kept"] = False
        bad, reasons = K.check_D071("grant-2024", tampered)
    elif dem == "D072":
        relations = out
        tampered = dict(relations)
        tampered["aff_grant"] = "grant-2024"  # group label auto-licensed
        bad, reasons = K.check_D072(((R.REL_LIC, "grant-2024"),),
                                    "grant-2024", tampered)
    elif dem == "D073":
        attributes = out
        tampered = dict(attributes)
        tampered["record"] = (True, False, True, None)  # normalized away
        bad, reasons = K.check_D073(True, True, False, 1000, tampered)
    elif dem == "D074":
        fees = out
        tampered = dict(fees)
        tampered["share_revenue_base"] = Fraction(2000)  # profit base
        tampered["base_misuse_detected"] = False
        bad, reasons = K.check_D074(Fraction(1, 10),
                                    ("2026-Q1", "CNY", Fraction(3000)),
                                    ("2026-Q2", "CNY", Fraction(5000)),
                                    tampered)
    elif dem == "D075":
        indemnity = out
        tampered = dict(indemnity)
        tampered["witness_carve"] = Fraction(1000000)  # general cap also
        tampered["classification_detectable"] = False  # on the carve-out
        bad, reasons = K.check_D075(
            (("confidentiality", True, Fraction(1500000)),
             ("general", False, Fraction(1500000))),
            Fraction(1000000), tampered)
    elif dem == "D076":
        survival = out
        tampered = dict(survival)
        tampered["carrier_after_termination"] = ()  # bulk deletion
        bad, reasons = K.check_D076(
            (("settlement", "net out open orders", True),
             ("audit", "books for 2y", True),
             ("escrow", "source escrow", True),
             ("third-party", "beneficiary rights", True),
             ("terminating", "the termination itself", False)), tampered)
    assert not bad, f"{dem} checker accepted a tampered result: {reasons}"


# ---------------------------------------------------------------------------
# per-demand adverse specifics beyond the shared parametrized set
# ---------------------------------------------------------------------------


def test_D065_full_lifecycle_states():
    """draft→formed→effective→terminated 是四个互异状态码；空存续清单
    在草稿态合法."""
    draft = R.contract_state_events(False, False, False, ())
    formed = R.contract_state_events(True, False, False, ())
    effective = R.contract_state_events(True, True, False, ())
    terminated = R.contract_state_events(True, True, True, ())
    codes = {draft["state"], formed["state"], effective["state"],
             terminated["state"]}
    assert codes == {0, 1, 2, 3}
    assert draft["state"] != formed["state"] != effective["state"]
    for out in (draft, formed, effective, terminated):
        ok, reasons = K.check_D065(out is not draft, out is not draft
                                   and out is not formed,
                                   out is terminated, (), out)
        assert ok, reasons


def test_D066_conflict_path_preserved_and_separate():
    """路径已声明的候选给最终判断；候选载体与判断载体全程分立."""
    cands = (("NY-law", False), ("DE-law", True))
    out = R.governing_law(cands, "DE-law")
    assert out["final"] == "DE-law"
    assert out["candidate_carrier"] == cands
    assert out["final_carrier"] == {"judgment": "DE-law"}
    ok, reasons = K.check_D066(cands, "DE-law", out)
    assert ok, reasons


def test_D067_different_axis_is_a_different_row():
    """六轴任一不同即查不中（行为轴不同 → 无行）——轴独立."""
    rows = (("licensee", "sublicense", "EU", "2026-01-01", "consent",
             R.EFFECT_EXCLUSIVE_OBLIGATION),)
    out = R.restriction_rows(rows, "licensee", "distribute", "EU",
                             "2026-01-01", "consent")
    assert out["found"] is None
    assert out["readback"] is None
    ok, reasons = K.check_D067(rows, "licensee", "distribute", "EU",
                               "2026-01-01", "consent", out)
    assert ok, reasons


def test_D068_exception_of_exception_wins():
    """例外之例外(2)＞例外(1)＞主规则(0)，三级互异."""
    assert R.prio_eval(True, True, True) == 2
    assert R.prio_eval(True, True, False) == 1
    assert R.prio_eval(True, False, False) == 0
    assert R.prio_eval(False, False, False) == 0
    out = R.priority_scope_eval(True, True, True, "cl-7", "cl-7", 0)
    ok, reasons = K.check_D068(True, True, True, "cl-7", "cl-7", 0, out)
    assert ok, reasons


def test_D069_effective_needs_its_own_event():
    """终止生效只由自己的事件置位：通知事件不置生效，生效事件置位."""
    rec = (True, True, False, False)
    assert R.apply_event(rec, R.EV_NOTICE) == (True, True, False, False)
    assert R.apply_event(rec, R.EV_EFFECTIVE) == (True, True, True, False)
    out = R.termination_event_chain(rec, (R.EV_EFFECTIVE,))
    ok, reasons = K.check_D069(rec, (R.EV_EFFECTIVE,), out)
    assert ok, reasons


def test_D070_consequence_flags_verbatim():
    """通知/同意/终止三开关逐字保留（真真假的行原样出来）."""
    flags = (True, True, False)
    assert R.coc_consequences(flags) == (True, True, False)
    assert R.coc_consequences(flags) != (True, False, True)
    out = R.change_of_control(Fraction(10))  # below both thresholds
    assert out["triggers"] == {"C-1": False, "C-2": False}
    assert out["uniform_threshold_rejected"] is False
    ok, reasons = K.check_D070(Fraction(10), R.COC_CONTRACTS, out)
    assert ok, reasons


def test_D072_sublicense_row_is_not_a_license_grant():
    """只有再许可行时许可键查无授权——关系键不串."""
    out = R.ip_relations(((R.REL_SUB, "sub-grant"),), "sub-grant")
    assert out["lic_grant"] is None
    assert out["aff_grant"] is None
    assert out["own_grant"] is None
    ok, reasons = K.check_D072(((R.REL_SUB, "sub-grant"),), "sub-grant",
                               out)
    assert ok, reasons


def test_D073_unlimited_perpetual_license_reads_cap_none():
    """无限量（None）与限量（1000）是两个独立的用量属性值."""
    unlimited = R.license_attributes(True, False, True, None)
    assert unlimited["cap_is_present"] is False
    assert unlimited["record"][3] is None
    assert unlimited["record"] != (True, True, False, 1000)
    ok, reasons = K.check_D073(True, False, True, None, unlimited)
    assert ok, reasons


def test_D075_capped_class_is_clipped_at_cap():
    """general 类被截在 cap 处；分类先行后逐类套规则."""
    items = (("general", False, Fraction(1500000)),)
    out = R.indemnity_classification(items)
    assert out["classified"][0]["applied"] == Fraction(1000000)
    ok, reasons = K.check_D075(items, Fraction(1000000), out)
    assert ok, reasons


def test_D076_undeclared_kind_never_appears():
    """表内未声明的种类（merger-clause）永不凭空出现在存续载体."""
    rows = (("settlement", "net out open orders", True),
            ("audit", "books for 2y", True))
    out = R.survival_rules(rows)
    assert "merger-clause" not in out["survivors"]
    ok, reasons = K.check_D076(rows, out)
    assert ok, reasons


# ---------------------------------------------------------------------------
# 4 — downstream consumption: run_case / step_event / run_trace
# ---------------------------------------------------------------------------


def test_downstream_pipeline_consumes_clauses():
    """run_case consumes the CaseInput assembled from the clause results
    (the surviving grant supplies the issue, the D071 non-termination is
    a defense — never a written fact, the D069 notice-only termination
    proposition stays awaiting, and the only quantities are the two
    exact period fees plus the capped indemnity); run_trace consumes the
    surviving audit as an evidence event plus the two exact fee
    installments (3000 + 5000 = 8000, never a merged average number)."""
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

    intake = R.build_clauses_intake()
    case = R.build_case_input(intake)
    env = R.build_environment(intake)

    # the assembled carriers are exactly the clause outputs
    assert case.issues == ("LICENSE_COMPLIANCE",)
    assert case.claims[0].claimant == "licensor"
    assert case.claims[0].respondent == "licensee"
    # D071: the converted-not-terminated proposition is a defense, and
    # the D069 notice-only termination stays awaiting — never written
    assert case.defenses[0].defense_id == "def-nonterm"
    assert case.defenses[0].basis == "license_converted_not_terminated"
    assert case.defenses[0].target_claims == ("c0",)
    standings = {(f.proposition.predicate, f.standing.name)
                 for f in case.fact_records}
    assert ("grant-alive", "ADMITTED_POSITIVE") in standings
    assert ("usage-reported", "ADMITTED_POSITIVE") in standings
    assert ("terminated_by_notice", "AWAITING_ADMISSION") in standings
    # D074/D075: the only quantities are the two exact period fees and
    # the capped indemnity
    assert [q.value for q in case.quantities] == [Fraction(3000),
                                                  Fraction(5000),
                                                  Fraction(1000000)]

    run = run_case(case, env)
    assert run.status is RunStatus.COMPLETE
    assert run.failures == ()
    judgments = run.judgments_of("c0")
    assert judgments and Judgment.ESTABLISHED in judgments

    # trace: the surviving audit becomes an evidence event; the two
    # period fees land as two exact installments (3000 + 5000 = 8000)
    events = R.clauses_trace_events(intake)
    assert [e.event.event_id for e in events[:1]] == ["ev-surviving-audit"]
    final, notes = run_trace(case.initial_state, events, env)
    assert "ev:ev-surviving-audit" in [e.evidence_id for e in final.evidence]
    event_ids = [e.event_id for e in final.events]
    assert "pay-fee-3000" in event_ids and "pay-fee-5000" in event_ids
    assert gross_of(final, "USAGE_FEE") == Fraction(8000)
    allocated = [e for e in final.ledger
                 if e.kind.name == "GROSS_ALLOCATED"
                 and e.basis_key == "USAGE_FEE"]
    assert sorted(e.amount for e in allocated) == [Fraction(3000),
                                                   Fraction(5000)]
    assert notes  # the step relation actually produced observations

    # step_event alone: one step, exactly the event's own semantics
    one = step_event(case.initial_state, events[0], env)
    assert [e.evidence_id for e in one.next_state.evidence] == \
        ["ev:ev-surviving-audit"]
    assert one.next_env is env

    # the clause decisions stay on the bundle: the signed-not-effective
    # state stayed its own state (D065), the undeclared conflict path
    # never decided (D066), the notice-only termination did not terminate
    # (D069), the uniform threshold was rejected (D070), the grant was
    # kept on conversion (D071), the affiliate got nothing (D072), the
    # profit-base misuse was detected (D074), the carve-out passed while
    # the capped class was clipped (D075), and the survivors stayed (D076)
    assert intake["state"]["state"] == 1
    assert intake["governing"]["final"] is None
    assert intake["chain"]["final"][2] is False
    assert intake["coc"]["uniform_threshold_rejected"] is True
    assert intake["conversion"]["grant_kept"] is True
    assert intake["relations"]["aff_grant"] is None
    assert intake["fees"]["base_misuse_detected"] is True
    assert intake["indemnity"]["classification_detectable"] is True
    assert len(intake["survival"]["survivors"]) == 4


# ---------------------------------------------------------------------------
# 6 — synthetic receipts through completion.validate_binding
# ---------------------------------------------------------------------------

_REQUIREMENTS = {
    r["id"]: r
    for r in json.loads((SPEC / 'REQUIREMENTS.json').read_text(encoding='utf-8'))
}

_SEMANTICS = {
    "D065": "contract state advances through distinct events: formation "
            "without effectiveness is its own state (a signing day never "
            "counts as the effective day), expiry is a distinct terminal "
            "state, and the surviving-obligation list rides on the "
            "transition carrier as its own component — no event, expiry "
            "included, erases it.",
    "D066": "the final applicable-law judgment is a pure function of the "
            "chosen candidate clause row plus its declared "
            "conflict-of-laws path; candidates and judgment are separate "
            "carriers, no candidate row means no judgment, and an "
            "undeclared conflict path never yields the final judgment — "
            "the incorporation venue alone does not decide.",
    "D067": "a restriction binds along six axes (subject, conduct, "
            "region, period, exception, normative effect) that read back "
            "field-by-field; a differing axis makes a different row, and "
            "the exclusivity-obligation effect code is never the "
            "exclusive-IP-transfer effect code.",
    "D068": "rules, exceptions and exceptions-of-exceptions carry an "
            "explicit three-level priority (2 > 1 > 0); a positive "
            "main-clause hit takes the later exception level (never "
            "skips it), and an exception applies only inside its "
            "declared scope key.",
    "D069": "exercise of the termination right, notice arrival, "
            "termination effectiveness and refusal to renew are four "
            "distinct events, each setting only its own flag; a "
            "stop-renewal notice leaves the current term's effectiveness "
            "flag untouched (false).",
    "D070": "each contract is triggered against its own change-of-control "
            "threshold row (fact 60 crosses 50 but not 80, so one "
            "uniform threshold is rejected) and the notice / consent / "
            "termination consequences are three separate verbatim flags.",
    "D071": "converting a license from exclusive to nonexclusive changes "
            "only the mode and keeps the usage grant verbatim; "
            "license_nonexclusive is not license_terminated, so deleting "
            "the whole usage grant on conversion is intercepted.",
    "D072": "ownership, co-ownership share, license, sublicense and "
            "affiliate scope are five distinct relation tags; the grant "
            "lookup is keyed by relation (a license row never creates an "
            "ownership grant) and an affiliate without a grant row of "
            "its own gets nothing.",
    "D073": "perpetuity, revocability, transferability and the usage cap "
            "are four independent attributes, each writable alone; a "
            "perpetual license that is revocable and capped differs from "
            "a perpetual irrevocable unlimited one, so perpetual never "
            "entails the rest.",
    "D074": "every fee line carries its own period and unit; the revenue "
            "share multiplies the declared base (bases 100000 vs 20000 "
            "at rate 1/10 give exact 10000 vs 2000, so a misused profit "
            "base is detected) and two period rows stay distinct while "
            "their amounts add exactly (8000, no cross-period double "
            "summation).",
    "D075": "indemnity items are classified first, then the cap / "
            "carve-out rule is applied per class: a carve-out passes "
            "through untouched, a capped kind is clipped at the cap "
            "(same amount 1500000 and cap 1000000 give different results "
            "per class), and the insurance limit is a separate field "
            "from the liability cap.",
    "D076": "the survival carrier keeps exactly the kinds the table "
            "declares to survive, each row traceable, undeclared kinds "
            "never appear, and a nonempty all-surviving table keeps a "
            "nonempty carrier after termination — settlement, audit, "
            "escrow and third-party rights are never bulk-deleted.",
}

_ENTRY = {
    "D065": "contract_state_events",
    "D066": "governing_law",
    "D067": "restriction_rows",
    "D068": "prio_eval/scoped_apply/priority_scope_eval",
    "D069": "apply_event/termination_event_chain",
    "D070": "coc_trigger/coc_consequences/change_of_control",
    "D071": "convert_license/license_conversion",
    "D072": "grant_of/ip_relations",
    "D073": "license_attributes",
    "D074": "fee_line/rev_share/fee_lines",
    "D075": "apply_cap/indemnity_classification",
    "D076": "survivors/survival_rules",
}


def _binding_row(dem, required):
    """Template for the controller's BINDINGS.json back-fill
    (DEMAND:D065–D076 rows).  Passes completion.validate_binding as-is."""
    return {
        "id": f"DEMAND:{dem}",
        "theorem": required["theorem"],
        "contract": required["contract"],
        "proof_mode": "KERNEL_CONTRACT_PROOF",
        "formal_scope": "Group-08 contract-clauses demand instance in the "
                        "shared semantic framework: this item's own "
                        "contract semantics plus the registered clause "
                        "component (the docPut lens law: repeated puts "
                        "to the same key agree with the last put, so a "
                        "clause field is never silently overwritten by "
                        "an earlier draft), with its adverse case "
                        "executed as a negative test.",
        "independent_semantics": _SEMANTICS[dem],
        "algorithm": f"tools/full_math/implementation/clauses_ref.py "
                     f"{_ENTRY[dem]} computes the intermediate result from "
                     f"structured input; clauses_check.check_{dem} "
                     f"re-derives the contract independently.",
        "observation_contract": "Inputs are the declared structures "
                                "(contract-state event flags with the "
                                "surviving-obligation list, governing-law "
                                "candidate rows keyed by clause name with "
                                "conflict-path flags, six-axis restriction "
                                "rows with typed effect codes, three-level "
                                "priority inputs with scope keys, "
                                "termination-chain event records over four "
                                "distinct event tags, per-contract "
                                "threshold rows with a transaction fact "
                                "and separate consequence flags, "
                                "license-conversion mode/grant pairs, "
                                "relation-tagged grant rows, four-slot "
                                "license attribute records with an "
                                "optional usage cap, period/unit-tagged "
                                "exact fee lines with share bases and "
                                "rates, classified indemnity items with "
                                "carve-out flags and caps, and "
                                "survival-declared clause tables); "
                                "outputs are exactly the contract "
                                "quantities (the event-advanced state "
                                "with the untouched survival component, "
                                "the row-determined judgment next to the "
                                "separate candidate carrier, the "
                                "field-by-field restriction read-back "
                                "with distinct effect codes, the "
                                "priority level with in-scope and "
                                "out-of-scope results, the folded event "
                                "trace with the notice-only adverse "
                                "witness, the per-contract trigger "
                                "verdicts, the grant-kept conversion, "
                                "the keyed relation grants, the "
                                "independent attribute reads with the "
                                "witness inequality, the exact "
                                "base-sensitive shares and period sums, "
                                "the per-class cap applications with the "
                                "separate insurance field, and the "
                                "declared-survivor carrier after "
                                "termination).",
        "external_assumptions": "The adopted contract interpretation, "
                                "governing-law and conflict-of-laws "
                                "doctrine, reasonableness of restriction "
                                "scopes, notice-validity and delivery "
                                "facts, control relationships and "
                                "transaction substance, IP ownership and "
                                "work-for-hire facts, declared sales "
                                "figures and audit outcomes, insurability "
                                "and loss characterization, escrow "
                                "conditions and third-party status "
                                "remain external validation obligations, "
                                "not part of this registration.",
        "proof_sources": [
            "proofs/lean/juris_lean/JurisLean/FullMath/Contracts.lean",
            "proofs/lean/juris_lean/JurisLean/FullMath/Acceptance.lean",
        ],
        "implementation_sources": [
            "tools/full_math/implementation/clauses_ref.py",
            "tools/full_math/implementation/clauses_check.py",
        ],
        "test_ids": [
            "tools/full_math/implementation_tests::"
            "test_clauses_group08.py::"
            f"test_demand_positive[{dem}]",
            "tools/full_math/implementation_tests::"
            "test_clauses_group08.py::"
            f"test_demand_counterexample[{dem}]",
            "tools/full_math/implementation_tests::"
            "test_clauses_group08.py::"
            "test_downstream_pipeline_consumes_clauses",
        ],
        "negative_test_ids": [
            "tools/full_math/implementation_tests::"
            "test_clauses_group08.py::"
            f"test_checker_rejects_tampered[{dem}]",
        ],
        "semantic_links": [
            "JurisLean.FullMath.Document.docPut_docPut",
        ],
    }


@pytest.mark.parametrize("dem", DEMANDS)
def test_b08_binding_receipt(dem):
    """Synthetic receipt: the binding row for DEMAND:D0XX passes
    completion.validate_binding against the real repository files."""
    required = _REQUIREMENTS[f"DEMAND:{dem}"]
    C.validate_binding(_binding_row(dem, required), required, repo=REPO)


@pytest.mark.parametrize("dem", DEMANDS)
def test_b08_binding_receipt_negative(dem):
    """A tampered receipt (swapped theorem) is rejected."""
    required = _REQUIREMENTS[f"DEMAND:{dem}"]
    row = dict(_binding_row(dem, required))
    row["theorem"] = "JurisLean.FullMath.Acceptance.nonexistent_demand"
    with pytest.raises(C.EvidenceError):
        C.validate_binding(row, required, repo=REPO)
