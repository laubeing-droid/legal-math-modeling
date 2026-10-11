"""W2-A batch B05 acceptance tests: D037-D046, group 05 刑事定罪、量刑与多被告.

Six pieces per demand (docs/full-math/W2B_CLASSIFICATION.md §5.4):

1. Lean contract  — Contracts.demand_D037..D046 restated as this item's own
   semantics (verified by CI; the registration-format tests live in
   test_registration_bindings.py).
2. Python entry   — tools/full_math/implementation/criminal_ref.py per-item
   entries computing the intermediate result from real structured input.
3. Independent checker — criminal_check.py re-derives the contract inline;
   no witness callbacks, no expectations from the main implementation.
4. Downstream consumption — unified.pipeline run_case / step_event /
   run_trace consume the criminal results through the adapters in
   criminal_ref (build_case_input / build_environment /
   criminal_trace_events).
5. Positive and adverse cases — the ALL_134 counterexample field of each
   demand is executed with per-item expectations.
6. Synthetic receipt — completion.validate_binding rows for DEMAND:D037-D046
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

from tools.full_math.implementation import criminal_check as K  # noqa: E402
from tools.full_math.implementation import criminal_ref as R  # noqa: E402
import completion as C  # noqa: E402

# Pipeline-facing names are imported INSIDE the downstream test, not at
# module level: other suites in this directory re-resolve the shared bare
# `unified` tree at their own import time, and call-time imports are the
# only bindings that always match the lazy in-function imports inside
# unified.pipeline/process (criminal_ref's adapters already import lazily).

DEMANDS = ("D037", "D038", "D039", "D040", "D041", "D042", "D043", "D044",
           "D045", "D046")

_CANDS = (("theft", True, True, True),
          ("handling", True, True, True),
          ("fraud", True, False, True))
_DICT_ROWS = ((266, "刑法第266条", "第一款"), (1, "law.txt", "第1项"))
_LEDGER_TERMS = ((1, 24), (1, 12))
_LEDGER_MIXED = ((1, 24), (2, None))
_LEDGER_DEATH = ((3, None), (1, 24))
_REGISTER = (("D1", "theft-elements", "recidivist", 36),
             ("D2", "handling-elements", "first-offense", 12))
_HONEST_ROWS = (("D1", "theft-elements", "recidivist", 36),
                ("D2", "handling-elements", "first-offense", 12))
_AMOUNT_ITEMS = ((7, True, True, True, Fraction(30000)),
                 (7, True, True, True, Fraction(30000)),
                 (8, True, False, True, Fraction(9000)))
_JURIS_ROWS = (("CN", "theft", True),
               ("US-FRE", "hearsay", False),
               ("US-FRE", "theft", True))
_HEARSAY_QUERIES = ((1975, True, True, True),
                    (1975, True, False, True),
                    (2020, True, True, True))


# ---------------------------------------------------------------------------
# 2/3/5 — entry + independent checker, positive and adverse (per item)
# ---------------------------------------------------------------------------


def _run_D037():
    """单标签接口不得悄悄丢掉第二项合法罪名候选（ALL_134 反例字段）."""
    out = R.crime_label_sets(_CANDS)
    ok, reasons = K.check_D037(_CANDS, out)
    return ok, reasons, out


def _run_D038():
    """law.txt第1项不自动打印为刑法第1条（ALL_134 反例字段）."""
    out = R.law_dict_roundtrip(_DICT_ROWS, 266)
    raw = R.law_dict_roundtrip(_DICT_ROWS, 999)
    ok, reasons = K.check_D038(_DICT_ROWS, 266, out)
    ok2, reasons2 = K.check_D038(_DICT_ROWS, 999, raw)
    return ok and ok2, reasons + reasons2, (out, raw)


def _run_D039():
    """−1/−2哨兵不进入刑期均值或罚金计算（ALL_134 反例字段）."""
    terms = R.penalty_ledger(_LEDGER_TERMS)
    mixed = R.penalty_ledger(_LEDGER_MIXED)
    death = R.penalty_ledger(_LEDGER_DEATH)
    ok, r1 = K.check_D039(_LEDGER_TERMS, terms)
    ok2, r2 = K.check_D039(_LEDGER_MIXED, mixed)
    ok3, r3 = K.check_D039(_LEDGER_DEATH, death)
    return ok and ok2 and ok3, r1 + r2 + r3, (terms, mixed, death)


def _run_D040():
    """有金标法条的预测分数不可标为无依据独立定罪能力（ALL_134 反例字段）."""
    out = R.prediction_configs(3, 2)
    ok, reasons = K.check_D040(3, 2, out)
    return ok, reasons, out


def _run_D041():
    """互换姓名仍维持全案金额/刑期合计但检查须失败（ALL_134 反例字段）."""
    honest = R.per_defendant_mapping(_REGISTER, _HONEST_ROWS)
    swapped = R.per_defendant_mapping(_REGISTER, R.identity_swap(_HONEST_ROWS))
    ok, r1 = K.check_D041(_REGISTER, _HONEST_ROWS, honest)
    ok2, r2 = K.check_D041(_REGISTER, tuple(swapped["rows"]), swapped)
    return ok and ok2, r1 + r2, (honest, swapped)


def _run_D042():
    """逐人平均99%不得声称每名被告都正确（ALL_134 反例字段）."""
    out = R.case_correctness(("D1", "D2"), {"D1": True, "D2": None}, True,
                             (Fraction(99), Fraction(100)))
    ok, reasons = K.check_D042(("D1", "D2"), {"D1": True, "D2": None}, True,
                               (Fraction(99), Fraction(100)), out)
    return ok, reasons, out


def _run_D043():
    """结构罚金5000，正文误写50000应被回读发现（ALL_134 反例字段）."""
    tampered = R.judgment_readback(("imprisonment", 24, Fraction(5000)),
                                   ("imprisonment", 24, Fraction(50000)))
    honest = R.judgment_readback(("imprisonment", 24, Fraction(5000)),
                                 ("imprisonment", 24, Fraction(5000)))
    ok, r1 = K.check_D043(("imprisonment", 24, Fraction(5000)),
                          ("imprisonment", 24, Fraction(50000)), tampered)
    ok2, r2 = K.check_D043(("imprisonment", 24, Fraction(5000)),
                           ("imprisonment", 24, Fraction(5000)), honest)
    return ok and ok2, r1 + r2, (tampered, honest)


def _run_D044():
    """理由解释一罪、主文出现另一罪不因文风相似而通过（ALL_134 反例字段）."""
    out = R.conviction_paths(("theft",), ("theft", "fraud"))
    ok, reasons = K.check_D044(("theft",), ("theft", "fraud"), out)
    return ok, reasons, out


def _run_D045():
    """赃款在两份记录出现不得加两遍（ALL_134 反例字段）."""
    out = R.criminal_amounts(_AMOUNT_ITEMS)
    ok, reasons = K.check_D045(_AMOUNT_ITEMS, out)
    return ok, reasons, out


def _run_D046():
    """不得把美国传闻标签直接变成中国证据排除结论（ALL_134 反例字段）."""
    observed = tuple(R.hearsay_resolve(v, e, x, u)
                     for v, e, x, u in _HEARSAY_QUERIES)
    queries = tuple(q + (o,) for q, o in zip(_HEARSAY_QUERIES, observed))
    juris = R.jurisdiction_rows(_JURIS_ROWS)
    ok, r1 = K.check_D046(queries, _JURIS_ROWS,
                          dict(juris, hearsay=observed))
    return ok, r1, (queries, juris)


_POSITIVE = {"D037": _run_D037, "D038": _run_D038, "D039": _run_D039,
             "D040": _run_D040, "D041": _run_D041, "D042": _run_D042,
             "D043": _run_D043, "D044": _run_D044, "D045": _run_D045,
             "D046": _run_D046}


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
    if dem == "D037":
        labels = out
        # 两个合法候选都在输出里；单标签载体丢掉第二项且被显式记录
        assert labels["labels"] == ("theft", "handling")
        assert labels["single_label_carrier"] == ("theft",)
        assert labels["dropped_by_single_label"] == ("handling",)
        assert "handling" not in labels["single_label_carrier"]
        # 阻却未过的 fraud 永不入输出
        assert "fraud" not in labels["labels"]
    elif dem == "D038":
        roundtrip, raw = out
        # 冻结词典按 ID 往返；未登记 ID fail-closed，law.txt 第1项
        # 不会被自动打印为法条
        assert roundtrip["roundtrip_ok"] is True
        assert roundtrip["frozen_unique"] is True
        assert roundtrip["fields"] == {"id": 266, "article": "刑法第266条",
                                       "clause": "第一款"}
        assert raw["registered"] is False
        assert raw["decode_id"] is None
        assert raw["roundtrip_ok"] is False
    elif dem == "D039":
        terms, mixed, death = out
        # 有期账精确求和；混入无期/死刑即无聚合——哨兵无从混入均值
        assert terms["all_terms"] is True
        assert terms["total"] == 36
        assert terms["average"] == Fraction(36, 2)
        assert mixed["poisoned"] is True
        assert mixed["total"] is None
        assert mixed["average"] is None
        assert death["has_death"] is True
        assert death["total"] is None
    elif dem == "D040":
        configs = out
        # 两预算固定、长度不同；有法条预算不是无依据；同命中数按另一
        # 预算长度重算得分不同——分母不混
        assert configs["with"]["budget"] == (0, 1, 2)
        assert configs["without"]["budget"] == (0, 1)
        assert configs["budgets_equal"] is False
        assert configs["lengths_equal"] is False
        assert configs["with"]["statute_free"] is False
        assert configs["without"]["statute_free"] is True
        assert configs["with"]["score"] == Fraction(1)
        assert configs["without"]["score"] == Fraction(2, 2)
        assert configs["same_hits_other_denominator"] == Fraction(3, 2)
        assert configs["mixing_denominators_detected"] is True
        assert Fraction(1) != Fraction(3, 2)
    elif dem == "D041":
        honest, swapped = out
        # 正置逐人查中；互换后合计不变（48）但逐人检查失败
        assert honest["all_ok"] is True
        assert honest["total"] == 48
        assert swapped["total"] == honest["total"]
        assert swapped["all_ok"] is False
        assert all(not c["ok"] for c in swapped["checks"])
    elif dem == "D042":
        correctness = out
        # D2 未决：显式列在 pending；平均 99.5 ≥ 99 但非全员正确
        assert correctness["pending"] == ("D2",)
        assert correctness["all_defendants_correct"] is False
        assert correctness["case_correct"] is False
        assert correctness["relation_consistency"] is True
        assert correctness["average"] == Fraction(199, 2)
        assert Fraction(99) <= correctness["average"]
    elif dem == "D043":
        tampered, honest = out
        # 结构罚金 5000 对正文 50000：回读恰好报 ["fine"]；如实则报空
        assert tampered["mismatches"] == ("fine",)
        assert tampered["projections_equal"] is False
        assert Fraction(50000) != Fraction(5000)
        assert honest["mismatches"] == ()
        assert honest["projections_equal"] is True
    elif dem == "D044":
        reasons_out = out
        # 理由只覆盖 theft：fraud 无路径不获核；文风相似不救
        assert reasons_out["certified"] == ("theft",)
        assert reasons_out["unbacked"] == ("fraud",)
        assert reasons_out["all_certified"] is False
        assert reasons_out["certified_equals_conclusions"] is False
    elif dem == "D045":
        amounts = out
        # 同源 7 计一次（30000 不加两遍）；未过行为轴的 8 永不入
        assert amounts["total"] == Fraction(30000)
        assert amounts["attributed_sum_without_dedup"] == Fraction(60000)
        assert amounts["duplicate_sources_skipped"] == (7,)
        assert amounts["unattributed_skipped"] == (8,)
        assert 8 not in amounts["counted_sources"]
    elif dem == "D046":
        queries, juris = out
        # 版本内全真给允许；版本外显式未决；US 行永不进 CN 载体
        assert queries[0][4] is True
        assert queries[1][4] is None
        assert queries[2][4] is None
        assert juris["cn"] == (("CN", "theft", True),)
        assert juris["leak"] == ()
        assert ("US-FRE", "theft", True) in juris["foreign_rows"]
        assert ("US-FRE", "theft", True) != ("CN", "theft", True)


@pytest.mark.parametrize("dem", DEMANDS)
def test_checker_rejects_tampered(dem):
    """The independent checker must fail a tampered intermediate result
    (the checker, not the entry, is the judge of the contract)."""
    ok, _reasons, out = _POSITIVE[dem]()
    assert ok  # sanity: the honest result passes its own checker
    if dem == "D037":
        labels = out
        tampered = dict(labels)
        tampered["labels"] = labels["labels"][:1]
        tampered["dropped_by_single_label"] = ()
        bad, reasons = K.check_D037(_CANDS, tampered)
    elif dem == "D038":
        roundtrip, _raw = out
        tampered = dict(roundtrip)
        tampered["decode_id"] = 1  # a different row's id — broken roundtrip
        bad, reasons = K.check_D038(_DICT_ROWS, 266, tampered)
    elif dem == "D039":
        terms, mixed, _death = out
        tampered = dict(mixed)
        tampered["total"] = 24  # a number produced across a life row
        tampered["average"] = Fraction(24, 2)
        bad, reasons = K.check_D039(_LEDGER_MIXED, tampered)
    elif dem == "D040":
        configs = out
        tampered = dict(configs)
        tampered["with"] = dict(configs["with"], statute_free=True)
        bad, reasons = K.check_D040(3, 2, tampered)
    elif dem == "D041":
        honest, swapped = out
        tampered = dict(swapped)
        tampered["all_ok"] = True  # a preserved total claimed per-person ok
        bad, reasons = K.check_D041(_REGISTER, tuple(swapped["rows"]),
                                    tampered)
    elif dem == "D042":
        correctness = out
        tampered = dict(correctness)
        tampered["all_defendants_correct"] = True
        tampered["case_correct"] = True  # the average read as correctness
        bad, reasons = K.check_D042(("D1", "D2"), {"D1": True, "D2": None},
                                    True, (Fraction(99), Fraction(100)),
                                    tampered)
    elif dem == "D043":
        tampered_out, _honest = out
        tampered = dict(tampered_out)
        tampered["mismatches"] = ()  # the mis-written fine read back clean
        tampered["projections_equal"] = True
        bad, reasons = K.check_D043(("imprisonment", 24, Fraction(5000)),
                                    ("imprisonment", 24, Fraction(50000)),
                                    tampered)
    elif dem == "D044":
        reasons_out = out
        tampered = dict(reasons_out)
        tampered["unbacked"] = ()
        tampered["all_certified"] = True  # the pathless crime certified
        tampered["certified_equals_conclusions"] = True
        bad, reasons = K.check_D044(("theft",), ("theft", "fraud"), tampered)
    elif dem == "D045":
        amounts = out
        tampered = dict(amounts)
        tampered["total"] = amounts["attributed_sum_without_dedup"]
        tampered["duplicate_sources_skipped"] = ()  # loot added twice
        bad, reasons = K.check_D045(_AMOUNT_ITEMS, tampered)
    elif dem == "D046":
        queries, juris = out
        tampered = dict(juris)
        tampered["cn"] = juris["cn"] + (("US-FRE", "theft", True),)
        tampered["leak"] = (("US-FRE", "theft", True),)
        bad, reasons = K.check_D046(queries, _JURIS_ROWS, tampered)
    assert not bad, f"{dem} checker accepted a tampered result: {reasons}"


# ---------------------------------------------------------------------------
# per-demand adverse specifics beyond the shared parametrized set
# ---------------------------------------------------------------------------


def test_D037_barrier_blocked_label_never_certified():
    """阻却未过的候选（fraud: not_barred=False）永不进入输出标签集."""
    labels = R.crime_label_sets(_CANDS)
    assert "fraud" not in labels["labels"]
    assert "fraud" not in labels["single_label_carrier"]
    ok, reasons = K.check_D037(_CANDS, labels)
    assert ok, reasons


def test_D038_unregistered_line_is_never_a_citation():
    """law.txt 第1项（原始语料行）保持自己的字段——不自动变成刑法第1条；
    未登记 ID（4242）fail-closed，不产出任何引用."""
    line = R.law_dict_roundtrip(_DICT_ROWS, 1)
    assert line["registered"] is True
    assert line["fields"]["article"] == "law.txt"
    assert line["fields"]["article"] != "刑法第1条"
    unregistered = R.law_dict_roundtrip(_DICT_ROWS, 4242)
    assert unregistered["registered"] is False
    assert unregistered["decode_id"] is None
    ok, reasons = K.check_D038(_DICT_ROWS, 1, line)
    assert ok, reasons


def test_D039_death_row_and_empty_ledger():
    """死刑行毒化聚合；空有期账聚合为 0（无哨兵数值可乘虚而入）."""
    death = R.penalty_ledger(((3, None),))
    assert death["total"] is None and death["average"] is None
    empty = R.penalty_ledger(())
    assert empty["total"] == 0
    assert empty["all_terms"] is True
    ok, reasons = K.check_D039((), empty)
    assert ok, reasons


def test_D040_same_hits_different_denominators():
    """同命中数按不同预算长度归一得分不同——分母是计算的一部分."""
    configs = R.prediction_configs(2, 2)
    assert configs["with"]["score"] == Fraction(2, 3)
    assert configs["without"]["score"] == Fraction(1)
    assert configs["scores_equal"] is False
    ok, reasons = K.check_D040(2, 2, configs)
    assert ok, reasons


def test_D041_partial_swap_keeps_total_breaks_one_check():
    """只错配一人刑期：合计随之改变、该人检查失败、另一人仍通过."""
    rows = list(_HONEST_ROWS)
    rows[0] = ("D1", "theft-elements", "recidivist", 12)
    partial = R.per_defendant_mapping(_REGISTER, tuple(rows))
    assert partial["total"] == 24
    assert [c["ok"] for c in partial["checks"]] == [False, True]
    assert partial["all_ok"] is False
    ok, reasons = K.check_D041(_REGISTER, tuple(rows), partial)
    assert ok, reasons


def test_D042_all_determined_true_closes_the_case():
    """全员确定成立且关系一致时 CaseCorrect 才为真、pending 为空."""
    out = R.case_correctness(("D1", "D2"), {"D1": True, "D2": True}, True,
                             (Fraction(100), Fraction(100)))
    assert out["case_correct"] is True
    assert out["pending"] == ()
    ok, reasons = K.check_D042(("D1", "D2"), {"D1": True, "D2": True}, True,
                               (Fraction(100), Fraction(100)), out)
    assert ok, reasons


def test_D044_full_path_coverage_certifies_everything():
    """理由路径覆盖全部主文罪名时，结论全核且清单相等."""
    out = R.conviction_paths(("theft", "handling"), ("handling", "theft"))
    assert out["certified"] == ("handling", "theft")
    assert out["unbacked"] == ()
    assert out["certified_equals_conclusions"] is True
    ok, reasons = K.check_D044(("theft", "handling"),
                               ("handling", "theft"), out)
    assert ok, reasons


def test_D045_unattributed_item_excluded_even_unique():
    """三轴任一未过即不计入——即便来源唯一、无重复."""
    out = R.criminal_amounts(((9, True, True, False, Fraction(7000)),))
    assert out["total"] == Fraction(0)
    assert out["unattributed_skipped"] == (9,)
    ok, reasons = K.check_D045(((9, True, True, False, Fraction(7000)),), out)
    assert ok, reasons


def test_D046_inversion_branches_stay_pending():
    """版本内但例外未证/用途不符：显式未决，不给排除也不给允许."""
    assert R.hearsay_resolve(1975, False, True, True) is None
    assert R.hearsay_resolve(1975, True, True, False) is None
    assert R.hearsay_resolve(1975, True, True, True) is True


# ---------------------------------------------------------------------------
# 4 — downstream consumption: run_case / step_event / run_trace
# ---------------------------------------------------------------------------


def test_downstream_pipeline_consumes_criminal():
    """run_case consumes the CaseInput assembled from the criminal results
    (the D037 surviving primary label as issue, the D044-pathless fraud
    citation never claimed, the D046 hearsay objection as a defense —
    never a written fact, the D045 deduplicated amount as the only
    quantity); run_trace consumes the attributed loot as an evidence
    event plus the structured fine's two exact installments."""
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

    intake = R.build_criminal_intake()
    case = R.build_case_input(intake)
    env = R.build_environment(intake)

    # the assembled carriers are exactly the criminal outputs
    assert case.issues == ("THEFT_CONVICTION",)  # D037 primary label
    assert case.claims[0].claimant == "prosecutor"
    assert case.claims[0].respondent == "defendant"
    # D044: the pathless "fraud" text crime is never claimed
    assert all(c.basis != "fraud" for c in case.claims)
    # D046: the hearsay objection is a defense targeting c0, and the
    # hearsay-only proposition stays awaiting — never silently written
    assert case.defenses[0].defense_id == "def-hearsay"
    assert case.defenses[0].basis == "hearsay_objection"
    assert case.defenses[0].target_claims == ("c0",)
    standings = {(f.proposition.predicate, f.standing.name)
                 for f in case.fact_records}
    assert ("elements_proved", "ADMITTED_POSITIVE") in standings
    assert ("unlawful_take", "ADMITTED_POSITIVE") in standings
    assert ("hearsay_only", "AWAITING_ADMISSION") in standings
    # D045: the only quantity is the deduplicated loot — 30000 once
    assert [q.value for q in case.quantities] == [Fraction(30000),
                                                  Fraction(5000)]

    run = run_case(case, env)
    assert run.status is RunStatus.COMPLETE
    assert run.failures == ()
    judgments = run.judgments_of("c0")
    assert judgments and Judgment.ESTABLISHED in judgments

    # trace: the attributed loot becomes an evidence event; the structured
    # fine lands as two exact installments (2000 + 3000 = 5000, never a
    # merged average number)
    events = R.criminal_trace_events(intake)
    assert [e.event.event_id for e in events[:1]] == ["ev-loot-source-7"]
    final, notes = run_trace(case.initial_state, events, env)
    assert "ev:ev-loot-source-7" in [e.evidence_id for e in final.evidence]
    event_ids = [e.event_id for e in final.events]
    assert "pay-fine-2000" in event_ids and "pay-fine-3000" in event_ids
    assert gross_of(final, "FINE_PAYMENT") == Fraction(5000)
    allocated = [e for e in final.ledger
                 if e.kind.name == "GROSS_ALLOCATED"
                 and e.basis_key == "FINE_PAYMENT"]
    assert sorted(e.amount for e in allocated) == [Fraction(2000),
                                                   Fraction(3000)]
    assert notes  # the step relation actually produced observations

    # step_event alone: one step, exactly the event's own semantics
    one = step_event(case.initial_state, events[0], env)
    assert [e.evidence_id for e in one.next_state.evidence] == \
        ["ev:ev-loot-source-7"]
    assert one.next_env is env

    # the criminal decisions stay on the bundle: the second legitimate
    # label was dropped visibly (D037), the unregistered line stayed
    # fail-closed (D038), the mixed ledger had no total (D039), the
    # denominators did not mix (D040), the swap failed the checks (D041),
    # the pending defendant was listed (D042), the mis-written fine was
    # found (D043), and the loot was counted once (D045)
    assert intake["labels"]["dropped_by_single_label"] == ("handling",)
    assert intake["raw_line"]["decode_id"] is None
    assert intake["ledger_mixed"]["total"] is None
    assert intake["configs"]["mixing_denominators_detected"] is True
    assert intake["swapped"]["all_ok"] is False
    assert intake["correctness"]["pending"] == ("D2",)
    assert intake["record"]["mismatches"] == ("fine",)
    assert intake["amounts"]["total"] == Fraction(30000)


# ---------------------------------------------------------------------------
# 6 — synthetic receipts through completion.validate_binding
# ---------------------------------------------------------------------------

_REQUIREMENTS = {
    r["id"]: r
    for r in json.loads((SPEC / 'REQUIREMENTS.json').read_text(encoding='utf-8'))
}

_SEMANTICS = {
    "D037": "each defendant's crime-label set is exactly the frozen "
            "candidate rows meeting the selected elements, barrier and "
            "concurrence policy at once — labels and semantics map in "
            "both directions; a single-label interface that keeps only "
            "the first legitimate candidate is distinguishable from the "
            "full output, so a second legitimate crime candidate is "
            "never silently dropped.",
    "D038": "the frozen statute dictionary answers a label-id lookup "
            "and, under declared (article, clause) uniqueness, the same "
            "row back by its article and clause (encode/decode "
            "roundtrip); the label id, the article and the clause stay "
            "distinct typed fields, and an unregistered id resolves to "
            "nothing (fail-closed) — a raw corpus line is never "
            "auto-rendered as a statute citation.",
    "D039": "penalty kinds are a sum type (term with months, life, "
            "death without); the numeric aggregate exists only when "
            "every row is a term row carrying months, and any "
            "life/death row poisons it — ordinary addition never mixes "
            "penalty kinds, so no sentinel number can enter a sentence "
            "average or a fine computation.",
    "D040": "with-statute and without-statute are two fixed feature "
            "budgets; the statute feature sits only in the with budget, "
            "the budgets differ in length, and each score is normalized "
            "by its own budget length (denominators never mix): a full "
            "3-feature hit is 1, not the 2-budget 3/2, so a gold-"
            "statute score cannot be reported as statute-free "
            "independent capability.",
    "D041": "per-defendant rows (person, elements, circumstance, "
            "penalty) are checked per person against the register; "
            "swapping two defendants' penalties keeps the case total "
            "but fails the per-person checks, so the common identity is "
            "preserved per defendant and the set result stays "
            "independently checkable.",
    "D042": "CaseCorrect = every required defendant's verdict is "
            "determined-true AND relation consistency holds; a required "
            "defendant with no verdict is explicitly pending (listed), "
            "never silently correct, and a high per-person average "
            "(99/100 → 99.5) coexists with not-all-correct.",
    "D043": "the main text's kind, period and fine projections are "
            "compared field-by-field against the verified structured "
            "record; each mismatch is reported by name, so the classic "
            "tamper (structured fine 5000, text 50000) is found on "
            "read-back while faithful text reads back empty.",
    "D044": "the certified conclusions are the verbatim intersection of "
            "the operative-text crimes with the reasons' rule paths; a "
            "pathless crime is never certified (membership, not string "
            "similarity), so a text citing a second crime fails when "
            "the reasons cover only the first.",
    "D045": "an item enters the criminal amount only when its property, "
            "act and subject attribution axes are all verified, and "
            "each verified source is counted exactly once — the same "
            "loot appearing in two records is added once, never twice, "
            "with the raw attributed sum kept visible for contrast.",
    "D046": "inside one declared US evidence-law version each "
            "element/exception/use query gets an allowed branch (all "
            "hold) or the explicit pending branch (none), never a "
            "silent exclusion; conclusion rows are keyed by "
            "jurisdiction, so a US-FRE row never enters the CN carrier "
            "even with a verbatim-identical label and boolean.",
}

_ENTRY = {
    "D037": "crime_label_sets",
    "D038": "law_dict_roundtrip",
    "D039": "penalty_ledger",
    "D040": "prediction_configs",
    "D041": "per_defendant_mapping/identity_swap",
    "D042": "case_correctness",
    "D043": "judgment_readback",
    "D044": "conviction_paths",
    "D045": "criminal_amounts",
    "D046": "hearsay_resolve/jurisdiction_rows",
}


def _binding_row(dem, required):
    """Template for the controller's BINDINGS.json back-fill
    (DEMAND:D037–D046 rows).  Passes completion.validate_binding as-is."""
    return {
        "id": f"DEMAND:{dem}",
        "theorem": required["theorem"],
        "contract": required["contract"],
        "proof_mode": "KERNEL_CONTRACT_PROOF",
        "formal_scope": "Group-05 criminal demand instance in the "
                        "shared semantic framework: this item's own "
                        "contract semantics plus the registered "
                        "per-person component (conviction slot keys are "
                        "indexed by the person, so two defendants never "
                        "share one elements slot), with its adverse "
                        "case executed as a negative test.",
        "independent_semantics": _SEMANTICS[dem],
        "algorithm": f"tools/full_math/implementation/criminal_ref.py "
                     f"{_ENTRY[dem]} computes the intermediate result from "
                     f"structured input; criminal_check.check_{dem} "
                     f"re-derives the contract independently.",
        "observation_contract": "Inputs are the declared structures "
                                "(crime-label candidate rows with "
                                "elements/barrier/concurrence flags, "
                                "frozen statute-dictionary rows keyed by "
                                "label id and article/clause with an "
                                "injectivity witness, penalty-kind "
                                "ledger rows over the sum type, the two "
                                "fixed feature budgets with hit counts, "
                                "per-defendant rows against a register, "
                                "required-defendant verdicts with an "
                                "optional-pending carrier and per-person "
                                "scores, the structured record against a "
                                "rendered main text, reason paths against "
                                "operative-text crimes, attribution-"
                                "flagged amount items with source ids, "
                                "and versioned jurisdiction-keyed "
                                "conclusion rows with hearsay queries); "
                                "outputs are exactly the contract "
                                "quantities (the policy label set with "
                                "the single-label drop carrier, the "
                                "roundtrip row with its typed fields and "
                                "the fail-closed unregistered verdict, "
                                "the sum-type aggregate with its poison "
                                "flags, the per-budget scores with their "
                                "free-label flags, the per-person checks "
                                "with the swap verdict, the explicit "
                                "pending carrier next to the average, "
                                "the named-field mismatch list, the "
                                "certified/unbacked split, the "
                                "deduplicated exact total with the raw "
                                "sum, and the allow-or-pending branches "
                                "with the keyed CN carrier).",
        "external_assumptions": "The criminal-law version and the adopted "
                                "dogmatic structure, substantive "
                                "element/barrier/concurrence "
                                "classification, penalty-kind substantive "
                                "choice, holdout accuracy and drift, "
                                "fact attribution to defendants, docket "
                                "completeness, narrative audit beyond "
                                "the declared projections, legal-"
                                "interpretation sufficiency, property "
                                "value and attribution proofs, statement "
                                "purpose and exception facts remain "
                                "external validation obligations, not "
                                "part of this registration.",
        "proof_sources": [
            "proofs/lean/juris_lean/JurisLean/FullMath/Contracts.lean",
            "proofs/lean/juris_lean/JurisLean/FullMath/Acceptance.lean",
        ],
        "implementation_sources": [
            "tools/full_math/implementation/criminal_ref.py",
            "tools/full_math/implementation/criminal_check.py",
        ],
        "test_ids": [
            "tools/full_math/implementation_tests::"
            "test_criminal_group05.py::"
            f"test_demand_positive[{dem}]",
            "tools/full_math/implementation_tests::"
            "test_criminal_group05.py::"
            f"test_demand_counterexample[{dem}]",
            "tools/full_math/implementation_tests::"
            "test_criminal_group05.py::"
            "test_downstream_pipeline_consumes_criminal",
        ],
        "negative_test_ids": [
            "tools/full_math/implementation_tests::"
            "test_criminal_group05.py::"
            f"test_checker_rejects_tampered[{dem}]",
        ],
        "semantic_links": [
            "JurisLean.FullMath.Burden.perPerson_slots_distinct",
        ],
    }


@pytest.mark.parametrize("dem", DEMANDS)
def test_b05_binding_receipt(dem):
    """Synthetic receipt: the binding row for DEMAND:D0XX passes
    completion.validate_binding against the real repository files."""
    required = _REQUIREMENTS[f"DEMAND:{dem}"]
    C.validate_binding(_binding_row(dem, required), required, repo=REPO)


@pytest.mark.parametrize("dem", DEMANDS)
def test_b05_binding_receipt_negative(dem):
    """A tampered receipt (swapped theorem) is rejected."""
    required = _REQUIREMENTS[f"DEMAND:{dem}"]
    row = dict(_binding_row(dem, required))
    row["theorem"] = "JurisLean.FullMath.Acceptance.nonexistent_demand"
    with pytest.raises(C.EvidenceError):
        C.validate_binding(row, required, repo=REPO)
