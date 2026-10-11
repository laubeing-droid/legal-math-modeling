"""W2-A batch B02 acceptance tests: D009-D018, group 02 法源、解释与类案研究.

Six pieces per demand (docs/full-math/W2B_CLASSIFICATION.md §5.4):

1. Lean contract  — Contracts.demand_D009..D018 restated as this item's own
   semantics (verified by CI; the registration-format tests live in
   test_registration_bindings.py).
2. Python entry   — tools/full_math/implementation/sourcing_ref.py per-item
   entries computing the intermediate result from real structured input.
3. Independent checker — sourcing_check.py re-derives the contract inline;
   no witness callbacks, no expectations from the main implementation.
4. Downstream consumption — unified.pipeline run_case / step_event /
   run_trace consume the sourcing results through the adapters in
   sourcing_ref (build_case_input / build_environment /
   sourcing_trace_events).
5. Positive and adverse cases — the ALL_134 counterexample field of each
   demand is executed with per-item expectations.
6. Synthetic receipt — completion.validate_binding rows for DEMAND:D009-D018.
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
# foreign tree: test_intake_group01 may already have imported the right
# tools/unified_math_v2 modules, and a blind re-import would create a
# second enum identity that fails `kind is LegalEventKind...` dispatch.
_existing_unified = sys.modules.get('unified')
if _existing_unified is None or \
        'unified_math_v2' not in str(getattr(_existing_unified, '__file__', '')):
    for _shared in ("reference", "unified", "unified_v21"):
        for _name in [m for m in sys.modules
                      if m == _shared or m.startswith(_shared + ".")]:
            del sys.modules[_name]

from tools.full_math.implementation import sourcing_check as K  # noqa: E402
from tools.full_math.implementation import sourcing_ref as R  # noqa: E402
import completion as C  # noqa: E402

# Pipeline-facing names are imported INSIDE the downstream test, not at
# module level: other suites in this directory re-resolve the shared bare
# `unified` tree at their own import time, and call-time imports are the
# only bindings that always match the lazy in-function imports inside
# unified.pipeline/process (sourcing_ref's adapters already import lazily).

DEMANDS = ("D009", "D010", "D011", "D012", "D013", "D014", "D015",
           "D016", "D017", "D018")


# ---------------------------------------------------------------------------
# 2/3/5 — entry + independent checker, positive and adverse (per item)
# ---------------------------------------------------------------------------


def _run_D009():
    """真实引文但引用错版本，版本检查须拒绝（ALL_134 反例字段）."""
    source_text = ("loan", "contract", "signed", "principal", "due")
    quote = R.quote_span(source_text, 1, 4)
    src_ver = {"published": 20, "effective": 30, "repeal": None}
    wrong_ver = {"published": 21, "effective": 30, "repeal": None}
    ok_quote, reasons_quote = K.check_D009(source_text, 1, 4, quote)
    accepts_right = R.version_accepts(src_ver, src_ver)
    accepts_wrong = R.version_accepts(src_ver, wrong_ver)
    ok_ver, reasons_ver = K.check_D009_version(src_ver, wrong_ver,
                                               accepts_wrong)
    ok = ok_quote and ok_ver and accepts_right and not accepts_wrong
    return ok, reasons_quote + reasons_ver, (source_text, quote, accepts_right,
                                             accepts_wrong)


def _run_D010():
    """只召回相似法条不能签全部适用法条证书（ALL_134 反例字段）."""
    rules = (("loan-delivery-civil", True), ("tort-lookalike", False))
    out = R.applicable_rules(rules)
    certificate = R.full_applicability_certificate(rules, out["hits"])
    merged = dict(out, certificate=certificate)
    ok, reasons = K.check_D010(rules, merged)
    return ok, reasons, (rules, merged, certificate)


def _run_D011():
    """后上传旧文本不得按新上传日期当新法（ALL_134 反例字段）."""
    old_text = {"published": 90, "effective": 10, "repeal": None}
    new_text = {"published": 40, "effective": 200, "repeal": None}
    out = R.historical_version_decision(old_text, new_text, 50)
    ok, reasons = K.check_D011(old_text, new_text, 50, out)
    return ok, reasons, (old_text, new_text, out)


def _run_D012():
    """定义中排除关联方，主文不得重新无条件纳入（ALL_134 反例字段）."""
    defs = (("affiliate", "excluded-from-main-text", True),
            ("loan", "principal-and-interest", False))
    resolved = R.resolve_definition(defs, (), "affiliate", 3)
    unregistered = R.resolve_definition(defs, (), "never-defined", 3)
    no_fuel = R.resolve_definition(defs, (), "affiliate", 0)
    ok_resolved, r1 = K.check_D012(defs, (), "affiliate", 3, resolved)
    ok_unreg, r2 = K.check_D012(defs, (), "never-defined", 3, unregistered)
    ok_fuel, r3 = K.check_D012(defs, (), "affiliate", 0, no_fuel)
    ok = ok_resolved and ok_unreg and ok_fuel
    return ok, r1 + r2 + r3, (defs, resolved, unregistered, no_fuel)


def _run_D013():
    """程序上相关但实体事实不同，不复制实体结论（ALL_134 反例字段）."""
    scores = {"case-a": Fraction(3, 4), "case-b": Fraction(1, 2)}
    ordering = R.compare_score(scores, "case-a", "case-b")
    transfer = R.transfer_case(
        relevant=("procedure", "substantive_facts"),
        target_features=("procedure",))
    merged = {**ordering, **transfer}
    ok, reasons = K.check_D013(scores, "case-a", "case-b",
                               ("procedure",),
                               ("procedure", "substantive_facts"),
                               merged)
    return ok, reasons, (scores, ordering, transfer, merged)


def _run_D014():
    """100项pool全命中不能改写成全库无遗漏（ALL_134 反例字段）."""
    corpus = ("p1", "p2", "p3", "outside-relevant")
    pool = ("p1", "p2", "p3")
    returned = R.pool_recall(pool, lambda s: s.startswith("p")
                             and s != "p3")
    claim_ok = R.corpus_completeness_claimable(corpus, pool,
                                               lambda s: s != "p3")
    out = {"returned": returned, "claim_ok": claim_ok}
    ok, reasons = K.check_D014(corpus, pool, lambda s: s != "p3", out)
    return ok, reasons, (corpus, pool, out)


def _run_D015():
    """案号真实但只支持相反观点，不准当正向依据（ALL_134 反例字段）."""
    cites = (("case-pro", ("supports", "loan"), True),
             ("case-con", ("contradicts", "loan"), False))
    support = R.approved_edges(cites, "loan")
    upgrade = R.upgrade_claim(("case-pro",), support["edges"])
    upgrade_con = R.upgrade_claim(("case-con",), support["edges"])
    merged = dict(support, upgrade=upgrade, upgrade_con=upgrade_con)
    ok, reasons = K.check_D015(cites, "loan", support)
    return ok, reasons, (cites, merged)


def _run_D016():
    """推翻一个争点不得删除该案所有无关论点，亦不得保留被推翻点
    （ALL_134 反例字段）."""
    overruled = (("case-pro", "quantum", 20),
                 ("case-pro", "limitation", 40))
    quantum_30 = R.precedent_validity(overruled, "case-pro", "quantum", 30)
    limitation_30 = R.precedent_validity(overruled, "case-pro",
                                         "limitation", 30)
    quantum_10 = R.precedent_validity(overruled, "case-pro", "quantum", 10)
    ok1, r1 = K.check_D016(overruled, "case-pro", "quantum", 30, quantum_30)
    ok2, r2 = K.check_D016(overruled, "case-pro", "limitation", 30,
                           limitation_30)
    ok3, r3 = K.check_D016(overruled, "case-pro", "quantum", 10, quantum_10)
    return ok1 and ok2 and ok3, r1 + r2 + r3, (overruled, quantum_30,
                                               limitation_30, quantum_10)


def _run_D017():
    """不能按英文合同或美国当事人自动选UCC（ALL_134 反例字段）."""
    cands = (("ucc-sale", True, False, True, True),
             ("civil-loan", True, True, True, True))
    ucc = R.select_framework(cands, "ucc-sale")
    civil = R.select_framework(cands, "civil-loan")
    ok1, r1 = K.check_D017(cands, "ucc-sale", ucc)
    ok2, r2 = K.check_D017(cands, "civil-loan", civil)
    return ok1 and ok2, r1 + r2, (cands, ucc, civil)


def _run_D018():
    """将申报门槛相同误当申报后果相同须被区分（ALL_134 反例字段）."""
    a = {"subjects": ("turnover",), "threshold": Fraction(100_000_000),
         "timing": 30, "effect": "prohibited"}
    b = {"subjects": ("turnover",), "threshold": Fraction(100_000_000),
         "timing": 30, "effect": "file-then-proceed"}
    out = R.compare_regimes(a, b)
    ok, reasons = K.check_D018(a, b, out)
    return ok, reasons, (a, b, out)


_POSITIVE = {"D009": _run_D009, "D010": _run_D010, "D011": _run_D011,
             "D012": _run_D012, "D013": _run_D013, "D014": _run_D014,
             "D015": _run_D015, "D016": _run_D016, "D017": _run_D017,
             "D018": _run_D018}


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
    if dem == "D009":
        source_text, quote, accepts_right, accepts_wrong = out
        # 引文即原文切片，且错版本被拒绝
        assert quote["span"] == ("contract", "signed", "principal")
        assert quote["length"] == quote["end"] - quote["start"] == 3
        assert accepts_right is True and accepts_wrong is False
        assert quote["span"] != tuple(source_text)
    elif dem == "D010":
        rules, merged, certificate = out
        # 相似不等于适用：tort-lookalike 不在适用结果里
        assert "tort-lookalike" not in merged["hits"]
        assert "loan-delivery-civil" in merged["hits"]
        assert certificate is True
        similar_only = ("tort-lookalike",)
        assert R.full_applicability_certificate(rules, similar_only) is False
    elif dem == "D011":
        _old, new, decision = out
        # 后上传旧文本按法效时间判定：新法未生效不适用，旧文本照常适用
        assert new["published"] < _old["published"]
        assert decision["new_applies"] is False
        assert decision["old_applies"] is True
        assert decision["registration_times"] == (90, 40)
        assert decision["effect_times"] == (10, 200)
    elif dem == "D012":
        _defs, resolved, unregistered, no_fuel = out
        # 排除限定词随解释保留；未注册与燃料耗尽都是明确拒绝路径
        assert resolved["status"] == "resolved"
        assert resolved["excluded"] is True
        assert unregistered["status"] == "rejected"
        assert unregistered["reason"] == "unregistered"
        assert no_fuel["status"] == "rejected"
        assert no_fuel["reason"] == "fuel_exhausted"
    elif dem == "D013":
        _scores, ordering, transfer, _merged = out
        # 排序键=指定 score；缺实体特征即拒绝复制实体结论
        assert ordering["a_before_b"] is True
        assert ordering["b_before_a"] is False
        assert transfer["copied"] is False
        assert transfer["missing_features"] == ("substantive_facts",)
    elif dem == "D014":
        corpus, pool, result = out
        # pool 内逐项命中，但池外还有相关条目：全库无遗漏声称被拒绝
        assert result["returned"] == ("p1", "p2")
        assert result["claim_ok"] is False
        assert "outside-relevant" in corpus
        assert "outside-relevant" not in pool
    elif dem == "D015":
        cites, merged = out
        # 反方 stance 的真实案号不成正向依据；升级需覆盖全部引用
        assert ("case-con", "loan") not in merged["edges"]
        assert ("case-pro", "loan") in merged["edges"]
        assert merged["upgrade"]["upgraded"] is True
        assert merged["upgrade_con"]["upgraded"] is False
        assert [c[0] for c in cites] == ["case-pro", "case-con"]
    elif dem == "D016":
        _overruled, quantum_30, limitation_30, quantum_10 = out
        # 被推翻点失效；无关论点保留；效力与引用时点关联
        assert quantum_30["valid"] is False
        assert limitation_30["valid"] is True
        assert quantum_10["valid"] is True
    elif dem == "D017":
        _cands, ucc, civil = out
        # 管辖真而标的不真：UCC 不被自动选中，未决分支保留
        assert ucc["status"] == "pending"
        assert ucc["branch"] == ("ucc-sale", True, False, True, True)
        assert ucc["flags"] == (True, False, True, True)
        assert civil["status"] == "selected"
    elif dem == "D018":
        a, b, comparison = out
        # 门槛相同、后果不同：须被区分并给出具名差异见证
        assert a["threshold"] == b["threshold"]
        assert comparison["equivalent"] is False
        assert comparison["difference_witness"] == ("effect",)


@pytest.mark.parametrize("dem", DEMANDS)
def test_checker_rejects_tampered(dem):
    """The independent checker must fail a tampered intermediate result
    (the checker, not the entry, is the judge of the contract)."""
    ok, _reasons, out = _POSITIVE[dem]()
    assert ok  # sanity: the honest result passes its own checker
    if dem == "D009":
        source_text, quote, _ar, _aw = out
        tampered = dict(quote, span=("contract", "signed"))
        bad, reasons = K.check_D009(source_text, 1, 4, tampered)
    elif dem == "D010":
        rules = (("loan-delivery-civil", True), ("tort-lookalike", False))
        bad, reasons = K.check_D010(rules, {
            "hits": ("tort-lookalike", "loan-delivery-civil"),
            "certificate": True})
    elif dem == "D011":
        old_text, new_text, _decision = out
        tampered = dict(R.historical_version_decision(old_text, new_text, 50),
                        new_applies=True)
        bad, reasons = K.check_D011(old_text, new_text, 50, tampered)
    elif dem == "D012":
        defs, _resolved, _unreg, _fuel = out
        tampered = dict(R.resolve_definition(defs, (), "affiliate", 3),
                        excluded=False)
        bad, reasons = K.check_D012(defs, (), "affiliate", 3, tampered)
    elif dem == "D013":
        scores, _ordering, _transfer, _merged = out
        honest_order = R.compare_score(scores, "case-a", "case-b")
        tampered_transfer = dict(
            R.transfer_case(("procedure", "substantive_facts"),
                            ("procedure",)),
            copied=True, missing_features=())
        bad, reasons = K.check_D013(scores, "case-a", "case-b",
                                    ("procedure",),
                                    ("procedure", "substantive_facts"),
                                    {**honest_order, **tampered_transfer})
    elif dem == "D014":
        corpus, pool, _result = out
        bad, reasons = K.check_D014(corpus, pool, lambda s: s != "p3",
                                    {"returned": ("p1", "p2"),
                                     "claim_ok": True})
    elif dem == "D015":
        cites = (("case-pro", ("supports", "loan"), True),
                 ("case-con", ("contradicts", "loan"), False))
        tampered = {"edges": (("case-pro", "loan"), ("case-con", "loan")),
                    "registry": tuple((c[0], tuple(c[1]), bool(c[2]))
                                      for c in cites)}
        bad, reasons = K.check_D015(cites, "loan", tampered)
    elif dem == "D016":
        overruled, _q30, _l30, _q10 = out
        tampered = dict(
            R.precedent_validity(overruled, "case-pro", "quantum", 30),
            valid=True)
        bad, reasons = K.check_D016(overruled, "case-pro", "quantum", 30,
                                    tampered)
    elif dem == "D017":
        cands = (("ucc-sale", True, False, True, True),
                 ("civil-loan", True, True, True, True))
        tampered = dict(R.select_framework(cands, "ucc-sale"),
                        status="selected")
        bad, reasons = K.check_D017(cands, "ucc-sale", tampered)
    elif dem == "D018":
        a, b, _comparison = out
        tampered = dict(R.compare_regimes(a, b), equivalent=True)
        bad, reasons = K.check_D018(a, b, tampered)
    assert not bad, f"{dem} checker accepted a tampered result: {reasons}"


# ---------------------------------------------------------------------------
# per-demand adverse specifics beyond the shared parametrized set
# ---------------------------------------------------------------------------


def test_D009_rejects_out_of_bounds_coordinates():
    """越界引文坐标在入口处即被拒绝（外边界防御）."""
    with pytest.raises(ValueError):
        R.quote_span(("a", "b"), 1, 5)
    with pytest.raises(ValueError):
        R.quote_span(("a", "b"), 2, 1)


def test_D011_repeal_window_and_same_day_boundary():
    """废止窗口与法效边界：生效当日即适用，废止当日不再适用."""
    v = {"published": 5, "effective": 10, "repeal": 20}
    assert R.applies_at(v, 10) is True
    assert R.applies_at(v, 19) is True
    assert R.applies_at(v, 20) is False
    assert R.applies_at(v, 9) is False


def test_D013_equal_scores_share_rank():
    """等分同位：相等 score 不产生先后."""
    ordering = R.compare_score({"x": Fraction(1, 3), "y": Fraction(1, 3)},
                               "x", "y")
    assert ordering["same_rank"] is True
    assert ordering["a_before_b"] is False and ordering["b_before_a"] is False


def test_D012_transitive_reference_resolves_through_cites():
    """跨条引用经有界追踪解析：引用边耗一格燃料，命中注册含义停机."""
    defs = (("base-meaning", "the-base", False),)
    cites = (("derived", "base-meaning"),)
    out = R.resolve_definition(defs, cites, "derived", 2)
    assert out["status"] == "resolved"
    assert out["meaning"] == "the-base"
    assert out["hops"] == 1
    too_short_fuel = R.resolve_definition(defs, cites, "derived", 1)
    assert too_short_fuel["status"] == "rejected"
    assert too_short_fuel["reason"] == "fuel_exhausted"


def test_D016_overrule_effective_day_boundary():
    """推翻生效日当日即失效（效力图的时点语义）."""
    overruled = (("case-x", "issue-1", 20),)
    at_19 = R.precedent_validity(overruled, "case-x", "issue-1", 19)
    at_20 = R.precedent_validity(overruled, "case-x", "issue-1", 20)
    assert at_19["valid"] is True
    assert at_20["valid"] is False
    assert at_20["blocking_overrules"] == (("case-x", "issue-1", 20),)


def test_D017_unregistered_framework_stays_pending():
    """未登记框架不发明：查无此候选即未决，分支不丢弃也不虚构."""
    out = R.select_framework((("a", True, True, True, True),), "ghost")
    assert out["status"] == "pending"
    assert out["branch"] is None


def test_D018_identical_regimes_are_equivalent():
    """四维全同的制度比较为等同，差异见证为空."""
    a = {"subjects": ("s",), "threshold": Fraction(1), "timing": 1,
         "effect": "e"}
    out = R.compare_regimes(a, dict(a))
    assert out["equivalent"] is True
    assert out["difference_witness"] == ()


# ---------------------------------------------------------------------------
# 4 — downstream consumption: run_case / step_event / run_trace
# ---------------------------------------------------------------------------


def test_downstream_pipeline_consumes_sourcing():
    """run_case consumes the CaseInput assembled from the sourcing results
    (D010 applicable hits as issues, D013 transferred claim, D009 quote
    provenance scoping the admitted facts); run_trace consumes the D009
    quotation as an evidence event plus the per-obligor payments."""
    # call-time imports: always the same unified copies the pipeline's own
    # lazy in-function imports resolve to (see module docstring note)
    from theory.spec.canonical_v2.case import CaseEvent, RunStatus
    from theory.spec.canonical_v2.kernel import Judgment
    from unified.pipeline import run_case, run_trace, step_event
    from unified.process import LegalEventKind, ProcessEvent, gross_of

    intake = R.build_sourcing_intake()
    case = R.build_case_input(intake)
    env = R.build_environment(intake)

    # the assembled carriers are exactly the sourcing outputs
    assert case.issues == ("loan-delivery-civil",)  # D010 hit
    assert set(case.parties) == {"case-pro", "borrower-d"}
    assert case.claims[0].claimant == "case-pro"
    assert case.claims[0].respondent == "borrower-d"
    assert case.claims[0].basis == "loan-delivery-civil"
    assert case.fact_records[0].proposition.subject == "quote:1:4"  # D009

    run = run_case(case, env)
    assert run.status is RunStatus.COMPLETE
    assert run.failures == ()
    judgments = run.judgments_of("c0")
    assert judgments and Judgment.ESTABLISHED in judgments

    # trace: the D009 quotation evidence event + per-obligor payments
    # (separate events, never averaged)
    initial = case.initial_state
    events = R.sourcing_trace_events(intake)
    evidence_event = events[0]
    final, notes = run_trace(initial, events, env)
    assert "ev:ev-quote-1-4" in [e.evidence_id for e in final.evidence]
    event_ids = [e.event_id for e in final.events]
    assert "pay-D1" in event_ids and "pay-D2" in event_ids
    # per-obligor payments land on the applicable rule basis; the totals
    # are the sum of the individual dispositions (two separate
    # gross-allocated entries, never averaged)
    assert gross_of(final, "loan-delivery-civil") == Fraction(5_000_000)
    allocated = [e for e in final.ledger
                 if e.kind.name == "GROSS_ALLOCATED"
                 and e.basis_key == "loan-delivery-civil"]
    assert sorted(e.amount for e in allocated) == [Fraction(2_000_000),
                                                   Fraction(3_000_000)]
    assert notes  # the step relation actually produced observations

    # step_event alone: one step, exactly the event's own semantics
    one = step_event(initial, evidence_event, env)
    assert [e.evidence_id for e in one.next_state.evidence] == \
        ["ev:ev-quote-1-4"]
    assert one.next_env is env

    # the sourcing decisions stay on the bundle: the wrong version is
    # rejected (D009), the UCC branch stays pending (D017), the regimes
    # with equal thresholds but different effects are distinguished (D018)
    assert intake["version_rejects"] is False
    assert intake["framework"]["status"] == "pending"
    assert intake["comparison"]["equivalent"] is False
    assert intake["definition"]["excluded"] is True
    assert intake["recall_claim_ok"] is False


# ---------------------------------------------------------------------------
# 6 — synthetic receipts through completion.validate_binding
# ---------------------------------------------------------------------------

_REQUIREMENTS = {
    r["id"]: r
    for r in json.loads((SPEC / 'REQUIREMENTS.json').read_text(encoding='utf-8'))
}

_SEMANTICS = {
    "D009": "quoted_span equals the [start,end) slice of the declared "
            "source; every protected proposition's provenance coordinates "
            "read back verbatim; a real quotation citing the wrong version "
            "is rejected by the cache-key version check.",
    "D010": "results satisfy the applicability predicate inside the frozen "
            "rule base and candidate interpretations; a full-applicability "
            "claim requires independent candidate coverage; similar but "
            "inapplicable rules never enter the result.",
    "D011": "applicability is decided by the legal-effect time at the "
            "event day (Applicable(v,eventTime)); the registration time "
            "and the effect time are stored separately; a later-uploaded "
            "old text is judged by its own effective window, never by its "
            "upload date.",
    "D012": "the qualifier/definition-scope and citation-graph interpreter "
            "keeps semantics: registered meanings resolve with their "
            "exclusion qualifier intact; recursive references follow a "
            "bounded chase with an explicit rejection path (fuel "
            "exhaustion), never an invented meaning.",
    "D013": "under a fixed issue the ranking agrees with the designated "
            "score (antisymmetric order, equal scores share a rank); a "
            "similar-case transfer copies the substantive conclusion only "
            "under a relevant-feature preservation witness.",
    "D014": "Returned is a subset of Relevant_D (pool-internal and "
            "relevant item by item); Returned=Relevant_D over the corpus "
            "is claimable only when the pool covers the corpus and every "
            "item is adjudicated; a relevant corpus item outside the pool "
            "refuses the no-miss claim.",
    "D015": "every cited proposition keeps its span and an approved "
            "semantic-support edge; approved edges are generated only "
            "from pro-stance citations; a declaration upgrade requires "
            "every cited id to carry an approved edge.",
    "D016": "the precedent validity graph is keyed by (case, issue) and "
            "tied to the citation day: the overturned point is invalid "
            "from its effective day on, unrelated issues of the same case "
            "stay valid and are never deleted.",
    "D017": "LegalFramework candidates are filtered by the conjunction of "
            "jurisdiction, subject, conflict-of-law and applicability "
            "conditions; undecided branches stay retained as pending and "
            "no single condition (English contract or US party alone) "
            "auto-selects the UCC.",
    "D018": "the cross-jurisdiction comparison preserves each domain's "
            "subjects/threshold/timing/effect; without a preserving "
            "mapping it returns a named difference witness — identical "
            "filing thresholds with different effects are distinguished, "
            "never reported as equivalent.",
}

_ENTRY = {
    "D009": "quote_span/version_accepts",
    "D010": "applicable_rules/full_applicability_certificate",
    "D011": "applies_at/historical_version_decision",
    "D012": "resolve_definition",
    "D013": "compare_score/transfer_case",
    "D014": "pool_recall/corpus_completeness_claimable",
    "D015": "approved_edges/upgrade_claim",
    "D016": "precedent_validity",
    "D017": "select_framework",
    "D018": "compare_regimes",
}


def _binding_row(dem, required):
    return {
        "id": f"DEMAND:{dem}",
        "theorem": required["theorem"],
        "contract": required["contract"],
        "proof_mode": "KERNEL_CONTRACT_PROOF",
        "formal_scope": "Group-02 sourcing demand instance in the shared "
                        "semantic framework: this item's own contract "
                        "semantics plus the registered fail-closed "
                        "applicable-source component, with its adverse "
                        "case executed as a negative test.",
        "independent_semantics": _SEMANTICS[dem],
        "algorithm": f"tools/full_math/implementation/sourcing_ref.py "
                     f"{_ENTRY[dem]} computes the intermediate result from "
                     f"structured input; sourcing_check.check_{dem} "
                     f"re-derives the contract independently.",
        "observation_contract": "Inputs are the declared structures "
                                "(source text with quote coordinates and "
                                "version triples, frozen rule tables, "
                                "effective/registration timelines, "
                                "definition and citation tables, score "
                                "and feature tables, pool/corpus lists, "
                                "citation stance records, per-issue "
                                "overrule days, framework condition "
                                "tuples, jurisdiction regime records); "
                                "outputs are exactly the contract "
                                "quantities (quote span with provenance "
                                "and version verdict, applicable hits "
                                "with coverage certificate, historical "
                                "version decision, definition resolution "
                                "with qualifier and rejection path, "
                                "score order and witnessed transfer "
                                "decision, returned subset and corpus "
                                "claim verdict, approved edges and "
                                "upgrade verdict, per-issue validity at "
                                "the citation day, framework selection "
                                "with retained pending branch, regime "
                                "comparison with difference witness).",
        "external_assumptions": "Truth of external legal facts, "
                                "natural-language coverage, human "
                                "relevance labels and official "
                                "revision/repeal registries remain "
                                "external validation obligations, not "
                                "part of this registration.",
        "proof_sources": [
            "proofs/lean/juris_lean/JurisLean/FullMath/Contracts.lean",
            "proofs/lean/juris_lean/JurisLean/FullMath/Acceptance.lean",
        ],
        "implementation_sources": [
            "tools/full_math/implementation/sourcing_ref.py",
            "tools/full_math/implementation/sourcing_check.py",
        ],
        "test_ids": [
            "tools/full_math/implementation_tests::test_sourcing_group02.py::"
            f"test_demand_positive[{dem}]",
            "tools/full_math/implementation_tests::test_sourcing_group02.py::"
            f"test_demand_counterexample[{dem}]",
            "tools/full_math/implementation_tests::test_sourcing_group02.py::"
            "test_downstream_pipeline_consumes_sourcing",
        ],
        "negative_test_ids": [
            "tools/full_math/implementation_tests::test_sourcing_group02.py::"
            f"test_checker_rejects_tampered[{dem}]",
        ],
        "semantic_links": ["JurisLean.FullMath.Burden.unknown_is_pending"],
    }


@pytest.mark.parametrize("dem", DEMANDS)
def test_b02_binding_receipt(dem):
    """Synthetic receipt: the binding row for DEMAND:D00X passes
    completion.validate_binding against the real repository files."""
    required = _REQUIREMENTS[f"DEMAND:{dem}"]
    C.validate_binding(_binding_row(dem, required), required, repo=REPO)


@pytest.mark.parametrize("dem", DEMANDS)
def test_b02_binding_receipt_negative(dem):
    """A tampered receipt (swapped theorem) is rejected."""
    required = _REQUIREMENTS[f"DEMAND:{dem}"]
    row = dict(_binding_row(dem, required))
    row["theorem"] = "JurisLean.FullMath.Acceptance.nonexistent_demand"
    with pytest.raises(C.EvidenceError):
        C.validate_binding(row, required, repo=REPO)
