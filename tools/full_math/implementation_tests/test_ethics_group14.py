"""W2-A batch B14 acceptance tests: D124-D134, groups 14+15 伦理、隐私
与表达可靠性＋美国法特定问题与法律语言任务.

Six pieces per demand (docs/full-math/W2B_CLASSIFICATION.md §5.4):

1. Lean contract  — Contracts.demand_D124..D134 restated as this item's
   own semantics over region-local operational defs, with the
   group-registered components (JurisLean.FullMath.Evidence.
   step_rules_mono for D124-D130, JurisLean.FullMath.Probability.
   condition_incompatible_iff for D131-D134) as the first conjunct;
   verified by the whole-repo replay build, and the registration-format
   tests live in test_registration_bindings.py.
2. Python entry   — tools/full_math/implementation/ethics_ref.py
   per-item entries computing the intermediate result from real
   structured input (the exact-ℚ Beta face unified.beta.beta_cdf_integer
   — the mirror of Seams/UnifiedBetaDomain.ratBernCdf — consumed by the
   D125 group-risk coverage and the D134 label confidence).
3. Independent checker — ethics_check.py re-derives the contract
   inline with different code paths (index scans, decision tables, row
   counters, gate ladders, score-vector picks, label-set assembly,
   bound-checked walks, two-column tables); no witness callbacks, no
   expectations from the main implementation, zero code sharing.
4. Downstream consumption — unified.pipeline run_case / step_event /
   run_trace consume the ethics/US-law results through the adapters in
   ethics_ref (build_case_input / build_environment /
   ethics_trace_events).
5. Positive and adverse cases — the ALL_134 counterexample field of
   each demand is executed with per-item expectations.
6. Synthetic receipt — completion.validate_binding rows for
   DEMAND:D124-D134 (the ``_binding_row`` template below is ready for
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
# foreign tree (same rationale as the B07/B13 siblings).
_existing_unified = sys.modules.get('unified')
if _existing_unified is None or \
        'unified_math_v2' not in str(getattr(_existing_unified, '__file__', '')):
    for _shared in ("reference", "unified", "unified_v21"):
        for _name in [m for m in sys.modules
                      if m == _shared or m.startswith(_shared + ".")]:
            del sys.modules[_name]

from tools.full_math.implementation import ethics_check as K  # noqa: E402
from tools.full_math.implementation import ethics_ref as R  # noqa: E402
import completion as C  # noqa: E402

# Pipeline-facing names are imported INSIDE the downstream test, not at
# module level (same rationale as test_tort_group07).

DEMANDS = ("D124", "D125", "D126", "D127", "D128", "D129", "D130",
           "D131", "D132", "D133", "D134")

F = Fraction


# ---------------------------------------------------------------------------
# 2/3/5 — entry + independent checker, positive and adverse (per item)
# ---------------------------------------------------------------------------


def _run_D124():
    """只生成董事会批准草稿就自动消除实际利益冲突（ALL_134 反例字段）."""
    out = R.conflict_clearance(R.MATTER_EDGES, R.ETH_REGISTRY)
    rep = K.check_D124(list(R.MATTER_EDGES), list(R.ETH_REGISTRY), out)
    return rep.ok, rep.reasons, out


def _run_D125():
    """移除敏感属性但代理变量仍泄露，不得声称已证明公平（反例字段）."""
    out = R.fairness_checks(R.proxy_keyed, R.LEAK_ROWS)
    rep = K.check_D125(R.proxy_keyed, list(R.LEAK_ROWS), out)
    return rep.ok, rep.reasons, out


def _run_D126():
    """文本写“不共享”不能直接证明代码与运营从不共享（反例字段）."""
    out = R.privacy_compliance(R.SITE_PERMS, [R.SERVICE_FLOW],
                               [R.NO_SHARE_PROMISE])
    rep = K.check_D126(list(R.SITE_PERMS), [tuple(R.SERVICE_FLOW)], out)
    return rep.ok, rep.reasons, out


def _run_D127():
    """遗漏法定项目却用更多可选披露补分，不算满足（反例字段）."""
    out = R.supply_chain_disclosure(R.SC_REGISTER, R.FULL_DONE)
    rep = K.check_D127(list(R.SC_REGISTER), list(R.FULL_DONE), out)
    return rep.ok, rep.reasons, out


def _run_D128():
    """把评分rubric或历史多数偏好当规范真理（反例字段）."""
    out = R.value_ordered_decision(
        {"kind": R.PREM_DECLARED, "order": list(R.PRIVACY_FIRST)})
    rep = K.check_D128({"kind": R.PREM_DECLARED,
                        "order": list(R.PRIVACY_FIRST)}, out)
    return rep.ok, rep.reasons, out


def _run_D129():
    """引用真实但不支持该命题仍应失败（反例字段）."""
    out = R.citation_support(R.REP_SOURCES, [],
                             [R.LOSS_CLAIM, R.COUNT_CLAIM])
    rep = K.check_D129(dict(R.REP_SOURCES), [], [dict(R.LOSS_CLAIM)],
                       out)
    return rep.ok, rep.reasons, out


def _run_D130():
    """从互斥分支各取有利结论合并必须拒绝（反例字段）."""
    out = R.scenario_merge(R.KAPPA1_ONLY)
    rep = K.check_D130(list(R.KAPPA1_ONLY), out)
    return rep.ok, rep.reasons, out


def _run_D131():
    """存在禁止性条文不自动推出任何私人可起诉（反例字段）."""
    out = R.private_action_scan(R.PRIV_ACTION_FRAGMENT)
    rep = K.check_D131(list(R.PRIV_ACTION_FRAGMENT), out)
    return rep.ok, rep.reasons, out


def _run_D132():
    """关键词相似的旁论不能替代核心裁判要旨（反例字段）."""
    out = R.holding_match_entry()
    rep = K.check_D132(R.SCQ_QUESTION, list(R.SCQ_KEYS),
                       list(R.SCQ_WORDS),
                       [dict(c) for c in R.HOLDING_POOL], out)
    return rep.ok, rep.reasons, out


def _run_D133():
    """首个名字抽对不等于全体原告齐全（反例字段）."""
    out = R.plaintiff_extraction(R.SSLA_SEGMENT)
    rep = K.check_D133({"len": R.SSLA_SEGMENT["len"],
                        "mentions": list(R.SSLA_SEGMENT["mentions"])}, out)
    return rep.ok, rep.reasons, out


def _run_D134():
    """统计证据类别命中不意味着识别了个案因果效应（反例字段）."""
    out = R.evidence_classification([R.STAT_PASSAGE, R.DIRECT_PASSAGE])
    rep = K.check_D134([tuple(R.STAT_PASSAGE), tuple(R.DIRECT_PASSAGE)],
                       out)
    return rep.ok, rep.reasons, out


_POSITIVE = {"D124": _run_D124, "D125": _run_D125, "D126": _run_D126,
             "D127": _run_D127, "D128": _run_D128, "D129": _run_D129,
             "D130": _run_D130, "D131": _run_D131, "D132": _run_D132,
             "D133": _run_D133, "D134": _run_D134}


@pytest.mark.parametrize("dem", DEMANDS)
def test_demand_positive(dem):
    """Entry computes the intermediate result; the independent checker
    re-derives the contract from the same input with different code
    paths and passes."""
    ok, reasons, _out = _POSITIVE[dem]()
    assert ok, f"{dem} contract violated: {reasons}"


@pytest.mark.parametrize("dem", DEMANDS)
def test_demand_counterexample(dem):
    """The ALL_134 counterexample field of each demand is distinguishable
    in the entry output with per-item expectations."""
    _ok, _reasons, out = _POSITIVE[dem]()
    if dem == "D124":
        conf = out
        # 登记触发＋义务上报；草稿不消除；权限门槛（非豁免不可清、合伙人不足、面板可清）
        assert conf["duties"] == [("concurrent-client", "disclose-and-screen")]
        assert conf["duties_from_registry"] is True
        assert conf["duties_triggered_in_graph"] is True
        assert conf["draft_clears_nothing"] is True
        assert conf["nonwaivable_never_cleared"] is True
        assert conf["partner_insufficient"] is True
        assert conf["panel_clears_waivable"] is True
    elif dem == "D125":
        fair = out
        # 代理泄露：不变性通过而两组风险 1/0；单标签证书≠公平全概念
        assert fair["leak_invariance"] is True
        assert fair["leak_rate_true"] == F(1)
        assert fair["leak_rate_false"] == F(0)
        assert fair["leak_rates_differ"] is True
        assert fair["leak_certs"] == ["invariance"]
        assert fair["leak_full_claim"] is False
        assert fair["single_tag_is_not_full"] is True
        # PY-PROB face: exact-ℚ Beta coverage through unified.beta
        assert fair["beta_coverage"][True] == F(1, 8)
        assert fair["beta_coverage"][False] == F(7, 8)
        assert fair["beta_coverage_exact"] is True
    elif dem == "D126":
        priv = out
        # 承诺不是判定输入；准许流过门；"不共享"文本旁边的广告流仍失败
        assert priv["verdict"] is True
        assert priv["promise_independent"] is True
        assert priv["any_promise_keeps_verdict"] is True
        assert priv["witness_site_service"] is True
        assert priv["witness_ad_flow_fails"] is True
        assert priv["witness_promise"] == ("email-list", "we never share")
        assert priv["witness_promise_contradicts_flow"] is True
    elif dem == "D127":
        disc = out
        # 法定门逐项；缺一仍败（两条可选补不上）；最佳实践恒 advisory
        assert disc["covered"] is True
        assert disc["missing_statutory"] == []
        assert disc["advisory"] == [("supplier-diversity", "advisory"),
                                    ("open-source-policy", "advisory")]
        assert disc["advisory_typed"] is True
        gap = R.supply_chain_disclosure(R.SC_REGISTER, R.GAP_DONE)
        assert gap["covered"] is False
        assert gap["missing_statutory"] == ["ghg-emissions"]
        assert gap["witness_optional_cannot_compensate"] is True
        assert gap["witness_gap_done_count"] == 4
        assert out["witness_full_covers"] is True
    elif dem == "D128":
        dec = out
        # 决策随声明序；敏感性；无序/多数偏好无决策
        assert dec["witness_privacy_pick_name"] == "balanced-veil"
        assert dec["witness_efficiency_pick"] == "fast-track"
        assert dec["sensitivity"] is True
        assert dec["empty_order_no_decision"] is True
        assert dec["majority_premise_no_decision"] is True
        assert dec["decision_within_options"] is True
    elif dem == "D129":
        cit = out
        # 数值重算绑定；真实但不支持→failed；灌水数值失败；冲突 held
        assert cit["witness_loss_recompute"] == F(500)
        assert cit["witness_loss_claimed"] == F(500)
        assert cit["witness_inflated_recompute"] == F(500)
        assert cit["witness_inflated_claimed"] == F(600)
        assert cit["witness_inflated_fails"] is True
        assert cit["witness_count_recompute"] == F(3)
        assert cit["witness_misused_cite_ok"] is True
        assert cit["witness_misused_scope_fails"] is True
        assert cit["witness_misused_fails"] is True
        assert cit["witness_conflict_holds"] is True
        assert cit["witness_conflict_not_verified"] is True
        assert cit["witness_conflict_free_verified"] is True
        assert cit["numbers_recompute"] == [True, True]
    elif dem == "D130":
        scen = out
        # 单场景装配条件见证；跨场景各取有利结论被拒
        assert scen["outcome"] == "conditional"
        assert scen["scenario"] == "kappa-1"
        assert scen["witness_single_scenario"] is True
        assert scen["witness_cherry_picked_rejected"] is True
        assert scen["no_unconditional_outcome"] is True
    elif dem == "D131":
        priv = out
        # 片段内判定；类型分立；禁止条文不推出私人起诉
        assert priv["has_private_action"] is True
        assert priv["pathways_within_fragment"] is True
        assert priv["types_disjoint"] is True
        # 禁止条文片段判定"无私人起诉途径"（反例：禁止性条文≠可起诉）
        assert priv["witness_prohibition_only"] is True
        assert R.private_action_scan(
            R.PROHIBITION_FRAGMENT)["has_private_action"] is False
        assert R.private_action_scan(
            R.RIGHT_PLUS_BAN_FRAGMENT)["has_private_action"] is False
        assert priv["witness_explicit_pathway"] is True
        assert priv["witness_pathway_cite"] == "§4(c)"
    elif dem == "D132":
        hold = out
        # 核心要旨配上不可迁移证书；关键词相似的旁论不匹配
        assert hold["certificate"] == {
            "cand": "holding-preemption",
            "question": "is the state-law claim preempted",
            "transferable": False}
        assert hold["matched_holding_only"] is True
        assert hold["certificate_not_transferable"] is True
        assert hold["witness_dictum_similar"] is True
        assert hold["witness_dictum_not_holding"] is True
        assert hold["witness_dictum_only_no_match"] is True
    elif dem == "D133":
        extr = out
        # 两原告各带跨度分别抽出；合并名不入；首名≠齐全；越界跨度排除
        assert extr["extracted"] == ["Alice Chen", "Bob Diaz"]
        assert extr["each_backed_by_span"] is True
        assert extr["witness_both_extracted"] is True
        assert extr["witness_separate_keys"] is True
        assert extr["witness_merged_never_enters"] is True
        assert extr["witness_first_only_is_not_complete"] is True
        assert extr["witness_ghost_excluded"] is True
    else:  # D134
        ev = out
        # 三型分类；无 do 桥；PY-PROB 面精确 Fraction 置信度 15/16
        assert ev["witness_statistical"] is True
        assert ev["witness_direct"] is True
        assert ev["witness_neither"] is True
        assert ev["no_do_conclusion_for_any_label"] is True
        assert ev["no_do_conclusion_for_statistical_hit"] is True
        assert ev["classification_not_causal_identification"] is True
        assert ev["beta_confidence_statistical"] == F(15, 16)
        assert ev["beta_confidence_is_fraction"] is True
        assert R.classify_hits(3, 0) == "statistical"
        assert R.classify_hits(0, 2) == "directEvidence"
        assert R.classify_hits(1, 1) == "neither"


@pytest.mark.parametrize("dem", DEMANDS)
def test_checker_rejects_tampered(dem):
    """The independent checker must fail a tampered intermediate result
    (the checker, not the entry, is the judge of the contract)."""
    ok, _reasons, out = _POSITIVE[dem]()
    assert ok  # sanity: the honest result passes its own checker
    tamper_key = {
        "D124": "draft_clears_nothing",
        "D125": "single_tag_is_not_full",
        "D126": "witness_ad_flow_fails",
        "D127": "witness_optional_cannot_compensate",
        "D128": "sensitivity",
        "D129": "witness_conflict_holds",
        "D130": "witness_cherry_picked_rejected",
        "D131": "witness_explicit_pathway",
        "D132": "witness_dictum_only_no_match",
        "D133": "witness_first_only_is_not_complete",
        "D134": "no_do_conclusion_for_statistical_hit",
    }
    tampered = dict(out)
    tampered[tamper_key[dem]] = False  # the adverse flag flipped
    if dem == "D124":
        rep = K.check_D124(list(R.MATTER_EDGES), list(R.ETH_REGISTRY),
                           tampered)
    elif dem == "D125":
        rep = K.check_D125(R.proxy_keyed, list(R.LEAK_ROWS), tampered)
    elif dem == "D126":
        rep = K.check_D126(list(R.SITE_PERMS), [tuple(R.SERVICE_FLOW)],
                           tampered)
    elif dem == "D127":
        rep = K.check_D127(list(R.SC_REGISTER), list(R.FULL_DONE), tampered)
    elif dem == "D128":
        rep = K.check_D128({"kind": R.PREM_DECLARED,
                            "order": list(R.PRIVACY_FIRST)}, tampered)
    elif dem == "D129":
        rep = K.check_D129(dict(R.REP_SOURCES), [], [dict(R.LOSS_CLAIM)],
                           tampered)
    elif dem == "D130":
        rep = K.check_D130(list(R.KAPPA1_ONLY), tampered)
    elif dem == "D131":
        rep = K.check_D131(list(R.PRIV_ACTION_FRAGMENT), tampered)
    elif dem == "D132":
        rep = K.check_D132(R.SCQ_QUESTION, list(R.SCQ_KEYS),
                           list(R.SCQ_WORDS),
                           [dict(c) for c in R.HOLDING_POOL], tampered)
    elif dem == "D133":
        rep = K.check_D133({"len": R.SSLA_SEGMENT["len"],
                            "mentions": list(R.SSLA_SEGMENT["mentions"])},
                           tampered)
    else:  # D134
        rep = K.check_D134([tuple(R.STAT_PASSAGE),
                            tuple(R.DIRECT_PASSAGE)], tampered)
    assert not rep.ok, f"{dem} checker accepted a tampered result: {rep.reasons}"


# ---------------------------------------------------------------------------
# 4 — downstream consumption through the unified pipeline
# ---------------------------------------------------------------------------

def test_downstream_pipeline_consumes_ethics():
    """run_case consumes the CaseInput assembled from the ethics/US-law
    results (the triggered conflict duties and the verified citations
    supply the issue, the unpermitted ad-partner flow stays an explicit
    failure predicate — never silently converted — and the only
    quantities are the recomputed loss total 500 and the plaintiff
    count 2 — computed by the entries, never re-derived); run_trace
    consumes the verified citation as an evidence event and the
    recomputed loss total as one exact posting."""
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

    intake = R.build_ethics_intake()
    case = R.build_case_input(intake)
    env = R.build_environment(intake)

    # the assembled carriers are exactly the ethics/US-law outputs
    assert case.issues == ("ETHICS_RELIABILITY",)
    assert case.claims[0].claimant == "client"
    assert case.claims[0].respondent == "firm"
    # D126: the unpermitted privacy flow rides on the case as a defense
    # gap; the flow stays awaiting — never dropped
    assert case.defenses[0].defense_id == "def-privacy-gap"
    assert case.defenses[0].basis == "privacy_flow_noncompliant"
    assert case.defenses[0].target_claims == ("c0",)
    standings = {(f.proposition.predicate, f.standing.name)
                 for f in case.fact_records}
    assert ("conflict-registry-triggered", "ADMITTED_POSITIVE") in standings
    assert ("citation-verified", "ADMITTED_POSITIVE") in standings
    assert ("privacy_flow_noncompliant", "AWAITING_ADMISSION") in standings
    # D129/D133: the only quantities are the recomputed loss total (500,
    # exact Fraction from the citation entry) and the plaintiff count
    # (2, span-annotated extraction) — never re-derived
    assert [q.value for q in case.quantities] == [Fraction(500),
                                                  Fraction(2)]
    assert {q.basis_kind for q in case.quantities} == \
        {"loss-recompute", "plaintiff-extraction"}

    run = run_case(case, env)
    assert run.status is RunStatus.COMPLETE
    assert run.failures == ()
    judgments = run.judgments_of("c0")
    assert judgments and Judgment.ESTABLISHED in judgments

    # trace: the verified citation lands as an evidence event and the
    # recomputed loss total (500) as one exact posting on the
    # LOSS_RECOMPUTE basis; the unpermitted flow posts nothing
    events = R.ethics_trace_events(intake)
    assert [e.event.event_id for e in events] == \
        ["ev-citation-verified", "post-loss-recompute"]
    final, notes = run_trace(case.initial_state, events, env)
    event_ids = [e.event_id for e in final.events]
    assert "ev-citation-verified" in event_ids
    assert "post-loss-recompute" in event_ids
    assert gross_of(final, "LOSS_RECOMPUTE") == Fraction(500)
    posted = [e for e in final.ledger
              if e.kind.name == "GROSS_ALLOCATED"
              and e.basis_key == "LOSS_RECOMPUTE"]
    assert sorted(e.amount for e in posted) == [Fraction(500)]
    assert notes  # the step relation actually produced observations

    # step_event alone: one step, exactly the event's own semantics
    one = step_event(case.initial_state, events[0], env)
    assert one.next_env is env

    # the ethics decisions stay on the bundle: the conflict clearance
    # (D124), the fairness certificates (D125), the privacy compliance
    # (D126), the disclosure coverage (D127), the value-ordered
    # decision (D128), the citation support (D129), the scenario merge
    # (D130), the private-action scan (D131), the holding match (D132),
    # the plaintiff extraction (D133) and the evidence classification
    # (D134)
    assert intake["conflicts"]["draft_clears_nothing"] is True
    assert intake["fairness"]["single_tag_is_not_full"] is True
    assert intake["privacy"]["witness_promise_contradicts_flow"] is True
    assert intake["disclosure"]["witness_full_covers"] is True
    assert intake["decision"]["sensitivity"] is True
    assert intake["citations"]["witness_misused_fails"] is True
    assert intake["scenarios"]["witness_cherry_picked_rejected"] is True
    assert intake["private_action"]["witness_explicit_pathway"] is True
    assert intake["holding"]["witness_dictum_only_no_match"] is True
    assert intake["plaintiffs"]["witness_first_only_is_not_complete"] is True
    assert intake["evidence"]["no_do_conclusion_for_any_label"] is True


# ---------------------------------------------------------------------------
# 6 — synthetic receipts through completion.validate_binding
# ---------------------------------------------------------------------------

_REQUIREMENTS = {
    r["id"]: r
    for r in json.loads((SPEC / 'REQUIREMENTS.json').read_text(encoding='utf-8'))
}

_SEMANTICS = {
    "D124": "the interest-relation graph triggers the registered "
             "conflicts and their disposition obligations (every "
             "reported duty pair comes from a registered rule whose "
             "trigger kind occurs in the graph), and a waiver or "
             "approval clears a conflict only when granted by adequate "
             "authority — non-waivable conflicts are never cleared, "
             "waivable ones need the ethics panel, and a draft clears "
             "nothing: generating a board-approval draft does not "
             "auto-erase the actual conflict.",
    "D125": "the counterfactual invariance check and the group risk "
             "indicators are separate tests, separately certified (a "
             "certificate attests exactly one tag; the full-fairness "
             "claim needs both): the proxy-keyed witness passes "
             "invariance while the two groups' rates are 1 and 0, so "
             "invariance is not fairness — removing the sensitive "
             "attribute while a proxy leaks it cannot claim proven "
             "fairness; the group-risk indicators carry exact-ℚ Beta "
             "coverage through the unified mirror of ratBernCdf.",
    "D126": "the privacy-policy promises, the actual data flows and the "
             "permitted uses stay separate: the compliance verdict is a "
             "function of the permission table and the flows only (any "
             "promise text leaves the verdict unchanged), a compliant "
             "flow's category/purpose pair is a registered permission, "
             "and the unpermitted ad-partner marketing flow fails even "
             "though the policy says 'we never share'.",
    "D127": "the statutory-coverage gate checks every statutory item of "
             "the register (covered iff each is in the done list): two "
             "statutory plus two best-practice entries — four done — "
             "still fail the gate because optional disclosures cannot "
             "compensate a missing statutory item, and the "
             "best-practice readout stays advisory-typed.",
    "D128": "the decision runs under the declared lexicographic value "
             "order (privacy-first picks balanced-veil, "
             "efficiency-first picks fast-track — the decision tracks "
             "the declared order, the sensitivity witness); with no "
             "declared order there is no decision, and a historical "
             "majority preference as a premise licenses nothing — "
             "values are not derived from facts.",
    "D129": "citation read-back, numeric recomputation and support "
             "scope bind to each claim item-wise; a real citation that "
             "does not support the proposition fails (the docket index "
             "cited for the loss total), an inflated number fails the "
             "exact recomputation, and an unresolved authenticity "
             "conflict holds the claim instead of escalating it to a "
             "verdict.",
    "D130": "conclusions from a single scenario assemble into a "
             "conditional witness carrying that label; conclusions "
             "cherry-picked from two mutually exclusive scenarios are "
             "rejected outright — no unconditional witness is ever "
             "produced.",
    "D131": "the private-action pathway and the substantive rights "
             "inside the selected statute fragment are separately typed "
             "(a provision is never both), and the determination is "
             "made only within the fragment: a prohibition-only "
             "fragment, and a prohibition-plus-rights fragment, both "
             "yield 'no private action' — a prohibitory provision does "
             "not imply private actionability.",
    "D132": "a holding match requires the candidate to be a core "
             "holding with the question's issue key and real keyword "
             "overlap; a keyword-similar dictum never substitutes, and "
             "every match certificate stays non-transferable (transfer "
             "to a new case needs its own relevance proof).",
    "D133": "every extracted plaintiff is backed by an independently "
             "annotated valid span (start ≤ end ≤ segment length); the "
             "two co-plaintiffs are extracted as separate keys, the "
             "merged name never enters, and an out-of-segment span is "
             "excluded — the first name alone is not the full "
             "plaintiff set.",
    "D134": "the output is the text classification (statistical / "
             "direct evidence / neither) by marker hits; the "
             "classification-to-causation bridge is structurally absent "
             "— no do-effect conclusion is generated for any label, and "
             "the statistical-evidence category hit does not identify "
             "an individual causal effect; the statistical label "
             "confidence is an exact-ℚ Beta computation through the "
             "unified mirror of ratBernCdf.",
}

_ENTRY = {
    "D124": "conflict_clearance",
    "D125": "fairness_checks",
    "D126": "privacy_compliance",
    "D127": "supply_chain_disclosure",
    "D128": "value_ordered_decision",
    "D129": "citation_support",
    "D130": "scenario_merge",
    "D131": "private_action_scan",
    "D132": "holding_match_entry",
    "D133": "plaintiff_extraction",
    "D134": "evidence_classification",
}

_REGISTERED = {
    "D124": "JurisLean.FullMath.Evidence.step_rules_mono",
    "D125": "JurisLean.FullMath.Evidence.step_rules_mono",
    "D126": "JurisLean.FullMath.Evidence.step_rules_mono",
    "D127": "JurisLean.FullMath.Evidence.step_rules_mono",
    "D128": "JurisLean.FullMath.Evidence.step_rules_mono",
    "D129": "JurisLean.FullMath.Evidence.step_rules_mono",
    "D130": "JurisLean.FullMath.Evidence.step_rules_mono",
    "D131": "JurisLean.FullMath.Probability.condition_incompatible_iff",
    "D132": "JurisLean.FullMath.Probability.condition_incompatible_iff",
    "D133": "JurisLean.FullMath.Probability.condition_incompatible_iff",
    "D134": "JurisLean.FullMath.Probability.condition_incompatible_iff",
}

_CARRIERS = {
    "D124": ["JurisLean.FullMath.Contracts.ethDuties",
             "JurisLean.FullMath.Contracts.ethCleared"],
    "D125": ["JurisLean.FullMath.Contracts.invariantUnder",
             "JurisLean.FullMath.Contracts.groupRate"],
    "D126": ["JurisLean.FullMath.Contracts.flowOk",
             "JurisLean.FullMath.Contracts.flowsOk"],
    "D127": ["JurisLean.FullMath.Contracts.statCovered",
             "JurisLean.FullMath.Contracts.advisoryDone"],
    "D128": ["JurisLean.FullMath.Contracts.decideBy",
             "JurisLean.FullMath.Contracts.decideUnder"],
    "D129": ["JurisLean.FullMath.Contracts.claimVerdict",
             "JurisLean.FullMath.Contracts.recompute"],
    "D130": ["JurisLean.FullMath.Contracts.assemble",
             "JurisLean.FullMath.Contracts.allSameScen"],
    "D131": ["JurisLean.FullMath.Contracts.provOf",
             "JurisLean.FullMath.Contracts.hasPrivAction"],
    "D132": ["JurisLean.FullMath.Contracts.holdingMatch",
             "JurisLean.FullMath.Contracts.keywordSimilar"],
    "D133": ["JurisLean.FullMath.Contracts.plaintiffsOf",
             "JurisLean.FullMath.Contracts.spanOk"],
    "D134": ["JurisLean.FullMath.Contracts.classifyHits",
             "JurisLean.FullMath.Contracts.doFromEvidence"],
}


def _binding_row(dem, required):
    """Template for the controller's BINDINGS.json back-fill
    (DEMAND:D124–D134 rows).  Passes completion.validate_binding as-is."""
    return {
        "id": f"DEMAND:{dem}",
        "theorem": required["theorem"],
        "contract": required["contract"],
        "proof_mode": "KERNEL_CONTRACT_PROOF",
        "formal_scope": "Group-14/15 ethics, privacy, expression-"
                        "reliability and US-law demand instance in the "
                        "shared semantic framework: this item's own "
                        "contract semantics over region-local ethics/US-"
                        "law operational defs (authority-gated conflict "
                        "clearance, separately certified fairness "
                        "checks, promise/flow/permission separation, "
                        "statutory coverage with advisory typing, "
                        "declared-value-order decisions with "
                        "sensitivity, item-wise citation support with "
                        "conflict holding, scenario-tagged assembly, "
                        "within-fragment private-action typing, "
                        "non-transferable holding matches, span-backed "
                        "plaintiff extraction, and statistical/direct "
                        "text classification without a causation "
                        "bridge) plus the group-registered component "
                        "(Evidence.step_rules_mono for group 14, "
                        "Probability.condition_incompatible_iff for "
                        "group 15), with its adverse case executed as "
                        "a negative test.",
        "independent_semantics": _SEMANTICS[dem],
        "algorithm": "tools/full_math/implementation/ethics_ref.py "
                     f"{_ENTRY[dem]} computes the intermediate result "
                     f"from structured input (the exact-ℚ Beta face "
                     f"unified.beta.beta_cdf_integer — the mirror of "
                     f"Seams/UnifiedBetaDomain.ratBernCdf — consumed by "
                     f"the D125 group-risk coverage and the D134 label "
                     f"confidence); "
                     f"ethics_check.check_{dem} re-derives the "
                     f"contract independently with different code paths "
                     f"(index scans, decision tables, row counters, "
                     f"gate ladders, score-vector picks, label-set "
                     f"assembly, bound-checked walks, two-column "
                     f"tables) — zero code sharing with the reference.",
        "observation_contract": "Inputs are the declared structures "
                                "(interest-relation edges and ethics "
                                "registry rows with waiver flags and "
                                "approval states, fairness audit rows "
                                "with protected/proxy/case fields and "
                                "certificates, privacy ledgers of "
                                "promises, permissions and flows, "
                                "disclosure registers with statutory/"
                                "best-practice typing, value premises "
                                "with declared orders and options with "
                                "integer preference scores, source "
                                "registries with support scopes, "
                                "conflict pairs and claims with exact "
                                "Fraction data, scenario-tagged "
                                "conclusions, statute fragments with "
                                "provision typing, holding candidates "
                                "with status/keys/words, segments with "
                                "annotated mention spans, and passage "
                                "marker-hit counts); outputs are "
                                "exactly the contract quantities (the "
                                "triggered duties with the authority-"
                                "gated clearance verdicts, the "
                                "invariance verdict with the group "
                                "rates and Beta coverage, the per-flow "
                                "compliance verdicts, the statutory "
                                "coverage with the advisory readout, "
                                "the decision with the sensitivity and "
                                "majority-rejection witnesses, the "
                                "verified/failed/held verdicts with "
                                "the recomputed numbers, the "
                                "conditional/rejected assembly, the "
                                "within-fragment pathway typing, the "
                                "match certificate, the extracted "
                                "plaintiff keys, and the classification "
                                "labels with the absent causation "
                                "bridge).",
        "external_assumptions": "The applicable professional-conduct "
                                "rules and non-waivable conflict "
                                "classes, the fairness policy that "
                                "declares which attributes must not "
                                "influence which outputs and the "
                                "representativeness of the audited "
                                "rows, the actual data practices "
                                "behind the privacy ledgers and the "
                                "consent semantics of the permission "
                                "table, the substantive truth and "
                                "sufficiency of supply-chain "
                                "disclosures, the authorization of the "
                                "declared value orderings, the "
                                "authenticity of cited sources and the "
                                "resolution of conflicts, the "
                                "mutual exclusivity of scenarios, the "
                                "US-statute fragment semantics and "
                                "holding typologies, the correctness "
                                "of span annotations on new texts, "
                                "and the classifier's real-world "
                                "performance remain external "
                                "validation obligations, not part of "
                                "this registration.",
        "proof_sources": [
            "proofs/lean/juris_lean/JurisLean/FullMath/Contracts.lean",
            "proofs/lean/juris_lean/JurisLean/FullMath/Acceptance.lean",
        ],
        "implementation_sources": [
            "tools/full_math/implementation/ethics_ref.py",
            "tools/full_math/implementation/ethics_check.py",
        ],
        "test_ids": [
            "tools/full_math/implementation_tests::"
            "test_ethics_group14.py::"
            f"test_demand_positive[{dem}]",
            "tools/full_math/implementation_tests::"
            "test_ethics_group14.py::"
            f"test_demand_counterexample[{dem}]",
            "tools/full_math/implementation_tests::"
            "test_ethics_group14.py::"
            "test_downstream_pipeline_consumes_ethics",
        ],
        "negative_test_ids": [
            "tools/full_math/implementation_tests::"
            "test_ethics_group14.py::"
            f"test_checker_rejects_tampered[{dem}]",
        ],
        "semantic_links": [_REGISTERED[dem]] + _CARRIERS[dem],
    }


@pytest.mark.parametrize("dem", DEMANDS)
def test_b14_binding_receipt(dem):
    """Synthetic receipt: the binding row for DEMAND:D1XX passes
    completion.validate_binding against the real repository files."""
    required = _REQUIREMENTS[f"DEMAND:{dem}"]
    C.validate_binding(_binding_row(dem, required), required, repo=REPO)


@pytest.mark.parametrize("dem", DEMANDS)
def test_b14_binding_receipt_negative(dem):
    """A tampered receipt (swapped theorem) is rejected."""
    required = _REQUIREMENTS[f"DEMAND:{dem}"]
    row = dict(_binding_row(dem, required))
    row["theorem"] = "JurisLean.FullMath.Acceptance.nonexistent_demand"
    with pytest.raises(C.EvidenceError):
        C.validate_binding(row, required, repo=REPO)
