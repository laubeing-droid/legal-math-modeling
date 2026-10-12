"""W2-A batch B13 acceptance tests: D116-D123, group 13 办案、交易
工作流与策略.

Six pieces per demand (docs/full-math/W2B_CLASSIFICATION.md §5.4):

1. Lean contract  — Contracts.demand_D116..D123 restated as this item's
   own semantics over region-local operational defs, with the
   group-registered Bellman component
   (JurisLean.FullMath.Numeric.bellman_onesided) as the first conjunct;
   verified by the whole-repo replay build, and the registration-format
   tests live in test_registration_bindings.py.
2. Python entry   — tools/full_math/implementation/workflow_ref.py
   per-item entries computing the intermediate result from real
   structured input (the Bellman surface mirrored from
   JurisLean.FullMath.Numeric.Bellman and actually consumed by the
   D118 value model).
3. Independent checker — workflow_check.py re-derives the contract
   inline with different code paths (index scans, round counters,
   branch tables, selection maxima, gate ladders, row-matching scans,
   flag accumulation); no witness callbacks, no expectations from the
   main implementation, zero code sharing.
4. Downstream consumption — unified.pipeline run_case / step_event /
   run_trace consume the workflow results through the adapters in
   workflow_ref (build_case_input / build_environment /
   workflow_trace_events).
5. Positive and adverse cases — the ALL_134 counterexample field of
   each demand is executed with per-item expectations.
6. Synthetic receipt — completion.validate_binding rows for
   DEMAND:D116-D123 (the ``_binding_row`` template below is ready for
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
# foreign tree (same rationale as the B07 sibling).
_existing_unified = sys.modules.get('unified')
if _existing_unified is None or \
        'unified_math_v2' not in str(getattr(_existing_unified, '__file__', '')):
    for _shared in ("reference", "unified", "unified_v21"):
        for _name in [m for m in sys.modules
                      if m == _shared or m.startswith(_shared + ".")]:
            del sys.modules[_name]

from tools.full_math.implementation import workflow_check as K  # noqa: E402
from tools.full_math.implementation import workflow_ref as R  # noqa: E402
import completion as C  # noqa: E402

# Pipeline-facing names are imported INSIDE the downstream test, not at
# module level (same rationale as test_tort_group07).

DEMANDS = ("D116", "D117", "D118", "D119", "D120", "D121", "D122", "D123")

F = Fraction

_REQUIRED = ("charter", "litigation-search", "board-minutes")
_VDR = ("charter", "board-minutes")

_ACTIONS = (
    (R.KIND_CONFIRM, "clause-7", True, F(3, 4), F(100), F(10)),
    (R.KIND_SUPPLEMENT, "missing-board-res", True, F(1, 2), F(40), F(5)),
    (R.KIND_WAIVER, "mandatory-audit", False, F(1), F(100), F(0)),
)

_RISKS = R.INFRA_RISKS

_SAMPLE = ("change-of-control-consent", 3, 5)


# ---------------------------------------------------------------------------
# 2/3/5 — entry + independent checker, positive and adverse (per item)
# ---------------------------------------------------------------------------


def _run_D116():
    """缺失材料不得通过从现有目录生成“必需清单”抹去（ALL_134 反例字段）."""
    out = R.diligence_gap(_REQUIRED, _VDR)
    rep = K.check_D116(list(_REQUIRED), list(_VDR), out)
    return rep.ok, rep.reasons, out


def _run_D117():
    """互相依赖形成环仍生成无条件可执行清单（ALL_134 反例字段）."""
    out = R.closing_schedule(R.SHIP_TASKS)
    rep = K.check_D117(R.SHIP_TASKS, out)
    return rep.ok, rep.reasons, out


def _run_D118():
    """强制法义务不能由私人豁免事件删除（ALL_134 反例字段）."""
    out = R.clarification_actions(_ACTIONS)
    rep = K.check_D118(list(_ACTIONS), out)
    return rep.ok, rep.reasons, out


def _run_D119():
    """将任意重要性权重误标法定唯一优先序（ALL_134 反例字段）."""
    out = R.risk_ranking(_RISKS)
    rep = K.check_D119(list(_RISKS), out)
    return rep.ok, rep.reasons, out


def _run_D120():
    """多数合同如此写不自动推导依法必须如此（ALL_134 反例字段）."""
    out = R.market_clause_advice(*_SAMPLE)
    rep = K.check_D120(3, 5, out)
    return rep.ok, rep.reasons, out


def _run_D121():
    """将非当事人异议路径无条件给另一诉讼当事人（ALL_134 反例字段）."""
    out = R.subpoena_options(True, True, True)
    rep = K.check_D121(True, True, True, out)
    return rep.ok, rep.reasons, out


def _run_D122():
    """只列弱反方并以数量宣称已回应最强反方（ALL_134 反例字段）."""
    out = R.argument_outline(R.FULL_OUTLINE)
    rep = K.check_D122(out)
    return rep.ok, rep.reasons, out


def _run_D123():
    """接口超时返回空列表，不能写成查无诉讼（ALL_134 反例字段）."""
    out = R.provenance_chain([R.LITIGATION_ASSERTION])
    rep = K.check_D123(out)
    return rep.ok, rep.reasons, out


_POSITIVE = {"D116": _run_D116, "D117": _run_D117, "D118": _run_D118,
             "D119": _run_D119, "D120": _run_D120, "D121": _run_D121,
             "D122": _run_D122, "D123": _run_D123}


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
    if dem == "D116":
        gap = out
        # 差集精确＋未决行；litigation-search 缺失不能被资料室回声抹去
        assert gap["missing"] == ["litigation-search"]
        assert gap["pending"] == [("litigation-search", "pending")]
        assert gap["gap_exact"] is True
        assert gap["missing_become_pending"] is True
        assert gap["no_silent_drop"] is True
        assert gap["witness_missing_kept"] is True
        assert gap["witness_not_in_room"] is True
        assert gap["fabricated_required_empty"] is True
        assert gap["fabrication_cannot_erase"] is True
    elif dem == "D117":
        sch = out
        # 无环链过裁定；两任务环报不可行（none），无任何合法序
        assert sch["order"] == ["board-approval", "signature", "closing"]
        assert sch["order_legal"] is True
        assert sch["ship_feasible"] is True
        assert sch["cycle_verdict"] is None
        assert sch["cycle_infeasible_reported"] is True
        assert sch["no_unconditional_checklist_for_cycle"] is True
        stuck = R.closing_schedule(R.CYC_TASKS)
        assert stuck["feasible"] is False
        assert stuck["order"] is None
    elif dem == "D118":
        clar = out
        # 书面确认/补证恒合法；强制规范豁免非法；价值=明确模型 65/15
        assert clar["confirm_always_legal"] is True
        assert clar["supplement_always_legal"] is True
        assert clar["waiver_needs_waivable"] is True
        assert clar["mandatory_waiver_illegal"] is True
        assert clar["witness_value_confirm"] == F(65)
        assert clar["witness_value_supplement"] == F(15)
        assert clar["value_from_explicit_model"] is True
        # the registered Bellman component is actually consumed
        assert clar["bellman_one_sided_bound_holds"] is True
        assert clar["bellman_horizons"][0] == {"clarify": F(0),
                                               "closing": F(0)}
        v1 = clar["bellman_horizons"][1]
        assert v1["closing"] == F(100)  # close now from closing
        assert v1["clarify"] == F(65)   # seek confirmation now
    elif dem == "D119":
        risks = out
        # 40/15/2 降序；硬约束条目被滤除；origin 非法定；权重变则序变
        assert risks["readout"] == [("power-grid", 40), ("revenue-stream", 15),
                                    ("ip-license", 2)]
        assert risks["sorted_descending"] is True
        assert risks["origin"] == "explicit-preference"
        assert risks["origin_not_statutory"] is True
        assert risks["weights_change_order"] is True
        assert risks["cfg_a_names"] == ["revenue-stream", "power-grid"]
        assert risks["cfg_b_names"] == ["power-grid", "revenue-stream"]
        blocked = R.risk_ranking(R.BLOCKED_TOP)
        assert blocked["blocked_excluded_any_weight"] is True
        assert blocked["witness_blocked_top_score"] == 100
        assert [i[0] for i in blocked["worklist"]] == \
            ["power-grid", "revenue-stream"]
    elif dem == "D120":
        advice = out
        # 3/5 多数样本仍是 marketSample，产不出 legalDuty
        assert advice["share"] == F(3, 5)
        assert advice["typed_market_sample"] is True
        assert advice["never_legal_duty"] is True
        assert advice["advice_differs_from_duty"] is True
        assert advice["majority_is_majority"] is True
        assert advice["majority_still_not_duty"] is True
        assert advice["majority_cannot_be_duty"] is True
    elif dem == "D121":
        sub = out
        # 完整上下文三选项；当事人缺 quash；逾期全空；期限普遍前置
        assert sub["options"] == ["quash", "vacate", "protective"]
        assert sub["full_context_options"] == ["quash", "vacate",
                                               "protective"]
        assert sub["party_context_options"] == ["vacate", "protective"]
        assert sub["party_misses_quash"] is True
        assert sub["nonparty_path_not_unconditional"] is True
        assert sub["late_context_empty"] is True
        assert sub["deadline_not_cured"] is True
        assert sub["timeliness_precondition"] is True
    elif dem == "D122":
        outline = out
        # 全提纲覆盖；弱提纲 3 项不过门；最佳反驳缺失
        assert outline["covers_frozen"] is True
        assert outline["deps_kept"] is True
        assert outline["alts_kept"] is True
        assert outline["weak_outline_fails"] is True
        assert outline["weak_count_three"] is True
        assert outline["count_is_not_coverage"] is True
        assert outline["best_rebuttal_missing"] is True
    else:  # D123
        prov = out
        # 有据断言过门；超时读 unavailable 而非查无；空洞断言拒收
        assert prov["all_sourced"] is True
        assert prov["full_assertion_sourced"] is True
        assert prov["timeout_readout"] == "unavailable"
        assert prov["timeout_is_unavailable"] is True
        assert prov["timeout_not_no_records"] is True
        assert prov["only_ok_empty_is_no_records"] is True
        assert prov["ok_one_found"] is True
        assert prov["hollow_rejected"] is True
        assert prov["timeout_never_negative_finding"] is True
        assert R.readout_of("timeout") == "unavailable"
        assert R.readout_of([]) == "no_records"
        assert R.readout_of(["docket-2026-001"]) == "found 1"


@pytest.mark.parametrize("dem", DEMANDS)
def test_checker_rejects_tampered(dem):
    """The independent checker must fail a tampered intermediate result
    (the checker, not the entry, is the judge of the contract)."""
    ok, _reasons, out = _POSITIVE[dem]()
    assert ok  # sanity: the honest result passes its own checker
    if dem == "D116":
        tampered = dict(out)
        tampered["missing"] = []  # the room echo erased the gap
        rep = K.check_D116(list(_REQUIRED), list(_VDR), tampered)
    elif dem == "D117":
        tampered = dict(out)
        tampered["cycle_verdict"] = ["task-a", "task-b"]  # unconditional
        rep = K.check_D117(R.SHIP_TASKS, tampered)
    elif dem == "D118":
        tampered = dict(out)
        tampered["mandatory_waiver_illegal"] = False  # mandatory waived
        rep = K.check_D118(list(_ACTIONS), tampered)
    elif dem == "D119":
        tampered = dict(out)
        tampered["origin_not_statutory"] = False  # mislabeled statutory
        rep = K.check_D119(list(_RISKS), tampered)
    elif dem == "D120":
        tampered = dict(out)
        tampered["majority_still_not_duty"] = False  # majority = duty
        rep = K.check_D120(3, 5, tampered)
    elif dem == "D121":
        tampered = dict(out)
        tampered["party_misses_quash"] = False  # quash given to a party
        rep = K.check_D121(True, True, True, tampered)
    elif dem == "D122":
        tampered = dict(out)
        tampered["count_is_not_coverage"] = False  # count claims coverage
        rep = K.check_D122(tampered)
    else:  # D123
        tampered = dict(out)
        tampered["timeout_not_no_records"] = False  # timeout = 查无
        rep = K.check_D123(tampered)
    assert not rep.ok, f"{dem} checker accepted a tampered result: {rep.reasons}"


# ---------------------------------------------------------------------------
# 4 — downstream consumption through the unified pipeline
# ---------------------------------------------------------------------------

def test_downstream_pipeline_consumes_workflow():
    """run_case consumes the CaseInput assembled from the
    workflow-strategy results (the exact VDR gap and the feasible
    closing order supply the issue, the still-pending
    litigation-search document stays awaiting — never silently
    dropped, and the only quantities are the confirmation value 65 and
    the top risk score 40 — computed by the explicit models, never
    re-derived); run_trace consumes the provenance-witnessed assertion
    as an evidence event and the clarification value as one exact
    posting."""
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

    intake = R.build_workflow_intake()
    case = R.build_case_input(intake)
    env = R.build_environment(intake)

    # the assembled carriers are exactly the workflow outputs
    assert case.issues == ("WORKFLOW_STRATEGY",)
    assert case.claims[0].claimant == "client"
    assert case.claims[0].respondent == "counterparty"
    # D116: the pending litigation-search document rides on the case as
    # a defense gap; the missing document stays awaiting — never dropped
    assert case.defenses[0].defense_id == "def-pending-search"
    assert case.defenses[0].basis == "diligence_document_pending"
    assert case.defenses[0].target_claims == ("c0",)
    standings = {(f.proposition.predicate, f.standing.name)
                 for f in case.fact_records}
    assert ("vdr-gap-exact", "ADMITTED_POSITIVE") in standings
    assert ("closing-order-feasible", "ADMITTED_POSITIVE") in standings
    assert ("diligence-document-pending", "AWAITING_ADMISSION") in standings
    # D118/D119: the only quantities are the confirmation value (65,
    # Bellman-mirrored prediction model) and the top risk score (40,
    # explicit preference) — exact Fractions, never re-derived
    assert [q.value for q in case.quantities] == [Fraction(65),
                                                  Fraction(40)]
    assert {q.basis_kind for q in case.quantities} == \
        {"clarification-value-model", "risk-ranking-readout"}

    run = run_case(case, env)
    assert run.status is RunStatus.COMPLETE
    assert run.failures == ()
    judgments = run.judgments_of("c0")
    assert judgments and Judgment.ESTABLISHED in judgments

    # trace: the sourced assertion lands as an evidence event and the
    # clarification value (65) as one exact posting on the
    # CLARIFICATION_VALUE basis; the pending document posts nothing
    events = R.workflow_trace_events(intake)
    assert [e.event.event_id for e in events] == \
        ["ev-sourced-assertion", "post-clarification-value"]
    final, notes = run_trace(case.initial_state, events, env)
    event_ids = [e.event_id for e in final.events]
    assert "ev-sourced-assertion" in event_ids
    assert "post-clarification-value" in event_ids
    assert gross_of(final, "CLARIFICATION_VALUE") == Fraction(65)
    posted = [e for e in final.ledger
              if e.kind.name == "GROSS_ALLOCATED"
              and e.basis_key == "CLARIFICATION_VALUE"]
    assert sorted(e.amount for e in posted) == [Fraction(65)]
    assert notes  # the step relation actually produced observations

    # step_event alone: one step, exactly the event's own semantics
    one = step_event(case.initial_state, events[0], env)
    assert one.next_env is env

    # the workflow decisions stay on the bundle: the VDR gap (D116),
    # the closing schedule (D117), the clarification gates and values
    # (D118), the risk ranking (D119), the market-sample advice (D120),
    # the subpoena options (D121), the outline coverage (D122) and the
    # provenance chain (D123)
    assert intake["gap"]["fabrication_cannot_erase"] is True
    assert intake["schedule"]["no_unconditional_checklist_for_cycle"] is True
    assert intake["clarifications"]["mandatory_waiver_illegal"] is True
    assert intake["clarifications"]["bellman_one_sided_bound_holds"] is True
    assert intake["risks"]["weights_change_order"] is True
    assert intake["advice"]["majority_still_not_duty"] is True
    assert intake["subpoena"]["party_misses_quash"] is True
    assert intake["outline"]["count_is_not_coverage"] is True
    assert intake["provenance"]["timeout_never_negative_finding"] is True


# ---------------------------------------------------------------------------
# 6 — synthetic receipts through completion.validate_binding
# ---------------------------------------------------------------------------

_REQUIREMENTS = {
    r["id"]: r
    for r in json.loads((SPEC / 'REQUIREMENTS.json').read_text(encoding='utf-8'))
}

_SEMANTICS = {
    "D116": "the required-documents minus VDR-catalog gap is exact "
             "(member of the gap iff required and not in the catalog, "
             "the required list never re-derived from the catalog), "
             "every missing document becomes an explicit pending row "
             "instead of being dropped, and the witness "
             "(litigation-search required, only the charter in the "
             "room) keeps the missing item pending — it cannot be "
             "erased by generating the required list from what the "
             "room already has.",
    "D117": "occurrences, permissions and prerequisites compose a "
             "legal closing order: each task is permitted and runs "
             "after its prerequisite; the acyclic board-approval → "
             "signature → closing chain receives its executable "
             "checklist, while the two-task dependency cycle is "
             "reported infeasible (none) — no unconditional checklist "
             "is ever produced for the cycle.",
    "D118": "written confirmation, waiver and supplementary evidence "
             "are gated legal moves: confirmation and supplement are "
             "always legal, a waiver only against a waivable norm (the "
             "mandatory-audit waiver stays illegal), and each move's "
             "value is computed by the explicit prediction model "
             "prob×gain−cost (witnesses 3/4×100−10=65 and "
             "1/2×40−5=15) on the Bellman backward-induction mirror of "
             "the registered component.",
    "D119": "the risk ranking executes the declared preference weight × "
             "risk measure in descending order (40/15/2 witness), "
             "hard-blocked items are filtered out before any weight is "
             "applied (the score-100 unpermitted plant stays out), the "
             "readout declares its origin as an explicit preference — "
             "never a statutory order — and the same measures under "
             "two weight vectors rank differently, so no weight vector "
             "is the statutory unique priority.",
    "D120": "market-clause distribution and normative force stay typed "
             "apart: advice built from market data is typed "
             "marketSample with the share it actually has (a 3/5 "
             "majority), declares the market-sample basis, and a 3/5 "
             "majority never yields any legalDuty-typed advice — the "
             "majority itself is not a source of legal obligation.",
    "D121": "quash/vacate/protective measures compose from "
             "jurisdiction/standing/stage/deadline gates: timeliness is "
             "a universal precondition of every measure, the "
             "non-party/pre-trial/timely context gets all three "
             "options, the party context does not get the non-party "
             "quash path, and the late context gets nothing — the "
             "deadline is not cured by standing or stage.",
    "D122": "the argument outline covers the frozen claim/rebuttal "
             "graph with every node's evidence dependencies and "
             "alternative (备位) positions kept; the weak outline (the "
             "main claim plus two weak rebuttals — three covered ids) "
             "fails coverage because the best rebuttal and the "
             "primary/fallback structure are missing — the count alone "
             "does not answer the strongest counter-argument.",
    "D123": "every data assertion of the final report links its query "
             "inputs, intermediate joins, original records and "
             "transform witness; a timed-out tool query reads back "
             "unavailable, never no-records, and only an ok empty "
             "result is a verified no-records; the hollow assertion "
             "(no joins, no records, a silently-empty transform) is "
             "rejected.",
}

_ENTRY = {
    "D116": "diligence_gap",
    "D117": "closing_schedule",
    "D118": "clarification_actions",
    "D119": "risk_ranking",
    "D120": "market_clause_advice",
    "D121": "subpoena_options",
    "D122": "argument_outline",
    "D123": "provenance_chain",
}

_SEMANTIC_LINKS = {
    "D116": ["JurisLean.FullMath.Numeric.bellman_onesided",
             "JurisLean.FullMath.Contracts.vdrGap",
             "JurisLean.FullMath.Contracts.toPending"],
    "D117": ["JurisLean.FullMath.Numeric.bellman_onesided",
             "JurisLean.FullMath.Contracts.cloLegalOrder",
             "JurisLean.FullMath.Contracts.cloVerdict"],
    "D118": ["JurisLean.FullMath.Numeric.bellman_onesided",
             "JurisLean.FullMath.Contracts.clarLegal",
             "JurisLean.FullMath.Contracts.clarValue"],
    "D119": ["JurisLean.FullMath.Numeric.bellman_onesided",
             "JurisLean.FullMath.Contracts.riskRank",
             "JurisLean.FullMath.Contracts.rankOrigin"],
    "D120": ["JurisLean.FullMath.Numeric.bellman_onesided",
             "JurisLean.FullMath.Contracts.marketShare",
             "JurisLean.FullMath.Contracts.adviseFromMarket"],
    "D121": ["JurisLean.FullMath.Numeric.bellman_onesided",
             "JurisLean.FullMath.Contracts.measureLegal",
             "JurisLean.FullMath.Contracts.legalOptions"],
    "D122": ["JurisLean.FullMath.Numeric.bellman_onesided",
             "JurisLean.FullMath.Contracts.coversFrozen",
             "JurisLean.FullMath.Contracts.depsKeptFor"],
    "D123": ["JurisLean.FullMath.Numeric.bellman_onesided",
             "JurisLean.FullMath.Contracts.readoutOf",
             "JurisLean.FullMath.Contracts.sourced"],
}


def _binding_row(dem, required):
    """Template for the controller's BINDINGS.json back-fill
    (DEMAND:D116–D123 rows).  Passes completion.validate_binding as-is."""
    return {
        "id": f"DEMAND:{dem}",
        "theorem": required["theorem"],
        "contract": required["contract"],
        "proof_mode": "KERNEL_CONTRACT_PROOF",
        "formal_scope": "Group-13 matter/trade workflow-strategy demand "
                        "instance in the shared semantic framework: this "
                        "item's own contract semantics over region-local "
                        "workflow operational defs (the exact VDR gap "
                        "with pending rows, legal closing orders with "
                        "infeasibility reporting, gated clarification "
                        "moves with explicit value models, preference-"
                        "measured risk ranking with hard blocks, "
                        "market-sample advice typed apart from legal "
                        "duty, subpoena option gates, outline coverage "
                        "of the frozen argument graph, and multi-hop "
                        "provenance chains with the timeout discipline) "
                        "plus the registered Bellman component (the "
                        "one-sided max-gap bound of the legal-action "
                        "Bellman operator), with its adverse case "
                        "executed as a negative test.",
        "independent_semantics": _SEMANTICS[dem],
        "algorithm": "tools/full_math/implementation/workflow_ref.py "
                     f"{_ENTRY[dem]} computes the intermediate result "
                     f"from structured input (the Bellman surface "
                     f"mirrored from "
                     f"JurisLean.FullMath.Numeric.Bellman and consumed "
                     f"by the D118 value model); "
                     f"workflow_check.check_{dem} re-derives the "
                     f"contract independently with different code paths "
                     f"(index scans, round counters, branch tables, "
                     f"selection maxima, gate ladders, row-matching "
                     f"scans, flag accumulation) — zero code sharing "
                     f"with the reference.",
        "observation_contract": "Inputs are the declared structures "
                                "(required-document and VDR-catalog "
                                "name lists, closing tasks as name/"
                                "prerequisite/permission triples, "
                                "clarification actions as kind/norm/"
                                "waivable/probability/gain/cost records "
                                "with exact Fraction values, risk items "
                                "as name/weight/measure/hard-block "
                                "records with integer preference "
                                "indices, market samples as clause/"
                                "count/total records, subpoena contexts "
                                "as standing/stage/timeliness flags, "
                                "outlines as covered/deps-kept/alts-"
                                "kept tables over the frozen graph, and "
                                "final assertions with their provenance "
                                "chains); outputs are exactly the "
                                "contract quantities (the exact gap "
                                "with its pending rows and the "
                                "fabrication witness, the executable "
                                "order or the infeasibility report with "
                                "the cycle witness, the legality gates "
                                "with the mandatory-waiver rejection and "
                                "the prediction-model values on the "
                                "Bellman mirror, the descending ranked "
                                "readout with the hard-block exclusion "
                                "and the weight-sensitivity witness, the "
                                "market-share advice typed apart from "
                                "legal duty, the option sets for the "
                                "full/party/late contexts, the coverage "
                                "verdict with the weak-outline witness, "
                                "and the sourcing verdicts with the "
                                "timeout readout discipline).",
        "external_assumptions": "The authoritative required-documents "
                                "list and the data room's actual "
                                "completeness, third-party cooperation "
                                "and document authenticity for closing "
                                "execution, the substantive calibration "
                                "of success probabilities and gains in "
                                "the explicit prediction model, the "
                                "declared preference weights and risk "
                                "measures, the market sample's "
                                "representativeness and selection bias, "
                                "the applicable foreign procedural rules "
                                "behind the option gates, the frozen "
                                "argument graph's candidate scope and "
                                "the adversarial target, and the "
                                "upstream legal tools' actual coverage "
                                "and availability remain external "
                                "validation obligations, not part of "
                                "this registration.",
        "proof_sources": [
            "proofs/lean/juris_lean/JurisLean/FullMath/Contracts.lean",
            "proofs/lean/juris_lean/JurisLean/FullMath/Acceptance.lean",
        ],
        "implementation_sources": [
            "tools/full_math/implementation/workflow_ref.py",
            "tools/full_math/implementation/workflow_check.py",
        ],
        "test_ids": [
            "tools/full_math/implementation_tests::"
            "test_workflow_group13.py::"
            f"test_demand_positive[{dem}]",
            "tools/full_math/implementation_tests::"
            "test_workflow_group13.py::"
            f"test_demand_counterexample[{dem}]",
            "tools/full_math/implementation_tests::"
            "test_workflow_group13.py::"
            "test_downstream_pipeline_consumes_workflow",
        ],
        "negative_test_ids": [
            "tools/full_math/implementation_tests::"
            "test_workflow_group13.py::"
            f"test_checker_rejects_tampered[{dem}]",
        ],
        "semantic_links": _SEMANTIC_LINKS[dem],
    }


@pytest.mark.parametrize("dem", DEMANDS)
def test_b13_binding_receipt(dem):
    """Synthetic receipt: the binding row for DEMAND:D1XX passes
    completion.validate_binding against the real repository files."""
    required = _REQUIREMENTS[f"DEMAND:{dem}"]
    C.validate_binding(_binding_row(dem, required), required, repo=REPO)


@pytest.mark.parametrize("dem", DEMANDS)
def test_b13_binding_receipt_negative(dem):
    """A tampered receipt (swapped theorem) is rejected."""
    required = _REQUIREMENTS[f"DEMAND:{dem}"]
    row = dict(_binding_row(dem, required))
    row["theorem"] = "JurisLean.FullMath.Acceptance.nonexistent_demand"
    with pytest.raises(C.EvidenceError):
        C.validate_binding(row, required, repo=REPO)
