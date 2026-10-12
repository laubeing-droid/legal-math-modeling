"""W2-A batch B07 acceptance tests: D057-D064, group 07 侵权责任与
损害.

Six pieces per demand (docs/full-math/W2B_CLASSIFICATION.md §5.4):

1. Lean contract  — Contracts.demand_D057..D064 restated as this item's own
   semantics over the shared quantity-ledger/interval carrier
   (Seams/UnifiedQuantLedger, the green B07 prerequisite); verified by the
   whole-repo replay build, and the registration-format tests live in
   test_registration_bindings.py.
2. Python entry   — tools/full_math/implementation/tort_ref.py per-item
   entries computing the intermediate result from real structured input
   (the interval/tort surface consumed from quantledger_ref, the Python
   mirror of JurisLean.Seams.UnifiedQuantLedger).
3. Independent checker — tort_check.py re-derives the contract inline
   with different code paths (index scans, four-product tables,
   early-return loops, branch tables, kept-key scans, endpoint tuples);
   no witness callbacks, no expectations from the main implementation,
   zero code sharing.
4. Downstream consumption — unified.pipeline run_case / step_event /
   run_trace consume the tort results through the adapters in tort_ref
   (build_case_input / build_environment / tort_trace_events).
5. Positive and adverse cases — the ALL_134 counterexample field of each
   demand is executed with per-item expectations.
6. Synthetic receipt — completion.validate_binding rows for
   DEMAND:D057-D064 (the ``_binding_row`` template below is ready for
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

from tools.full_math.implementation import tort_check as K  # noqa: E402
from tools.full_math.implementation import tort_ref as R  # noqa: E402
import completion as C  # noqa: E402

# Pipeline-facing names are imported INSIDE the downstream test, not at
# module level (same rationale as test_drafting_group12).

DEMANDS = ("D057", "D058", "D059", "D060", "D061", "D062", "D063", "D064")

F = Fraction

_CANDS = (("general", True), ("product", False), ("openResidual", False))

_LOSSES = (
    R.LossEntry(1, 2, 3, 4, F(1000)),       # medical (invoice)
    R.LossEntry(1, 2, 3, 4, F(800)),        # same key appraisal (dedup)
    R.LossEntry(2, 2, 5, 6, F(6000)),       # lost income
    R.LossEntry(3, 2, 7, 8, F(500)),        # property damage
)

_LOSS_TUPLES = tuple(
    (e.event, e.beneficiary, e.item, e.time, e.amount) for e in _LOSSES)

_REMEDIES = (F(7500), R.REMEDY_APOLOGY, R.REMEDY_CESSATION)

_RECORD = (1, (F(1, 4), F(3, 4)), (F(1875), F(5625)), F(0))


# ---------------------------------------------------------------------------
# 2/3/5 — entry + independent checker, positive and adverse (per item)
# ---------------------------------------------------------------------------


def _run_D057():
    """分类器不认识的新情形不能返回无任何请求权（ALL_134 反例字段）."""
    out = R.tort_classification(_CANDS)
    rep = K.check_D057(_CANDS, out)
    return rep.ok, rep.reasons, out


def _run_D058():
    """相关性显著不直接推出法律上的相当因果或责任（ALL_134 反例字段）."""
    out = R.causation_layering(F(1, 3), F(2, 3), F(100), F(120),
                               F(0), F(1), True)
    rep = K.check_D058(F(1, 3), F(2, 3), F(100), F(120), F(0), F(1),
                       True, out)
    return rep.ok, rep.reasons, out


def _run_D059():
    """用小比例掩盖根本不承担该责任的主体（ALL_134 反例字段）."""
    out = R.gate_share_readout((True, True), (F(1, 4), F(3, 4)))
    rep = K.check_D059((True, True), (F(1, 4), F(3, 4)), out)
    return rep.ok, rep.reasons, out


def _run_D060():
    """同一损害多个连带债务全额相加造成超额受偿（ALL_134 反例字段）."""
    out = R.liability_modes(F(7500), F(1875), F(7500), F(2000),
                            (F(7500),), (F(7500), F(0)),
                            (F(1875), F(5625)))
    rep = K.check_D060(F(7500), F(1875), F(7500), F(2000), (F(7500),),
                       (F(7500), F(0)), (F(1875), F(5625)), out)
    return rep.ok, rep.reasons, out


def _run_D061():
    """发票额和同一损失评估额不得无条件双计（ALL_134 反例字段）."""
    out = R.loss_ledger_readout(_LOSSES)
    rep = K.check_D061(_LOSS_TUPLES, out)
    return rep.ok, rep.reasons, out


def _run_D062():
    """把外部连带金额按内部份额削减，须发现语义不符（ALL_134 反例字段）."""
    out = R.payment_consistency(F(7500), (F(1, 4), F(3, 4)), (F(7500),),
                                (F(7500), F(0)), (F(1875), F(5625)))
    rep = K.check_D062(F(7500), (F(1, 4), F(3, 4)), (F(7500),),
                       (F(7500), F(0)), (F(1875), F(5625)), out)
    return rep.ok, rep.reasons, out


def _run_D063():
    """道歉或禁令不能当赔偿金额零而消失（ALL_134 反例字段）."""
    out = R.remedy_readout(_REMEDIES)
    rep = K.check_D063(_REMEDIES, out)
    return rep.ok, rep.reasons, out


def _run_D064():
    """不同情景各取最有利结果拼成无条件总结（ALL_134 反例字段）."""
    out = R.summary_witness(1, (F(1, 4), F(3, 4)), (F(1875), F(5625)),
                            _RECORD)
    rep = K.check_D064(1, (F(1, 4), F(3, 4)), (F(1875), F(5625)),
                       _RECORD, out)
    return rep.ok, rep.reasons, out


_POSITIVE = {"D057": _run_D057, "D058": _run_D058, "D059": _run_D059,
             "D060": _run_D060, "D061": _run_D061, "D062": _run_D062,
             "D063": _run_D063, "D064": _run_D064}


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
    if dem == "D057":
        cls = out
        # 要件选择＋开放残余：未满足不入选择、必入残余；新情形保留请求权载体
        assert cls["selected"] == [("general", True)]
        assert cls["residual"] == [("product", False), ("openResidual", False)]
        assert cls["unmet_never_selected"] is True
        assert cls["unmet_in_residual"] is True
        assert cls["every_candidate_bucketed"] is True
        assert cls["witness_residual"] == [("openResidual", False)]
        assert cls["unknown_kept_in_residual"] is True
        assert cls["no_claimless_output"] is True
    elif dem == "D058":
        caus = out
        # 类型化三标签；因果乘积 [100/3, 80]；门开度量下界正⇒归责
        assert caus["tags_distinct"] is True
        assert caus["cross_tag_rejected"] is True
        assert caus["product"] == (F(100, 3), F(80))
        assert caus["product_sound_interior"] is True
        assert caus["fault_wellformed"] is True
        assert caus["fault_scaled_wellformed"] is True
        assert caus["imputed"] is True
        assert caus["imputed_iff_gate_and_positive_lo"] is True
        # 度量再强 [9/10,1] 门关⇒不归责
        assert caus["strong_measure_gate_closed_not_imputed"] is True
        closed = R.causation_layering(F(9, 10), F(1), F(100), F(120),
                                      F(0), F(1), False)
        assert closed["imputed"] is False
    elif dem == "D059":
        gs = out
        # 门关⇒份额零；1/10 掩盖非法；1/4+3/4 合法
        assert gs["legal"] is True
        assert gs["closed_gate_zero_share"] is True
        assert gs["small_share_mask_illegal"] is True
        assert gs["open_shares_legal"] is True
        assert gs["all_open_sum_one"] is True
        masked = R.gate_share_readout((False, True), (F(1, 10), F(9, 10)))
        assert masked["legal"] is False
    elif dem == "D060":
        modes = out
        # 三方式外部义务；双全额超额拒；追偿池=缺额池；主清足⇒补零
        assert modes["several_due"] == F(1875)
        assert modes["joint_due"] == F(7500)
        assert modes["supp_due"] == F(0)  # 主责 7500 足额清偿损失 7500
        assert modes["several_equals_share"] is True
        assert modes["joint_equals_loss"] is True
        assert modes["supp_is_unpaid_remainder_capped"] is True
        assert modes["supp_zero_when_primary_covers"] is True
        assert modes["recovery_ok"] is True
        assert modes["double_full_violates"] is True
        assert modes["recourse"] == [F(5625), F(0)]
        assert modes["deficit"] == [F(0), F(5625)]
        assert modes["recourse_pool_equals_deficit_pool"] is True
    elif dem == "D061":
        losses = out
        # 首见去重：同键 1000+800 只计 1000；总额 7500 不虚增
        assert losses["keys_nodup_after"] is True
        assert losses["raw_total"] == F(8300)
        assert losses["deduped_total"] == F(7500)
        assert losses["dedup_no_inflate"] is True
        assert losses["witness_raw_total"] == F(1800)
        assert losses["witness_deduped_total"] == F(1000)
        assert losses["witness_first_kept"] is True
        assert losses["double_count_prevented"] is True
    elif dem == "D062":
        cons = out
        # 共享基数一致；连带外部不按份额削减；区间端点代数＋共同基数带
        assert cons["sums_to_one"] is True
        assert cons["share_total_equals_base"] is True
        assert cons["joint_due_full_loss"] is True
        assert cons["joint_not_share_reduced"] is True
        assert cons["recovery_ok"] is True
        assert cons["recovery_ok_iff_within_loss"] is True
        assert cons["single_full_recovery_ok"] is True
        assert cons["recourse_pool_equals_deficit_pool"] is True
        assert cons["interval_add_comm"] is True
        assert cons["interval_add_assoc"] is True
        assert cons["interval_scale_distrib"] is True
        assert cons["interval_scale_assoc"] is True
        assert cons["common_base_band"] == (F(150), F(200))
        assert cons["quarter_share_band"] == (F(25), F(50))
    elif dem == "D063":
        rem = out
        # 非金钱无金额视图；金钱投影盲区：道歉不消失
        assert rem["nonmonetary_amounts_none"] is True
        assert rem["money_amounts_preserved"] is True
        assert rem["monetary_total"] == F(7500)
        assert rem["witness_totals_equal"] is True
        assert rem["witness_lists_differ"] is True
        assert rem["apology_not_dropped"] is True
    else:  # D064
        summ = out
        # 同见证三投影；比例守恒继承；跨场景拼接拒
        assert summ["from_same_witness"] is True
        assert summ["fields_from_witness"] is True
        assert summ["witness_ratio_sum"] == F(1)
        assert summ["record_ratio_sum"] == F(1)
        assert summ["ratio_conservation_inherited"] is True
        assert summ["cross_scenario_mix_rejected"] is True
        mixed = R.summary_witness(1, (F(1),), (F(100),),
                                  (1, (F(1),), (F(999),), F(0)))
        assert mixed["from_same_witness"] is False


@pytest.mark.parametrize("dem", DEMANDS)
def test_checker_rejects_tampered(dem):
    """The independent checker must fail a tampered intermediate result
    (the checker, not the entry, is the judge of the contract)."""
    ok, _reasons, out = _POSITIVE[dem]()
    assert ok  # sanity: the honest result passes its own checker
    if dem == "D057":
        tampered = dict(out)
        tampered["unmet_never_selected"] = False  # unmet candidate selected
        rep = K.check_D057(_CANDS, tampered)
    elif dem == "D058":
        tampered = dict(out)
        tampered["product"] = (F(40), F(90))  # wrong product endpoints
        rep = K.check_D058(F(1, 3), F(2, 3), F(100), F(120), F(0), F(1),
                           True, tampered)
    elif dem == "D059":
        tampered = dict(out)
        tampered["small_share_mask_illegal"] = False  # masked config legal
        rep = K.check_D059((True, True), (F(1, 4), F(3, 4)), tampered)
    elif dem == "D060":
        tampered = dict(out)
        tampered["double_full_violates"] = False  # 200 recovery on 100 loss
        rep = K.check_D060(F(7500), F(1875), F(7500), F(2000), (F(7500),),
                           (F(7500), F(0)), (F(1875), F(5625)), tampered)
    elif dem == "D061":
        tampered = dict(out)
        tampered["deduped_total"] = F(8300)  # double count accepted
        rep = K.check_D061(_LOSS_TUPLES, tampered)
    elif dem == "D062":
        tampered = dict(out)
        tampered["joint_not_share_reduced"] = False  # joint reduced to share
        rep = K.check_D062(F(7500), (F(1, 4), F(3, 4)), (F(7500),),
                           (F(7500), F(0)), (F(1875), F(5625)), tampered)
    elif dem == "D063":
        tampered = dict(out)
        tampered["nonmonetary_amounts_none"] = False  # apology priced at 0
        rep = K.check_D063(_REMEDIES, tampered)
    else:  # D064
        tampered = dict(out)
        tampered["cross_scenario_mix_rejected"] = False  # stitched summary
        rep = K.check_D064(1, (F(1, 4), F(3, 4)), (F(1875), F(5625)),
                           _RECORD, tampered)
    assert not rep.ok, f"{dem} checker accepted a tampered result: {rep.reasons}"


# ---------------------------------------------------------------------------
# 4 — downstream consumption through the unified pipeline
# ---------------------------------------------------------------------------

def test_downstream_pipeline_consumes_tort():
    """run_case consumes the CaseInput assembled from the tort/damages
    results (the elements-met classification and the open liability gate
    supply the issue, the unclassifiable residual scenario stays
    awaiting — never silently dropped, and the only quantities are the
    deduped loss total and the first co-tortfeasor's internal share on
    the one shared base — never re-derived from a different ledger);
    run_trace consumes the joint external recovery of the full loss and
    the internal recourse pool (5625) as payment events."""
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

    intake = R.build_tort_intake()
    case = R.build_case_input(intake)
    env = R.build_environment(intake)

    # the assembled carriers are exactly the tort outputs
    assert case.issues == ("TORT_DAMAGES",)
    assert case.claims[0].claimant == "victim"
    assert case.claims[0].respondent == "client"
    # D057: the open-residual scenario rides on the case as a defense
    # gap; the unclassifiable scenario stays awaiting — never dropped
    assert case.defenses[0].defense_id == "def-residual-open"
    assert case.defenses[0].basis == "tort_type_residual_open"
    assert case.defenses[0].target_claims == ("c0",)
    standings = {(f.proposition.predicate, f.standing.name)
                 for f in case.fact_records}
    assert ("tort-elements-met", "ADMITTED_POSITIVE") in standings
    assert ("liability-gate-open", "ADMITTED_POSITIVE") in standings
    assert ("tort-type-residual-open", "AWAITING_ADMISSION") in standings
    # D061/D062: the only quantities are the deduped loss total (7500)
    # and the internal share on the shared base (1875) — one base,
    # never merged with a second ledger
    assert [q.value for q in case.quantities] == [Fraction(7500),
                                                  Fraction(1875)]
    assert {q.basis_kind for q in case.quantities} == \
        {"tort-loss-total", "internal-share-first"}

    run = run_case(case, env)
    assert run.status is RunStatus.COMPLETE
    assert run.failures == ()
    judgments = run.judgments_of("c0")
    assert judgments and Judgment.ESTABLISHED in judgments

    # trace: the joint external recovery lands on the JOINT_RECOVERY
    # basis (the full 7500 loss) and the internal recourse pool lands
    # on the INTERNAL_SHARE basis (5625); the residual bucket receives
    # nothing
    events = R.tort_trace_events(intake)
    assert [e.event.event_id for e in events] == \
        ["pay-joint-recovery", "pay-internal-recourse"]
    final, notes = run_trace(case.initial_state, events, env)
    event_ids = [e.event_id for e in final.events]
    assert "pay-joint-recovery" in event_ids
    assert "pay-internal-recourse" in event_ids
    assert gross_of(final, "JOINT_RECOVERY") == Fraction(7500)
    assert gross_of(final, "INTERNAL_SHARE") == Fraction(5625)
    allocated = [e for e in final.ledger
                 if e.kind.name == "GROSS_ALLOCATED"
                 and e.basis_key == "JOINT_RECOVERY"]
    assert sorted(e.amount for e in allocated) == [Fraction(7500)]
    assert notes  # the step relation actually produced observations

    # step_event alone: one step, exactly the event's own semantics
    one = step_event(case.initial_state, events[0], env)
    assert one.next_env is env

    # the tort/damages decisions stay on the bundle: the classification
    # with its residual bucket (D057), the causation layering (D058),
    # the gate/share separation (D059), the liability modes (D060), the
    # deduped loss ledger (D061), the payment consistency (D062), the
    # remedy readout (D063) and the scenario-witness summary (D064)
    assert intake["classify"]["no_claimless_output"] is True
    assert intake["causation"]["strong_measure_gate_closed_not_imputed"] is True
    assert intake["gates"]["small_share_mask_illegal"] is True
    assert intake["modes"]["double_full_violates"] is True
    assert intake["losses"]["double_count_prevented"] is True
    assert intake["consistency"]["joint_not_share_reduced"] is True
    assert intake["remedies"]["apology_not_dropped"] is True
    assert intake["summary"]["cross_scenario_mix_rejected"] is True


# ---------------------------------------------------------------------------
# 6 — synthetic receipts through completion.validate_binding
# ---------------------------------------------------------------------------

_REQUIREMENTS = {
    r["id"]: r
    for r in json.loads((SPEC / 'REQUIREMENTS.json').read_text(encoding='utf-8'))
}

_SEMANTICS = {
    "D057": "tort-type candidates are selected by their elements "
            "while an open residual bucket keeps everything the "
            "classifier does not recognize: an element-unmet "
            "candidate never enters the selection and always lands in "
            "the residual, every candidate lands in exactly one "
            "bucket, and an unknown new scenario keeps its claim "
            "carrier instead of returning a claim-less empty result.",
    "D058": "behaviour, damage, causation and fault are typed "
            "interval relations (three distinct tags, cross-tag "
            "operations rejected, the [0,1] fault well-formedness "
            "surviving [0,1] scaling) and statistical causation is "
            "layered apart from legal imputation: the cause×loss "
            "four-endpoint product stays sound while imputation "
            "needs an open legal gate AND a strictly positive causal "
            "lower bound — a [9/10, 1] measure with a closed gate "
            "never imputes.",
    "D059": "the establishment gate and the share choice are separate "
            "fields connected only by the legality predicate: a "
            "closed gate forces a zero share, the masked "
            "configuration (gate closed with a 1/10 share) is "
            "illegal, and the open-gate 1/4+3/4 configuration is "
            "legal with the shares summing to one.",
    "D060": "several/joint/supplementary external payment duties are "
            "built separately from the internal recourse relation: "
            "several equals the internal share, joint equals the "
            "full loss, supplementary equals the unpaid remainder "
            "capped by the supplementary due; the joint external "
            "total constraint rejects two full-100 recoveries on a "
            "100 loss; the recourse pool equals the deficit pool "
            "when total payments equal total internal shares; the "
            "supplementary party pays exactly zero when the primary "
            "party covers the loss.",
    "D061": "the loss ledger is deduplicated by the (event, "
            "beneficiary, item, time) key before the explicit "
            "aggregation: keys are duplicate-free after dedup, dedup "
            "never inflates a nonnegative ledger, an already-unique "
            "ledger is returned identically, and an invoice 1000 "
            "plus an 800 appraisal of the same loss key is pressed "
            "back from a double-counted 1800 to the first-seen 1000.",
    "D062": "per-party payments satisfy the external recovery "
            "constraint and the internal rules on one shared loss "
            "base: shares summing to one pay exactly the base, the "
            "joint external duty is the full loss (never the "
            "internal share reduced), the recovery constraint is "
            "exactly total recoveries not exceeding the loss, the "
            "recourse pool balances, and the interval endpoint "
            "algebra (assoc/comm/distrib/scale-assoc, [100,200]∩"
            "[150,300] = [150,200]) keeps the share×loss computation "
            "consistent.",
    "D063": "restitution, cessation and apology are action/state "
            "objectives that never coerce into RMB: non-monetary "
            "remedies carry no amount view (None, never a fake 0), "
            "money amounts are preserved exactly, and the money "
            "projection is a blind spot — two remedy lists with the "
            "same monetary total 100 remain different obligations.",
    "D064": "every responsibility, ratio, value and limit in the "
            "final summary comes from one scenario witness: a "
            "same-witness record takes the witness's three "
            "projections as its own fields and inherits its ratio "
            "conservation, while a record stitched from scenario 1's "
            "identity and scenario 2's values is the summary of no "
            "single witness.",
}

_ENTRY = {
    "D057": "tort_classification",
    "D058": "causation_layering",
    "D059": "gate_share_readout",
    "D060": "liability_modes",
    "D061": "loss_ledger_readout",
    "D062": "payment_consistency",
    "D063": "remedy_readout",
    "D064": "summary_witness",
}

_SEMANTIC_LINKS = {
    "D057": ["JurisLean.FullMath.Numeric.Iv.fixed_y_bounds",
             "JurisLean.Seams.UnifiedQuantLedger.unmatched_partition",
             "JurisLean.Seams.UnifiedQuantLedger.unknown_kept_in_residual"],
    "D058": ["JurisLean.FullMath.Numeric.Iv.fixed_y_bounds",
             "JurisLean.Seams.UnifiedQuantLedger.causeTimesLoss_sound",
             "JurisLean.Seams.UnifiedQuantLedger.FaultOK_scale",
             "JurisLean.Seams.UnifiedQuantLedger.correlation_not_imputation"],
    "D059": ["JurisLean.FullMath.Numeric.Iv.fixed_y_bounds",
             "JurisLean.Seams.UnifiedQuantLedger.no_resp_zero_share",
             "JurisLean.Seams.UnifiedQuantLedger.small_share_mask_rejected",
             "JurisLean.Seams.UnifiedQuantLedger.goodShares_legal"],
    "D060": ["JurisLean.FullMath.Numeric.Iv.fixed_y_bounds",
             "JurisLean.Seams.UnifiedQuantLedger.joint_double_full_violates",
             "JurisLean.Seams.UnifiedQuantLedger.recourse_pool_balanced",
             "JurisLean.Seams.UnifiedQuantLedger.supp_zero_when_primary_covers"],
    "D061": ["JurisLean.FullMath.Numeric.Iv.fixed_y_bounds",
             "JurisLean.Seams.UnifiedQuantLedger.dedupFirst_keys_nodup",
             "JurisLean.Seams.UnifiedQuantLedger.dedup_sum_le",
             "JurisLean.Seams.UnifiedQuantLedger.dedupFirst_id_of_nodup",
             "JurisLean.Seams.UnifiedQuantLedger.invoice_double_count_prevented"],
    "D062": ["JurisLean.FullMath.Numeric.Iv.fixed_y_bounds",
             "JurisLean.Seams.UnifiedQuantLedger.pays_sum_base",
             "JurisLean.Seams.UnifiedQuantLedger.joint_external_not_share_reduced",
             "JurisLean.Seams.UnifiedQuantLedger.recourse_pool_balanced",
             "JurisLean.Seams.UnifiedQuantLedger.QIv.scale_distrib",
             "JurisLean.Seams.UnifiedQuantLedger.QIv.scale_assoc"],
    "D063": ["JurisLean.FullMath.Numeric.Iv.fixed_y_bounds",
             "JurisLean.Seams.UnifiedQuantLedger.nonmonetary_no_amount",
             "JurisLean.Seams.UnifiedQuantLedger.monetary_total_blind_spot"],
    "D064": ["JurisLean.FullMath.Numeric.Iv.fixed_y_bounds",
             "JurisLean.Seams.UnifiedQuantLedger.same_witness_consistent",
             "JurisLean.Seams.UnifiedQuantLedger.cross_scenario_mix_rejected"],
}


def _binding_row(dem, required):
    """Template for the controller's BINDINGS.json back-fill
    (DEMAND:D057–D064 rows).  Passes completion.validate_binding as-is."""
    return {
        "id": f"DEMAND:{dem}",
        "theorem": required["theorem"],
        "contract": required["contract"],
        "proof_mode": "KERNEL_CONTRACT_PROOF",
        "formal_scope": "Group-07 tort/damages demand instance in the "
                        "shared semantic framework: this item's own "
                        "contract semantics over the quantity-ledger "
                        "interval carrier (tagged legal intervals with "
                        "endpoint algebra, element-based tort "
                        "classification with an open residual, "
                        "gate/share separation, several/joint/"
                        "supplementary external duties with the "
                        "recourse pool, first-seen loss dedup, "
                        "non-monetary remedies, scenario witnesses) "
                        "plus the registered interval component (for "
                        "a fixed second factor every product with a "
                        "member of the interval lies between the two "
                        "endpoint products), with its adverse case "
                        "executed as a negative test.",
        "independent_semantics": _SEMANTICS[dem],
        "algorithm": "tools/full_math/implementation/tort_ref.py "
                     f"{_ENTRY[dem]} computes the intermediate result "
                     f"from structured input (the interval/tort "
                     f"surface consumed from quantledger_ref, the "
                     f"mirror of "
                     f"JurisLean.Seams.UnifiedQuantLedger); "
                     f"tort_check.check_{dem} re-derives the contract "
                     f"independently with different code paths "
                     f"(index scans, four-product tables, "
                     f"early-return loops, branch tables, kept-key "
                     f"scans, endpoint tuples) — zero code sharing "
                     f"with the reference.",
        "observation_contract": "Inputs are the declared structures "
                                "(tort-type candidates as kind/elements-"
                                "met pairs, causal/loss/fault interval "
                                "endpoints with a legal-gate flag, "
                                "gate/share configurations, liability-"
                                "mode parameters with recovery, payment "
                                "and internal-share sequences, loss "
                                "entries keyed by event/beneficiary/"
                                "item/time with exact Fraction amounts, "
                                "shared-base share and recovery "
                                "sequences, remedy lists mixing money "
                                "amounts and non-monetary tags, and "
                                "scenario witnesses with their summary "
                                "records); outputs are exactly the "
                                "contract quantities (the selected and "
                                "residual buckets with the unknown-"
                                "scenario carrier, the tagged interval "
                                "readouts with the cause×loss product "
                                "and the imputation verdict, the gate/"
                                "share legality with the masked "
                                "rejection, the three external duties "
                                "with the recovery constraint and the "
                                "balanced recourse pool, the deduped "
                                "loss totals with the invoice/appraisal "
                                "witness, the shared-base payment "
                                "consistency with the endpoint algebra, "
                                "the amount views with the blind-spot "
                                "witness, and the same-witness summary "
                                "with the cross-scenario rejection).",
        "external_assumptions": "Element findings for the tort-type "
                                "classification and the residual "
                                "scenario's later analysis, causal-"
                                "measure estimation and the legal "
                                "imputation gate's substantive "
                                "justification, discretionary share "
                                "quantification, the applicable "
                                "liability-mode law and its ordering "
                                "policy, compensability and valuation "
                                "of loss items including future "
                                "damages, the joint/supplementary "
                                "policy boundaries with actual payment "
                                "records, feasibility and "
                                "proportionality of non-monetary "
                                "relief, and free-text semantic review "
                                "of the final summary remain external "
                                "validation obligations, not part of "
                                "this registration.",
        "proof_sources": [
            "proofs/lean/juris_lean/JurisLean/FullMath/Contracts.lean",
            "proofs/lean/juris_lean/JurisLean/FullMath/Acceptance.lean",
        ],
        "implementation_sources": [
            "tools/full_math/implementation/tort_ref.py",
            "tools/full_math/implementation/tort_check.py",
        ],
        "test_ids": [
            "tools/full_math/implementation_tests::"
            "test_tort_group07.py::"
            f"test_demand_positive[{dem}]",
            "tools/full_math/implementation_tests::"
            "test_tort_group07.py::"
            f"test_demand_counterexample[{dem}]",
            "tools/full_math/implementation_tests::"
            "test_tort_group07.py::"
            "test_downstream_pipeline_consumes_tort",
        ],
        "negative_test_ids": [
            "tools/full_math/implementation_tests::"
            "test_tort_group07.py::"
            f"test_checker_rejects_tampered[{dem}]",
        ],
        "semantic_links": _SEMANTIC_LINKS[dem],
    }


@pytest.mark.parametrize("dem", DEMANDS)
def test_b07_binding_receipt(dem):
    """Synthetic receipt: the binding row for DEMAND:D0XX passes
    completion.validate_binding against the real repository files."""
    required = _REQUIREMENTS[f"DEMAND:{dem}"]
    C.validate_binding(_binding_row(dem, required), required, repo=REPO)


@pytest.mark.parametrize("dem", DEMANDS)
def test_b07_binding_receipt_negative(dem):
    """A tampered receipt (swapped theorem) is rejected."""
    required = _REQUIREMENTS[f"DEMAND:{dem}"]
    row = dict(_binding_row(dem, required))
    row["theorem"] = "JurisLean.FullMath.Acceptance.nonexistent_demand"
    with pytest.raises(C.EvidenceError):
        C.validate_binding(row, required, repo=REPO)
