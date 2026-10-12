"""Group-07 tort/damages reference entries (D057-D064, W2-A batch B07).

Every entry consumes real structured input (no fixtures, no precomputed
answers) and produces the intermediate result whose formal contract is
``JurisLean.FullMath.Contracts.demand_D057`` … ``demand_D064``:

* D057 ``tort_classification`` — tort-type candidates are selected by
  their elements while an open residual bucket keeps everything the
  classifier does not recognize: an element-unmet candidate goes to the
  residual and never into the selection, every candidate lands in
  exactly one of the two buckets, and an unknown new scenario is kept
  in the residual instead of returning a claim-less empty result
  (ALL_134 counterexample: 分类器不认识的新情形不能返回无任何请求权).
* D058 ``causation_layering`` — behaviour, damage, causation and fault
  are typed relations and statistical causation is layered apart from
  legal imputation: the three interval tags (loss/cause/fault) are
  distinct with cross-tag operations rejected, the cause×loss
  four-endpoint product stays sound, the fault share's [0,1]
  well-formedness survives [0,1] scaling, and imputation needs an open
  legal gate AND a strictly positive causal lower bound — a [9/10, 1]
  measure with a closed gate never imputes (ALL_134 counterexample:
  相关性显著不直接推出法律上的相当因果或责任).
* D059 ``gate_share_readout`` — the establishment gate and the share
  choice are separate fields connected only by the legality predicate:
  a closed gate forces a zero share, the masked configuration (gate
  closed with a 1/10 share) is illegal, and the open-gate 1/4+3/4
  configuration is legal (ALL_134 counterexample: 用小比例掩盖根本不
  承担该责任的主体).
* D060 ``liability_modes`` — several/joint/supplementary external
  payment duties are built separately from the internal recourse
  relation: several = internal share, joint = full loss,
  supplementary = the unpaid remainder capped by the supplementary
  due; the joint external total constraint rejects two full-100
  recoveries on a 100 loss; the recourse pool equals the deficit pool
  when total payments equal total internal shares; the supplementary
  party pays exactly zero when the primary party covers the loss
  (ALL_134 counterexample: 同一损害多个连带债务全额相加造成超额受偿).
* D061 ``loss_ledger_readout`` — the loss ledger is deduplicated by
  the (event, beneficiary, item, time) key before the explicit
  aggregation: keys are duplicate-free after dedup, dedup never
  inflates a nonnegative ledger, an already-unique ledger is returned
  identically, and an invoice 1000 plus an 800 appraisal of the same
  loss key double-counts to 1800 only before dedup presses it back to
  1000 (ALL_134 counterexample: 发票额和同一损失评估额不得无条件双计).
* D062 ``payment_consistency`` — per-party payments satisfy the
  external recovery constraint and the internal rules on one shared
  loss base: shares summing to one pay exactly the base, the joint
  external duty is the full loss (never the internal share reduced),
  the recovery constraint is exactly "total recoveries ≤ loss", the
  recourse pool balances, and the interval endpoint algebra
  (assoc/comm/distrib/scale-assoc plus the [100,200]∩[150,300] =
  [150,200] common-base band) keeps the share×loss computation
  consistent (ALL_134 counterexample: 把外部连带金额按内部份额削减，
  须发现语义不符).
* D063 ``remedy_readout`` — restitution, cessation and apology are
  action/state objectives that never coerce into RMB: non-monetary
  remedies carry no amount view (None, never a fake 0), money amounts
  are preserved exactly, and the money projection is a blind spot —
  two remedy lists with the same monetary total 100 remain different
  obligations (ALL_134 counterexample: 道歉或禁令不能当赔偿金额零而
  消失).
* D064 ``summary_witness`` — every responsibility, ratio, value and
  limit in the final summary comes from one scenario witness: a
  same-witness record takes the witness's three projections as its
  fields and inherits its ratio conservation, while a record stitched
  from scenario 1's identity and scenario 2's values is the summary of
  no single witness (ALL_134 counterexample: 不同情景各取最有利结果拼
  成无条件总结).

Amounts are ``Fraction`` (ℚ).  The quantity/interval surface is
consumed from ``quantledger_ref`` (the Python mirror of
``JurisLean.Seams.UnifiedQuantLedger``, the green B07 prerequisite
carrier), never redefined here.  The downstream adapters at the bottom
feed these intermediate results into the unified pipeline public
entries (``run_case`` / ``step_event`` / ``run_trace``); they never
accept a precomputed verdict.  The independent contract checker lives
in ``tort_check`` and shares no code with this module.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Dict, List, Optional, Sequence, Tuple

from tools.full_math.implementation.quantledger_ref import (
    IV_TAGS,
    IvQ,
    LossEntry,
    MODE_JOINT,
    MODE_SEVERAL,
    MODE_SUPP,
    REMEDY_APOLOGY,
    REMEDY_CESSATION,
    REMEDY_RESTITUTION,
    TAG_CAUSE,
    TAG_FAULT,
    TAG_LOSS,
    TagIv,
    amount_of,
    cause_times_loss,
    dedup_first,
    deficit_of,
    external_due,
    imputed,
    joint_recovery_ok,
    legal_shares,
    loss_total,
    monetary_total,
    pays_sum_base,
    recourse_of,
    supp_distribution,
    tort_partition,
    v_add,
    v_inter,
    v_scale,
)

F = Fraction

# ---------------------------------------------------------------------------
# D057 — element-based tort classification with an open residual bucket
# ---------------------------------------------------------------------------


def tort_classification(cands: Sequence[Tuple[str, bool]]) -> dict:
    """Tort-type candidates selected by elements with an open residual
    bucket (Lean ``Contracts.demand_D057``): unmet candidates never enter
    the selection, every candidate lands in exactly one bucket, and an
    unknown new scenario keeps its claim carrier in the residual."""

    cands = [(str(k), bool(m)) for k, m in cands]
    selected, residual = tort_partition(cands)
    sel_set = set(selected)
    res_set = set(residual)
    # the ALL_134 witness: an unrecognized scenario alongside a general-tort
    # candidate — both buckets stay non-empty (no claim-less empty result)
    witness = [("openResidual", False), ("general", True)]
    w_sel, w_res = tort_partition(witness)
    return {
        "candidates": cands,
        "selected": selected,
        "residual": residual,
        "unmet_never_selected": all(c not in sel_set for c in cands if not c[1]),
        "unmet_in_residual": all(c in res_set for c in cands if not c[1]),
        "every_candidate_bucketed":
            all((c in sel_set) != (c in res_set) for c in cands),
        "buckets_partition": len(selected) + len(residual) == len(cands),
        "witness_selected": w_sel,
        "witness_residual": w_res,
        "unknown_kept_in_residual": w_res == [("openResidual", False)],
        "unknown_still_claimable": len(w_res) == 1,
        "no_claimless_output": len(selected) + len(residual) == len(cands),
    }


# ---------------------------------------------------------------------------
# D058 — typed interval relations; statistical vs legal layering
# ---------------------------------------------------------------------------


def causation_layering(cause_lo: Fraction, cause_hi: Fraction,
                       loss_lo: Fraction, loss_hi: Fraction,
                       fault_lo: Fraction = F(0), fault_hi: Fraction = F(1),
                       legal_gate: bool = True) -> dict:
    """Behaviour/damage/causation/fault as typed interval relations with
    statistical causation layered apart from legal imputation (Lean
    ``Contracts.demand_D058``)."""

    ci = TagIv(TAG_CAUSE, IvQ(Fraction(cause_lo), Fraction(cause_hi)))
    li = TagIv(TAG_LOSS, IvQ(Fraction(loss_lo), Fraction(loss_hi)))
    fi = TagIv(TAG_FAULT, IvQ(Fraction(fault_lo), Fraction(fault_hi)))
    product = cause_times_loss(ci, li)
    # cross-tag operations are rejected at the value level (the Lean
    # type-level discipline mirrored by an explicit probe)
    try:
        TagIv(TAG_CAUSE, ci.iv).plus(TagIv(TAG_LOSS, li.iv))
        cross_tag_rejected = False
    except TypeError:
        cross_tag_rejected = True
    # soundness probe: an interior (x, y) pair lands inside the product
    x = (ci.iv.lo + ci.iv.hi) / 2
    y = (li.iv.lo + li.iv.hi) / 2
    product_contains_interior = product.iv.mem(x * y)
    scaled_fault = fi.scaled(F(1, 2))
    # the ALL_134 witness: a [9/10, 1] causal measure with a closed gate
    strong = TagIv(TAG_CAUSE, IvQ(F(9, 10), F(1)))
    return {
        "cause": (ci.iv.lo, ci.iv.hi),
        "loss": (li.iv.lo, li.iv.hi),
        "fault": (fi.iv.lo, fi.iv.hi),
        "tags_distinct": len(set(IV_TAGS)) == 3,
        "tag_kinds": ("loss", "cause", "fault"),
        "cross_tag_rejected": cross_tag_rejected,
        "product": (product.iv.lo, product.iv.hi),
        "product_sound_interior": product_contains_interior,
        "fault_wellformed": fi.fault_ok(),
        "fault_scaled_wellformed": scaled_fault.fault_ok(),
        "legal_gate": legal_gate,
        "imputed": imputed(legal_gate, ci.iv.lo),
        "imputed_iff_gate_and_positive_lo":
            imputed(legal_gate, ci.iv.lo)
            == (legal_gate and ci.iv.lo > 0),
        "strong_measure_gate_closed_not_imputed":
            not imputed(False, strong.iv.lo),
    }


# ---------------------------------------------------------------------------
# D059 — establishment gate separate from the share choice
# ---------------------------------------------------------------------------


def gate_share_readout(gates: Sequence[bool],
                       shares: Sequence[Fraction]) -> dict:
    """The establishment gate and the share choice as separate fields
    connected only by the legality predicate (Lean
    ``Contracts.demand_D059``): a closed gate forces a zero share."""

    gates = [bool(g) for g in gates]
    shares = [Fraction(s) for s in shares]
    legal = legal_shares(gates, shares)
    # the ALL_134 witness: gate closed with a 1/10 share (masking no
    # liability with a small ratio) is illegal; open 1/4+3/4 is legal
    bad = legal_shares([False, True], [F(1, 10), F(9, 10)])
    good = legal_shares([True, True], [F(1, 4), F(3, 4)])
    return {
        "gates": gates,
        "shares": shares,
        "legal": legal,
        "closed_gate_zero_share":
            all(s == 0 for g, s in zip(gates, shares) if not g),
        "closed_gate_positive_share_rejected":
            not (any(s > 0 for g, s in zip(gates, shares) if not g)
                 and legal),
        "small_share_mask_illegal": bad is False,
        "open_shares_legal": good is True,
        "all_open_sum_one":
            (not all(gates)) or sum(shares, F(0)) == 1,
    }


# ---------------------------------------------------------------------------
# D060 — several/joint/supplementary external duties + internal recourse
# ---------------------------------------------------------------------------


def liability_modes(loss: Fraction, internal_share: Fraction,
                    primary_due: Fraction, secondary_due: Fraction,
                    recoveries: Sequence[Fraction] = (),
                    paid: Sequence[Fraction] = (),
                    internal_shares: Sequence[Fraction] = ()) -> dict:
    """Several/joint/supplementary external payment duties with the
    internal recourse relation (Lean ``Contracts.demand_D060``)."""

    loss = Fraction(loss)
    internal_share = Fraction(internal_share)
    primary_due = Fraction(primary_due)
    secondary_due = Fraction(secondary_due)
    recoveries = [Fraction(r) for r in recoveries]
    several = external_due(MODE_SEVERAL, loss, internal_share,
                           primary_due, secondary_due)
    joint = external_due(MODE_JOINT, loss, internal_share,
                         primary_due, secondary_due)
    supp = external_due(MODE_SUPP, loss, internal_share,
                        primary_due, secondary_due)
    supp_rows = supp_distribution(primary_due, secondary_due, loss)
    # the internal recourse pool: paid vs internal shares
    paid = [Fraction(p) for p in paid]
    internal_shares = [Fraction(s) for s in internal_shares]
    pool_balanced = (sum(paid, F(0)) == sum(internal_shares, F(0))
                     and paid)
    recourse = [recourse_of(p, s) for p, s in zip(paid, internal_shares)]
    deficit = [deficit_of(p, s) for p, s in zip(paid, internal_shares)]
    # the ALL_134 witness: two full-100 recoveries on a 100 loss
    double_full = [F(100), F(100)]
    return {
        "loss": loss,
        "internal_share": internal_share,
        "several_due": several,
        "joint_due": joint,
        "supp_due": supp,
        "several_equals_share": several == internal_share,
        "joint_equals_loss": joint == loss,
        "supp_is_unpaid_remainder_capped":
            supp == min(max(loss - primary_due, F(0)), secondary_due),
        "supp_rows": supp_rows,
        "supp_zero_when_primary_covers":
            supp_distribution(primary_due, secondary_due,
                              primary_due)[1] == 0,
        "recoveries": recoveries,
        "recovery_total": sum(recoveries, F(0)),
        "recovery_ok": joint_recovery_ok(loss, recoveries),
        "double_full_violates": not joint_recovery_ok(F(100), double_full),
        "paid": paid,
        "internal_shares": internal_shares,
        "recourse": recourse,
        "deficit": deficit,
        "recourse_pool_equals_deficit_pool":
            pool_balanced and sum(recourse, F(0)) == sum(deficit, F(0)),
    }


# ---------------------------------------------------------------------------
# D061 — loss ledger: first-seen dedup + explicit aggregation
# ---------------------------------------------------------------------------


def loss_ledger_readout(entries: Sequence[LossEntry]) -> dict:
    """The loss ledger deduplicated by the (event, beneficiary, item,
    time) key before the explicit aggregation (Lean
    ``Contracts.demand_D061``)."""

    entries = list(entries)
    deduped = dedup_first(entries)
    keys = [e.key for e in deduped]
    raw_keys = [e.key for e in entries]
    # the ALL_134 witness: invoice 1000 and appraisal 800 on one key
    invoice = LossEntry(1, 2, 3, 4, F(1000))
    appraisal = LossEntry(1, 2, 3, 4, F(800))
    pair = [invoice, appraisal]
    pair_dedup = dedup_first(pair)
    return {
        "entries": entries,
        "deduped": deduped,
        "keys_nodup_after": len(set(keys)) == len(keys),
        "raw_total": loss_total(entries),
        "deduped_total": loss_total(deduped),
        "dedup_no_inflate": loss_total(deduped) <= loss_total(entries),
        "identity_when_nodup":
            (len(set(raw_keys)) == len(raw_keys)) and dedup_first(entries) == entries,
        "witness_raw_total": loss_total(pair),
        "witness_deduped_total": loss_total(pair_dedup),
        "witness_first_kept": pair_dedup == [invoice],
        "double_count_prevented":
            loss_total(pair_dedup) == F(1000) and loss_total(pair) == F(1800),
    }


# ---------------------------------------------------------------------------
# D062 — per-party payments on one shared loss base
# ---------------------------------------------------------------------------


def payment_consistency(base: Fraction, shares: Sequence[Fraction],
                        recoveries: Sequence[Fraction],
                        paid: Sequence[Fraction] = (),
                        internal_shares: Sequence[Fraction] = ()) -> dict:
    """Per-party payments against the external recovery constraint and
    the internal rules on one shared loss base (Lean
    ``Contracts.demand_D062``)."""

    base = Fraction(base)
    shares = [Fraction(s) for s in shares]
    recoveries = [Fraction(r) for r in recoveries]
    paid = [Fraction(p) for p in paid]
    internal_shares = [Fraction(s) for s in internal_shares]
    share_sum = sum(shares, F(0))
    # the joint external duty is the full loss — never the internal share
    share_total = pays_sum_base(base, shares)
    recourse = [recourse_of(p, s) for p, s in zip(paid, internal_shares)]
    deficit = [deficit_of(p, s) for p, s in zip(paid, internal_shares)]
    # interval endpoint algebra on the shared-base band
    a = IvQ(F(100), F(200))
    b = IvQ(F(150), F(300))
    band = v_inter(a, b)
    scaled = v_scale(F(1, 4), a)
    return {
        "base": base,
        "shares": shares,
        "share_sum": share_sum,
        "sums_to_one": share_sum == 1,
        "share_total_equals_base": share_sum == 1 and share_total == base,
        "joint_due_full_loss": external_due(MODE_JOINT, base, F(1, 4),
                                            F(0), F(0)) == base,
        "joint_not_share_reduced":
            external_due(MODE_JOINT, base, F(1, 4), F(0), F(0)) != F(1, 4),
        "recoveries": recoveries,
        "recovery_ok": joint_recovery_ok(base, recoveries),
        "recovery_ok_iff_within_loss":
            joint_recovery_ok(base, recoveries)
            == (sum(recoveries, F(0)) <= base),
        "single_full_recovery_ok": joint_recovery_ok(F(100), [F(100)]),
        "recourse_pool_equals_deficit_pool":
            sum(paid, F(0)) == sum(internal_shares, F(0))
            and sum(recourse, F(0)) == sum(deficit, F(0)),
        "interval_add_comm":
            v_add(a, b) == v_add(b, a),
        "interval_add_assoc":
            v_add(v_add(a, b), band if band is not None else a)
            == v_add(a, v_add(b, band if band is not None else a)),
        "interval_scale_distrib":
            v_scale(F(1, 4), v_add(a, b))
            == v_add(v_scale(F(1, 4), a), v_scale(F(1, 4), b)),
        "interval_scale_assoc":
            v_scale(F(1, 2), v_scale(F(1, 4), a)) == v_scale(F(1, 8), a),
        "common_base_band": (band.lo, band.hi) if band is not None else None,
        "common_base_band_is_150_200":
            band is not None and (band.lo, band.hi) == (F(150), F(200)),
        "quarter_share_band": (scaled.lo, scaled.hi),
    }


# ---------------------------------------------------------------------------
# D063 — non-monetary remedies are action/state objectives
# ---------------------------------------------------------------------------


def remedy_readout(remedies: Sequence) -> dict:
    """Restitution/cessation/apology as action-state objectives that
    never coerce into RMB (Lean ``Contracts.demand_D063``): the money
    projection is a blind spot."""

    remedies = list(remedies)
    nonmonetary = (REMEDY_RESTITUTION, REMEDY_CESSATION, REMEDY_APOLOGY)
    # the ALL_134 witness: same monetary total, different obligations
    with_apology = [F(100), REMEDY_APOLOGY]
    money_only = [F(100)]
    return {
        "remedies": remedies,
        "amounts": [amount_of(r) for r in remedies],
        "nonmonetary_amounts_none":
            all(amount_of(r) is None for r in nonmonetary),
        "money_amounts_preserved":
            all(amount_of(q) == q for q in [F(0), F(100), F(1, 3)]),
        "monetary_total": monetary_total(remedies),
        "witness_total_with_apology": monetary_total(with_apology),
        "witness_total_money_only": monetary_total(money_only),
        "witness_totals_equal":
            monetary_total(with_apology) == monetary_total(money_only),
        "witness_lists_differ": with_apology != money_only,
        "apology_not_dropped":
            monetary_total(with_apology) == F(100)
            and with_apology != money_only,
    }


# ---------------------------------------------------------------------------
# D064 — the summary comes from one scenario witness
# ---------------------------------------------------------------------------


def summary_witness(scen_id: int, ratios: Sequence[Fraction],
                    values: Sequence[Fraction],
                    record: Optional[Tuple[int, Tuple[Fraction, ...],
                                           Tuple[Fraction, ...],
                                           Fraction]] = None) -> dict:
    """Every responsibility, ratio, value and limit of the summary from
    one scenario witness (Lean ``Contracts.demand_D064``)."""

    from tools.full_math.implementation.quantledger_ref import (
        ScenarioWitness,
        SummaryRecord,
    )

    ratios = tuple(Fraction(r) for r in ratios)
    values = tuple(Fraction(v) for v in values)
    w = ScenarioWitness(int(scen_id), ratios, values)
    if record is None:
        r = SummaryRecord(w.scen_id, w.ratios, w.values, F(0))
    else:
        rid, rratios, rvalues, rlimit = record
        r = SummaryRecord(int(rid), tuple(Fraction(x) for x in rratios),
                          tuple(Fraction(x) for x in rvalues),
                          Fraction(rlimit))
    same = r.from_same_witness(w)
    # the ALL_134 witness: scenario 1's identity + scenario 2's values
    wa = ScenarioWitness(1, (F(1),), (F(100),))
    wb = ScenarioWitness(2, (F(1),), (F(999),))
    mixed = SummaryRecord(1, (F(1),), (F(999),), F(0))
    return {
        "witness": w,
        "record": r,
        "from_same_witness": same,
        "fields_from_witness":
            (r.scen_id == w.scen_id and r.ratios == w.ratios
             and r.values == w.values),
        "witness_ratio_sum": sum(w.ratios, F(0)),
        "record_ratio_sum": sum(r.ratios, F(0)),
        "ratio_conservation_inherited":
            (not same) or (sum(w.ratios, F(0)) == 1
                           and sum(r.ratios, F(0)) == 1),
        "cross_scenario_mix_rejected":
            (not mixed.from_same_witness(wa))
            and (not mixed.from_same_witness(wb)),
    }


# ---------------------------------------------------------------------------
# Downstream adapters: tort/damages results → pipeline carriers (PY-RUN)
# ---------------------------------------------------------------------------

TORT_ENV_ID = "env-tort-b07"


def build_tort_intake() -> dict:
    """Synthetic tort/damages bundle for one liability matter: every
    field is produced by the entries above from declared structured
    inputs; the classification with its residual bucket, the causation
    layering, the gate/share readout, the liability modes, the deduped
    loss ledger, the payment consistency, the remedy readout and the
    scenario-witness summary all stay distinguishable."""

    losses = [
        LossEntry(1, 2, 3, 4, F(1000)),       # medical (invoice)
        LossEntry(1, 2, 3, 4, F(800)),        # same key appraisal (dedup)
        LossEntry(2, 2, 5, 6, F(6000)),       # lost income
        LossEntry(3, 2, 7, 8, F(500)),        # property damage
    ]
    return {
        "case_id": "case-b07",
        "classify": tort_classification([("general", True),
                                         ("product", False),
                                         ("openResidual", False)]),
        "causation": causation_layering(F(1, 3), F(2, 3), F(100), F(120),
                                        F(0), F(1), True),
        "gates": gate_share_readout([True, True], [F(1, 4), F(3, 4)]),
        "modes": liability_modes(F(7500), F(1875), F(7500), F(2000),
                                 recoveries=[F(7500)],
                                 paid=[F(7500), F(0)],
                                 internal_shares=[F(1875), F(5625)]),
        "losses": loss_ledger_readout(losses),
        "consistency": payment_consistency(F(7500), [F(1, 4), F(3, 4)],
                                           [F(7500)], [F(7500), F(0)],
                                           [F(1875), F(5625)]),
        "remedies": remedy_readout([F(7500), REMEDY_APOLOGY,
                                    REMEDY_CESSATION]),
        "summary": summary_witness(1, [F(1, 4), F(3, 4)], [F(1875), F(5625)]),
        "admitted_facts": ("tort-elements-met", "liability-gate-open"),
    }


def build_case_input(intake: dict):
    """Assemble the normalized CaseInput from the tort/damages results;
    the pipeline consumes exactly these intermediate objects: the
    elements-met classification and the open liability gate supply the
    admitted facts, the unclassifiable residual scenario stays awaiting
    (never silently dropped), and the only quantities are the deduped
    loss total and the internal share of the first co-tortfeasor —
    computed on the one shared base, never re-derived from a different
    ledger."""

    from theory.spec.canonical_v2.case import (
        CaseInput,
        Claim,
        Defense,
        ExactQuantity,
        FactRecord,
        FactStanding,
        Polar,
        ProcessState,
        ScopedAtom,
    )
    from theory.spec.canonical_v2.kernel import NormState

    case_id = intake["case_id"]
    issue = "TORT_DAMAGES"
    state = ProcessState(
        r=NormState(relations=()),
        environment_id=TORT_ENV_ID,
        stages=((f"{case_id}-trial", "trial"),),
        events=(),
        target_day=10,
        as_of_day=10,
    )
    parties = ("client", "counterparty", "victim", "cotortfeasor")
    # the victim's damages claim rides on the elements-met classification
    # with its deduped loss ledger (D057/D061); the counterparty's
    # defense points at the open residual bucket (D057) — an
    # unclassifiable scenario awaits its own analysis, it is not forced
    # into an existing category
    claims = (
        Claim("c0", "victim", "client", issue, "tort-elements-met",
              "tort-damages", subject="", issue=issue),
    )
    defenses = (
        Defense("def-residual-open", "counterparty", ("c0",),
                "tort_type_residual_open"),
    )
    standings = {
        "admitted": FactStanding.ADMITTED_POSITIVE,
        "awaiting": FactStanding.AWAITING_ADMISSION,
    }
    # admitted: the elements-met classification (D057) and the open
    # liability gate with its positive causal lower bound (D058/D059);
    # awaiting: the unclassifiable residual scenario (D057 adverse side)
    facts = tuple(
        FactRecord(
            fact_id,
            ScopedAtom(case_id=case_id, subject=f"span:{i}", issue=issue,
                       stage="trial", predicate=predicate,
                       polar=Polar.POS),
            standing,
            produced_at=i,
            known_at=i,
        )
        for i, (fact_id, predicate, standing) in enumerate((
            ("f-elements", "tort-elements-met",
             standings["admitted"]),        # D057 element-based selection
            ("f-gate", "liability-gate-open",
             standings["admitted"]),        # D058/D059 gate + measure
            ("f-residual", "tort-type-residual-open",
             standings["awaiting"]),        # D057 adverse, never dropped
        ))
    )
    quantities = (
        ExactQuantity(intake["losses"]["deduped_total"], "CNY-fen",
                      "tort-loss-total", "loss-ledger"),
        ExactQuantity(intake["consistency"]["shares"][0]
                      * intake["consistency"]["base"], "CNY-fen",
                      "internal-share-first", "shared-base"),
    )
    return CaseInput(
        case_id=case_id,
        initial_state=state,
        parties=parties,
        issues=(issue,),
        claims=claims,
        defenses=defenses,
        fact_records=facts,
        evidence_records=(),
        questions=(),
        quantities=quantities,
    )


def build_environment(intake: dict):
    """Declared environment: named sufficiency template licensed by the
    elements-met and gate-open predicates; no verdicts, no prebuilt
    framework."""

    from theory.spec.canonical_v2.case import (
        LegalEnvironment,
        StrongTemplate,
    )
    from theory.spec.canonical_v2.kernel import Jurisdiction, JurisdictionRoute

    issue = "TORT_DAMAGES"
    template = StrongTemplate(
        template_id="tpl-tort-b07",
        kind="TORT_ELEMENTS",
        scope_issue=issue,
        premise_predicates=("tort-elements-met", "liability-gate-open"),
        conclusion_predicate=issue,
        failure_predicates=("tort-type-residual-open",),
        license_rule_id="",
        source_id=f"tort:{issue}",
    )
    return LegalEnvironment(
        environment_id=TORT_ENV_ID,
        jurisdiction=Jurisdiction(route=JurisdictionRoute.MAINLAND),
        rules=(),
        strong_templates=(template,),
    )


def tort_trace_events(intake: dict):
    """The liability witness becomes payment events on the shared loss
    base: the joint external recovery of the full loss lands on the
    JOINT_RECOVERY basis, and the internal recourse (the over-paid
    joint recoverer's claim, exactly the recourse pool) lands on the
    INTERNAL_SHARE basis; the residual bucket receives no payment at
    all."""

    from theory.spec.canonical_v2.case import CaseEvent
    from unified.process import LegalEventKind, ProcessEvent

    modes = intake["modes"]
    events = [
        ProcessEvent(
            event=CaseEvent(
                event_id="pay-joint-recovery",
                event_type="PAYMENT_PERFORMED",
                occurred_at=4,
                observed_at=4,
                object_ref="joint_recovery",
            ),
            kind=LegalEventKind.PAYMENT_PERFORMED,
            basis_key="JOINT_RECOVERY",
            amount=modes["recoveries"][0],
            debt_order=("JOINT_RECOVERY",),
        ),
        ProcessEvent(
            event=CaseEvent(
                event_id="pay-internal-recourse",
                event_type="PAYMENT_PERFORMED",
                occurred_at=7,
                observed_at=7,
                object_ref="internal_recourse",
            ),
            kind=LegalEventKind.PAYMENT_PERFORMED,
            basis_key="INTERNAL_SHARE",
            amount=sum(modes["recourse"], F(0)),
            debt_order=("INTERNAL_SHARE",),
        ),
    ]
    return tuple(events)
