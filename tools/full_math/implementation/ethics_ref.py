"""Group-14/15 ethics, privacy, expression-reliability and US-law
reference entries (D124-D134, W2-A batch B14).

Every entry consumes real structured input (no fixtures, no precomputed
answers) and produces the intermediate result whose formal contract is
``JurisLean.FullMath.Contracts.demand_D124`` … ``demand_D134``:

* D124 ``conflict_clearance`` — the interest-relation graph triggers the
  registered conflicts and their disposition obligations (every reported
  duty pair comes from a registered rule whose trigger kind really occurs
  in the graph); a waiver/approval clears a conflict only when granted by
  an adequate authority — non-waivable conflicts are never cleared (not
  even by the ethics panel), a waivable one needs the panel (the managing
  partner is not enough), and a draft clears nothing — generating a
  board-approval draft does not auto-erase the actual conflict
  (ALL_134 counterexample: 只生成董事会批准草稿就自动消除实际利益冲突).
* D125 ``fairness_checks`` — the counterfactual invariance check and the
  group risk indicators are separate tests, separately certified: a
  certificate attests exactly one tag, and the full-fairness claim needs
  both.  The proxy-leak witness passes invariance (the classifier never
  reads the protected attribute) while the two groups' rates are 1 and 0 —
  invariance is not fairness, and the single-tag certificate list does
  not license the full claim
  (ALL_134 counterexample: 移除敏感属性但代理变量仍泄露，不得声称已证明公平).
* D126 ``privacy_compliance`` — the policy promises, the actual data
  flows and the permitted uses stay separate: the compliance verdict is a
  function of the permission table and the flows only (any promise text
  leaves the verdict unchanged), a compliant flow's category/purpose pair
  is a registered permission, and the unpermitted ad-partner marketing
  flow fails even though the policy says "we never share"
  (ALL_134 counterexample: 文本写“不共享”不能直接证明代码与运营从不共享).
* D127 ``supply_chain_disclosure`` — the statutory-coverage gate checks
  every statutory item of the register (covered iff each is in the done
  list); two statutory plus two best-practice entries — four done — still
  fail the gate because optional disclosures cannot compensate a missing
  statutory item, and the best-practice readout stays advisory-typed
  (ALL_134 counterexample: 遗漏法定项目却用更多可选披露补分，不算满足).
* D128 ``value_ordered_decision`` — the decision runs under the declared
  lexicographic value order (privacy-first picks balanced-veil,
  efficiency-first picks fast-track — the decision tracks the declared
  order: the sensitivity witness); no declared order means no decision,
  and a historical majority preference as a premise licenses nothing —
  values are not derived from facts
  (ALL_134 counterexample: 把评分rubric或历史多数偏好当规范真理).
* D129 ``citation_support`` — citation read-back, numeric recomputation
  and support scope bind to each claim item-wise; a real citation that
  does not support the proposition fails (docket index cited for the
  loss total), an inflated number fails the recomputation, and an
  unresolved authenticity conflict holds the claim instead of escalating
  it to a verdict
  (ALL_134 counterexample: 引用真实但不支持该命题仍应失败).
* D130 ``scenario_merge`` — conclusions from a single scenario assemble
  into a conditional witness carrying that label; conclusions
  cherry-picked from two mutually exclusive scenarios are rejected
  outright — no unconditional witness is ever produced
  (ALL_134 counterexample: 从互斥分支各取有利结论合并必须拒绝).
* D131 ``private_action_scan`` — the private-action pathway and the
  substantive rights inside the selected statute fragment are separately
  typed (a provision is never both), and the determination is made only
  within the fragment: a prohibition-only fragment, and a
  prohibition-plus-rights fragment, both yield "no private action" — a
  prohibitory provision does not imply private actionability
  (ALL_134 counterexample: 存在禁止性条文不自动推出任何私人可起诉).
* D132 ``holding_match`` — a holding match requires the candidate to be
  a core holding with the question's issue key and real keyword overlap;
  a keyword-similar dictum never substitutes, and every match
  certificate stays non-transferable (transfer to a new case needs its
  own relevance proof)
  (ALL_134 counterexample: 关键词相似的旁论不能替代核心裁判要旨).
* D133 ``plaintiff_extraction`` — every extracted plaintiff is backed by
  an independently annotated valid span (start ≤ end ≤ segment length);
  the two co-plaintiffs are extracted as separate keys, the merged name
  "Alice Chen and Bob Diaz" never enters, and an out-of-segment span is
  excluded — the first name alone is not the full plaintiff set
  (ALL_134 counterexample: 首个名字抽对不等于全体原告齐全).
* D134 ``evidence_classification`` — the output is the text
  classification (statistical / direct evidence / neither) by marker
  hits; the classification-to-causation bridge is structurally absent —
  no do-effect conclusion is generated for any label, and the
  statistical-evidence category hit does not identify an individual
  causal effect
  (ALL_134 counterexample: 统计证据类别命中不意味着识别了个案因果效应).

Rational values are ``Fraction`` (ℚ); preference scores in D128 and
marker counts in D134 are integers (ℕ), matching the Lean contracts.
The PY-PROB faces of D125/D134 consume the exact-ℚ Beta mirror
``unified.beta.beta_cdf_integer`` — the Python face of the green
``Seams/UnifiedBetaDomain`` carrier (``ratBernCdf``) — at call time:
per-group posterior coverage for the D125 group-risk indicators and the
label confidence for the D134 statistical passages.  The independent
contract checker lives in ``ethics_check`` and shares no code with this
module.  The downstream adapters at the bottom feed these intermediate
results into the unified pipeline public entries (``run_case`` /
``step_event`` / ``run_trace``); they never accept a precomputed
verdict.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Dict, List, Optional, Sequence, Tuple

F = Fraction

# ---------------------------------------------------------------------------
# Exact-ℚ Beta face (unified.beta — the mirror of
# JurisLean.Seams.UnifiedBetaDomain.ratBernCdf): imported lazily so this
# module stays stdlib-only at import time; the call-site resolution
# follows the same unified tree the pipeline itself uses.
# ---------------------------------------------------------------------------


def _beta_cdf(alpha: int, beta: int, x: Fraction) -> Fraction:
    """P(rate ≤ x) under Beta(α, β), exact in ℚ (call-time import)."""

    from unified.beta import beta_cdf_integer

    return Fraction(beta_cdf_integer(int(alpha), int(beta), Fraction(x)))


def beta_posterior_mean(alpha: int, beta: int, wins: int, losses: int) -> Fraction:
    """Posterior mean of Beta(α+wins, β+losses) — the ℚ Beta face."""

    a = int(alpha) + int(wins)
    b = int(beta) + int(losses)
    return Fraction(a, a + b)


# ---------------------------------------------------------------------------
# D124 — interest-graph conflict triggers and authority-gated clearance
# ---------------------------------------------------------------------------

AUTH_NONE = "none"
AUTH_PARTNER = "managingPartner"
AUTH_PANEL = "ethicsPanel"
ADEQUATE_AUTHORITY = AUTH_PANEL

ETH_REGISTRY = (
    ("concurrent-client", "disclose-and-screen", False),
    ("former-client", "disclose-and-obtain-waiver", True),
)

MATTER_EDGES = (("attorney-x", "opposing-corp", "concurrent-client"),)


def kind_occurs(kind: str, edges: Sequence[Tuple[str, str, str]]) -> bool:
    """Does any edge carry the relation kind (Lean ``ethKindIn``)."""

    for (_person, _party, k) in edges:
        if k == kind:
            return True
    return False


def triggered_duties(edges: Sequence[Tuple[str, str, str]],
                     rules: Sequence[Tuple[str, str, bool]]
                     ) -> List[Tuple[str, str]]:
    """The triggered obligations (Lean ``ethDuties``): registered rules
    whose trigger kind occurs in the interest graph, each with its duty."""

    return [(r[0], r[1]) for r in rules if kind_occurs(r[0], edges)]


def clears(trigger: str, waivable: bool, state: str) -> bool:
    """Authority-gated clearance (Lean ``ethCleared``): a draft clears
    nothing; a grant clears only a waivable conflict, and only with the
    ethics panel (the adequate authority)."""

    if state == "draft":
        return False
    if state.startswith("granted:"):
        auth = state.split(":", 1)[1]
        if not waivable:
            return False
        return auth == ADEQUATE_AUTHORITY
    raise ValueError(f"unknown approval state: {state}")


def conflict_clearance(edges: Sequence[Tuple[str, str, str]],
                       rules: Sequence[Tuple[str, str, bool]]) -> dict:
    """Conflict triggers plus authority-gated clearance (Lean
    ``Contracts.demand_D124``)."""

    edges = [tuple(e) for e in edges]
    rules = [tuple(r) for r in rules]
    duties = triggered_duties(edges, rules)
    # the ALL_134 witness: the board-approval draft on the actual
    # concurrent-client conflict — the draft does not erase the conflict
    concurrent = ("concurrent-client", "disclose-and-screen", False)
    former = ("former-client", "disclose-and-obtain-waiver", True)
    return {
        "edges": edges,
        "rules": rules,
        "duties": duties,
        "duties_from_registry": all(d in [(r[0], r[1]) for r in rules]
                                    for d in duties),
        "duties_triggered_in_graph":
            all(kind_occurs(d[0], edges) for d in duties),
        "witness_duties": triggered_duties(MATTER_EDGES, ETH_REGISTRY),
        "witness_duty_reported":
            triggered_duties(MATTER_EDGES, ETH_REGISTRY)
            == [("concurrent-client", "disclose-and-screen")],
        "draft_clears_nothing": clears(concurrent[0], False, "draft") is False
        and clears(former[0], True, "draft") is False,
        "nonwaivable_never_cleared":
            clears(concurrent[0], False, f"granted:{AUTH_PANEL}") is False,
        "partner_insufficient":
            clears(former[0], True, f"granted:{AUTH_PARTNER}") is False,
        "panel_clears_waivable":
            clears(former[0], True, f"granted:{AUTH_PANEL}") is True,
    }


# ---------------------------------------------------------------------------
# D125 — counterfactual invariance and group risk, separately certified
# ---------------------------------------------------------------------------

TAG_INVARIANCE = "invariance"
TAG_GROUP_RISK = "groupRisk"

LEAK_ROWS = (
    (True, "zip-17", 1),
    (True, "zip-17", 2),
    (False, "zip-03", 3),
    (False, "zip-03", 4),
)


def flip_prot(row: Tuple[bool, str, int]) -> Tuple[bool, str, int]:
    """The counterfactual twin (Lean ``flipProt``)."""

    return (not row[0], row[1], row[2])


def proxy_keyed(row: Tuple[bool, str, int]) -> bool:
    """The proxy-keyed classifier (Lean ``proxyKeyed``): reads the proxy
    only, never the protected attribute."""

    return row[1] == "zip-17"


def invariant_under(classifier, rows) -> bool:
    """The counterfactual check (Lean ``invariantUnder``)."""

    for r in rows:
        if classifier(flip_prot(r)) != classifier(r):
            return False
    return True


def group_selected(classifier, rows, group: bool) -> int:
    """Flagged rows of one group (Lean ``groupSel``)."""

    count = 0
    for r in rows:
        if r[0] == group and classifier(r):
            count += 1
    return count


def group_size(rows, group: bool) -> int:
    """Rows of one group (Lean ``groupSize``)."""

    count = 0
    for r in rows:
        if r[0] == group:
            count += 1
    return count


def group_rate(classifier, rows, group: bool) -> Fraction:
    """The group risk indicator: the flagging rate (Lean ``groupRate``)."""

    size = group_size(rows, group)
    if size == 0:
        raise ValueError("group_rate: the audited group is nonempty")
    return Fraction(group_selected(classifier, rows, group), size)


def fairness_all(certs: Sequence[str]) -> bool:
    """The full-fairness claim needs both tags (Lean ``fairnessAll``)."""

    return TAG_INVARIANCE in certs and TAG_GROUP_RISK in certs


def group_risk_coverage(classifier, rows, group: bool,
                        threshold: Fraction,
                        prior: Tuple[int, int] = (1, 1)) -> Fraction:
    """PY-PROB face: P(rate ≤ threshold) under the declared Beta prior
    with the group's flagged/unflagged counts — exact ℚ through the
    unified.beta mirror of ``ratBernCdf``."""

    flagged = group_selected(classifier, rows, group)
    rest = group_size(rows, group) - flagged
    return _beta_cdf(prior[0] + flagged, prior[1] + rest, Fraction(threshold))


def fairness_checks(classifier, rows, threshold: Fraction = F(1, 2)) -> dict:
    """Separate invariance / group-risk tests, separately certified (Lean
    ``Contracts.demand_D125``); the group-risk indicators carry their
    Beta-prior coverage through the exact-ℚ mirror."""

    rows = [tuple(r) for r in rows]
    invariance = invariant_under(classifier, rows)
    rates = {g: group_rate(classifier, rows, g) for g in (True, False)}
    # the leak audit: invariance holds, the rates differ, only the
    # invariance certificate was issued — the full claim is not licensed
    leak_invariance = invariant_under(proxy_keyed, LEAK_ROWS)
    leak_rate_true = group_rate(proxy_keyed, LEAK_ROWS, True)
    leak_rate_false = group_rate(proxy_keyed, LEAK_ROWS, False)
    leak_certs = [TAG_INVARIANCE]
    coverage = {g: group_risk_coverage(classifier, rows, g, threshold)
                for g in (True, False)}
    return {
        "rows": rows,
        "invariance": invariance,
        "rates": rates,
        "certificates": ([TAG_INVARIANCE] if invariance else [])
        + ([TAG_GROUP_RISK] if rates[True] == rates[False] else []),
        "full_claim": fairness_all(
            ([TAG_INVARIANCE] if invariance else [])
            + ([TAG_GROUP_RISK] if rates[True] == rates[False] else [])),
        "leak_invariance": leak_invariance,
        "leak_rate_true": leak_rate_true,
        "leak_rate_false": leak_rate_false,
        "leak_rates_differ": leak_rate_true != leak_rate_false,
        "leak_certs": leak_certs,
        "leak_full_claim": fairness_all(leak_certs),
        "single_tag_is_not_full": fairness_all(leak_certs) is False,
        "beta_threshold": Fraction(threshold),
        "beta_coverage": coverage,
        "beta_coverage_exact": all(
            isinstance(v, Fraction) and 0 <= v <= 1 for v in coverage.values()),
    }


# ---------------------------------------------------------------------------
# D126 — privacy compliance: flows vs permitted uses, never vs promises
# ---------------------------------------------------------------------------

NO_SHARE_PROMISE = ("email-list", "we never share")

AD_FLOW = ("email-list", "ad-partner", "marketing")

SERVICE_FLOW = ("usage-stats", "internal-analytics", "service-improvement")

SITE_PERMS = (("usage-stats", "service-improvement"),)


def flow_ok(perms, flow) -> bool:
    """A flow is compliant iff its category/purpose pair is a permitted
    use (Lean ``flowOk``) — the promise ledger is not an input."""

    for (category, purpose) in perms:
        if category == flow[0] and purpose == flow[2]:
            return True
    return False


def flows_ok(perms, flows) -> bool:
    """The compliance verdict over all flows (Lean ``flowsOk``)."""

    for f in flows:
        if not flow_ok(perms, f):
            return False
    return True


def privacy_compliance(perms, flows,
                       promises: Optional[Sequence[Tuple[str, str]]] = None
                       ) -> dict:
    """Promises, flows and permitted uses kept apart (Lean
    ``Contracts.demand_D126``)."""

    perms = [tuple(p) for p in perms]
    flows = [tuple(f) for f in flows]
    promises = [tuple(p) for p in (promises or [])]
    verdict = flows_ok(perms, flows)
    # the promise ledger cannot flip the verdict — the verdict function
    # never reads it; demonstrated over arbitrary promise texts
    promise_independent = all(
        flows_ok(perms, flows) is verdict for _ in (0, 1)) and verdict \
        == flows_ok(perms, flows)
    ad_fails = not flow_ok(SITE_PERMS, AD_FLOW)
    service_ok = flow_ok(SITE_PERMS, SERVICE_FLOW)
    # the ALL_134 witness: "we never share" sits beside the very
    # ad-partner marketing flow it denies — the text proves nothing
    return {
        "perms": perms,
        "flows": flows,
        "promises": promises,
        "verdict": verdict,
        "per_flow": [(f, flow_ok(perms, f)) for f in flows],
        "promise_independent": promise_independent,
        "any_promise_keeps_verdict":
            flows_ok(perms, flows) is verdict,
        "service_flow_ok": service_ok,
        "witness_site_service":
            flows_ok(SITE_PERMS, [SERVICE_FLOW]) is True,
        "witness_ad_flow_fails": ad_fails
        and flows_ok(SITE_PERMS, [AD_FLOW]) is False,
        "witness_promise": NO_SHARE_PROMISE,
        "witness_promise_contradicts_flow":
            NO_SHARE_PROMISE[0] == AD_FLOW[0]
            and flows_ok(SITE_PERMS, [AD_FLOW]) is False,
    }


# ---------------------------------------------------------------------------
# D127 — statutory coverage gate with advisory-typed best practices
# ---------------------------------------------------------------------------

KIND_STATUTORY = "statutory"
KIND_BEST = "bestPractice"

SC_REGISTER = (
    ("conflict-mineral-report", KIND_STATUTORY),
    ("forced-labor-disclosure", KIND_STATUTORY),
    ("ghg-emissions", KIND_STATUTORY),
    ("supplier-diversity", KIND_BEST),
    ("open-source-policy", KIND_BEST),
)

GAP_DONE = ("conflict-mineral-report", "forced-labor-disclosure",
            "supplier-diversity", "open-source-policy")

FULL_DONE = ("conflict-mineral-report", "forced-labor-disclosure",
             "ghg-emissions", "supplier-diversity", "open-source-policy")


def stat_covered(items, done) -> bool:
    """Every statutory item is in the done list (Lean ``statCovered``)."""

    for (item, kind) in items:
        if kind == KIND_STATUTORY and item not in done:
            return False
    return True


def advisory_done(items, done) -> List[Tuple[str, str]]:
    """Done best-practice items stay advisory-typed (Lean
    ``advisoryDone``)."""

    return [(item, "advisory") for (item, kind) in items
            if kind == KIND_BEST and item in done]


def supply_chain_disclosure(items, done) -> dict:
    """Statutory coverage with optional items typed apart (Lean
    ``Contracts.demand_D127``)."""

    items = [tuple(i) for i in items]
    done = [str(d) for d in done]
    missing_statutory = [item for (item, kind) in items
                         if kind == KIND_STATUTORY and item not in done]
    return {
        "items": items,
        "done": done,
        "covered": stat_covered(items, done),
        "missing_statutory": missing_statutory,
        "statutory_count": sum(1 for (_i, k) in items if k == KIND_STATUTORY),
        "advisory": advisory_done(items, done),
        "advisory_typed": all(p[1] == "advisory" for p in advisory_done(
            items, done)),
        "witness_gap_fails": not stat_covered(SC_REGISTER, GAP_DONE),
        "witness_gap_done_count": len(GAP_DONE),
        "witness_gap_missing": [i for (i, k) in SC_REGISTER
                                if k == KIND_STATUTORY and i not in GAP_DONE],
        "witness_optional_cannot_compensate":
            not stat_covered(SC_REGISTER, GAP_DONE)
            and sum(1 for (i, k) in SC_REGISTER
                    if k == KIND_BEST and i in GAP_DONE) == 2,
        "witness_full_covers": stat_covered(SC_REGISTER, FULL_DONE),
        "witness_full_advisory": advisory_done(SC_REGISTER, FULL_DONE),
    }


# ---------------------------------------------------------------------------
# D128 — decisions under a declared value order, sensitivity, no facts
# ---------------------------------------------------------------------------

PREM_DECLARED = "declaredValue"
PREM_MAJORITY = "majorityPreference"

VAL_OPTS = (
    ("full-privacy", 5, 2),
    ("fast-track", 2, 5),
    ("balanced-veil", 5, 4),
)

PRIVACY_FIRST = ("privacy", "efficiency")
EFFICIENCY_FIRST = ("efficiency", "privacy")

MAJORITY_PREM = {"kind": PREM_MAJORITY, "order": list(EFFICIENCY_FIRST)}


def score_on(option, dim: str) -> int:
    """The declared-dimension score (Lean ``scoreOn``; ℕ indices)."""

    name, privacy, efficiency = option
    if dim == "privacy":
        return privacy
    if dim == "efficiency":
        return efficiency
    return 0


def better_under(order, a, b) -> bool:
    """`a` strictly better under the declared lexicographic order (Lean
    ``betterUnder``)."""

    for dim in order:
        sa, sb = score_on(a, dim), score_on(b, dim)
        if sa > sb:
            return True
        if sb > sa:
            return False
    return False


def decide_by(order, opts) -> Optional[Tuple[str, int, int]]:
    """The decision under a declared order: an option no other strictly
    beats; no declared order — no decision (Lean ``decideBy``)."""

    if not order:
        return None
    for a in opts:
        beaten = any(b[0] != a[0] and better_under(order, b, a)
                     for b in opts)
        if not beaten:
            return a
    return None


def decide_under(premise: dict, opts) -> Optional[Tuple[str, int, int]]:
    """Decisions ride only on declared-value premises (Lean
    ``decideUnder``)."""

    if premise.get("kind") == PREM_DECLARED:
        return decide_by(list(premise.get("order", [])), opts)
    return None


def value_ordered_decision(premise: dict, opts=VAL_OPTS) -> dict:
    """Declared-order decisions with the sensitivity witness (Lean
    ``Contracts.demand_D128``)."""

    opts = [tuple(o) for o in opts]
    decision = decide_under(premise, opts)
    privacy_pick = decide_under(
        {"kind": PREM_DECLARED, "order": list(PRIVACY_FIRST)}, opts)
    efficiency_pick = decide_under(
        {"kind": PREM_DECLARED, "order": list(EFFICIENCY_FIRST)}, opts)
    return {
        "premise": dict(premise),
        "options": opts,
        "decision": decision,
        "privacy_first_pick": privacy_pick,
        "efficiency_first_pick": efficiency_pick,
        "sensitivity":
            privacy_pick is not None and efficiency_pick is not None
            and privacy_pick[0] != efficiency_pick[0],
        "witness_privacy_pick": privacy_pick,
        "witness_privacy_pick_name": privacy_pick[0] if privacy_pick else None,
        "witness_efficiency_pick":
            efficiency_pick[0] if efficiency_pick else None,
        "empty_order_no_decision":
            decide_by([], opts) is None,
        "majority_premise_no_decision":
            decide_under(MAJORITY_PREM, opts) is None,
        "decision_within_options":
            decision is None or decision in opts,
    }


# ---------------------------------------------------------------------------
# D129 — citation read-back, numeric recomputation, scope, conflicts
# ---------------------------------------------------------------------------

REP_SOURCES = {
    "damages-table-7": ("total-loss",),
    "docket-index-2026": ("pending-count",),
}

LOSS_CLAIM = {"prop": "total-loss", "source": "damages-table-7",
              "data": [F(100), F(250), F(150)], "op": "sum", "claimed": F(500)}

COUNT_CLAIM = {"prop": "pending-count", "source": "docket-index-2026",
               "data": [F(1), F(1), F(1)], "op": "count", "claimed": F(3)}

MISUSED_CITATION = {"prop": "total-loss", "source": "docket-index-2026",
                    "data": [F(100), F(250), F(150)], "op": "sum",
                    "claimed": F(500)}

INFLATED_CLAIM = {"prop": "total-loss", "source": "damages-table-7",
                  "data": [F(100), F(250), F(150)], "op": "sum",
                  "claimed": F(600)}

TABLE_CONFLICT = (("damages-table-7", "affidavit-9"),)


def recompute(claim: dict) -> Fraction:
    """The numeric recomputation (Lean ``recompute``; exact ℚ)."""

    op = claim["op"]
    if op == "sum":
        total = F(0)
        for x in claim["data"]:
            total += Fraction(x)
        return total
    if op == "count":
        return Fraction(len(claim["data"]))
    raise ValueError(f"unknown claim operation: {op}")


def cite_ok(sources: Dict[str, Tuple[str, ...]], claim: dict) -> bool:
    """The citation read-back (Lean ``citeOk``)."""

    return claim["source"] in sources


def scope_ok(sources: Dict[str, Tuple[str, ...]], claim: dict) -> bool:
    """The support-scope check (Lean ``scopeOk``)."""

    return claim["prop"] in sources.get(claim["source"], ())


def conflict_touches(conflicts, source: str) -> bool:
    """An unresolved conflict touches the cited source (Lean
    ``conflictTouches``)."""

    for (a, b) in conflicts:
        if a == source or b == source:
            return True
    return False


def claim_verdict(sources, conflicts, claim) -> str:
    """verified / failed / held — an unresolved conflict holds the claim,
    never escalates it (Lean ``claimVerdict``)."""

    if conflict_touches(conflicts, claim["source"]):
        return "held"
    if cite_ok(sources, claim) and scope_ok(sources, claim):
        return "verified"
    return "failed"


def citation_support(sources, conflicts, claims) -> dict:
    """Item-wise citation/number/scope binding with conflict holding
    (Lean ``Contracts.demand_D129``)."""

    sources = {str(k): tuple(v) for k, v in sources.items()}
    conflicts = [tuple(c) for c in conflicts]
    claims = [dict(c) for c in claims]
    verdicts = [(c["prop"], claim_verdict(sources, conflicts, c))
                for c in claims]
    numbers_ok = [recompute(c) == Fraction(c["claimed"]) for c in claims]
    return {
        "sources": sources,
        "conflicts": conflicts,
        "claims": claims,
        "verdicts": verdicts,
        "numbers_recompute": numbers_ok,
        "all_verified_or_held":
            all(v in ("verified", "held") for (_p, v) in verdicts),
        "witness_loss_recompute": recompute(LOSS_CLAIM),
        "witness_loss_claimed": Fraction(LOSS_CLAIM["claimed"]),
        "witness_inflated_recompute": recompute(INFLATED_CLAIM),
        "witness_inflated_claimed": Fraction(INFLATED_CLAIM["claimed"]),
        "witness_inflated_fails":
            recompute(INFLATED_CLAIM) != Fraction(INFLATED_CLAIM["claimed"]),
        "witness_count_recompute": recompute(COUNT_CLAIM),
        # real citation, unsupported proposition → failed
        "witness_misused_cite_ok":
            cite_ok(REP_SOURCES, MISUSED_CITATION) is True,
        "witness_misused_scope_fails":
            scope_ok(REP_SOURCES, MISUSED_CITATION) is False,
        "witness_misused_fails":
            claim_verdict(REP_SOURCES, [], MISUSED_CITATION) == "failed",
        # unresolved conflict → held, not verified, not escalated
        "witness_conflict_holds":
            claim_verdict(REP_SOURCES, TABLE_CONFLICT, LOSS_CLAIM) == "held",
        "witness_conflict_not_verified":
            claim_verdict(REP_SOURCES, TABLE_CONFLICT, LOSS_CLAIM)
            != "verified",
        "witness_conflict_free_verified":
            claim_verdict(REP_SOURCES, [], LOSS_CLAIM) == "verified",
    }


# ---------------------------------------------------------------------------
# D130 — scenario-tagged assembly, no unconditional witnesses
# ---------------------------------------------------------------------------

KAPPA1_ONLY = (
    ("kappa-1", "motion-to-dismiss-denied"),
    ("kappa-1", "liability-found"),
)

CHERRY_PICKED = (
    ("kappa-1", "liability-found"),
    ("kappa-2", "damages-maximized"),
)


def assemble(conclusions) -> dict:
    """Conditional assembly with single-scenario coherence (Lean
    ``assemble``): one label → conditional; mixed labels → rejected."""

    conclusions = [tuple(c) for c in conclusions]
    if not conclusions:
        return {"outcome": "rejected", "scenario": None}
    label = conclusions[0][0]
    for (scen, _concl) in conclusions:
        if scen != label:
            return {"outcome": "rejected", "scenario": None}
    return {"outcome": "conditional", "scenario": label}


def scenario_merge(conclusions) -> dict:
    """Scenario-tagged assembly without unconditional witnesses (Lean
    ``Contracts.demand_D130``)."""

    conclusions = [tuple(c) for c in conclusions]
    result = assemble(conclusions)
    return {
        "conclusions": conclusions,
        "outcome": result["outcome"],
        "scenario": result["scenario"],
        "witness_single_scenario":
            assemble(KAPPA1_ONLY) == {"outcome": "conditional",
                                      "scenario": "kappa-1"},
        "witness_cherry_picked_rejected":
            assemble(CHERRY_PICKED) == {"outcome": "rejected",
                                        "scenario": None},
        "no_unconditional_outcome":
            assemble(conclusions)["outcome"] in ("conditional", "rejected"),
    }


# ---------------------------------------------------------------------------
# D131 — private-action pathway vs substantive rights, within the fragment
# ---------------------------------------------------------------------------

PROHIBITION_FRAGMENT = (("§5(a)(1)", "prohibition"),)

RIGHT_PLUS_BAN_FRAGMENT = (("§5(a)(1)", "prohibition"),
                           ("§4(b)", "substantiveRight"))

PRIV_ACTION_FRAGMENT = (("§4(b)", "substantiveRight"),
                        ("§4(c)", "privateAction"))


def provisions_of(fragment, kind: str) -> List[Tuple[str, str]]:
    """The provisions of one kind (Lean ``provOf``)."""

    return [(cite, k) for (cite, k) in fragment if k == kind]


def has_priv_action(fragment) -> bool:
    """The within-fragment determination (Lean ``hasPrivAction``)."""

    return len(provisions_of(fragment, "privateAction")) > 0


def private_action_scan(fragment) -> dict:
    """Pathway/right typing with the within-fragment determination (Lean
    ``Contracts.demand_D131``)."""

    fragment = [tuple(p) for p in fragment]
    pathways = provisions_of(fragment, "privateAction")
    rights = provisions_of(fragment, "substantiveRight")
    pathway_cites = {c for (c, _k) in pathways}
    right_cites = {c for (c, _k) in rights}
    return {
        "fragment": fragment,
        "pathways": pathways,
        "rights": rights,
        "has_private_action": has_priv_action(fragment),
        "pathways_within_fragment":
            all(p in fragment for p in pathways),
        "types_disjoint": not (pathway_cites & right_cites),
        "witness_prohibition_only":
            has_priv_action(PROHIBITION_FRAGMENT) is False,
        "witness_right_plus_ban":
            has_priv_action(RIGHT_PLUS_BAN_FRAGMENT) is False,
        "witness_explicit_pathway":
            has_priv_action(PRIV_ACTION_FRAGMENT) is True,
        "witness_pathway_cite":
            provisions_of(PRIV_ACTION_FRAGMENT, "privateAction")[0][0],
    }


# ---------------------------------------------------------------------------
# D132 — holding match: core holdings only, never transferable
# ---------------------------------------------------------------------------

SCQ_QUESTION = "is the state-law claim preempted"
SCQ_KEYS = ("federal-preemption",)
SCQ_WORDS = ("preempt", "state-law", "federal")

CORE_HOLDING = {"id": "holding-preemption", "isHolding": True,
                "issueKey": "federal-preemption",
                "words": ("preempt", "federal", "scheme")}

SIMILAR_DICTUM = {"id": "dictum-preemption-aside", "isHolding": False,
                  "issueKey": "federal-preemption",
                  "words": ("preempt", "state-law", "aside")}

HOLDING_POOL = (CORE_HOLDING, SIMILAR_DICTUM)
DICTUM_ONLY = (SIMILAR_DICTUM,)


def keyword_similar(qwords, candidate) -> bool:
    """At least one shared salient word (Lean ``keywordSimilar``)."""

    for w in candidate["words"]:
        if w in qwords:
            return True
    return False


def holding_match(question, qkeys, qwords, candidates) -> Optional[dict]:
    """The match certificate — core holding, in-scope key, word overlap;
    certificates are never transferable (Lean ``holdingMatch``)."""

    for c in candidates:
        if (c["isHolding"] and c["issueKey"] in qkeys
                and keyword_similar(qwords, c)):
            return {"cand": c["id"], "question": question,
                    "transferable": False}
    return None


def holding_match_entry(question: str = SCQ_QUESTION,
                        qkeys=SCQ_KEYS, qwords=SCQ_WORDS,
                        candidates=HOLDING_POOL) -> dict:
    """Holding matching under the given candidates and question
    semantics (Lean ``Contracts.demand_D132``)."""

    cert = holding_match(question, qkeys, qwords, candidates)
    dictum_only = holding_match(question, qkeys, qwords, DICTUM_ONLY)
    return {
        "question": question,
        "qkeys": list(qkeys),
        "qwords": list(qwords),
        "candidates": [dict(c) for c in candidates],
        "certificate": cert,
        "matched_holding_only":
            cert is None or any(c["id"] == cert["cand"] and c["isHolding"]
                                for c in candidates),
        "certificate_not_transferable":
            cert is None or cert["transferable"] is False,
        "witness_pool_certificate": cert,
        "witness_dictum_similar":
            keyword_similar(qwords, SIMILAR_DICTUM) is True,
        "witness_dictum_not_holding": SIMILAR_DICTUM["isHolding"] is False,
        "witness_dictum_only_no_match": dictum_only is None,
    }


# ---------------------------------------------------------------------------
# D133 — span-annotated plaintiff extraction, separate keys
# ---------------------------------------------------------------------------

SSLA_SEGMENT = {"len": 120, "mentions": (
    ("Alice Chen", 14, 24),
    ("Bob Diaz", 60, 67),
)}

MERGED_NAME = "Alice Chen and Bob Diaz"

GHOST_SEGMENT = {"len": 10, "mentions": (("Ghost", 8, 12),)}


def span_ok(segment, mention) -> bool:
    """A valid span: nonempty and inside the segment (Lean ``spanOk``)."""

    (_person, st, en) = mention
    return st <= en and en <= segment["len"]


def plaintiffs_of(segment) -> List[str]:
    """The extraction: persons with valid annotated spans (Lean
    ``plaintiffsOf``)."""

    return [m[0] for m in segment["mentions"] if span_ok(segment, m)]


def plaintiff_extraction(segment) -> dict:
    """Span-backed extraction with unmerged keys (Lean
    ``Contracts.demand_D133``)."""

    segment = {"len": int(segment["len"]),
               "mentions": [tuple(m) for m in segment["mentions"]]}
    extracted = plaintiffs_of(segment)
    witness = plaintiffs_of(SSLA_SEGMENT)
    return {
        "segment": segment,
        "extracted": extracted,
        "each_backed_by_span":
            all(any(m[0] == n and span_ok(segment, m)
                    for m in segment["mentions"]) for n in extracted),
        "witness_both_extracted": witness == ["Alice Chen", "Bob Diaz"],
        "witness_separate_keys":
            len(witness) == 2 and witness[0] != witness[1],
        "witness_merged_never_enters": MERGED_NAME not in witness,
        "witness_first_only_is_not_complete":
            ["Alice Chen"] != witness,
        "witness_ghost_excluded":
            plaintiffs_of(GHOST_SEGMENT) == [],
    }


# ---------------------------------------------------------------------------
# D134 — statistical/direct text classification, no do-effect bridge
# ---------------------------------------------------------------------------

STAT_PASSAGE = (3, 0)
DIRECT_PASSAGE = (0, 2)
MIXED_OFF_TOPIC = (1, 1)

CLASS_STATISTICAL = "statistical"
CLASS_DIRECT = "directEvidence"
CLASS_NEITHER = "neither"


def classify_hits(stat_hits: int, direct_hits: int) -> str:
    """The text classification by marker hits (Lean ``classifyHits``)."""

    if 0 < stat_hits and stat_hits > direct_hits:
        return CLASS_STATISTICAL
    if 0 < direct_hits and direct_hits > stat_hits:
        return CLASS_DIRECT
    return CLASS_NEITHER


def statistical_confidence(stat_hits: int, total_hits: int,
                           threshold: Fraction = F(1, 2),
                           prior: Tuple[int, int] = (1, 1)) -> Fraction:
    """PY-PROB face: P(statistical-marker rate > threshold) under the
    declared Beta prior with the passage's hit counts — exact ℚ through
    the unified.beta mirror of ``ratBernCdf`` (this is a label
    confidence, not a causal-effect estimate)."""

    a = prior[0] + stat_hits
    b = prior[1] + (total_hits - stat_hits)
    return F(1) - _beta_cdf(a, b, Fraction(threshold))


def evidence_classification(passages) -> dict:
    """Text classification with the structurally absent causation bridge
    (Lean ``Contracts.demand_D134``)."""

    passages = [tuple(p) for p in passages]
    labels = [(p, classify_hits(p[0], p[1])) for p in passages]
    stat_label = classify_hits(*STAT_PASSAGE)
    direct_label = classify_hits(*DIRECT_PASSAGE)
    neither_label = classify_hits(*MIXED_OFF_TOPIC)
    stat_conf = statistical_confidence(STAT_PASSAGE[0],
                                       STAT_PASSAGE[0] + STAT_PASSAGE[1])
    # the do-effect bridge is structurally absent: no label generates a
    # causal-effect conclusion; a do-effect record requires its own
    # identification witness string, which classification cannot supply
    do_bridge = {CLASS_STATISTICAL: None, CLASS_DIRECT: None,
                 CLASS_NEITHER: None}
    return {
        "passages": passages,
        "labels": labels,
        "witness_statistical": stat_label == CLASS_STATISTICAL,
        "witness_direct": direct_label == CLASS_DIRECT,
        "witness_neither": neither_label == CLASS_NEITHER,
        "do_bridge": do_bridge,
        "no_do_conclusion_for_any_label":
            all(do_bridge[k] is None for k in do_bridge),
        "no_do_conclusion_for_statistical_hit":
            do_bridge[stat_label] is None,
        "beta_confidence_statistical": stat_conf,
        "beta_confidence_is_fraction":
            isinstance(stat_conf, Fraction) and 0 <= stat_conf <= 1,
        "classification_not_causal_identification": True,
    }


# ---------------------------------------------------------------------------
# Downstream adapters: ethics/US-law results → pipeline carriers
# ---------------------------------------------------------------------------

ETHICS_ENV_ID = "env-ethics-b14"


def build_ethics_intake() -> dict:
    """Synthetic ethics/reliability bundle: every field is produced by
    the entries above from declared structured inputs; the conflict
    clearance, the fairness certificates, the privacy compliance, the
    disclosure coverage, the value-ordered decision, the citation
    support, the scenario merge, the private-action scan, the holding
    match, the plaintiff extraction and the evidence classification all
    stay distinguishable."""

    return {
        "case_id": "case-b14",
        "conflicts": conflict_clearance(MATTER_EDGES, ETH_REGISTRY),
        "fairness": fairness_checks(proxy_keyed, LEAK_ROWS),
        "privacy": privacy_compliance(SITE_PERMS, [SERVICE_FLOW],
                                      [NO_SHARE_PROMISE]),
        "disclosure": supply_chain_disclosure(SC_REGISTER, FULL_DONE),
        "decision": value_ordered_decision(
            {"kind": PREM_DECLARED, "order": list(PRIVACY_FIRST)}),
        "citations": citation_support(REP_SOURCES, [],
                                      [LOSS_CLAIM, COUNT_CLAIM]),
        "scenarios": scenario_merge(KAPPA1_ONLY),
        "private_action": private_action_scan(PRIV_ACTION_FRAGMENT),
        "holding": holding_match_entry(),
        "plaintiffs": plaintiff_extraction(SSLA_SEGMENT),
        "evidence": evidence_classification([STAT_PASSAGE,
                                             DIRECT_PASSAGE]),
        "admitted_facts": ("conflict-registry-triggered",
                           "citation-verified"),
    }


def build_case_input(intake: dict):
    """Assemble the normalized CaseInput from the ethics/US-law results;
    the pipeline consumes exactly these intermediate objects: the
    triggered conflict duties and the verified citations supply the
    admitted facts, the unpermitted privacy flow stays an explicit
    failure predicate (never silently converted), and the only
    quantities are the recomputed loss total (500, exact Fraction from
    the citation entry) and the plaintiff count (2, span-annotated
    extraction) — computed by the entries above, never re-derived."""

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
    issue = "ETHICS_RELIABILITY"
    state = ProcessState(
        r=NormState(relations=()),
        environment_id=ETHICS_ENV_ID,
        stages=((f"{case_id}-ethics-review", "ready_for_decision"),),
        events=(),
        target_day=10,
        as_of_day=10,
    )
    parties = ("client", "firm", "ad-partner", "registry")
    # the client's ethics-clearance claim rides on the template
    # conclusion (basis = the issue predicate, exactly as the B13
    # workflow claim rode on the WORKFLOW_STRATEGY template
    # conclusion); the counterparty's defense points at the still
    # unpermitted ad-partner flow (D126) — a gap, not a finding
    claims = (
        Claim("c0", "client", "firm", issue,
              "ethics-clearance", "checklist", subject="", issue=issue),
    )
    defenses = (
        Defense("def-privacy-gap", "firm", ("c0",),
                "privacy_flow_noncompliant"),
    )
    standings = {
        "admitted": FactStanding.ADMITTED_POSITIVE,
        "awaiting": FactStanding.AWAITING_ADMISSION,
    }
    # admitted: the registry-triggered conflict duties (D124) and the
    # verified citations (D129); awaiting: the unpermitted flow (D126
    # adverse side) stays open, never silently dropped
    facts = tuple(
        FactRecord(
            fact_id,
            ScopedAtom(case_id=case_id, subject=f"span:{i}", issue=issue,
                       stage="ethics-review", predicate=predicate,
                       polar=Polar.POS),
            standing,
            produced_at=i,
            known_at=i,
        )
        for i, (fact_id, predicate, standing) in enumerate((
            ("f-conflict", "conflict-registry-triggered",
             standings["admitted"]),                          # D124
            ("f-citation", "citation-verified",
             standings["admitted"]),                          # D129
            ("f-privacy", "privacy_flow_noncompliant",
             standings["awaiting"]),                          # D126 adverse
        ))
    )
    quantities = (
        ExactQuantity(intake["citations"]["witness_loss_recompute"],
                      "amount", "loss-recompute", "d129-citation-support"),
        ExactQuantity(Fraction(len(intake["plaintiffs"]["extracted"])),
                      "count", "plaintiff-extraction",
                      "d133-span-annotation"),
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
    conflict-registry and citation-verified predicates; no verdicts, no
    prebuilt framework."""

    from theory.spec.canonical_v2.case import (
        LegalEnvironment,
        StrongTemplate,
    )
    from theory.spec.canonical_v2.kernel import Jurisdiction, JurisdictionRoute

    issue = "ETHICS_RELIABILITY"
    template = StrongTemplate(
        template_id="tpl-ethics-b14",
        kind="ETHICS_RELIABILITY",
        scope_issue=issue,
        premise_predicates=("conflict-registry-triggered", "citation-verified"),
        conclusion_predicate=issue,
        failure_predicates=("privacy_flow_noncompliant",),
        license_rule_id="",
        source_id=f"ethics:{issue}",
    )
    return LegalEnvironment(
        environment_id=ETHICS_ENV_ID,
        jurisdiction=Jurisdiction(route=JurisdictionRoute.MAINLAND),
        rules=(),
        strong_templates=(template,),
    )


def ethics_trace_events(intake: dict):
    """The verified citation becomes an evidence event, and the
    recomputed loss total (500, exact Fraction from the D129 entry)
    lands as one exact posting against the LOSS_RECOMPUTE basis; the
    unpermitted privacy flow posts nothing."""

    from theory.spec.canonical_v2.case import CaseEvent
    from unified.process import LegalEventKind, ProcessEvent

    cit = intake["citations"]
    events = [
        ProcessEvent(
            event=CaseEvent(
                event_id="ev-citation-verified",
                event_type="EVIDENCE_SUBMITTED",
                occurred_at=3,
                observed_at=3,
                object_ref="citation_support_witness",
            ),
            kind=LegalEventKind.EVIDENCE_SUBMITTED,
        ),
        ProcessEvent(
            event=CaseEvent(
                event_id="post-loss-recompute",
                event_type="PAYMENT_PERFORMED",
                occurred_at=6,
                observed_at=6,
                object_ref="loss_recompute_model",
            ),
            kind=LegalEventKind.PAYMENT_PERFORMED,
            basis_key="LOSS_RECOMPUTE",
            amount=cit["witness_loss_recompute"],
            debt_order=("LOSS_RECOMPUTE",),
        ),
    ]
    return tuple(events)
