"""Independent checker for the T116-T121 behavior batch (J.7 discipline).

Deliberately re-implements the batch's semantics with its own inline logic
instead of importing the reference functions: IR/argmax/Pareto over the
negotiation carriers, shared-θ vs rectangular robust values, the VOI chain,
the finite-horizon Snell bound (re-derived by FULL ENUMERATION of stopping
rules — a different algorithm from the reference's backward induction),
the three trace projections, the compliance comparison, and the backflow
chain are all re-derived here from the frozen carriers alone.  It shares
only the immutable data classes of ``behavior_ref`` — never its functions —
and never calls the evaluator.

Lean contract: JurisLean.Seams.UnifiedW4Behavior (T116-T121).
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from typing import Dict, FrozenSet, Iterable, Mapping, Tuple

from tools.full_math.implementation.behavior_ref import (
    Act,
    BehaviorEvent,
    ComplianceAction,
    ComplianceGame,
    InfoAcquisition,
    MultiIssueNegotiation,
    ObservationLayer,
    ScenarioTree,
    ThresholdRule,
    Trace,
)

F = Fraction


@dataclass(frozen=True)
class CheckReport:
    ok: bool
    reasons: Tuple[str, ...]

    @classmethod
    def pass_(cls) -> "CheckReport":
        return cls(True, ())

    @classmethod
    def fail(cls, *reasons: str) -> "CheckReport":
        return cls(False, tuple(reasons))


# ---------------------------------------------------------------------------
# T116：非凸 IR / 全 argmax / Pareto（inline re-derivation）
# ---------------------------------------------------------------------------


def _ir_inline(nego: MultiIssueNegotiation) -> FrozenSet[str]:
    ok = set()
    for aid in nego.agreements:
        if all(nego.utilities[p][aid] >= nego.reservations[p]
               for p in nego.reservations):
            ok.add(aid)
    return frozenset(ok)


def _objective_inline(nego: MultiIssueNegotiation, aid: str) -> Fraction:
    total = Fraction(0)
    for p in nego.weights:
        total += nego.weights[p] * nego.utilities[p][aid]
    return total


def _argmax_inline(nego: MultiIssueNegotiation) -> FrozenSet[str]:
    if not nego.agreements:
        return frozenset()
    scored = [(aid, _objective_inline(nego, aid)) for aid in nego.agreements]
    best = max(v for _aid, v in scored)
    return frozenset(aid for aid, v in scored if v == best)


def _dominates_inline(nego: MultiIssueNegotiation, s: str, t: str) -> bool:
    weak = strict = False
    for p in nego.utilities:
        us, ut = nego.utilities[p][s], nego.utilities[p][t]
        if us > ut:
            return False
        weak = True
        if us < ut:
            strict = True
    return weak and strict


def check_negotiation(nego: MultiIssueNegotiation,
                      reported_ir: Iterable[str],
                      reported_argmax: Iterable[str],
                      reported_pareto: Mapping[str, bool]) -> CheckReport:
    """Differential check of a negotiation solution: IR set, FULL argmax set
    (missing or extra maximizers both fail — §8.4 保留全 argmax)， and the
    per-agreement Pareto flags."""

    problems = []
    if _ir_inline(nego) != frozenset(reported_ir):
        problems.append("IR set mismatch")
    if _argmax_inline(nego) != frozenset(reported_argmax):
        problems.append("argmax set mismatch (not the FULL maximizer set)")
    for aid in nego.agreements:
        expected = not any(_dominates_inline(nego, aid, t)
                           for t in nego.agreements)
        if reported_pareto.get(aid) != expected:
            problems.append(f"Pareto flag mismatch at {aid}")
    if problems:
        return CheckReport.fail(*problems)
    return CheckReport.pass_()


def check_argmax_flag_forge(nego: MultiIssueNegotiation,
                            s: str, claimed_argmax: bool) -> CheckReport:
    """Rejection gate: a claimed argmax membership that contradicts the
    inline objective comparison is rejected (不冒称唯一/不漏argmax)."""

    truth = s in _argmax_inline(nego)
    if claimed_argmax == truth:
        return CheckReport.pass_()
    return CheckReport.fail(
        f"claimed argmax membership of {s!r}={claimed_argmax} contradicts "
        f"the enumerated maximizer set")


# ---------------------------------------------------------------------------
# T117：共享 θ 稳健 vs 矩形分解（inline re-derivation）
# ---------------------------------------------------------------------------


def _shared_inline(tree: ScenarioTree, theta: str) -> Fraction:
    return tree.r1[theta] + tree.r2[theta]


def check_robust_instance(tree: ScenarioTree,
                          reported_shared: Fraction,
                          reported_rect: Fraction) -> CheckReport:
    """Differential: shared-θ value = min over θ of the SAME-θ two-period
    total; rectangular = per-period minima summed.  A report claiming the
    rectangular stepwise value EQUALS the shared value on the canonical
    complementary instance (θ + (1−θ)) is rejected (§8.4：逐期各取最坏值会
    伪造)."""

    problems = []
    inline_shared = min(_shared_inline(tree, s) for s in tree.scenarios)
    inline_rect = (min(tree.r1[s] for s in tree.scenarios)
                   + min(tree.r2[s] for s in tree.scenarios))
    if inline_shared != reported_shared:
        problems.append("shared-θ value mismatch")
    if inline_rect != reported_rect:
        problems.append("rectangular value mismatch")
    totals = {_shared_inline(tree, s) for s in tree.scenarios}
    if len(totals) == 1 and len(tree.scenarios) >= 2 \
            and inline_rect != inline_shared \
            and reported_rect == reported_shared:
        problems.append(
            "rect==shared reported on an instance where stepwise min-max "
            "falsifies the shared total")
    if problems:
        return CheckReport.fail(*problems)
    return CheckReport.pass_()


def check_box_reach_claim(tree: ScenarioTree, pair: Tuple[Fraction, Fraction],
                          claimed_reachable: bool) -> CheckReport:
    """Rejection gate for the non-rectangle reading: reachability under the
    shared θ is re-derived from the scenario table; a pair admitted by the
    per-period box but absent from the reachable set must not be reported
    reachable."""

    reachable = frozenset((tree.r1[s], tree.r2[s]) for s in tree.scenarios)
    truth = pair in reachable
    if claimed_reachable == truth:
        return CheckReport.pass_()
    return CheckReport.fail(
        f"pair {pair} reachability claim {claimed_reachable} contradicts "
        "the shared-θ reachable set")


# ---------------------------------------------------------------------------
# T118：VOI 链 / Snell 全枚举 / 非单调补证（inline re-derivation）
# ---------------------------------------------------------------------------


def check_voi(problem: InfoAcquisition, reported_gross: Fraction,
              reported_net: Fraction) -> CheckReport:
    """Differential: with/without decision values recomputed inline; gross
    must be nonneg and net must equal gross minus the permission cost (§8.4
    净信息价值还减成本，可为负)."""

    problems = []
    without = max(
        sum((problem.prior[s] * problem.utils[c][s] for s in problem.states),
            Fraction(0))
        for c in problem.choices)
    with_info = sum(
        (problem.prior[s] * max(problem.utils[c][s] for c in problem.choices)
         for s in problem.states),
        Fraction(0))
    gross = with_info - without
    if gross < 0:
        problems.append("inline gross VOI is negative — model broken")
    if gross != reported_gross:
        problems.append("gross VOI mismatch")
    if reported_net != reported_gross - problem.cost:
        problems.append("net VOI is not gross minus permission cost")
    if reported_gross < 0:
        problems.append("reported a negative GROSS value as a pass")
    if problems:
        return CheckReport.fail(*problems)
    return CheckReport.pass_()


def _enumerate_stop_payoffs(g: Tuple[Fraction, ...],
                            c: Tuple[Fraction, ...]) -> Dict[int, Fraction]:
    """Every admissible stop (deadline forces T): payoff g[t] − Σ_{i<t} c[i]."""

    out: Dict[int, Fraction] = {}
    for t in range(len(g)):
        out[t] = g[t] - sum(c[:t], Fraction(0))
    return out


def check_snell_by_enumeration(g: Tuple[Fraction, ...],
                               c: Tuple[Fraction, ...],
                               reported_v0: Fraction,
                               reported_stop: int) -> CheckReport:
    """Snell bound re-derived by FULL ENUMERATION of admissible stopping
    rules (independent of the reference's backward induction): the reported
    V_0 must equal the enumerated maximum, the reported stop must achieve it,
    and every other admissible stop must pay at most V_0 (Lean
    stopPayoff_le_snell / snell_policy_achieves)."""

    if len(g) < 1 or len(c) != len(g) - 1:
        return CheckReport.fail("malformed horizon")
    problems = []
    payoffs = _enumerate_stop_payoffs(g, c)
    best = max(payoffs.values())
    if reported_v0 != best:
        problems.append("reported V_0 differs from the enumerated optimum")
    if reported_stop not in payoffs:
        problems.append("reported stop outside the finite horizon")
    elif payoffs[reported_stop] != reported_v0:
        problems.append("reported Snell policy does not achieve V_0")
    for t, payoff in payoffs.items():
        if payoff > reported_v0:
            problems.append(f"admissible stop at {t} beats the reported V_0")
    if problems:
        return CheckReport.fail(*problems)
    return CheckReport.pass_()


def check_nonmonotone_witness(after_first: Fraction,
                              after_second: Fraction) -> CheckReport:
    """The 补证 gate: the second (contradicting) piece of evidence must be
    allowed to LOWER the expected decision value — a report claiming the
    path values are monotone nondecreasing is rejected."""

    if after_second < after_first:
        return CheckReport.pass_()
    return CheckReport.fail(
        "reported values are nondecreasing — the non-monotone counterexample "
        "is not exercised")


# ---------------------------------------------------------------------------
# T119：同轨迹三投影（inline re-derivation）
# ---------------------------------------------------------------------------


def _causal_inline(trace: Trace) -> Fraction:
    total = Fraction(0)
    for a in trace:
        total += a.harm
    return total


def _liable_inline(trace: Trace) -> FrozenSet[str]:
    liable = set()
    for a in trace:
        if a.privileged is False and a.harm > 0:
            liable.add(a.actor)
    return frozenset(liable)


def _utility_inline(trace: Trace, actor: str) -> Fraction:
    total = Fraction(0)
    for a in trace:
        if a.actor == actor:
            total += a.gain
    return total


def check_trace_readings(trace: Trace, reported_causal: Fraction,
                         reported_liable: Iterable[str],
                         reported_utility: Mapping[str, Fraction]
                         ) -> CheckReport:
    """Differential of the three same-path projections."""

    problems = []
    if _causal_inline(trace) != reported_causal:
        problems.append("causal reading mismatch")
    if _liable_inline(trace) != frozenset(reported_liable):
        problems.append("liability projection mismatch")
    actors = {a.actor for a in trace}
    if set(reported_utility) != actors:
        problems.append("utility projection must value every actor")
    else:
        for actor in actors:
            if _utility_inline(trace, actor) != reported_utility[actor]:
                problems.append(f"utility mismatch for {actor}")
    if problems:
        return CheckReport.fail(*problems)
    return CheckReport.pass_()


def check_separation_gate(trace: Trace,
                          claimed_separated: bool) -> CheckReport:
    """The separation claim is only honest when a PRIVILEGED harmful act
    exists (caused harm without liability).  A separation claim on a trace
    where liability follows harm is rejected (投影分离要有构造性见证)."""

    privileged_harmful = [a for a in trace if a.privileged and a.harm > 0]
    causal_positive = _causal_inline(trace) > 0
    liable = _liable_inline(trace)
    truth = bool(privileged_harmful) and causal_positive and all(
        a.actor not in liable for a in privileged_harmful)
    if claimed_separated == truth:
        return CheckReport.pass_()
    return CheckReport.fail(
        f"separation claim {claimed_separated} contradicts the inline "
        f"projection analysis (privileged harmful acts: "
        f"{len(privileged_harmful)}, liable: {sorted(liable)})")


# ---------------------------------------------------------------------------
# T120：合规激励比较（inline re-derivation）
# ---------------------------------------------------------------------------


def _eu_inline(a: ComplianceAction) -> Fraction:
    return a.gain - a.p_exec * a.fine


def check_compliance(game: ComplianceGame,
                     reported: Mapping[str, object]) -> CheckReport:
    """Differential of the §8.5 comparison, plus the no-deletion gate: the
    violating side must still be IN the action space (不能删掉违规选项制造
    定理) and the dominance verdict must match the declared sanction and
    execution parameters."""

    problems = []
    if not any(not a.permitted for a in game.actions):
        problems.append("violating side deleted from the action space")
    permitted = [a for a in game.actions if a.permitted]
    violating = [a for a in game.actions if not a.permitted]
    if not permitted:
        problems.append("no permitted action to compare against")
        return CheckReport.fail(*problems)
    sup_p = max(_eu_inline(a) for a in permitted)
    sup_v = max(_eu_inline(a) for a in violating)
    if sup_p != reported.get("sup_permitted"):
        problems.append("sup over permitted mismatch")
    if sup_v != reported.get("sup_violating"):
        problems.append("sup over violating mismatch")
    truth = sup_p >= sup_v
    if reported.get("compliance_dominates") != truth:
        problems.append("dominance verdict contradicts the parameters")
    if problems:
        return CheckReport.fail(*problems)
    return CheckReport.pass_()


# ---------------------------------------------------------------------------
# T121：事件→观察→同一规则重新评价（inline re-derivation）
# ---------------------------------------------------------------------------


def _lookup_inline(obs: Mapping[str, Fraction], key: str) -> Fraction:
    if key in obs:
        return obs[key]
    return Fraction(0)


def check_backflow(obs: ObservationLayer, event: BehaviorEvent,
                   rule: ThresholdRule,
                   receipt: Mapping[str, object]) -> CheckReport:
    """Differential of the §9.1/§9.4 chain: observation update, same-rule
    re-evaluation verdicts, and the flip.  Gates: the receipt must NOT claim
    the rule was replaced (同一规则), the observation update must be exactly
    old+amount, and a misreported flip is rejected."""

    problems = []
    if receipt.get("rule_replaced") is True:
        problems.append("receipt claims the rule was replaced (§9.4 同一规则)")
    expected_after = dict(obs)
    expected_after[event.key] = _lookup_inline(obs, event.key) + event.amount
    if receipt.get("obs_after") != expected_after:
        problems.append("observation layer update mismatch")
    before = rule.threshold <= _lookup_inline(obs, rule.key)
    after = rule.threshold <= _lookup_inline(expected_after, rule.key)
    if receipt.get("verdict_before") != before:
        problems.append("verdict before mismatch")
    if receipt.get("verdict_after") != after:
        problems.append("verdict after mismatch")
    if receipt.get("flipped") != (before != after):
        problems.append("flip claim mismatch")
    if problems:
        return CheckReport.fail(*problems)
    return CheckReport.pass_()
