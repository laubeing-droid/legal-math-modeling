"""T116-T121 behavior batch reference (plan §8.4, §8.5, §9.1, §9.4).

K rows 2545-2550 (docs/spec/20261007-统一法律数学模型_附录K_全量目标落实表.md):
T116 多议题谈判 — §8.4：多议题非凸 IR 和 argmax，不假设凸/唯一；
T117 稳健行动   — §8.4：共享 θ 稳健情景树，非矩形反例 θ+(1−θ)；
T118 信息取得与停止 — §8.4,12.5：权限成本 VOI、有限期停时、非单调补证；
T119 行为评价   — §8.5：因果、法律责任、效用同轨迹不同投影；
T120 合规激励   — §8.5：合规激励比较含实际违规行动及制裁/执行；
T121 行为回流   — §9.1,9.4：行为实际事件→效力/观察→同一规则重新评价。

All arithmetic is Fraction (金额/概率禁浮点).  Every constructor is fail-fast
(TypeError on floats, ValueError on malformed parameters); the violation side
of the compliance game can never be deleted from the action space (§8.5:
不能删掉违规选项制造定理).

Lean contract: proofs/lean/juris_lean/JurisLean/Seams/UnifiedW4Behavior.lean
(namespace JurisLean.Seams.UnifiedW4Behavior).  Independent checker:
tools/full_math/implementation/behavior_check.py (shares only these frozen
carriers, re-implements every predicate inline, never calls these functions).
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Dict, FrozenSet, Mapping, Sequence, Tuple

F = Fraction


def _q(value: object, what: str) -> F:
    """Fail-fast rational coercion: ints and Fractions pass, floats die."""

    if isinstance(value, F):
        return value
    if isinstance(value, int) and not isinstance(value, bool):
        return F(value)
    raise TypeError(f"{what} must be a Fraction/int (no floats): {value!r}")


# ---------------------------------------------------------------------------
# T116 多议题谈判：非凸 IR 与全 argmax（§8.4）
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class MultiIssueNegotiation:
    """Multi-issue negotiation problem: a FINITE agreement set (the issue
    vectors themselves are opaque ids — the space is never assumed convex or
    a single component), per-party utilities, per-party reservation values
    (litigation outside options) and positive Pareto weights."""

    agreements: Tuple[str, ...]
    utilities: Mapping[str, Mapping[str, F]]   # party -> agreement -> u
    reservations: Mapping[str, F]              # party -> d_i
    weights: Mapping[str, F]                   # party -> w_i > 0

    def __post_init__(self) -> None:
        if not self.agreements:
            raise ValueError("agreement set must be nonempty")
        if len(set(self.agreements)) != len(self.agreements):
            raise ValueError("duplicate agreement id")
        parties = set(self.utilities)
        if parties != set(self.reservations) or parties != set(self.weights):
            raise ValueError("utility/reservation/weight party sets differ")
        if not parties:
            raise ValueError("at least one party required")
        for party in parties:
            _q(self.reservations[party], f"reservation[{party}]")
            w = _q(self.weights[party], f"weight[{party}]")
            if w <= 0:
                raise ValueError(f"Pareto weights must be positive: {party}")
            utils = self.utilities[party]
            if set(utils) != set(self.agreements):
                raise ValueError(f"utilities of {party} must cover every agreement")
            for aid in self.agreements:
                _q(utils[aid], f"utilities[{party}][{aid}]")


def weighted_sum(nego: MultiIssueNegotiation, aid: str) -> F:
    """∑_i w_i · u_i(s) — the positive-weight-sum objective (§8.4)."""

    return sum(
        (nego.weights[p] * nego.utilities[p][aid] for p in nego.utilities),
        F(0),
    )


def ir_set(nego: MultiIssueNegotiation) -> Tuple[str, ...]:
    """S_IR = {s ∈ S : u_i(s) ≥ d_i, ∀i} — defined directly; may be empty,
    multi-component or non-convex (§8.4: 不假设凸/唯一)."""

    return tuple(
        aid for aid in nego.agreements
        if all(nego.utilities[p][aid] >= nego.reservations[p]
               for p in nego.utilities)
    )


def argmax_set(nego: MultiIssueNegotiation) -> Tuple[str, ...]:
    """ALL weighted-sum maximizers over the feasible agreement set — the full
    argmax is kept; uniqueness is never claimed (§8.4: 非凸域保留全 argmax).
    口径与 Lean IsArgmaxW 一致：对整个可行集取 argmax（IR 是单独读出）."""

    if not nego.agreements:
        return ()
    best = max(weighted_sum(nego, aid) for aid in nego.agreements)
    return tuple(aid for aid in nego.agreements
                 if weighted_sum(nego, aid) == best)


def dominates(nego: MultiIssueNegotiation, s: str, t: str) -> bool:
    """t dominates s: every party weakly better and at least one strictly."""

    weak = all(nego.utilities[p][s] <= nego.utilities[p][t]
               for p in nego.utilities)
    strict = any(nego.utilities[p][s] < nego.utilities[p][t]
                 for p in nego.utilities)
    return weak and strict


def is_pareto(nego: MultiIssueNegotiation, s: str) -> bool:
    """Pareto point: feasible and undominated over the agreement set
    （§8.4 的偏序定义；口径与 Lean IsPareto 一致——对可行集，不先过 IR 门）."""

    if s not in nego.agreements:
        raise ValueError(f"{s!r} is not a declared agreement")
    return not any(dominates(nego, s, t) for t in nego.agreements)


def pareto_of_argmax(nego: MultiIssueNegotiation) -> bool:
    """The T116 flagship instance-check: every positive-weight-sum maximizer
    over the feasible set is a Pareto point (Lean wsum_max_is_pareto)."""

    return all(is_pareto(nego, s) for s in argmax_set(nego))


# ---------------------------------------------------------------------------
# T117 稳健行动：共享 θ 情景树，非矩形反例（§8.4, EXT08）
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ScenarioTree:
    """Two-period scenario tree over a finite scenario set Θ with the SAME
    θ threading both periods (r1(θ) then r2(θ); shared, never independent)."""

    scenarios: Tuple[str, ...]
    r1: Mapping[str, F]   # period-1 payoff under scenario θ
    r2: Mapping[str, F]   # period-2 payoff under the SAME θ

    def __post_init__(self) -> None:
        if not self.scenarios:
            raise ValueError("scenario set must be nonempty")
        for table, name in ((self.r1, "r1"), (self.r2, "r2")):
            if set(table) != set(self.scenarios):
                raise ValueError(f"{name} must value every scenario")
            for s in self.scenarios:
                _q(table[s], f"{name}[{s}]")


def eval_under_shared_theta(tree: ScenarioTree, theta: str) -> F:
    """evalUnder: the SAME θ is threaded to both period payoffs."""

    if theta not in tree.scenarios:
        raise ValueError(f"{theta!r} is not a declared scenario")
    return tree.r1[theta] + tree.r2[theta]


def robust_value(tree: ScenarioTree) -> F:
    """min_θ (r1(θ) + r2(θ)) — the shared-θ robust value (sup_π inf_θ E u)."""

    return min(eval_under_shared_theta(tree, s) for s in tree.scenarios)


def rectangular_value(tree: ScenarioTree) -> F:
    """min_θ r1 + min_θ r2 — the stepwise per-period worst-case sum; exact
    ONLY for rectangular independent uncertainty (§8.4)."""

    return (min(tree.r1[s] for s in tree.scenarios)
            + min(tree.r2[s] for s in tree.scenarios))


def shared_reachable_pairs(tree: ScenarioTree) -> FrozenSet[Tuple[F, F]]:
    """{(r1(θ), r2(θ))} — the reachable payoff pairs under the shared θ."""

    return frozenset((tree.r1[s], tree.r2[s]) for s in tree.scenarios)


def rectangular_box_contains(tree: ScenarioTree, pair: Tuple[F, F]) -> bool:
    """Is (x, y) inside the per-period rectangle [min r1, max r1] ×
    [min r2, max r2]?  The box may admit pairs no shared θ can reach."""

    _q(pair[0], "pair[0]")
    _q(pair[1], "pair[1]")
    lo1, hi1 = min(tree.r1[s] for s in tree.scenarios), max(
        tree.r1[s] for s in tree.scenarios)
    lo2, hi2 = min(tree.r2[s] for s in tree.scenarios), max(
        tree.r2[s] for s in tree.scenarios)
    return lo1 <= pair[0] <= hi1 and lo2 <= pair[1] <= hi2


def robust_action_ok(tree: ScenarioTree, threshold: F, chosen: str) -> bool:
    """Robust action check: the chosen scenario-branch meets the threshold in
    EVERY scenario (§8.4: 稳健行动在全部情景满足约束)."""

    _q(threshold, "threshold")
    if chosen not in tree.scenarios:
        raise ValueError(f"{chosen!r} is not a declared scenario")
    return all(
        threshold <= eval_under_shared_theta(tree, s) for s in tree.scenarios)


# ---------------------------------------------------------------------------
# T118 信息取得与停止：权限成本 VOI、有限期停时、非单调补证（§8.4,12.5）
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class InfoAcquisition:
    """Information problem: prior weights over states, utility of each choice
    per state, and the PERMISSION COST of acquiring the signal (§8.4 净信息
   价值还减成本，可为负; §12.5 权限成本在可选动作及同一状态内)."""

    states: Tuple[str, ...]
    choices: Tuple[str, ...]
    prior: Mapping[str, F]                # state -> weight (sums to 1)
    utils: Mapping[str, Mapping[str, F]]  # choice -> state -> u
    cost: F                               # permission/acquisition cost

    def __post_init__(self) -> None:
        if not self.states or not self.choices:
            raise ValueError("states and choices must be nonempty")
        if set(self.prior) != set(self.states):
            raise ValueError("prior must value every state")
        if set(self.utils) != set(self.choices):
            raise ValueError("utils must value every choice")
        total = sum((_q(self.prior[s], f"prior[{s}]") for s in self.states), F(0))
        if total != 1:
            raise ValueError("prior weights must sum to 1")
        for c in self.choices:
            if set(self.utils[c]) != set(self.states):
                raise ValueError(f"utils[{c}] must value every state")
            for s in self.states:
                _q(self.utils[c][s], f"utils[{c}][{s}]")
        if _q(self.cost, "cost") < 0:
            raise ValueError("permission cost must be nonnegative")


def decision_value_without_info(problem: InfoAcquisition) -> F:
    """max_k ∑_s prior_s · u_k(s)."""

    return max(
        sum((problem.prior[s] * problem.utils[c][s] for s in problem.states),
            F(0))
        for c in problem.choices)


def decision_value_with_info(problem: InfoAcquisition) -> F:
    """∑_s prior_s · max_k u_k(s) — the signal is free to ignore, so the
    adaptive best per cell (§8.4 gross VOI ≥ 0 reading)."""

    return sum(
        (problem.prior[s] * max(problem.utils[c][s] for c in problem.choices)
         for s in problem.states),
        F(0))


def voi_gross_and_net(problem: InfoAcquisition) -> Tuple[F, F]:
    """(gross, net): gross = with − without ≥ 0; net = gross − cost — the
    permission cost is subtracted and can push the NET value negative."""

    with_info = decision_value_with_info(problem)
    without = decision_value_without_info(problem)
    gross = with_info - without
    if gross < 0:
        raise AssertionError("gross VOI must be nonneg (§8.4)")
    return gross, gross - problem.cost


def snell_values(g: Sequence[F], c: Sequence[F]) -> Tuple[F, ...]:
    """Finite-horizon Snell recursion (deterministic ℚ reading of §8.4):
    V_T = g_T; V_t = max(g_t, V_{t+1} − c_t).  `g` has length T+1 (terminal
    deadline included), `c` has length T (continuation cost per step)."""

    if len(g) < 1 or len(c) != len(g) - 1:
        raise ValueError("g needs T+1 entries and c exactly T entries")
    gq = [_q(v, f"g[{i}]") for i, v in enumerate(g)]
    cq = [_q(v, f"c[{i}]") for i, v in enumerate(c)]
    values = [F(0)] * len(gq)
    values[-1] = gq[-1]
    for t in range(len(gq) - 2, -1, -1):
        cont = values[t + 1] - cq[t]
        values[t] = gq[t] if gq[t] >= cont else cont
    return tuple(values)


def stopping_payoff(g: Sequence[F], c: Sequence[F],
                    stop_at: int) -> F:
    """Payoff of the admissible stopping rule that stops at `stop_at`
    (deadline forces stop at T): g[stop_at] minus each continuation cost
    before it."""

    if not 0 <= stop_at < len(g):
        raise ValueError("stop index outside the finite horizon")
    gq = [_q(v, f"g[{i}]") for i, v in enumerate(g)]
    cq = [_q(v, f"c[{i}]") for i, v in enumerate(c)]
    return gq[stop_at] - sum(cq[:stop_at], F(0))


def snell_optimality_report(g: Sequence[F], c: Sequence[F]) -> Dict[str, object]:
    """Backward-induction receipt: the Snell value vector, the greedy policy
    (stop at t iff g_t ≥ V_{t+1} − c_t), its payoff, and the bound that EVERY
    admissible stop pays at most V_0 (Lean stopPayoff_le_snell)."""

    values = snell_values(g, c)
    horizon = len(values) - 1
    cq = [_q(v, f"c[{i}]") for i, v in enumerate(c)]
    gq = [_q(v, f"g[{i}]") for i, v in enumerate(g)]
    stop_t = horizon
    for t in range(horizon):
        cont = values[t + 1] - cq[t]
        if gq[t] >= cont:
            stop_t = t
            break
    policy_payoff = stopping_payoff(g, c, stop_t)
    if policy_payoff != values[0]:
        raise AssertionError("Snell policy must achieve V_0 (existence)")
    others = {t: stopping_payoff(g, c, t) for t in range(len(gq))}
    worst_violation = max(others.values())
    if worst_violation > values[0]:
        raise AssertionError("every admissible stop must pay ≤ V_0 (optimality)")
    return {
        "values": values,
        "stop_at": stop_t,
        "policy_payoff": policy_payoff,
        "all_payoffs": others,
        "v0": values[0],
    }


def nonmonotone_evidence_witness() -> Dict[str, F]:
    """合成非单调补证反例：decision value 9/10 after the first piece of
    evidence; after the second (contradicting) piece the belief in the first
    state falls to 1/5, leaving a decision value of only 4/5 — acquiring
    evidence can LOWER the expected decision value along a path (§8.4,12.5)."""

    return {
        "after_first": dec_value(F(9, 10)),
        "after_second": dec_value(F(1, 5)),
    }


def dec_value(q: F) -> F:
    """max(q, 1−q): the decision value of a two-state belief (q, 1−q) with
    the two matching actions."""

    q = _q(q, "q")
    other = 1 - q
    return q if q >= other else other


# ---------------------------------------------------------------------------
# T119 行为评价：因果/法律责任/效用同轨迹三投影（§8.5）
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Act:
    """One act event: actor, privilege mark (合法性层), physical harm caused
    (因果层), private net gain (效用层) — four fields of the SAME event, so
    the three readings travel the same path (§8.5 同路径投影)."""

    actor: str
    privileged: bool
    harm: F
    gain: F

    def __post_init__(self) -> None:
        if _q(self.harm, "harm") < 0:
            raise ValueError("harm is a nonneg physical quantity")
        _q(self.gain, "gain")


Trace = Tuple[Act, ...]


def causal_reading(trace: Trace) -> F:
    """Projection 1 (因果解释): total physical harm along the trace."""

    return sum((a.harm for a in trace), F(0))


def liable_actors(trace: Trace) -> FrozenSet[str]:
    """Projection 2 (法律责任归属): an actor is liable iff they performed a
    non-privileged harmful act — the legality mark defeats causal liability
    (privileged defense causes harm without liability)."""

    return frozenset(
        a.actor for a in trace
        if not a.privileged and a.harm > 0)


def utility_reading(trace: Trace, actor: str) -> F:
    """Projection 3 (效用度量): the actor's private net gain along the trace."""

    return sum((a.gain for a in trace if a.actor == actor), F(0))


def projection_separation_witness() -> Dict[str, object]:
    """同轨迹不同投影：one privileged-defense act — causal reading 5 > 0,
    actor 7 NOT liable, utility reading 0 ≠ 5 (Lean projection_separation)."""

    trace: Trace = (Act("7", True, F(5), F(0)),)
    return {
        "trace": trace,
        "causal": causal_reading(trace),
        "liable": liable_actors(trace),
        "utility7": utility_reading(trace, "7"),
    }


# ---------------------------------------------------------------------------
# T120 合规激励：含实际违规行动及制裁/执行的比较（§8.5）
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ComplianceAction:
    """One action of the PHYSICAL action space (违规/违法行动包含在内)：legality
    mark, gross gain, sanction fine F, execution probability p (§8.5)."""

    aid: str
    permitted: bool
    gain: F
    fine: F
    p_exec: F

    def __post_init__(self) -> None:
        _q(self.gain, "gain")
        _q(self.fine, "fine")
        p = _q(self.p_exec, "p_exec")
        if not 0 <= p <= 1:
            raise ValueError(f"execution probability out of [0,1]: {self.aid}")
        if self.fine < 0:
            raise ValueError(f"sanction must be nonnegative: {self.aid}")


@dataclass(frozen=True)
class ComplianceGame:
    """The finite PHYSICAL action space WITH its violating actions.  §8.5:
    合规最优的准确命题是 sup_{a∈Permitted} Eu ≥ sup_{a∈Phys\\Permitted} Eu；
    罚则修改通过金额、执行概率影响两侧，不能删掉违规选项制造定理——构造器
    fail-fast：违规行动集不允许为空."""

    actions: Tuple[ComplianceAction, ...]

    def __post_init__(self) -> None:
        if not self.actions:
            raise ValueError("action space must be nonempty")
        ids = [a.aid for a in self.actions]
        if len(set(ids)) != len(ids):
            raise ValueError("duplicate action id")
        if not any(not a.permitted for a in self.actions):
            raise ValueError(
                "the violating side of the action space was deleted — "
                "§8.5 forbids manufacturing the dominance theorem by "
                "removing the violation option")


def expected_utility(a: ComplianceAction) -> F:
    """Eu(a) = gain − p·F."""

    return a.gain - a.p_exec * a.fine


def compliance_report(game: ComplianceGame) -> Dict[str, object]:
    """sup over permitted vs sup over violating (both sides live) + the
    dominance verdict under the declared sanction/execution parameters."""

    permitted = [a for a in game.actions if a.permitted]
    violating = [a for a in game.actions if not a.permitted]
    sup_permitted = max(expected_utility(a) for a in permitted)
    sup_violating = max(expected_utility(a) for a in violating)
    return {
        "sup_permitted": sup_permitted,
        "sup_violating": sup_violating,
        "compliance_dominates": sup_permitted >= sup_violating,
        "deterrence_gap": sup_permitted - sup_violating,
    }


# ---------------------------------------------------------------------------
# T121 行为回流：事件→观察→同一规则重新评价（§9.1,9.4）
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class BehaviorEvent:
    """An actual behavior event (a may be unlawful): object key, amount,
    normative-backflow authority bit (§9.1 事件带实际行为人与效力时点)."""

    key: str
    amount: F
    authorized: bool

    def __post_init__(self) -> None:
        if _q(self.amount, "amount") < 0:
            raise ValueError("event amount is nonnegative")


ObservationLayer = Dict[str, F]


def apply_event_obs(obs: ObservationLayer,
                    event: BehaviorEvent) -> ObservationLayer:
    """The event updates ONLY the visible observation layer (§9.1 Step 3);
    no evaluation conclusion is written here."""

    return {**obs, event.key: obs.get(event.key, F(0)) + event.amount}


@dataclass(frozen=True)
class ThresholdRule:
    """The SAME rule used before and after the event (§9.4: 同一规则重新
    评价；LegalDerives 只读 V 与 Γ)."""

    key: str
    threshold: F

    def __post_init__(self) -> None:
        _q(self.threshold, "threshold")


def rule_eval(rule: ThresholdRule, obs: ObservationLayer) -> bool:
    """Evaluation reads only the observation layer."""

    return rule.threshold <= obs.get(rule.key, F(0))


def backflow_chain(obs: ObservationLayer, event: BehaviorEvent,
                   rule: ThresholdRule) -> Dict[str, object]:
    """The §9.1/§9.4 chain receipt: observation before/after, the SAME rule's
    verdict before/after, and whether the event flipped it (事件改变观察、
    观察改变规则评价结论).  A behavior event never replaces the RULE — norm
    changes are separate authorized events (§9.4 规范回流必须是有权限、有程序、
    有生效条件的事件), so the authority bit rides along as recorded
    provenance only."""

    after = apply_event_obs(obs, event)
    before_verdict = rule_eval(rule, obs)
    after_verdict = rule_eval(rule, after)
    return {
        "obs_before": dict(obs),
        "obs_after": after,
        "verdict_before": before_verdict,
        "verdict_after": after_verdict,
        "flipped": before_verdict != after_verdict,
        "rule_replaced": False,
        "event_authorized": event.authorized,
    }


def backflow_witness() -> Dict[str, object]:
    """见证：obs (k↦5), event (k, +6, authorized), rule (k, ≥10) — the same
    rule flips false→true (Lean backflow_chain_witness)."""

    return backflow_chain({"k": F(5)}, BehaviorEvent("k", F(6), True),
                          ThresholdRule("k", F(10)))
