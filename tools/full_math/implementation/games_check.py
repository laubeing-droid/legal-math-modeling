"""Independent checker for the T112-T115 W4 games layer (J.7 discipline).

This module deliberately re-derives the layer's semantics inline instead of
importing the reference functions: the sentencing clip/composition gates, the
backward-induction recursion, the path-Bayes belief discipline, the sequential
best-response checks and the tail/threshold arithmetic are all re-implemented
here from the frozen carriers alone — different code paths (e.g. closed-form
geometric series instead of explicit summation, threshold algebra instead of
if-composition).  It shares only the immutable data classes of
``games_ref`` — never its functions — and never calls the evaluator.

Lean contract: JurisLean.Seams.UnifiedW4Games (T112-T115).
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Callable, Optional, Sequence, Tuple

from tools.full_math.implementation.games_ref import (
    BargainParams,
    Belief,
    BIResult,
    LineKind,
    NormDomain,
    Penalty,
    PenaltyKind,
    SentCert,
    SentencingLayer,
    SeqEqReport,
    SigGame,
    SigType,
)

Frac = Fraction


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
# Inline semantic re-derivations（与主实现零函数共享）
# ---------------------------------------------------------------------------


def _domain_holds(d: NormDomain) -> bool:
    return d.months_lo <= d.months_hi


def _in_domain(d: NormDomain, p: Penalty) -> bool:
    # §11.3.10 分型：fixed 走月区间，无期/死刑走许可位
    if p.kind == PenaltyKind.FIXED:
        months = p.months
        return d.months_lo <= months and months <= d.months_hi
    if p.kind == PenaltyKind.LIFE:
        return bool(d.allows_life)
    if p.kind == PenaltyKind.DEATH:
        return bool(d.allows_death)
    return False


def _clip(d: NormDomain, x: Frac) -> Frac:
    # 与主实现的 max/min 路径不同：if/else 投影
    if x <= d.months_lo:
        return d.months_lo
    if x >= d.months_hi:
        return d.months_hi
    return x


def _gate(a: SentCert, b: SentCert) -> bool:
    one_each = {a.line, b.line} == {LineKind.RESPONSIBILITY, LineKind.PREVENTION}
    return one_each and a.facts_id == b.facts_id


def _r1(p: BargainParams, y: Frac) -> Tuple[Frac, Frac]:
    if p.delta * y < 0:
        return (Frac(0), Frac(0))
    return (p.delta * y, p.delta * (p.cake - y))


def _b1(p: BargainParams) -> Frac:
    v1 = _r1(p, p.offers_y[0])[1]
    v2 = _r1(p, p.offers_y[1])[1]
    # 与主实现不同的写法：显式三分（> / = / <），平局取第一
    if v2 > v1:
        return p.offers_y[1]
    return p.offers_y[0]


def _cont(p: BargainParams) -> Tuple[Frac, Frac]:
    return _r1(p, _b1(p))


def _thr(p: BargainParams) -> Frac:
    return p.delta * _cont(p)[1]


def _acc0(p: BargainParams, x: Frac) -> bool:
    return x >= _thr(p)


def _r0(p: BargainParams, x: Frac) -> Tuple[Frac, Frac]:
    if _acc0(p, x):
        return (p.cake - x, x)
    return _cont(p)


def _a0(p: BargainParams) -> Frac:
    v1 = _r0(p, p.offers_x[0])[0]
    v2 = _r0(p, p.offers_x[1])[0]
    if v2 > v1:
        return p.offers_x[1]
    return p.offers_x[0]


def _outcome(p: BargainParams) -> Tuple[Frac, Frac]:
    return _r0(p, _a0(p))


def _posterior(game: SigGame, sS: Tuple[bool, bool],
               m: bool) -> Optional[Frac]:
    both = sS[0] == m and sS[1] == m
    only_s = sS[0] == m and sS[1] != m
    only_w = sS[1] == m and sS[0] != m
    if both:
        return game.prior
    if only_s:
        return Frac(1)
    if only_w:
        return Frac(0)
    return None


def _eu(game: SigGame, m: bool, mu: Frac, a: bool) -> Frac:
    s_pay, w_pay = game.pay(m, a)
    return mu * s_pay + (1 - mu) * w_pay


def _sender_val(game: SigGame, sR: Tuple[bool, bool], t: int, m: bool) -> Frac:
    return game.us(m, sR[t])[t]


# ---------------------------------------------------------------------------
# Public checks
# ---------------------------------------------------------------------------


def check_sentencing_layer(domain: NormDomain, responsibility: Frac,
                           adjustment: Frac, certs: Sequence[SentCert],
                           layer: SentencingLayer) -> CheckReport:
    """量刑双线差分：合成恒在域内（裁剪后）、域内合成不扭曲、同源/异源门
    逐对差分（T112：异源被拒；越界经验值只有裁剪一条路）."""

    problems = []
    if not _domain_holds(domain):
        problems.append("normative domain malformed")
    raw = responsibility + adjustment
    expected = _clip(domain, raw)
    if layer.composed_penalty.kind != PenaltyKind.FIXED:
        problems.append("composed penalty must be a fixed-term sentence")
    elif layer.composed_penalty.months != expected:
        problems.append("composition does not match the clip projection")
    if not _in_domain(domain, layer.composed_penalty):
        problems.append("composed penalty outside the normative domain")
    if layer.unclipped_in_domain != (expected == raw):
        problems.append("unclipped flag mismatch")
    expected_same = tuple((x.cert_id, y.cert_id) for x in certs
                          for y in certs if x.cert_id < y.cert_id and _gate(x, y))
    expected_foreign = tuple(
        (x.cert_id, y.cert_id) for x in certs for y in certs
        if x.cert_id < y.cert_id and x.line != y.line
        and x.facts_id != y.facts_id)
    if set(layer.same_source_pairs) != set(expected_same):
        problems.append("same-source pair set mismatch")
    if set(layer.foreign_pairs) != set(expected_foreign):
        problems.append("foreign-facts pair set mismatch")
    for c in certs:
        if c.line not in (LineKind.RESPONSIBILITY, LineKind.PREVENTION):
            problems.append(f"certificate {c.cert_id} carries unknown line")
    if problems:
        return CheckReport.fail(*problems)
    return CheckReport.pass_()


def check_bargain_result(p: BargainParams, res: BIResult) -> CheckReport:
    """后向归纳差分＋拒绝门：独立重算末轮选择/根选择/终局收益并逐项对照；
    篡改出价（bid rigging：选择的报价不是菜单收益最大化者）被拒；四节点
    单步偏离检查被独立复核."""

    problems = []
    if res.b1 != _b1(p):
        problems.append("round-1 proposer choice tampered (not payoff-maximal)")
    if res.a0 != _a0(p):
        problems.append("root proposer choice tampered (not payoff-maximal)")
    if res.outcome != _outcome(p):
        problems.append("backward-induction outcome mismatch")
    if res.r1_value != _cont(p):
        problems.append("round-1 continuation value mismatch")
    if res.b1 not in p.offers_y:
        problems.append("round-1 choice off menu")
    if res.a0 not in p.offers_x:
        problems.append("root choice off menu")
    # 单步偏离独立复核（与主实现的枚举路径不同：直接从闭式读数核差值）
    cont = _cont(p)
    for y in p.offers_y:
        if cont[1] < _r1(p, y)[1]:
            problems.append("round-1 one-step deviation profitable")
    for x in p.offers_x:
        if _outcome(p)[0] < _r0(p, x)[0]:
            problems.append("root one-step deviation profitable")
    if _acc0(p, _a0(p)):
        if not (_thr(p) <= _outcome(p)[1]):
            problems.append("root responder threshold violated on accept")
    else:
        if not (_a0(p) < _thr(p)):
            problems.append("root responder threshold violated on reject")
    # 末轮应答阈值独立复核：接受时 A 的收益非负（拒绝收益 0）；拒绝时 δ·y<0
    y_star = _b1(p)
    if p.delta * y_star >= 0:
        if not (_r1(p, y_star)[0] >= 0):
            problems.append("round-1 responder threshold violated on accept")
    else:
        if not (p.delta * y_star < 0):
            problems.append("round-1 responder threshold violated on reject")
    if problems:
        return CheckReport.fail(*problems)
    return CheckReport.pass_()


def check_beliefs_and_seq(game: SigGame, sS: Tuple[bool, bool],
                          sR: Tuple[bool, bool], mu_l: Belief, mu_h: Belief,
                          report: SeqEqReport) -> CheckReport:
    """信念与序贯检查差分：路径贝叶斯后验独立重算（不一致信念被拒）；离轨
    信念必须落支撑内（不任填 0/0）；接收者/发送者最优回应逐项复核."""

    problems = []
    for m, mu, name in ((True, mu_l, "L"), (False, mu_h, "H")):
        post = _posterior(game, sS, m)
        if post is None:
            if not (0 <= mu.mu_strong <= 1):
                problems.append(f"off-path belief at {name} outside support")
        elif mu.mu_strong != post:
            problems.append(f"on-path belief at {name} violates path Bayes")
    for m, mu, name in ((True, mu_l, "L"), (False, mu_h, "H")):
        chosen = sR[0] if m else sR[1]
        if _eu(game, m, mu.mu_strong, chosen) < _eu(game, m, mu.mu_strong,
                                                    not chosen):
            problems.append(f"receiver deviation profitable at {name}")
    for t, msg in ((SigType.STRONG, sS[0]), (SigType.WEAK, sS[1])):
        if _sender_val(game, sR, t, msg) < _sender_val(game, sR, t, not msg):
            problems.append(f"sender type {t} deviation profitable")
    if report.ok != (not report.reasons):
        problems.append("seq report internal flag inconsistent")
    expected_ok = all((report.consistent_l, report.consistent_h,
                       report.receiver_br_l, report.receiver_br_h,
                       report.sender_br_strong, report.sender_br_weak))
    if report.ok != expected_ok:
        problems.append("seq report components do not sum to its verdict")
    if problems:
        return CheckReport.fail(*problems)
    return CheckReport.pass_()


def check_tail_bound(delta: Frac, big_m: Frac, per_period: Frac,
                     big_n: int, k: int, claimed_lhs: Frac,
                     claimed_rhs: Frac, claimed_ok: bool) -> CheckReport:
    """尾界差分＋拒绝门：独立用闭式几何部分和（与主实现的逐项求和不同路径）
    重算 |Σ|·(1−δ) 与 M·δ^N；超界尾和（claimed_ok=True 而 lhs>rhs）被拒."""

    if not (0 <= delta < 1):
        return CheckReport.fail("discount outside [0, 1)")
    # 闭式：Σ_{t<k} δ^{N+t} = δ^N·(1−δ^k)/(1−δ)
    series = Frac(1) - delta ** k
    expected_sum = (delta ** big_n) * series / (1 - delta) * per_period
    expected_lhs = abs(expected_sum) * (1 - delta)
    expected_rhs = big_m * delta ** big_n
    problems = []
    if claimed_lhs != expected_lhs:
        problems.append("tail-sum lhs mismatch against closed-form series")
    if claimed_rhs != expected_rhs:
        problems.append("tail bound rhs mismatch")
    if claimed_ok != (claimed_lhs <= claimed_rhs):
        problems.append("over-bound tail sum reported acceptable")
    if problems:
        return CheckReport.fail(*problems)
    return CheckReport.pass_()


def check_threshold(r: Frac, t: Frac, p_pay: Frac, delta: Frac,
                    threshold: Frac, sustains: bool,
                    credible: bool) -> CheckReport:
    """可信惩罚阈值差分：δ* = (T−R)/(T−P) 闭式重算；T ≤ P 拒绝；维持判据与
    credibility 前置独立核验."""

    problems = []
    if not p_pay < t:
        return CheckReport.fail("threshold undefined when T ≤ P")
    expected = (t - r) / (t - p_pay)
    if threshold != expected:
        problems.append("threshold mismatch against (T-R)/(T-P)")
    expected_sustains = t + delta * p_pay / (1 - delta) <= r / (1 - delta)
    if sustains != expected_sustains:
        problems.append("sustain verdict mismatch")
    if sustains and not credible:
        problems.append("cooperation claimed with non-permitted punishment")
    if problems:
        return CheckReport.fail(*problems)
    return CheckReport.pass_()
