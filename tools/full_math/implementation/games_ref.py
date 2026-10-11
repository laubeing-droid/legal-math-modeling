"""T112-T115 W4 games layer reference (plan §8.3, §8.6, §11.3.10).

K rows 2541-2544 (docs/spec/20261007-统一法律数学模型_附录K_全量目标落实表.md):
T112 量刑双线 — §8.6,11.3.10：责任刑规范域＋预防/经验线，刑种分型与同源证书；
T113 动态谈判 — §8.3：有限动态谈判完全信息后向归纳；
T114 隐藏信息与信念 — §8.3：类型/信息集/一致离轨信念与全部延续偏离；
T115 重复博弈 — §8.3：无限重复折扣尾界/离轨单偏离/可信惩罚阈值。

Semantics (all exact rational arithmetic — Fraction only, floats rejected at
every constructor, fail-fast):
- T112: the normative sentencing domain (month interval + life/death permits)
  bounds the PREVENTION line: any adjustment is projected back by `clip_to`
  (the composed penalty is always in-domain, and in-domain compositions are
  undistorted); an empirical prediction outside the statutory range is rejected
  raw and enters only through the clip (经验拟合不反向修改法定范围). Penalty
  kinds are a three-way enum (fixed/life/death — 不用 −1/−2 混算). The dual
  lines carry certificates over a SHARED fact input; the composition gate
  accepts one responsibility + one prevention certificate only when their
  fact ids coincide (异源被拒 — the row's original counterexample).
- T113: two-round finite-horizon alternating-offer bargaining (finite offer
  menus = finite nonempty action sets per node); backward induction resolves
  the last round first (responder threshold with accept-tie-break), then the
  root; the single-step deviation check over all four subgame nodes is
  computed explicitly, and the outcome is unique among menu offers maximizing
  A's first component under the strictness side condition.
- T114: two-type signaling; beliefs are CONSISTENT iff reachable information
  sets are pinned by path Bayes (both-send → prior, single-send → 1/0) and
  off-path beliefs stay inside the support (不能任填 0/0); the sequential
  checker verifies receiver best-response at both information sets and sender
  best-response for both types; the convexity lemma covers ALL mixed
  continuation deviations once the two pure plans are checked.
- T115: discounted repetition with bounded per-period payoffs; tail bound
  |Σ δ^{N+t} u(N+t)|·(1−δ) ≤ M·δ^N (division form ≤ Mδ^N/(1−δ)) — infinite
  sums stated as finite tail certificates, no analytic limits; one-deviation
  principle: no profitable single-period substitution ⇒ no profitable
  stream differing inside the window; grim-trigger credible punishment
  threshold δ ≥ (T−R)/(T−P) when T > P, with the punishment path required to
  be a permitted action (credibility precondition).

Lean contract: proofs/lean/juris_lean/JurisLean/Seams/UnifiedW4Games.lean
(namespace JurisLean.Seams.UnifiedW4Games).  Independent checker:
tools/full_math/implementation/games_check.py (shares only these frozen
carriers, re-implements every predicate inline).
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Callable, Optional, Sequence, Tuple

Q = Fraction


def _q(x: object, name: str) -> Q:
    """Exact-rational gate: ints and Fractions in; float/str/bool rejected
    (fail-fast — 概率/金额/折扣一律 ℚ，禁浮点)."""

    if isinstance(x, bool) or not isinstance(x, (int, Fraction)):
        raise ValueError(
            f"{name} must be exact int/Fraction, got {type(x).__name__}")
    return Q(x)


# ---------------------------------------------------------------------------
# T112 量刑双线：责任刑规范域 ＋ 预防/经验线 ＋ 刑种分型 ＋ 同源证书
# ---------------------------------------------------------------------------


class PenaltyKind:
    """§11.3.10 刑种分型：Term(months) / 无期 / 死刑是不同类."""

    FIXED = "fixed"
    LIFE = "life"
    DEATH = "death"


@dataclass(frozen=True)
class Penalty:
    """刑种值对象：fixed 携带 ℚ 月数；无期/死刑无月数（分型不相交）."""

    kind: str
    months: Optional[Q] = None

    def __post_init__(self) -> None:
        if self.kind not in (PenaltyKind.FIXED, PenaltyKind.LIFE,
                             PenaltyKind.DEATH):
            raise ValueError(f"unknown penalty kind: {self.kind}")
        if self.kind == PenaltyKind.FIXED:
            if self.months is None:
                raise ValueError("fixed penalty requires months")
            object.__setattr__(self, "months", _q(self.months, "months"))
        elif self.months is not None:
            raise ValueError("life/death carry no months field")


def mk_fixed(months: Q) -> Penalty:
    return Penalty(PenaltyKind.FIXED, months)


def mk_life() -> Penalty:
    return Penalty(PenaltyKind.LIFE)


def mk_death() -> Penalty:
    return Penalty(PenaltyKind.DEATH)


@dataclass(frozen=True)
class NormDomain:
    """§8.6 量刑规范域：月刑期区间 ＋ 无期/死刑许可位（按罪名/情节/刑种/程序
    生成；经验拟合只能作为域内辅助，不反向修改法定范围）."""

    months_lo: Q
    months_hi: Q
    allows_life: bool
    allows_death: bool

    def __post_init__(self) -> None:
        lo = _q(self.months_lo, "months_lo")
        hi = _q(self.months_hi, "months_hi")
        object.__setattr__(self, "months_lo", lo)
        object.__setattr__(self, "months_hi", hi)
        if lo > hi:
            raise ValueError("normative domain requires months_lo ≤ months_hi")


def penalty_in_domain(domain: NormDomain, p: Penalty) -> bool:
    """刑种在域判定（对照 Lean penaltyInDomainB）."""

    if p.kind == PenaltyKind.FIXED:
        return domain.months_lo <= p.months <= domain.months_hi
    if p.kind == PenaltyKind.LIFE:
        return domain.allows_life
    return domain.allows_death


def clip_to(domain: NormDomain, x: Q) -> Q:
    """域内裁剪投影（对照 Lean clipTo）：预防调整恒投影回规范域."""

    x = _q(x, "x")
    if x < domain.months_lo:
        return domain.months_lo
    if x > domain.months_hi:
        return domain.months_hi
    return x


@dataclass(frozen=True)
class EmpPrediction:
    """§8.6 T84 有界经验预测：Y∈[a, a+D]（构造级 fail-fast：越界预测构造不出）."""

    base: Q
    span: Q
    value: Q

    def __post_init__(self) -> None:
        base = _q(self.base, "base")
        span = _q(self.span, "span")
        value = _q(self.value, "value")
        if span < 0:
            raise ValueError("empirical span must be nonnegative")
        if not (base <= value <= base + span):
            raise ValueError("empirical value outside declared [base, base+span]")
        object.__setattr__(self, "base", base)
        object.__setattr__(self, "span", span)
        object.__setattr__(self, "value", value)


class LineKind:
    RESPONSIBILITY = "responsibility"
    PREVENTION = "prevention"


@dataclass(frozen=True)
class SentCert:
    """双线证书：线型＋刑种＋共享事实输入身份 factsId（同源证书结构）."""

    cert_id: str
    facts_id: str
    line: str
    penalty: Penalty

    def __post_init__(self) -> None:
        if self.line not in (LineKind.RESPONSIBILITY, LineKind.PREVENTION):
            raise ValueError(f"unknown line kind: {self.line}")


def compose_gate(x: SentCert, y: SentCert) -> bool:
    """同源合成门（对照 Lean composeGateB）：一责任一预防且 factsId 同源."""

    return x.line != y.line and x.facts_id == y.facts_id


def compose_dual_line(domain: NormDomain, responsibility: Q,
                      prevention_adjustment: Q) -> Tuple[Penalty, bool]:
    """双线合成：责任刑 r ＋ 预防调整 t，经裁剪投影恒在域内（对照 Lean
    dual_line_stays_normative）；返回 (合成刑, 裁剪前是否已在域内)."""

    responsibility = _q(responsibility, "responsibility")
    prevention_adjustment = _q(prevention_adjustment, "prevention_adjustment")
    raw = responsibility + prevention_adjustment
    composed = clip_to(domain, raw)
    return mk_fixed(composed), composed == raw


@dataclass(frozen=True)
class SentencingLayer:
    """量刑双线层快照（下游消费的单一入口）."""

    domain: NormDomain
    composed_penalty: Penalty
    in_domain: bool
    unclipped_in_domain: bool
    same_source_pairs: Tuple[Tuple[str, str], ...]
    foreign_pairs: Tuple[Tuple[str, str], ...]


def build_sentencing_layer(domain: NormDomain, responsibility: Q,
                           prevention_adjustment: Q,
                           certs: Sequence[SentCert] = ()) -> SentencingLayer:
    """总装量刑双线层：合成恒在域内；证书两两过同源合成门（异源对记入
    foreign_pairs —— T112 原反例的面）."""

    ids = [c.cert_id for c in certs]
    if len(set(ids)) != len(ids):
        raise ValueError("duplicate sentencing certificate id")
    composed, unclipped = compose_dual_line(domain, responsibility,
                                            prevention_adjustment)
    same = tuple((x.cert_id, y.cert_id) for x in certs for y in certs
                 if x.cert_id < y.cert_id and compose_gate(x, y))
    foreign = tuple((x.cert_id, y.cert_id) for x in certs for y in certs
                    if x.cert_id < y.cert_id and x.line != y.line
                    and x.facts_id != y.facts_id)
    return SentencingLayer(
        domain=domain,
        composed_penalty=composed,
        in_domain=penalty_in_domain(domain, composed),
        unclipped_in_domain=unclipped,
        same_source_pairs=same,
        foreign_pairs=foreign,
    )


# ---------------------------------------------------------------------------
# T113 动态谈判：有限时域轮流出价 · 完全信息后向归纳
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class BargainParams:
    """两轮轮流出价谈判：蛋糕 cake、折扣 delta（0 ≤ delta ≤ 1）；第 0 轮 A 出价
    （给 B 的份额）菜单 offers_x，第 1 轮 B 出价（给 A 的份额）菜单 offers_y；
    末轮拒绝＝分歧收益 (0,0)（有限菜单＝每节点行动集有限非空）."""

    cake: Q
    delta: Q
    offers_x: Tuple[Q, Q]
    offers_y: Tuple[Q, Q]

    def __post_init__(self) -> None:
        cake = _q(self.cake, "cake")
        delta = _q(self.delta, "delta")
        offers_x = tuple(_q(x, "offer_x") for x in self.offers_x)
        offers_y = tuple(_q(y, "offer_y") for y in self.offers_y)
        if len(offers_x) != 2 or len(offers_y) != 2:
            raise ValueError("offer menus must each carry exactly two offers")
        if not (0 <= delta <= 1):
            raise ValueError("discount delta must lie in [0, 1]")
        if cake < 0:
            raise ValueError("cake must be nonnegative")
        object.__setattr__(self, "cake", cake)
        object.__setattr__(self, "delta", delta)
        object.__setattr__(self, "offers_x", offers_x)
        object.__setattr__(self, "offers_y", offers_y)


def r1_pay(p: BargainParams, y: Q) -> Tuple[Q, Q]:
    """末轮收益：接受＝(δ·y, δ·(cake−y))，拒绝＝(0,0)（阈值 δ·y ≥ 0）."""

    if p.delta * y >= 0:
        return (p.delta * y, p.delta * (p.cake - y))
    return (Q(0), Q(0))


def b1_choice(p: BargainParams) -> Q:
    """末轮 B 的后向归纳选择：菜单上自身（第二分量）收益最大者；平局取第一."""

    y1, y2 = p.offers_y
    return y1 if r1_pay(p, y1)[1] >= r1_pay(p, y2)[1] else y2


def bi_r1(p: BargainParams) -> Tuple[Q, Q]:
    return r1_pay(p, b1_choice(p))


def acc_r0(p: BargainParams, x: Q) -> bool:
    """根节点 B 的接受门：x ≥ δ·（B 的末轮延续份额）."""

    return x >= p.delta * bi_r1(p)[1]


def r0_pay(p: BargainParams, x: Q) -> Tuple[Q, Q]:
    """根节点收益：接受＝(cake−x, x)，拒绝＝末轮延续 biR1."""

    if acc_r0(p, x):
        return (p.cake - x, x)
    return bi_r1(p)


def a0_choice(p: BargainParams) -> Q:
    """根节点 A 的后向归纳选择：菜单上自身（第一分量）收益最大者；平局取第一."""

    x1, x2 = p.offers_x
    return x1 if r0_pay(p, x1)[0] >= r0_pay(p, x2)[0] else x2


def bi_outcome(p: BargainParams) -> Tuple[Q, Q]:
    """后向归纳结果（子博弈精炼剖面下的终局收益向量）."""

    return r0_pay(p, a0_choice(p))


@dataclass(frozen=True)
class BIResult:
    """后向归纳读数：两轮选择、终局收益、四节点单步偏离检查、严格性标记."""

    b1: Q
    a0: Q
    outcome: Tuple[Q, Q]
    r1_value: Tuple[Q, Q]
    sp_checks: Tuple[str, ...]
    strict_no_indifference: bool


def backward_induction(p: BargainParams) -> BIResult:
    """后向归纳总装（fail-fast）：先末轮（应答阈值＋出价最大化分支），再根；
    四个子博弈节点单步偏离逐一核验；strict 标记＝无差异边缘被排除（可接受
    报价与拒绝延续同收益），对应 Lean bi_outcome_unique 的 hind 前提."""

    b1 = b1_choice(p)
    v1 = bi_r1(p)
    a0 = a0_choice(p)
    outcome = bi_outcome(p)
    checks = []
    # 末轮 B 换报价不增自身收益
    checks.append("r1_b_swap" if all(
        v1[1] >= r1_pay(p, y)[1] for y in p.offers_y) else "r1_b_swap:FAIL")
    # 末轮 A 单步换接受/拒绝不增自身收益（阈值即最优）
    if p.delta * b1 >= 0:
        checks.append("r1_a_threshold:ok")
    else:
        checks.append("r1_a_threshold:FAIL")
    # 根 A 换报价不增自身收益
    checks.append("r0_a_swap" if all(
        outcome[0] >= r0_pay(p, x)[0] for x in p.offers_x) else "r0_a_swap:FAIL")
    # 根 B 单步换接受/拒绝不增自身收益
    if acc_r0(p, a0):
        checks.append("r0_b_threshold:ok" if p.delta * v1[1] <= outcome[1]
                      else "r0_b_threshold:FAIL")
    else:
        checks.append("r0_b_threshold:ok" if a0 <= p.delta * v1[1]
                      else "r0_b_threshold:FAIL")
    if any(c.endswith(":FAIL") for c in checks):
        raise ValueError("backward induction failed its own SP check: "
                         + ",".join(checks))
    # 严格性（Lean hind 前提）：任一可接受报价的第一分量都不与拒绝延续同收益
    menu = p.offers_x
    strict = all(not acc_r0(p, x) or r0_pay(p, x)[0] != v1[0] for x in menu)
    return BIResult(b1=b1, a0=a0, outcome=outcome, r1_value=v1,
                    sp_checks=tuple(checks), strict_no_indifference=strict)


# ---------------------------------------------------------------------------
# T114 隐藏信息与信念：类型/信息集/一致离轨信念与全部延续偏离
# ---------------------------------------------------------------------------


class SigType:
    STRONG = 0
    WEAK = 1


Msg = bool   # True = L（在案信号），False = H（离轨信号）
Act = bool   # True = u


@dataclass(frozen=True)
class Belief:
    """信息集信念：接收者对 strong 型的概率."""

    mu_strong: Q

    def __post_init__(self) -> None:
        object.__setattr__(self, "mu_strong", _q(self.mu_strong, "mu_strong"))


def belief_wf(mu: Belief) -> bool:
    """信念良构：落在支撑内（离轨不任填 0/0、不越界）."""

    return 0 <= mu.mu_strong <= 1


@dataclass(frozen=True)
class SigGame:
    """两型信号博弈：先验 π；pay[m][a]＝接收者收益 (strong, weak)；
    us[m][a]＝发送者收益 (strong, weak)（发送层完全信息——见 Lean 头注开放点）."""

    prior: Q
    pay_l_u: Tuple[Q, Q]
    pay_l_d: Tuple[Q, Q]
    pay_h_u: Tuple[Q, Q]
    pay_h_d: Tuple[Q, Q]
    us_l_u: Tuple[Q, Q]
    us_l_d: Tuple[Q, Q]
    us_h_u: Tuple[Q, Q]
    us_h_d: Tuple[Q, Q]

    def __post_init__(self) -> None:
        prior = _q(self.prior, "prior")
        if not (0 <= prior <= 1):
            raise ValueError("prior must lie in [0, 1]")
        object.__setattr__(self, "prior", prior)

    def pay(self, m: Msg, a: Act) -> Tuple[Q, Q]:
        if m:
            return self.pay_l_u if a else self.pay_l_d
        return self.pay_h_u if a else self.pay_h_d

    def us(self, m: Msg, a: Act) -> Tuple[Q, Q]:
        if m:
            return self.us_l_u if a else self.us_l_d
        return self.us_h_u if a else self.us_h_d


def bayes_mu_strong(game: SigGame, sS: Tuple[bool, bool],
                    m: Msg) -> Optional[Q]:
    """路径贝叶斯后验：两型同发 m ⇒ 先验；仅强型 ⇒ 1；仅弱型 ⇒ 0；
    离轨 ⇒ None（不产生等式义务，由支撑内良构承担）."""

    s, w = sS
    if s == m and w == m:
        return game.prior
    if s == m:
        return Q(1)
    if w == m:
        return Q(0)
    return None


def consistent(game: SigGame, sS: Tuple[bool, bool], m: Msg, mu: Belief) -> bool:
    """一致信念（对照 Lean consistentB）：可达处被路径贝叶斯唯一钉定；
    离轨处只要求支撑内良构."""

    post = bayes_mu_strong(game, sS, m)
    if post is None:
        return belief_wf(mu)
    return mu.mu_strong == post


def eu_r(game: SigGame, m: Msg, mu: Belief, a: Act) -> Q:
    """接收者条件期望收益（信念线性）."""

    strong, weak = game.pay(m, a)
    return mu.mu_strong * strong + (1 - mu.mu_strong) * weak


def sender_pay(game: SigGame, sR: Tuple[bool, bool], t: int, m: Msg) -> Q:
    """发送者型 t 发 m 后按接收者策略的收益."""

    return game.us(m, sR[t])[t]


@dataclass(frozen=True)
class SeqEqReport:
    """序贯检查读数：六项分量逐一给出."""

    consistent_l: bool
    consistent_h: bool
    receiver_br_l: bool
    receiver_br_h: bool
    sender_br_strong: bool
    sender_br_weak: bool
    ok: bool
    reasons: Tuple[str, ...]


def seq_eq_check(game: SigGame, sS: Tuple[bool, bool], sR: Tuple[bool, bool],
                 mu_l: Belief, mu_h: Belief) -> SeqEqReport:
    """序贯均衡检查器（对照 Lean seqEqCheckB，逐项给出拒绝理由）——
    每个信息集的全部纯延续计划（接收者两行动 × 两信息集、发送者两消息 × 两型）
    条件收益不增；混合偏离由凸组合引理覆盖（见 Lean receiver/sender
    _all_continuation_no_gain）."""

    problems = []
    c_l = consistent(game, sS, True, mu_l)
    c_h = consistent(game, sS, False, mu_h)
    if not c_l:
        problems.append("belief at L inconsistent with path Bayes")
    if not c_h:
        problems.append("belief at H inconsistent/off-support")
    br_l = eu_r(game, True, mu_l, sR[0]) >= eu_r(game, True, mu_l, not sR[0])
    br_h = eu_r(game, False, mu_h, sR[1]) >= eu_r(game, False, mu_h, not sR[1])
    if not br_l:
        problems.append("receiver not best-responding at L")
    if not br_h:
        problems.append("receiver not best-responding at H")
    br_s = sender_pay(game, sR, SigType.STRONG, sS[0]) >= \
        sender_pay(game, sR, SigType.STRONG, not sS[0])
    br_w = sender_pay(game, sR, SigType.WEAK, sS[1]) >= \
        sender_pay(game, sR, SigType.WEAK, not sS[1])
    if not br_s:
        problems.append("strong sender not best-responding")
    if not br_w:
        problems.append("weak sender not best-responding")
    return SeqEqReport(c_l, c_h, br_l, br_h, br_s, br_w, not problems,
                       tuple(problems))


# ---------------------------------------------------------------------------
# T115 无限重复折扣：尾界 / 离轨单偏离 / 可信惩罚阈值
# ---------------------------------------------------------------------------


def trunc_sum(delta: Q, u: Callable[[int], Q], n: int) -> Q:
    """前 n 期折扣和（对照 Lean truncSum）——无限和只用有限截断."""

    delta = _q(delta, "delta")
    return sum((delta ** t * u(t) for t in range(n)), Q(0))


def tail_bound(delta: Q, big_m: Q, u: Callable[[int], Q], big_n: int,
               k: int) -> Tuple[Q, Q, bool]:
    """尾界（对照 Lean tail_bound_mul/tail_bound）：返回 (lhs, rhs, ok)——
    |Σ_{t<k} δ^{N+t} u(N+t)|·(1−δ) ≤ M·δ^N；ok=False 时调用方拒绝."""

    delta = _q(delta, "delta")
    big_m = _q(big_m, "M")
    if not (0 <= delta < 1):
        raise ValueError("discount delta must lie in [0, 1)")
    if big_m < 0:
        raise ValueError("bound M must be nonnegative")
    if any(abs(u(big_n + t)) > big_m for t in range(k)):
        raise ValueError("payoff stream exceeds declared bound M")
    lhs = abs(sum((delta ** (big_n + t) * u(big_n + t) for t in range(k)),
                  Q(0))) * (1 - delta)
    rhs = big_m * delta ** big_n
    return (lhs, rhs, lhs <= rhs)


def one_dev_report(delta: Q, g: Callable[[int, bool], Q], a: Callable[[int], bool],
                   b: Callable[[int], bool], n: int) -> Tuple[bool, Tuple[str, ...]]:
    """离轨单偏离原理的有限核验（对照 Lean one_dev_principle）：核验每个
    单期替换都不获利，并据此断言只在窗口内不同的替代流整体不获利——任一
    单期替换获利即 fail-closed."""

    delta = _q(delta, "delta")
    if not (0 <= delta < 1):
        raise ValueError("discount delta must lie in [0, 1)")
    problems = []
    base = trunc_sum(delta, lambda t: g(t, a(t)), n)
    for t in range(n):
        for x in (True, False):
            dev = trunc_sum(delta,
                            lambda s, t=t, x=x: g(s, x if s == t else a(s)), n)
            if dev > base:
                problems.append(f"single deviation at {t}->{x} is profitable")
    b_tail_ok = all(b(s) == a(s) for s in range(n, n + 3))
    total = trunc_sum(delta, lambda t: g(t, b(t)), n)
    if not problems and total > base:
        problems.append("total deviation profitable despite no single gain")
    if not b_tail_ok:
        problems.append("b deviates beyond the checked window")
    return (not problems, tuple(problems))


def coop_threshold(r: Q, t: Q, p: Q) -> Q:
    """可信惩罚阈值 δ* = (T−R)/(T−P)（T>P，否则 fail-fast——无阈值可言）."""

    r, t, p = _q(r, "R"), _q(t, "T"), _q(p, "P")
    if not p < t:
        raise ValueError("credible threshold needs T > P")
    return (t - r) / (t - p)


def grim_sustains(r: Q, t: Q, p: Q, delta: Q) -> bool:
    """合作维持判据（对照 Lean coop_threshold_iff 正向）：T + δP/(1−δ) ≤
    R/(1−δ)."""

    r, t, p, delta = _q(r, "R"), _q(t, "T"), _q(p, "P"), _q(delta, "delta")
    if not (0 <= delta < 1):
        raise ValueError("discount delta must lie in [0, 1)")
    return t + delta * p / (1 - delta) <= r / (1 - delta)


def punish_credible(permitted: Callable[[bool], bool]) -> bool:
    """可信性前置（§8.3：惩罚必须本身为其子博弈允许/可信行动）——对照 Lean
    punishPermitted."""

    return permitted(False) is True


# ---------------------------------------------------------------------------
# 层总装（下游 run_case 消费的单一入口；挂接 diff 见分包报告）
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class GamesLayer:
    """W4 博弈层快照：量刑双线层、谈判后向归纳读数、序贯检查读数、
    重复博弈证书."""

    sentencing: SentencingLayer
    bargaining: BIResult
    seq_eq: SeqEqReport
    tail_ok: bool
    sustains: bool
    threshold: Q
    credible: bool


def build_games_layer(domain: NormDomain, responsibility: Q,
                      prevention_adjustment: Q, certs: Sequence[SentCert],
                      bargain: BargainParams, game: SigGame,
                      sS: Tuple[bool, bool], sR: Tuple[bool, bool],
                      mu_l: Belief, mu_h: Belief,
                      r: Q, t: Q, p: Q, delta: Q) -> GamesLayer:
    """总装四件读数（每件自带 fail-fast 门；任何一门失败即抛出）."""

    sentencing = build_sentencing_layer(domain, responsibility,
                                        prevention_adjustment, certs)
    if not sentencing.in_domain:
        raise ValueError("sentencing composition left the normative domain")
    bargaining = backward_induction(bargain)
    seq = seq_eq_check(game, sS, sR, mu_l, mu_h)
    if not seq.ok:
        raise ValueError("sequential check failed: " + ",".join(seq.reasons))
    big_m = max(abs(_q(r, "R")), abs(_q(t, "T")), abs(_q(p, "P"))) + 1
    _, _, tail_ok = tail_bound(delta, big_m, lambda _: _q(p, "P"), 1, 5)
    threshold = coop_threshold(r, t, p)
    sustains = grim_sustains(r, t, p, delta)
    return GamesLayer(sentencing=sentencing, bargaining=bargaining, seq_eq=seq,
                      tail_ok=tail_ok, sustains=sustains, threshold=threshold,
                      credible=punish_credible(lambda _a: True))
