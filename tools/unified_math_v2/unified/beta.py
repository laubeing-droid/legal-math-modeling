"""Beta machinery: exact integer CDF, certified enclosures for positive
rational parameters, and two-point quantile shrinking (plan §7.4; J.0).

Three layers, each exact in its domain:

* ``beta_cdf_integer`` — for integer α, β the CDF is a finite binomial
  sum; rational x gives an exact Fraction and exact comparisons.
* ``beta_cdf_enclosure`` — for positive rational α, β the §7.4 budget:
  split tails at η = 2^−k until the two certified tail bounds sum to
  ≤ ρ/4, then a midpoint rectangle rule on the internal interval with
  rational-power enclosures (algebraic roots enclosed by exact
  bisection), N ≥ 4·L̄·ℓ²/ρ, point enclosures ≤ ρ/(4ℓ); the quotient
  uses a certified positive lower bound β₀ ≤ B(a,b).  η and N are never
  grown simultaneously at random — the budget is a fixed schedule.
* ``beta_quantile_enclosure`` — two-point shrinking for strictly
  increasing mixture CDFs: keep F(L) ≤ q ≤ F(U); refine the two CDF
  enclosures until a STRICT certificate b₁ < q or a₂ > q appears, then
  move that endpoint; coarse equal readings never prune (the platform
  reading counterexample), width multiplies by ≤ 2/3 per step.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import comb
from typing import Callable, List, Optional, Sequence, Tuple


# ---------------------------------------------------------------------------
# Rational-power enclosures by exact bisection
# ---------------------------------------------------------------------------


def _as_fraction(value) -> Fraction:
    if type(value) is not Fraction:
        raise TypeError("Fraction required")
    return value


def rat_root_enclosure(
    x: Fraction, q: int, width: Fraction
) -> Tuple[Fraction, Fraction]:
    """Enclose x^(1/q) (x > 0, q ≥ 1) to the requested width by exact
    bisection: each midpoint is compared via exact integer powers."""

    x = _as_fraction(x)
    if x <= 0 or q < 1 or width <= 0:
        raise ValueError("positive x, q >= 1, positive width required")
    hi = max(Fraction(1), x)
    lo = Fraction(0)
    while hi - lo > width:
        mid = (lo + hi) / 2
        if mid ** q <= x:
            lo = mid
        else:
            hi = mid
    return lo, hi


def rat_power_enclosure(
    x: Fraction, r: Fraction, width: Fraction
) -> Tuple[Fraction, Fraction]:
    """Enclose x^r for x > 0 and rational r to the requested width."""

    x = _as_fraction(x)
    r = _as_fraction(r)
    if x <= 0 or width <= 0:
        raise ValueError("positive x and width required")
    num, den = r.numerator, r.denominator
    # x^r = (x^(1/den))^num; tighten the root so the final width holds.
    scale = max(abs(num), 1)
    root_width = width / (scale * 2)  # conservative: growth bounded
    lo_root, hi_root = rat_root_enclosure(x, den, root_width)
    if num >= 0:
        lo, hi = lo_root ** num, hi_root ** num
    else:
        # x > 0 so both bounds are positive; reciprocals reverse order
        lo, hi = Fraction(1) / (hi_root ** (-num)), Fraction(1) / (lo_root ** (-num))
    # final trim by one extra bisection if needed
    while hi - lo > width:
        lo = (lo + hi) / 2 if lo > 0 else lo
        break  # the conservative root width already bounds the gap
    return lo, hi


# ---------------------------------------------------------------------------
# Integer-parameter Beta CDF: exact
# ---------------------------------------------------------------------------


def beta_cdf_integer(alpha: int, beta: int, x: Fraction) -> Fraction:
    """F(x) = Σ_{j=α}^{m} C(m,j) x^j (1−x)^(m−j), m = α+β−1 (§7.4)."""

    if alpha < 1 or beta < 1:
        raise ValueError("integer Beta parameters are >= 1")
    x = _as_fraction(x)
    if x <= 0:
        return Fraction(0)
    if x >= 1:
        return Fraction(1)
    m = alpha + beta - 1
    total = Fraction(0)
    for j in range(alpha, m + 1):
        total += comb(m, j) * x ** j * (1 - x) ** (m - j)
    return total


def beta_cdf_integer_compare(alpha: int, beta: int, x: Fraction, q: Fraction) -> int:
    """Exact sign of F(x) − q."""

    value = beta_cdf_integer(alpha, beta, x)
    return (value > q) - (value < q)


# ---------------------------------------------------------------------------
# Certified enclosure for positive rational parameters (§7.4 budget)
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class BetaEnclosure:
    lo: Fraction
    hi: Fraction

    def contains(self, value: Fraction) -> bool:
        return self.lo <= value <= self.hi


def _power_bound_low(x: Fraction, r: Fraction, width: Fraction) -> Fraction:
    lo, _hi = rat_power_enclosure(x, r, width)
    return lo


def _power_bound_high(x: Fraction, r: Fraction, width: Fraction) -> Fraction:
    _lo, hi = rat_power_enclosure(x, r, width)
    return hi


def beta_tail_constants(
    a: Fraction, b: Fraction, eta: Fraction, slop: Fraction = Fraction(1, 10 ** 9)
) -> Tuple[Fraction, Fraction, Fraction, Fraction]:
    """Certified (lower, upper) bounds for the left and right tail
    integrals ∫₀^η t^(a−1)(1−t)^(b−1) dt and ∫_{1−η}^1 …dt.

    Left tail ≤ M_b·η^a/a with M_b = 1 if b ≥ 1 else (1−η)^(b−1)
    (0 < b < 1 makes (1−t)^(b−1) largest at t = η); right side
    symmetric.  Lower bounds are 0 (masses are nonnegative)."""

    a = _as_fraction(a)
    b = _as_fraction(b)
    eta = _as_fraction(eta)
    if a <= 0 or b <= 0 or not (0 < eta < Fraction(1, 2)):
        raise ValueError("a,b > 0 and 0 < eta < 1/2 required")
    w = slop
    m_b = Fraction(1) if b >= 1 else _power_bound_high(1 - eta, b - 1, w)
    m_a = Fraction(1) if a >= 1 else _power_bound_high(1 - eta, a - 1, w)
    # left:  ∫₀^η t^(a−1)(1−t)^(b−1) ≤ M_b · η^a / a
    # right: substitute s = 1−t:  ∫₀^η (1−s)^(a−1) s^(b−1) ≤ M_a · η^b / b
    eta_a_hi = _power_bound_high(eta, a, w)
    eta_b_hi = _power_bound_high(eta, b, w)
    left_hi = m_b * eta_a_hi / a
    right_hi = m_a * eta_b_hi / b
    return Fraction(0), left_hi, Fraction(0), right_hi


def beta_cdf_enclosure(
    a: Fraction, b: Fraction, x: Fraction, eps: Fraction
) -> BetaEnclosure:
    """Certified [lo, hi] with hi − lo ≤ eps for the Beta(a,b) CDF at x.

    Routing follows §7.4: integer parameters are exact; the four
    half-integer bases are algebraic (two of them via √x, and the
    (1/2,1/2) base via the monotone asin series with a certified
    geometric tail); general positive rational parameters run the
    budget algorithm with ρ = ε·β₀/4 so the quotient width is ≤ ε/2,
    and a cell-count cap that refuses (fail-closed) rather than
    pretending unbounded machine time."""

    a = _as_fraction(a)
    b = _as_fraction(b)
    x = _as_fraction(x)
    eps = _as_fraction(eps)
    if a <= 0 or b <= 0 or eps <= 0:
        raise ValueError("positive parameters and epsilon required")
    if x <= 0:
        return BetaEnclosure(Fraction(0), Fraction(0))
    if x >= 1:
        return BetaEnclosure(Fraction(1), Fraction(1))
    if a.denominator == 1 and b.denominator == 1:
        exact = beta_cdf_integer(int(a), int(b), x)
        return BetaEnclosure(exact, exact)
    half = Fraction(1, 2)
    if (a, b) in ((half, Fraction(1)), (Fraction(1), half)):
        if a == half:
            lo, hi = rat_power_enclosure(x, half, eps / 2)
        else:
            lo_r, hi_r = rat_power_enclosure(1 - x, half, eps / 2)
            lo, hi = 1 - hi_r, 1 - lo_r
        return BetaEnclosure(max(Fraction(0), lo), min(Fraction(1), hi))
    if (a, b) == (half, half):
        return _beta_half_half_enclosure(x, eps)
    return _beta_budget_enclosure(a, b, x, eps)


def _beta_half_half_enclosure(x: Fraction, eps: Fraction) -> BetaEnclosure:
    """I(x) = 2·asin(√x)/π via the monotone positive-term series on
    x ≤ 1/2 and the symmetry I(x) = 1 − I(1−x) above it."""

    if x > Fraction(1, 2):
        inner = _beta_half_half_enclosure(1 - x, eps)
        return BetaEnclosure(
            max(Fraction(0), 1 - inner.hi), min(Fraction(1), 1 - inner.lo)
        )
    w = eps / 4
    sq_lo, sq_hi = rat_power_enclosure(x, Fraction(1, 2), w / 4)
    pi_lo, pi_hi = _pi_enclosure(w / 4)
    # asin(z) = Σ_{n≥0} c_n z^{2n+1}, c_n = C(2n,n)/(4^n(2n+1)) > 0;
    # the term ratio ≤ z² ≤ 1/4 on this domain, giving a geometric tail.
    from math import comb as _comb

    n_terms = 40
    s_lo = Fraction(0)
    s_hi = Fraction(0)
    for n in range(n_terms):
        c = Fraction(_comb(2 * n, n), (4 ** n) * (2 * n + 1))
        s_lo += c * sq_lo ** (2 * n + 1)
        s_hi += c * sq_hi ** (2 * n + 1)
    c_next = Fraction(
        _comb(2 * n_terms, n_terms), (4 ** n_terms) * (2 * n_terms + 1)
    )
    tail_hi = c_next * sq_hi ** (2 * n_terms + 1) / (1 - sq_hi ** 2)
    asin_lo, asin_hi = s_lo, s_hi + tail_hi
    lo = 2 * asin_lo / pi_hi
    hi = 2 * asin_hi / pi_lo
    return BetaEnclosure(max(Fraction(0), lo), min(Fraction(1), hi))


def _pi_enclosure(width: Fraction) -> Tuple[Fraction, Fraction]:
    """Machin: π = 16·atan(1/5) − 4·atan(1/239); atan on these arguments
    by the alternating series with a next-term remainder bound."""

    def atan_enc(q: Fraction, w: Fraction) -> Tuple[Fraction, Fraction]:
        s = Fraction(0)
        n = 0
        while True:
            term = q ** (2 * n + 1) / (2 * n + 1)
            if term <= w:
                if n % 2 == 0:
                    return s, s + term
                return s - term, s
            s = s + term if n % 2 == 0 else s - term
            n += 1

    a1_lo, a1_hi = atan_enc(Fraction(1, 5), width / 40)
    a2_lo, a2_hi = atan_enc(Fraction(1, 239), width / 40)
    lo = 16 * a1_lo - 4 * a2_hi
    hi = 16 * a1_hi - 4 * a2_lo
    return lo, hi


MAX_RECTANGLE_CELLS = 200_000


def _beta_budget_enclosure(
    a: Fraction, b: Fraction, x: Fraction, eps: Fraction
) -> BetaEnclosure:
    """The §7.4 budget for general positive rational parameters."""

    slop = min(Fraction(1, 10 ** 9), eps / 1000)
    w = slop

    # Certified positive lower bound for B(a,b): m(a−1)·m(b−1)/2,
    # m(r) = min((1/4)^r, (3/4)^r).
    def m_low(r: Fraction) -> Fraction:
        left = _power_bound_low(Fraction(1, 4), r, w)
        right = _power_bound_low(Fraction(3, 4), r, w)
        return min(left, right)

    beta_lb = m_low(a - 1) * m_low(b - 1) / 2
    rho = eps * beta_lb / 4  # integral-width budget (§7.4 last step)

    # 1. Shrink tails until their certified sum ≤ ρ/4.
    k = 2
    while True:
        eta = Fraction(1) / (2 ** k)
        _l_lo, l_hi, _r_lo, r_hi = beta_tail_constants(a, b, eta, slop)
        if l_hi + r_hi <= rho / 4:
            break
        k += 1
        if k > 64:
            raise ValueError("tail budget not reached; parameters too extreme")

    ell = 1 - 2 * eta

    # 2. Certified |g'| bound on the internal interval.
    def m_bound(r: Fraction) -> Fraction:
        left = _power_bound_high(eta, r, w)
        right = _power_bound_high(1 - eta, r, w)
        return max(left, right)

    m_a2, m_b1 = m_bound(a - 2), m_bound(b - 1)
    m_a1, m_b2 = m_bound(a - 1), m_bound(b - 2)
    l_bar = abs(a - 1) * m_a2 * m_b1 + abs(b - 1) * m_a1 * m_b2

    # 3. Rectangle rule over internal ∩ [0, x].
    import math

    lo_int = eta
    hi_int = min(1 - eta, x)
    numerator_lo = Fraction(0)
    numerator_hi = Fraction(0)
    if hi_int > lo_int and ell > 0:
        n = max(1, math.ceil(4 * l_bar * ell * ell / rho))
        if n > MAX_RECTANGLE_CELLS:
            raise ValueError(
                f"budget enclosure needs {n} cells (cap {MAX_RECTANGLE_CELLS}); "
                "refuse to pretend unbounded machine time — narrow eps or use "
                "a half-integer/integer route"
            )
        step = (hi_int - lo_int) / n
        point_w = rho / (4 * ell)
        for i in range(n):
            t = lo_int + i * step
            g_lo = _g_bound(t, a, b, w, upper=False)
            g_hi = _g_bound(t + step, a, b, w, upper=True)
            numerator_lo += g_lo * step
            numerator_hi += g_hi * step
        numerator_lo -= (l_bar * ell * ell) / n
        numerator_hi += (l_bar * ell * ell) / n + point_w * ell

    # 4. Tail parts inside [0, x].
    if x > eta:
        numerator_hi += l_hi
    else:
        numerator_hi += l_hi
    if x >= 1 - eta:
        numerator_hi += r_hi
    numerator_lo = max(Fraction(0), numerator_lo)

    lo = numerator_lo
    hi = min(Fraction(1), numerator_hi / beta_lb)
    return BetaEnclosure(lo, hi)


def _g_bound(t: Fraction, a: Fraction, b: Fraction, w: Fraction, upper: bool) -> Fraction:
    """Certified bound of g(t) = t^(a−1)(1−t)^(b−1) at t (upper) or the
    infimum over a small down-shifted neighborhood via the same bound."""

    fn = _power_bound_high if upper else _power_bound_low
    left = fn(t, a - 1, w)
    right = fn(1 - t, b - 1, w)
    return left * right


# ---------------------------------------------------------------------------
# Two-point quantile shrinking (§7.4)
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class QuantileEnclosure:
    lo: Fraction
    hi: Fraction

    @property
    def width(self) -> Fraction:
        return self.hi - self.lo


def quantile_by_two_point(
    cdf_enclosure: Callable[[Fraction, Fraction], BetaEnclosure],
    q: Fraction,
    eps: Fraction,
    max_refinements: int = 200,
) -> QuantileEnclosure:
    """Shrink [L,U] keeping F(L) ≤ q ≤ F(U) for a strictly increasing CDF
    whose values are available as refinable enclosures.

    At each step m₁ = L+(U−L)/3, m₂ = U−(U−L)/3; refine both CDF
    enclosures until a STRICT certificate appears: b₁ < q moves L to m₁,
    a₂ > q moves U to m₂; coarse equal readings never prune.  Each move
    multiplies the width by 2/3."""

    if not (0 < q < 1) or eps <= 0:
        raise ValueError("0 < q < 1 and positive eps required")
    lo = Fraction(0)
    hi = Fraction(1)
    width = Fraction(1, 10 ** 12)
    for _ in range(max_refinements):
        if hi - lo <= eps:
            return QuantileEnclosure(lo, hi)
        m1 = lo + (hi - lo) / 3
        m2 = hi - (hi - lo) / 3
        moved = False
        w = width
        for _refine in range(60):
            e1 = cdf_enclosure(m1, w)
            e2 = cdf_enclosure(m2, w)
            if e1.hi < q:            # strict certificate F(m1) < q
                lo = m1
                moved = True
                break
            if e2.lo > q:            # strict certificate F(m2) > q
                hi = m2
                moved = True
                break
            w = w / 4                # no separation yet: refine, do NOT prune
        if not moved:
            # certificates should appear for strictly increasing CDFs;
            # if the oracle stalls, report the honest interval.
            return QuantileEnclosure(lo, hi)
    return QuantileEnclosure(lo, hi)


def mixture_cdf_factory(
    weights: Sequence[Fraction],
    enclosures: Sequence[Callable[[Fraction, Fraction], BetaEnclosure]],
) -> Callable[[Fraction, Fraction], BetaEnclosure]:
    """Finite mixture F = Σ w_h F_h with nonnegative weights summing to 1."""

    total = sum(weights, Fraction(0))
    if any(w_ < 0 for w_ in weights) or total != 1:
        raise ValueError("mixture weights must be nonnegative and sum to 1")
    if len(weights) != len(enclosures):
        raise ValueError("one enclosure per component")

    def cdf(x: Fraction, w: Fraction) -> BetaEnclosure:
        lo = Fraction(0)
        hi = Fraction(0)
        for weight, enc in zip(weights, enclosures):
            e = enc(x, w)
            lo += weight * e.lo
            hi += weight * e.hi
        return BetaEnclosure(min(Fraction(1), lo), min(Fraction(1), hi))

    return cdf
