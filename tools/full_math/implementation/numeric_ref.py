"""Reference algorithms for the numeric layer (N01–N10).

Mirrors of the Lean contracts: residual decomposition, calendar ordinals,
interval arithmetic with four-endpoint multiplication, LP weak duality
checkers, one-dimensional KKT certificates, integer branch-and-bound with
pruning certificates, projected-gradient contraction residuals, and
finite-horizon Bellman values.
"""
from __future__ import annotations
from fractions import Fraction
from typing import Dict, List, Sequence, Tuple


def residual_split(principal: Fraction, payments: Sequence[Fraction]) -> Tuple[Fraction, Fraction, Fraction]:
    """Return (R, C, U) with C = max(R,0), U = max(-R,0)."""
    r = principal - sum(payments, Fraction(0))
    return r, max(r, Fraction(0)), max(-r, Fraction(0))


def residual_checks(principal: Fraction, payments: Sequence[Fraction]) -> bool:
    r, c, u = residual_split(principal, payments)
    return c >= 0 and u >= 0 and c * u == 0 and c - u == r


def is_leap(y: int) -> bool:
    return (y % 4 == 0 and y % 100 != 0) or y % 400 == 0


MONTH_LEN = {1: 31, 3: 31, 4: 30, 5: 31, 6: 30, 7: 31, 8: 31, 9: 30, 10: 31, 11: 30, 12: 31}


def month_len(y: int, m: int) -> int:
    if m == 2:
        return 29 if is_leap(y) else 28
    return MONTH_LEN[m]


def day_of_year(y: int, m: int, d: int) -> int:
    return sum(month_len(y, k) for k in range(1, m)) + d


def succ_day_ordinal(y: int, m: int, d: int) -> bool:
    return day_of_year(y, m, d + 1) == day_of_year(y, m, d) + 1


# ---------------- intervals ----------------

def iv_add(a: Tuple[Fraction, Fraction], b: Tuple[Fraction, Fraction]):
    return (a[0] + b[0], a[1] + b[1])


def iv_mul(a: Tuple[Fraction, Fraction], b: Tuple[Fraction, Fraction]):
    ends = [a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1]]
    return (min(ends), max(ends))


def iv_recip(b: Tuple[Fraction, Fraction]):
    if b[0] > 0 or b[1] < 0:
        return (Fraction(1) / b[1] if b[1] != 0 else None, Fraction(1) / b[0])
    raise ValueError("zero not excluded from denominator")


def iv_contains(i: Tuple[Fraction, Fraction], x: Fraction) -> bool:
    return i[0] <= x <= i[1]


def iv_mul_sound(a, b, xs, ys) -> bool:
    prod = iv_mul(a, b)
    return all(iv_contains(prod, x * y) for x in xs for y in ys)


# ---------------- LP ----------------

def primal_feasible(A: List[List[Fraction]], b: List[Fraction], x: List[Fraction]) -> bool:
    n = len(x)
    return all(
        b[i] <= sum((A[i][j] * x[j] for j in range(n)), Fraction(0))
        for i in range(len(b))
    )


def dual_feasible(A: List[List[Fraction]], b: List[Fraction], c: List[Fraction], lam: List[Fraction]) -> bool:
    n = len(c)
    m = len(b)
    return (
        all(sum((lam[i] * A[i][j] for i in range(m)), Fraction(0)) == c[j] for j in range(n))
        and all(l >= 0 for l in lam)
    )


def weak_duality_holds(A, b, c, x, lam) -> bool:
    primal = sum((c[j] * x[j] for j in range(len(c))), Fraction(0))
    dual = sum((lam[i] * b[i] for i in range(len(b))), Fraction(0))
    return dual <= primal


# ---------------- KKT (1-d) ----------------

def kkt1_check(h: Fraction, g: Fraction, l: Fraction, xstar: Fraction, mu: Fraction) -> bool:
    return (
        h >= 0 and l <= xstar and mu >= 0
        and h * xstar + g - mu == 0
        and mu * (xstar - l) == 0
    )


def quad1(h: Fraction, g: Fraction, x: Fraction) -> Fraction:
    return h / 2 * x * x + g * x


def kkt1_suffices(h, g, l, xstar, mu, samples: Sequence[Fraction]) -> bool:
    if not kkt1_check(h, g, l, xstar, mu):
        return False
    return all(quad1(h, g, xstar) <= quad1(h, g, x) for x in samples if x >= l)


# ---------------- projected gradient ----------------

def clip(l: Fraction, u: Fraction, x: Fraction) -> Fraction:
    if x < l:
        return l
    if u < x:
        return u
    return x


def T_map(l, u, a, b, eta, x):
    return clip(l, u, (1 - eta * a) * x - eta * b)


def T_fixed_point(l, u, a, b, eta) -> Fraction:
    return clip(l, u, -b / a)


def residual_error_bound(k: Fraction, e0: Fraction, eps: Fraction, n: int) -> Fraction:
    return k ** n * e0 + eps / (1 - k)


# ---------------- Bellman ----------------

def bellman_vf(legal, r, p, beta, horizon, s0):
    """Backward induction: value[t][s]. legal: dict s -> list of actions."""
    states = sorted(legal.keys())
    v = {s: Fraction(0) for s in states}
    for _ in range(horizon):
        v_next = {}
        for s in states:
            v_next[s] = max(
                r(s, a) + beta * sum(p(s, a, sp) * v[sp] for sp in states)
                for a in legal[s]
            )
        v = v_next
    return v[s0]


def bellman_attained_by_legal(legal, r, p, beta, horizon, s0):
    v = {s: Fraction(0) for s in sorted(legal.keys())}
    states = sorted(legal.keys())
    chosen = None
    for _ in range(horizon):
        v_next = {}
        for s in states:
            best, best_a = None, None
            for a in legal[s]:
                q = r(s, a) + beta * sum(p(s, a, sp) * v[sp] for sp in states)
                if best is None or q > best:
                    best, best_a = q, a
            v_next[s] = best
            if s == s0:
                chosen = best_a
        v = v_next
    return chosen in legal[s0]
