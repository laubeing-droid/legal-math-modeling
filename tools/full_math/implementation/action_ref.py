"""Reference algorithms for the action layer (G01–G05, EXT08).

Settlement zones with legality-first intersection, gross value of
information, reserve-price mechanism DSIC checks, finite-horizon legal
dynamic programming, and shared-θ robust bounds vs rectangular
decomposition.
"""
from __future__ import annotations
from fractions import Fraction
from typing import Dict, List, Optional, Sequence, Tuple

F = Fraction


# ---------------- G01 settlement ----------------

def plaintiff_l(merit, cost, shift):
    return merit - cost + shift


def defendant_u(merit, cost, shift):
    return merit + cost - shift


def settlement_zone(P, D):
    L = plaintiff_l(*P)
    U = defendant_u(*D)
    return (L, U) if L <= U else None


def admissible_settlements(legal: Sequence[F], P, D) -> List[F]:
    zone = settlement_zone(P, D)
    if zone is None:
        return []
    L, U = zone
    return [s for s in legal if L <= s <= U]


# ---------------- G02 value of information ----------------

def gross_voi(weights: Sequence[F], cell_utils: Dict) -> F:
    """cell_utils[k][c]: utility of choice k in cell c."""
    cells = list(range(len(weights)))
    adaptive = sum(weights[c] * max(cell_utils[k][c] for k in cell_utils)
                   for c in cells)
    best_fixed = max(sum(weights[c] * cell_utils[k][c] for c in cells)
                     for k in cell_utils)
    return adaptive - best_fixed


# ---------------- G03 mechanism ----------------

def second_price_reserve(r: F, bid: F):
    win = r < bid
    return (F(1) if win else F(0), r if win else F(0))


def util(value: F, bid: F, r: F) -> F:
    alloc, pay = second_price_reserve(r, bid)
    return value * alloc - pay


def dsic_holds(r: F, values: Sequence[F], bids: Sequence[F]) -> bool:
    return all(util(v, v, r) >= util(v, b, r) for v in values for b in bids)


# ---------------- G04/EXT08 finite-horizon DP (mirror of numeric_ref) ----------------

def legal_dp_value(legal: Dict, r, p, beta, horizon, s0):
    states = sorted(legal.keys())
    v = {s: F(0) for s in states}
    for _ in range(horizon):
        v = {s: max(r(s, a) + beta * sum(p(s, a, sp) * v[sp] for sp in states)
                    for a in legal[s]) for s in states}
    return v[s0]


def legal_dp_policy_legal(legal: Dict, r, p, beta, horizon, s0) -> bool:
    states = sorted(legal.keys())
    v = {s: F(0) for s in states}
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


# ---------------- G05 robust ----------------

def shared_theta_value(theta_grid: Sequence[F], policy) -> F:
    """max_policy min_theta V(policy, theta) over the grid with V = policy(theta)."""
    return min(policy(theta) for theta in theta_grid)


def rectangular_bound(theta_grid, r1, r2) -> F:
    return min(r1(t) for t in theta_grid) + min(r2(t) for t in theta_grid)


def shared_total(theta) -> F:
    return theta + (1 - theta)
