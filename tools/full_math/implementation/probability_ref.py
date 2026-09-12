"""Reference algorithms for the probability layer (P01–P13, EXT06, E01).

Chain Bayesian networks with exact normalization, conditioning with typed
incompatible branch, Dirichlet updates, hierarchical Beta weights with
rising factorial ratios, misspecification bounds, Brier identity, PAV with
independent KKT certificates, conformal quantiles with +infinity handling,
finite betting paths, and E01 evaluation contracts with cluster-isolated
splits.
"""
from __future__ import annotations
from fractions import Fraction
from math import comb, prod
from typing import Dict, List, Optional, Sequence, Tuple


# ---------------- P01: chain BN ----------------

def chain_joint(kernels: Sequence[Dict[str, Fraction]], assignment: Sequence[bool]) -> Fraction:
    """kernels[i] = {'f': q0, 't': q1} conditioned on the prefix (marginal use)."""
    p = Fraction(1)
    for i, bit in enumerate(assignment[: len(kernels)]):
        p *= kernels[i]["t" if bit else "f"]
    return p


def chain_normalizes(kernels) -> bool:
    n = len(kernels)
    total = Fraction(0)
    for mask in range(1 << n):
        assignment = [(mask >> (n - 1 - i)) & 1 == 1 for i in range(n)]
        total += chain_joint(kernels, assignment)
    return total == 1


# ---------------- P02: conditioning ----------------

def condition(p: Dict[str, Fraction], evidence) -> Tuple[Optional[Dict[str, Fraction]], bool]:
    z = sum((v for k, v in p.items() if evidence(k)), Fraction(0))
    if z > 0:
        return {k: (v / z if evidence(k) else Fraction(0)) for k, v in p.items()}, True
    return None, False


# ---------------- P05/P06: Dirichlet / hierarchical Beta ----------------

def dir_weights(alpha: Sequence[Fraction], counts: Sequence[Fraction]) -> List[Fraction]:
    total = sum((a + n for a, n in zip(alpha, counts)), Fraction(0))
    return [(a + n) / total for a, n in zip(alpha, counts)]


def rising(x: Fraction, n: int) -> Fraction:
    return prod((x + j for j in range(n)), start=Fraction(1))


def beta_ratio(alpha: Fraction, beta: Fraction, w: int, l: int) -> Fraction:
    return (rising(alpha, w) * rising(beta, l)) / rising(alpha + beta, w + l)


def hyper_weights(pi: Sequence[Fraction], ratios: Sequence[Fraction]) -> List[Fraction]:
    raw = [p * r for p, r in zip(pi, ratios)]
    total = sum(raw, Fraction(0))
    if total <= 0:
        raise ValueError("mixture mass must be positive")
    return [x / total for x in raw]


# ---------------- P08: misspecification ----------------

def contamination_bounds(eps: Fraction, p: Fraction, q: Fraction,
                         l: Fraction, u: Fraction) -> bool:
    star = (1 - eps) * p + eps * q
    return (1 - eps) * l <= star <= (1 - eps) * u + eps


# ---------------- P10: unprocessed mass ----------------

def unprocessed_bounds(a: Fraction, b: Fraction, u: Fraction, v: Fraction,
                       r: Fraction) -> bool:
    if a + b == 0:
        return False  # degenerate branch handled separately
    lower = a / (a + b + r)
    mid = (a + u) / (a + b + u + v)
    upper = (a + r) / (a + b + r)
    return lower <= mid <= upper


# ---------------- P11: Brier ----------------

def brier_excess(p: Fraction, q: Fraction) -> Fraction:
    return (q - p) ** 2


# ---------------- P12: PAV with KKT certificate ----------------

def pav_weights(y: Sequence[Fraction], w: Sequence[Fraction]) -> List[Fraction]:
    blocks = [[i] for i in range(len(y))]
    values = [yi for yi in y]

    def block_value(block):
        return sum((w[i] * y[i] for i in block), Fraction(0)) / sum((w[i] for i in block), Fraction(0))

    i = 0
    while i < len(blocks) - 1:
        if block_value(blocks[i]) > block_value(blocks[i + 1]):
            merged = blocks[i] + blocks[i + 1]
            blocks[i:i + 2] = [merged]
            if i > 0:
                i -= 1
        else:
            i += 1
    out = [Fraction(0)] * len(y)
    for block in blocks:
        v = block_value(block)
        for i in block:
            out[i] = v
    return out


def pav_kkt_certificate(y: Sequence[Fraction], w: Sequence[Fraction]) -> Optional[dict]:
    """Independent optimality certificate: `x` is nondecreasing, constant on
    blocks, each block value is the weighted mean (stationarity), the total
    gradient sums to zero, and the per-block partial sums of the negated
    gradient are nonnegative (dual feasibility)."""
    x = pav_weights(y, w)
    n = len(y)
    if any(x[i] > x[i + 1] for i in range(n - 1)):
        return None
    g = [2 * w[i] * (x[i] - y[i]) for i in range(n)]
    if sum(g, Fraction(0)) != 0:
        return None
    blocks = []
    i = 0
    while i < n:
        j = i
        while j + 1 < n and x[j] == x[j + 1]:
            j += 1
        blocks.append((i, j))
        i = j + 1
    for (a, b) in blocks:
        mean = sum((w[k] * y[k] for k in range(a, b + 1)), Fraction(0)) /             sum((w[k] for k in range(a, b + 1)), Fraction(0))
        if x[a] != mean:
            return None
        partial = Fraction(0)
        for k in range(a, b):
            partial -= g[k]
            if partial < 0:
                return None
    return {"x": x, "blocks": blocks, "g": g}


def pav_optimal_over(y, w, x, samples: Sequence[Sequence[Fraction]]) -> bool:
    fx = sum((w[i] * (x[i] - y[i]) ** 2 for i in range(len(y))), Fraction(0))
    for z in samples:
        if any(z[i] > z[i + 1] for i in range(len(z) - 1)):
            continue
        fz = sum((w[i] * (z[i] - y[i]) ** 2 for i in range(len(y))), Fraction(0))
        if fz < fx:
            return False
    return True


# ---------------- P13: conformal ----------------

def conformal_k(n: int, alpha: Fraction) -> int:
    import math
    return math.ceil(Fraction(n + 1) * (1 - alpha))


def conformal_quantile(scores: Sequence[Fraction], k: int):
    if k == len(scores) + 1:
        return float("inf")
    return sorted(scores)[k - 1]


def conformal_coverage_count(scores: Sequence[Fraction], k: int) -> int:
    q = conformal_quantile(scores, k)
    if q == float("inf"):
        return len(scores)
    return sum(1 for s in scores if s <= q)


# ---------------- EXT06: betting path ----------------

def betting_factor(lam: Fraction, loss: Fraction, r: Fraction) -> Fraction:
    return 1 + lam * (loss - r)


def path_nonnegative(lams: Sequence[Fraction], losses: Sequence[Fraction], r: Fraction) -> bool:
    m = Fraction(1)
    for lam, loss in zip(lams, losses):
        if not (0 <= lam <= 1 / r if r > 0 else False):
            return False
        if not (0 <= loss <= 1):
            return False
        m *= betting_factor(lam, loss, r)
        if m < 0:
            return False
    return True


# ---------------- E01: evaluation contract ----------------

def brier_score(predictions: Sequence[Fraction], outcomes: Sequence[int]) -> Fraction:
    return sum(((p - o) ** 2 for p, o in zip(predictions, outcomes)), Fraction(0)) / len(outcomes)


def clusters_disjoint(train_clusters: set, test_clusters: set) -> bool:
    return not (train_clusters & test_clusters)


def e01_status(calibration_score: Fraction, threshold: Fraction,
               n_calibration: int, min_n: int) -> str:
    if n_calibration < min_n:
        return "REAL_VALIDATION_REQUIRED"
    if calibration_score > threshold:
        return "REAL_VALIDATION_REQUIRED"
    return "WITHIN_DECLARED_RISK"


def cantelli_bound(mean: Fraction, var: Fraction, t: Fraction) -> Fraction:
    """One-sided Cantelli bound P(X - mean >= t) <= var / (var + t^2)."""
    if t <= 0 or var <= 0:
        raise ValueError("t and variance must be positive")
    return var / (var + t * t)
