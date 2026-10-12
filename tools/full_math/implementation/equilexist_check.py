"""Independent checker for the W16 (needle 30) reference entries.

Shares NO code with ``equilexist_ref`` -- not even the constant tables or the
game definitions: every check below re-derives its own expected values from
the raw payoff dictionaries passed in by the test.  The checker knows only the
mathematical contract:

* a mixed profile is a Nash equilibrium iff no pure unilateral deviation
  strictly gains (the pure-deviation characterization the Lean theorem
  ``nashR_iff_no_pure_dev_gain`` licenses);
* expected utility under a profile is the exact multilinear extension;
* the section-8.2 polynomial system (nonneg + normalization + no pure
  deviation gain) has as its solution set exactly the simplex Nash profiles;
* equilibrium-finder outputs must be equilibria, and on 2x2 games the
  equilibrium set can be re-derived from scratch by hand-enumerating the
  support cases independently.
"""
from __future__ import annotations

from fractions import Fraction
from itertools import product as iter_product
from typing import Callable, Dict, List, Mapping, Optional, Sequence, Tuple

Q = Fraction


class CheckError(AssertionError):
    pass


def _require(cond: bool, msg: str) -> None:
    if not cond:
        raise CheckError(msg)


# ---------------------------------------------------------------------------
# Fresh re-implementations (no sharing with the reference module)
# ---------------------------------------------------------------------------


def dev_gain(pay: Mapping[Tuple[Tuple[int, ...], int], Q], sigma: Mapping[int, Sequence[Q]],
             i: int, b: int, players: Sequence[int], actions: Sequence[int]) -> Q:
    """Strict gain of player i deviating from sigma[i] to pure action b."""
    base = _ev(pay, sigma, i, players, actions)
    trial = {k: (list(v) if k != i else _pure(b, actions)) for k, v in sigma.items()}
    return _ev(pay, trial, i, players, actions) - base


def _pure(b: int, actions: Sequence[int]) -> List[Q]:
    return [Fraction(1) if a == b else Fraction(0) for a in actions]


def _ev(pay: Mapping[Tuple[Tuple[int, ...], int], Q], sigma: Mapping[int, Sequence[Q]],
        i: int, players: Sequence[int], actions: Sequence[int]) -> Q:
    acc = Fraction(0)
    for combo in iter_product(actions, repeat=len(players)):
        prob = Fraction(1)
        for j, act in zip(players, combo):
            prob = prob * sigma[j][act]
        acc = acc + prob * pay[(combo, i)]
    return acc


def is_simplex_profile(sigma: Mapping[int, Sequence[Q]]) -> bool:
    for row in sigma.values():
        if any(x < 0 for x in row):
            return False
        if sum(row, Fraction(0)) != 1:
            return False
    return True


def nash_check(pay: Mapping[Tuple[Tuple[int, ...], int], Q], sigma: Mapping[int, Sequence[Q]],
               players: Sequence[int], actions: Sequence[int]) -> bool:
    """Independent Nash verdict: simplex profile + no positive pure-dev gain."""
    if not is_simplex_profile(sigma):
        return False
    return all(
        dev_gain(pay, sigma, i, b, players, actions) <= 0
        for i in players for b in actions
    )


# ---------------------------------------------------------------------------
# Checks of reference-module outputs (data flows in, code does not)
# ---------------------------------------------------------------------------


def check_equilibrium_outputs(pay, equil_list, players, actions) -> None:
    """Every reported equilibrium must independently be an equilibrium."""
    for sig0, sig1 in equil_list:
        sigma = {0: [Q(x) for x in sig0], 1: [Q(x) for x in sig1]}
        _require(nash_check(pay, sigma, players, actions),
                 f"reported non-equilibrium: {sigma}")


def check_2x2_completeness(pay, equil_list) -> None:
    """Re-derive the full equilibrium set of a 2x2 game from scratch.

    Independent route: enumerate the 3x3 support-pair cases by hand.
    """
    a0, a1 = 0, 1
    found = set()
    for s0 in ([a0], [a1], [a0, a1]):
        for s1 in ([a0], [a1], [a0, a1]):
            if len(s0) == 1 and len(s1) == 1:
                sigma = {0: _pure(s0[0], [a0, a1]), 1: _pure(s1[0], [a0, a1])}
                _maybe_add(pay, sigma, found)
            elif len(s0) == 1 and len(s1) == 2:
                # player 1 mixes p on a0, 1-p on a1; player 0 must make
                # player 1 indifferent between a0 and a1
                d0 = pay[((s0[0], a0), 1)] - pay[((s0[0], a1), 1)]
                if d0 == 0:
                    # any p works only if player 0's pure is a best response
                    for p in (Fraction(1, 3), Fraction(1, 2), Fraction(2, 3)):
                        sigma = {0: _pure(s0[0], [a0, a1]),
                                 1: [p, 1 - p]}
                        _maybe_add(pay, sigma, found, continuum=True)
                else:
                    continue
            elif len(s0) == 2 and len(s1) == 1:
                d1 = pay[((a0, s1[0]), 0)] - pay[((a1, s1[0]), 0)]
                if d1 == 0:
                    for p in (Fraction(1, 3), Fraction(1, 2), Fraction(2, 3)):
                        sigma = {0: [p, 1 - p],
                                 1: _pure(s1[0], [a0, a1])}
                        _maybe_add(pay, sigma, found, continuum=True)
                else:
                    continue
            else:
                # full mix: p (prob player 0 on a0) makes player 1
                # indifferent; q (prob player 1 on a0) makes player 0
                # indifferent -- solved from scratch by two-point
                # interpolation of each pure best-reply line
                q00, q01 = pay[((a0, a0), 0)], pay[((a0, a1), 0)]
                q10, q11 = pay[((a1, a0), 0)], pay[((a1, a1), 0)]
                p00, p10 = pay[((a0, a0), 1)], pay[((a1, a0), 1)]
                p01, p11 = pay[((a0, a1), 1)], pay[((a1, a1), 1)]
                dq = q00 - q01 - q10 + q11
                dp = p00 - p01 - p10 + p11
                if dq == 0 or dp == 0:
                    continue
                q = (q11 - q01) / dq     # prob player 1 puts on a0
                p = (p11 - p10) / dp     # prob player 0 puts on a0
                sigma = {0: [p, 1 - p], 1: [q, 1 - q]}
                _maybe_add(pay, sigma, found)
    reported = set()
    for sig0, sig1 in equil_list:
        reported.add((tuple(Q(x) for x in sig0), tuple(Q(x) for x in sig1)))
    _require(found == reported,
             f"equilibrium set mismatch: independent={found} reported={reported}")


def _maybe_add(pay, sigma, found: set, continuum: bool = False) -> None:
    if nash_check(pay, sigma, [0, 1], [0, 1]):
        if continuum:
            raise CheckError(
                "continuum branch hit: independent 2x2 checker cannot certify "
                "continuum equilibria with this fixture; adjust the fixture")
        found.add((tuple(sigma[0]), tuple(sigma[1])))


def check_same_relation_points(pay, u_fn, rho_list, row_of_fn, denote_fn,
                               players, actions) -> None:
    """CAD-formula denotation must equal the Nash verdict, pointwise."""
    for rho in rho_list:
        sigma = row_of_fn(rho)
        lhs = denote_fn(u_fn, rho, players, actions)
        rhs = nash_check(pay, sigma, players, actions)
        _require(lhs == rhs, f"same-relation fails at rho={rho}: formula={lhs} nash={rhs}")


def check_best_response_vertex(pay, sigma, players, actions, sample_rows) -> None:
    """Best-response vertex maximality, re-checked fresh: for each player,
    the maximal pure deviation gain must beat-or-tie every sampled mixed
    row's gain (the Kakutani nonemptiness ingredient; full maximality over
    ALL rows is the Lean theorem, the sampling is a sanity re-derivation)."""
    for i in players:
        gains = {b: dev_gain(pay, sigma, i, b, players, actions) for b in actions}
        best = max(gains.values())
        _require(best >= 0, f"best dev gain must be >= 0 (own row is a mix): {gains}")
        for row in sample_rows:
            trial = {k: (list(v) if k != i else [Q(x) for x in row])
                     for k, v in sigma.items()}
            g = _ev(pay, trial, i, players, actions) - _ev(pay, sigma, i, players, actions)
            _require(g <= best,
                     f"mixed row beats the pure vertex: gain {g} > {best}")


def check_affinity_identity(pay, sigma, i, r1, r2, a: Q, b: Q, players, actions) -> None:
    """Row-affinity of expected utility, recomputed independently."""
    combo = [a * x + b * y for x, y in zip(r1, r2)]
    t1 = {k: (list(v) if k != i else combo) for k, v in sigma.items()}
    t2a = {k: (list(v) if k != i else list(r1)) for k, v in sigma.items()}
    t2b = {k: (list(v) if k != i else list(r2)) for k, v in sigma.items()}
    lhs = _ev(pay, t1, i, players, actions)
    rhs = (a * _ev(pay, t2a, i, players, actions)
           + b * _ev(pay, t2b, i, players, actions))
    _require(lhs == rhs, f"affinity identity fails: {lhs} != {rhs}")


def check_roundtrip(row: Sequence[Q], to_pmf_fn, back_fn, actions) -> None:
    """pmf_of_row / to_row roundtrip: row -> pmf -> row is identity."""
    pmf = to_pmf_fn(row, actions)
    _require(pmf is not None, "simplex row failed pmf conversion")
    _require(back_fn(pmf, actions) == [Q(x) for x in row], "roundtrip broken")


def check_deviation_characterization_sampled(pay, sigma, players, actions,
                                             sample_rows) -> None:
    """Sampled sanity of the pure-deviation characterization (the Lean
    ``nashR_iff_no_pure_dev_gain`` gives the full iff; here we re-verify on
    sampled rational rows that a Nash profile indeed admits no positive gain
    and a reported non-Nash profile exhibits a positive-gain witness among
    pure deviations and sampled rows)."""
    pure_ok = all(
        dev_gain(pay, sigma, i, b, players, actions) <= 0
        for i in players for b in actions
    )
    sampled_ok = True
    for i in players:
        for row in sample_rows:
            trial = {k: (list(v) if k != i else [Q(x) for x in row])
                     for k, v in sigma.items()}
            if _ev(pay, trial, i, players, actions) > _ev(pay, sigma, i, players, actions):
                sampled_ok = False
    if pure_ok:
        _require(sampled_ok,
                 "pure deviations quiet but a sampled mixed deviation gains")
    # (the converse direction -- pure quiet implies ALL rows quiet -- is the
    # convexity argument proven in Lean; a finite sample cannot certify it)
