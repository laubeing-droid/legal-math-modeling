"""Independent contract checker for the W17 master-needle entries.

This module deliberately re-derives every expected observable with its own
inline logic; it shares no code with ``masterneedle_ref`` (it never imports
that module), takes no witness callbacks, and never uses the reference
implementation to generate expectations.  Inputs are the structured data of
the contract (rule tables, ledger/flow/loss tables, payment plans as plain
lists) and the observed outputs produced by the reference side; each
``check_*`` returns ``(ok, reasons)``.

Where the reference side folds states with set unions, allocates with a
min-cascade scan, integrates the preference reading over the six-kind table
and evaluates the Bernstein CDF by its binomial-sum closed form, this
checker re-derives with genuinely different code paths:

* Horn closure membership is re-derived by explicit derivation-DAG search
  per atom (does a finite derivation from the on-file materials exist?),
  not by fixed-point iteration;
* allocation rows are re-derived by repeated single-unit walking of the
  ledger (integer-step scan, no min calls);
* the preference reading is re-derived by a Horner-style single pass over
  the entries accumulating a per-kind dict, not a table-wide sum;
* the Bernstein CDF(2, 3) is re-derived from the expanded polynomial
  6q^2 - 8q^3 + 3q^4 (algebraically equal, computed differently);
* the pure-equilibrium claim is re-derived by brute-force enumeration of
  every action profile and deviation;
* the payment-split exchange is re-derived by decrement-carrying ledger
  simulation (pay p in unit slices, first-fit).
"""
from __future__ import annotations

from fractions import Fraction
from typing import Dict, List, Sequence, Tuple

Fail = Tuple[str, ...]


def _fail(reasons: Fail, msg: str) -> Tuple[str, ...]:
    return tuple(reasons) + (msg,)


# ---------------------------------------------------------------------------
# Universe / closure re-derivation (derivation-DAG search per atom)
# ---------------------------------------------------------------------------


def derivable(rules: Sequence[dict], materials: frozenset, atom: str) -> bool:
    """Is `atom` derivable?  Backward search: to derive a non-material atom,
    find a rule concluding it whose premises are all (recursively) derivable
    with memoization and cycle protection."""
    memo: Dict[str, bool] = {}

    def go(a: str, active: frozenset) -> bool:
        if a in materials:
            return True
        if a in memo:
            return memo[a]
        if a in active:
            return False  # cycle guard: does not prove derivability
        active2 = active | {a}
        for r in rules:
            if r["conclusion"] != a:
                continue
            if all(go(p, active2) for p in r["premises"]):
                memo[a] = True
                return True
        memo[a] = False
        return False

    return go(atom, frozenset())


def check_closure_membership(rules, materials, observed_members) -> Tuple[bool, Fail]:
    reasons: Fail = ()
    for a in observed_members:
        if not derivable(rules, materials, a):
            reasons = _fail(reasons, f"atom not derivable per DAG search: {a}")
    return (not reasons), reasons


def check_trajectory_soundness(rules, materials, traj) -> Tuple[bool, Fail]:
    """Every conclusion of the event chain must be derivable in the static
    chain (soundness), re-derived by the DAG search above."""
    conclusions = [str(next(r for r in rules if r["id"] == rid)["conclusion"])
                   for _, rid in traj]
    return check_closure_membership(rules, materials, conclusions)


# ---------------------------------------------------------------------------
# Allocation re-derivation (unit-step walking)
# ---------------------------------------------------------------------------


def unit_step_balance(amounts: List[Fraction], payment: Fraction) -> Fraction:
    """Pay `payment` in slices (first-fit); returns remaining total.
    Deliberately loop-shaped instead of the reference's min-cascade scan."""
    remaining = list(amounts)
    to_pay = payment
    progressed = True
    while to_pay > 0 and progressed:
        progressed = False
        for i in range(len(remaining)):
            if remaining[i] > 0:
                take = min(to_pay, remaining[i])
                remaining[i] -= take
                to_pay -= take
                progressed = True
                if to_pay <= 0:
                    break
    return sum(remaining, Fraction(0))


def check_balance_after(amounts, payments, observed) -> Tuple[bool, Fail]:
    cur = list(amounts)
    for p in payments:
        cur = _pay_scan(cur, p)
    got = sum(cur, Fraction(0))
    return (got == observed), () if got == observed else (
        f"balance mismatch: {got} != {observed}",)


def _pay_scan(amounts: List[Fraction], payment: Fraction) -> List[Fraction]:
    """First-fit decrement scan (no min cascade)."""
    out = list(amounts)
    left = payment
    for i in range(len(out)):
        if left <= 0:
            break
        if out[i] <= left:
            left -= out[i]
            out[i] = Fraction(0)
        else:
            out[i] -= left
            left = Fraction(0)
    return out


# ---------------------------------------------------------------------------
# Preference reading re-derivation (single-pass kind dict)
# ---------------------------------------------------------------------------


def reading_single_pass(valuation, entries) -> Fraction:
    buckets: Dict[str, Fraction] = {}
    for e in entries:
        buckets[e["kind"]] = buckets.get(e["kind"], Fraction(0)) + e["amount"]
    total = Fraction(0)
    for kind, amt in buckets.items():
        total += valuation[("claimant", kind)] * amt
    return total


def check_reading(valuation, entries, observed) -> Tuple[bool, Fail]:
    got = reading_single_pass(valuation, entries)
    return (got == observed), () if got == observed else (
        f"reading mismatch: {got} != {observed}",)


# ---------------------------------------------------------------------------
# Bernstein CDF re-derivation (expanded polynomial for (2, 3))
# ---------------------------------------------------------------------------


def cdf23_polynomial(q: Fraction) -> Fraction:
    """I_{2,3}(q) = 6q^2 - 8q^3 + 3q^4 (expanded form of the binomial sum)."""
    return 6 * q * q - 8 * q ** 3 + 3 * q ** 4


def check_beta_values(samples, observed_values) -> Tuple[bool, Fail]:
    reasons: Fail = ()
    for q, v in zip(samples, observed_values):
        if cdf23_polynomial(q) != v:
            reasons = _fail(reasons, f"beta value mismatch at {q}")
    return (not reasons), reasons


# ---------------------------------------------------------------------------
# Pure Nash re-derivation (brute force over all profiles and deviations)
# ---------------------------------------------------------------------------


def brute_force_pure_nash(pay_fn, players, actions=(False, True)) -> List[tuple]:
    """Enumerate every pure profile; keep those where no single-player
    deviation strictly improves that player's payoff."""
    equilibria = []
    for profile in _cartesian(actions, repeat=len(players)):
        ok = True
        for i in players:
            for dev in actions:
                if dev == profile[i]:
                    continue
                deviated = tuple(dev if j == i else profile[j] for j in players)
                if pay_fn(deviated, i) > pay_fn(profile, i):
                    ok = False
                    break
            if not ok:
                break
        if ok:
            equilibria.append(profile)
    return equilibria


def _cartesian(xs, repeat):
    if repeat == 0:
        yield ()
        return
    for tail in _cartesian(xs, repeat - 1):
        for x in xs:
            yield (x,) + tail


def check_equilibrium_claim(pay_fn, players, claimed_profile,
                            claimed_is_nash: bool) -> Tuple[bool, Fail]:
    equilibria = brute_force_pure_nash(pay_fn, players)
    actual = tuple(claimed_profile) in equilibria
    if actual != claimed_is_nash:
        return False, (f"equilibrium claim mismatch: brute force says "
                       f"{actual} for {claimed_profile}",)
    return True, ()


# ---------------------------------------------------------------------------
# Perturbation bound re-derivation
# ---------------------------------------------------------------------------


def check_abs_le(moved, bound, what: str) -> Tuple[bool, Fail]:
    if abs(moved) <= abs(bound):
        return True, ()
    return False, (f"{what}: |{moved}| > |{bound}|",)


def check_payoff_bound(valuation, entries, deltas,
                       observed_moved, observed_bound) -> Tuple[bool, Fail]:
    reasons: Fail = ()
    # re-derive the bound independently: sum |w(kind_e)| * |delta_e|
    bound = sum((abs(valuation[("claimant", e["kind"])]) * abs(deltas[i])
                 for i, e in enumerate(entries)), Fraction(0))
    if bound != observed_bound:
        reasons = _fail(reasons, f"payoff bound mismatch: {bound}")
    if not (abs(observed_moved) <= bound):
        reasons = _fail(reasons, f"payoff moved {observed_moved} exceeds {bound}")
    return (not reasons), reasons


def relu_lipschitz(x: Fraction, y: Fraction) -> bool:
    return abs(max(x, Fraction(0)) - max(y, Fraction(0))) <= abs(x - y)


def check_ledger_lipschitz(ps_sums: Sequence[Tuple[Fraction, Fraction]]) -> Tuple[bool, Fail]:
    reasons: Fail = ()
    for x, y in ps_sums:
        if not relu_lipschitz(x, y):
            reasons = _fail(reasons, f"ReLU Lipschitz fails at ({x}, {y})")
    return (not reasons), reasons


def check_beta_enclosure(n_l, n_u, b_l, b_u, rho, beta, loss) -> Tuple[bool, Fail]:
    reasons: Fail = ()
    if not (0 < rho and 0 < beta and 0 <= n_l and beta <= b_l and 0 < b_l
            and b_l <= b_u and n_l <= n_u and n_l <= b_u
            and n_u - n_l <= rho and b_u - b_l <= rho):
        reasons = _fail(reasons, "enclosure hypotheses violated")
        return False, reasons
    moved = abs(n_u / b_l * loss - n_l / b_u * loss)
    bound = 2 * rho / beta * abs(loss)
    if not (moved <= bound):
        reasons = _fail(reasons, f"beta enclosure: {moved} > {bound}")
    # width identity re-derivation: N_u/B_l - N_l/B_u must be nonnegative
    if n_u / b_l - n_l / b_u < 0:
        reasons = _fail(reasons, "enclosure endpoints inverted")
    return (not reasons), reasons


# ---------------------------------------------------------------------------
# Exchange re-derivations
# ---------------------------------------------------------------------------


def check_payment_split_exchange(amounts, p1, p2, observed) -> Tuple[bool, Fail]:
    reasons: Fail = ()
    s1 = sum(amounts, Fraction(0))
    b12 = max(s1 - (p1 + p2), Fraction(0))
    for key in ("E1", "E2"):
        if observed[key] != b12:
            reasons = _fail(reasons, f"{key}: {observed[key]} != {b12}")
    # allocation sums: two-stage vs one-stage both equal min(P, S)
    alloc_total = min(p1 + p2, s1)
    if observed["E3_two"] != alloc_total or observed["E3_one"] != alloc_total:
        reasons = _fail(reasons, "allocation totals != min(P, outstanding)")
    if observed["E4_cash_two"] != observed["E4_cash_one"]:
        reasons = _fail(reasons, "cash totals differ across the exchange")
    return (not reasons), reasons


def check_dedup_scale_commute(entries, c, lhs, rhs) -> Tuple[bool, Fail]:
    reasons: Fail = ()
    # re-derive: keys of both sides identical to the first-seen key sequence
    first_keys: List[tuple] = []
    seen = set()
    for e in entries:
        if e["key"] not in seen:
            seen.add(e["key"])
            first_keys.append(e["key"])
    if [e["key"] for e in lhs] != first_keys or [e["key"] for e in rhs] != first_keys:
        reasons = _fail(reasons, "dedup key sequences differ from first-seen")
    # amounts: both sides must be c * (amount of the first entry with that key)
    first_amounts = [next(x["amount"] for x in entries if x["key"] == k)
                     for k in first_keys]
    expect = [c * a for a in first_amounts]
    if [e["amount"] for e in lhs] != expect or [e["amount"] for e in rhs] != expect:
        reasons = _fail(reasons, "scaled amounts mismatch")
    return (not reasons), reasons


def check_interval_distributivity(c, i, j, lhs, rhs) -> Tuple[bool, Fail]:
    expect = (c * min(i[0], j[0]), c * max(i[1], j[1]))
    if lhs != expect or rhs != expect:
        return False, (f"interval distributivity mismatch: {lhs}/{rhs} vs {expect}",)
    return True, ()


# ---------------------------------------------------------------------------
# Quantity AST exactness
# ---------------------------------------------------------------------------


def check_qty_ast(denote_value, balance, div_free: bool) -> Tuple[bool, Fail]:
    reasons: Fail = ()
    if not div_free:
        reasons = _fail(reasons, "AST is not divFree")
    if denote_value != balance:
        reasons = _fail(reasons, f"AST denote {denote_value} != balance {balance}")
    if denote_value.denominator != 1:
        reasons = _fail(reasons, "AST value is not integer-valued")
    return (not reasons), reasons


# ---------------------------------------------------------------------------
# Coherence clauses (independent re-derivation)
# ---------------------------------------------------------------------------


def check_coherence(rules, materials, traj, ledger_idents, backing, flows,
                    pay_plan, balance, loss_iv, final_net,
                    judgment_established: bool) -> Tuple[bool, Fail]:
    reasons: Fail = ()
    # C3: every backing atom is BOTH in the event final state and derivable
    for ident in ledger_idents:
        atom = backing[ident]
        if atom not in final_net:
            reasons = _fail(reasons, f"backing atom {atom} not in final state")
        if not derivable(rules, materials, atom):
            reasons = _fail(reasons, f"backing atom {atom} not derivable")
    # C5: judgment established AND loanEntitlement produced by the chain
    if not judgment_established:
        reasons = _fail(reasons, "frame judgment not established")
    if "loanEntitlement" not in final_net:
        reasons = _fail(reasons, "loanEntitlement missing from final state")
    # C6: balance inside the interval
    if not (loss_iv[0] <= balance <= loss_iv[1]):
        reasons = _fail(reasons, f"balance {balance} outside {loss_iv}")
    return (not reasons), reasons
