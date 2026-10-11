"""Independent checker for the payoff chain and the lawView use points (W1-13).

Re-implements the two needles' semantics inline from the frozen carriers
alone — cost aggregation, the preference integral, the anchor payoff
reading, the truncated view, the docket read, and the rule-network closure —
sharing NO functions with ``payoffchain_ref`` (dataclasses, enums and
frozen tables only).  Every check returns a CheckReport; differential checks
compare a reported value against a value recomputed here.
"""
from __future__ import annotations

from dataclasses import dataclass, replace
from fractions import Fraction
from typing import Dict, FrozenSet, Iterable, Tuple

from tools.full_math.implementation.payoffchain_ref import (
    ALL_CONS,
    CashEntry,
    Consequence,
    DECLARED_CONSEQUENCES,
    LawRule,
    LegalStatus,
    PayFlow,
    Role,
    WITNESS_ENTRIES,
    CONSEQUENCE_VALUATION,
    FAMILY_RULES,
    MAT_ATOMS,
)


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
# Inline semantic re-derivations — needle 28 (zero function sharing)
# ---------------------------------------------------------------------------


def _cost(entries: Iterable[CashEntry], k: Consequence) -> Fraction:
    acc = Fraction(0)
    for e in entries:
        if e.kind == k:
            acc = acc + e.amount
    return acc


def _cost_total(entries: Tuple[CashEntry, ...]) -> Fraction:
    acc = Fraction(0)
    for k in ALL_CONS:
        acc = acc + _cost(entries, k)
    return acc


def _cash_total(entries: Tuple[CashEntry, ...]) -> Fraction:
    acc = Fraction(0)
    for e in entries:
        acc = acc + e.amount
    return acc


def _integral(role: Role, entries: Tuple[CashEntry, ...]) -> Fraction:
    acc = Fraction(0)
    for k in ALL_CONS:
        acc = acc + CONSEQUENCE_VALUATION[(role, k)] * _cost(entries, k)
    return acc


def _legal_payoff(role: Role, status: LegalStatus) -> Fraction:
    acc = Fraction(0)
    for c in DECLARED_CONSEQUENCES[status]:
        acc = acc + CONSEQUENCE_VALUATION[(role, c)]
    return acc


def _status_entries(status: LegalStatus) -> Tuple[CashEntry, ...]:
    return tuple(CashEntry(0, c, Fraction(1), False)
                 for c in DECLARED_CONSEQUENCES[status])


# ---------------------------------------------------------------------------
# Inline semantic re-derivations — needle 48
# ---------------------------------------------------------------------------


def _view(as_of: int, ledger) -> Tuple[Tuple[int, str], ...]:
    out = []
    for e in ledger:
        if e[0] <= as_of:
            out.append(e)
    return tuple(out)


def _occurs(as_of: int, ledger, atom: str) -> bool:
    for e in _view(as_of, ledger):
        if e[1] == atom:
            return True
    return False


def _material(atom: str) -> bool:
    for m in MAT_ATOMS:
        if m == atom:
            return True
    return False


def _docket(as_of: int, ledger) -> FrozenSet[str]:
    onfile = set()
    for m in MAT_ATOMS:
        if _occurs(as_of, ledger, m):
            onfile.add(m)
    return frozenset(onfile)


def _holds(atom: str, docket: FrozenSet[str]) -> bool:
    if not _material(atom):
        return False
    return atom in docket


def _closure(docket: FrozenSet[str]) -> FrozenSet[str]:
    derived = set(docket)
    frontier = True
    while frontier:
        frontier = False
        for r in FAMILY_RULES:
            if r.conclusion in derived:
                continue
            ok = True
            for p in r.premises:
                if p not in derived:
                    ok = False
                    break
            if ok:
                derived.add(r.conclusion)
                frontier = True
    return frozenset(derived)


def _eval(atom: str, ledger, as_of: int) -> bool:
    return atom in _closure(_docket(as_of, ledger))


# ---------------------------------------------------------------------------
# Public differential checks — needle 28
# ---------------------------------------------------------------------------


def check_total_preservation(entries: Tuple[CashEntry, ...],
                             reported_cost_total: Fraction,
                             reported_cash_total: Fraction) -> CheckReport:
    """Layer 1->2: aggregation preserves the unweighted total, and both
    reported totals match the inline recomputation."""

    problems = []
    if _cost_total(entries) != _cash_total(entries):
        problems.append("cost total != cash total — aggregation lost amount")
    if reported_cost_total != _cost_total(entries):
        problems.append(f"cost total mismatch: {reported_cost_total}")
    if reported_cash_total != _cash_total(entries):
        problems.append(f"cash total mismatch: {reported_cash_total}")
    if problems:
        return CheckReport.fail(*problems)
    return CheckReport.pass_()


def check_image_preservation(entries: Tuple[CashEntry, ...]) -> CheckReport:
    """Layer 1->2 image half: every nonzero cost component's kind is the
    kind of some entry (the reverse direction legitimately fails under
    netting — that boundary is asserted separately)."""

    problems = []
    for k in ALL_CONS:
        if _cost(entries, k) != 0:
            witnessed = any(e.kind == k for e in entries)
            if not witnessed:
                problems.append(f"nonzero cost at {k} without any entry of that kind")
    if problems:
        return CheckReport.fail(*problems)
    return CheckReport.pass_()


def check_integral_covariance(role: Role, entry: CashEntry,
                              entries_before: Tuple[CashEntry, ...],
                              reported_before: Fraction,
                              reported_after: Fraction) -> CheckReport:
    """Layer 2->3 covariance: adding one entry moves the integral by exactly
    valuation(role, kind) * amount, and the reported readings match."""

    problems = []
    expected_before = _integral(role, entries_before)
    expected_after = _integral(role, (entry,) + entries_before)
    delta = CONSEQUENCE_VALUATION[(role, entry.kind)] * entry.amount
    if expected_after != expected_before + delta:
        problems.append("inline covariance broken (internal inconsistency)")
    if reported_before != expected_before or reported_after != expected_after:
        problems.append(
            f"reported readings mismatch: {reported_before}/{reported_after}")
    if problems:
        return CheckReport.fail(*problems)
    return CheckReport.pass_()


def check_status_reading_grid(reported: Dict[Tuple[Role, LegalStatus], Fraction],
                              readings_on_status_flows:
                              Dict[Tuple[Role, LegalStatus], Fraction]) -> CheckReport:
    """Layer 3->4: on every status vector the preference integral equals the
    anchor payoff reading (all 8 grid cells derived, none hardcoded)."""

    problems = []
    for role in (Role.CLAIMANT, Role.RESPONDENT):
        for status in (LegalStatus.UPHELD, LegalStatus.PARTIALLY_UPHELD,
                       LegalStatus.DISMISSED, LegalStatus.UNENFORCEABLE):
            expected = _legal_payoff(role, status)
            integral = _integral(role, _status_entries(status))
            if integral != expected:
                problems.append(
                    f"status-vector integral != payoff at ({role}, {status})")
            if reported.get((role, status)) != expected:
                problems.append(
                    f"reported payoff mismatch at ({role}, {status}): "
                    f"{reported.get((role, status))}")
            if readings_on_status_flows.get((role, status)) != integral:
                problems.append(
                    f"reported status-flow reading mismatch at ({role}, {status})")
    if problems:
        return CheckReport.fail(*problems)
    return CheckReport.pass_()


def check_docket_blindness(role: Role, status: LegalStatus,
                           d1: bool, d2: bool,
                           reading_d1: Fraction, reading_d2: Fraction) -> CheckReport:
    """Layer 4 docket blindness: the anchor reading depends on the status
    projection only (consumed anchor theorem, recomputed inline)."""

    if _legal_payoff(role, status) == _legal_payoff(role, status) and \
            reading_d1 == _legal_payoff(role, status) and \
            reading_d2 == _legal_payoff(role, status):
        return CheckReport.pass_()
    return CheckReport.fail(
        f"payoff reading moved with the docket bit: {reading_d1} vs {reading_d2}")


def check_reflection(role: Role, entries: Tuple[CashEntry, ...],
                     e1: CashEntry, e2: CashEntry,
                     equal_readings: bool,
                     reported_amounts_equal: bool) -> CheckReport:
    """End-to-end reflection: same kind, nonzero weight, equal readings
    imply equal amounts; at a zero-weight kind the implication must fail
    when amounts differ."""

    problems = []
    w = CONSEQUENCE_VALUATION[(role, e1.kind)]
    r1 = _integral(role, (e1,) + entries)
    r2 = _integral(role, (e2,) + entries)
    if equal_readings != (r1 == r2):
        problems.append("reported reading equality mismatch")
    if w != 0:
        # reflection must hold
        if r1 == r2 and e1.amount != e2.amount:
            problems.append("reflection failed at a nonzero-weight kind")
        if r1 == r2 and not reported_amounts_equal:
            problems.append("reflection not reported")
    else:
        # zero-weight boundary: reflection is NOT required
        if e1.amount != e2.amount and r1 == r2 and reported_amounts_equal:
            problems.append("reflection claimed at a zero-weight kind")
    if problems:
        return CheckReport.fail(*problems)
    return CheckReport.pass_()


def check_status_projection_drops_cash(fl1: PayFlow, fl2: PayFlow) -> CheckReport:
    """Counterexample differential: two flows with identical status
    projections (what the old encoding can see) yet different readings."""

    problems = []
    if fl1.declared_status != fl2.declared_status or fl1.docket != fl2.docket:
        problems.append("counterexample flows differ in the status projection")
    if _integral(Role.CLAIMANT, fl1.entries) == _integral(Role.CLAIMANT, fl2.entries):
        problems.append("counterexample flows have equal readings — vacuous")
    if problems:
        return CheckReport.fail(*problems)
    return CheckReport.pass_()


def check_old_anchor_independence(payoff_f1: Fraction, payoff_f2: Fraction,
                                  reading_f1: Fraction,
                                  reading_f2: Fraction) -> CheckReport:
    """The old status congruence still holds (anchor payoff equal) while the
    cash side moves (readings differ) — the constructive 'independent
    preservations' repair."""

    if payoff_f1 == payoff_f2 and reading_f1 != reading_f2:
        return CheckReport.pass_()
    return CheckReport.fail(
        "old-anchor/payoff-chain independence not witnessed: "
        f"payoffs {payoff_f1}/{payoff_f2}, readings {reading_f1}/{reading_f2}")


# ---------------------------------------------------------------------------
# Public differential checks — needle 48
# ---------------------------------------------------------------------------


def check_use_point(rule: LawRule, ledger, as_of: int) -> CheckReport:
    """Per-rule use point: every premise material read on the docket equals
    its view read, and every premise atom is a material atom."""

    problems = []
    docket = _docket(as_of, ledger)
    for p in rule.premises:
        if not _material(p):
            problems.append(f"premise {p} is not a material atom")
            continue
        if _holds(p, docket) != _occurs(as_of, ledger, p):
            problems.append(f"use point broken at premise {p}")
    if problems:
        return CheckReport.fail(*problems)
    return CheckReport.pass_()


def check_future_blindness(rule: LawRule, ledger, future,
                           as_of: int) -> CheckReport:
    """Per-rule non-anticipation: appending events dated after as_of leaves
    the rule body's evaluation unchanged (recomputed inline on both sides)."""

    problems = []
    for x in future:
        if not as_of < x[0]:
            problems.append(f"future event {x} is not after the cut")
    appended = tuple(ledger) + tuple(future)
    if _eval(rule.conclusion, appended, as_of) != _eval(rule.conclusion, ledger, as_of):
        problems.append(f"rule {rule.rid} evaluation moved under future events")
    if problems:
        return CheckReport.fail(*problems)
    return CheckReport.pass_()


def check_blocked_when_missing(rule: LawRule, ledger, as_of: int,
                               missing_atom: str) -> CheckReport:
    """Out-of-window rejection: with the given material absent from the
    view, the rule conclusion is NOT derivable in the rule network."""

    problems = []
    if _occurs(as_of, ledger, missing_atom):
        problems.append(f"atom {missing_atom} is in the view — gate vacuous")
    if _eval(rule.conclusion, ledger, as_of):
        problems.append(
            f"rule {rule.rid} fired despite missing premise material")
    if problems:
        return CheckReport.fail(*problems)
    return CheckReport.pass_()


def check_eval_is_view_valued(atom: str, ledger, as_of: int) -> CheckReport:
    """The old anchor's hview premise as a checked fact here: the evaluation
    equals the evaluation on the pre-truncated ledger."""

    view_only = _view(as_of, ledger)
    if _eval(atom, ledger, as_of) == _eval(atom, view_only, as_of):
        return CheckReport.pass_()
    return CheckReport.fail("evaluation is not view-valued")
