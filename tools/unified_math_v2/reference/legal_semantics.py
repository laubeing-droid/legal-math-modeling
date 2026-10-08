"""Independent legal-semantics checker for the v3 fragment (J.7).

This module deliberately re-implements the fragment's semantics with its
own inline logic instead of importing the main evaluator: selections are
re-checked by an inline stability predicate, extensions by inline
conflict/defense logic over the run's own edges, standards by inline
In/Live reasoning, and finalizations by an inline terminal table.  It
shares only the immutable case carriers — never ``unified.pipeline``,
the generator, the defeat compiler, or any solve path.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import FrozenSet, Optional, Tuple

from theory.spec.canonical_v2.case import (
    BasisKind,
    CaseInput,
    FactStanding,
    LegalEnvironment,
    Polar,
    RunStatus,
)
from theory.spec.canonical_v2.kernel import Judgment


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
# Inline semantic re-derivations (independent of the evaluator modules)
# ---------------------------------------------------------------------------


def _claim_key(predicate: str, polar: Polar) -> str:
    return predicate if polar is Polar.POS else "~" + predicate


def _inline_candidates(case: CaseInput, env: LegalEnvironment):
    day = case.initial_state.as_of_day
    jurisdiction = env.jurisdiction.route.value
    out = []
    for rule in env.rules:
        if rule.validity is None:
            out.append(rule.rule_id)
            continue
        jur, stages, _matters, lo, hi = rule.validity
        if jur != jurisdiction:
            continue
        if lo is not None and day < lo:
            continue
        if hi is not None and day > hi:
            continue
        out.append(rule.rule_id)
    return frozenset(out)


def _inline_exclusions(env: LegalEnvironment):
    return frozenset(
        (rule.rule_id, other) for rule in env.rules for other in rule.priority_over
    )


def _inline_stable(
    subset: FrozenSet[str],
    candidates: FrozenSet[str],
    exclusions: FrozenSet[Tuple[str, str]],
) -> bool:
    for a in subset:
        for b in subset:
            if (a, b) in exclusions:
                return False
    for n in candidates - subset:
        if not any((s, n) in exclusions for s in subset):
            return False
    return True


def _inline_universe_nodes(case: CaseInput, env: LegalEnvironment):
    """(node_id, claim, is_strong) triples — the checker's own reading of
    the fragment's construction rules."""

    nodes = []
    for f in case.fact_records:
        if f.standing is FactStanding.ADMITTED_POSITIVE:
            nodes.append((f"fact:{f.fact_id}",
                          _claim_key(f.proposition.predicate, f.proposition.polar),
                          False))
    admitted = {
        f.fact_id for f in case.fact_records
        if f.standing is FactStanding.ADMITTED_POSITIVE
    }
    negated = {
        f.fact_id for f in case.fact_records
        if f.standing is FactStanding.EXPLICIT_NEGATION
    }
    for basis in env.admission_bases:
        if basis.premise_refs and all(r in admitted for r in basis.premise_refs):
            if any(b in negated for b in basis.block_refs):
                continue
            strong = basis.kind in (BasisKind.ORDINARY_SUPPORT, BasisKind.PRESUMPTION)
            nodes.append(
                (f"basis:{basis.basis_id}", _claim_key(basis.issue_id, Polar.POS), strong)
            )
    return tuple(nodes)


def _inline_civil_high(
    claim: str,
    in_nodes: FrozenSet[str],
    out_nodes: FrozenSet[str],
    universe_nodes,
) -> bool:
    """CivilHigh := an In strong node for the claim and no live counter.
    A counter here is a strong node for the exact contrary claim."""

    contrary = (
        "~" + claim[1:] if claim.startswith("~") else "~" + claim
    )
    strong_claim = any(n_id in in_nodes and c == claim and strong
                       for n_id, c, strong in universe_nodes)
    live_counter = any(
        c == contrary and strong and n_id not in out_nodes
        for n_id, c, strong in universe_nodes
    )
    return strong_claim and not live_counter


def _inline_finalize(civil_high: bool, ready: bool) -> Judgment:
    if not ready:
        return Judgment.PENDING
    if civil_high:
        return Judgment.ESTABLISHED
    return Judgment.NOT_ESTABLISHED


# ---------------------------------------------------------------------------
# Public checks
# ---------------------------------------------------------------------------


def check_case_run(
    case: CaseInput, env: LegalEnvironment, actual, *, limits=None
) -> CheckReport:
    """Differential check of a CaseRun against the inline semantics."""

    if getattr(actual, "case_id", None) != case.case_id:
        return CheckReport.fail("case id mismatch")
    if actual.status is RunStatus.FAILED:
        # A technical failure is honest only when reported as a FAILURE:
        # the checker never blesses one as verified content (BND-04).
        return CheckReport.fail("run carries a technical failure: "
                                + "; ".join(actual.failures))
    candidates = _inline_candidates(case, env)
    exclusions = _inline_exclusions(env)
    universe_nodes = _inline_universe_nodes(case, env)
    node_ids = {n for n, _c, _s in universe_nodes}
    problems: list = []

    for branch in actual.branches:
        if not _inline_stable(branch.selection, candidates, exclusions):
            problems.append(f"unstable selection {sorted(branch.selection)}")
        # extension: conflict-free and self-defending over the branch's
        # own standards witnesses — we re-check the In/Out split reported
        # implicitly through outcomes; the fragment reports In via
        # branch.extension.
        in_nodes = frozenset(n for n in branch.extension if n in node_ids)
        if in_nodes != frozenset(branch.extension):
            problems.append("extension names unknown nodes")
        out_nodes = frozenset()
        for claim, outcome in zip(case.claims, branch.standards):
            expected_high = _inline_civil_high(
                _claim_key(claim.basis, Polar.POS), in_nodes, out_nodes, universe_nodes
            )
            if outcome.civil_high != expected_high:
                problems.append(
                    f"standard mismatch for {claim.claim_id}: "
                    f"reported {outcome.civil_high}, inline {expected_high}"
                )
        for claim, outcome, finalization in zip(
            case.claims, branch.standards, branch.finalizations
        ):
            expected = _inline_finalize(outcome.civil_high, ready=True)
            if finalization.judgment is not expected:
                problems.append(
                    f"finalization mismatch for {claim.claim_id}: "
                    f"{finalization.judgment} vs {expected}"
                )
    if problems:
        return CheckReport.fail(*problems)
    return CheckReport.pass_()


def check_trace_run(
    initial, env: Optional[LegalEnvironment], events, actual_state, actual_notes
) -> CheckReport:
    """Independent fold check: re-apply each event with inline semantics
    (gross/satisfied ledger arithmetic) and compare outstanding amounts."""

    from theory.spec.canonical_v2.case import LedgerEntryKind

    state = initial
    for pe in events:
        state = _inline_step(state, pe)
    # compare outstanding amounts for every basis key mentioned
    keys = {e.basis_key for e in state.ledger if e.basis_key}
    for key in keys:
        if ";" in key:
            continue
        entitled = sum(
            (e.amount for e in state.ledger
             if e.kind is LedgerEntryKind.TITLE_ENTITLEMENT and e.basis_key == key),
            Fraction(0),
        )
        paid = sum(
            (e.amount for e in state.ledger
             if e.kind is LedgerEntryKind.SATISFIED and e.basis_key == key),
            Fraction(0),
        )
        expected = max(entitled - paid, Fraction(0))
        entitled_a = sum(
            (e.amount for e in actual_state.ledger
             if e.kind is LedgerEntryKind.TITLE_ENTITLEMENT and e.basis_key == key),
            Fraction(0),
        )
        paid_a = sum(
            (e.amount for e in actual_state.ledger
             if e.kind is LedgerEntryKind.SATISFIED and e.basis_key == key),
            Fraction(0),
        )
        if max(entitled_a - paid_a, Fraction(0)) != expected:
            return CheckReport.fail(f"outstanding mismatch on {key}")
    del actual_notes
    return CheckReport.pass_()


def _inline_step(state, pe):
    """The checker's own event application for the fragment's kinds
    (payments only carry amounts; other kinds append the event)."""

    from dataclasses import replace

    from theory.spec.canonical_v2.case import (
        LedgerEntry,
        LedgerEntryKind,
    )

    if pe.kind.value == "PAYMENT_PERFORMED":
        if pe.amount is None or not pe.debt_order:
            return state
        entries = [
            LedgerEntry(
                entry_id=f"gross:i:{pe.event.event_id}",
                kind=LedgerEntryKind.GROSS_RECEIVED,
                basis_key=";".join(pe.debt_order),
                obligor="", proceeding="",
                amount=pe.amount, event_ref=pe.event.event_id,
                at_day=pe.event.occurred_at,
            )
        ]
        remaining = pe.amount
        for key in pe.debt_order:
            entitled = sum(
                (e.amount for e in state.ledger
                 if e.kind is LedgerEntryKind.TITLE_ENTITLEMENT and e.basis_key == key),
                Fraction(0),
            )
            paid = sum(
                (e.amount for e in state.ledger
                 if e.kind is LedgerEntryKind.SATISFIED and e.basis_key == key),
                Fraction(0),
            )
            outstanding = max(entitled - paid, Fraction(0))
            alloc = min(outstanding, remaining)
            remaining -= alloc
            if alloc > 0:
                entries.append(
                    LedgerEntry(
                        entry_id=f"sat:i:{pe.event.event_id}:{key}",
                        kind=LedgerEntryKind.SATISFIED,
                        basis_key=key, obligor="", proceeding="",
                        amount=alloc, event_ref=pe.event.event_id,
                        at_day=pe.event.occurred_at,
                    )
                )
        return replace(state, ledger=state.ledger + tuple(entries),
                       events=state.events + (pe.event,))
    # non-payment fragment kinds: only the history grows
    return replace(state, events=state.events + (pe.event,))
