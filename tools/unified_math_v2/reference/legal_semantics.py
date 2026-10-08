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


def _claim_key(predicate: str, polar: Polar, subject: str = "") -> str:
    while predicate.startswith("~"):
        predicate = predicate[1:]
        polar = Polar.NEG if polar is Polar.POS else Polar.POS
    core = f"{len(subject)}|{subject}|{predicate}"
    return core if polar is Polar.POS else "~" + core


def _inline_candidates(case: CaseInput, env: LegalEnvironment):
    day = case.initial_state.as_of_day
    jurisdiction = env.jurisdiction.route.value
    case_stages = {s for _p, s in case.initial_state.stages}
    stage = next(iter(case_stages)) if len(case_stages) == 1 else ""
    out = []
    for rule in env.rules:
        if rule.validity is None:
            out.append(rule.rule_id)
            continue
        jur, stages, _matters, lo, hi = rule.validity
        if jur != jurisdiction:
            continue
        if stages and stage not in stages:
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


def _inline_universe_nodes(case: CaseInput, env: LegalEnvironment,
                           selection=frozenset()):
    """(node_id, claim, is_strong) triples — the checker's own reading of
    the fragment's construction rules: facts are W-DIRECT only; bases
    create no nodes; StrongBasis comes ONLY from named sufficiency
    templates whose premises are admitted, whose named failures are
    unmet, and whose license rule is inside the selection."""

    nodes = []
    for f in case.fact_records:
        if f.standing is FactStanding.ADMITTED_POSITIVE:
            nodes.append(
                (f"fact:{f.fact_id}",
                 _claim_key(f.proposition.predicate, f.proposition.polar,
                            f.proposition.subject),
                 False))
    admitted_predicates = {
        f.proposition.predicate for f in case.fact_records
        if f.standing is FactStanding.ADMITTED_POSITIVE
    }
    admitted_positive_predicates = {
        f.proposition.predicate for f in case.fact_records
        if f.standing is FactStanding.ADMITTED_POSITIVE
        and f.proposition.polar is Polar.POS
    }
    negated_predicates = {
        f.proposition.predicate for f in case.fact_records
        if f.standing is FactStanding.EXPLICIT_NEGATION
    }
    admitted_keys = {
        (f.proposition.predicate, f.proposition.polar, f.proposition.issue)
        for f in case.fact_records
        if f.standing is FactStanding.ADMITTED_POSITIVE
    }
    for template in env.strong_templates:
        if template.license_rule_id and template.license_rule_id not in selection:
            continue
        scope = template.scope_issue

        def _matches(pred, scope=scope):
            if scope:
                return (pred, Polar.POS, scope) in admitted_keys or (
                    (pred, Polar.POS, "") in admitted_keys
                )
            return any(
                k[0] == pred and k[1] is Polar.POS for k in admitted_keys
            )

        if not all(_matches(p) for p in template.premise_predicates):
            continue
        # failure EVENTS are POS-polarity admitted positives
        # (round-2 defect 1 + round-3 N2)
        if any(p in admitted_positive_predicates
               for p in template.failure_predicates):
            continue
        nodes.append(
            (f"template:{template.template_id}",
             _claim_key(template.conclusion_predicate, Polar.POS,
                        template.subject),
             True)
        )
    # mirror the counter-evidence profile (W-MATERIAL / W-ALT nodes)
    from unified.standards import counter_reason_nodes
    for r in counter_reason_nodes(getattr(env, "counter_evidences", ())):
        nodes.append((r.node_id, r.claim, r.kind.value == "W-MATERIAL"))
    return tuple(nodes)


_SPECIAL_KINDS = frozenset({
    "JUDICIAL_ADMISSION", "FORENSIC_EXEMPT", "FINAL_BINDING",
    "EVIDENCE_OBSTRUCTION",
})


def _inline_special_establishments(case: CaseInput, env: LegalEnvironment,
                                   selection=frozenset()):
    """The checker's own re-derivation of the special channels."""

    admitted = {
        f.fact_id for f in case.fact_records
        if f.standing is FactStanding.ADMITTED_POSITIVE
    }
    out = set()
    for basis in env.admission_bases:
        if basis.kind.value not in _SPECIAL_KINDS:
            continue
        if basis.license_rule_id and basis.license_rule_id not in selection:
            continue
        if not basis.premise_refs or not all(r in admitted for r in basis.premise_refs):
            continue
        # block references name admitted revocation/defeat events
        if any(b in admitted for b in basis.block_refs):
            continue
        out.add(basis.issue_id)
    return frozenset(out)


def _inline_civil_high(
    claim: str,
    in_nodes: FrozenSet[str],
    out_nodes: FrozenSet[str],
    universe_nodes,
) -> bool:
    """CivilHigh := an In strong node for the claim and no live counter.
    A counter here is a strong node for the exact contrary claim."""

    contrary = (
        claim[1:] if claim.startswith("~") else "~" + claim
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
    problems: list = []

    for branch in actual.branches:
        if not _inline_stable(branch.selection, candidates, exclusions):
            problems.append(f"unstable selection {sorted(branch.selection)}")
        universe_nodes = _inline_universe_nodes(case, env, branch.selection)
        special = _inline_special_establishments(case, env, branch.selection)
        node_ids = {n for n, _c, _s in universe_nodes}
        # extension: the fragment reports In via branch.extension
        in_nodes = frozenset(n for n in branch.extension if n in node_ids)
        if in_nodes != frozenset(branch.extension):
            problems.append("extension names unknown nodes")
        # Out re-derivation (obligation 5): in the fragment the graph
        # edges are the contrary-claim rebuttals, so a node is Out when
        # some In node holds a contrary claim.
        claims_of = {n: c for n, c, _s in universe_nodes}

        def _contrary(a, b):
            return a == ("~" + b[1:] if b.startswith("~") else "~" + b) or                 b == ("~" + a[1:] if a.startswith("~") else "~" + a)

        out_nodes = frozenset(
            n for n in node_ids
            if any(_contrary(claims_of[s], claims_of[n]) for s in in_nodes)
        )
        # burden readiness and need, re-derived from materials
        stages = {s for _p, s in case.initial_state.stages}
        window_closed = any(
            f.proposition.predicate == "evidence_window_closed"
            and f.standing is FactStanding.ADMITTED_POSITIVE
            for f in case.fact_records
        )
        stage_ready = bool(stages) and bool(
            stages & {"trial", "ready_for_decision", "decided"}
        )
        burden_ready = (
            bool(stages) and stages <= {"ready_for_decision", "decided", "trial"}
        ) or window_closed
        referenced_ids = set()
        for basis in env.admission_bases:
            referenced_ids.update(basis.premise_refs)
            referenced_ids.update(basis.block_refs)
        need = any(
            f.standing in (FactStanding.NOT_SUBMITTED, FactStanding.AWAITING_ADMISSION)
            and f.fact_id in referenced_ids
            for f in case.fact_records
        )
        fact_ids = {f.fact_id for f in case.fact_records}
        exhausted4 = all(
            all(r in fact_ids for r in basis.premise_refs)
            and all(b in fact_ids for b in basis.block_refs)
            for basis in env.admission_bases
        )
        for claim, outcome in zip(case.claims, branch.standards):
            expected_high = _inline_civil_high(
                _claim_key(claim.basis, Polar.POS, claim.subject),
                in_nodes, out_nodes, universe_nodes,
            )
            if outcome.civil_high != expected_high:
                problems.append(
                    f"standard mismatch for {claim.claim_id}: "
                    f"reported {outcome.civil_high}, inline {expected_high}"
                )
        # blockers re-derived: a defense blocks when its issue is strong
        # In or specially established
        expected_blockers = frozenset(
            d.defense_id for d in case.defenses
            if _inline_civil_high(
                _claim_key(d.basis, Polar.POS, d.subject),
                in_nodes, out_nodes, universe_nodes,
            ) or d.basis in special
        )
        for claim, outcome, finalization in zip(
            case.claims, branch.standards, branch.finalizations
        ):
            blocked = bool(expected_blockers)
            established = outcome.civil_high or claim.basis in special
            burden_ready_effective = burden_ready and not need
            if not stage_ready:
                expected = Judgment.PENDING
                expected_basis = "NOT_READY"
            elif blocked:
                expected = Judgment.NOT_ESTABLISHED
                expected_basis = "NEG_BLOCKED"
            elif established:
                expected = Judgment.ESTABLISHED
                expected_basis = "POS"
            elif burden_ready_effective:
                expected = Judgment.NOT_ESTABLISHED
                expected_basis = "NEG_BURDEN"
            elif exhausted4 and need:
                expected = Judgment.PENDING
                expected_basis = "LEGALLY_UNDETERMINED"
            else:
                expected = Judgment.PENDING
                expected_basis = "GAP"
            if finalization.judgment is not expected:
                problems.append(
                    f"finalization mismatch for {claim.claim_id}: "
                    f"{finalization.judgment} vs {expected}"
                )
            if getattr(finalization, "basis", None) is not None and                     finalization.basis.value != expected_basis:
                problems.append(
                    f"basis mismatch for {claim.claim_id}: "
                    f"{finalization.basis.value} vs {expected_basis}"
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
    def _effective_outstanding(ledger, key):
        titles = tuple(
            e for e in ledger
            if e.kind is LedgerEntryKind.TITLE_ENTITLEMENT and e.basis_key == key
        )
        dead = {sid for e in titles for sid in e.supersedes}
        entitled = sum(
            (e.amount for e in titles if e.entry_id not in dead), Fraction(0)
        )
        paid = sum(
            (e.amount for e in ledger
             if e.kind is LedgerEntryKind.SATISFIED and e.basis_key == key),
            Fraction(0),
        )
        return max(entitled - paid, Fraction(0))

    keys = {e.basis_key for e in state.ledger if e.basis_key}
    for key in keys:
        if ";" in key or key == "unallocated":
            continue
        if _effective_outstanding(actual_state.ledger, key) !=                 _effective_outstanding(state.ledger, key):
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
        single = len(pe.debt_order) == 1
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
            titles = tuple(
                e for e in state.ledger
                if e.kind is LedgerEntryKind.TITLE_ENTITLEMENT
                and e.basis_key == key
            )
            dead = {sid for e in titles for sid in e.supersedes}
            entitled = sum(
                (e.amount for e in titles if e.entry_id not in dead),
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
            gross_amount = pe.amount if single else alloc
            if gross_amount > 0:
                entries.append(
                    LedgerEntry(
                        entry_id=f"gross-alloc:i:{pe.event.event_id}:{key}",
                        kind=LedgerEntryKind.GROSS_ALLOCATED,
                        basis_key=key, obligor="", proceeding="",
                        amount=gross_amount, event_ref=pe.event.event_id,
                        at_day=pe.event.occurred_at,
                    )
                )
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
        if not single and remaining > 0:
            entries.append(
                LedgerEntry(
                    entry_id=f"gross-alloc:i:{pe.event.event_id}:unallocated",
                    kind=LedgerEntryKind.GROSS_ALLOCATED,
                    basis_key="unallocated", obligor="", proceeding="",
                    amount=remaining, event_ref=pe.event.event_id,
                    at_day=pe.event.occurred_at,
                )
            )
        return replace(state, ledger=state.ledger + tuple(entries),
                       events=state.events + (pe.event,))
    if pe.kind.value == "AWARD_EFFECTIVE":
        if not pe.authority_ref or pe.amount is None or not pe.basis_key:
            return replace(state, events=state.events + (pe.event,))
        return replace(
            state,
            ledger=state.ledger + (
                LedgerEntry(
                    entry_id=f"title:i:{pe.event.event_id}",
                    kind=LedgerEntryKind.TITLE_ENTITLEMENT,
                    basis_key=pe.basis_key, obligor="", proceeding="",
                    amount=pe.amount, event_ref=pe.event.event_id,
                    at_day=pe.event.occurred_at,
                ),
            ),
            events=state.events + (pe.event,),
        )
    if pe.kind.value == "AWARD_REVOKED":
        prior = tuple(
            e for e in state.ledger
            if e.kind is LedgerEntryKind.TITLE_ENTITLEMENT
            and e.basis_key == pe.basis_key
        )
        return replace(
            state,
            ledger=state.ledger + (
                LedgerEntry(
                    entry_id=f"title:i:{pe.event.event_id}",
                    kind=LedgerEntryKind.TITLE_ENTITLEMENT,
                    basis_key=pe.basis_key, obligor="", proceeding="",
                    amount=Fraction(0), event_ref=pe.event.event_id,
                    at_day=pe.event.occurred_at,
                    supersedes=tuple(e.entry_id for e in prior),
                ),
            ),
            events=state.events + (pe.event,),
        )
    # other fragment kinds: only the history grows
    return replace(state, events=state.events + (pe.event,))
