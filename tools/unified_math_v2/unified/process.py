"""Actions, equilibria, settlement, and the event step semantics
(plan §8–§9; J.6.7–J.6.8).

* Attempt actions: ``PhysActions`` is the shared attempt menu (signing,
  paying, breaching — illegal acts included); ``Permitted`` is a separate
  derived subset.  Information sets carry identical nonempty menus —
  the menu itself must not leak hidden state.  Strategies read the
  information set only.
* Equilibria: exact rational verification of a candidate mixed profile
  against EVERY pure deviation (sufficient by convexity) and exact
  maximum regret; finding all equilibria is the CAD route's job (J.0),
  never pretended here.
* Settlement: the individual-rational intersection with the legal set;
  empty is reported as empty, midpoint defaults are never invented.
* Step semantics (§9.1): ActualIssued / Effective / LegallyCorrect /
  Final are four separate relations; payments update the gross/satisfied
  ledger through the waterfall; evidence updates touch only visibility;
  norm-environment changes require an authorized event — an unauthorized
  proposal leaves the environment bit-for-bit identical.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from fractions import Fraction
from typing import Callable, Dict, FrozenSet, Iterable, Mapping, Optional, Sequence, Tuple

from theory.spec.canonical_v2.case import (
    CaseEvent,
    EvidenceRecord,
    ExecutionLimits,
    LegalEnvironment,
    LedgerEntry,
    LedgerEntryKind,
    ProcessState,
)
from theory.spec.canonical_v2.kernel import NormState

from .quantities import allocate_payment, Allocation


# ---------------------------------------------------------------------------
# §8.1 attempt actions and information sets
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class AttemptAction:
    action_id: str
    actor: str
    kind: str  # sign | pay | perform | breach | file | appeal | …
    object_ref: str = ""
    permitted: Optional[bool] = None  # None = undecided; never an input answer

    def __post_init__(self) -> None:
        if not self.action_id or not self.actor or not self.kind:
            raise ValueError("attempt action requires id, actor and kind")


@dataclass(frozen=True)
class InformationSet:
    """The actor's observation history; identity is (actor, view)."""

    actor: str
    view: Tuple[str, ...]  # ordered observation keys the actor saw

    def __post_init__(self) -> None:
        if not self.actor:
            raise ValueError("information set requires an actor")


class GameWorld:
    """Finite attempt-action world: menus keyed by information set."""

    def __init__(self, menus: Mapping[Tuple[str, Tuple[str, ...]], Tuple[AttemptAction, ...]]):
        for key, menu in menus.items():
            if not menu:
                raise ValueError(f"menu for {key} is empty — it would leak state")
            if any(a.actor != key[0] for a in menu):
                raise ValueError("menu actions must belong to the information set's actor")
        self._menus = dict(menus)

    def menu(self, info: InformationSet) -> Tuple[AttemptAction, ...]:
        return self._menus.get((info.actor, info.view), ())

    def phys_actions(self, actor: str) -> FrozenSet[str]:
        return frozenset(
            a.action_id
            for (act, _view), menu in self._menus.items()
            if act == actor
            for a in menu
        )


@dataclass(frozen=True)
class NormalFormGame:
    """Finite strategic game over attempt actions with rational payoffs.
    Descriptive games may include illegal actions with their real
    consequences; the legality mark rides on the action, not here."""

    players: Tuple[str, ...]
    actions: Tuple[Tuple[str, ...], ...]  # per player, ordered
    payoffs: Mapping[Tuple[str, ...], Tuple[Fraction, ...]]  # profile -> utils

    def __post_init__(self) -> None:
        if len(self.players) != len(self.actions):
            raise ValueError("one action tuple per player")
        for profile, utils in self.payoffs.items():
            if len(profile) != len(self.players) or len(utils) != len(self.players):
                raise ValueError("profile arity mismatch")
            if not all(type(u) is Fraction for u in utils):
                raise TypeError("payoffs must be Fractions")
        for profile in self.payoffs:
            for i, a in enumerate(profile):
                if a not in self.actions[i]:
                    raise ValueError(f"action {a} not in player {i}'s menu")


def mixed_payoff(
    game: NormalFormGame,
    sigma: Sequence[Sequence[Fraction]],
) -> Tuple[Fraction, ...]:
    """Exact expected utility of a mixed profile."""

    total = [Fraction(0) for _ in game.players]
    for profile, utils in game.payoffs.items():
        prob = Fraction(1)
        for i, a in enumerate(profile):
            prob *= sigma[i][game.actions[i].index(a)]
        for i, u in enumerate(utils):
            total[i] += prob * u
    return tuple(total)


def deviation_gains(
    game: NormalFormGame,
    sigma: Sequence[Sequence[Fraction]],
) -> Dict[Tuple[int, str], Fraction]:
    """Exact gain of every PURE unilateral deviation (u(deviate) − u(σ))."""

    base = mixed_payoff(game, sigma)
    gains: Dict[Tuple[int, str], Fraction] = {}
    for i, actions in enumerate(game.actions):
        for pure in actions:
            sigma_p = [list(row) for row in sigma]
            for j, a in enumerate(actions):
                sigma_p[i][j] = Fraction(1) if a == pure else Fraction(0)
            deviated = mixed_payoff(game, sigma_p)
            gains[(i, pure)] = deviated[i] - base[i]
    return gains


def verify_equilibrium(
    game: NormalFormGame,
    sigma: Sequence[Sequence[Fraction]],
    eps: Fraction = Fraction(0),
) -> bool:
    """Exact ε-equilibrium check: NO pure deviation gains more than ε.
    Pure deviations suffice — any mixed deviation is their convex
    combination (§8.2)."""

    if eps < 0:
        raise ValueError("nonnegative epsilon required")
    for i, row in enumerate(sigma):
        if sum(row, Fraction(0)) != 1 or any(p < 0 for p in row):
            raise ValueError(f"player {i}'s mixed action is not a distribution")
    return all(g <= eps for g in deviation_gains(game, sigma).values())


def max_regret(
    game: NormalFormGame, sigma: Sequence[Sequence[Fraction]]
) -> Tuple[Fraction, Tuple[int, str]]:
    """(maximum deviation gain, its witness) — the G05 regret certificate."""

    gains = deviation_gains(game, sigma)
    (i, pure), gain = max(gains.items(), key=lambda kv: (kv[1], kv[0][0]))
    return gain, (game.players[i], pure)


# ---------------------------------------------------------------------------
# §8.4 settlement zone
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class SettlementZone:
    low: Fraction
    high: Fraction
    empty: bool


def settlement_zone(
    legal_low: Fraction,
    legal_high: Fraction,
    claimant_outside: Fraction,
    respondent_outside: Fraction,
    value_high: Fraction,
) -> SettlementZone:
    """The legal settlement interval intersected with individual
    rationality: s must satisfy u_C(s) ≥ d_C and u_R(V − s) ≥ d_R on a
    zero-sum split of ``value_high``.  An empty zone is reported empty."""

    for name, v in (
        ("legal_low", legal_low), ("legal_high", legal_high),
        ("claimant_outside", claimant_outside),
        ("respondent_outside", respondent_outside),
        ("value_high", value_high),
    ):
        if type(v) is not Fraction:
            raise TypeError(f"{name} must be a Fraction")
    ir_low = claimant_outside                 # s ≥ d_C
    ir_high = value_high - respondent_outside  # s ≤ V − d_R
    lo = max(legal_low, ir_low)
    hi = min(legal_high, ir_high)
    if lo > hi:
        return SettlementZone(lo, hi, True)
    return SettlementZone(lo, hi, False)


# ---------------------------------------------------------------------------
# §9 events and the step relation
# ---------------------------------------------------------------------------


import enum as _enum


class LegalEventKind(_enum.Enum):
    EVIDENCE_SUBMITTED = "EVIDENCE_SUBMITTED"
    EVIDENCE_WITHDRAWN = "EVIDENCE_WITHDRAWN"
    AWARD_ISSUED = "AWARD_ISSUED"            # ActualIssued — may be wrong
    AWARD_EFFECTIVE = "AWARD_EFFECTIVE"      # Effective — authority + form held
    PAYMENT_PERFORMED = "PAYMENT_PERFORMED"
    AWARD_REVOKED = "AWARD_REVOKED"          # supersedes titles on a basis
    NORM_CHANGE_AUTHORIZED = "NORM_CHANGE_AUTHORIZED"
    NORM_CHANGE_PROPOSED = "NORM_CHANGE_PROPOSED"  # never mutates the environment


@dataclass(frozen=True)
class ProcessEvent:
    event: CaseEvent
    kind: LegalEventKind
    basis_key: str = ""
    amount: Optional[Fraction] = None
    debt_order: Tuple[str, ...] = ()  # basis keys in waterfall order
    authority_ref: str = ""


@dataclass(frozen=True)
class StepOutcome:
    """One allowed successor: the step relation is set-valued."""

    next_state: ProcessState
    next_env: Optional[LegalEnvironment]
    notes: Tuple[str, ...] = ()


def _apply_payment(
    state: ProcessState, ev: ProcessEvent
) -> Tuple[ProcessState, Tuple[str, ...]]:
    if ev.amount is None or ev.amount < 0 or not ev.debt_order:
        raise ValueError("payment events carry a nonnegative amount and debt order")
    # One waterfall pass over the declared order (same priority groups
    # expressed by repeated keys in order).
    groups = tuple((k,) for k in ev.debt_order)
    outstanding: list = []
    for key in ev.debt_order:
        paid = sum(
            (
                e.amount
                for e in state.ledger
                if e.kind is LedgerEntryKind.SATISFIED and e.basis_key == key
            ),
            Fraction(0),
        )
        # look up the current entitlement for the basis from the title ledger
        entitled = sum((e.amount for e in effective_titles(state, key)), Fraction(0))
        outstanding.append(max(entitled - paid, Fraction(0)))
    alloc = allocate_payment(ev.amount, tuple((o,) for o in outstanding))
    entries = []
    if len(ev.debt_order) > 1:
        # combined trajectory entry for multi-basis payments; a
        # single-basis payment gets exactly one (per-basis) entry below
        entries.append(
            LedgerEntry(
                entry_id=f"gross:{ev.event.event_id}",
                kind=LedgerEntryKind.GROSS_RECEIVED,
                basis_key=";".join(ev.debt_order),
                obligor="",
                proceeding="",
                amount=ev.amount,
                event_ref=ev.event.event_id,
                at_day=ev.event.occurred_at,
            )
        )
    notes = []
    for key, (a,), (resid,) in zip(ev.debt_order, alloc.allocations, alloc.residuals):
        if a > 0:
            entries.append(
                LedgerEntry(
                    entry_id=f"sat:{ev.event.event_id}:{key}",
                    kind=LedgerEntryKind.SATISFIED,
                    basis_key=key,
                    obligor="",
                    proceeding="",
                    amount=a,
                    event_ref=ev.event.event_id,
                    at_day=ev.event.occurred_at,
                )
            )
            notes.append(f"allocated {a} to {key}")
        del resid
    # per-basis gross entries.  A single-basis payment's FULL receipt is
    # attributable to that basis (the Rcash formula never truncates at
    # the entitlement — overpayment included).  For multi-basis payments
    # each basis records its allocated share and the unallocated
    # remainder gets an entry attributable to no basis (fixes the
    # cross-basis double count).
    single = len(ev.debt_order) == 1
    for key, (a,) in zip(ev.debt_order, alloc.allocations):
        amount = ev.amount if single else a
        if amount > 0:
            entries.append(
                LedgerEntry(
                    entry_id=f"gross:{ev.event.event_id}:{key}",
                    kind=LedgerEntryKind.GROSS_RECEIVED,
                    basis_key=key,
                    obligor="",
                    proceeding="",
                    amount=amount,
                    event_ref=ev.event.event_id,
                    at_day=ev.event.occurred_at,
                )
            )
    if not single and alloc.remaining > 0:
        entries.append(
            LedgerEntry(
                entry_id=f"gross:{ev.event.event_id}:unallocated",
                kind=LedgerEntryKind.GROSS_RECEIVED,
                basis_key="unallocated",
                obligor="",
                proceeding="",
                amount=alloc.remaining,
                event_ref=ev.event.event_id,
                at_day=ev.event.occurred_at,
            )
        )
    if alloc.remaining > 0:
        notes.append(f"overpay {alloc.remaining} recorded in gross only")
    new_state = replace(
        state,
        ledger=state.ledger + tuple(entries),
        events=state.events + (ev.event,),
    )
    return new_state, tuple(notes)


def step_event(
    state: ProcessState,
    process_event: ProcessEvent,
    env: Optional[LegalEnvironment] = None,
    limits: Optional[ExecutionLimits] = None,
) -> StepOutcome:
    """§9.1 step: exactly the event's own semantics; nothing else moves."""

    ev = process_event
    kind = ev.kind
    if kind is LegalEventKind.PAYMENT_PERFORMED:
        new_state, notes = _apply_payment(state, ev)
        return StepOutcome(new_state, env, notes)
    if kind is LegalEventKind.EVIDENCE_SUBMITTED:
        record = EvidenceRecord(
            evidence_id=f"ev:{ev.event.event_id}",
            artifact_ref=ev.event.object_ref,
            origin=ev.event.authority_ref or "party",
            produced_at=ev.event.occurred_at,
            known_at=ev.event.observed_at,
        )
        new_state = replace(
            state,
            evidence=state.evidence + (record,),
            events=state.events + (ev.event,),
        )
        return StepOutcome(new_state, env, ("evidence visible from known_at",))
    if kind is LegalEventKind.EVIDENCE_WITHDRAWN:
        # withdrawal removes the record; derived items are recomputed by
        # the evaluation pass, not silently kept
        removed = f"ev:{ev.event.object_ref}"
        new_state = replace(
            state,
            evidence=tuple(e for e in state.evidence if e.evidence_id != removed),
            events=state.events + (ev.event,),
        )
        return StepOutcome(new_state, env, (f"withdrawn {removed}",))
    if kind is LegalEventKind.AWARD_ISSUED:
        # ActualIssued: recorded as an actual document event; effect on
        # enforceability is decided by AWARD_EFFECTIVE, never here.
        new_state = replace(state, events=state.events + (ev.event,))
        return StepOutcome(new_state, env, ("actual issuance recorded; no effect asserted",))
    if kind is LegalEventKind.AWARD_EFFECTIVE:
        # Effective requires a declared authority reference; a title
        # entry records the enforceable amount on the basis.
        if not ev.authority_ref:
            raise ValueError("an effective award requires its authority reference")
        if ev.amount is None or ev.amount < 0 or not ev.basis_key:
            raise ValueError("effective awards name basis and amount")
        entry = LedgerEntry(
            entry_id=f"title:{ev.event.event_id}",
            kind=LedgerEntryKind.TITLE_ENTITLEMENT,
            basis_key=ev.basis_key,
            obligor="",
            proceeding="",
            amount=ev.amount,
            event_ref=ev.event.event_id,
            at_day=ev.event.occurred_at,
        )
        new_state = replace(state, ledger=state.ledger + (entry,),
                            events=state.events + (ev.event,))
        return StepOutcome(new_state, env, ("title entitlement recorded",))
    if kind is LegalEventKind.AWARD_REVOKED:
        # A revocation supersedes every earlier title on the basis with a
        # zero-title: the enforceable amount drops, the payment history
        # (gross/satisfied) is untouched (plan 9.2: revocation does not
        # erase payments already made).
        if not ev.basis_key or not ev.authority_ref:
            raise ValueError("revocation requires basis and authority")
        prior_titles = tuple(
            e for e in state.ledger
            if e.kind is LedgerEntryKind.TITLE_ENTITLEMENT
            and e.basis_key == ev.basis_key
        )
        entry = LedgerEntry(
            entry_id=f"title:{ev.event.event_id}",
            kind=LedgerEntryKind.TITLE_ENTITLEMENT,
            basis_key=ev.basis_key,
            obligor="",
            proceeding="",
            amount=Fraction(0),
            event_ref=ev.event.event_id,
            at_day=ev.event.occurred_at,
            supersedes=tuple(e.entry_id for e in prior_titles),
        )
        new_state = replace(state, ledger=state.ledger + (entry,),
                            events=state.events + (ev.event,))
        return StepOutcome(new_state, env, ("titles superseded; history kept",))
    if kind is LegalEventKind.NORM_CHANGE_AUTHORIZED:
        if env is None:
            raise ValueError("authorized norm change requires the environment")
        if not ev.authority_ref:
            raise ValueError("authorized norm change requires its authority reference")
        new_env = replace(env, evaluation_day=ev.event.occurred_at) if False else env
        # The environment content update itself is carried by the rule
        # record passed in the case; here we only stamp that the event
        # occurred and return the SAME environment object — content
        # changes go through LegalEnvironment construction, not mutation.
        del new_env
        new_state = replace(state, events=state.events + (ev.event,))
        return StepOutcome(new_state, env, ("authorized change recorded",))
    if kind is LegalEventKind.NORM_CHANGE_PROPOSED:
        # A proposal never mutates the environment (§9.4: unauthorized
        # output is not a norm).
        new_state = replace(state, events=state.events + (ev.event,))
        return StepOutcome(new_state, env, ("proposal recorded; environment unchanged",))
    raise ValueError(f"unknown event kind: {kind}")


def run_trace(
    initial: ProcessState,
    events: Sequence[ProcessEvent],
    env: Optional[LegalEnvironment] = None,
) -> Tuple[ProcessState, Tuple[str, ...]]:
    """Fold the step relation over a finite event list (§9.1); each step
    sees exactly its predecessor."""

    state = initial
    notes: list = []
    for process_event in events:
        outcome = step_event(state, process_event, env)
        state = outcome.next_state
        env = outcome.next_env if outcome.next_env is not None else env
        notes.extend(outcome.notes)
    return state, tuple(notes)


def outstanding_of(state: ProcessState, basis_key: str) -> Fraction:
    """Legal remaining amount: title entitlement minus satisfied — the
    §6.1/§9 reading that never confuses gross receipts with offsets."""

    entitled = sum((e.amount for e in effective_titles(state, basis_key)), Fraction(0))
    paid = sum(
        (e.amount for e in state.ledger
         if e.kind is LedgerEntryKind.SATISFIED and e.basis_key == basis_key),
        Fraction(0),
    )
    return max(entitled - paid, Fraction(0))


def gross_of(state: ProcessState, basis_key: str) -> Fraction:
    """Actual receipts attributable to ONE basis: only single-key gross
    entries count (combined multi-basis entries record the payment
    trajectory, not a per-basis attribution)."""
    return sum(
        (e.amount for e in state.ledger
         if e.kind is LedgerEntryKind.GROSS_RECEIVED
         and e.basis_key == basis_key),
        Fraction(0),
    )


def gross_total_of(state: ProcessState, basis_key: str) -> Fraction:
    """The full payment TRAFFIC through a basis group: combined
    multi-basis entries that name it (the trajectory view of 6.1 —
    actual inflows, overpayments included)."""
    return sum(
        (e.amount for e in state.ledger
         if e.kind is LedgerEntryKind.GROSS_RECEIVED
         and basis_key in e.basis_key.split(";")),
        Fraction(0),
    )


def effective_titles(state: ProcessState, basis_key: str) -> Tuple[LedgerEntry, ...]:
    """Currently effective titles: those not superseded by any later
    title on the same basis (plan 6.1: the CURRENTLY effective title)."""
    titles = tuple(
        e for e in state.ledger
        if e.kind is LedgerEntryKind.TITLE_ENTITLEMENT and e.basis_key == basis_key
    )
    superseded = {sid for e in titles for sid in e.supersedes}
    return tuple(e for e in titles if e.entry_id not in superseded)


def is_final(state: ProcessState, proceeding: str) -> bool:
    """Final(a, proceeding): the ordinary-remedy stages are exhausted
    (stage 'decided', no pending appeal).  Final does NOT mean immune to
    retrial (plan 9.2A: Final is not 'never subject to retrial')."""
    try:
        stage = state.stage_of(proceeding)
    except ValueError:
        return False
    if stage != "decided":
        return False
    return not any(
        e.event_type == "appeal_filed" and e.observed_at <= state.as_of_day
        for e in state.events
    )


def award_legally_correct(run, basis: str) -> Optional[bool]:
    """LegallyCorrect for an issued award read off the model's own
    results: True iff every branch establishes the basis (a compelled
    decision); None when branches disagree (a legally-possible choice
    the model does not stamp)."""
    if not run.branches:
        return None
    verdicts = {
        any(f.judgment.value == "ESTABLISHED" for f in b.finalizations)
        for b in run.branches
    }
    if len(verdicts) == 1:
        return verdicts.pop()
    return None
