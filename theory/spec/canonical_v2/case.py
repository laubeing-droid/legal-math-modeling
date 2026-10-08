#!/usr/bin/env python3
"""Case-level input, state, and view carriers for the unified legal model.

This module lands the J.4 contracts of the unified construction plan
(20261007 附录J §J.4): normalized case inputs, process states, knowledge
views, exact-quantity arithmetic, and exact-JSON discipline.

Design invariants (fail-closed, enforced in constructors):

* A ``CaseInput`` never carries a final answer: no adjudication verdict,
  no pre-built argumentation framework, no fixed amount or payoff table.
* A ``KnowledgeView`` is a projection of visible evidence plus named
  local assessments; it cannot read the hidden world state ``R``.
* Rules are finite typed records; arbitrary callables are rejected.
* All exact quantities are ``Fraction`` with unit and basis identity;
  floats never enter the exact channel.
* Legal undetermined, missing input, and algorithm failure are distinct
  axes (RunStatus + FailureStatus), never collapsed into one bucket.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from enum import Enum
from fractions import Fraction
from typing import Optional, Tuple

from .kernel import Jurisdiction, NormState, Question
from .types import Modality


# ---------------------------------------------------------------------------
# J.4.3 Exact JSON discipline
# ---------------------------------------------------------------------------


def _unique_pairs(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _reject_number(value):
    raise ValueError(f"non-integer JSON number in exact input: {value}")


def load_exact_json(text):
    """Parse exact-input JSON: duplicate keys, NaN/Infinity and JSON
    decimals (binary floats in disguise) are all rejected."""

    return json.loads(
        text,
        object_pairs_hook=_unique_pairs,
        parse_float=_reject_number,
        parse_constant=_reject_number,
    )


def fraction_from_json(value):
    """Decode {"n": "-17", "d": "100"} with positive, canonical components."""

    if type(value) is not dict or set(value) != {"n", "d"}:
        raise ValueError("expected rational object")
    if type(value["n"]) is not str or type(value["d"]) is not str:
        raise ValueError("rational components must be decimal strings")
    n, d = int(value["n"]), int(value["d"])
    if str(n) != value["n"] or str(d) != value["d"] or d <= 0:
        raise ValueError("noncanonical rational components")
    return Fraction(n, d)


def fraction_to_json(value):
    if type(value) is not Fraction:
        raise TypeError("Fraction required")
    return {"n": str(value.numerator), "d": str(value.denominator)}


def round_fraction(value: Fraction, mode: str) -> int:
    """Exact integer rounding of a Fraction under a named policy.

    HALF_UP/HALF_DOWN resolve absolute-value midpoints then restore the
    sign; DOWN rounds toward zero; UP rounds away from zero.  Every other
    name is an error: no silent default policy.
    """

    if type(value) is not Fraction:
        raise TypeError("Fraction required")
    sign = -1 if value < 0 else 1
    q, r = divmod(abs(value.numerator), value.denominator)
    if mode == "HALF_UP":
        up = 2 * r >= value.denominator
    elif mode == "HALF_DOWN":
        up = 2 * r > value.denominator
    elif mode == "DOWN":
        up = False
    elif mode == "UP":
        up = r != 0
    else:
        raise ValueError("unknown rounding policy")
    return sign * (q + int(up))


# ---------------------------------------------------------------------------
# Scoped atoms, facts, evidence
# ---------------------------------------------------------------------------


class Polar(str, Enum):
    """Signed polarity of a proposition occurrence (§2.2, §3.3)."""

    POS = "POS"
    NEG = "NEG"


class FactStanding(str, Enum):
    """Fact-record standings; unsubmitted, awaiting review, not proved and
    explicit negation are distinct (J.4.1 FactRecord contract)."""

    NOT_SUBMITTED = "NOT_SUBMITTED"
    AWAITING_ADMISSION = "AWAITING_ADMISSION"
    ADMITTED_POSITIVE = "ADMITTED_POSITIVE"
    NOT_PROVED = "NOT_PROVED"
    EXPLICIT_NEGATION = "EXPLICIT_NEGATION"


@dataclass(frozen=True)
class ScopedAtom:
    """Typed, scoped proposition key (I.3.1): case, subject, issue, stage,
    predicate and polarity.  Same display name with different subject or
    issue is a different atom; nothing is merged by string alone."""

    case_id: str
    subject: str
    issue: str
    stage: str
    predicate: str
    polar: Polar

    def __post_init__(self) -> None:
        for name in ("case_id", "subject", "issue", "predicate"):
            if not getattr(self, name):
                raise ValueError(f"ScopedAtom requires a nonempty {name}")


@dataclass(frozen=True)
class FactRecord:
    """One fact as material: proposition object, polarity, standing,
    source/assumption ids, observation time and issue scope."""

    fact_id: str
    proposition: ScopedAtom
    standing: FactStanding
    source_ids: Tuple[str, ...] = ()
    produced_at: int = 0
    known_at: int = 0
    issues: Tuple[str, ...] = ()

    def __post_init__(self) -> None:
        if not self.fact_id:
            raise ValueError("FactRecord requires fact_id")
        if self.known_at < self.produced_at:
            raise ValueError("a fact cannot be known before it is produced")


@dataclass(frozen=True)
class EvidenceRecord:
    """Raw material item e=(artifact, origin, eventId, author, time, use,
    contentSpan) per §5.3.1.  Says/records are not truth."""

    evidence_id: str
    artifact_ref: str
    origin: str
    event_ref: str = ""
    author: str = ""
    produced_at: int = 0
    known_at: int = 0
    use: str = ""
    content_span: str = ""


# ---------------------------------------------------------------------------
# Claims, defenses, rules, bases, quantities
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Claim:
    """Claim c=(a,b,basis,object,remedy,time) per §2.2: claimant and
    respondent cannot be swapped; the basis names the claim-basis chain."""

    claim_id: str
    claimant: str
    respondent: str
    basis: str
    object: str
    remedy: str
    at_day: int = 0
    subject: str = ""
    issue: str = ""  # scopes the claim to an issue; empty = any


@dataclass(frozen=True)
class Defense:
    defense_id: str
    defender: str
    target_claims: Tuple[str, ...]
    basis: str
    at_day: int = 0
    subject: str = ""

    def __post_init__(self) -> None:
        if not self.target_claims:
            raise ValueError("a defense must target at least one claim")


class RuleKind(str, Enum):
    STRICT_HORN = "STRICT_HORN"
    DEFEASIBLE = "DEFEASIBLE"
    CONSTITUTIVE = "CONSTITUTIVE"
    PROCEDURAL = "PROCEDURAL"
    BURDEN = "BURDEN"
    ADMISSION = "ADMISSION"


@dataclass(frozen=True)
class RuleGuard:
    """A named attackable guard slot g=(Inst,kind,slot) with its scope
    fields (§4.3 table, right column): subject/act/matter or
    jurisdiction/time/stage depending on kind."""

    rule_instance: str
    kind: str  # exception | authority | scope | procedure
    slot: str
    scope: Tuple[str, ...] = ()
    source: str = ""


def _validity(
    jurisdiction: str,
    stage_scope: Tuple[str, ...],
    matter_scope: Tuple[str, ...],
    from_day: Optional[int],
    to_day: Optional[int],
) -> Tuple:
    if not jurisdiction:
        raise ValueError("rule validity requires a jurisdiction")
    if from_day is not None and to_day is not None and from_day > to_day:
        raise ValueError("validity window is empty")
    return (jurisdiction, tuple(stage_scope), tuple(matter_scope), from_day, to_day)


@dataclass(frozen=True)
class LegalRuleRecord:
    """Typed finite rule record (J.4.1): premises/conclusion are scoped
    atoms, exceptions are named guards, priority is a declared relation,
    source and validity scope are explicit.  No callables are accepted."""

    rule_id: str
    kind: RuleKind
    premises: Tuple[ScopedAtom, ...]
    conclusion: ScopedAtom
    modality: Modality
    guards: Tuple[RuleGuard, ...] = ()
    priority_over: Tuple[str, ...] = ()
    source_id: str = ""
    validity: Optional[Tuple] = None

    def __post_init__(self) -> None:
        if not self.rule_id or not self.source_id:
            raise ValueError("rule requires id and source")
        if not self.premises and self.kind is RuleKind.STRICT_HORN:
            raise ValueError("a strict Horn rule needs premises")
        if callable(self.conclusion) or any(callable(p) for p in self.premises):
            raise TypeError("rule content must be typed data, not callables")

    def with_validity(
        self,
        jurisdiction: str,
        stage_scope: Tuple[str, ...] = (),
        matter_scope: Tuple[str, ...] = (),
        from_day: Optional[int] = None,
        to_day: Optional[int] = None,
    ) -> "LegalRuleRecord":
        return LegalRuleRecord(
            rule_id=self.rule_id,
            kind=self.kind,
            premises=self.premises,
            conclusion=self.conclusion,
            modality=self.modality,
            guards=self.guards,
            priority_over=self.priority_over,
            source_id=self.source_id,
            validity=_validity(jurisdiction, stage_scope, matter_scope, from_day, to_day),
        )

    def applicable_at(self, jurisdiction: str, day: int, stage: str = "") -> bool:
        """Validity-window check only; conflict exclusion is §3.1's job."""
        if self.validity is None:
            return True
        jur, stages, matters, lo, hi = self.validity
        if jur != jurisdiction:
            return False
        if stages and stage not in stages:
            return False
        if lo is not None and day < lo:
            return False
        if hi is not None and day > hi:
            return False
        return True


class BasisKind(str, Enum):
    """Admission-basis kinds (J.4.1): ordinary support, presumption,
    forensic exemption/judicial admission, final binding, evidence
    obstruction are separate channels, never one Boolean."""

    ORDINARY_SUPPORT = "ORDINARY_SUPPORT"
    PRESUMPTION = "PRESUMPTION"
    FORENSIC_EXEMPT = "FORENSIC_EXEMPT"
    JUDICIAL_ADMISSION = "JUDICIAL_ADMISSION"
    FINAL_BINDING = "FINAL_BINDING"
    EVIDENCE_OBSTRUCTION = "EVIDENCE_OBSTRUCTION"


@dataclass(frozen=True)
class StrongTemplate:
    """A NAMED sufficiency template (plan §5.3.2 W-STRONG, §5.3.4 loan
    template, §5.3.5 S1–S6): the only source of StrongBasis.  The
    template itself declares which premise predicates license strong
    support for WHICH conclusion predicate, plus its named failure
    predicates (具名败因) and the rule that licenses it.  An admission
    basis never carries a conclusion or a strength — only templates do.

    ``license_rule_id`` binds the template to a LegalRuleRecord: the
    template fires only in norm selections that adopt that rule (empty
    means selection-independent)."""

    template_id: str
    kind: str  # LOAN_DELIVERY | S1_DIRECT | S2_RECORD | ... (open domain)
    scope_issue: str
    premise_predicates: Tuple[str, ...]
    conclusion_predicate: str
    failure_predicates: Tuple[str, ...] = ()
    license_rule_id: str = ""
    source_id: str = ""
    subject: str = ""  # scopes the conclusion; empty = issue-level

    def __post_init__(self) -> None:
        if not self.template_id or not self.kind or not self.source_id:
            raise ValueError("template requires id, kind and source")
        if not self.premise_predicates or not self.conclusion_predicate:
            raise ValueError("a sufficiency template names premises and its conclusion")


@dataclass(frozen=True)
class AdmissionBasis:
    """A material-reference record for an admission channel.  It NEVER
    carries a conclusion predicate or a strength: ordinary support
    creates nothing by itself, and special channels (judicial
    admission, forensic exemption, final binding, evidence obstruction)
    establish their ISSUE directly when their premises hold.  An
    optional license rule binds the channel to a norm selection."""

    basis_id: str
    kind: BasisKind
    issue_id: str
    subject: str
    stage: str
    version: str
    premise_refs: Tuple[str, ...] = ()
    block_refs: Tuple[str, ...] = ()
    authorization_refs: Tuple[str, ...] = ()
    license_rule_id: str = ""


@dataclass(frozen=True)
class ExactQuantity:
    """Exact rational amount with unit and computation-basis identity;
    same number in different units/bases never merges (J.4.1)."""

    value: Fraction
    unit: str
    basis_kind: str
    source_id: str = ""

    def __post_init__(self) -> None:
        if type(self.value) is not Fraction:
            raise TypeError("ExactQuantity.value must be a Fraction")
        if not self.unit or not self.basis_kind:
            raise ValueError("unit and basis kind are required")


# ---------------------------------------------------------------------------
# Environment, events, process state, knowledge view
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class AuthorizedAssessment:
    """I.3.1: which subject, under which authority/procedure, in which
    scope and version, made which local assessment from which materials."""

    assessment_id: str
    assessor: str
    authority_ref: str
    issue: str
    version: str
    materials: Tuple[str, ...] = ()


@dataclass(frozen=True)
class LegalEnvironment:
    """Jurisdiction, versioned rules, interpretation policy identity,
    authorized assessments, declared admission bases, procedure policy,
    evaluation day."""

    environment_id: str
    jurisdiction: Jurisdiction
    rules: Tuple[LegalRuleRecord, ...] = ()
    strong_templates: Tuple[StrongTemplate, ...] = ()
    counter_evidences: Tuple[object, ...] = ()  # standards.CounterEvidence
    interpretation_policy_id: str = ""
    authorized_assessments: Tuple[AuthorizedAssessment, ...] = ()
    admission_bases: Tuple[AdmissionBasis, ...] = ()
    procedure_policy_id: str = ""
    evaluation_day: int = 0

    def __post_init__(self) -> None:
        seen = set()
        for rule in self.rules:
            if rule.rule_id in seen:
                raise ValueError(f"duplicate rule id: {rule.rule_id}")
            seen.add(rule.rule_id)
        basis_ids = [b.basis_id for b in self.admission_bases]
        if len(set(basis_ids)) != len(basis_ids):
            raise ValueError("duplicate admission basis ids")
        template_ids = [t.template_id for t in self.strong_templates]
        if len(set(template_ids)) != len(template_ids):
            raise ValueError("duplicate strong template ids")


@dataclass(frozen=True)
class CaseEvent:
    """An actual event: occurrence and observation times are separate; the
    event actually happened regardless of strategy recommendation (§9.1)."""

    event_id: str
    event_type: str
    occurred_at: int
    observed_at: int
    object_ref: str
    material_refs: Tuple[str, ...] = ()
    authority_ref: str = ""

    def __post_init__(self) -> None:
        if not self.event_id or not self.event_type:
            raise ValueError("event requires id and type")
        if self.observed_at < self.occurred_at:
            raise ValueError("an event cannot be observed before it occurs")


class LedgerEntryKind(str, Enum):
    """§6.1 accounts: GROSS_RECEIVED is the payment TRAJECTORY (one entry
    per payment, full amount); GROSS_ALLOCATED is the per-basis
    attribution (allocated share; the full amount for a single-basis
    payment — the Rcash view never truncates at the entitlement);
    satisfied is the legal offset; the effective title is separate."""

    GROSS_RECEIVED = "GROSS_RECEIVED"
    GROSS_ALLOCATED = "GROSS_ALLOCATED"
    SATISFIED = "SATISFIED"
    TITLE_ENTITLEMENT = "TITLE_ENTITLEMENT"


@dataclass(frozen=True)
class LedgerEntry:
    entry_id: str
    kind: LedgerEntryKind
    basis_key: str
    obligor: str
    proceeding: str
    amount: Fraction
    event_ref: str
    at_day: int
    supersedes: Tuple[str, ...] = ()  # title entries this one replaces

    def __post_init__(self) -> None:
        if type(self.amount) is not Fraction or self.amount < 0:
            raise ValueError("ledger amounts are nonnegative Fractions")
        if not self.basis_key:
            raise ValueError("ledger entries bind to a named basis")


@dataclass(frozen=True)
class ProcessState:
    """§9.1 state s=(R,E,Γ,Prc,Ledger) with the actual event prefix and the
    two time axes.  K is NOT stored here: it is rebuilt from the visible
    projection of E (J.4.1 ProcessState contract)."""

    r: NormState
    evidence: Tuple[EvidenceRecord, ...] = ()
    environment_id: str = ""
    stages: Tuple[Tuple[str, str], ...] = ()  # (proceeding, stage)
    ledger: Tuple[LedgerEntry, ...] = ()
    events: Tuple[CaseEvent, ...] = ()
    target_day: int = 0
    as_of_day: int = 0

    def __post_init__(self) -> None:
        if self.as_of_day < self.target_day:
            raise ValueError("as_of cannot precede target day")
        seen = set()
        for proceeding, _stage in self.stages:
            if proceeding in seen:
                raise ValueError(f"duplicate proceeding stage row: {proceeding}")
            seen.add(proceeding)

    def stage_of(self, proceeding: str) -> str:
        for proc, stage in self.stages:
            if proc == proceeding:
                return stage
        raise ValueError(f"unknown proceeding: {proceeding}")

    def visible_evidence(self, known_by_day: int) -> Tuple[EvidenceRecord, ...]:
        """§2.1 projection: only evidence knowable by the cutoff enters V."""

        return tuple(e for e in self.evidence if e.known_at <= known_by_day)


@dataclass(frozen=True)
class LocalAssessmentCard:
    """A named local assessment carried inside the knowledge view: which
    authorized assessor produced which evaluation inputs for which issue.
    It is an input to reasoning, never a final verdict (§5.3.1)."""

    card_id: str
    assessment_ref: str
    issue: str
    content: Tuple[Tuple[str, str], ...] = ()  # ordered (key, value) pairs


@dataclass(frozen=True)
class KnowledgeView:
    """The only input the judging path may read: visible evidence, facts
    with standings, per-procedure stages, named local assessment cards,
    claims/defenses and exact quantities.  No reference to hidden R."""

    case_id: str
    as_of_day: int
    visible_evidence: Tuple[EvidenceRecord, ...]
    facts: Tuple[FactRecord, ...]
    stages: Tuple[Tuple[str, str], ...]
    cards: Tuple[LocalAssessmentCard, ...]
    claims: Tuple[Claim, ...]
    defenses: Tuple[Defense, ...]
    quantities: Tuple[ExactQuantity, ...]


@dataclass(frozen=True)
class CaseInput:
    """Normalized case input (J.4.1).  Carries the initial state snapshot,
    finite party/issue/claim/defense tables, records, questions and
    quantities — and never a pre-computed answer."""

    case_id: str
    initial_state: ProcessState
    parties: Tuple[str, ...]
    issues: Tuple[str, ...]
    claims: Tuple[Claim, ...]
    defenses: Tuple[Defense, ...]
    fact_records: Tuple[FactRecord, ...]
    evidence_records: Tuple[EvidenceRecord, ...]
    questions: Tuple[Question, ...]
    quantities: Tuple[ExactQuantity, ...]

    def __post_init__(self) -> None:
        if not self.case_id:
            raise ValueError("case requires an id")
        claim_ids = [c.claim_id for c in self.claims]
        if len(set(claim_ids)) != len(claim_ids):
            raise ValueError("duplicate claim ids")
        fact_ids = [f.fact_id for f in self.fact_records]
        if len(set(fact_ids)) != len(fact_ids):
            raise ValueError("duplicate fact ids")


@dataclass(frozen=True)
class ExecutionLimits:
    """Resource budgets only; they pause work, never shrink the solution
    set (J.4.1).  None means unlimited."""

    max_nodes: Optional[int] = None
    max_seconds: Optional[float] = None
    max_bytes: Optional[int] = None


class RunStatus(str, Enum):
    """J.4.2/J.15.1 execution states.

    COMPLETE requires no technical failure and every required root closed;
    SOUND_PARTIAL requires verified content plus a real open frontier;
    PAUSED is a resource stop with no verified content; FAILED carries a
    technical failure (attempt is terminal; re-runs start new attempts).
    """

    COMPLETE = "COMPLETE"
    SOUND_PARTIAL = "SOUND_PARTIAL"
    PAUSED = "PAUSED"
    FAILED = "FAILED"


def knowledge_view(case: CaseInput, env: Optional[LegalEnvironment] = None) -> KnowledgeView:
    """Build the judging path's only input: the visible projection of E at
    the state's as_of day, with standings, stages, cards, claims and
    quantities.  Reads nothing from ``case.initial_state.r``.

    Local assessment cards come from the environment's authorized
    assessments, materialized as named cards; an assessment whose issue is
    outside the declared issues is dropped, not silently kept.
    """

    state = case.initial_state
    visible = state.visible_evidence(state.as_of_day)
    visible_ids = frozenset(e.evidence_id for e in visible)
    cards: Tuple[LocalAssessmentCard, ...] = ()
    if env is not None:
        issue_set = frozenset(case.issues)
        # A card whose declared materials are not yet visible is withheld:
        # the view must not carry assessments grounded in unseen evidence.
        cards = tuple(
            LocalAssessmentCard(
                card_id=f"card:{a.assessment_id}:{a.issue}",
                assessment_ref=a.assessment_id,
                issue=a.issue,
            )
            for a in env.authorized_assessments
            if (not issue_set or a.issue in issue_set)
            and all(m in visible_ids for m in a.materials)
        )
    return KnowledgeView(
        case_id=case.case_id,
        as_of_day=state.as_of_day,
        visible_evidence=visible,
        facts=case.fact_records,
        stages=state.stages,
        cards=cards,
        claims=case.claims,
        defenses=case.defenses,
        quantities=case.quantities,
    )
