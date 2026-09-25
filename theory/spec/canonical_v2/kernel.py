#!/usr/bin/env python3
"""Kernel object carriers for object definition v3 (TY-01..TY-04, EV-01..05).

These frozen records mirror the minimal structures declared in
`JurisLean/LegalModelV2.lean`: Relation (clause 1, shared constraints),
LegalPower (clause 5, three non-implying modalities), Event / EventHistory
(clauses 4 and 6, the time-structure carrier H), and Jurisdiction (the
jurisdiction axis J of the condition group). Python records carry
serializable contracts only; Lean-definition authority stays with the
registry file.

The EV block lands the eval contracts as skeletons: the Judgment/Truth
layering, Eval(q) = (Judgment, Disposition) with Disposition a field of
domain D or ∅, the EffectType transfer function (only constitutive
adjudications move R_t), K_{e,t} as a candidate-state set that evidence
updates narrow without ever touching R_t, and the ApplicableNorm version
selector where facts-time from H governs and t alone never decides.
Legal semantics feeding these skeletons live outside this module; the
contracts pin the shapes and the fail-closed disciplines.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Dict, FrozenSet, Mapping, Optional, Tuple


class SharedConstraintKind(str, Enum):
    """Constraints a relation whole may carry (object definition v3 clause 1)."""

    SAME_LOSS = "SAME_LOSS"
    COMPETING_EXCLUSIVE = "COMPETING_EXCLUSIVE"
    JOINT_REDUCTION = "JOINT_REDUCTION"


class JurisdictionRoute(str, Enum):
    """Jurisdiction routing axis (TY-04)."""

    MAINLAND = "MAINLAND"
    HONG_KONG = "HONG_KONG"
    UNITED_STATES = "UNITED_STATES"
    OTHER = "OTHER"


@dataclass(frozen=True)
class SharedConstraint:
    """One shared constraint linking several relations of the whole."""

    kind: SharedConstraintKind
    memberRelations: Tuple[str, ...]
    subjectRef: str = ""

    def __post_init__(self) -> None:
        if not self.memberRelations:
            raise ValueError("SharedConstraint needs at least one member relation")
        if self.kind is SharedConstraintKind.SAME_LOSS and not self.subjectRef:
            raise ValueError("SAME_LOSS constraint must name the shared loss")


@dataclass(frozen=True)
class Relation:
    """TY-01: a legal relation; shared constraints ride on the whole."""

    relationId: str
    parties: Tuple[str, ...]
    kind: str
    sharedConstraints: Tuple[SharedConstraint, ...] = ()


@dataclass(frozen=True)
class LegalPower:
    """TY-02: Power / Obligation / Occurred as independent fields.

    Clause 5: no unconditional implication among the three modalities;
    specific norms may still establish conditional derivation elsewhere.
    """

    powerId: str
    powerGranted: bool
    obligationImposed: bool
    occurred: bool


@dataclass(frozen=True)
class Event:
    """TY-03: an event; the member of history H."""

    eventId: str
    atDay: int
    eventType: str


@dataclass(frozen=True)
class EventHistory:
    """TY-03: the event-history time structure H (insertion order preserved)."""

    events: Tuple[Event, ...]


@dataclass(frozen=True)
class Jurisdiction:
    """TY-04: the jurisdiction axis J of the condition group."""

    route: JurisdictionRoute
    code: str = ""

    def __post_init__(self) -> None:
        if self.route is JurisdictionRoute.OTHER and not self.code:
            raise ValueError("Jurisdiction route OTHER must carry an explicit code")


@dataclass(frozen=True)
class ApplicableNormQuery:
    """Signature carrier for A(J, V, q, H, t) (object definition v3 clause 6).

    H and t are both mandatory arguments; neither alone fixes the norm
    version. Resolution semantics are the EV-04 target, not this record.
    """

    jurisdiction: Jurisdiction
    normEnv: str
    question: str
    history: EventHistory
    atDay: int


# --- EV pool: object definition v3 eval contracts (EV-01..05) ---


class QuestionKind(str, Enum):
    """Clause 3: questions split into substantive / procedural / effect."""

    SUBSTANTIVE = "SUBSTANTIVE"
    PROCEDURAL = "PROCEDURAL"
    EFFECT = "EFFECT"


class Judgment(str, Enum):
    """Clause 2: what the evidence, burden, and procedure can support."""

    ESTABLISHED = "ESTABLISHED"
    NOT_ESTABLISHED = "NOT_ESTABLISHED"
    PENDING = "PENDING"


class EffectType(str, Enum):
    """Clause 4: how a judgment event may act on R_t."""

    CONFIRMATORY = "CONFIRMATORY"
    CONSTITUTIVE = "CONSTITUTIVE"
    PERFORMANCE = "PERFORMANCE"
    PROCEDURAL_BINDING = "PROCEDURAL_BINDING"


@dataclass(frozen=True)
class Disposition:
    """Clause 3: procedural legal effect, a member of D or ∅ (None).

    A field of EvalResult, never a fourth Judgment value; `kind` is an open
    string domain (e.g. "DISMISS_PROCEDURE", "AWARD", "REMIT").
    """

    kind: str
    payload: str = ""


@dataclass(frozen=True)
class Question:
    """A legal question q. `truth_in_R` is the normative-semantics input
    Truth(q, R_t) supplied from R_t — it is never derived from Judgment
    (clause 2 layering). Procedural stage rides in q (EV-04)."""

    questionId: str
    kind: QuestionKind
    stage: str = ""
    truth_in_R: Optional[bool] = None


@dataclass(frozen=True)
class EvalResult:
    """Clause 3: Eval(q) = (Judgment(q), Disposition(q))."""

    questionId: str
    judgment: Judgment
    disposition: Optional[Disposition] = None


@dataclass(frozen=True)
class CandidateState:
    """One evidence-supportable world state; a member of K_{e,t}."""

    stateId: str


@dataclass(frozen=True)
class NormState:
    """R_t: the normative-relation whole (shared constraints ride inside)."""

    relations: Tuple[Relation, ...]


@dataclass(frozen=True)
class KernelState:
    """Clause 1: B_t = (R_t, K_{e,t}). K is a candidate-state SET; it is
    never smuggled down to a single most-likely state."""

    normative: NormState
    candidates: FrozenSet[CandidateState]


@dataclass(frozen=True)
class JudgmentEvent:
    """Clause 4: an adjudication event carrying its EffectType. Only a
    constitutive event may carry formed relations; anything else is a
    constructor error, so a confirmatory judgment cannot be *implemented*
    as creating a relation."""

    effect_type: EffectType
    formed_relations: Tuple[Relation, ...] = ()

    def __post_init__(self) -> None:
        if self.effect_type is not EffectType.CONSTITUTIVE and self.formed_relations:
            raise ValueError(
                f"{self.effect_type.value} judgment cannot form relations; "
                "only CONSTITUTIVE transfers entity state"
            )


def transfer(state: NormState, event: JudgmentEvent) -> NormState:
    """Clause 4: R_{t+1} = T(R_t, EffectType(JudgmentEvent)).

    Only constitutive adjudications transfer entity state; confirmatory,
    performance, and procedural-binding events return R_t unchanged.
    """

    if event.effect_type is EffectType.CONSTITUTIVE:
        return NormState(state.relations + event.formed_relations)
    return state


def eval_question(
    question: Question, judgment: Judgment, disposition: Optional[Disposition] = None
) -> EvalResult:
    """Clause 3 skeleton: pair the per-question judgment with its
    disposition field. The judgment itself comes from evidential semantics
    outside this skeleton; no cross-question derivation exists here."""

    return EvalResult(
        questionId=question.questionId, judgment=judgment, disposition=disposition
    )


def eval_batch(
    entries: Tuple[Tuple[Question, Judgment, Optional[Disposition]], ...]
) -> Mapping[str, EvalResult]:
    """Evaluate exactly the requested questions: a determined procedural
    judgment never auto-generates a substantive one (clause 3)."""

    results: Dict[str, EvalResult] = {}
    for question, judgment, disposition in entries:
        results[question.questionId] = eval_question(question, judgment, disposition)
    return results


def narrow_candidates(
    state: KernelState, survivors: FrozenSet[CandidateState]
) -> KernelState:
    """Clause 4: evidence updates act on K only, never on R.

    Evidence narrows the candidate set to still-supported states; a survivor
    outside the current K would mean inventing state, which fails closed.
    R_t is returned bit-for-bit identical."""

    if not survivors <= state.candidates:
        raise ValueError("evidence update cannot introduce candidate states")
    return KernelState(normative=state.normative, candidates=frozenset(survivors))


@dataclass(frozen=True)
class NormVersion:
    """One version in a norm environment V, effective from a day."""

    tag: str
    effective_day: int


def applicable_norm(
    versions: Tuple[NormVersion, ...], query: ApplicableNormQuery
) -> NormVersion:
    """Clause 6 skeleton: A(J, V, q, H, t) version selection.

    Facts-time from H governs: the applicable version is the latest one
    effective at or before the last relevant event in H. t only bounds
    validity (evaluation cannot precede the facts) — t alone never decides
    the version, so a newer law effective after the facts never captures
    them however late the evaluation. Fails closed on empty H, empty
    version list, or facts predating every version.
    """

    if not versions:
        raise ValueError("no norm versions supplied for environment V")
    if not query.history.events:
        raise ValueError("H must carry the relevant event time structure")
    facts_day = max(event.atDay for event in query.history.events)
    if query.atDay < facts_day:
        raise ValueError("evaluation time t cannot precede the facts in H")
    eligible = [v for v in versions if v.effective_day <= facts_day]
    if not eligible:
        raise ValueError("facts predate every supplied norm version")
    return max(eligible, key=lambda v: v.effective_day)
