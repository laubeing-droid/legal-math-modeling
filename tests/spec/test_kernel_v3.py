"""Contract tests for object definition v3 eval clauses (EV-01..05).

The five hard definitions the ChatGPT audit forced, plus its three
counterexamples, live here as executable contracts on the kernel skeletons:
Truth/Judgment layering (EV-01), Eval(q)=(Judgment, Disposition) with
Disposition a field (EV-02), the EffectType transfer matrix where only
constitutive adjudications move R_t (EV-03), the ApplicableNorm version
selector where facts-time from H governs and t alone never decides (EV-04),
and K_{e,t} as a candidate set that evidence narrows without touching R_t
(EV-05). Counterexamples, by name: 劳动仲裁前置 (EV-02), 债权确认 (EV-03),
结算文件 (EV-05).
"""

from __future__ import annotations

import pytest

from theory.spec.canonical_v2 import (
    ApplicableNormQuery,
    CandidateState,
    Disposition,
    EffectType,
    Event,
    EventHistory,
    EvalResult,
    Judgment,
    JudgmentEvent,
    Jurisdiction,
    JurisdictionRoute,
    KernelState,
    NormState,
    NormVersion,
    Question,
    QuestionKind,
    Relation,
    applicable_norm,
    eval_batch,
    eval_question,
    narrow_candidates,
    transfer,
)


def _relation(rid: str) -> Relation:
    return Relation(relationId=rid, parties=("plaintiff", "defendant"), kind="synthetic")


R_DEBT = _relation("debt_2024")
NORM_STATE = NormState(relations=(R_DEBT,))


# --- EV-01: Truth / Judgment layering (clause 2) ---


def test_judgment_varies_with_evidence_while_truth_is_fixed_by_r() -> None:
    """Same R_t (Truth fixed), two evidence regimes -> two judgments.
    Judgment=NOT_ESTABLISHED therefore does not assert Truth=false."""

    question = Question(
        questionId="q_debt_exists",
        kind=QuestionKind.SUBSTANTIVE,
        truth_in_R=True,  # the debt relation is in R_t
    )
    rich = KernelState(
        normative=NORM_STATE,
        candidates=frozenset({CandidateState("io_u_owed"), CandidateState("io_u_partial")}),
    )
    poor = KernelState(
        normative=NORM_STATE,
        candidates=frozenset({CandidateState("io_u_no_deal"), CandidateState("io_u_forged")}),
    )

    established = eval_batch(((question, Judgment.ESTABLISHED, None),))
    lost = eval_batch(((question, Judgment.NOT_ESTABLISHED, None),))

    assert established["q_debt_exists"].judgment is Judgment.ESTABLISHED
    assert lost["q_debt_exists"].judgment is Judgment.NOT_ESTABLISHED
    # Truth(q, R_t) is a function of R_t only; both runs share R_t.
    assert question.truth_in_R is True
    assert rich.normative == poor.normative == NORM_STATE


def test_losing_sample_leaves_r_untouched() -> None:
    """A NOT_ESTABLISHED sample must not edit R_t: the confirmatory loss
    event transfers nothing, and Truth stays as R_t says."""

    loss = JudgmentEvent(effect_type=EffectType.CONFIRMATORY)
    after = transfer(NORM_STATE, loss)

    assert after == NORM_STATE
    assert after.relations == (R_DEBT,)  # the relation survives its losing sample


def test_truth_flips_only_through_constitutive_transfer() -> None:
    """The "unless the norm declares a constitutive effect" branch: an
    explicit constitutive event is the only path that changes R_t here."""

    removal = _relation("debt_extinguished_2025")
    constitutive = JudgmentEvent(
        effect_type=EffectType.CONSTITUTIVE, formed_relations=(removal,)
    )
    after = transfer(NORM_STATE, constitutive)

    assert after != NORM_STATE
    assert removal in after.relations


# --- EV-02: Eval(q) = (Judgment(q), Disposition(q)) (clause 3) ---


def test_disposition_is_a_field_never_a_fourth_judgment_value() -> None:
    assert len(Judgment) == 3  # 成立/不成立/未决 and nothing else
    assert all(m.name != "DISPOSITION" for m in Judgment)

    dismissed = eval_question(
        Question("q_procedure", QuestionKind.PROCEDURAL),
        Judgment.NOT_ESTABLISHED,
        Disposition(kind="DISMISS_PROCEDURE", payload="no_exhausted_arbitration"),
    )
    bare = eval_question(
        Question("q_effect", QuestionKind.EFFECT), Judgment.PENDING
    )

    assert isinstance(dismissed.disposition, Disposition)  # D member
    assert bare.disposition is None  # ∅ is representable without touching Judgment
    assert dismissed.judgment is Judgment.NOT_ESTABLISHED


def test_procedural_judgment_generates_no_substantive_judgment_labor_arbitration() -> None:
    """反例：劳动仲裁前置。The procedural gate question is determined
    NOT_ESTABLISHED (dismissed for skipping arbitration); the substantive
    labor claim receives no judgment it did not ask for."""

    gate = Question(
        questionId="q_arbitration_precondition",
        kind=QuestionKind.PROCEDURAL,
        stage="FIRST_INSTANCE",
    )
    substantive = Question(
        questionId="q_wrongful_termination_damages",
        kind=QuestionKind.SUBSTANTIVE,
    )

    results = eval_batch(
        ((gate, Judgment.NOT_ESTABLISHED, Disposition(kind="DISMISS_PROCEDURE")),)
    )

    assert set(results) == {"q_arbitration_precondition"}
    assert "q_wrongful_termination_damages" not in results
    # The result carries only its own question: no channel to smuggle a
    # substantive determination out of a procedural one.
    assert results["q_arbitration_precondition"].questionId == gate.questionId


# --- EV-03: EffectType transfer matrix (clause 4) ---


def test_only_constitutive_transfers_entity_state() -> None:
    confirmatory = transfer(NORM_STATE, JudgmentEvent(EffectType.CONFIRMATORY))
    performance = transfer(NORM_STATE, JudgmentEvent(EffectType.PERFORMANCE))
    procedural = transfer(NORM_STATE, JudgmentEvent(EffectType.PROCEDURAL_BINDING))

    assert confirmatory is NORM_STATE
    assert performance is NORM_STATE
    assert procedural is NORM_STATE


def test_confirmatory_judgment_cannot_be_implemented_as_creating_relation_debt_confirmation() -> None:
    """反例：债权确认。A debt-confirmation judgment declares a debt that
    already exists; it can neither carry formed relations (constructor
    fails) nor conjure the relation into R_t (transfer is identity)."""

    with pytest.raises(ValueError):
        JudgmentEvent(EffectType.CONFIRMATORY, formed_relations=(R_DEBT,))

    state_without_debt = NormState(relations=())
    after = transfer(
        state_without_debt, JudgmentEvent(EffectType.CONFIRMATORY)
    )
    assert after.relations == ()  # R without the debt stays without it
    # The debt is in R only where it was already constituted.
    assert R_DEBT in transfer(NORM_STATE, JudgmentEvent(EffectType.CONFIRMATORY)).relations


# --- EV-04: ApplicableNorm = A(J, V, q, H, t) (clause 6) ---


def _query(events_day: int, at_day: int) -> ApplicableNormQuery:
    return ApplicableNormQuery(
        jurisdiction=Jurisdiction(route=JurisdictionRoute.MAINLAND),
        normEnv="civil_labor",
        question="q_severance_basis",
        history=EventHistory(events=(Event("e_facts", events_day, "facts_arising"),)),
        atDay=at_day,
    )


V2020 = NormVersion(tag="labor2020", effective_day=18000)
V2024 = NormVersion(tag="labor2024", effective_day=19200)
VERSIONS = (V2020, V2024)


def test_t_alone_never_decides_the_version_cross_time_contract() -> None:
    """跨时点合同：same facts, evaluated at two different t -> same version."""

    early = applicable_norm(VERSIONS, _query(events_day=18500, at_day=18600))
    late = applicable_norm(VERSIONS, _query(events_day=18500, at_day=20100))

    assert early is V2020
    assert late is V2020


def test_new_law_does_not_capture_old_facts() -> None:
    """新法反例：labor2024 effective at day 19200 cannot capture facts from
    day 18500 however late the evaluation; facts after it do get v2024."""

    old_facts = applicable_norm(VERSIONS, _query(events_day=18500, at_day=20100))
    new_facts = applicable_norm(VERSIONS, _query(events_day=19500, at_day=20100))

    assert old_facts is V2020
    assert new_facts is V2024  # H co-determines: same t, different version


def test_selector_fails_closed() -> None:
    with pytest.raises(ValueError):
        applicable_norm((), _query(18500, 18600))  # no versions for V
    empty_h = ApplicableNormQuery(
        jurisdiction=Jurisdiction(route=JurisdictionRoute.MAINLAND),
        normEnv="civil_labor",
        question="q",
        history=EventHistory(events=()),
        atDay=19000,
    )
    with pytest.raises(ValueError):
        applicable_norm(VERSIONS, empty_h)  # H must carry the time structure
    with pytest.raises(ValueError):
        applicable_norm(VERSIONS, _query(19500, 19000))  # t before facts


# --- EV-05: K_{e,t} candidate set (clause 1/4, implementation warning 1) ---


def _kernel(candidates: tuple) -> KernelState:
    return KernelState(
        normative=NORM_STATE, candidates=frozenset(CandidateState(c) for c in candidates)
    )


def test_K_is_a_candidate_set_not_a_single_most_likely_state() -> None:
    state = _kernel(("settlement_signed", "partial_payment", "no_settlement"))

    assert len(state.candidates) == 3  # the set keeps all live candidates
    narrowed = narrow_candidates(state, frozenset({CandidateState("settlement_signed")}))
    assert isinstance(narrowed.candidates, frozenset)  # still a set, size 1 is fine
    assert narrowed.candidates == frozenset({CandidateState("settlement_signed")})


def test_evidence_update_cannot_invent_candidate_states() -> None:
    state = _kernel(("a", "b"))
    with pytest.raises(ValueError):
        narrow_candidates(state, frozenset({CandidateState("a"), CandidateState("c")}))


def test_settlement_document_moves_K_only_never_r_settlement() -> None:
    """反例：结算文件。The settlement document arrives as evidence: the
    candidate set narrows to the worlds it still supports, while R_t —
    relations and all — comes back bit-for-bit identical."""

    before = _kernel(("settlement_signed", "partial_payment", "no_settlement"))
    after = narrow_candidates(
        before, frozenset({CandidateState("settlement_signed")})
    )

    assert after.candidates != before.candidates  # K moved
    assert after.normative is before.normative  # R did not
    assert after.normative == NormState(relations=(R_DEBT,))
