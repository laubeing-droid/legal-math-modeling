"""WP-1 tests: exact JSON discipline, rounding, and case-carrier contracts.

Covers the J.4.3 exact-json family (duplicate keys, NaN/Infinity, JSON
decimals, bools, big numerators, negative denominators, noncanonical
components), the four rounding modes at half points, and the J.4.1
carrier invariants (no callable rules, no hidden-R read, standing and
time-axis separation).
"""

from fractions import Fraction as Q
from unittest import TestCase

import pytest

from theory.spec.canonical_v2.case import (
    AdmissionBasis,
    BasisKind,
    CaseEvent,
    CaseInput,
    Claim,
    Defense,
    ExactQuantity,
    FactRecord,
    FactStanding,
    KnowledgeView,
    LegalEnvironment,
    LegalRuleRecord,
    LedgerEntry,
    LedgerEntryKind,
    LocalAssessmentCard,
    Polar,
    ProcessState,
    RuleGuard,
    RuleKind,
    RunStatus,
    ScopedAtom,
    AuthorizedAssessment,
    fraction_from_json,
    fraction_to_json,
    knowledge_view,
    load_exact_json,
    round_fraction,
)
from theory.spec.canonical_v2.kernel import Jurisdiction, JurisdictionRoute, NormState
from theory.spec.canonical_v2.types import Modality


def _atom(predicate="delivered", subject="D", polar=Polar.POS, issue="loan"):
    return ScopedAtom(
        case_id="case-1", subject=subject, issue=issue, stage="trial",
        predicate=predicate, polar=polar,
    )


def _rule(record_id="r1", head_predicate="payment_due"):
    return LegalRuleRecord(
        rule_id=record_id,
        kind=RuleKind.STRICT_HORN,
        premises=(_atom("signed"), _atom("delivered")),
        conclusion=_atom(head_predicate),
        modality=Modality.OBLIGATION,
        source_id="civil-code:577",
    )


def _state(day=10):
    return ProcessState(
        r=NormState(relations=()),
        environment_id="env-1",
        stages=(("loan-trial", "trial"),),
        events=(CaseEvent(event_id="e1", event_type="hearing", occurred_at=5,
                          observed_at=6, object_ref="loan"),),
        target_day=8,
        as_of_day=day,
    )


def _case():
    return CaseInput(
        case_id="case-1",
        initial_state=_state(),
        parties=("C", "D"),
        issues=("loan",),
        claims=(Claim("c1", "C", "D", "loan-contract", "money", "payment"),),
        defenses=(Defense("d1", "D", ("c1",), "limitation", at_day=9),),
        fact_records=(
            FactRecord("f1", _atom("signed"), FactStanding.ADMITTED_POSITIVE,
                       source_ids=("contract",), produced_at=1, known_at=1),
            FactRecord("f2", _atom("payment"), FactStanding.NOT_PROVED,
                       produced_at=2, known_at=3),
        ),
        evidence_records=(),
        questions=(),
        quantities=(ExactQuantity(Q(100), "CNY", "principal", "contract"),),
    )


class ExactJsonTests(TestCase):
    def test_roundtrip_canonical(self):
        text = '{"a": {"n": "-17", "d": "100"}, "b": 3}'
        obj = load_exact_json(text)
        self.assertEqual(fraction_from_json(obj["a"]), Q(-17, 100))
        self.assertEqual(fraction_to_json(Q(-17, 100)), {"n": "-17", "d": "100"})

    def test_duplicate_key_rejected(self):
        with pytest.raises(ValueError, match="duplicate JSON key"):
            load_exact_json('{"a": 1, "a": 2}')

    def test_nan_infinity_rejected(self):
        with pytest.raises(ValueError):
            load_exact_json('{"a": NaN}')
        with pytest.raises(ValueError):
            load_exact_json('{"a": Infinity}')

    def test_json_decimal_rejected(self):
        # 0.1 is a binary float in disguise; exact inputs carry strings.
        with pytest.raises(ValueError, match="non-integer JSON number"):
            load_exact_json('{"a": 0.1}')

    def test_rational_schema_enforced(self):
        with pytest.raises(ValueError, match="expected rational object"):
            fraction_from_json({"n": "1"})
        with pytest.raises(ValueError, match="decimal strings"):
            fraction_from_json({"n": 1, "d": "2"})
        with pytest.raises(ValueError, match="noncanonical"):
            fraction_from_json({"n": "1", "d": "-2"})
        with pytest.raises(ValueError, match="noncanonical"):
            fraction_from_json({"n": "+3", "d": "2"})

    def test_non_reduced_input_is_reduced_on_read(self):
        # Canonical decimal components are required; the fraction itself is
        # normalized to lowest terms on parse (J.4.3: output reduced).
        self.assertEqual(fraction_from_json({"n": "2", "d": "4"}), Q(1, 2))

    def test_big_numerator_exact(self):
        n = 10**40 + 7
        value = fraction_from_json({"n": str(n), "d": "3"})
        self.assertEqual(value, Q(n, 3))

    def test_fraction_to_json_requires_fraction(self):
        with pytest.raises(TypeError):
            fraction_to_json(0.5)


class RoundingTests(TestCase):
    def test_half_up(self):
        self.assertEqual(round_fraction(Q(1, 2), "HALF_UP"), 1)
        self.assertEqual(round_fraction(Q(-1, 2), "HALF_UP"), -1)
        self.assertEqual(round_fraction(Q(3, 2), "HALF_UP"), 2)
        self.assertEqual(round_fraction(Q(-3, 2), "HALF_UP"), -2)
        self.assertEqual(round_fraction(Q(7, 3), "HALF_UP"), 2)

    def test_half_down(self):
        self.assertEqual(round_fraction(Q(1, 2), "HALF_DOWN"), 0)
        self.assertEqual(round_fraction(Q(-1, 2), "HALF_DOWN"), 0)
        self.assertEqual(round_fraction(Q(3, 2), "HALF_DOWN"), 1)
        self.assertEqual(round_fraction(Q(5, 2), "HALF_DOWN"), 2)

    def test_down_and_up(self):
        self.assertEqual(round_fraction(Q(9, 10), "DOWN"), 0)
        self.assertEqual(round_fraction(Q(-9, 10), "DOWN"), 0)
        self.assertEqual(round_fraction(Q(9, 10), "UP"), 1)
        self.assertEqual(round_fraction(Q(-9, 10), "UP"), -1)
        self.assertEqual(round_fraction(Q(-1, 1), "UP"), -1)

    def test_unknown_policy_is_error(self):
        with pytest.raises(ValueError, match="unknown rounding policy"):
            round_fraction(Q(1, 2), "BANKERS")

    def test_float_rejected(self):
        with pytest.raises(TypeError):
            round_fraction(0.5, "HALF_UP")  # type: ignore[arg-type]


class CarrierContractTests(TestCase):
    def test_rule_rejects_callable(self):
        with pytest.raises(TypeError, match="not callables"):
            LegalRuleRecord(
                rule_id="bad", kind=RuleKind.STRICT_HORN,
                premises=(_atom(),), conclusion=lambda: None,  # type: ignore[arg-type]
                modality=Modality.OBLIGATION, source_id="s",
            )

    def test_rule_validity_window(self):
        rule = _rule().with_validity("CN", from_day=5, to_day=9)
        self.assertTrue(rule.applicable_at("CN", 7))
        self.assertFalse(rule.applicable_at("CN", 4))
        self.assertFalse(rule.applicable_at("CN", 10))
        self.assertFalse(rule.applicable_at("US", 7))

    def test_atom_scoping_separates_subjects(self):
        a = _atom(subject="D")
        b = _atom(subject="G")
        self.assertNotEqual(a, b)

    def test_known_at_not_before_produced(self):
        with pytest.raises(ValueError, match="known before"):
            FactRecord("f", _atom(), FactStanding.ADMITTED_POSITIVE,
                       produced_at=5, known_at=4)

    def test_event_observation_order(self):
        with pytest.raises(ValueError, match="observed before"):
            CaseEvent(event_id="e", event_type="filing", occurred_at=3,
                      observed_at=2, object_ref="x")

    def test_ledger_requires_fraction(self):
        with pytest.raises(ValueError, match="nonnegative Fractions"):
            LedgerEntry("l", LedgerEntryKind.GROSS_RECEIVED, "loan", "D",
                        "loan-trial", 100, "e1", 1)  # type: ignore[arg-type]

    def test_quantity_rejects_float(self):
        with pytest.raises(TypeError):
            ExactQuantity(0.5, "CNY", "principal")  # type: ignore[arg-type]

    def test_as_of_not_before_target(self):
        with pytest.raises(ValueError, match="as_of"):
            ProcessState(r=NormState(relations=()), target_day=5, as_of_day=4)

    def test_duplicate_claim_rejected(self):
        claim = Claim("c1", "C", "D", "b", "o", "r")
        with pytest.raises(ValueError, match="duplicate claim"):
            CaseInput(
                case_id="x", initial_state=_state(), parties=("C", "D"),
                issues=("i",), claims=(claim, claim), defenses=(),
                fact_records=(), evidence_records=(), questions=(), quantities=(),
            )

    def test_run_status_axes_distinct(self):
        # The four execution states exist; legal undetermined lives in
        # Judgment/kernel, not here.
        self.assertEqual(
            {s.value for s in RunStatus},
            {"COMPLETE", "SOUND_PARTIAL", "PAUSED", "FAILED"},
        )


class KnowledgeViewTests(TestCase):
    def test_view_reads_no_hidden_r(self):
        case = _case()
        env = LegalEnvironment(
            environment_id="env-1",
            jurisdiction=Jurisdiction(route=JurisdictionRoute.MAINLAND),
        )
        view = knowledge_view(case, env)
        # The view is built from case tables and visible evidence only.
        self.assertEqual(view.case_id, "case-1")
        self.assertNotIn("r", view.__dict__)
        self.assertEqual(len(view.facts), 2)
        self.assertEqual(view.facts[1].standing, FactStanding.NOT_PROVED)

    def test_cards_filtered_by_visible_materials(self):
        case = _case()
        env = LegalEnvironment(
            environment_id="env-1",
            jurisdiction=Jurisdiction(route=JurisdictionRoute.MAINLAND),
            authorized_assessments=(
                AuthorizedAssessment("a1", "expert", "auth-1", "loan", "v1",
                                     materials=()),
                AuthorizedAssessment("a2", "expert", "auth-1", "loan", "v1",
                                     materials=("unseen-evidence",)),
            ),
        )
        view = knowledge_view(case, env)
        self.assertEqual([c.assessment_ref for c in view.cards], ["a1"])

    def test_evidence_visibility_projection(self):
        from theory.spec.canonical_v2.case import EvidenceRecord
        early = EvidenceRecord("ev1", "art1", "bank", known_at=2)
        late = EvidenceRecord("ev2", "art2", "bank", known_at=99)
        state = ProcessState(
            r=NormState(relations=()), environment_id="env",
            evidence=(early, late), target_day=1, as_of_day=10,
        )
        self.assertEqual(state.visible_evidence(10), (early,))
        self.assertEqual(state.visible_evidence(99), (early, late))


class AdmissionBasisTests(TestCase):
    def test_channels_are_distinct_kinds(self):
        kinds = {k for k in BasisKind}
        self.assertIn(BasisKind.JUDICIAL_ADMISSION, kinds)
        self.assertIn(BasisKind.EVIDENCE_OBSTRUCTION, kinds)
        basis = AdmissionBasis("b1", BasisKind.PRESUMPTION, "loan", "C",
                               "trial", "v1", premise_refs=("f1",))
        self.assertEqual(basis.kind, BasisKind.PRESUMPTION)


class GuardTests(TestCase):
    def test_guard_record(self):
        guard = RuleGuard(rule_instance="r1", kind="exception", slot="grace",
                          scope=("loan",), source="contract:5")
        rule = LegalRuleRecord(
            rule_id="r-guarded", kind=RuleKind.DEFEASIBLE,
            premises=(_atom(),), conclusion=_atom("waived"),
            modality=Modality.CONSTITUTIVE, guards=(guard,), source_id="s",
        )
        self.assertEqual(rule.guards[0].kind, "exception")
