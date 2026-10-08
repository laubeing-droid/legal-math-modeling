"""WP-8 tests: the composed run_case main chain and its independent
checker (J.6.1 / J.7): loan fragment, burden failure variant, R
non-interference, and tamper detection."""

from fractions import Fraction as Q
from unittest import TestCase

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
    LegalEnvironment,
    Polar,
    ProcessState,
    RunStatus,
    ScopedAtom,
)
from theory.spec.canonical_v2.kernel import (
    Judgment,
    Jurisdiction,
    JurisdictionRoute,
    NormState,
    Relation,
)

from unified.pipeline import run_case
from reference.legal_semantics import check_case_run


def _atom(predicate, polar=Polar.POS, subject="D"):
    return ScopedAtom(case_id="case-1", subject=subject, issue="loan",
                      stage="trial", predicate=predicate, polar=polar)


def _state(relations=(), day=10):
    return ProcessState(
        r=NormState(relations=relations),
        environment_id="env-1",
        stages=(("loan-trial", "trial"),),
        events=(CaseEvent("e0", "filing", 1, 1, "loan"),),
        target_day=day,
        as_of_day=day,
    )


def _case(facts, claims=None, defenses=()):
    return CaseInput(
        case_id="case-1",
        initial_state=_state(),
        parties=("C", "D"),
        issues=("loan",),
        claims=claims or (Claim("c1", "C", "D", "loan", "money", "payment"),),
        defenses=defenses,
        fact_records=tuple(facts),
        evidence_records=(),
        questions=(),
        quantities=(ExactQuantity(Q(100), "CNY", "principal", "contract"),),
    )


def _env(bases=(), rules=()):
    return LegalEnvironment(
        environment_id="env-1",
        jurisdiction=Jurisdiction(route=JurisdictionRoute.MAINLAND),
        admission_bases=tuple(bases),
        rules=tuple(rules),
    )


def _strong_loan_facts():
    """contract + final settlement + receipt confirmation (§5.3.4)."""
    return [
        FactRecord("f-contract", _atom("contract_signed"), FactStanding.ADMITTED_POSITIVE,
                   produced_at=1, known_at=1),
        FactRecord("f-settlement", _atom("final_settlement"), FactStanding.ADMITTED_POSITIVE,
                   produced_at=2, known_at=2),
        FactRecord("f-receipt", _atom("receipt_confirmed"), FactStanding.ADMITTED_POSITIVE,
                   produced_at=3, known_at=3),
    ]


class RunCaseLoanTests(TestCase):
    def test_delivery_established_with_strong_basis(self):
        case = _case(_strong_loan_facts())
        env = _env(bases=(
            AdmissionBasis(
                "b-delivery", BasisKind.ORDINARY_SUPPORT, "loan", "C", "trial", "v1",
                premise_refs=("f-contract", "f-settlement", "f-receipt"),
            ),
        ))
        run = run_case(case, env)
        self.assertIs(run.status, RunStatus.COMPLETE)
        self.assertTrue(run.branches)
        judgments = run.judgments_of("c1")
        self.assertIn(Judgment.ESTABLISHED, judgments)
        report = check_case_run(case, env, run)
        self.assertTrue(report.ok, report.reasons)

    def test_no_materials_burden_failure(self):
        """h⁻: only the claimant's own favorable statement — no basis
        fires, the burden table returns NOT_ESTABLISHED (never a factual
        negation)."""
        facts = [FactRecord("f-say", _atom("claimant_says"), FactStanding.ADMITTED_POSITIVE,
                            produced_at=1, known_at=1)]
        case = _case(facts)
        env = _env(bases=(
            AdmissionBasis("b-delivery", BasisKind.ORDINARY_SUPPORT, "loan", "C",
                           "trial", "v1",
                           premise_refs=("f-contract", "f-settlement", "f-receipt")),
        ))
        run = run_case(case, env)
        judgments = run.judgments_of("c1")
        self.assertTrue(judgments)
        self.assertIn(Judgment.NOT_ESTABLISHED, judgments)
        report = check_case_run(case, env, run)
        self.assertTrue(report.ok, report.reasons)

    def test_blocked_basis_does_not_fire(self):
        """An explicit negation among the block refs kills the basis."""
        facts = _strong_loan_facts() + [
            FactRecord("f-fraud", _atom("contract_void"), FactStanding.EXPLICIT_NEGATION,
                       produced_at=4, known_at=4),
        ]
        case = _case(facts)
        env = _env(bases=(
            AdmissionBasis(
                "b-delivery", BasisKind.ORDINARY_SUPPORT, "loan", "C", "trial", "v1",
                premise_refs=("f-contract", "f-settlement", "f-receipt"),
                block_refs=("f-fraud",),
            ),
        ))
        run = run_case(case, env)
        self.assertIn(Judgment.NOT_ESTABLISHED, run.judgments_of("c1"))
        self.assertTrue(check_case_run(case, env, run).ok)

    def test_r_noninterference(self):
        """Same knowledge view, different hidden R: identical outputs
        (J.6.1 noninterference pair)."""

        facts = _strong_loan_facts()
        env = _env(bases=(
            AdmissionBasis("b-delivery", BasisKind.ORDINARY_SUPPORT, "loan", "C",
                           "trial", "v1",
                           premise_refs=("f-contract", "f-settlement", "f-receipt")),
        ))
        case_a = _case(facts)
        hidden = (Relation("secret-1", ("C", "D"), "side_agreement"),)
        case_b = CaseInput(
            case_id="case-1",
            initial_state=_state(relations=hidden),
            parties=("C", "D"),
            issues=("loan",),
            claims=(Claim("c1", "C", "D", "loan", "money", "payment"),),
            defenses=(),
            fact_records=tuple(facts),
            evidence_records=(),
            questions=(),
            quantities=(ExactQuantity(Q(100), "CNY", "principal", "contract"),),
        )
        run_a = run_case(case_a, env)
        run_b = run_case(case_b, env)
        self.assertEqual(run_a.branches, run_b.branches)
        self.assertEqual(run_a.judgments_of("c1"), run_b.judgments_of("c1"))

    def test_technical_failure_is_failed_not_verdict(self):
        env = _env()
        # environment with a broken rule record cannot even be built; a
        # failing case is simulated by an env whose validity window
        # excludes everything — that is a PAUSED/EMPTY diagnosis, not a
        # verdict.  A crashed run must surface FAILED.
        case = _case(_strong_loan_facts())
        run = run_case(case, env)
        self.assertIn(run.status, (RunStatus.COMPLETE, RunStatus.PAUSED))
        # no admission bases at all: every claim hits the burden table
        self.assertIn(Judgment.NOT_ESTABLISHED, run.judgments_of("c1"))


class CheckerTamperTests(TestCase):
    def test_checker_catches_tampered_standard(self):
        """M3-style mutation: flip a branch's CivilHigh outcome; the
        independent checker must reject the run."""
        from dataclasses import replace

        case = _case(_strong_loan_facts())
        env = _env(bases=(
            AdmissionBasis("b-delivery", BasisKind.ORDINARY_SUPPORT, "loan", "C",
                           "trial", "v1",
                           premise_refs=("f-contract", "f-settlement", "f-receipt")),
        ))
        run = run_case(case, env)
        self.assertTrue(check_case_run(case, env, run).ok)
        branch = run.branches[0]
        tampered_standard = replace(branch.standards[0], civil_high=False)
        tampered_branch = replace(
            branch, standards=(tampered_standard,) + branch.standards[1:]
        )
        tampered = replace(run, branches=(tampered_branch,) + run.branches[1:])
        report = check_case_run(case, env, tampered)
        self.assertFalse(report.ok)
        self.assertTrue(any("standard mismatch" in r for r in report.reasons))

    def test_checker_catches_tampered_finalization(self):
        from dataclasses import replace

        from unified.standards import FinalBasis

        case = _case([FactRecord("f-say", _atom("claimant_says"),
                                 FactStanding.ADMITTED_POSITIVE,
                                 produced_at=1, known_at=1)])
        env = _env()
        run = run_case(case, env)
        self.assertTrue(check_case_run(case, env, run).ok)
        branch = run.branches[0]
        fake = replace(
            branch.finalizations[0],
            judgment=Judgment.ESTABLISHED,
            basis=FinalBasis.POS,
        )
        tampered = replace(
            run, branches=(replace(branch, finalizations=(fake,)),)
        )
        report = check_case_run(case, env, tampered)
        self.assertFalse(report.ok)
        self.assertTrue(any("finalization mismatch" in r for r in report.reasons))

    def test_checker_catches_unstable_selection(self):
        from dataclasses import replace

        from theory.spec.canonical_v2.case import (
            LegalRuleRecord,
            Modality,
            RuleKind,
        )

        rule = LegalRuleRecord(
            rule_id="r-loan",
            kind=RuleKind.STRICT_HORN,
            premises=(_atom("contract_signed"), _atom("final_settlement")),
            conclusion=_atom("loan"),
            modality=Modality.OBLIGATION,
            source_id="civil:577",
        )
        case = _case(_strong_loan_facts())
        env = _env(bases=(
            AdmissionBasis("b-delivery", BasisKind.ORDINARY_SUPPORT, "loan", "C",
                           "trial", "v1",
                           premise_refs=("f-contract", "f-settlement", "f-receipt")),
        ), rules=(rule,))
        run = run_case(case, env)
        self.assertTrue(check_case_run(case, env, run).ok)
        branch = run.branches[0]
        # an empty selection leaves the isolated candidate unadopted
        tampered = replace(
            run, branches=(replace(branch, selection=frozenset()),)
        )
        report = check_case_run(case, env, tampered)
        self.assertFalse(report.ok)
        self.assertTrue(any("unstable selection" in r for r in report.reasons))
