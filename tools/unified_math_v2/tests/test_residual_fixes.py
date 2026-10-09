"""Residual-defect regression tests (recon-confirmed pair, fixed on
BOTH the evaluator and the independent-checker sides):

* defect 1 — special channels (自认/免证/终局拘束/举证妨碍) must not
  confirm an issue against an ADOPTED contrary assertion on the same
  issue (§11.1 射程: same predicate/subject, reversed-polarity claim
  key) — the issue falls back to ordinary evaluation;
* defect 2 — a second AWARD_EFFECTIVE on a basis that still holds an
  effective TITLE_ENTITLEMENT is fail-closed: the evaluator raises
  (AWARD_REVOKED must supersede first) and the checker's own fold
  refuses the title, so a stacked ledger diverges on outstanding.
"""

from dataclasses import replace
from fractions import Fraction as Q
from unittest import TestCase

import pytest

from theory.spec.canonical_v2.case import (
    AdmissionBasis,
    BasisKind,
    CaseEvent,
    CaseInput,
    Claim,
    ExactQuantity,
    FactRecord,
    FactStanding,
    LedgerEntry,
    LedgerEntryKind,
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
)

from reference.legal_semantics import check_case_run, check_trace_run
from unified.pipeline import run_case
from unified.process import (
    LegalEventKind,
    ProcessEvent,
    outstanding_of,
    run_trace,
    step_event,
)


def _atom(predicate, polar=Polar.POS, subject="D", issue="loan"):
    return ScopedAtom(case_id="case-1", subject=subject, issue=issue,
                      stage="trial", predicate=predicate, polar=polar)


def _state(day=10):
    return ProcessState(
        r=NormState(relations=()),
        environment_id="env-1",
        stages=(("loan-trial", "trial"),),
        events=(CaseEvent("e0", "filing", 1, 1, "loan"),),
        target_day=day, as_of_day=day,
    )


def _case(facts):
    return CaseInput(
        case_id="case-1",
        initial_state=_state(),
        parties=("C", "D"),
        issues=("loan",),
        claims=(Claim("c1", "C", "D", "loan", "money", "payment"),),
        defenses=(),
        fact_records=tuple(facts),
        evidence_records=(),
        questions=(),
        quantities=(ExactQuantity(Q(100), "CNY", "principal", "contract"),),
    )


def _env(bases=()):
    return LegalEnvironment(
        environment_id="env-1",
        jurisdiction=Jurisdiction(route=JurisdictionRoute.MAINLAND),
        admission_bases=tuple(bases),
    )


def _admission_basis():
    return AdmissionBasis("b-admit", BasisKind.JUDICIAL_ADMISSION, "loan", "D",
                          "trial", "v1", premise_refs=("f-admit",))


def _admit_fact():
    return FactRecord("f-admit", _atom("court_admission"),
                      FactStanding.ADMITTED_POSITIVE,
                      produced_at=1, known_at=1)


def _award(event_id, amount, occurred=1):
    return ProcessEvent(
        event=CaseEvent(event_id, "award", occurred, occurred, "loan"),
        kind=LegalEventKind.AWARD_EFFECTIVE,
        basis_key="loan", amount=amount, authority_ref="court:2026-1",
    )


def _revoke(event_id, occurred=2):
    return ProcessEvent(
        event=CaseEvent(event_id, "revocation", occurred, occurred, "loan"),
        kind=LegalEventKind.AWARD_REVOKED,
        basis_key="loan", authority_ref="court:2026-2",
    )


class SpecialChannelContraryFactGuardTests(TestCase):
    """Defect 1 (§11.1 射程): a special channel must not confirm an
    issue when the SAME issue carries an adopted contrary assertion —
    same predicate/subject, reversed polarity (the claim-key contrary)."""

    def test_admission_conflicts_with_adopted_contrary_fact(self):
        facts = [
            _admit_fact(),
            FactRecord("f-contrary", _atom("loan", polar=Polar.NEG),
                       FactStanding.ADMITTED_POSITIVE,
                       produced_at=2, known_at=2),
        ]
        case = _case(facts)
        env = _env((_admission_basis(),))
        run = run_case(case, env)
        self.assertIs(run.status, RunStatus.COMPLETE)
        # the channel no longer confirms the issue directly; with no
        # strong template the ordinary path meets a ready burden window
        self.assertNotIn(Judgment.ESTABLISHED, run.judgments_of("c1"))
        self.assertIn(Judgment.NOT_ESTABLISHED, run.judgments_of("c1"))
        self.assertTrue(check_case_run(case, env, run).ok)

    def test_admission_without_conflict_still_establishes(self):
        case = _case([_admit_fact()])
        env = _env((_admission_basis(),))
        run = run_case(case, env)
        self.assertIn(Judgment.ESTABLISHED, run.judgments_of("c1"))
        self.assertTrue(check_case_run(case, env, run).ok)

    def test_other_subject_contrary_does_not_block(self):
        """ScopedAtom discipline: a contrary assertion on a DIFFERENT
        subject is a different atom — the channel still establishes."""
        facts = [
            _admit_fact(),
            FactRecord("f-other", _atom("loan", polar=Polar.NEG, subject="D2"),
                       FactStanding.ADMITTED_POSITIVE,
                       produced_at=2, known_at=2),
        ]
        case = _case(facts)
        env = _env((_admission_basis(),))
        run = run_case(case, env)
        self.assertIn(Judgment.ESTABLISHED, run.judgments_of("c1"))
        self.assertTrue(check_case_run(case, env, run).ok)


class ConsecutiveAwardGuardTests(TestCase):
    """Defect 2: consecutive AWARD_EFFECTIVE on one basis must not stack
    outstanding amounts — an explicit AWARD_REVOKED comes first."""

    def test_second_effective_award_on_live_title_rejected(self):
        state = step_event(_state(), _award("t1", Q(100))).next_state
        self.assertEqual(outstanding_of(state, "loan"), Q(100))
        with pytest.raises(ValueError, match="AWARD_REVOKED"):
            step_event(state, _award("t2", Q(100)))

    def test_revoke_then_reaward_keeps_single_entitlement(self):
        evs = (_award("t1", Q(100)), _revoke("r1"), _award("t2", Q(100)))
        final, notes = run_trace(_state(), evs)
        self.assertEqual(outstanding_of(final, "loan"), Q(100))
        report = check_trace_run(_state(), None, evs, final, notes)
        self.assertTrue(report.ok, report.reasons)

    def test_checker_refuses_stacked_awards(self):
        """The independent checker's own fold refuses a second award on
        a live title, so an actual ledger carrying BOTH titles (the old
        stacking behavior) diverges on outstanding and is reported."""
        evs = (_award("t1", Q(100)), _award("t2", Q(100)))
        stacked = (
            LedgerEntry("title:t1", LedgerEntryKind.TITLE_ENTITLEMENT, "loan",
                        "", "", Q(100), "t1", 1),
            LedgerEntry("title:t2", LedgerEntryKind.TITLE_ENTITLEMENT, "loan",
                        "", "", Q(100), "t2", 1),
        )
        actual = replace(
            _state(),
            ledger=stacked,
            events=tuple(CaseEvent(e, "award", 1, 1, "loan")
                         for e in ("t1", "t2")),
        )
        report = check_trace_run(_state(), None, evs, actual, ())
        self.assertFalse(report.ok)
        self.assertTrue(any("loan" in r for r in report.reasons))
