"""WP-7 tests: attempt actions, exact equilibrium checks, settlement,
and the §9 step semantics."""

from dataclasses import replace
from fractions import Fraction as Q
from unittest import TestCase

import pytest

from theory.spec.canonical_v2.case import (
    CaseEvent,
    LegalEnvironment,
    ProcessState,
)
from theory.spec.canonical_v2.kernel import Jurisdiction, JurisdictionRoute, NormState

from unified.process import (
    AttemptAction,
    GameWorld,
    InformationSet,
    LegalEventKind,
    NormalFormGame,
    ProcessEvent,
    award_legally_correct,
    gross_of,
    is_final,
    max_regret,
    mixed_payoff,
    outstanding_of,
    run_trace,
    settlement_zone,
    step_event,
    verify_equilibrium,
)


def _state(day=10):
    return ProcessState(
        r=NormState(relations=()),
        environment_id="env",
        target_day=day,
        as_of_day=day,
    )


def _event(eid, kind_value, occurred=5, observed=6, obj="loan"):
    return CaseEvent(
        event_id=eid, event_type=kind_value,
        occurred_at=occurred, observed_at=observed, object_ref=obj,
    )


class AttemptActionTests(TestCase):
    def test_menu_consistency(self):
        pay = AttemptAction("pay", "D", "pay")
        breach = AttemptAction("breach", "D", "breach")
        world = GameWorld({("D", ("t1",)): (pay, breach)})
        menu = world.menu(InformationSet("D", ("t1",)))
        self.assertEqual(len(menu), 2)
        self.assertEqual(world.phys_actions("D"), frozenset({"pay", "breach"}))

    def test_empty_menu_rejected(self):
        with pytest.raises(ValueError, match="leak state"):
            GameWorld({("D", ("t1",)): ()})

    def test_foreign_action_rejected(self):
        with pytest.raises(ValueError, match="belong"):
            GameWorld({("D", ("t1",)): (AttemptAction("x", "C", "pay"),)})

    def test_unknown_information_set_empty_menu(self):
        world = GameWorld({("D", ("t1",)): (AttemptAction("pay", "D", "pay"),)})
        self.assertEqual(world.menu(InformationSet("D", ("t2",))), ())


class EquilibriumTests(TestCase):
    def _prisoners(self):
        profiles = {
            ("C", "C"): (Q(3), Q(3)),
            ("C", "D"): (Q(0), Q(5)),
            ("D", "C"): (Q(5), Q(0)),
            ("D", "D"): (Q(1), Q(1)),
        }
        return NormalFormGame(("P1", "P2"), (("C", "D"), ("C", "D")), profiles)

    def test_defect_is_equilibrium(self):
        game = self._prisoners()
        sigma = ([Q(0), Q(1)], [Q(0), Q(1)])
        self.assertTrue(verify_equilibrium(game, sigma))
        gain, witness = max_regret(game, sigma)
        self.assertEqual(gain, Q(0))

    def test_cooperate_is_not(self):
        game = self._prisoners()
        sigma = ([Q(1), Q(0)], [Q(1), Q(0)])
        self.assertFalse(verify_equilibrium(game, sigma))
        gain, (player, pure) = max_regret(game, sigma)
        self.assertEqual(gain, Q(2))
        self.assertEqual(pure, "D")

    def test_mixed_expected_value_exact(self):
        game = self._prisoners()
        sigma = ([Q(1, 2), Q(1, 2)], [Q(1, 2), Q(1, 2)])
        values = mixed_payoff(game, sigma)
        self.assertEqual(values[0], Q(9, 4))
        self.assertEqual(values[1], Q(9, 4))

    def test_anti_coordination_mixed_equilibrium(self):
        profiles = {
            ("A", "A"): (Q(0), Q(0)),
            ("A", "B"): (Q(2), Q(1)),
            ("B", "A"): (Q(1), Q(2)),
            ("B", "B"): (Q(0), Q(0)),
        }
        game = NormalFormGame(("R", "C"), (("A", "B"), ("A", "B")), profiles)
        # u_R(A)=2(1−y), u_R(B)=y are equal at y=2/3; symmetric for the
        # column player: both mixing 2/3-on-A is the mixed equilibrium.
        sigma = ([Q(2, 3), Q(1, 3)], [Q(2, 3), Q(1, 3)])
        self.assertTrue(verify_equilibrium(game, sigma))
        # The staggered same-mix profile is NOT an equilibrium here.
        bad = ([Q(1, 3), Q(2, 3)], [Q(1, 3), Q(2, 3)])
        self.assertFalse(verify_equilibrium(game, bad))

    def test_float_payoff_rejected(self):
        with pytest.raises(TypeError):
            NormalFormGame(
                ("P",), (("a",),), {("a",): (0.5,)}  # type: ignore[arg-type]
            )


class SettlementTests(TestCase):
    def test_intersection(self):
        zone = settlement_zone(Q(10), Q(50), Q(15), Q(20), Q(60))
        self.assertFalse(zone.empty)
        self.assertEqual(zone.low, Q(15))
        self.assertEqual(zone.high, Q(40))

    def test_empty_reported_not_midpointed(self):
        zone = settlement_zone(Q(10), Q(50), Q(45), Q(20), Q(60))
        self.assertTrue(zone.empty)

    def test_float_rejected(self):
        with pytest.raises(TypeError):
            settlement_zone(0.5, Q(1), Q(0), Q(0), Q(1))  # type: ignore[arg-type]


class StepEventTests(TestCase):
    def _title(self, state, basis, amount):
        ev = ProcessEvent(
            event=_event("t1", "award"),
            kind=LegalEventKind.AWARD_EFFECTIVE,
            basis_key=basis,
            amount=amount,
            authority_ref="court:2026-1",
        )
        return step_event(state, ev).next_state

    def test_effective_award_needs_authority(self):
        with pytest.raises(ValueError, match="authority"):
            step_event(
                _state(),
                ProcessEvent(
                    event=_event("t1", "award"),
                    kind=LegalEventKind.AWARD_EFFECTIVE,
                    basis_key="loan",
                    amount=Q(100),
                ),
            )

    def test_actual_issuance_records_without_effect(self):
        outcome = step_event(
            _state(),
            ProcessEvent(event=_event("a1", "award"), kind=LegalEventKind.AWARD_ISSUED),
        )
        self.assertEqual(len(outcome.next_state.events), 1)
        # no title entitlement appeared: ActualIssued != Effective
        self.assertEqual(outstanding_of(outcome.next_state, "loan"), Q(0))
        self.assertIn("no effect asserted", outcome.notes[0])

    def test_payment_waterfall(self):
        state = self._title(_state(), "loan", Q(100))
        outcome = step_event(
            state,
            ProcessEvent(
                event=_event("p1", "payment"),
                kind=LegalEventKind.PAYMENT_PERFORMED,
                amount=Q(40),
                debt_order=("loan",),
            ),
        )
        after = outcome.next_state
        self.assertEqual(outstanding_of(after, "loan"), Q(60))
        self.assertEqual(gross_of(after, "loan"), Q(40))

    def test_overpay_recorded_in_gross_only(self):
        state = self._title(_state(), "loan", Q(100))
        outcome = step_event(
            state,
            ProcessEvent(
                event=_event("p1", "payment"),
                kind=LegalEventKind.PAYMENT_PERFORMED,
                amount=Q(140),
                debt_order=("loan",),
            ),
        )
        after = outcome.next_state
        # satisfied caps at entitlement; a single-basis payment's FULL
        # receipt (overpayment included) is attributable to the basis —
        # the Rcash formula never truncates at the entitlement
        from unified.process import gross_total_of
        self.assertEqual(outstanding_of(after, "loan"), Q(0))
        self.assertEqual(gross_of(after, "loan"), Q(140))
        self.assertEqual(gross_total_of(after, "loan"), Q(140))
        self.assertIn("overpay", outcome.notes[-1])

    def test_multi_debt_waterfall_order(self):
        state = self._title(
            self._title(_state(), "wage", Q(10)), "loan", Q(100)
        )
        outcome = step_event(
            state,
            ProcessEvent(
                event=_event("p1", "payment"),
                kind=LegalEventKind.PAYMENT_PERFORMED,
                amount=Q(12),
                debt_order=("wage", "loan"),
            ),
        )
        after = outcome.next_state
        self.assertEqual(outstanding_of(after, "wage"), Q(0))
        self.assertEqual(outstanding_of(after, "loan"), Q(98))

    def test_evidence_submission_visibility(self):
        outcome = step_event(
            _state(),
            ProcessEvent(
                event=_event("e1", "filing", occurred=5, observed=9),
                kind=LegalEventKind.EVIDENCE_SUBMITTED,
            ),
        )
        after = outcome.next_state
        self.assertEqual(len(after.evidence), 1)
        self.assertEqual(after.evidence[0].known_at, 9)
        self.assertEqual(after.visible_evidence(8), ())
        self.assertEqual(len(after.visible_evidence(9)), 1)

    def test_proposal_does_not_mutate_environment(self):
        env = LegalEnvironment(
            environment_id="env",
            jurisdiction=Jurisdiction(route=JurisdictionRoute.MAINLAND),
        )
        outcome = step_event(
            _state(),
            ProcessEvent(
                event=_event("n1", "proposal"),
                kind=LegalEventKind.NORM_CHANGE_PROPOSED,
            ),
            env=env,
        )
        self.assertIs(outcome.next_env, env)  # bit-for-bit identical

    def test_run_trace_folds(self):
        state = self._title(_state(), "loan", Q(100))
        events = (
            ProcessEvent(
                event=_event("p1", "payment"),
                kind=LegalEventKind.PAYMENT_PERFORMED,
                amount=Q(30),
                debt_order=("loan",),
            ),
            ProcessEvent(
                event=_event("p2", "payment"),
                kind=LegalEventKind.PAYMENT_PERFORMED,
                amount=Q(20),
                debt_order=("loan",),
            ),
        )
        final, _notes = run_trace(state, events)
        self.assertEqual(outstanding_of(final, "loan"), Q(50))
        # title event + two payments
        self.assertEqual(len(final.events), 3)

    def test_effective_award_is_not_performance(self):
        # A title alone never reduces the outstanding amount via "payment":
        # only PERFORMANCE events create SATISFIED entries.
        state = self._title(_state(), "loan", Q(100))
        self.assertEqual(outstanding_of(state, "loan"), Q(100))
        self.assertEqual(gross_of(state, "loan"), Q(0))


class TitleLifecycleTests(TestCase):
    def _title_state(self, basis="loan", amount=Q(100)):
        ev = ProcessEvent(
            event=_event("t1", "award"),
            kind=LegalEventKind.AWARD_EFFECTIVE,
            basis_key=basis,
            amount=amount,
            authority_ref="court:2026-1",
        )
        return step_event(_state(), ev).next_state

    def test_revocation_supersedes_title_keeps_history(self):
        state = self._title_state()
        state = step_event(
            state,
            ProcessEvent(
                event=_event("p1", "payment"),
                kind=LegalEventKind.PAYMENT_PERFORMED,
                amount=Q(40), debt_order=("loan",),
            ),
        ).next_state
        revoked = step_event(
            state,
            ProcessEvent(
                event=_event("r1", "revocation"),
                kind=LegalEventKind.AWARD_REVOKED,
                basis_key="loan",
                authority_ref="court:2026-2",
            ),
        ).next_state
        # the enforceable amount drops to zero…
        self.assertEqual(outstanding_of(revoked, "loan"), Q(0))
        # …but the payment history is untouched (revocation never erases
        # payments already made)
        self.assertEqual(gross_of(revoked, "loan"), Q(40))

    def test_revocation_requires_authority(self):
        with pytest.raises(ValueError, match="authority"):
            step_event(
                _state(),
                ProcessEvent(
                    event=_event("r1", "revocation"),
                    kind=LegalEventKind.AWARD_REVOKED,
                    basis_key="loan",
                ),
            )

    def test_multi_basis_payment_no_double_count(self):
        state = self._title_state("wage", Q(10))
        state = step_event(
            state,
            ProcessEvent(
                event=_event("t2", "award"),
                kind=LegalEventKind.AWARD_EFFECTIVE,
                basis_key="loan", amount=Q(100),
                authority_ref="court:2026-1",
            ),
        ).next_state
        after = step_event(
            state,
            ProcessEvent(
                event=_event("p1", "payment"),
                kind=LegalEventKind.PAYMENT_PERFORMED,
                amount=Q(15), debt_order=("wage", "loan"),
            ),
        ).next_state
        self.assertEqual(gross_of(after, "wage"), Q(10))
        self.assertEqual(gross_of(after, "loan"), Q(5))
        self.assertEqual(gross_of(after, "wage") + gross_of(after, "loan"), Q(15))

    def test_is_final(self):
        from theory.spec.canonical_v2.case import ProcessState as PS
        decided = PS(r=NormState(relations=()), environment_id="e",
                     stages=(("p1", "decided"),), target_day=5, as_of_day=5)
        self.assertTrue(is_final(decided, "p1"))
        appealed = replace(decided, events=(
            CaseEvent("a1", "appeal_filed", 6, 6, "p1"),), as_of_day=7, target_day=5)
        self.assertFalse(is_final(appealed, "p1"))
        trial = PS(r=NormState(relations=()), environment_id="e",
                   stages=(("p1", "trial"),), target_day=5, as_of_day=5)
        self.assertFalse(is_final(trial, "p1"))

    def test_award_legally_correct(self):
        class FakeFinalization:
            def __init__(self, judgment):
                self.judgment = judgment
        class FakeBranch:
            def __init__(self, judgments):
                self.finalizations = [FakeFinalization(j) for j in judgments]
        class FakeRun:
            def __init__(self, branches):
                self.branches = branches
        from theory.spec.canonical_v2.kernel import Judgment as J
        self.assertIs(award_legally_correct(
            FakeRun([FakeBranch([J.ESTABLISHED])]), "loan"), True)
        self.assertIs(award_legally_correct(
            FakeRun([FakeBranch([J.ESTABLISHED]), FakeBranch([J.NOT_ESTABLISHED])]),
            "loan"), None)
        self.assertIs(award_legally_correct(FakeRun([]), "loan"), None)
