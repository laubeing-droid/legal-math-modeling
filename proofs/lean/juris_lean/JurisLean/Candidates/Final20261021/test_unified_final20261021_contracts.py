"""Synthetic contract oracle and mutation checks, NOT execution of Lean.

Run explicitly from this directory or by unittest/pytest path. No bytecode,
cache, network, real case material, or external writes are needed.
The actual Lean consumer assertions are in Acceptance.lean and await CI.
"""
from dataclasses import dataclass, replace
from fractions import Fraction as Q
from itertools import product
import unittest


@dataclass(frozen=True)
class State:
    debt: Q = Q(10)
    allocated: Q = Q(0)
    cash: Q = Q(0)
    remainder: Q = Q(0)
    accrual: Q = Q(0)
    used: frozenset = frozenset()
    forms: bool = True
    claim: str = "UNKNOWN"
    procedure: str = "OPEN"
    revision: int = 0
    currency: str = "SYN"
    unit: str = "unit"
    rest_claim: Q | None = None
    eligible: bool = False
    refund_cash: Q = Q(0)


def payment_vector(before, amount, key):
    """Independent reference arithmetic for the declared min-allocation rule."""
    allocated = min(amount, before.debt)
    return replace(before, debt=before.debt-allocated,
                   allocated=before.allocated+allocated, cash=before.cash+amount,
                   remainder=before.remainder+amount-allocated,
                   used=before.used | {key}, revision=before.revision+1)


def check_payment(before, after, *, status, amount=Q(7), key=1,
                  applicable="YES", identity=True, permitted=True, previous=None):
    """Reject a report when it breaks a named contract, including no-known-post UNKNOWN."""
    if status == "UNKNOWN_COMMIT":
        if after is not None:
            raise ValueError("UNKNOWN_POSTSTATE_ASSERTED")
        return
    if status in {"PENDING", "REJECTED_NO_COMMIT", "CONFLICT", "REPLAY"}:
        if after.used != before.used:
            raise ValueError("BURNED_BY_UNKNOWN" if status == "PENDING" else "U_WRITE_ON_NONCOMMIT")
        if after != before:
            raise ValueError("NONCOMMIT_BUSINESS_WRITE")
        return
    if status != "COMMITTED":
        raise ValueError("UNKNOWN_STATUS")
    if applicable != "YES" or not identity or not permitted or key in before.used or amount < 0:
        raise ValueError("COMMIT_PRECONDITION")
    if previous is not None and previous != before:
        raise ValueError("NON_CONTINUOUS_CONSUME")
    if (after.forms, after.claim, after.procedure) != (before.forms, before.claim, before.procedure):
        raise ValueError("LAYER_COLLAPSE")
    expected = payment_vector(before, amount, key)
    if after != expected:
        raise ValueError("STATE_CONSERVATION_MISMATCH")


def check_accrual(before, after, amount):
    if (after.cash, after.refund_cash) != (before.cash, before.refund_cash):
        raise ValueError("ACCRUAL_CASH_COLLAPSE")
    if after != replace(before, debt=before.debt+amount, accrual=before.accrual+amount):
        raise ValueError("ACCRUAL_FRAME")


def check_restitution(before, after, node, *, claim_amount=None, paid=Q(0)):
    if node == "N1":
        if claim_amount is None or claim_amount < 0:
            raise ValueError("REST_CLAIM_MISSING")
        expected = replace(before, rest_claim=claim_amount)
    elif node == "N2":
        if before.rest_claim is None:
            raise ValueError("REST_CLAIM_MISSING")
        expected = replace(before, eligible=True)
    elif node == "N3":
        if before.rest_claim is None:
            raise ValueError("PREMATURE_CASH")
        if not before.eligible:
            raise ValueError("AUTO_FULL_REFUND")
        expected = replace(before, rest_claim=max(Q(0), before.rest_claim-paid),
                           refund_cash=before.refund_cash+paid)
    else:
        raise ValueError("REST_NODE_UNKNOWN")
    if after != expected:
        raise ValueError("PREMATURE_CASH" if node != "N3" else "REST_FRAME")


def add_amount(a, b):
    av, ac, au, ar = a
    bv, bc, bu, br = b
    if (ac, au, ar) != (bc, bu, br):
        raise ValueError("UNIT_BINDING_MISSING")
    return av+bv, ac, au, ar


class TestUnifiedContracts(unittest.TestCase):
    def test_general_nonnegative_rational_conservation(self):
        for d, p in product([Q(0), Q(1, 2), Q(1), Q(10)], repeat=2):
            s = State(debt=d)
            after = payment_vector(s, p, 1)
            check_payment(s, after, status="COMMITTED", amount=p)
            self.assertEqual(d, after.debt+after.allocated)
            self.assertEqual(p, after.allocated+after.remainder)

    def test_continuous_two_steps(self):
        s0 = State()
        s1 = payment_vector(s0, Q(7), 1)
        s2 = payment_vector(s1, Q(7), 2)
        check_payment(s1, s2, status="COMMITTED", key=2, previous=s1)
        self.assertEqual((s1.debt, s2.debt, s2.allocated, s2.cash, s2.remainder), (3, 0, 10, 14, 4))

    def test_two_initial_reads_rejected(self):
        s0 = State()
        s1 = payment_vector(s0, Q(7), 1)
        with self.assertRaisesRegex(ValueError, "NON_CONTINUOUS_CONSUME"):
            check_payment(s1, payment_vector(s0, Q(7), 2), status="COMMITTED", key=2, previous=s0)

    def test_zero_committed_yes_consumes_identity(self):
        s = State()
        after = payment_vector(s, Q(0), 1)
        check_payment(s, after, status="COMMITTED", amount=Q(0))
        self.assertIn(1, after.used)
        self.assertEqual(after.debt, s.debt)

    def test_unknown_commit_has_no_known_post(self):
        check_payment(State(), None, status="UNKNOWN_COMMIT")
        with self.assertRaisesRegex(ValueError, "UNKNOWN_POSTSTATE_ASSERTED"):
            check_payment(State(), State(), status="UNKNOWN_COMMIT")

    def test_pending_identity_unknown_not_burned(self):
        s = State()
        check_payment(s, s, status="PENDING", identity=False)
        with self.assertRaisesRegex(ValueError, "BURNED_BY_UNKNOWN"):
            check_payment(s, replace(s, used=frozenset({1})), status="PENDING", identity=False)

    def test_unknown_or_no_applicability_never_commits(self):
        for applicability in ["UNKNOWN", "NO"]:
            with self.assertRaisesRegex(ValueError, "COMMIT_PRECONDITION"):
                check_payment(State(), payment_vector(State(), Q(0), 1),
                              status="COMMITTED", amount=Q(0), applicable=applicability)

    def test_rejection_conflict_and_replay_preserve_current(self):
        s1 = payment_vector(State(), Q(7), 1)
        s2 = payment_vector(s1, Q(7), 2)
        for status in ["REJECTED_NO_COMMIT", "CONFLICT", "REPLAY"]:
            check_payment(s2, s2, status=status)
        check_payment(s1, s1, status="REJECTED_NO_COMMIT", key=2)
        self.assertEqual(s1.debt, 3)

    def test_cannot_commit_same_canonical_identity_twice(self):
        s1 = payment_vector(State(), Q(7), 1)
        with self.assertRaisesRegex(ValueError, "COMMIT_PRECONDITION"):
            check_payment(s1, payment_vector(s1, Q(7), 1), status="COMMITTED")

    def test_three_observations_and_layer_collapse(self):
        s = State()
        after = payment_vector(s, Q(10), 1)
        self.assertEqual((after.forms, after.debt, after.claim, after.procedure), (True, 0, "UNKNOWN", "OPEN"))
        with self.assertRaisesRegex(ValueError, "LAYER_COLLAPSE"):
            check_payment(s, replace(after, forms=False, procedure="CLOSED"), status="COMMITTED", amount=Q(10))

    def test_false_reported_after_debt(self):
        s = State()
        after = payment_vector(s, Q(7), 1)
        with self.assertRaisesRegex(ValueError, "STATE_CONSERVATION_MISMATCH"):
            check_payment(s, replace(after, debt=Q(10)), status="COMMITTED")

    def test_accrual_has_no_cash(self):
        s = State()
        after = replace(s, debt=Q(11), accrual=Q(1))
        check_accrual(s, after, Q(1))
        with self.assertRaisesRegex(ValueError, "ACCRUAL_CASH_COLLAPSE"):
            check_accrual(s, replace(after, cash=Q(1)), Q(1))

    def test_restitution_three_nodes_partial_amount(self):
        s = payment_vector(State(), Q(7), 1)
        n1 = replace(s, rest_claim=Q(3))
        n2 = replace(n1, eligible=True)
        n3 = replace(n2, rest_claim=Q(0), refund_cash=Q(3))
        check_restitution(s, n1, "N1", claim_amount=Q(3))
        check_restitution(n1, n2, "N2")
        check_restitution(n2, n3, "N3", paid=Q(3))
        self.assertEqual((n3.debt, n3.cash, n3.refund_cash), (3, 7, 3))

    def test_n1_premature_cash(self):
        with self.assertRaisesRegex(ValueError, "PREMATURE_CASH"):
            check_restitution(State(), replace(State(), refund_cash=Q(7)), "N3", paid=Q(7))

    def test_n2_auto_full_refund(self):
        before = replace(State(), rest_claim=Q(3))
        with self.assertRaisesRegex(ValueError, "AUTO_FULL_REFUND"):
            check_restitution(before, replace(before, refund_cash=Q(7)), "N3", paid=Q(7))

    def test_no_cash_on_claim_or_eligibility(self):
        before = replace(State(), rest_claim=Q(3))
        with self.assertRaisesRegex(ValueError, "PREMATURE_CASH"):
            check_restitution(before, replace(before, eligible=True, refund_cash=Q(3)), "N2")

    def test_exact_half_and_mixed_currency(self):
        self.assertEqual(add_amount((Q(1, 2), "SYN", "u", 0), (Q(1, 2), "SYN", "u", 0))[0], 1)
        with self.assertRaisesRegex(ValueError, "UNIT_BINDING_MISSING"):
            add_amount((Q(1), "USD", "u", 0), (Q(1), "SYN", "u", 0))


if __name__ == "__main__":
    unittest.main(verbosity=2)
