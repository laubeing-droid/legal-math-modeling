"""WP-5 tests: quantity AST, real formulas, FM projection, waterfall,
cash accounts, band pricing, interest segments, Opt construction."""

from fractions import Fraction as Q
from unittest import TestCase

import pytest

from unified.quantities import (
    Allocation,
    DomainError,
    InterestSegment,
    Poly,
    QBin,
    QConst,
    QPiecewise,
    QRound,
    RAnd,
    RAtom,
    RExists,
    RFormula,
    RNot,
    ROr,
    allocate_payment,
    band_price,
    band_widths,
    cash_accounts,
    denote,
    eval_quantity,
    earlier_groups_fully_paid,
    fm_eliminate,
    free_vars,
    opt_formula,
    rename_var,
    schedule_interest,
)


def _lin(variables, coeffs, rel, const=Q(0)):
    """Linear atom Σ coeffs·v ⋈ const (const is the RIGHT-hand side)."""

    vs = tuple(variables)
    terms = tuple(
        (tuple(1 if v == w else 0 for w in vs), c)
        for v, c in zip(vs, coeffs) if c
    )
    if const:
        terms = terms + ((tuple(0 for _ in vs), -const),)
    return RAtom(Poly(vs, terms) if terms or vs else Poly((), ()), rel)


class QuantityAstTests(TestCase):
    def test_exact_arithmetic(self):
        expr = QBin("mul", QBin("sub", QConst(Q(1, 3)), QConst(Q(1, 6))), QConst(Q(4)))
        self.assertEqual(eval_quantity(expr, {}), Q(2, 3))

    def test_division_by_zero_is_domain_error(self):
        expr = QBin("div", QConst(Q(1)), QConst(Q(0)))
        with pytest.raises(DomainError):
            eval_quantity(expr, {})

    def test_free_variable_from_env(self):
        expr = QBin("add", "x", QConst(Q(1)))
        self.assertEqual(eval_quantity(expr, {"x": Q(2)}), Q(3))
        with pytest.raises(DomainError):
            eval_quantity(expr, {})

    def test_round_node_exact(self):
        expr = QRound(QBin("div", QConst(Q(3)), QConst(Q(2))), "HALF_UP")
        self.assertEqual(eval_quantity(expr, {}), Q(2))

    def test_piecewise_first_matching_branch(self):
        positive = RNot(_lin(("x",), (Q(1),), "<="))  # x > 0
        expr = QPiecewise(
            ((positive, QConst(Q(10))),), default=QConst(Q(0))
        )
        self.assertEqual(eval_quantity(expr, {"x": Q(5)}), Q(10))
        self.assertEqual(eval_quantity(expr, {"x": Q(-1)}), Q(0))

    def test_piecewise_no_branch_is_domain_error(self):
        positive = RNot(_lin(("x",), (Q(1),), "<="))  # x > 0
        with pytest.raises(DomainError):
            eval_quantity(QPiecewise(((positive, QConst(Q(1))),)), {"x": Q(0)})

    def test_float_rejected(self):
        with pytest.raises(TypeError):
            QConst(0.5)  # type: ignore[arg-type]


class RealFormulaTests(TestCase):
    def test_denote_exact(self):
        # x² ≤ 2 has no rational witness at x=3/2: 9/4 > 2.
        poly = Poly(("x",), (((2,), Q(1)), ((0,), Q(-2))))
        atom = RAtom(poly, "<=")
        self.assertFalse(denote(atom, {"x": Q(3, 2)}))
        self.assertTrue(denote(atom, {"x": Q(7, 5)}))

    def test_boolean_structure(self):
        f = RAnd((_lin(("x",), (Q(1),), "<=", const=Q(5)),
                  RNot(_lin(("x",), (Q(1),), "<", const=Q(2)))))
        self.assertTrue(denote(f, {"x": Q(3)}))
        self.assertTrue(denote(f, {"x": Q(2)}))    # ¬(2<2) holds
        self.assertFalse(denote(f, {"x": Q(1)}))   # 1<2 defeats the negation
        self.assertFalse(denote(f, {"x": Q(6)}))

    def test_quantifier_denotation_refused(self):
        with pytest.raises(DomainError):
            denote(RExists("x", _lin(("x",), (Q(1),), "<", const=Q(1))), {})

    def test_free_vars(self):
        f = RExists("x", _lin(("x", "y"), (Q(1), Q(1)), "<=", const=Q(3)))
        self.assertEqual(free_vars(f), frozenset({"y"}))


class FMProjectionTests(TestCase):
    def test_redundant_bounds_project_to_true(self):
        f = RAnd((_lin(("x",), (Q(1),), "<=", const=Q(5)),
                  _lin(("x",), (Q(-1),), "<=", const=Q(-2))))
        out = fm_eliminate(f, "x")
        # 5 − 2 ≥ 0 holds; result is the empty conjunction (TRUE)
        self.assertEqual(out.parts, ())

    def test_contradictory_bounds_project_to_false(self):
        f = RAnd((_lin(("x",), (Q(1),), "<=", const=Q(1)),
                  _lin(("x",), (Q(-1),), "<=", const=Q(-5))))  # x ≥ 5
        out = fm_eliminate(f, "x")
        # 1 − 5 ≥ 0 fails: a FALSE atom is present
        self.assertEqual(len(out.parts), 1)

    def test_projection_carries_parameter(self):
        # x ≤ y ∧ x ≥ 0, eliminate x  ⟺  y ≥ 0
        f = RAnd((_lin(("x", "y"), (Q(1), Q(-1)), "<="),
                  _lin(("x",), (Q(-1),), "<=")))
        out = fm_eliminate(f, "x")
        self.assertEqual(len(out.parts), 1)
        # y ≥ 0 must be the surviving atom
        self.assertTrue(denote(out.parts[0], {"y": Q(1)}))
        self.assertFalse(denote(out.parts[0], {"y": Q(-1)}))

    def test_equality_substitution(self):
        # x = y + 1 ∧ x ≤ 3, eliminate x ⟺ y ≤ 2
        f = RAnd((_lin(("x", "y"), (Q(1), Q(-1)), "=", const=Q(1)),
                  _lin(("x",), (Q(1),), "<=", const=Q(3))))
        out = fm_eliminate(f, "x")
        self.assertEqual(len(out.parts), 1)
        self.assertTrue(denote(out.parts[0], {"y": Q(2)}))
        self.assertFalse(denote(out.parts[0], {"y": Q(5, 2)}))

    def test_strictness_preserved(self):
        # x < 0 ∧ x > 0 eliminate x: U−L = 0 with a strict side ⟺ 0 < 0
        # FALSE — the strictness must survive, not round to non-strict.
        f = RAnd((_lin(("x",), (Q(1),), "<", const=Q(0)),
                  _lin(("x",), (Q(-1),), "<", const=Q(0))))
        out = fm_eliminate(f, "x")
        self.assertEqual(len(out.parts), 1)  # a FALSE atom survives

    def test_nonlinear_refused(self):
        quad = RAtom(Poly(("x",), (((2,), Q(1)), ((0,), Q(-2)))), "<=")
        with pytest.raises(ValueError):
            fm_eliminate(RAnd((quad,)), "x")


class WaterfallTests(TestCase):
    def test_conservation_telescoping(self):
        alloc = allocate_payment(Q(10), ((Q(3), Q(4)), (Q(5),)))
        self.assertEqual(
            alloc.total_allocated() + alloc.remaining, Q(10)
        )

    def test_partial_group_residual(self):
        alloc = allocate_payment(Q(10), ((Q(3), Q(4)), (Q(5),)))
        # group 0 fully paid (3+4=7), group 1 gets 3 of 5
        self.assertEqual(alloc.allocations[0], (Q(3), Q(4)))
        self.assertEqual(alloc.allocations[1], (Q(3),))
        self.assertEqual(alloc.residuals[1], (Q(2),))
        self.assertEqual(alloc.remaining, Q(0))

    def test_t25_counterexample_shape(self):
        # debts (1, 100), assets 101 => allocations (1, 100): the
        # absolute-amount monotonicity is FALSE and our property is the
        # corrected one: later group paid => earlier groups cleared.
        alloc = allocate_payment(Q(101), ((Q(1),), (Q(100),)))
        self.assertEqual(alloc.allocations, ((Q(1),), (Q(100),)))
        self.assertTrue(earlier_groups_fully_paid(alloc, 1))
        # The second group's absolute amount (100) exceeds the first
        # group's (1): the old claim is refuted by this very witness.
        self.assertGreater(
            sum(alloc.allocations[1]), sum(alloc.allocations[0])
        )

    def test_priority_property_when_partial(self):
        # earlier group partially paid => later groups get nothing
        alloc = allocate_payment(Q(2), ((Q(3), Q(4)), (Q(5),)))
        self.assertEqual(alloc.allocations[1], (Q(0),))
        self.assertFalse(earlier_groups_fully_paid(alloc, 1) is False)

    def test_earlier_unpaid_blocks_later(self):
        alloc = allocate_payment(Q(2), ((Q(3),), (Q(5),)))
        # group 1 got 0; property trivially holds
        self.assertTrue(earlier_groups_fully_paid(alloc, 1))

    def test_overpay_remainder_kept(self):
        alloc = allocate_payment(Q(10), ((Q(3),),))
        self.assertEqual(alloc.remaining, Q(7))
        self.assertEqual(alloc.residuals, ((Q(0),),))

    def test_monotonicity_of_later_recovery(self):
        # raising an earlier debt (same assets) never raises later
        # recovery — the monotone direction the plan keeps.
        low = allocate_payment(Q(10), ((Q(2),), (Q(8),), (Q(5),)))
        high = allocate_payment(Q(10), ((Q(4),), (Q(6),), (Q(5),)))
        later_low = low.allocations[2][0]
        later_high = high.allocations[2][0]
        self.assertGreaterEqual(later_low, later_high)


class CashAccountTests(TestCase):
    def test_three_cases(self):
        # b=100 gross=40/100/140 -> C=60/0/0, U=0/0/40 (J.9 civil_amount)
        self.assertEqual(cash_accounts(Q(100), Q(40)), (Q(60), Q(60), Q(0)))
        self.assertEqual(cash_accounts(Q(100), Q(100)), (Q(0), Q(0), Q(0)))
        r, c, u = cash_accounts(Q(100), Q(140))
        self.assertEqual((r, c, u), (Q(-40), Q(0), Q(40)))
        self.assertEqual(c - u, r)


class BandTests(TestCase):
    def test_conservation_within_cover(self):
        widths = band_widths(Q(7), (Q(2), Q(5)))
        self.assertEqual(sum(widths), Q(7))
        self.assertEqual(widths, (Q(2), Q(3), Q(2)))

    def test_below_first_edge(self):
        self.assertEqual(band_widths(Q(1), (Q(2), Q(5))), (Q(1), Q(0), Q(0)))

    def test_price(self):
        # 10% on first 2, 20% on next 3, 30% beyond: x=7 -> 1/5+3/5+3/5=7/5
        price = band_price(Q(7), (Q(2), Q(5)), (Q(1, 10), Q(1, 5), Q(3, 10)))
        self.assertEqual(price, Q(7, 5))

    def test_ascending_edges_enforced(self):
        with pytest.raises(ValueError):
            band_widths(Q(3), (Q(5), Q(2)))


class InterestTests(TestCase):
    def test_segment_exact(self):
        seg = InterestSegment(0, 30, Q(1000), Q(6, 100), 30, 360)
        self.assertEqual(seg.interest(), Q(5))

    def test_schedule_sums_segments(self):
        segs = (
            InterestSegment(0, 30, Q(1000), Q(6, 100), 30, 360),
            InterestSegment(30, 60, Q(500), Q(6, 100), 30, 360),
        )
        self.assertEqual(schedule_interest(segs), Q(5) + Q(5, 2))

    def test_different_conventions_not_blended(self):
        # a 365-denominator segment is its own arithmetic line
        seg = InterestSegment(0, 30, Q(1000), Q(6, 100), 30, 365)
        self.assertEqual(seg.interest(), Q(1000) * Q(6, 100) * Q(30, 365))


class OptFormulaTests(TestCase):
    def test_rename_var(self):
        atom = _lin(("x", "y"), (Q(1), Q(-1)), "<=")
        renamed = rename_var(atom, "x", "z")
        self.assertEqual(free_vars(renamed), frozenset({"z", "y"}))
        self.assertEqual(denote(renamed, {"z": Q(1), "y": Q(2)}),
                         denote(atom, {"x": Q(1), "y": Q(2)}))

    def test_opt_formula_shape(self):
        constraint = RAnd((_lin(("y",), (Q(1),), "<=", const=Q(5)),
                           _lin(("y",), (Q(-1),), "<=")))
        objective = Poly(("y",), (((2,), Q(1)),))
        formula = opt_formula(constraint, objective)
        self.assertIn("y#", str(formula))
        # f(y)−f(z) ≤ 0 at y=0,z=5: −25 ≤ 0 holds
        diff_atom = formula.parts[-1].body.parts[1]
        self.assertTrue(denote(diff_atom, {"y": Q(0), "y#": Q(5)}))
        self.assertFalse(denote(diff_atom, {"y": Q(5), "y#": Q(0)}))
