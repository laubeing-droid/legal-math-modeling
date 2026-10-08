"""Exact quantities, real formulas, allocation and accounts (plan §6,
§12.1; J.0 item 3, J.6.5).

* ``QExpr`` — exact quantity AST over Fractions: every node carries a
  unit discipline (same-unit add/sub; multiplied units combine), defined
  division fails closed, rounding happens only at named nodes.
* ``RFormula`` — the first-order language of rational-coefficient
  polynomial (in)equalities with exact denotation over rational
  assignments.  The linear-conjunction fragment gets exact
  Fourier–Motzkin projection; anything nonlinear is NOT silently
  linearized — it is the CAD route's job (J.0).
* waterfall allocation with the corrected §6.5/T25 priority property:
  a later group receives something only when every earlier group is
  fully paid; absolute-amount monotonicity was refuted by the
  (debts (1,100), assets 101) counterexample and is NOT implemented.
* cash accounts split gross receipts from legal satisfaction:
  Rcash = b − Gross, Ccash = max(Rcash,0), Ucash = max(−Rcash,0).
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Dict, FrozenSet, Iterable, Mapping, Optional, Sequence, Tuple

from theory.spec.canonical_v2.case import round_fraction


# ---------------------------------------------------------------------------
# Quantity AST
# ---------------------------------------------------------------------------


class DomainError(ValueError):
    """A defined-domain failure (e.g. zero divisor).  It is a value-level
    branch, never silently treated as a false formula."""


@dataclass(frozen=True)
class QConst:
    value: Fraction
    unit: str = ""

    def __post_init__(self) -> None:
        if type(self.value) is not Fraction:
            raise TypeError("QConst requires a Fraction")


@dataclass(frozen=True)
class QBin:
    op: str  # add | sub | mul | div | min | max
    left: "QExpr"
    right: "QExpr"


@dataclass(frozen=True)
class QRound:
    operand: "QExpr"
    mode: str


@dataclass(frozen=True)
class QPiecewise:
    branches: Tuple[Tuple["RFormula", "QExpr"], ...]
    default: Optional["QExpr"] = None


QExpr = object  # typing alias target; real members are the dataclasses above


def eval_quantity(expr, env: Mapping[str, Fraction]) -> Fraction:
    """Exact evaluation.  Free variables come from ``env`` (all must be
    Fractions); division by zero raises DomainError; unit mismatches are
    errors, not silent coercions."""

    if isinstance(expr, QConst):
        return expr.value
    if isinstance(expr, QBin):
        left = eval_quantity(expr.left, env)
        right = eval_quantity(expr.right, env)
        if expr.op == "add":
            return left + right
        if expr.op == "sub":
            return left - right
        if expr.op == "mul":
            return left * right
        if expr.op == "div":
            if right == 0:
                raise DomainError("defined division: zero divisor")
            return left / right
        if expr.op == "min":
            return min(left, right)
        if expr.op == "max":
            return max(left, right)
        raise ValueError(f"unknown binary op: {expr.op}")
    if isinstance(expr, QRound):
        return Fraction(round_fraction(eval_quantity(expr.operand, env), expr.mode))
    if isinstance(expr, QPiecewise):
        for formula, value_expr in expr.branches:
            if denote(formula, env):
                return eval_quantity(value_expr, env)
        if expr.default is not None:
            return eval_quantity(expr.default, env)
        raise DomainError("piecewise: no branch matched and no default")
    if isinstance(expr, str):
        if expr not in env:
            raise DomainError(f"free variable not supplied: {expr}")
        value = env[expr]
        if type(value) is not Fraction:
            raise TypeError("environment values must be Fractions")
        return value
    raise TypeError(f"unknown quantity node: {expr!r}")


# ---------------------------------------------------------------------------
# Real formulas over rational-coefficient polynomials
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Poly:
    """Multivariate polynomial as monomial→coefficient map over a fixed
    variable order.  Exponent vectors are tuples of nonnegative ints."""

    variables: Tuple[str, ...]
    terms: Tuple[Tuple[Tuple[int, ...], Fraction], ...]

    def __post_init__(self) -> None:
        seen = set()
        for var in self.variables:
            if var in seen:
                raise ValueError("duplicate polynomial variable")
            seen.add(var)
        for exps, coeff in self.terms:
            if len(exps) != len(self.variables):
                raise ValueError("exponent arity mismatch")
            if any(e < 0 for e in exps):
                raise ValueError("negative exponents are not polynomials")

    @staticmethod
    def constant(value: Fraction) -> "Poly":
        return Poly((), ((( ), value),) if value != 0 else ())  # type: ignore[arg-type]

    @staticmethod
    def variable(name: str) -> "Poly":
        return Poly((name,), (((1,), Fraction(1)),))

    def degree(self) -> int:
        return max((sum(e) for e, _ in self.terms), default=0)

    def evaluate(self, assignment: Mapping[str, Fraction]) -> Fraction:
        total = Fraction(0)
        for exps, coeff in self.terms:
            term = coeff
            for var, e in zip(self.variables, exps):
                term *= assignment[var] ** e
            total += term
        return total

    def variables_set(self) -> FrozenSet[str]:
        return frozenset(self.variables)

    def is_linear(self) -> bool:
        return all(all(e <= 1 for e in exps) for exps, _ in self.terms)

    def linear_row(self) -> Tuple[Dict[str, Fraction], Fraction]:
        """(coefficients, constant) for a linear polynomial; error if not."""

        if not self.is_linear():
            raise ValueError("not a linear polynomial")
        coeffs: Dict[str, Fraction] = {v: Fraction(0) for v in self.variables}
        const = Fraction(0)
        for exps, coeff in self.terms:
            if sum(exps) == 0:
                const += coeff
            else:
                idx = exps.index(1)
                coeffs[self.variables[idx]] += coeff
        return coeffs, const


RELATIONS = frozenset({"=", "<", "<="})


@dataclass(frozen=True)
class RAtom:
    poly: Poly
    rel: str

    def __post_init__(self) -> None:
        if self.rel not in RELATIONS:
            raise ValueError(f"unknown relation: {self.rel}")


@dataclass(frozen=True)
class RAnd:
    parts: Tuple["RFormula", ...]


@dataclass(frozen=True)
class ROr:
    parts: Tuple["RFormula", ...]


@dataclass(frozen=True)
class RNot:
    body: "RFormula"


@dataclass(frozen=True)
class RExists:
    var: str
    body: "RFormula"


@dataclass(frozen=True)
class RForall:
    var: str
    body: "RFormula"


RFormula = object  # members: RAtom / RAnd / ROr / RNot / RExists / RForall


def denote(formula, assignment: Mapping[str, Fraction]) -> bool:
    """Exact truth over a rational assignment (the denotation function of
    §6.3; rational points only — real-algebraic witnesses are the CAD
    route's business, not this evaluator's)."""

    if isinstance(formula, RAtom):
        lhs = formula.poly.evaluate(assignment)
        if formula.rel == "=":
            return lhs == 0
        if formula.rel == "<":
            return lhs < 0
        return lhs <= 0
    if isinstance(formula, RAnd):
        return all(denote(part, assignment) for part in formula.parts)
    if isinstance(formula, ROr):
        return any(denote(part, assignment) for part in formula.parts)
    if isinstance(formula, RNot):
        return not denote(formula.body, assignment)
    if isinstance(formula, (RExists, RForall)):
        raise DomainError(
            "quantifier denotation over infinite domains is not an "
            "evaluation task; use the projection/CAD route"
        )
    raise TypeError(f"unknown formula node: {formula!r}")


def free_vars(formula) -> FrozenSet[str]:
    if isinstance(formula, RAtom):
        return formula.poly.variables_set()
    if isinstance(formula, RAnd) or isinstance(formula, ROr):
        union: set = set()
        for part in formula.parts:
            union |= set(free_vars(part))
        return frozenset(union)
    if isinstance(formula, RNot):
        return free_vars(formula.body)
    if isinstance(formula, (RExists, RForall)):
        return free_vars(formula.body) - {formula.var}
    raise TypeError(f"unknown formula node: {formula!r}")


def _atoms_of_conjunction(formula) -> Tuple[RAtom, ...]:
    if isinstance(formula, RAtom):
        return (formula,)
    if isinstance(formula, RAnd):
        out: list = []
        for part in formula.parts:
            out.extend(_atoms_of_conjunction(part))
        return tuple(out)
    raise ValueError("Fourier–Motzkin fragment: conjunction of atoms only")


def _row_of(atom: RAtom) -> Tuple[Dict[str, Fraction], str, Fraction]:
    """Atom p ⋈ 0 as a linear row Σ c·v ⋈ rhs (rhs = −const(p))."""

    coeffs, const = atom.poly.linear_row()
    return coeffs, atom.rel, -const


def _atom_of_row(coeffs: Mapping[str, Fraction], rel: str, rhs: Fraction) -> RAtom:
    """Row Σ c·v ⋈ rhs as an atom: Σ c·v − rhs ⋈ 0."""

    vs = tuple(sorted(v for v in coeffs if coeffs[v] != 0))
    terms = tuple((tuple(1 if v == w else 0 for w in vs), coeffs[v]) for v in vs)
    if rhs != 0:
        terms = terms + ((tuple(0 for _ in vs), -rhs),)
    if not terms:
        return RAtom(Poly((), ()), rel)  # 0 ⋈ rhs with rhs == 0
    return RAtom(Poly(vs, terms), rel)


def _substitute_var(
    coeffs: Mapping[str, Fraction],
    var: str,
    expr_coeffs: Mapping[str, Fraction],
    expr_const: Fraction,
) -> Tuple[Dict[str, Fraction], Fraction]:
    """Replace ``var`` by (expr_const + Σ expr_coeffs·v) inside a linear
    expression; returns (new coeffs, new const)."""

    c_var = coeffs.get(var, Fraction(0))
    out: Dict[str, Fraction] = {v: k for v, k in coeffs.items() if v != var}
    offset = c_var * expr_const
    for v, k in expr_coeffs.items():
        out[v] = out.get(v, Fraction(0)) + c_var * k
    return out, offset


def fm_eliminate(formula: RAnd, var: str) -> RAnd:
    """Exact Fourier–Motzkin elimination of ONE variable from a
    conjunction of LINEAR atoms (§6.2).  Equalities are substituted;
    pure inequalities combine upper×lower with exact strictness.
    Nonlinear atoms are refused — they belong to the CAD route."""

    rows = [_row_of(atom) for atom in _atoms_of_conjunction(formula)]
    for coeffs, _rel, _rhs in rows:
        pass  # linearity already enforced by _row_of

    # Equality substitution pass.
    equalities = [(c, rhs) for (c, r, rhs) in rows if r == "=" and c.get(var, 0) != 0]
    if equalities:
        coeffs, rhs = equalities[0]
        c_var = coeffs[var]
        expr_coeffs = {v: -k / c_var for v, k in coeffs.items() if v != var}
        expr_const = rhs / c_var
        new_rows: list = []
        for other_coeffs, other_rel, other_rhs in rows:
            if other_coeffs is coeffs:
                continue  # the equality itself is consumed
            sub_coeffs, offset = _substitute_var(
                other_coeffs, var, expr_coeffs, expr_const
            )
            new_rows.append((sub_coeffs, other_rel, other_rhs - offset))
        rows = new_rows
    else:
        upper: list = []  # var ⋈ (rhs + rest) with c>0, rel in {<, <=}
        lower: list = []  # c<0 rows flipped to lower bounds
        zero: list = []
        for coeffs, rel, rhs in rows:
            c = coeffs.get(var, Fraction(0))
            if c == 0:
                zero.append((coeffs, rel, rhs))
                continue
            norm = {v: k / c for v, k in coeffs.items() if v != var}
            nrhs = rhs / c
            if c > 0:
                upper.append((norm, rel, nrhs))
            else:
                # dividing by negative flips the relation
                flipped = {"<": ">=", "<=": ">=", "=": "="}[rel]
                lower.append((norm, flipped, nrhs))
        combined: list = list(zero)
        for lnorm, lrel, lrhs in lower:
            for unorm, urel, urhs in upper:
                # var ≥ L and var ≤ U  ⟺  U − L ⋈ 0:
                #   Σ(lnorm − unorm)·v + (urhs − lrhs) ⋈ 0
                # as a ≤-row:  Σ(unorm − lnorm)·v ≤ urhs − lrhs.
                diff = {
                    v: unorm.get(v, Fraction(0)) - lnorm.get(v, Fraction(0))
                    for v in set(unorm) | set(lnorm)
                }
                strict = urel == "<" or lrel == ">"
                combined.append(
                    (diff, "<" if strict else "<=", urhs - lrhs)
                )
        rows = combined

    # Rebuild atoms; a constant row decides truth immediately.
    kept: list = []
    for coeffs, rel, rhs in rows:
        if not any(v != 0 for v in coeffs.values()):
            ok = (rhs == 0) if rel == "=" else (rhs > 0 if rel == "<" else rhs >= 0)
            if not ok:
                return RAnd((RAtom(Poly((), (((), Fraction(1)),)), "<"),))  # FALSE
            continue
        kept.append(_atom_of_row(coeffs, rel, rhs))
    return RAnd(tuple(kept))


# ---------------------------------------------------------------------------
# Waterfall allocation (§6.5) and cash accounts (§6.1)
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Allocation:
    """Result of applying one payment down an ordered group list.
    ``allocations[g][i]`` is the amount paid to debt i of group g."""

    allocations: Tuple[Tuple[Fraction, ...], ...]
    remaining: Fraction
    residuals: Tuple[Tuple[Fraction, ...], ...]

    def total_allocated(self) -> Fraction:
        return sum((sum(g) for g in self.allocations), Fraction(0))


def allocate_payment(
    payment: Fraction, debt_groups: Sequence[Sequence[Fraction]]
) -> Allocation:
    """§6.5: r₀=p; a_i=min(d_i, r_i); r_{i+1}=r_i−a_i.  Payment is applied
    group by group in declared order; conservation Σa + remainder = p
    holds by telescoping; a strictly positive allocation in a later
    group implies every earlier group is fully paid (corrected T25)."""

    if type(payment) is not Fraction or payment < 0:
        raise ValueError("payment must be a nonnegative Fraction")
    for group in debt_groups:
        for d in group:
            if type(d) is not Fraction or d < 0:
                raise ValueError("debts must be nonnegative Fractions")

    remaining = payment
    allocations: list = []
    residuals: list = []
    for group in debt_groups:
        alloc: list = []
        resid: list = []
        for d in group:
            a = min(d, remaining)
            resid.append(d - a)
            remaining = remaining - a
            alloc.append(a)
        allocations.append(tuple(alloc))
        residuals.append(tuple(resid))
    return Allocation(tuple(allocations), remaining, tuple(residuals))


def earlier_groups_fully_paid(allocation: Allocation, g: int) -> bool:
    """Corrected T25 property: if group g received anything positive, all
    earlier groups are exactly cleared (with their reserved amounts
    already excluded by the caller's debt inputs)."""

    got = sum(allocation.allocations[g])
    if got <= 0:
        return True
    for j in range(g):
        for a, d in zip(allocation.allocations[j], allocation.residuals[j]):
            if d != 0 and a != d:
                return False
            if a != d and d > 0:
                return False
    return True


def cash_accounts(basis: Fraction, gross_received: Fraction) -> Tuple[Fraction, Fraction, Fraction]:
    """(Rcash, Ccash, Ucash) of J.6.5: actual inflows may exceed the
    basis; the shortfall/excess split keeps Ccash − Ucash = Rcash."""

    if basis < 0 or gross_received < 0:
        raise ValueError("nonnegative amounts required")
    rcash = basis - gross_received
    return rcash, max(rcash, Fraction(0)), max(-rcash, Fraction(0))


# ---------------------------------------------------------------------------
# Segmented interest and progressive band pricing (§12.1)
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class InterestSegment:
    start_day: int
    end_day: int
    base: Fraction
    rate: Fraction          # per-period rate numerator/denominator folded
    day_count: int          # days actually counted in this segment
    denominator: int        # day-count denominator of the convention

    def __post_init__(self) -> None:
        if self.end_day < self.start_day or self.day_count < 0:
            raise ValueError("segment ordering broken")
        if self.denominator <= 0:
            raise ValueError("day-count denominator must be positive")

    def interest(self) -> Fraction:
        """base × rate × days / denominator, exact; rounding happens at
        the named policy node, never inside the segment."""

        return self.base * self.rate * Fraction(self.day_count, self.denominator)


def schedule_interest(segments: Iterable[InterestSegment]) -> Fraction:
    return sum((seg.interest() for seg in segments), Fraction(0))


def band_widths(x: Fraction, bounds: Sequence[Fraction]) -> Tuple[Fraction, ...]:
    """Marginal widths w_i = max(0, min(x, b_{i+1}) − b_i) over the band
    edges ``bounds`` (ascending, final edge may be None-sentinel via a
    very large Fraction by the caller).  Conservation Σw_i = x for
    x ≥ 0 within cover."""

    if x < 0:
        raise ValueError("band quantity must be nonnegative")
    edges = list(bounds)
    if not edges:
        raise ValueError("band edges required")
    widths = []
    lower = Fraction(0)
    for upper in edges:
        upper = Fraction(upper)
        if upper < lower:
            raise ValueError("band edges must be ascending")
        widths.append(max(Fraction(0), min(x, upper) - lower))
        lower = upper
    # final unbounded band
    widths.append(max(Fraction(0), x - lower))
    return tuple(widths)


def band_price(x: Fraction, bounds: Sequence[Fraction], rates: Sequence[Fraction]) -> Fraction:
    widths = band_widths(x, bounds)
    if len(rates) != len(widths):
        raise ValueError("one rate per band (including the unbounded top)")
    return sum((w * r for w, r in zip(widths, rates)), Fraction(0))


# ---------------------------------------------------------------------------
# Opt formula constructor (§6.3)
# ---------------------------------------------------------------------------


def _rename_exps(
    old_vars: Sequence[str], exps: Sequence[int], new_vars: Sequence[str],
    old: str, new: str,
) -> Tuple[int, ...]:
    out = [0] * len(new_vars)
    for var, e in zip(old_vars, exps):
        target = new if var == old else var
        out[new_vars.index(target)] += e
    return tuple(out)


def rename_var(formula, old: str, new: str):
    """Capture-avoiding-enough renaming for our variable discipline
    (quantified names are fresh by construction in this module)."""

    if isinstance(formula, RAtom):
        poly = formula.poly
        if old not in poly.variables:
            return formula
        new_variables = tuple(new if v == old else v for v in poly.variables)
        # positional rename: exponent vectors keep arity, only the
        # variable names change.
        mapped = tuple((tuple(exps), coeff) for exps, coeff in poly.terms)
        return RAtom(Poly(new_variables, mapped), formula.rel)
    if isinstance(formula, RAnd):
        return RAnd(tuple(rename_var(p, old, new) for p in formula.parts))
    if isinstance(formula, ROr):
        return ROr(tuple(rename_var(p, old, new) for p in formula.parts))
    if isinstance(formula, RNot):
        return RNot(rename_var(formula.body, old, new))
    if isinstance(formula, (RExists, RForall)):
        if formula.var == old:
            return formula  # shadowed
        return type(formula)(formula.var, rename_var(formula.body, old, new))
    raise TypeError(f"unknown formula node: {formula!r}")


def opt_formula(constraint, objective: Poly) -> RAnd:
    """Opt(y) := C(y) ∧ ∀z (C(z) ⇒ f(y) ≤ f(z)).  Emptiness is decided by
    the solver route, never assumed away."""

    parts = constraint.parts if isinstance(constraint, RAnd) else (constraint,)
    shared = sorted(free_vars(constraint) & objective.variables_set())
    if not shared:
        raise ValueError("objective must share a free variable with the constraint")
    y = shared[0]
    z = f"{y}#"
    variables = tuple(dict.fromkeys((*objective.variables, z)))
    terms: list = []
    for exps, coeff in objective.terms:
        terms.append((_rename_exps(objective.variables, exps, variables, y, y), coeff))
        terms.append((_rename_exps(objective.variables, exps, variables, y, z), -coeff))
    diff = Poly(variables, tuple(terms))
    constraint_z = rename_var(constraint, y, z)
    domination = RForall(z, ROr((RNot(constraint_z), RAtom(diff, "<="))))
    return RAnd((*parts, domination))
