"""Exact finite reference for ULM-NEXT.

All examples are mathematical fixtures, not calibrated legal predictions.
This module deliberately has no API that converts a probability into an
admitted legal fact. It is not a replacement for JC's admission or solvers.
"""
from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from fractions import Fraction
from itertools import product
from types import MappingProxyType
from typing import Callable, Hashable, Iterable, Mapping, Sequence

Q = Fraction
ZERO, ONE = Q(0), Q(1)


class ModelError(ValueError):
    pass


class IncompatibleEvidence(ModelError):
    """Zero evidence mass: no posterior under this model, not legal falsity."""


def rational(value: int | str | Fraction) -> Fraction:
    if isinstance(value, bool) or isinstance(value, float):
        raise ModelError("Use integers or exact decimal/fraction strings, not bool/float")
    if not isinstance(value, (int, str, Fraction)):
        raise ModelError("Unsupported rational input")
    try:
        return Q(value)
    except (ValueError, ZeroDivisionError) as exc:
        raise ModelError("Invalid rational input") from exc


def probability(value: int | str | Fraction) -> Fraction:
    result = rational(value)
    if not ZERO <= result <= ONE:
        raise ModelError("Probability outside [0,1]")
    return result


@dataclass(frozen=True)
class PMF:
    mass: Mapping[Hashable, Fraction]

    def __post_init__(self) -> None:
        values = {key: probability(value) for key, value in self.mass.items()}
        if not values or sum(values.values(), ZERO) != ONE:
            raise ModelError("PMF must be nonempty and sum exactly to one")
        object.__setattr__(self, "mass", MappingProxyType(values))

    def expectation(self, values: Mapping[Hashable, Fraction]) -> Fraction:
        if set(values) != set(self.mass):
            raise ModelError("Expectation domain mismatch")
        return sum((weight * rational(values[key]) for key, weight in self.mass.items()), ZERO)


def normalize(weights: Mapping[Hashable, Fraction]) -> tuple[PMF, Fraction]:
    values = {key: rational(value) for key, value in weights.items()}
    if not values or any(value < 0 for value in values.values()):
        raise ModelError("Weights must be nonempty and nonnegative")
    total = sum(values.values(), ZERO)
    if total == 0:
        raise IncompatibleEvidence("MODEL_EVIDENCE_INCOMPATIBLE: zero evidence mass")
    return PMF({key: value / total for key, value in values.items()}), total


def condition(prior: PMF, likelihood: Mapping[Hashable, Fraction]) -> tuple[PMF, Fraction]:
    if set(prior.mass) != set(likelihood):
        raise ModelError("Likelihood domain mismatch")
    likelihood = {key: probability(value) for key, value in likelihood.items()}
    return normalize({key: p * likelihood[key] for key, p in prior.mass.items()})


@dataclass(frozen=True)
class Node:
    name: str
    states: tuple[str, ...]
    parents: tuple[str, ...]
    cpt: Mapping[tuple[str, ...], tuple[Fraction, ...]]

    def __post_init__(self) -> None:
        if not self.name or not self.states or len(set(self.states)) != len(self.states):
            raise ModelError("Node name/states must be nonempty and unique")
        if len(set(self.parents)) != len(self.parents) or self.name in self.parents:
            raise ModelError("Duplicate/self parent")
        rows = {tuple(key): tuple(probability(x) for x in row) for key, row in self.cpt.items()}
        for row in rows.values():
            if len(row) != len(self.states) or sum(row, ZERO) != ONE:
                raise ModelError("CPT rows must match states and sum to one")
        object.__setattr__(self, "cpt", MappingProxyType(rows))


@dataclass(frozen=True)
class Observation:
    observation_id: str
    variable: str
    value: str


@dataclass(frozen=True)
class QueryResult:
    distribution: PMF
    evidence_mass: Fraction
    model_id: str


class BayesNet:
    """Finite DAG supplied in topological order with complete explicit CPTs."""
    def __init__(self, model_id: str, nodes: Sequence[Node]) -> None:
        if not model_id or not nodes:
            raise ModelError("Model id/nodes required")
        self.model_id = model_id
        self.nodes = tuple(nodes)
        self.domains: dict[str, tuple[str, ...]] = {}
        for node in self.nodes:
            if node.name in self.domains:
                raise ModelError("Duplicate variable")
            if any(parent not in self.domains for parent in node.parents):
                raise ModelError("Parents must precede children; missing parent/cycle/order error")
            expected = set(product(*(self.domains[p] for p in node.parents)))
            if set(node.cpt) != expected:
                raise ModelError("Missing or extraneous CPT row")
            self.domains[node.name] = node.states

    def observations(self, observations: Iterable[Observation]) -> dict[str, str]:
        by_id: dict[str, tuple[str, str]] = {}
        by_variable: dict[str, str] = {}
        for obs in observations:
            if not obs.observation_id:
                raise ModelError("Observation identity required")
            content = (obs.variable, obs.value)
            if obs.observation_id in by_id and by_id[obs.observation_id] != content:
                raise ModelError("Same observation identity, contradictory content")
            if obs.variable not in self.domains or obs.value not in self.domains[obs.variable]:
                raise ModelError("Unknown observation variable/state")
            if obs.variable in by_variable and by_variable[obs.variable] != obs.value:
                raise ModelError("Conflicting hard observations")
            by_id[obs.observation_id] = content
            by_variable[obs.variable] = obs.value
        return by_variable

    def joint(self, assignment: Mapping[str, str]) -> Fraction:
        if set(assignment) != set(self.domains):
            raise ModelError("Assignment is not complete")
        result = ONE
        for node in self.nodes:
            try:
                key = tuple(assignment[parent] for parent in node.parents)
                index = node.states.index(assignment[node.name])
                result *= node.cpt[key][index]
            except (ValueError, KeyError) as exc:
                raise ModelError("Invalid assignment") from exc
        return result

    def enumerate_query(self, query: str, observations: Iterable[Observation] = ()) -> QueryResult:
        if query not in self.domains:
            raise ModelError("Unknown query")
        evidence = self.observations(observations)
        names = tuple(self.domains)
        weights = {state: ZERO for state in self.domains[query]}
        for values in product(*(self.domains[name] for name in names)):
            assignment = dict(zip(names, values))
            if all(assignment[name] == value for name, value in evidence.items()):
                weights[assignment[query]] += self.joint(assignment)
        distribution, mass = normalize(weights)
        return QueryResult(distribution, mass, self.model_id)

    def eliminate_query(self, query: str, observations: Iterable[Observation] = ()) -> QueryResult:
        """Independent factor implementation, not a call to the enumeration oracle."""
        if query not in self.domains:
            raise ModelError("Unknown query")
        evidence = self.observations(observations)
        factors: list[Factor] = []
        for node in self.nodes:
            scope = node.parents + (node.name,)
            table = {key + (state,): row[index] for key, row in node.cpt.items()
                     for index, state in enumerate(node.states)}
            factors.append(Factor(scope, table).restrict(evidence))
        for variable in self.domains:
            if variable == query or variable in evidence:
                continue
            related = [factor for factor in factors if variable in factor.scope]
            factors = [factor for factor in factors if variable not in factor.scope]
            if related:
                merged = Factor.multiply(related, self.domains)
                factors.append(merged.sum_out(variable, self.domains))
        final = Factor.multiply(factors, self.domains)
        if query in evidence:
            mass = sum(final.table.values(), ZERO)
            if mass <= 0:
                raise IncompatibleEvidence("MODEL_EVIDENCE_INCOMPATIBLE")
            distribution = PMF({state: ONE if state == evidence[query] else ZERO
                                for state in self.domains[query]})
        else:
            if final.scope != (query,):
                raise ModelError("Unexpected factor scope")
            distribution, mass = normalize({state: final.table[(state,)]
                                            for state in self.domains[query]})
        return QueryResult(distribution, mass, self.model_id)


@dataclass(frozen=True)
class Factor:
    scope: tuple[str, ...]
    table: Mapping[tuple[str, ...], Fraction]

    def restrict(self, evidence: Mapping[str, str]) -> "Factor":
        keep = tuple(i for i, name in enumerate(self.scope) if name not in evidence)
        scope = tuple(self.scope[i] for i in keep)
        table = {}
        for key, value in self.table.items():
            if all(key[i] == evidence[name] for i, name in enumerate(self.scope) if name in evidence):
                table[tuple(key[i] for i in keep)] = value
        return Factor(scope, table)

    @staticmethod
    def multiply(factors: Sequence["Factor"], domains: Mapping[str, tuple[str, ...]]) -> "Factor":
        scope = tuple(name for name in domains if any(name in factor.scope for factor in factors))
        table: dict[tuple[str, ...], Fraction] = {}
        for key in product(*(domains[name] for name in scope)):
            assignment = dict(zip(scope, key))
            weight = ONE
            for factor in factors:
                weight *= factor.table[tuple(assignment[name] for name in factor.scope)]
            table[key] = weight
        return Factor(scope, table)

    def sum_out(self, variable: str, domains: Mapping[str, tuple[str, ...]]) -> "Factor":
        if variable not in self.scope:
            raise ModelError("Variable outside factor")
        scope = tuple(name for name in self.scope if name != variable)
        table = {}
        for key in product(*(domains[name] for name in scope)):
            assignment = dict(zip(scope, key))
            total = ZERO
            for state in domains[variable]:
                assignment[variable] = state
                total += self.table[tuple(assignment[name] for name in self.scope)]
            table[key] = total
        return Factor(scope, table)


def dirichlet_predictive(alpha: Sequence[Fraction], counts: Sequence[int]) -> tuple[Fraction, ...]:
    alpha = tuple(rational(x) for x in alpha)
    if not alpha or len(alpha) != len(counts) or any(x <= 0 for x in alpha):
        raise ModelError("Positive prior row required")
    if any(type(n) is not int or n < 0 for n in counts):
        raise ModelError("Counts must be nonnegative integers")
    updated = tuple(a + n for a, n in zip(alpha, counts))
    return tuple(value / sum(updated, ZERO) for value in updated)


def rising(a: Fraction, n: int) -> Fraction:
    if type(n) is not int or n < 0:
        raise ModelError("Invalid count")
    result = ONE
    for k in range(n):
        result *= a + k
    return result


def fit_strength_grid(mu: Sequence[Fraction], counts_by_group: Sequence[Sequence[int]],
                      strength_prior: PMF) -> PMF:
    """Exact posterior of a shared finite Dirichlet concentration hyperparameter."""
    mu = tuple(probability(x) for x in mu)
    if not mu or sum(mu, ZERO) != ONE or any(x <= 0 for x in mu):
        raise ModelError("Positive normalized base probabilities required")
    weights = {}
    for raw_strength, prior_weight in strength_prior.mass.items():
        strength = rational(raw_strength)
        if strength <= 0:
            raise ModelError("Concentration must be positive")
        weight = prior_weight
        for counts in counts_by_group:
            dirichlet_predictive(tuple(strength * p for p in mu), counts)
            numerator = ONE
            for p, n in zip(mu, counts):
                numerator *= rising(strength * p, n)
            weight *= numerator / rising(strength, sum(counts))
        weights[strength] = weight
    return normalize(weights)[0]


def mixture_query(results: Mapping[str, QueryResult], model_prior: PMF) -> QueryResult:
    if set(results) != set(model_prior.mass):
        raise ModelError("Model set mismatch")
    states = set(next(iter(results.values())).distribution.mass)
    if any(set(r.distribution.mass) != states or r.evidence_mass <= 0 for r in results.values()):
        raise ModelError("Mixture requires common target states and defined component posteriors")
    # Zero-likelihood components can be represented as zero unnormalized mass
    # in an extended implementation; they must not be assigned a fake posterior.
    mass = sum((model_prior.mass[k] * r.evidence_mass for k, r in results.items()), ZERO)
    if mass == 0:
        raise IncompatibleEvidence("Zero mixture evidence mass")
    values = {state: sum((model_prior.mass[k] * r.evidence_mass * r.distribution.mass[state]
                         for k, r in results.items()), ZERO) / mass for state in states}
    return QueryResult(PMF(values), mass, "conditioned-model-mixture")


def scenario_event_bounds(worlds: PMF, outcomes: Mapping[Hashable, frozenset[Hashable]],
                          event: Callable[[Hashable], bool]) -> tuple[Fraction, Fraction]:
    if set(worlds.mass) != set(outcomes):
        raise ModelError("Scenario domain mismatch")
    lower, upper = ZERO, ZERO
    for world, p in worlds.mass.items():
        if not outcomes[world]:
            raise ModelError("Empty family must be typed as no-extension/incomplete, not quantified vacuously")
        lower += p * int(all(event(y) for y in outcomes[world]))
        upper += p * int(any(event(y) for y in outcomes[world]))
    return lower, upper


def unfinished_posterior_bounds(a: Fraction, b: Fraction, remaining: Fraction) -> tuple[Fraction, Fraction]:
    a, b, remaining = map(rational, (a, b, remaining))
    if min(a, b, remaining) < 0 or a + b + remaining > 1:
        raise ModelError("Invalid subprobability masses")
    total_bound = a + b + remaining
    if total_bound == 0:
        raise IncompatibleEvidence("Zero maximum evidence mass")
    # This numerical envelope is conditional on the full evidence mass being positive.
    return a / total_bound, (a + remaining) / total_bound


class Establishment(str, Enum):
    ESTABLISHED = "established"
    NOT_ESTABLISHED = "notEstablished"
    UNDETERMINED = "undetermined"


@dataclass(frozen=True)
class Assessment:
    request_id: str
    state: Establishment
    review_complete: bool
    basis_ref: str

    def __post_init__(self) -> None:
        if not self.request_id or not self.basis_ref or not isinstance(self.state, Establishment):
            raise ModelError("Explicit assessment identity/state/basis required")
        if type(self.review_complete) is not bool:
            raise ModelError("review_complete must be boolean")


def burden_result(assessment: Assessment, *, stage_closed: bool, authority_valid: bool) -> str:
    if not (stage_closed and authority_valid and assessment.review_complete):
        return "pending"
    return "satisfied" if assessment.state is Establishment.ESTABLISHED else "burden_failure"


def payment_claim(*, request_id: str, relation: Assessment, maturity: Assessment,
                  payment: Assessment, stage_closed: bool, authority_valid: bool,
                  other_defence_applies: bool | None, value: Fraction,
                  established_payment_amount: Fraction) -> dict[str, object]:
    """A scoped ordinary payment-claim fixture; not all Chinese contract law."""
    assessments = (relation, maturity, payment)
    if any(a.request_id != request_id for a in assessments):
        raise ModelError("Cross-request assessment mixing")
    value, paid = rational(value), rational(established_payment_amount)
    if value < 0 or paid < 0:
        raise ModelError("Nonnegative amounts required")
    if not (stage_closed and authority_valid and all(a.review_complete for a in assessments)):
        return {"kind": "pending", "principal": None, "overpayment": None}
    if other_defence_applies is None:
        return {"kind": "pending", "principal": None, "overpayment": None}
    if relation.state is not Establishment.ESTABLISHED or maturity.state is not Establishment.ESTABLISHED:
        return {"kind": "claim_basis_not_established", "principal": ZERO, "overpayment": ZERO}
    if other_defence_applies:
        return {"kind": "other_defence_applies", "principal": None, "overpayment": None}
    recognised_paid = paid if payment.state is Establishment.ESTABLISHED else ZERO
    residual = value - recognised_paid
    return {"kind": "scoped_payment_result", "principal": max(ZERO, residual),
            "overpayment": max(ZERO, -residual)}


@dataclass(frozen=True)
class Interval:
    lo: Fraction
    hi: Fraction

    def __post_init__(self) -> None:
        object.__setattr__(self, "lo", rational(self.lo))
        object.__setattr__(self, "hi", rational(self.hi))
        if self.lo > self.hi:
            raise ModelError("Empty interval: preserve explicit no-feasible-result status")

    def add(self, other: "Interval") -> "Interval":
        return Interval(self.lo + other.lo, self.hi + other.hi)

    def subtract(self, other: "Interval") -> "Interval":
        return Interval(self.lo - other.hi, self.hi - other.lo)

    def scale(self, factor: Fraction) -> "Interval":
        endpoints = (self.lo * rational(factor), self.hi * rational(factor))
        return Interval(min(endpoints), max(endpoints))

    def multiply(self, other: "Interval") -> "Interval":
        endpoints = [a * b for a in (self.lo, self.hi) for b in (other.lo, other.hi)]
        return Interval(min(endpoints), max(endpoints))

    def divide(self, other: "Interval") -> "Interval":
        if other.lo <= 0 <= other.hi:
            raise ModelError("Denominator interval contains zero")
        return self.multiply(Interval(ONE / other.hi, ONE / other.lo))


def exact_grid_range(candidates: Mapping[str, Fraction], allowed: Callable[[str], bool]) -> dict[str, object]:
    feasible = {key: rational(value) for key, value in candidates.items() if allowed(key)}
    if not feasible:
        return {"kind": "no_feasible_grid_point", "values": (), "interval": None}
    lo, hi = min(feasible.values()), max(feasible.values())
    return {"kind": "exact_over_declared_grid", "values": tuple(sorted(set(feasible.values()))),
            "interval": Interval(lo, hi),
            "lo_witnesses": tuple(k for k, v in feasible.items() if v == lo),
            "hi_witnesses": tuple(k for k, v in feasible.items() if v == hi)}


def dot(a: Sequence[Fraction], b: Sequence[Fraction]) -> Fraction:
    if len(a) != len(b):
        raise ModelError("Dimension mismatch")
    return sum((rational(x) * rational(y) for x, y in zip(a, b)), ZERO)


def verify_lp_optimum(A: Sequence[Sequence[Fraction]], b: Sequence[Fraction], c: Sequence[Fraction],
                      x: Sequence[Fraction], dual: Sequence[Fraction]) -> tuple[str, ...]:
    if len(A) != len(b) or len(dual) != len(b) or len(x) != len(c) or any(len(row) != len(c) for row in A):
        raise ModelError("LP dimensions mismatch")
    A = tuple(tuple(rational(v) for v in row) for row in A)
    b, c, x, dual = (tuple(rational(v) for v in vec) for vec in (b, c, x, dual))
    errors = []
    if any(v < 0 for v in x) or any(dot(row, x) > rhs for row, rhs in zip(A, b)):
        errors.append("PRIMAL_INFEASIBLE")
    if any(v < 0 for v in dual) or any(sum((dual[i] * A[i][j] for i in range(len(A))), ZERO) < c[j]
                                      for j in range(len(c))):
        errors.append("DUAL_INFEASIBLE")
    if dot(c, x) != dot(b, dual):
        errors.append("OBJECTIVE_GAP")
    return tuple(errors)


def information_value(joint: PMF, utilities: Mapping[str, Mapping[Hashable, Fraction]],
                      cost: Fraction = ZERO) -> dict[str, Fraction]:
    if not utilities:
        raise ModelError("Nonempty action set required")
    if any(not isinstance(key, tuple) or len(key) != 2 for key in joint.mass):
        raise ModelError("Expected joint domain (outcome,signal)")
    ys = {key[0] for key in joint.mass}
    signals = {key[1] for key in joint.mass}
    if any(set(row) != ys for row in utilities.values()):
        raise ModelError("Utility domain mismatch")
    before = max(sum((p * rational(row[y]) for (y, z), p in joint.mass.items()), ZERO)
                 for row in utilities.values())
    after = sum((max(sum((p * rational(row[y]) for (y, zz), p in joint.mass.items() if zz == z), ZERO)
                     for row in utilities.values()) for z in signals), ZERO)
    cost = rational(cost)
    if cost < 0:
        raise ModelError("Cost must be nonnegative")
    return {"before": before, "after": after, "gross_voi": after - before,
            "net_voi": after - before - cost}


def settlement_bounds(mp: Fraction, md: Fraction, cp: Fraction, cd: Fraction,
                      sp: Fraction = ZERO, sd: Fraction = ZERO) -> dict[str, object]:
    mp, md, cp, cd, sp, sd = map(rational, (mp, md, cp, cd, sp, sd))
    if min(cp, cd, sp, sd) < 0:
        raise ModelError("Costs must be nonnegative")
    lo, hi = mp - cp + sp, md + cd - sd
    return {"lo": lo, "hi": hi, "feasible": lo <= hi,
            "interval": Interval(lo, hi) if lo <= hi else None}


def nash_bargain(interval: Interval, weight: Fraction) -> Fraction:
    weight = probability(weight)
    return interval.lo + weight * (interval.hi - interval.lo)


def incentive_gap(gain: Fraction, detection: Fraction, sanction: Fraction) -> Fraction:
    gain, sanction = rational(gain), rational(sanction)
    if gain < 0 or sanction < 0:
        raise ModelError("Gain and sanction must be nonnegative")
    return probability(detection) * sanction - gain


def nash_regrets(payoff1: Sequence[Sequence[Fraction]], payoff2: Sequence[Sequence[Fraction]],
                 strategy1: Sequence[Fraction], strategy2: Sequence[Fraction]) -> tuple[Fraction, Fraction]:
    p = PMF(dict(enumerate(strategy1)))
    q = PMF(dict(enumerate(strategy2)))
    rows, cols = len(strategy1), len(strategy2)
    if any(len(mat) != rows or any(len(row) != cols for row in mat) for mat in (payoff1, payoff2)):
        raise ModelError("Payoff dimensions mismatch")
    u1 = sum((p.mass[i] * q.mass[j] * rational(payoff1[i][j]) for i in range(rows) for j in range(cols)), ZERO)
    u2 = sum((p.mass[i] * q.mass[j] * rational(payoff2[i][j]) for i in range(rows) for j in range(cols)), ZERO)
    best1 = max(sum((q.mass[j] * rational(payoff1[i][j]) for j in range(cols)), ZERO) for i in range(rows))
    best2 = max(sum((p.mass[i] * rational(payoff2[i][j]) for i in range(rows)), ZERO) for j in range(cols))
    return best1 - u1, best2 - u2


def verify_mechanism(*, types1: Sequence[str], types2: Sequence[str], outcomes: Sequence[str],
                     prior: PMF, allocation: Mapping[tuple[str, str], PMF],
                     utility1: Callable[[str, str, str], Fraction],
                     utility2: Callable[[str, str, str], Fraction],
                     outside1: Mapping[str, Fraction], outside2: Mapping[str, Fraction],
                     legal_outcomes: frozenset[str], net_transfer: Mapping[str, Fraction]) -> dict[str, object]:
    """Exact BIC, interim IR and per-realized-outcome budget-balance checker.

    Net transfer is the sum of transfers to all parties in this closed model.
    Zero means balance, and does not assert allocation efficiency.
    """
    if not types1 or not types2 or not outcomes or any(len(set(x)) != len(x) for x in (types1, types2, outcomes)):
        raise ModelError("Nonempty unique types/outcomes required")
    pairs = set(product(types1, types2))
    if set(prior.mass) != pairs or set(allocation) != pairs:
        raise ModelError("Type profile domain mismatch")
    if set(outside1) != set(types1) or set(outside2) != set(types2) or set(net_transfer) != set(outcomes):
        raise ModelError("Outside option/transfer domain mismatch")
    if any(set(p.mass) != set(outcomes) for p in allocation.values()):
        raise ModelError("Allocation outcome domain mismatch")
    violations: list[dict[str, object]] = []
    uncovered = []

    def eu(report1: str, report2: str, true1: str, true2: str, utility: Callable) -> Fraction:
        return sum((p * rational(utility(o, true1, true2))
                    for o, p in allocation[(report1, report2)].mass.items()), ZERO)

    for a in types1:
        margin = sum((prior.mass[(a, b)] for b in types2), ZERO)
        if margin == 0:
            uncovered.append((1, a))
            continue
        truth = sum((prior.mass[(a, b)] * eu(a, b, a, b, utility1) for b in types2), ZERO)
        for report in types1:
            dev = sum((prior.mass[(a, b)] * eu(report, b, a, b, utility1) for b in types2), ZERO)
            if dev > truth:
                violations.append({"code": "BIC_1", "type": a, "report": report, "gain": (dev-truth)/margin})
        if truth < margin * rational(outside1[a]):
            violations.append({"code": "IR_1", "type": a})
    for b in types2:
        margin = sum((prior.mass[(a, b)] for a in types1), ZERO)
        if margin == 0:
            uncovered.append((2, b))
            continue
        truth = sum((prior.mass[(a, b)] * eu(a, b, a, b, utility2) for a in types1), ZERO)
        for report in types2:
            dev = sum((prior.mass[(a, b)] * eu(a, report, a, b, utility2) for a in types1), ZERO)
            if dev > truth:
                violations.append({"code": "BIC_2", "type": b, "report": report, "gain": (dev-truth)/margin})
        if truth < margin * rational(outside2[b]):
            violations.append({"code": "IR_2", "type": b})
    for profile, dist in allocation.items():
        for outcome, mass in dist.mass.items():
            if mass > 0 and outcome not in legal_outcomes:
                violations.append({"code": "ILLEGAL_OUTCOME", "profile": profile, "outcome": outcome})
            if mass > 0 and rational(net_transfer[outcome]) != 0:
                violations.append({"code": "NOT_EX_POST_BALANCED", "profile": profile, "outcome": outcome})
    return {"accepted_on_declared_scope": not violations, "violations": tuple(violations),
            "zero_prior_types_without_bic_guarantee": tuple(uncovered)}


def expected_brier(true_probability: Fraction, prediction: Fraction) -> Fraction:
    p, q = probability(true_probability), probability(prediction)
    return p * (ONE - q) ** 2 + (ONE - p) * q ** 2
