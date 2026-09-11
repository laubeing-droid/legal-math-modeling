"""Exact finite references for the VNext construction specification.

All demonstration probabilities are synthetic assumptions. This file is not
connected to JC and makes no empirical calibration or Lean-proof claim.
Python >= 3.11; standard library only. No floating-point inputs are accepted.
"""
from __future__ import annotations

import argparse
import itertools
import json
from dataclasses import dataclass
from fractions import Fraction as Q
from pathlib import Path
from types import MappingProxyType
from typing import Callable, Hashable, Mapping, Sequence, TypeVar

T = TypeVar("T", bound=Hashable)


def exact(value: Q | int) -> Q:
    if type(value) not in (Q, int):
        raise TypeError("Use Fraction or int; no floats or booleans")
    return Q(value)


def probability(value: Q | int) -> Q:
    value = exact(value)
    if not 0 <= value <= 1:
        raise ValueError("Probability outside [0, 1]")
    return value


def distribution(values: Mapping[T, Q | int]) -> dict[T, Q]:
    result = {key: probability(value) for key, value in values.items()}
    if not result or sum(result.values(), Q(0)) != 1:
        raise ValueError("A distribution must be nonempty and sum exactly to 1")
    return result


@dataclass(frozen=True)
class SearchResult:
    found: frozenset
    rejected: frozenset
    pending: frozenset
    complete: bool


def scan(universe: Sequence[T], predicate: Callable[[T], bool | None],
         budget: int | None = None) -> SearchResult:
    """Classify a finite carrier. None stays pending, never rejected.

    predicate must decide the FULL candidate semantics, not prefix maximality.
    A budget counts attempted candidate checks, not wall-clock time.
    """
    if len(set(universe)) != len(universe):
        raise ValueError("Duplicate carrier entries")
    if budget is None:
        budget = len(universe)
    if type(budget) is not int or budget < 0:
        raise ValueError("budget must be a nonnegative integer")
    accepted, rejected, pending = set(), set(), set(universe)
    for candidate in universe[:budget]:
        decision = predicate(candidate)
        if decision is None:
            continue
        if type(decision) is not bool:
            raise TypeError("A member checker returns bool or None")
        pending.remove(candidate)
        (accepted if decision else rejected).add(candidate)
    return SearchResult(frozenset(accepted), frozenset(rejected),
                        frozenset(pending), not pending)


def verify_partition(universe: Sequence[T], result: SearchResult,
                     independent_semantics: Callable[[T], bool]) -> bool:
    """Finite, deliberately expensive reference verification.

    Production must supply an independent semantic predicate/verified checker;
    supplying the same buggy solver predicate is not independent verification.
    """
    if len(set(universe)) != len(universe):
        return False
    a, j, pending = result.found, result.rejected, result.pending
    if a & j or a & pending or j & pending or a | j | pending != set(universe):
        return False
    if result.complete != (not pending):
        return False
    return (all(independent_semantics(x) is True for x in a)
            and all(independent_semantics(x) is False for x in j))


def powerset(items: Sequence[T]) -> tuple[frozenset[T], ...]:
    if len(set(items)) != len(items):
        raise ValueError("Duplicate elements")
    return tuple(frozenset(c) for r in range(len(items) + 1)
                 for c in itertools.combinations(items, r))


def dung_member(profile: str, arguments: tuple[str, ...],
                edges: frozenset[tuple[str, str]], subset: frozenset[str]) -> bool:
    """Mathematical member oracle, including global preferred maximality."""
    carrier = frozenset(arguments)
    if len(carrier) != len(arguments) or any(a not in carrier or b not in carrier
                                            for a, b in edges):
        raise ValueError("Invalid argument graph")
    if profile not in {"grounded", "stable", "preferred", "complete"}:
        raise ValueError("Unknown profile")
    if not subset <= carrier:
        return False

    def cf(s):
        return not any(a in s and b in s for a, b in edges)

    def defended(s, a):
        return all(any((c, b) in edges for c in s)
                   for b in carrier if (b, a) in edges)

    def admissible(s):
        return cf(s) and all(defended(s, a) for a in s)

    if profile == "stable":
        return cf(subset) and all(any((b, a) in edges for b in subset)
                                  for a in carrier - subset)
    if profile == "preferred":
        return admissible(subset) and not any(
            subset < other and admissible(other) for other in powerset(arguments))
    if profile == "complete":
        return admissible(subset) and subset == frozenset(
            a for a in carrier if defended(subset, a))
    current = frozenset()
    for _ in range(len(arguments) + 1):
        nxt = frozenset(a for a in carrier if defended(current, a))
        if nxt == current:
            return subset == current
        current = nxt
    raise AssertionError("Finite grounded iteration invariant was violated")


@dataclass(frozen=True)
class BinaryNode:
    name: str
    parents: tuple[str, ...]
    p_true: Mapping[tuple[bool, ...], Q]

    def __post_init__(self):
        if not self.name or len(set(self.parents)) != len(self.parents):
            raise ValueError("Node/parent identity invalid")
        rows = {tuple(row): probability(p) for row, p in self.p_true.items()}
        if (any(type(x) is not bool for row in rows for x in row)
                or set(rows) != set(itertools.product((False, True), repeat=len(self.parents)))):
            raise ValueError("CPT rows must exactly cover the parent domain")
        object.__setattr__(self, "p_true", MappingProxyType(rows))


@dataclass(frozen=True)
class Factor:
    scope: tuple[str, ...]
    table: Mapping[tuple[bool, ...], Q]

    def restrict(self, evidence: Mapping[str, bool]) -> Factor:
        indices = tuple(i for i, name in enumerate(self.scope) if name not in evidence)
        table = {}
        for assignment, value in self.table.items():
            if all(assignment[i] == evidence[name]
                   for i, name in enumerate(self.scope) if name in evidence):
                table[tuple(assignment[i] for i in indices)] = value
        return Factor(tuple(self.scope[i] for i in indices), table)

    def multiply(self, other: Factor) -> Factor:
        scope = tuple(dict.fromkeys(self.scope + other.scope))
        left = tuple(scope.index(x) for x in self.scope)
        right = tuple(scope.index(x) for x in other.scope)
        table = {}
        for assignment in itertools.product((False, True), repeat=len(scope)):
            a = tuple(assignment[i] for i in left)
            b = tuple(assignment[i] for i in right)
            table[assignment] = self.table[a] * other.table[b]
        return Factor(scope, table)

    def sum_out(self, variable: str) -> Factor:
        if variable not in self.scope:
            return self
        index = self.scope.index(variable)
        table = {}
        for assignment, value in self.table.items():
            reduced = assignment[:index] + assignment[index + 1:]
            table[reduced] = table.get(reduced, Q(0)) + value
        return Factor(self.scope[:index] + self.scope[index + 1:], table)


@dataclass(frozen=True)
class BinaryBN:
    nodes: tuple[BinaryNode, ...]

    def __post_init__(self):
        seen = set()
        for node in self.nodes:
            if node.name in seen or not set(node.parents) <= seen:
                raise ValueError("Provide unique nodes in topological order")
            seen.add(node.name)

    def _validate_event(self, event: Mapping[str, bool]):
        if not set(event) <= {n.name for n in self.nodes}:
            raise ValueError("Unknown variable in event")
        if any(type(x) is not bool for x in event.values()):
            raise TypeError("Binary event values must be bool")

    def joint(self) -> dict[tuple[bool, ...], Q]:
        result = {}
        for values in itertools.product((False, True), repeat=len(self.nodes)):
            assignment = dict(zip((n.name for n in self.nodes), values))
            mass = Q(1)
            for node in self.nodes:
                p = node.p_true[tuple(assignment[x] for x in node.parents)]
                mass *= p if assignment[node.name] else 1 - p
            result[values] = mass
        return result

    def mass_by_enumeration(self, event: Mapping[str, bool]) -> Q:
        self._validate_event(event)
        names = tuple(n.name for n in self.nodes)
        return sum((p for row, p in self.joint().items()
                    if all(row[names.index(k)] == v for k, v in event.items())), Q(0))

    def mass_by_elimination(self, event: Mapping[str, bool]) -> Q:
        self._validate_event(event)
        factors = []
        for node in self.nodes:
            table = {}
            for row, p in node.p_true.items():
                table[row + (False,)] = 1 - p
                table[row + (True,)] = p
            factors.append(Factor(node.parents + (node.name,), table).restrict(event))
        for name in reversed([n.name for n in self.nodes if n.name not in event]):
            selected = [f for f in factors if name in f.scope]
            factors = [f for f in factors if name not in f.scope]
            if selected:
                product = selected[0]
                for factor in selected[1:]:
                    product = product.multiply(factor)
                factors.append(product.sum_out(name))
        result = Factor((), {(): Q(1)})
        for factor in factors:
            result = result.multiply(factor)
        if result.scope:
            raise AssertionError("Not all variables were eliminated")
        return result.table[()]

    def posterior(self, event: Mapping[str, bool], evidence: Mapping[str, bool],
                  *, elimination: bool = False) -> Q:
        self._validate_event(event)
        self._validate_event(evidence)
        mass = self.mass_by_elimination if elimination else self.mass_by_enumeration
        z = mass(evidence)
        if z == 0:
            raise ValueError("Evidence has zero probability under this model")
        if any(k in evidence and evidence[k] != v for k, v in event.items()):
            return Q(0)
        return mass({**evidence, **event}) / z


def dirichlet_predictive(alpha: Sequence[Q | int], counts: Sequence[int]) -> tuple[Q, ...]:
    if not alpha or len(alpha) != len(counts):
        raise ValueError("Empty or mismatching CPT row")
    priors = tuple(exact(x) for x in alpha)
    if any(x <= 0 for x in priors) or any(type(n) is not int or n < 0 for n in counts):
        raise ValueError("Positive prior concentrations and nonnegative counts required")
    values = tuple(a + n for a, n in zip(priors, counts))
    return tuple(x / sum(values) for x in values)


def model_envelope(models: Sequence[BinaryBN], event: Mapping[str, bool],
                   evidence: Mapping[str, bool]) -> tuple[Q, Q]:
    if not models:
        raise ValueError("No registered models")
    # A zero-evidence model raises, rather than being silently dropped.
    values = [model.posterior(event, evidence) for model in models]
    return min(values), max(values)


def partial_posterior_bounds(a: Q | int, b: Q | int, r: Q | int) -> tuple[Q, Q]:
    a, b, r = exact(a), exact(b), exact(r)
    if min(a, b, r) < 0:
        raise ValueError("Negative mass")
    if a + b == 0:
        raise ValueError("No witnessed positive evidence mass; conditional event unresolved")
    return a / (a + b + r), (a + r) / (a + b + r)


def expected_outcome_bounds(weights: Mapping[T, Q | int],
                            outcomes: Mapping[T, Sequence[Q | int]]) -> tuple[Q, Q]:
    probabilities = distribution(weights)
    low = high = Q(0)
    for scenario, mass in probabilities.items():
        if not mass:
            continue
        values = tuple(exact(x) for x in outcomes.get(scenario, ()))
        if not values:
            raise ValueError("A positive-mass scenario has no defined outcome")
        low += mass * min(values)
        high += mass * max(values)
    return low, high


def exact_simple_interest(periods: Sequence[tuple[Q | int, Q | int, Q | int]]) -> Q:
    """Inputs: principal, annual rate, year fraction; legal basis is external."""
    total = Q(0)
    for principal, rate, year_fraction in periods:
        p, r, t = exact(principal), exact(rate), exact(year_fraction)
        if min(p, r, t) < 0:
            raise ValueError("This example's declared domain is nonnegative")
        total += p * r * t
    return total


def settlement_point(a: Q | int, b: Q | int, weight: Q | int) -> Q:
    a, b, weight = exact(a), exact(b), probability(weight)
    if a > b:
        raise ValueError("No individually rational amount interval in this model")
    return (1 - weight) * a + weight * b


def bic_regret(types: tuple[tuple[str, ...], ...], outcomes: tuple[str, ...],
               prior: Mapping[tuple[str, ...], Q | int],
               mechanism: Mapping[tuple[str, ...], Mapping[str, Q | int]],
               utility: Mapping[tuple[int, str, str], Q | int]) -> Q:
    """Exact BIC regret on a fully supplied finite type/utility model.

    Does not check legality, collusion, identity manipulation, or real utility.
    Zero-marginal own types are rejected as undefined rather than guessed.
    """
    if not types or any(not row or len(set(row)) != len(row) for row in types):
        raise ValueError("Finite nonempty unique type domains required")
    if not outcomes or len(set(outcomes)) != len(outcomes):
        raise ValueError("Invalid outcome domain")
    profiles = tuple(itertools.product(*types))
    if set(prior) != set(profiles) or set(mechanism) != set(profiles):
        raise ValueError("Incomplete type/report coverage")
    mu = distribution(prior)
    mechanisms = {}
    for reports, row in mechanism.items():
        if set(row) != set(outcomes):
            raise ValueError("Incomplete outcome distribution")
        mechanisms[reports] = distribution(row)
    regret = Q(0)
    for player, domain in enumerate(types):
        for actual in domain:
            conditioned = [p for p in profiles if p[player] == actual]
            normalizer = sum((mu[p] for p in conditioned), Q(0))
            if not normalizer:
                raise ValueError("A type has zero marginal probability")
            for reported in domain:
                deviation = Q(0)
                for true_profile in conditioned:
                    reports = list(true_profile)
                    reports[player] = reported
                    reports = tuple(reports)
                    for outcome in outcomes:
                        u = exact(utility[player, actual, outcome])
                        deviation += mu[true_profile] / normalizer * u * (
                            mechanisms[reports][outcome] - mechanisms[true_profile][outcome])
                regret = max(regret, deviation)
    return regret


def evsi(joint: Mapping[tuple[str, str], Q | int],
         utilities: Mapping[str, Mapping[str, Q | int]], cost: Q | int = 0) -> Q:
    """Finite observational information value with an unchanged action set."""
    weights = distribution(joint)
    if not utilities:
        raise ValueError("No available actions")
    actions = {a: {y: exact(v) for y, v in row.items()}
               for a, row in utilities.items()}
    targets = {y for _, y in weights}
    if any(not targets <= set(row) for row in actions.values()):
        raise ValueError("Missing utility entries")
    before = max(sum((p * row[y] for (_, y), p in weights.items()), Q(0))
                 for row in actions.values())
    after = sum((max(sum((p * row[y] for (signal, y), p in weights.items()
                         if signal == z), Q(0)) for row in actions.values())
                 for z in {z for z, _ in weights}), Q(0))
    return after - before - exact(cost)


def brier(probabilities: Sequence[Q | int], labels: Sequence[int]) -> Q:
    if not probabilities or len(probabilities) != len(labels):
        raise ValueError("Empty or mismatching evaluation data")
    if any(type(y) is not int or y not in (0, 1) for y in labels):
        raise ValueError("Binary observed labels required")
    return sum(((probability(p) - y) ** 2 for p, y in zip(probabilities, labels)), Q(0)) / len(labels)


def demo() -> dict:
    model = BinaryBN((
        BinaryNode("A", (), {(): Q(3, 5)}),
        BinaryNode("E", ("A",), {(False,): Q(1, 5), (True,): Q(4, 5)}),
    ))
    posterior = model.posterior({"A": True}, {"E": True})
    expectation = Q(300000) + 200000 * posterior - Q(100000, 4)
    return {
        "status": "SYNTHETIC_MATHEMATICAL_REFERENCE",
        "lean_status": "CI_NOT_RUN",
        "jc_integration": "NOT_PERFORMED",
        "empirical_status": "NOT_EVALUATED",
        "posterior_A": str(posterior),
        "posterior_A_elimination": str(model.posterior({"A": True}, {"E": True}, elimination=True)),
        "scenario_amounts_yuan": [200000, 300000, 400000, 500000],
        "expected_amount_yuan": str(expectation),
        "warning": "The expectation is not an amount legally ordered by a court.",
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    text = json.dumps(demo(), ensure_ascii=False, indent=2) + "\n"
    if args.output:
        args.output.write_text(text, encoding="utf-8")
    print(text, end="")
