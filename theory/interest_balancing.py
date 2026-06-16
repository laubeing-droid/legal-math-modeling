"""
Interest Balancing in Legal Decision-Making
=============================================

Mathematical Framework
----------------------
Given a set of stakeholders S = {s_1, ..., s_n}, each with:
  - an interest vector I_j
  - a weight w_j (importance / legal priority)

A legal decision D selects an outcome that maximises weighted
satisfaction:

  D* = argmax_D  Σ_j  w_j × sat(I_j, D)

where sat(I_j, D) ∈ [0, 1] is the satisfaction of stakeholder s_j
under outcome D.

Conflict detection:
  interests conflict iff  ∃ D s.t. sat(I_a, D) > sat(I_a, D')
                          AND sat(I_b, D) < sat(I_b, D')
  for some stakeholders a, b and outcomes D, D'.

Pareto optimality:
  An outcome D is Pareto-optimal iff there is no D' such that
    sat(I_j, D') ≥ sat(I_j, D)  ∀ j
    and  ∃ j  s.t.  sat(I_j, D') > sat(I_j, D)

References:
  - Alexy, "A Theory of Constitutional Rights" (2002)
  - Dworkin, "Taking Rights Seriously" (1977)
  - Calabresi & Melamed, "Property Rules, Liability Rules..." (1972)
"""

from __future__ import annotations

import itertools
from dataclasses import dataclass, field
from typing import FrozenSet


# ---------------------------------------------------------------------------
# Data structures
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Interest:
    """A stakeholder's interest in a specific dimension."""
    label: str
    protected_by: str = ""  # e.g. "statute", "common law", "constitution"

    def __hash__(self) -> int:
        return hash(self.label)

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, Interest):
            return NotImplemented
        return self.label == other.label


@dataclass(frozen=True)
class Stakeholder:
    """A party with weighted interests."""
    name: str
    interests: FrozenSet[Interest]
    weight: float  # 0..1; relative importance / legal priority


@dataclass(frozen=True)
class Outcome:
    """A possible legal outcome / decision."""
    name: str
    # satisfaction[stakeholder_name][interest_label] = value in [0, 1]
    satisfaction: FrozenSet[tuple[str, str, float]]  # (stakeholder, interest, value)

    def get_satisfaction(self, stakeholder: str, interest: str) -> float:
        for s, i, v in self.satisfaction:
            if s == stakeholder and i == interest:
                return v
        return 0.0


@dataclass(frozen=True)
class Conflict:
    stakeholder_a: str
    stakeholder_b: str
    interest_a: str
    interest_b: str
    description: str


@dataclass(frozen=True)
class BalanceResult:
    best_outcome: str
    weighted_score: float
    scores: dict[str, float]  # outcome_name -> weighted score
    is_pareto_optimal: bool
    conflicts: tuple[Conflict, ...]


# ---------------------------------------------------------------------------
# Algorithms
# ---------------------------------------------------------------------------

def weighted_satisfaction(
    outcome: Outcome,
    stakeholders: list[Stakeholder],
) -> float:
    """
    Weighted satisfaction score:

      score = Σ_j  w_j × (1/|I_j|) × Σ_{i∈I_j} sat(s_j, i, D)
    """
    total = 0.0
    for sh in stakeholders:
        sh_interests = list(sh.interests)
        if not sh_interests:
            continue
        avg_sat = sum(
            outcome.get_satisfaction(sh.name, interest.label)
            for interest in sh_interests
        ) / len(sh_interests)
        total += sh.weight * avg_sat
    return total


def detect_conflicts(
    outcomes: list[Outcome],
    stakeholders: list[Stakeholder],
) -> list[Conflict]:
    """
    Detect pairwise stakeholder conflicts across outcomes.
    A conflict exists between a and b when some outcome benefits a
    at b's expense.
    """
    conflicts: list[Conflict] = []
    for a, b in itertools.combinations(stakeholders, 2):
        for interest_a in a.interests:
            for interest_b in b.interests:
                max_a = max(
                    (o.get_satisfaction(a.name, interest_a.label) for o in outcomes),
                    default=0.0,
                )
                max_b = max(
                    (o.get_satisfaction(b.name, interest_b.label) for o in outcomes),
                    default=0.0,
                )
                # If both can be highly satisfied, no conflict on these interests
                # We look for cases where satisfying a harms b
                for o in outcomes:
                    sa = o.get_satisfaction(a.name, interest_a.label)
                    sb = o.get_satisfaction(b.name, interest_b.label)
                    # Check both directions: a high + b low, OR b high + a low
                    if (sa > 0.7 and sb < 0.3) or (sb > 0.7 and sa < 0.3):
                        conflicts.append(Conflict(
                            stakeholder_a=a.name,
                            stakeholder_b=b.name,
                            interest_a=interest_a.label,
                            interest_b=interest_b.label,
                            description=(
                                f"Outcome '{o.name}': {a.name}.{interest_a.label}="
                                f"{sa:.2f} vs {b.name}.{interest_b.label}={sb:.2f}"
                            ),
                        ))
                        break  # one conflict per interest pair is enough
    return conflicts


def is_pareto_optimal(
    candidate: Outcome,
    all_outcomes: list[Outcome],
    stakeholders: list[Stakeholder],
) -> bool:
    """Check if candidate is Pareto-optimal among all_outcomes."""
    for other in all_outcomes:
        if other.name == candidate.name:
            continue
        # Check: other weakly dominates candidate?
        weakly_dominates = True
        strictly_better = False
        for sh in stakeholders:
            for interest in sh.interests:
                s_cand = candidate.get_satisfaction(sh.name, interest.label)
                s_other = other.get_satisfaction(sh.name, interest.label)
                if s_other < s_cand:
                    weakly_dominates = False
                    break
                if s_other > s_cand:
                    strictly_better = True
            if not weakly_dominates:
                break
        if weakly_dominates and strictly_better:
            return False
    return True


def balance(
    stakeholders: list[Stakeholder],
    outcomes: list[Outcome],
) -> BalanceResult:
    """
    Find the outcome that maximises weighted satisfaction across
    all stakeholders, and check Pareto optimality.
    """
    scores: dict[str, float] = {}
    for o in outcomes:
        scores[o.name] = weighted_satisfaction(o, stakeholders)

    best_name = max(scores, key=lambda k: scores[k])
    best_outcome = next(o for o in outcomes if o.name == best_name)
    pareto = is_pareto_optimal(best_outcome, outcomes, stakeholders)
    conflicts = detect_conflicts(outcomes, stakeholders)

    return BalanceResult(
        best_outcome=best_name,
        weighted_score=scores[best_name],
        scores=scores,
        is_pareto_optimal=pareto,
        conflicts=tuple(conflicts),
    )


# ---------------------------------------------------------------------------
# Demo
# ---------------------------------------------------------------------------

def _demo() -> None:
    print("=" * 65)
    print("Interest Balancing Module -- Demo")
    print("=" * 65)
    print("\nScenario: Tort case -- construction site injury")
    print("  Plaintiff (worker) vs Defendant (contractor) vs Public interest")

    # Stakeholders
    worker = Stakeholder(
        name="Worker",
        interests=frozenset({
            Interest("medical_compensation", protected_by="statute"),
            Interest("lost_wages", protected_by="statute"),
            Interest("deterrence", protected_by="common_law"),
        }),
        weight=0.45,
    )
    contractor = Stakeholder(
        name="Contractor",
        interests=frozenset({
            Interest("financial_viability", protected_by="common_law"),
            Interest("freedom_to_operate", protected_by="statute"),
        }),
        weight=0.30,
    )
    public = Stakeholder(
        name="Public",
        interests=frozenset({
            Interest("safety_standards", protected_by="statute"),
            Interest("economic_activity", protected_by="policy"),
        }),
        weight=0.25,
    )

    stakeholders = [worker, contractor, public]

    # Outcomes
    full_compensation = Outcome(
        name="Full Compensation + Punitive Damages",
        satisfaction=frozenset({
            ("Worker", "medical_compensation", 1.0),
            ("Worker", "lost_wages", 1.0),
            ("Worker", "deterrence", 0.9),
            ("Contractor", "financial_viability", 0.1),
            ("Contractor", "freedom_to_operate", 0.3),
            ("Public", "safety_standards", 0.9),
            ("Public", "economic_activity", 0.2),
        }),
    )

    partial_compensation = Outcome(
        name="Partial Compensation (compensatory only)",
        satisfaction=frozenset({
            ("Worker", "medical_compensation", 0.8),
            ("Worker", "lost_wages", 0.6),
            ("Worker", "deterrence", 0.5),
            ("Contractor", "financial_viability", 0.6),
            ("Contractor", "freedom_to_operate", 0.6),
            ("Public", "safety_standards", 0.7),
            ("Public", "economic_activity", 0.6),
        }),
    )

    no_liability = Outcome(
        name="No Liability (assumption of risk)",
        satisfaction=frozenset({
            ("Worker", "medical_compensation", 0.0),
            ("Worker", "lost_wages", 0.0),
            ("Worker", "deterrence", 0.1),
            ("Contractor", "financial_viability", 1.0),
            ("Contractor", "freedom_to_operate", 1.0),
            ("Public", "safety_standards", 0.1),
            ("Public", "economic_activity", 0.9),
        }),
    )

    structured_settlement = Outcome(
        name="Structured Settlement + Safety Order",
        satisfaction=frozenset({
            ("Worker", "medical_compensation", 0.9),
            ("Worker", "lost_wages", 0.7),
            ("Worker", "deterrence", 0.6),
            ("Contractor", "financial_viability", 0.5),
            ("Contractor", "freedom_to_operate", 0.5),
            ("Public", "safety_standards", 0.85),
            ("Public", "economic_activity", 0.5),
        }),
    )

    outcomes = [full_compensation, partial_compensation, no_liability, structured_settlement]

    result = balance(stakeholders, outcomes)

    print("\n--- Weighted Satisfaction Scores ---")
    for name, score in sorted(result.scores.items(), key=lambda x: -x[1]):
        marker = " <-- SELECTED" if name == result.best_outcome else ""
        print(f"  {name:<45s}  score={score:.3f}{marker}")

    print(f"\n--- Result ---")
    print(f"  Best outcome:     {result.best_outcome}")
    print(f"  Weighted score:   {result.weighted_score:.3f}")
    print(f"  Pareto optimal:   {result.is_pareto_optimal}")

    if result.conflicts:
        print(f"\n--- Detected Conflicts ({len(result.conflicts)}) ---")
        for c in result.conflicts:
            print(f"  {c.stakeholder_a} vs {c.stakeholder_b}: "
                  f"interests={c.interest_a}/{c.interest_b}")
            print(f"    {c.description}")
    else:
        print("\n  No pairwise conflicts detected.")

    print("\n--- Pareto Optimality Check (all outcomes) ---")
    for o in outcomes:
        po = is_pareto_optimal(o, outcomes, stakeholders)
        print(f"  {o.name:<45s}  Pareto-optimal={po}")

    print("\n" + "=" * 65)
    print("Demo completed successfully.")


if __name__ == "__main__":
    _demo()
