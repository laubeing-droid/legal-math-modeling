"""
Analogical Reasoning in Legal Case Analysis
============================================

Mathematical Framework
----------------------
A legal case C is represented as a triple C = (F, I, O) where:
  - F = {f_1, f_2, ..., f_n} is the set of material facts
  - I = {i_1, i_2, ..., i_m} is the set of legal issues
  - O is the outcome (holding)

Similarity between two cases C_a and C_b:

  sim(C_a, C_b) = w_f * |F_a ∩ F_b| / |F_a ∪ F_b|
                + w_i * |I_a ∩ I_b| / |I_a ∪ I_b|

where w_f + w_i = 1.

Analogy Strength:

  strength(C_a → C_b) = sim(C_a, C_b) × relevance(C_b) × authority(C_b)

Distinguishing: find the critical fact f* ∈ (F_a △ F_b) that maximally
alters the legal outcome prediction.

References:
  - Sunstein, "On Analogical Reasoning" (1993)
  - Brewer, "Exemplary Reasoning" (1996)
"""

from __future__ import annotations

import itertools
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import FrozenSet


# ---------------------------------------------------------------------------
# Core data structures
# ---------------------------------------------------------------------------

class LegalDomain(Enum):
    CONTRACT = auto()
    TORT = auto()
    PROPERTY = auto()
    CRIMINAL = auto()
    CONSTITUTIONAL = auto()


@dataclass(frozen=True)
class LegalFact:
    """A material fact in a case, represented as a semantic label."""
    label: str
    domain: LegalDomain
    materiality: float = 1.0  # 0.0 .. 1.0

    def __hash__(self) -> int:
        return hash((self.label, self.domain))

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, LegalFact):
            return NotImplemented
        return self.label == other.label and self.domain == other.domain


@dataclass(frozen=True)
class LegalIssue:
    """A legal issue / question of law."""
    label: str

    def __hash__(self) -> int:
        return hash(self.label)

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, LegalIssue):
            return NotImplemented
        return self.label == other.label


@dataclass(frozen=True)
class Case:
    """Represents a legal case C = (F, I, O)."""
    name: str
    facts: FrozenSet[LegalFact]
    issues: FrozenSet[LegalIssue]
    outcome: str
    court_level: int = 1        # 1 = trial, 2 = appellate, 3 = supreme
    year: int = 2020
    jurisdiction: str = "default"

    @property
    def fact_labels(self) -> set[str]:
        return {f.label for f in self.facts}

    @property
    def issue_labels(self) -> set[str]:
        return {i.label for i in self.issues}


# ---------------------------------------------------------------------------
# Similarity and analogy calculations
# ---------------------------------------------------------------------------

def jaccard(a: set, b: set) -> float:
    """Jaccard similarity coefficient: |A ∩ B| / |A ∪ B|."""
    if not a and not b:
        return 1.0
    union = a | b
    if not union:
        return 1.0
    return len(a & b) / len(union)


def similarity(
    c1: Case,
    c2: Case,
    weight_facts: float = 0.6,
    weight_issues: float = 0.4,
) -> float:
    """
    Weighted Jaccard similarity over facts and legal issues.

    sim(C_a, C_b) = w_f * J(F_a, F_b) + w_i * J(I_a, I_b)
    """
    assert abs(weight_facts + weight_issues - 1.0) < 1e-9
    fact_sim = jaccard(c1.fact_labels, c2.fact_labels)
    issue_sim = jaccard(c1.issue_labels, c2.issue_labels)
    return weight_facts * fact_sim + weight_issues * issue_sim


def analogy_strength(
    source: Case,
    target: Case,
    relevance: float = 1.0,
    weight_facts: float = 0.6,
    weight_issues: float = 0.4,
) -> float:
    """
    strength(source → target) = sim(source, target) × relevance × authority

    authority = court_level / max_court_level  (normalised to [0, 1])
    """
    sim = similarity(source, target, weight_facts, weight_issues)
    max_level = max(source.court_level, target.court_level, 1)
    authority = target.court_level / max_level
    return sim * relevance * authority


def find_distinguishing_facts(c1: Case, c2: Case) -> list[str]:
    """
    Return the symmetric difference of facts, i.e. facts present in one
    case but not the other -- candidates for distinguishing.
    """
    return sorted(c1.fact_labels.symmetric_difference(c2.fact_labels))


def best_analogy(
    query: Case,
    candidates: list[Case],
    relevance: dict[str, float] | None = None,
) -> tuple[Case, float]:
    """Return the candidate with the highest analogy strength."""
    rel = relevance or {}
    best_case, best_score = None, -1.0
    for cand in candidates:
        r = rel.get(cand.name, 1.0)
        s = analogy_strength(query, cand, relevance=r)
        if s > best_score:
            best_case, best_score = cand, s
    assert best_case is not None
    return best_case, best_score


# ---------------------------------------------------------------------------
# Demo
# ---------------------------------------------------------------------------

def _demo() -> None:
    print("=" * 65)
    print("Analogical Reasoning Module -- Demo")
    print("=" * 65)

    def fact(label: str, mat: float = 1.0) -> LegalFact:
        return LegalFact(label, LegalDomain.CONTRACT, mat)

    def issue(label: str) -> LegalIssue:
        return LegalIssue(label)

    smith_jones = Case(
        name="Smith v. Jones (2019)",
        facts=frozenset({
            fact("written_agreement"),
            fact("breach_of_delivery"),
            fact("commercial_context"),
            fact("notice_given"),
        }),
        issues=frozenset({
            issue("breach_of_contract"),
            issue("damages_quantum"),
        }),
        outcome="Plaintiff awarded damages",
        court_level=2,
        year=2019,
    )

    acme_widget = Case(
        name="Acme Corp v. Widget Ltd (2021)",
        facts=frozenset({
            fact("written_agreement"),
            fact("breach_of_delivery"),
            fact("commercial_context"),
            fact("mitigation_attempted"),
        }),
        issues=frozenset({
            issue("breach_of_contract"),
            issue("mitigation_duty"),
        }),
        outcome="Plaintiff awarded reduced damages for failure to mitigate",
        court_level=2,
        year=2021,
    )

    green_valley = Case(
        name="Green v. Valley Farms (2022)",
        facts=frozenset({
            fact("oral_agreement"),
            fact("breach_of_delivery"),
            fact("agricultural_context"),
            fact("force_majeure_claim"),
        }),
        issues=frozenset({
            issue("breach_of_contract"),
            issue("force_majeure"),
        }),
        outcome="Defence of force majeure upheld; no damages",
        court_level=1,
        year=2022,
    )

    query = Case(
        name="New Dispute: Alpha v. Beta (2024)",
        facts=frozenset({
            fact("written_agreement"),
            fact("breach_of_delivery"),
            fact("commercial_context"),
        }),
        issues=frozenset({
            issue("breach_of_contract"),
            issue("damages_quantum"),
        }),
        outcome="?",
        court_level=1,
        year=2024,
    )

    candidates = [smith_jones, acme_widget, green_valley]

    print("\n--- Pairwise Similarities ---")
    for c1, c2 in itertools.combinations(candidates, 2):
        s = similarity(c1, c2)
        print(f"  sim({c1.name}, {c2.name}) = {s:.4f}")

    print(f"\n--- Query Case: {query.name} ---")
    for cand in candidates:
        s = analogy_strength(query, cand)
        print(f"  strength({query.name} -> {cand.name}) = {s:.4f}")

    best, score = best_analogy(query, candidates)
    print(f"\n  Best analogy: {best.name}  (strength = {score:.4f})")

    print("\n--- Distinguishing Facts ---")
    for cand in candidates:
        diffs = find_distinguishing_facts(query, cand)
        print(f"  {query.name} vs {cand.name}: {diffs}")

    print("\n" + "=" * 65)
    print("Demo completed successfully.")


if __name__ == "__main__":
    _demo()
