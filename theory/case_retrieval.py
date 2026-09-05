"""
Case Retrieval and Ranking for Legal Research
==============================================

Mathematical Framework
----------------------
Given a query case Q and a corpus D = {C_1, ..., C_n}, retrieve
the top-k most legally relevant cases.

Legal Relevance Score:

  rel(Q, C) = w1 * issue_overlap(Q, C)
            + w2 * fact_overlap(Q, C)
            + w3 * jurisdiction_match(Q, C)
            + w4 * recency(Q, C)

where:
  - issue_overlap = |I_Q ∩ I_C| / |I_Q|
  - fact_overlap  = |F_Q ∩ F_C| / |F_Q|
  - jurisdiction_match ∈ {0, 1}
  - recency = exp(-λ * (current_year - year(C)))

Top-k retrieval: select the k cases with the highest rel(Q, C).

Re-ranking by legal authority:

  final_score(Q, C) = α * rel(Q, C) + (1 - α) * authority(C)

where authority(C) = court_level(C) / max_court_level.

References:
  - Weber et al., "Conceptual Retrieval and Case Law" (2014)
  - Zhong et al., "Legal Case Retrieval: A Survey" (2020)
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from enum import Enum, auto
from typing import FrozenSet


# ---------------------------------------------------------------------------
# Enums and data structures
# ---------------------------------------------------------------------------

class CourtLevel(Enum):
    TRIAL = 1
    APPELLATE = 2
    SUPREME = 3


@dataclass(frozen=True)
class LegalIssue:
    label: str

    def __hash__(self) -> int:
        return hash(self.label)

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, LegalIssue):
            return NotImplemented
        return self.label == other.label


@dataclass(frozen=True)
class LegalFact:
    label: str

    def __hash__(self) -> int:
        return hash(self.label)

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, LegalFact):
            return NotImplemented
        return self.label == other.label


@dataclass(frozen=True)
class Case:
    name: str
    facts: FrozenSet[LegalFact]
    issues: FrozenSet[LegalIssue]
    jurisdiction: str
    court: CourtLevel
    year: int
    outcome: str = ""

    @property
    def fact_labels(self) -> set[str]:
        return {f.label for f in self.facts}

    @property
    def issue_labels(self) -> set[str]:
        return {i.label for i in self.issues}


@dataclass
class RetrievalResult:
    case_name: str
    relevance_score: float
    authority_score: float
    final_score: float
    rank: int


# ---------------------------------------------------------------------------
# Scoring components
# ---------------------------------------------------------------------------

MAX_COURT_LEVEL = max(l.value for lvl in CourtLevel if (l := lvl))


def issue_overlap(query: Case, candidate: Case) -> float:
    """|I_Q ∩ I_C| / |I_Q|.  Fraction of query issues covered."""
    q_issues = query.issue_labels
    if not q_issues:
        return 0.0
    return len(q_issues & candidate.issue_labels) / len(q_issues)


def fact_overlap(query: Case, candidate: Case) -> float:
    """|F_Q ∩ F_C| / |F_Q|.  Fraction of query facts covered."""
    q_facts = query.fact_labels
    if not q_facts:
        return 0.0
    return len(q_facts & candidate.fact_labels) / len(q_facts)


def jurisdiction_match(query: Case, candidate: Case) -> float:
    """1.0 if same jurisdiction, else 0.0."""
    return 1.0 if query.jurisdiction == candidate.jurisdiction else 0.0


def recency(candidate: Case, current_year: int, decay: float = 0.05) -> float:
    """Exponential decay: exp(-λ * (current_year - year))."""
    return math.exp(-decay * (current_year - candidate.year))


def authority_score(candidate: Case) -> float:
    """Normalised court level."""
    return candidate.court.value / MAX_COURT_LEVEL


def relevance(
    query: Case,
    candidate: Case,
    current_year: int = 2024,
    w1: float = 0.35,
    w2: float = 0.30,
    w3: float = 0.15,
    w4: float = 0.20,
    decay: float = 0.05,
) -> float:
    """Composite legal relevance score."""
    return (
        w1 * issue_overlap(query, candidate)
        + w2 * fact_overlap(query, candidate)
        + w3 * jurisdiction_match(query, candidate)
        + w4 * recency(candidate, current_year, decay)
    )


def retrieve_top_k(
    query: Case,
    corpus: list[Case],
    k: int = 3,
    current_year: int = 2024,
    alpha: float = 0.7,
) -> list[RetrievalResult]:
    """
    Two-stage retrieval:
      1. Score all cases by legal relevance.
      2. Re-rank by: final_score = α * relevance + (1-α) * authority.
    Return top-k results.
    """
    scored: list[RetrievalResult] = []
    for cand in corpus:
        rel = relevance(query, cand, current_year)
        auth = authority_score(cand)
        final = alpha * rel + (1.0 - alpha) * auth
        scored.append(RetrievalResult(
            case_name=cand.name,
            relevance_score=rel,
            authority_score=auth,
            final_score=final,
            rank=0,
        ))

    scored.sort(key=lambda r: r.final_score, reverse=True)
    for i, r in enumerate(scored):
        r.rank = i + 1

    return scored[:k]


# ---------------------------------------------------------------------------
# Demo
# ---------------------------------------------------------------------------

def _demo() -> None:
    print("=" * 65)
    print("Case Retrieval Module -- Demo")
    print("=" * 65)

    def f(label: str) -> LegalFact:
        return LegalFact(label)

    def i(label: str) -> LegalIssue:
        return LegalIssue(label)

    query = Case(
        name="Query: Alpha v. Beta (2024)",
        facts=frozenset({
            f("written_contract"),
            f("breach_of_delivery"),
            f("commercial_context"),
            f("consequential_damages_claim"),
        }),
        issues=frozenset({
            i("breach_of_contract"),
            i("damages_quantum"),
            i("mitigation_duty"),
        }),
        jurisdiction="federal",
        court=CourtLevel.TRIAL,
        year=2024,
    )

    corpus = [
        Case(
            name="Smith v. Jones (2019)",
            facts=frozenset({f("written_contract"), f("breach_of_delivery"),
                             f("commercial_context"), f("notice_given")}),
            issues=frozenset({i("breach_of_contract"), i("damages_quantum")}),
            jurisdiction="federal", court=CourtLevel.APPELLATE, year=2019,
        ),
        Case(
            name="Acme v. Widget (2021)",
            facts=frozenset({f("written_contract"), f("breach_of_delivery"),
                             f("commercial_context"), f("mitigation_attempted")}),
            issues=frozenset({i("breach_of_contract"), i("mitigation_duty")}),
            jurisdiction="federal", court=CourtLevel.SUPREME, year=2021,
        ),
        Case(
            name="Green v. Valley (2022)",
            facts=frozenset({f("oral_agreement"), f("breach_of_delivery"),
                             f("agricultural_context"), f("force_majeure_claim")}),
            issues=frozenset({i("breach_of_contract"), i("force_majeure")}),
            jurisdiction="state", court=CourtLevel.TRIAL, year=2022,
        ),
        Case(
            name="TechCo v. DataInc (2020)",
            facts=frozenset({f("software_licence"), f("service_outage"),
                             f("data_loss"), f("sla_breach")}),
            issues=frozenset({i("breach_of_contract"), i("limitation_of_liability")}),
            jurisdiction="federal", court=CourtLevel.APPELLATE, year=2020,
        ),
        Case(
            name="Lakeside v. MfgCorp (2018)",
            facts=frozenset({f("written_contract"), f("breach_of_delivery"),
                             f("commercial_context"), f("consequential_damages_claim")}),
            issues=frozenset({i("breach_of_contract"), i("damages_quantum"),
                              i("foreseeability")}),
            jurisdiction="federal", court=CourtLevel.SUPREME, year=2018,
        ),
        Case(
            name="Baker v. Thornton (2023)",
            facts=frozenset({f("employment_agreement"), f("wrongful_termination"),
                             f("whistleblower_retaliation")}),
            issues=frozenset({i("wrongful_termination"), i("retaliation_claim")}),
            jurisdiction="state", court=CourtLevel.APPELLATE, year=2023,
        ),
        Case(
            name="Rivera v. SupplyChain (2022)",
            facts=frozenset({f("written_contract"), f("breach_of_delivery"),
                             f("international_trade"), f("consequential_damages_claim")}),
            issues=frozenset({i("breach_of_contract"), i("damages_quantum"),
                              i("choice_of_law")}),
            jurisdiction="federal", court=CourtLevel.APPELLATE, year=2022,
        ),
        Case(
            name="Estate of Fox v. Insurer (2019)",
            facts=frozenset({f("insurance_policy"), f("claim_denial"),
                             f("bad_faith"), f("coverage_dispute")}),
            issues=frozenset({i("insurance_coverage"), i("bad_faith")}),
            jurisdiction="state", court=CourtLevel.SUPREME, year=2019,
        ),
        Case(
            name="Metro v. Contractor (2021)",
            facts=frozenset({f("written_contract"), f("breach_of_delivery"),
                             f("construction_context"), f("payment_dispute")}),
            issues=frozenset({i("breach_of_contract"), i("quantum_meruit")}),
            jurisdiction="federal", court=CourtLevel.TRIAL, year=2021,
        ),
        Case(
            name="NorthStar v. Innovate (2023)",
            facts=frozenset({f("software_licence"), f("breach_of_delivery"),
                             f("commercial_context"), f("consequential_damages_claim")}),
            issues=frozenset({i("breach_of_contract"), i("damages_quantum"),
                              i("mitigation_duty")}),
            jurisdiction="federal", court=CourtLevel.SUPREME, year=2023,
        ),
    ]

    print(f"\nQuery: {query.name}")
    print(f"  Issues: {sorted(query.issue_labels)}")
    print(f"  Facts:  {sorted(query.fact_labels)}")
    print(f"\nCorpus size: {len(corpus)} cases")

    results = retrieve_top_k(query, corpus, k=3, current_year=2024, alpha=0.7)

    print(f"\n--- Top 3 Retrieved Cases (alpha=0.70) ---")
    print(f"{'Rank':<5} {'Case':<38} {'Rel':>6} {'Auth':>6} {'Final':>6}")
    print("-" * 65)
    for r in results:
        print(f"{r.rank:<5} {r.case_name:<38} {r.relevance_score:>6.3f} "
              f"{r.authority_score:>6.3f} {r.final_score:>6.3f}")

    print("\n" + "=" * 65)
    print("Demo completed successfully.")


if __name__ == "__main__":
    _demo()
