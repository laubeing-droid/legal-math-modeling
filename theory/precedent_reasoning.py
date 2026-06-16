"""
Precedent Reasoning (Stare Decisis) in Legal Systems
=====================================================

Mathematical Framework
----------------------
A precedent P = (C, H, R) where:
  - C = case facts and issues
  - H = holding (ratio decidendi)
  - R = court level in the judicial hierarchy

Binding strength:
  bind(P, Q) = authority(P) × f(Δ_facts(P, Q))

where authority(P) = level(P) / max_level and Δ_facts measures
material factual divergence.

Four precedent actions:
  1. FOLLOW    (遵循)  -- apply the holding directly
  2. DISTINGUISH (区分) -- decline to apply because material facts differ
  3. OVERRULE  (推翻)  -- reject the holding as wrongly decided
  4. CREATE    (创设)  -- establish a new rule for an unaddressed issue

Distinguishing condition:
  DISTINGUISH(P, Q) iff  Δ_facts(P, Q) > threshold
                         AND the differing fact is legally material

References:
  - Alexander, "Precedent" in A Companion to Philosophy of Law (1996)
  - MacCormick, "Legal Reasoning and Legal Theory" (1978)
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum, auto
from typing import FrozenSet


# ---------------------------------------------------------------------------
# Enums
# ---------------------------------------------------------------------------

class PrecedentAction(Enum):
    FOLLOW = "FOLLOW"
    DISTINGUISH = "DISTINGUISH"
    OVERRULE = "OVERRULE"
    CREATE = "CREATE"


class CourtLevel(Enum):
    """Higher numeric value = more authoritative."""
    TRIAL = 1
    APPELLATE = 2
    SUPREME = 3


# ---------------------------------------------------------------------------
# Core data structures
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class MaterialFact:
    label: str
    materiality: float = 1.0  # 0 .. 1

    def __hash__(self) -> int:
        return hash(self.label)

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, MaterialFact):
            return NotImplemented
        return self.label == other.label


@dataclass(frozen=True)
class Holding:
    rule: str
    confidence: float = 1.0  # 0 .. 1


@dataclass(frozen=True)
class Precedent:
    name: str
    facts: FrozenSet[MaterialFact]
    holding: Holding
    court: CourtLevel
    year: int = 2020
    jurisdiction: str = "default"

    @property
    def fact_labels(self) -> set[str]:
        return {f.label for f in self.facts}


@dataclass
class PrecedentLink:
    """A link from a current case to a precedent, with an action."""
    source: str        # current case name
    target: str        # precedent case name
    action: PrecedentAction
    reason: str = ""
    binding_strength: float = 0.0


# ---------------------------------------------------------------------------
# Algorithms
# ---------------------------------------------------------------------------

MAX_COURT_LEVEL: int = max(lvl.value for lvl in CourtLevel)


def authority(p: Precedent) -> float:
    """Normalised authority: court level / max court level."""
    return p.court.value / MAX_COURT_LEVEL


def factual_divergence(p: Precedent, q: Precedent) -> float:
    """
    Normalised factual divergence: 1 - Jaccard similarity of facts.
    0 means identical facts; 1 means completely different.
    """
    fl_p = p.fact_labels
    fl_q = q.fact_labels
    union = fl_p | fl_q
    if not union:
        return 0.0
    intersection = fl_p & fl_q
    return 1.0 - len(intersection) / len(union)


def binding_strength(
    precedent: Precedent,
    current: Precedent,
) -> float:
    """
    bind(P, Q) = authority(P) × (1 - Δ_facts(P, Q))
    """
    auth = authority(precedent)
    div = factual_divergence(precedent, current)
    return auth * (1.0 - div)


def materiality_of_distinguishing_facts(
    precedent: Precedent,
    current: Precedent,
) -> float:
    """Average materiality of facts that differ between the two cases."""
    diff_labels = precedent.fact_labels.symmetric_difference(current.fact_labels)
    if not diff_labels:
        return 0.0
    all_facts = set(precedent.facts) | set(current.facts)
    diff_facts = [f for f in all_facts if f.label in diff_labels]
    if not diff_facts:
        return 0.0
    return sum(f.materiality for f in diff_facts) / len(diff_facts)


def determine_action(
    precedent: Precedent,
    current: Precedent,
    distinguish_threshold: float = 0.3,
    overrule: bool = False,
) -> PrecedentAction:
    """
    Determine the appropriate precedent action.

    Decision logic:
      1. If explicit overrule requested -> OVERRULE
      2. If factual divergence materiality > threshold -> DISTINGUISH
      3. If precedent covers the issue and facts are similar -> FOLLOW
      4. Otherwise -> CREATE (new rule needed)
    """
    if overrule:
        return PrecedentAction.OVERRULE

    mat = materiality_of_distinguishing_facts(precedent, current)
    if mat > distinguish_threshold:
        return PrecedentAction.DISTINGUISH

    bs = binding_strength(precedent, current)
    if bs > 0.4:
        return PrecedentAction.FOLLOW

    return PrecedentAction.CREATE


def apply_precedent(
    precedent: Precedent,
    current: Precedent,
    distinguish_threshold: float = 0.3,
    overrule: bool = False,
) -> PrecedentLink:
    """Apply a precedent to a current case and return the link."""
    action = determine_action(precedent, current, distinguish_threshold, overrule)
    bs = binding_strength(precedent, current)

    reasons = {
        PrecedentAction.FOLLOW: f"Binding strength {bs:.2f}; facts closely analogous.",
        PrecedentAction.DISTINGUISH: (
            f"Material factual divergence "
            f"{materiality_of_distinguishing_facts(precedent, current):.2f} "
            f"exceeds threshold {distinguish_threshold}."
        ),
        PrecedentAction.OVERRULE: "Holding explicitly overruled as wrongly decided.",
        PrecedentAction.CREATE: "No sufficiently analogous precedent; new rule created.",
    }

    return PrecedentLink(
        source=current.name,
        target=precedent.name,
        action=action,
        reason=reasons[action],
        binding_strength=bs,
    )


def precedent_chain(
    current: Precedent,
    precedents: list[Precedent],
    distinguish_threshold: float = 0.3,
    overrule_names: set[str] | None = None,
) -> list[PrecedentLink]:
    """Build a precedent reasoning chain against a list of prior precedents."""
    overrule_set = overrule_names or set()
    links: list[PrecedentLink] = []
    for p in precedents:
        link = apply_precedent(
            p, current, distinguish_threshold, overrule=(p.name in overrule_set)
        )
        links.append(link)
    return links


# ---------------------------------------------------------------------------
# Demo
# ---------------------------------------------------------------------------

def _demo() -> None:
    print("=" * 65)
    print("Precedent Reasoning Module -- Demo")
    print("=" * 65)

    def fact(label: str, mat: float = 1.0) -> MaterialFact:
        return MaterialFact(label, mat)

    # Historical precedent (Supreme Court)
    brown_v_board = Precedent(
        name="Brown v. Board of Education (1954)",
        facts=frozenset({
            fact("racial_segregation"),
            fact("public_school"),
            fact("state_mandated"),
            fact("equal_protection_clause"),
        }),
        holding=Holding(rule="Separate educational facilities are inherently unequal"),
        court=CourtLevel.SUPREME,
        year=1954,
    )

    # Appellate precedent on employment discrimination
    griggs_v_duke = Precedent(
        name="Griggs v. Duke Power (1971)",
        facts=frozenset({
            fact("employment_discrimination"),
            fact("facially_neutral_policy"),
            fact("disparate_impact"),
            fact("lack_business_necessity"),
        }),
        holding=Holding(rule="Facially neutral policies with disparate impact violate Title VII"),
        court=CourtLevel.SUPREME,
        year=1971,
    )

    # Current case 1 -- closely analogous to Brown
    current_similar = Precedent(
        name="Harris v. School District (2023)",
        facts=frozenset({
            fact("racial_segregation"),
            fact("public_school"),
            fact("state_mandated"),
            fact("equal_protection_clause"),
        }),
        holding=Holding(rule="?"),
        court=CourtLevel.APPELLATE,
        year=2023,
    )

    # Current case 2 -- materially different facts from Brown
    current_different = Precedent(
        name="Martinez v. TechCorp (2024)",
        facts=frozenset({
            fact("employment_discrimination"),
            fact("facially_neutral_policy"),
            fact("disparate_impact"),
            fact("algorithmic_hiring"),
        }),
        holding=Holding(rule="?"),
        court=CourtLevel.APPELLATE,
        year=2024,
    )

    precedents = [brown_v_board, griggs_v_duke]

    print("\n--- Precedent Chain for: Harris v. School District (2023) ---")
    links1 = precedent_chain(current_similar, precedents)
    for link in links1:
        print(f"  [{link.action.value:12s}] {link.source} <- {link.target}")
        print(f"                 strength={link.binding_strength:.2f}  reason={link.reason}")

    print("\n--- Precedent Chain for: Martinez v. TechCorp (2024) ---")
    links2 = precedent_chain(current_different, precedents)
    for link in links2:
        print(f"  [{link.action.value:12s}] {link.source} <- {link.target}")
        print(f"                 strength={link.binding_strength:.2f}  reason={link.reason}")

    # Demonstrate an OVERRULE
    print("\n--- OVERRULE demonstration ---")
    link_overrule = apply_precedent(griggs_v_duke, current_different, overrule=True)
    print(f"  [{link_overrule.action.value:12s}] {link_overrule.source} <- {link_overrule.target}")
    print(f"                 strength={link_overrule.binding_strength:.2f}  reason={link_overrule.reason}")

    print("\n" + "=" * 65)
    print("Demo completed successfully.")


if __name__ == "__main__":
    _demo()
