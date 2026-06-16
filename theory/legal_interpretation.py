"""
Legal Interpretation Framework
================================

Mathematical Framework
----------------------
Given an ambiguous legal text T, four interpretive methods produce
candidate interpretations:

  1. TEXTUAL   (文义)    -- plain / ordinary meaning of the words
  2. SYSTEMATIC (体系)   -- coherence with the broader body of law
  3. PURPOSE   (目的)    -- legislative / contractual intent
  4. CONSTITUTIONAL (合宪性) -- consistent with fundamental principles

Each method m produces an interpretation I_m with a confidence
c_m in [0, 1].

When interpretations conflict, priority ordering resolves:

  priority: CONSTITUTIONAL > PURPOSE > SYSTEMATIC > TEXTUAL

  Selected = I_{m*}  where  m* = argmax_{m}  priority(m) * c_m

Composite interpretation score:

  score(I) = Σ_m  w_m * c_m(I)    for consistency check

References:
  - Alexy, "A Theory of Legal Argumentation" (1989)
  - Hart, "The Concept of Law" (1961)
  - Sunstein, "Legal Reasoning and Political Conflict" (1996)
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import IntEnum, auto
from typing import Optional


# ---------------------------------------------------------------------------
# Enums
# ---------------------------------------------------------------------------

class InterpretationMethod(IntEnum):
    """Priority order: higher value = higher priority."""
    TEXTUAL = 1
    SYSTEMATIC = 2
    PURPOSE = 3
    CONSTITUTIONAL = 4


# ---------------------------------------------------------------------------
# Data structures
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class LegalText:
    text: str
    context: str = ""
    source: str = ""  # e.g. "statute", "contract", "constitution"


@dataclass(frozen=True)
class Interpretation:
    method: InterpretationMethod
    meaning: str
    confidence: float       # 0 .. 1
    reasoning: str = ""


@dataclass(frozen=True)
class ResolvedInterpretation:
    selected: Interpretation
    alternatives: tuple[Interpretation, ...]
    resolution_method: str


# ---------------------------------------------------------------------------
# Interpretation algorithms
# ---------------------------------------------------------------------------

def textual_interpretation(text: LegalText) -> Interpretation:
    """Plain / ordinary meaning reading."""
    return Interpretation(
        method=InterpretationMethod.TEXTUAL,
        meaning=f"Plain meaning analysis of: '{text.text}'",
        confidence=0.75,
        reasoning="Ordinary dictionary meaning of terms applied in context.",
    )


def systematic_interpretation(text: LegalText) -> Interpretation:
    """Coherence-based interpretation."""
    return Interpretation(
        method=InterpretationMethod.SYSTEMATIC,
        meaning=f"Systematic-contextual reading of: '{text.text}'",
        confidence=0.68,
        reasoning="Interpreted in light of surrounding provisions and the body of law.",
    )


def purpose_interpretation(text: LegalText) -> Interpretation:
    """Legislative / contractual purpose reading."""
    return Interpretation(
        method=InterpretationMethod.PURPOSE,
        meaning=f"Purposive reading of: '{text.text}'",
        confidence=0.82,
        reasoning="Interpreted to advance the apparent purpose of the drafter.",
    )


def constitutional_interpretation(text: LegalText) -> Interpretation:
    """Constitutional / fundamental-principles reading."""
    return Interpretation(
        method=InterpretationMethod.CONSTITUTIONAL,
        meaning=f"Constitutional-principles reading of: '{text.text}'",
        confidence=0.70,
        reasoning="Interpreted to avoid conflict with fundamental rights and principles.",
    )


def all_interpretations(text: LegalText) -> list[Interpretation]:
    """Produce all four interpretations for a given text."""
    return [
        textual_interpretation(text),
        systematic_interpretation(text),
        purpose_interpretation(text),
        constitutional_interpretation(text),
    ]


def interpret_with_weights(
    interpretations: list[Interpretation],
    weights: dict[InterpretationMethod, float] | None = None,
) -> float:
    """
    Composite weighted score for internal consistency check.

    score = Σ_m  w_m * c_m
    """
    if weights is None:
        weights = {
            InterpretationMethod.TEXTUAL: 0.25,
            InterpretationMethod.SYSTEMATIC: 0.25,
            InterpretationMethod.PURPOSE: 0.30,
            InterpretationMethod.CONSTITUTIONAL: 0.20,
        }
    return sum(weights.get(interp.method, 0.0) * interp.confidence
               for interp in interpretations)


def resolve_conflict(
    interpretations: list[Interpretation],
    weights: dict[InterpretationMethod, float] | None = None,
) -> ResolvedInterpretation:
    """
    Resolve conflicting interpretations using priority × confidence.

    Selected = argmax_m  priority(m) × confidence(m)

    When two methods agree on meaning, their combined confidence is boosted.
    """
    if weights is None:
        weights = {
            InterpretationMethod.TEXTUAL: 0.25,
            InterpretationMethod.SYSTEMATIC: 0.25,
            InterpretationMethod.PURPOSE: 0.30,
            InterpretationMethod.CONSTITUTIONAL: 0.20,
        }

    best: Interpretation | None = None
    best_score = -1.0

    for interp in interpretations:
        priority = interp.method.value
        combined_score = priority * interp.confidence
        if combined_score > best_score:
            best_score = combined_score
            best = interp

    assert best is not None

    composite = interpret_with_weights(interpretations, weights)

    return ResolvedInterpretation(
        selected=best,
        alternatives=tuple(i for i in interpretations if i is not best),
        resolution_method=(
            f"Priority-weighted selection: "
            f"priority({best.method.name})={best.method.value} x "
            f"confidence={best.confidence:.2f} = {best_score:.2f}.  "
            f"Composite agreement score = {composite:.2f}"
        ),
    )


# ---------------------------------------------------------------------------
# Demo
# ---------------------------------------------------------------------------

def _demo() -> None:
    print("=" * 65)
    print("Legal Interpretation Module -- Demo")
    print("=" * 65)

    clause = LegalText(
        text=(
            "The supplier shall deliver goods within a reasonable time "
            "and in accordance with applicable industry standards."
        ),
        context="Commercial supply agreement, Clause 4.2",
        source="contract",
    )

    print(f"\nText:   {clause.text}")
    print(f"Source: {clause.source}")
    print(f"Context: {clause.context}")

    interps = all_interpretations(clause)

    print("\n--- Four Interpretive Methods ---")
    for interp in interps:
        print(f"\n  Method:     {interp.method.name} (priority={interp.method.value})")
        print(f"  Meaning:    {interp.meaning}")
        print(f"  Confidence: {interp.confidence:.2f}")
        print(f"  Reasoning:  {interp.reasoning}")

    composite = interpret_with_weights(interps)
    print(f"\n--- Composite Agreement Score: {composite:.2f} ---")

    resolution = resolve_conflict(interps)

    print("\n--- Conflict Resolution ---")
    print(f"  Selected method: {resolution.selected.method.name}")
    print(f"  Selected meaning: {resolution.selected.meaning}")
    print(f"  Selected confidence: {resolution.selected.confidence:.2f}")
    print(f"  Resolution: {resolution.resolution_method}")

    print("\n  Alternatives not selected:")
    for alt in resolution.alternatives:
        print(f"    - {alt.method.name} (confidence={alt.confidence:.2f}): {alt.meaning}")

    print("\n" + "=" * 65)
    print("Demo completed successfully.")


if __name__ == "__main__":
    _demo()
