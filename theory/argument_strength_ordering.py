"""
Argument Strength Ordering for Legal Argumentation.

Mathematical definition
-----------------------
Given an argument A, the strength function S maps A to a value in [0, 1]:

    S(A) = w1 * evidence_strength(A)
         + w2 * rule_authority(A)
         + w3 * chain_length_factor(A)
         + w4 * source_reliability(A)

where
  w1 + w2 + w3 + w4 = 1,  wi >= 0

Components
----------
evidence_strength(A) : average credibility of factual premises in A
rule_authority(A)    : average authority score of defeasible rules in A
chain_length_factor(A) : exponential decay w.r.t. proof depth:
                         c^depth(A)  where c in (0,1], default c = 0.9
source_reliability(A): average reliability of evidence sources

Ordering
--------
A <= B  iff  S(A) <= S(B)
A <  B  iff  S(A) <  S(B)  and  there is no extension making them equal
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Sequence


# ------------------------------------------------------------------ #
#  Data structures                                                     #
# ------------------------------------------------------------------ #

@dataclass
class Evidence:
    """A piece of evidence supporting a premise."""
    name: str
    credibility: float      # in [0, 1]
    source_reliability: float  # in [0, 1]


@dataclass
class DefeasibleRuleRef:
    """Reference to a defeasible rule used in an argument."""
    name: str
    authority: float  # in [0, 1]


@dataclass
class LegalArgument:
    """An argument with all components needed for strength calculation."""
    name: str
    conclusion: str
    evidences: list[Evidence] = field(default_factory=list)
    rules: list[DefeasibleRuleRef] = field(default_factory=list)
    depth: int = 0  # proof chain depth (leaf = 0)


@dataclass
class StrengthWeights:
    """Weights for the four strength components, must sum to 1."""
    evidence: float = 0.35
    rule_authority: float = 0.25
    chain_length: float = 0.15
    source_reliability: float = 0.25
    decay_base: float = 0.9  # chain decay constant

    def __post_init__(self) -> None:
        total = (self.evidence + self.rule_authority
                 + self.chain_length + self.source_reliability)
        if abs(total - 1.0) > 1e-9:
            raise ValueError(
                f"Weights must sum to 1.0, got {total:.4f}"
            )


# ------------------------------------------------------------------ #
#  Strength computation                                                #
# ------------------------------------------------------------------ #

def evidence_strength(arg: LegalArgument) -> float:
    """Average credibility of all evidences; 1.0 if no evidences."""
    if not arg.evidences:
        return 1.0
    return sum(e.credibility for e in arg.evidences) / len(arg.evidences)


def rule_authority_score(arg: LegalArgument) -> float:
    """Average authority of all rules; 1.0 if no rules (strict arg)."""
    if not arg.rules:
        return 1.0
    return sum(r.authority for r in arg.rules) / len(arg.rules)


def chain_length_factor(depth: int, base: float = 0.9) -> float:
    """Exponential decay: base^depth.  base=0.9 means 10% loss per hop."""
    return base ** depth


def source_reliability_score(arg: LegalArgument) -> float:
    """Average source reliability; 1.0 if no evidences."""
    if not arg.evidences:
        return 1.0
    return sum(e.source_reliability for e in arg.evidences) / len(arg.evidences)


def compute_strength(
    arg: LegalArgument,
    weights: StrengthWeights | None = None,
) -> float:
    """
    Compute the overall strength of an argument.

    Returns a value in [0, 1].
    """
    if weights is None:
        weights = StrengthWeights()

    s_evidence = evidence_strength(arg)
    s_rule = rule_authority_score(arg)
    s_chain = chain_length_factor(arg.depth, weights.decay_base)
    s_source = source_reliability_score(arg)

    total = (
        weights.evidence * s_evidence
        + weights.rule_authority * s_rule
        + weights.chain_length * s_chain
        + weights.source_reliability * s_source
    )
    return round(total, 6)


# ------------------------------------------------------------------ #
#  Ordering utilities                                                  #
# ------------------------------------------------------------------ #

def compare(a: LegalArgument, b: LegalArgument,
            weights: StrengthWeights | None = None) -> int:
    """
    Compare two arguments by strength.
    Returns: -1 if a < b, 0 if a == b, +1 if a > b
    """
    sa = compute_strength(a, weights)
    sb = compute_strength(b, weights)
    if sa < sb:
        return -1
    elif sa > sb:
        return +1
    return 0


def rank_arguments(
    args: Sequence[LegalArgument],
    weights: StrengthWeights | None = None,
) -> list[tuple[LegalArgument, float]]:
    """Return arguments sorted by strength (descending) with scores."""
    scored = [(a, compute_strength(a, weights)) for a in args]
    scored.sort(key=lambda x: x[1], reverse=True)
    return scored


# ------------------------------------------------------------------ #
#  Demo                                                                #
# ------------------------------------------------------------------ #

def demo() -> None:
    print("=" * 64)
    print("Argument Strength Ordering Demo")
    print("=" * 64)

    weights = StrengthWeights(
        evidence=0.30,
        rule_authority=0.25,
        chain_length=0.20,
        source_reliability=0.25,
        decay_base=0.9,
    )

    arg_a = LegalArgument(
        name="Plaintiff negligence claim",
        conclusion="Defendant is negligent",
        evidences=[
            Evidence("expert_witness_testimony", 0.85, 0.90),
            Evidence("medical_records", 0.95, 0.95),
        ],
        rules=[
            DefeasibleRuleRef("standard_of_care_rule", 0.80),
            DefeasibleRuleRef("causation_rule", 0.70),
        ],
        depth=2,
    )

    arg_b = LegalArgument(
        name="Defense contributory negligence",
        conclusion="Plaintiff contributorily negligent",
        evidences=[
            Evidence("witness_deposition", 0.60, 0.70),
        ],
        rules=[
            DefeasibleRuleRef("contributory_negligence_rule", 0.55),
        ],
        depth=1,
    )

    arg_c = LegalArgument(
        name="Strict liability (no fault required)",
        conclusion="Defendant strictly liable",
        evidences=[
            Evidence("product_defect_report", 0.90, 0.85),
            Evidence("regulatory_violation_record", 0.88, 0.92),
            Evidence("consumer_complaints", 0.70, 0.65),
        ],
        rules=[
            DefeasibleRuleRef("strict_liability_rule", 0.90),
        ],
        depth=1,
    )

    args = [arg_a, arg_b, arg_c]

    # Print component breakdown
    print("\n--- Component Breakdown ---")
    header = f"{'Argument':<40} {'Evidence':>9} {'RuleAuth':>9} {'Chain':>7} {'Source':>8}"
    print(header)
    print("-" * len(header))
    for arg in args:
        se = evidence_strength(arg)
        sr = rule_authority_score(arg)
        sc = chain_length_factor(arg.depth, weights.decay_base)
        ss = source_reliability_score(arg)
        print(f"{arg.name:<40} {se:>9.4f} {sr:>9.4f} {sc:>7.4f} {ss:>8.4f}")

    # Print final scores
    print("\n--- Final Strength Scores ---")
    print(f"  Weights: evidence={weights.evidence}, "
          f"rule_auth={weights.rule_authority}, "
          f"chain={weights.chain_length}, "
          f"source={weights.source_reliability}")
    print()
    ranked = rank_arguments(args, weights)
    for rank, (arg, score) in enumerate(ranked, 1):
        print(f"  #{rank}  S({arg.name}) = {score:.6f}")

    # Pairwise comparisons
    print("\n--- Pairwise Comparisons ---")
    import itertools
    for a, b in itertools.combinations(args, 2):
        result = compare(a, b, weights)
        symbol = {+1: ">", -1: "<", 0: "="}[result]
        print(f"  S({a.name}) {symbol} S({b.name})")

    print()


if __name__ == "__main__":
    demo()
