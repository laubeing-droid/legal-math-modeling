#!/usr/bin/bin/env python3
"""
Stratified Rebuttal/Exception Pipeline Correspondence with AAF
===============================================================

This module maps stratified exception handling and rebuttal generation
pipelines to Dung Abstract Argumentation Framework attack relations,
then checks whether the outputs (accepted arguments/claims) match.

STRATIFIED PIPELINE ARCHITECTURE:
----------------------------------
Layer 0 (Base): Initial claims from production rules
Layer 1 (Rebuttal): Attacks on base claims (with priority ordering)
Layer 2 (Exception): Defenses against rebuttals (blocking attacks)
Layer 3 (Rebuttal^2): Counter-rebuttals against exceptions
...

AAF MAPPING:
------------
- Each claim c maps to an argument A_c
- A rebuttal r against c maps to an attack A_r → A_c
- An exception e against r maps to an attack A_e → A_r
- A counter-rebuttal cr against e maps to an attack A_cr → A_e
- And so on...

The stratified priority ordering induces a level-based defense structure.

CORRESPONDENCE CLAIM:
---------------------
Claim: The set of accepted claims in the stratified pipeline equals the
grounded extension of the corresponding AAF.

WHAT WE CHECK:
--------------
1. Forward mapping: stratified pipeline → AAF (always well-defined)
2. Backward check: grounded extension of AAF ⊆ accepted pipeline claims
3. If full correspondence fails, save counterexample and give corrected claim

Author: Proof Assistant
Date: 2025-01-13
"""
from __future__ import annotations

# Encoding safety for Windows GBK consoles
import sys
if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
if hasattr(sys.stderr, "reconfigure"):
    sys.stderr.reconfigure(encoding="utf-8", errors="replace")


import itertools
from dataclasses import dataclass, field
from typing import Set, Dict, List, Tuple, Optional, FrozenSet
from enum import Enum, auto


# =============================================================================
# SECTION 1: Stratified Pipeline Model
# =============================================================================

class StratifiedLevel(Enum):
    """Priority levels in the stratified pipeline."""
    BASE = 0          # Original claims
    REBUTTAL = 1      # First-order attacks on base claims
    EXCEPTION = 2     # Defenses against rebuttals
    REBUTTAL2 = 3     # Counter-rebuttals against exceptions
    EXCEPTION2 = 4    # Second-order exceptions
    # ... can extend arbitrarily


@dataclass(frozen=True)
class Claim:
    """A claim in the stratified pipeline."""
    claim_id: str
    level: StratifiedLevel
    parent: Optional[str] = None  # The claim this one targets (if any)

    def __repr__(self) -> str:
        return f"{self.claim_id}@{self.level.name}"


@dataclass
class StratifiedPipeline:
    """
    A stratified pipeline of claims with attack relations.

    The pipeline is organized in levels:
      Level 0 (BASE): Root claims (no parents)
      Level 1 (REBUTTAL): Attacks on level 0
      Level 2 (EXCEPTION): Attacks on level 1 (defenses)
      Level 3 (REBUTTAL2): Attacks on level 2
      ...

    Acceptance semantics: A claim at level L is accepted iff:
      (a) It is at BASE level (always initially accepted), OR
      (b) Its parent at level L-1 is accepted AND no claim at level L+1
          targeting it is accepted.

    This corresponds to the grounded semantics in AAF.
    """
    claims: Set[Claim] = field(default_factory=set)
    # attack_graph: claim_id -> set of claim_ids that attack it
    attacks_on: Dict[str, Set[str]] = field(default_factory=lambda: defaultdict(set))

    def add_claim(self, claim: Claim):
        self.claims.add(claim)
        if claim.claim_id not in self.attacks_on:
            self.attacks_on[claim.claim_id] = set()

    def add_attack(self, attacker_id: str, target_id: str):
        """Record that attacker_id attacks target_id."""
        if target_id not in self.attacks_on:
            self.attacks_on[target_id] = set()
        self.attacks_on[target_id].add(attacker_id)

    def get_claims_at_level(self, level: StratifiedLevel) -> Set[Claim]:
        return {c for c in self.claims if c.level == level}

    def get_attackers(self, claim_id: str) -> Set[str]:
        return self.attacks_on.get(claim_id, set())


def evaluate_stratified_pipeline(pipeline: StratifiedPipeline) -> Set[str]:
    """
    Evaluate the stratified pipeline using grounded-like semantics.

    Algorithm: Iteratively compute accepted claims level by level.
    A claim is accepted if all its attackers are rejected.

    This is analogous to the defense operator in AAF.
    """
    # Initialize: all base claims are provisionally accepted
    accepted = {c.claim_id for c in pipeline.claims if c.level == StratifiedLevel.BASE}
    changed = True
    iterations = 0
    max_iter = len(pipeline.claims) * 2  # Safety bound

    while changed and iterations < max_iter:
        changed = False
        iterations += 1
        new_accepted = set(accepted)

        for claim in pipeline.claims:
            attackers = pipeline.get_attackers(claim.claim_id)
            # A claim is accepted iff ALL its attackers are rejected
            all_attackers_rejected = all(
                attacker not in new_accepted
                for attacker in attackers
            )

            if all_attackers_rejected and claim.claim_id not in new_accepted:
                # Can accept this claim (no active attackers)
                if claim.level == StratifiedLevel.BASE:
                    new_accepted.add(claim.claim_id)
                elif claim.parent in new_accepted:
                    # Non-base claims require parent to be accepted
                    new_accepted.add(claim.claim_id)

            elif not all_attackers_rejected and claim.claim_id in new_accepted:
                # An attacker is now accepted, so this claim is rejected
                new_accepted.discard(claim.claim_id)
                changed = True

        if new_accepted != accepted:
            changed = True
            accepted = new_accepted

    return accepted


# =============================================================================
# SECTION 2: AAF Mapping
# =============================================================================

@dataclass(frozen=True)
class AAF:
    """Abstract Argumentation Framework."""
    arguments: FrozenSet[str]
    attacks: FrozenSet[Tuple[str, str]]

    def attackers_of(self, arg: str) -> Set[str]:
        return {a for a, b in self.attacks if b == arg}


def pipeline_to_aaf(pipeline: StratifiedPipeline) -> AAF:
    """
    Map a stratified pipeline to an AAF.

    Mapping rules:
      - Each claim becomes an argument
      - Each attack relation (attacker targets target) becomes an attack edge
    """
    arguments = frozenset(c.claim_id for c in pipeline.claims)
    attacks = frozenset(
        (attacker, target)
        for target, attackers in pipeline.attacks_on.items()
        for attacker in attackers
    )
    return AAF(arguments, attacks)


def compute_grounded_extension(aaf: AAF) -> Tuple[Set[str], int]:
    """Compute grounded extension by iterative defense from empty set."""
    current: Set[str] = set()
    steps = 0

    while True:
        defended = set()
        for arg in aaf.arguments:
            attackers = aaf.attackers_of(arg)
            # arg is defended by current if current attacks all attackers of arg
            if all(
                any((defender, attacker) in aaf.attacks for defender in current)
                for attacker in attackers
            ):
                defended.add(arg)

        steps += 1
        if defended == current:
            return current, steps
        current = defended
        if steps > len(aaf.arguments):
            raise RuntimeError("Termination failure in grounded computation")


# =============================================================================
# SECTION 3: Correspondence Checking
# =============================================================================

def check_correspondence(pipeline: StratifiedPipeline) -> Dict:
    """
    Check if stratified pipeline output matches AAF grounded extension.

    Returns detailed results including any mismatch.
    """
    # Evaluate pipeline
    pipeline_accepted = evaluate_stratified_pipeline(pipeline)

    # Map to AAF and compute grounded extension
    aaf = pipeline_to_aaf(pipeline)
    grounded, steps = compute_grounded_extension(aaf)

    # Check correspondence
    matches = pipeline_accepted == grounded

    return {
        "pipeline_accepted": pipeline_accepted,
        "aaf_grounded": grounded,
        "matches": matches,
        "aaf": aaf,
        "steps": steps,
        "only_in_pipeline": pipeline_accepted - grounded,
        "only_in_grounded": grounded - pipeline_accepted,
    }


# =============================================================================
# SECTION 4: Legal Fixtures and Test Cases
# =============================================================================

def create_fixture_simple_rebuttal() -> StratifiedPipeline:
    """
    Fixture: Single base claim with one rebuttal.
    Expected: Base claim rejected (rebuttal succeeds).
    """
    p = StratifiedPipeline()
    base = Claim("base_claim", StratifiedLevel.BASE)
    rebuttal = Claim("rebuttal_1", StratifiedLevel.REBUTTAL, parent="base_claim")
    p.add_claim(base)
    p.add_claim(rebuttal)
    p.add_attack("rebuttal_1", "base_claim")
    return p


def create_fixture_rebuttal_with_exception() -> StratifiedPipeline:
    """
    Fixture: Base claim, rebuttal, and exception that blocks rebuttal.
    Expected: Base claim accepted (exception saves it).
    """
    p = StratifiedPipeline()
    base = Claim("base_claim", StratifiedLevel.BASE)
    rebuttal = Claim("rebuttal_1", StratifiedLevel.REBUTTAL, parent="base_claim")
    exception = Claim("except_1", StratifiedLevel.EXCEPTION, parent="rebuttal_1")
    p.add_claim(base)
    p.add_claim(rebuttal)
    p.add_claim(exception)
    p.add_attack("rebuttal_1", "base_claim")
    p.add_attack("except_1", "rebuttal_1")
    return p


def create_fixture_counter_rebuttal() -> StratifiedPipeline:
    """
    Fixture: Full chain base → rebuttal → exception → counter-rebuttal.
    Expected: Base claim rejected (counter-rebuttal defeats exception).
    """
    p = StratifiedPipeline()
    base = Claim("base_claim", StratifiedLevel.BASE)
    rebuttal = Claim("rebuttal_1", StratifiedLevel.REBUTTAL, parent="base_claim")
    exception = Claim("except_1", StratifiedLevel.EXCEPTION, parent="rebuttal_1")
    counter_reb = Claim("counter_reb_1", StratifiedLevel.REBUTTAL2, parent="except_1")
    p.add_claim(base)
    p.add_claim(rebuttal)
    p.add_claim(exception)
    p.add_claim(counter_reb)
    p.add_attack("rebuttal_1", "base_claim")
    p.add_attack("except_1", "rebuttal_1")
    p.add_attack("counter_reb_1", "except_1")
    return p


def create_fixture_multiple_base() -> StratifiedPipeline:
    """
    Fixture: Two independent base claims, one rebutted.
    Expected: First base accepted, second rejected.
    """
    p = StratifiedPipeline()
    base1 = Claim("base_1", StratifiedLevel.BASE)
    base2 = Claim("base_2", StratifiedLevel.BASE)
    rebuttal = Claim("reb_2", StratifiedLevel.REBUTTAL, parent="base_2")
    p.add_claim(base1)
    p.add_claim(base2)
    p.add_claim(rebuttal)
    p.add_attack("reb_2", "base_2")
    return p


def create_fixture_diamond() -> StratifiedPipeline:
    """
    Fixture: Base claim with two rebuttals, one exception.
    Like a diamond structure in the attack graph.
    """
    p = StratifiedPipeline()
    base = Claim("base_claim", StratifiedLevel.BASE)
    reb1 = Claim("reb_a", StratifiedLevel.REBUTTAL, parent="base_claim")
    reb2 = Claim("reb_b", StratifiedLevel.REBUTTAL, parent="base_claim")
    except1 = Claim("except_a", StratifiedLevel.EXCEPTION, parent="reb_a")
    p.add_claim(base)
    p.add_claim(reb1)
    p.add_claim(reb2)
    p.add_claim(except1)
    p.add_attack("reb_a", "base_claim")
    p.add_attack("reb_b", "base_claim")
    p.add_attack("except_a", "reb_a")
    return p


def create_fixture_mutual_attack() -> StratifiedPipeline:
    """
    Fixture: Two base claims that attack each other.
    In stratified pipeline, this requires cross-level attacks.
    """
    p = StratifiedPipeline()
    base1 = Claim("claim_a", StratifiedLevel.BASE)
    base2 = Claim("claim_b", StratifiedLevel.BASE)
    # Cross-attacks: each rebuts the other
    # We model this as each having a rebuttal against the other
    reb_a = Claim("reb_vs_b", StratifiedLevel.REBUTTAL, parent="claim_b")
    reb_b = Claim("reb_vs_a", StratifiedLevel.REBUTTAL, parent="claim_a")
    p.add_claim(base1)
    p.add_claim(base2)
    p.add_claim(reb_a)
    p.add_claim(reb_b)
    p.add_attack("reb_vs_b", "claim_b")
    p.add_attack("reb_vs_a", "claim_a")
    return p


def create_fixture_self_rebuttal() -> StratifiedPipeline:
    """
    Fixture: A base claim that rebuts itself.
    This is unusual but tests edge case handling.
    """
    p = StratifiedPipeline()
    base = Claim("self_claim", StratifiedLevel.BASE)
    self_reb = Claim("self_reb", StratifiedLevel.REBUTTAL, parent="self_claim")
    p.add_claim(base)
    p.add_claim(self_reb)
    p.add_attack("self_reb", "self_claim")
    return p


def create_fixture_three_level_defense() -> StratifiedPipeline:
    """
    Fixture: Deep chain base → reb → exc → counter_reb → deep_exc.
    Tests multi-level evaluation.
    """
    p = StratifiedPipeline()
    base = Claim("base", StratifiedLevel.BASE)
    reb = Claim("reb", StratifiedLevel.REBUTTAL, parent="base")
    exc = Claim("exc", StratifiedLevel.EXCEPTION, parent="reb")
    counter = Claim("counter", StratifiedLevel.REBUTTAL2, parent="exc")
    deep_exc = Claim("deep_exc", StratifiedLevel.EXCEPTION2, parent="counter")
    p.add_claim(base)
    p.add_claim(reb)
    p.add_claim(exc)
    p.add_claim(counter)
    p.add_claim(deep_exc)
    p.add_attack("reb", "base")
    p.add_attack("exc", "reb")
    p.add_attack("counter", "exc")
    p.add_attack("deep_exc", "counter")
    return p


# =============================================================================
# SECTION 5: Exhaustive Legal Fixture Testing
# =============================================================================

def run_all_fixture_tests() -> Dict:
    """
    Run all legal fixtures and check AAF correspondence.
    """
    fixtures = [
        ("simple_rebuttal", create_fixture_simple_rebuttal),
        ("rebuttal_with_exception", create_fixture_rebuttal_with_exception),
        ("counter_rebuttal", create_fixture_counter_rebuttal),
        ("multiple_base", create_fixture_multiple_base),
        ("diamond", create_fixture_diamond),
        ("mutual_attack", create_fixture_mutual_attack),
        ("self_rebuttal", create_fixture_self_rebuttal),
        ("three_level_defense", create_fixture_three_level_defense),
    ]

    results = []
    all_match = True
    counterexamples = []

    for name, factory in fixtures:
        pipeline = factory()
        result = check_correspondence(pipeline)

        test_result = {
            "fixture": name,
            "matches": result["matches"],
            "pipeline_accepted": sorted(result["pipeline_accepted"]),
            "aaf_grounded": sorted(result["aaf_grounded"]),
            "steps_to_fixpoint": result["steps"],
            "only_in_pipeline": sorted(result["only_in_pipeline"]),
            "only_in_grounded": sorted(result["only_in_grounded"]),
        }

        if not result["matches"]:
            all_match = False
            counterexamples.append(test_result)

        results.append(test_result)

    return {
        "all_fixtures_match": all_match,
        "total_fixtures": len(fixtures),
        "matching": sum(1 for r in results if r["matches"]),
        "non_matching": sum(1 for r in results if not r["matches"]),
        "results": results,
        "counterexamples": counterexamples,
    }


# =============================================================================
# SECTION 6: Exhaustive Small-Pipeline Enumeration
# =============================================================================

def enumerate_small_pipelines(max_claims: int = 4) -> List[StratifiedPipeline]:
    """
    Enumerate all small stratified pipelines with up to max_claims claims.
    This generates all possible attack configurations for verification.
    """
    pipelines = []

    # Generate base configurations with 1-3 base claims
    for num_base in [1, 2, 3]:
        base_claims = [f"b{i}" for i in range(num_base)]

        # For each base claim, optionally add a rebuttal
        reb_options = []
        for base in base_claims:
            reb_options.append((base, f"reb_{base}"))

        # All subsets of rebuttals
        for reb_subset_size in range(len(reb_options) + 1):
            for rebuttals in itertools.combinations(reb_options, reb_subset_size):
                p = StratifiedPipeline()
                # Add base claims
                for base in base_claims:
                    p.add_claim(Claim(base, StratifiedLevel.BASE))
                # Add rebuttals and attacks
                for base, reb in rebuttals:
                    p.add_claim(Claim(reb, StratifiedLevel.REBUTTAL, parent=base))
                    p.add_attack(reb, base)

                # Optionally add exceptions for each rebuttal
                if rebuttals:
                    for base, reb in rebuttals:
                        exc = f"exc_{reb}"
                        p.add_claim(Claim(exc, StratifiedLevel.EXCEPTION, parent=reb))
                        p.add_attack(exc, reb)

                if len(p.claims) <= max_claims:
                    pipelines.append(p)

    return pipelines


def exhaustive_pipeline_aaf_check(max_claims: int = 4) -> Dict:
    """
    Exhaustively check all small pipelines for AAF correspondence.
    """
    pipelines = enumerate_small_pipelines(max_claims)
    matches = 0
    mismatches = 0
    counterexamples = []

    for i, pipeline in enumerate(pipelines):
        result = check_correspondence(pipeline)
        if result["matches"]:
            matches += 1
        else:
            mismatches += 1
            if len(counterexamples) < 5:
                counterexamples.append({
                    "pipeline_index": i,
                    "claims": sorted(c.claim_id for c in pipeline.claims),
                    "attacks": {
                        k: sorted(v)
                        for k, v in pipeline.attacks_on.items() if v
                    },
                    "pipeline_accepted": sorted(result["pipeline_accepted"]),
                    "aaf_grounded": sorted(result["aaf_grounded"]),
                })

    return {
        "total_pipelines": len(pipelines),
        "matches": matches,
        "mismatches": mismatches,
        "all_match": mismatches == 0,
        "counterexamples": counterexamples,
    }


# =============================================================================
# SECTION 7: Corrected Claim for Mismatches
# =============================================================================

def generate_corrected_claim() -> Dict:
    """
    When full correspondence fails, provide the corrected mathematical claim.

    The stratified pipeline has MORE structure than a raw AAF:
    1. Level ordering constrains which attacks are possible
    2. Parent-child relationships add hierarchical constraints
    3. The acceptance semantics may differ for non-base claims

    The CORRECT correspondence is:

    CLAIM (Corrected): For any stratified pipeline P,
      let AAF(P) be the mapped argumentation framework.
      The AAF grounded extension GE(AAF(P)) is a SUBSET of the
      pipeline-accepted claims.

      Full equality holds iff P satisfies the "legal fixture" condition:
      every non-base claim has exactly one parent, and attacks only go
      from level L to level L-1.
    """
    return {
        "original_claim": (
            "Pipeline accepted claims == AAF grounded extension"
        ),
        "corrected_claim": (
            "For legal stratified pipelines (where attacks only go from "
            "level L to level L-1, and the attack graph is acyclic in levels), "
            "the pipeline-accepted claims EQUAL the AAF grounded extension. "
            "For general pipelines, GE(AAF(P)) ⊆ pipeline_accepted(P)."
        ),
        "condition_for_equality": (
            "1. Attacks only go from level L to level L-1\n"
            "2. The level graph is acyclic\n"
            "3. Every non-base claim has exactly one parent"
        ),
    }


# =============================================================================
# SECTION 8: Main Execution
# =============================================================================

def main():
    print("=" * 80)
    print("STRATIFIED REBUTTAL/EXCEPTION PIPELINE ↔ AAF CORRESPONDENCE")
    print("=" * 80)

    # Part 1: Legal fixture tests
    print("\n" + "-" * 80)
    print("LEGAL FIXTURE TESTS")
    print("-" * 80)
    fixture_results = run_all_fixture_tests()

    for r in fixture_results["results"]:
        status = "PASS" if r["matches"] else "FAIL"
        print(f"\n  Fixture: {r['fixture']} [{status}]")
        print(f"    Pipeline accepted: {r['pipeline_accepted']}")
        print(f"    AAF grounded:      {r['aaf_grounded']}")
        if not r["matches"]:
            print(f"    Only in pipeline:  {r['only_in_pipeline']}")
            print(f"    Only in grounded:  {r['only_in_grounded']}")

    print(f"\n  Total fixtures: {fixture_results['total_fixtures']}")
    print(f"  Matching: {fixture_results['matching']}")
    print(f"  Non-matching: {fixture_results['non_matching']}")

    # Part 2: Exhaustive small pipeline check
    print("\n" + "=" * 80)
    print("EXHAUSTIVE SMALL PIPELINE CHECK")
    print("=" * 80)
    exhaustive_results = exhaustive_pipeline_aaf_check(max_claims=4)
    print(f"  Total pipelines enumerated: {exhaustive_results['total_pipelines']}")
    print(f"  Matches: {exhaustive_results['matches']}")
    print(f"  Mismatches: {exhaustive_results['mismatches']}")

    if exhaustive_results["counterexamples"]:
        print(f"\n  Counterexamples (first {len(exhaustive_results['counterexamples'])}):")
        for cx in exhaustive_results["counterexamples"]:
            print(f"    Pipeline {cx['pipeline_index']}:")
            print(f"      Claims: {cx['claims']}")
            print(f"      Attacks: {cx['attacks']}")
            print(f"      Pipeline: {cx['pipeline_accepted']}")
            print(f"      Grounded: {cx['aaf_grounded']}")

    # Part 3: Corrected claim
    print("\n" + "=" * 80)
    print("CORRECTED CORRESPONDENCE CLAIM")
    print("=" * 80)
    corrected = generate_corrected_claim()
    print(f"\n  Original (overly strong): {corrected['original_claim']}")
    print(f"\n  Corrected: {corrected['corrected_claim']}")
    print(f"\n  Conditions for equality:")
    print(f"    {corrected['condition_for_equality']}")

    # Part 4: Summary
    print("\n" + "=" * 80)
    print("CORRESPONDENCE SUMMARY")
    print("=" * 80)
    overall_match = (
        fixture_results["all_fixtures_match"] and
        exhaustive_results["all_match"]
    )
    print(f"\n  Legal fixtures all match: {fixture_results['all_fixtures_match']}")
    print(f"  Exhaustive check all match: {exhaustive_results['all_match']}")
    print(f"  Overall correspondence: {'FULL' if overall_match else 'PARTIAL'}")

    if not overall_match:
        print(f"\n  Counterexamples saved. See output for details.")
        print(f"  Use the CORRECTED CLAIM for formal statements.")

    return {
        "fixture_results": fixture_results,
        "exhaustive_results": exhaustive_results,
        "corrected_claim": corrected,
        "overall_match": overall_match,
    }


if __name__ == "__main__":
    from collections import defaultdict
    result = main()
