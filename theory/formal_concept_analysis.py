"""Formal Concept Analysis (FCA) for legal knowledge discovery.

Mathematical Framework
---------------------
A *formal context* is a triple (G, M, I) where:
  - G is a set of objects (legal cases)
  - M is a set of attributes (legal features)
  - I subseteq G x M is an incidence relation (object g has attribute m)

For A subseteq G and B subseteq M the derivation operators are:
  - A' = { m in M : for all g in A, (g,m) in I }   (common attributes)
  - B' = { g in G : for all m in B, (g,m) in I }   (common objects)

A *formal concept* is a pair (A, B) with A' = B and B' = A.
  - A is the *extent* (objects), B is the *intent* (attributes).

The set of all formal concepts, ordered by inclusion of extents (or
dual inclusion of intents), forms a complete lattice -- the
*concept lattice*.

This module implements Ganter's NextClosure algorithm for computing
all concepts, plus attribute reduction and rule extraction.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, FrozenSet, List, Optional, Set, Tuple


# ---------------------------------------------------------------------------
# Data structures
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class FormalConcept:
    """A single formal concept: extent (objects) and intent (attributes)."""
    extent: FrozenSet[str]
    intent: FrozenSet[str]

    def __repr__(self) -> str:
        objs = ", ".join(sorted(self.extent))
        attrs = ", ".join(sorted(self.intent))
        return f"Concept(extent={{{objs}}}, intent={{{attrs}}})"


# ---------------------------------------------------------------------------
# Formal Context
# ---------------------------------------------------------------------------

class FormalContext:
    """A formal context (G, M, I): objects x attributes binary relation."""

    def __init__(self, objects: List[str], attributes: List[str]) -> None:
        self.objects: List[str] = list(objects)
        self.attributes: List[str] = list(attributes)
        self._obj_idx: Dict[str, int] = {o: i for i, o in enumerate(self.objects)}
        self._attr_idx: Dict[str, int] = {a: i for i, a in enumerate(self.attributes)}
        # incidence matrix: self._incidence[obj_index][attr_index] = True/False
        n_obj = len(self.objects)
        n_attr = len(self.attributes)
        self._incidence: List[List[bool]] = [[False] * n_attr for _ in range(n_obj)]

    def set_relation(self, obj: str, attr: str, value: bool = True) -> None:
        """Set (or clear) the relation I(obj, attr)."""
        oi = self._obj_idx[obj]
        ai = self._attr_idx[attr]
        self._incidence[oi][ai] = value

    def has_attribute(self, obj: str, attr: str) -> bool:
        return self._incidence[self._obj_idx[obj]][self._attr_idx[attr]]

    # -- derivation operators ------------------------------------------------

    def object_derivation(self, obj_set: FrozenSet[str]) -> FrozenSet[str]:
        """A' = { m in M : for all g in A, (g,m) in I }."""
        if not obj_set:
            return frozenset(self.attributes)
        attr_sets = []
        for obj in obj_set:
            oi = self._obj_idx[obj]
            s = {self.attributes[ai] for ai, val in enumerate(self._incidence[oi]) if val}
            attr_sets.append(s)
        common = attr_sets[0]
        for s in attr_sets[1:]:
            common &= s
        return frozenset(common)

    def attribute_derivation(self, attr_set: FrozenSet[str]) -> FrozenSet[str]:
        """B' = { g in G : for all m in B, (g,m) in I }."""
        if not attr_set:
            return frozenset(self.objects)
        obj_sets = []
        for attr in attr_set:
            ai = self._attr_idx[attr]
            s = {self.objects[oi] for oi in range(len(self.objects)) if self._incidence[oi][ai]}
            obj_sets.append(s)
        common = obj_sets[0]
        for s in obj_sets[1:]:
            common &= s
        return frozenset(common)

    def closure(self, attr_set: FrozenSet[str]) -> FrozenSet[str]:
        """Compute the closure of an attribute set: B -> B'' via (B')' ."""
        return self.object_derivation(self.attribute_derivation(attr_set))


# ---------------------------------------------------------------------------
# Ganter's NextClosure Algorithm
# ---------------------------------------------------------------------------

def _next_closure(
    context: FormalContext,
    current: List[str],
    attrs: List[str],
) -> Optional[List[str]]:
    """Compute the next closed attribute set in lectic order.

    Returns None if *current* is the last (largest) closed set.
    """
    attr_set = set(attrs)
    m = len(attrs)

    for i in range(m - 1, -1, -1):
        a = attrs[i]
        if a in current:
            current = [c for c in current if c != a]
        else:
            # Try adding a and computing the closure
            candidate = frozenset(current + [a])
            closed = context.closure(candidate)
            # Check that everything before position i in candidate is the same
            # and that nothing new appears before position i
            ok = True
            for j in range(i):
                b = attrs[j]
                if b not in candidate and b in closed:
                    ok = False
                    break
            if ok:
                result = [attr for attr in attrs if attr in closed]
                return result
    return None


def build_concept_lattice(context: FormalContext) -> List[FormalConcept]:
    """Compute all formal concepts of a context using Ganter's NextClosure.

    Returns concepts sorted by extent size (smallest first).
    """
    attrs = list(context.attributes)
    concepts: List[FormalConcept] = []

    # Start with the empty set (closure = all objects' common attributes)
    current: List[str] = []
    while True:
        closed_attrs = frozenset(current) if current else frozenset()
        # Ensure it's actually closed
        closed_attrs = context.closure(closed_attrs)
        extent = context.attribute_derivation(closed_attrs)
        # Avoid duplicates
        concept = FormalConcept(extent=extent, intent=closed_attrs)
        if not any(c.extent == extent for c in concepts):
            concepts.append(concept)

        nxt = _next_closure(context, list(current), attrs)
        if nxt is None:
            break
        current = nxt

    # Sort by extent size (ascending), then by intent
    concepts.sort(key=lambda c: (len(c.extent), sorted(c.intent)))
    return concepts


# ---------------------------------------------------------------------------
# Attribute Reduction
# ---------------------------------------------------------------------------

def attribute_reduction(context: FormalContext) -> List[str]:
    """Find a minimal attribute set that preserves the concept lattice.

    Uses a greedy approach: try removing each attribute and check
    whether the resulting lattice (concept set) is isomorphic.
    """
    full_lattice = build_concept_lattice(context)
    full_extents = frozenset(c.extent for c in full_lattice)

    remaining = list(context.attributes)

    # Greedy removal: try each attribute, remove if lattice preserved
    changed = True
    while changed:
        changed = False
        for attr in list(remaining):
            trial_attrs = [a for a in remaining if a != attr]
            trial_ctx = _project_context(context, trial_attrs)
            trial_lattice = build_concept_lattice(trial_ctx)
            trial_extents = frozenset(c.extent for c in trial_lattice)
            if trial_extents == full_extents:
                remaining = trial_attrs
                changed = True
                break

    return remaining


def _project_context(context: FormalContext, keep_attrs: List[str]) -> FormalContext:
    """Create a new context with only the specified attributes."""
    new_ctx = FormalContext(context.objects, keep_attrs)
    for obj in context.objects:
        for attr in keep_attrs:
            if context.has_attribute(obj, attr):
                new_ctx.set_relation(obj, attr, True)
    return new_ctx


# ---------------------------------------------------------------------------
# Rule Extraction
# ---------------------------------------------------------------------------

def extract_rules(concept: FormalConcept) -> List[Tuple[FrozenSet[str], FrozenSet[str]]]:
    """Extract if-then rules from a formal concept.

    For a concept (A, B) where |B| >= 2, we generate rules:
      for each proper subset S of B:
        if (attributes in S), then (attributes in B - S)

    This captures the logical dependencies encoded in the concept.

    Returns a list of (premise, conclusion) pairs.
    """
    attrs = sorted(concept.intent)
    if len(attrs) < 2:
        return []

    rules: List[Tuple[FrozenSet[str], FrozenSet[str]]] = []

    # Generate all non-empty proper subsets
    n = len(attrs)
    for mask in range(1, (1 << n) - 1):  # exclude empty and full set
        premise = frozenset(attrs[i] for i in range(n) if mask & (1 << i))
        conclusion = frozenset(a for a in attrs if a not in premise)
        if conclusion:  # only meaningful rules
            rules.append((premise, conclusion))

    return rules


# ---------------------------------------------------------------------------
# Demo — Legal Case Context
# ---------------------------------------------------------------------------

def demo() -> None:
    print("=" * 65)
    print("Formal Concept Analysis — Legal Case Discovery Demo")
    print("=" * 65)

    # Define attributes
    attributes = [
        "contract_breach",
        "tort_claim",
        "high_damages",
        "federal_court",
        "strong_evidence",
        "plaintiff_wins",
    ]

    # Define 8 legal cases with their attributes
    cases: Dict[str, List[str]] = {
        "Case1": ["contract_breach", "high_damages", "strong_evidence", "plaintiff_wins"],
        "Case2": ["contract_breach", "federal_court", "strong_evidence", "plaintiff_wins"],
        "Case3": ["tort_claim", "high_damages", "strong_evidence", "plaintiff_wins"],
        "Case4": ["contract_breach", "tort_claim", "high_damages", "federal_court"],
        "Case5": ["tort_claim", "federal_court", "strong_evidence"],
        "Case6": ["contract_breach", "high_damages", "federal_court", "plaintiff_wins"],
        "Case7": ["tort_claim", "high_damages", "federal_court", "strong_evidence", "plaintiff_wins"],
        "Case8": ["contract_breach", "strong_evidence"],
    }

    # Build formal context
    ctx = FormalContext(list(cases.keys()), attributes)
    for case_name, attrs in cases.items():
        for attr in attrs:
            ctx.set_relation(case_name, attr, True)

    # Print context table
    print("\nFormal Context (cases x attributes):")
    header = "          " + "  ".join(f"{a[:8]:>8}" for a in attributes)
    print(header)
    print("-" * len(header))
    for obj in ctx.objects:
        row = f"{obj:>8}  "
        for attr in attributes:
            row += f"{'X':>8}" if ctx.has_attribute(obj, attr) else f"{'.':>8}"
        print(row)

    # Build concept lattice
    lattice = build_concept_lattice(ctx)

    print(f"\nFormal Concepts ({len(lattice)} found):")
    print("-" * 65)
    for i, concept in enumerate(lattice):
        objs = ", ".join(sorted(concept.extent))
        attrs = ", ".join(sorted(concept.intent))
        print(f"  C{i:02d}: Extent={{{objs}}}")
        print(f"       Intent={{{attrs}}}")

    # Attribute reduction
    print("\nAttribute Reduction:")
    print(f"  Original attributes: {attributes}")
    minimal = attribute_reduction(ctx)
    print(f"  Minimal attributes:  {minimal}")
    removed = set(attributes) - set(minimal)
    if removed:
        print(f"  Removable: {sorted(removed)}")
    else:
        print(f"  (All attributes are essential)")

    # Rule extraction from largest concept(s)
    print("\nExtracted Rules (from concepts with >= 2 attributes):")
    rule_count = 0
    for concept in lattice:
        rules = extract_rules(concept)
        if rules:
            print(f"\n  From concept (intent={{{', '.join(sorted(concept.intent))}}}):")
            for premise, conclusion in rules[:5]:  # show up to 5 per concept
                p = ", ".join(sorted(premise))
                c = ", ".join(sorted(conclusion))
                print(f"    IF {{{p}}} THEN {{{c}}}")
                rule_count += 1
            if len(rules) > 5:
                print(f"    ... and {len(rules) - 5} more rules")

    print(f"\n  Total rules extracted: {rule_count}")

    # Demonstrate a specific query
    print("\nQuery: Which cases share {contract_breach, strong_evidence}?")
    query = frozenset({"contract_breach", "strong_evidence"})
    matching = ctx.attribute_derivation(query)
    print(f"  Cases: {sorted(matching)}")

    common_attrs = ctx.object_derivation(matching)
    print(f"  Common attributes of those cases: {sorted(common_attrs)}")

    print("\nDemo completed successfully.")


if __name__ == "__main__":
    demo()
