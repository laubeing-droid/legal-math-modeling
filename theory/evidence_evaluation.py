"""Evidence Evaluation: credibility scoring, chain-of-custody, and contradiction detection.

Mathematical Framework
---------------------
Evidence credibility is modelled as a product of three independent factors:

    S(e) = reliability(e) * independence(e) * authenticity(e)

where each factor lies in [0, 1].  The composite credibility score S(e) is
interpreted as the probability that the evidence faithfully represents the
fact it purports to prove.

Chain-of-custody completeness measures the fraction of required custody
transfer links that are documented:

    C_chain = documented_links / required_links

Contradiction detection uses a simple semantic-pair comparator: when two
evidence items assert incompatible propositions about the same fact, a
contradiction is flagged and both items' effective credibility is discounted.

This module reuses the credibility-axiom concept from
evidence_credibility_axioms.py but adds operational scoring, chain tracking,
and conflict resolution.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from typing import Dict, List, Optional, Set, Tuple


# ---------------------------------------------------------------------------
# Data structures
# ---------------------------------------------------------------------------

class EvidenceType(Enum):
    DOCUMENT = "document"
    TESTIMONY = "testimony"
    PHYSICAL = "physical"
    DIGITAL = "digital"
    EXPERT = "expert"


class ContradictionSeverity(Enum):
    MINOR = "minor"           # slight inconsistency, explainable
    MATERIAL = "material"     # one item must be wrong
    FATAL = "fatal"           # directly opposing core assertions


@dataclass
class CustodyLink:
    """One transfer in the chain of custody."""
    from_person: str
    to_person: str
    timestamp: str           # ISO format or free text
    documented: bool = True


@dataclass
class EvidenceItem:
    """A piece of evidence with credibility factors."""
    id: str
    description: str
    evidence_type: EvidenceType
    reliability: float       # [0, 1] — source trustworthiness
    independence: float      # [0, 1] — free from contamination / bias
    authenticity: float      # [0, 1] — genuineness
    asserted_fact: str       # what this evidence claims
    custody_chain: List[CustodyLink] = field(default_factory=list)
    required_custody_links: int = 1

    @property
    def credibility(self) -> float:
        return self.reliability * self.independence * self.authenticity

    @property
    def custody_completeness(self) -> float:
        if self.required_custody_links == 0:
            return 1.0
        documented = sum(1 for link in self.custody_chain if link.documented)
        return min(documented / self.required_custody_links, 1.0)

    @property
    def effective_score(self) -> float:
        return self.credibility * self.custody_completeness


@dataclass
class Contradiction:
    """Records a detected contradiction between two evidence items."""
    evidence_a: str
    evidence_b: str
    fact_a: str
    fact_b: str
    severity: ContradictionSeverity
    explanation: str


# ---------------------------------------------------------------------------
# Contradiction detection
# ---------------------------------------------------------------------------

# A simple keyword-based conflict map.  In production this would use NLI models.
_CONFLICT_PAIRS: List[Tuple[str, str]] = [
    ("present", "absent"),
    ("delivered", "not delivered"),
    ("not delivered", "delivered"),
    ("signed", "not signed"),
    ("not signed", "signed"),
    ("guilty", "innocent"),
    ("innocent", "guilty"),
    ("compliant", "non-compliant"),
    ("non-compliant", "compliant"),
    ("true", "false"),
    ("false", "true"),
    ("yes", "no"),
    ("no", "yes"),
]


def _contains_word_boundary(text: str, phrase: str) -> bool:
    """Check if phrase appears in text at word/phrase boundaries.

    Uses tokenization on whitespace and underscores to avoid substring false
    positives while handling legal identifiers like 'contract_signed',
    'not_signed' consistently.  Hyphens are preserved as part of compound
    tokens so that 'non-compliant' does not falsely match 'compliant'.

    'unsigned' is a single token and will NOT match 'signed'.
    'contract_signed' splits to ['contract', 'signed'] and WILL match 'signed'.
    'not_signed' splits to ['not', 'signed'] and will match 'not signed'.
    'non-compliant' stays as one token and will NOT match 'compliant'.
    """
    import re
    # Tokenize on whitespace and underscores (NOT hyphens)
    tokens = re.split(r'[\s_]+', text.lower())
    phrase_tokens = re.split(r'[\s_]+', phrase.lower())
    if len(phrase_tokens) == 1:
        # Single word: set membership
        return phrase_tokens[0] in tokens
    # Multi-word: contiguous sequence check (order-preserving)
    n = len(phrase_tokens)
    return any(tokens[i:i + n] == phrase_tokens for i in range(len(tokens) - n + 1))


def detect_contradiction(a: EvidenceItem, b: EvidenceItem) -> Optional[Contradiction]:
    """Detect whether two evidence items contradict each other.

    Uses word-boundary matching against known conflict pairs to avoid
    false positives from substring matching (e.g., 'signed' in 'unsigned').
    Returns None if no contradiction is detected.
    """
    fa = a.asserted_fact.lower()
    fb = b.asserted_fact.lower()

    for pos, neg in _CONFLICT_PAIRS:
        # Check: one asserts positive, the other asserts negative
        if _contains_word_boundary(fa, pos) and _contains_word_boundary(fb, neg):
            return Contradiction(
                evidence_a=a.id,
                evidence_b=b.id,
                fact_a=a.asserted_fact,
                fact_b=b.asserted_fact,
                severity=ContradictionSeverity.MATERIAL,
                explanation=(
                    f"'{a.id}' asserts '{a.asserted_fact}' while "
                    f"'{b.id}' asserts '{b.asserted_fact}'."
                ),
            )
        if _contains_word_boundary(fa, neg) and _contains_word_boundary(fb, pos):
            return Contradiction(
                evidence_a=a.id,
                evidence_b=b.id,
                fact_a=a.asserted_fact,
                fact_b=b.asserted_fact,
                severity=ContradictionSeverity.MATERIAL,
                explanation=(
                    f"'{a.id}' asserts '{a.asserted_fact}' while "
                    f"'{b.id}' asserts '{b.asserted_fact}'."
                ),
            )
    return None


# ---------------------------------------------------------------------------
# Evidence collection evaluation
# ---------------------------------------------------------------------------

@dataclass
class EvidenceEvaluation:
    """Evaluates a collection of evidence items."""
    items: List[EvidenceItem]
    contradictions: List[Contradiction] = field(default_factory=list)
    penalties: Dict[str, float] = field(default_factory=dict)

    def run(self) -> None:
        """Detect all pairwise contradictions and compute penalties."""
        self.contradictions.clear()
        self.penalties.clear()
        n = len(self.items)
        for i in range(n):
            for j in range(i + 1, n):
                c = detect_contradiction(self.items[i], self.items[j])
                if c is not None:
                    self.contradictions.append(c)
                    # Apply a 30% credibility discount to both conflicting items
                    self.penalties.setdefault(self.items[i].id, 0.30)
                    self.penalties.setdefault(self.items[j].id, 0.30)

    def adjusted_score(self, item: EvidenceItem) -> float:
        penalty = self.penalties.get(item.id, 0.0)
        return item.effective_score * (1 - penalty)

    def summary(self) -> List[Dict]:
        self.run()
        rows = []
        for item in self.items:
            rows.append({
                "id": item.id,
                "type": item.evidence_type.value,
                "credibility": round(item.credibility, 4),
                "custody": round(item.custody_completeness, 4),
                "effective": round(item.effective_score, 4),
                "penalty": self.penalties.get(item.id, 0.0),
                "adjusted": round(self.adjusted_score(item), 4),
            })
        return rows


# ---------------------------------------------------------------------------
# Demo
# ---------------------------------------------------------------------------

def demo() -> None:
    print("=" * 70)
    print("Evidence Evaluation — Demo")
    print("=" * 70)

    items = [
        EvidenceItem(
            id="E1",
            description="Signed delivery receipt",
            evidence_type=EvidenceType.DOCUMENT,
            reliability=0.95,
            independence=0.90,
            authenticity=0.98,
            asserted_fact="Package was delivered on 2025-03-01",
            custody_chain=[
                CustodyLink("warehouse_clerk", "plaintiff_counsel", "2025-03-02"),
            ],
            required_custody_links=1,
        ),
        EvidenceItem(
            id="E2",
            description="Defendant's email claiming non-delivery",
            evidence_type=EvidenceType.DIGITAL,
            reliability=0.88,
            independence=0.85,
            authenticity=0.92,
            asserted_fact="Package was not delivered on 2025-03-01",
            custody_chain=[
                CustodyLink("email_server", "defendant_counsel", "2025-03-05"),
            ],
            required_custody_links=1,
        ),
        EvidenceItem(
            id="E3",
            description="GPS tracking log",
            evidence_type=EvidenceType.DIGITAL,
            reliability=0.97,
            independence=0.99,
            authenticity=0.95,
            asserted_fact="Package was delivered on 2025-03-01",
            custody_chain=[
                CustodyLink("logistics_provider", "plaintiff_counsel", "2025-03-03"),
            ],
            required_custody_links=1,
        ),
        EvidenceItem(
            id="E4",
            description="Warehouse inventory record",
            evidence_type=EvidenceType.DOCUMENT,
            reliability=0.80,
            independence=0.70,
            authenticity=0.85,
            asserted_fact="Package left warehouse on 2025-02-28",
            custody_chain=[
                CustodyLink("warehouse_mgr", "forensic_analyst", "2025-03-10"),
                CustodyLink("forensic_analyst", "plaintiff_counsel", "2025-03-12"),
            ],
            required_custody_links=2,
        ),
    ]

    ev = EvidenceEvaluation(items=items)
    ev.run()

    print("\nEvidence Scores:")
    print("-" * 70)
    print(f"{'ID':<5} {'Type':<12} {'Credib.':>8} {'Custody':>8} "
          f"{'Effect.':>8} {'Penalty':>8} {'Adjusted':>9}")
    print("-" * 70)
    for row in ev.summary():
        print(
            f"{row['id']:<5} {row['type']:<12} {row['credibility']:>8.4f} "
            f"{row['custody']:>8.4f} {row['effective']:>8.4f} "
            f"{row['penalty']:>8.2f} {row['adjusted']:>9.4f}"
        )

    print(f"\nContradictions detected: {len(ev.contradictions)}")
    for c in ev.contradictions:
        print(f"  [{c.severity.value.upper()}] {c.explanation}")

    print("\nDemo completed successfully.")


# ---------------------------------------------------------------------------
# Inference chain checking (Horn forward chaining)
# ---------------------------------------------------------------------------

@dataclass
class HornRule:
    """A Horn rule: if all premises hold, derive the conclusion."""
    premises: List[str]
    conclusion: str
    name: str = ""


def check_inference_chain(
    facts: List[str],
    rules: List[HornRule],
) -> Dict:
    """Simulate Horn forward chaining from given facts.

    Starting from the initial fact atoms, repeatedly fire every rule whose
    premises are all satisfied until no new facts can be derived (fixpoint).

    Parameters
    ----------
    facts : list[str]
        Initial fact atoms (strings).
    rules : list[HornRule]
        Rules to apply.

    Returns
    -------
    dict with keys:
        complete : bool
            True if every rule's conclusion is eventually reachable.
        reachable : set[str]
            All facts derivable (including the initial ones).
        missing_links : list[str]
            Names (or indices) of rules whose premises are never fully
            satisfied during the derivation.
        chain_depth : int
            Maximum derivation depth (longest shortest proof path).
    """
    reachable: Set[str] = set(facts)
    # depth[fact] = derivation depth (0 for initial facts)
    depth: Dict[str, int] = {f: 0 for f in facts}
    missing_links: List[str] = []
    changed = True

    while changed:
        changed = False
        for rule in rules:
            if rule.conclusion in reachable:
                continue  # already derived
            if all(p in reachable for p in rule.premises):
                # fire this rule
                if rule.premises:
                    max_premise_depth = max(depth.get(p, 0) for p in rule.premises)
                else:
                    max_premise_depth = 0  # axiom/fact with no premises
                depth[rule.conclusion] = max_premise_depth + 1
                reachable.add(rule.conclusion)
                changed = True

    # Check which rules never fired
    for rule in rules:
        if rule.conclusion not in reachable:
            label = rule.name if rule.name else f"Rule({rule.premises} -> {rule.conclusion})"
            missing_links.append(label)

    chain_depth = max(depth.values()) if depth else 0
    complete = len(missing_links) == 0

    return {
        "complete": complete,
        "reachable": reachable,
        "missing_links": missing_links,
        "chain_depth": chain_depth,
    }


def demo_inference_chain() -> None:
    """Demo: check inference chain completeness for a contract breach case."""
    print("=" * 70)
    print("Inference Chain Checking — Contract Breach Demo")
    print("=" * 70)

    # Facts established by evidence
    facts = [
        "contract_signed",
        "payment_due_date_passed",
        "defendant_received_notice",
        "goods_inspection_failed",
        "defendant_did_not_cure",
    ]

    # Legal inference rules (Horn clauses)
    rules = [
        HornRule(
            premises=["contract_signed", "payment_due_date_passed"],
            conclusion="breach_of_payment",
            name="payment_breach_rule",
        ),
        HornRule(
            premises=["contract_signed", "goods_inspection_failed"],
            conclusion="breach_of_warranty",
            name="warranty_breach_rule",
        ),
        HornRule(
            premises=["breach_of_payment", "defendant_received_notice"],
            conclusion="material_breach_established",
            name="material_breach_rule",
        ),
        HornRule(
            premises=["breach_of_warranty", "defendant_did_not_cure"],
            conclusion="uncured_warranty_breach",
            name="uncured_warranty_rule",
        ),
        HornRule(
            premises=["material_breach_established", "uncured_warranty_breach"],
            conclusion="contract_terminable",
            name="termination_rule",
        ),
        HornRule(
            premises=["contract_terminable"],
            conclusion="damages_recoverable",
            name="damages_rule",
        ),
        # This rule's premise cannot be satisfied from the given facts
        HornRule(
            premises=["fraud_proven"],
            conclusion="punitive_damages_available",
            name="fraud_punitive_rule",
        ),
    ]

    result = check_inference_chain(facts, rules)

    print(f"\nInitial facts ({len(facts)}):")
    for f in facts:
        print(f"  + {f}")

    print(f"\nRules ({len(rules)}):")
    for r in rules:
        print(f"  {r.name}: {r.premises} -> {r.conclusion}")

    print(f"\nResults:")
    print(f"  Complete (all rules fire): {result['complete']}")
    print(f"  Chain depth:              {result['chain_depth']}")
    print(f"  Derived facts ({len(result['reachable']) - len(facts)} new):")
    for f in sorted(result['reachable']):
        marker = "+" if f not in facts else " "
        print(f"    {marker} {f}")

    if result['missing_links']:
        print(f"\n  Missing links ({len(result['missing_links'])}):")
        for ml in result['missing_links']:
            print(f"    - {ml}")
    else:
        print("\n  No missing links — full inference chain is derivable.")

    print("\nDemo completed successfully.")


if __name__ == "__main__":
    demo()
    print()


# ---------------------------------------------------------------------------
# Temporal integration (F1)
# ---------------------------------------------------------------------------

def check_inference_chain_with_temporal(
    facts: List[str],
    rules: List[HornRule],
    fact_date=None,
    current_date=None,
) -> Dict:
    """Horn forward chaining with temporal filtering.

    If fact_date and current_date are provided, filters rules by
    temporal applicability before inference:
    - Substantive law: filtered by fact_date (实体从旧)
    - Procedural law: filtered by current_date (程序从新)

    Falls back to check_inference_chain if dates not provided.
    """
    if fact_date is None or current_date is None:
        return check_inference_chain(facts, rules)

    try:
        from theory.temporal_integration import TemporalFilter
        from theory.argumentation_horn_unification import HornRule as AafHornRule

        tf = TemporalFilter()
        # Convert evidence HornRule to AafHornRule for temporal filter
        for i, rule in enumerate(rules):
            aaf_rule = AafHornRule(
                id=rule.name or f"rule_{i}",
                premises=rule.premises,
                head=rule.conclusion,
                exceptions=[],
            )
            tf.add_rule(aaf_rule, effective_date=fact_date)

        # Filter by temporal applicability
        applicable = tf.filter_rules(current_date)
        applicable_ids = {r.id for r in applicable}

        # Filter original rules
        filtered = [
            r for i, r in enumerate(rules)
            if (r.name or f"rule_{i}") in applicable_ids
        ]

        result = check_inference_chain(facts, filtered)
        result["temporal_filtered"] = True
        result["original_rule_count"] = len(rules)
        result["applicable_rule_count"] = len(filtered)
        return result
    except ImportError:
        # temporal_integration not available, fall back
        return check_inference_chain(facts, rules)
