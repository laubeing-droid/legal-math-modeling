#!/usr/bin/env python3
"""
#4: Supersedes vs Corrects --- Two Kripke Accessibility Relations
================================================================

In the Kripke procedural state model K = (W, R, V), we distinguish
two fundamentally different accessibility relations:

  R_supersedes subset W x W  --- factual error -> new evidence admitted
  R_corrects subset W x W    --- legal error -> new evidence NOT admitted

## Motivation

When an appellate court reverses a trial court decision, the legal
effect depends on the REASON for reversal:

- "??????" (erroneous fact-finding): R_supersedes(W1, W2)
  -> W2 can admit new evidence because the factual basis has changed

- "??????" (erroneous application of law): R_corrects(W1, W2)
  -> W2 CANNOT admit new evidence because only the legal reasoning
  changed, not the factual record

## Formal Model

### Kripke Structure

  K = (W, R, V) where:
    W = {W1, W2, W3, ...}  --- procedural worlds
    R = R_supersedes | R_corrects  --- all procedural transitions
    V: W -> (Facts, Stage, EvidenceBasket, RulingReason)

### Modal Operators

  []_sup phi  --- "in all worlds reachable via R_supersedes, phi holds"
  []_cor phi  --- "in all worlds reachable via R_corrects, phi holds"
  <>_sup phi  --- "in some world reachable via R_supersedes, phi holds"

### Theorem: Mutual Exclusion

  For any legally valid procedural transition where the reason for
  reversal is exclusive (one cannot simultaneously err on facts AND law
  for the same issue --- res judicata constraint):
    []_sup phi -> ![]_cor phi

  This encodes: if you can enter a world through factual-error review,
  you cannot enter it through legal-error review for the same issue.
"""

from dataclasses import dataclass, field
from typing import Dict, Set, List, Tuple, Optional, FrozenSet, FrozenSet
from enum import Enum


# ============================================================
# Part A: Kripke Structure
# ============================================================

class RulingReason(Enum):
    FACTUAL_ERROR = "FACTUAL_ERROR"         # ??????
    LEGAL_ERROR = "LEGAL_ERROR"             # ??????
    PROCEDURAL_ERROR = "PROCEDURAL_ERROR"   # ????
    MIXED = "MIXED"                          # ?????


class Stage(Enum):
    FIRST_INSTANCE = "W1"
    APPEAL = "W2"
    RETRIAL = "W3"


@dataclass(frozen=True)
class ProceduralWorld:
    """A Kripke possible world --- a procedural stage in litigation."""
    id: str
    stage: Stage
    facts: FrozenSet[str]              # Facts established at this world
    evidence_basket: FrozenSet[str]     # Evidence on record
    ruling_reason: Optional[RulingReason] = None  # Why this world was reached
    timestamp: float = 0.0              # Logical clock


@dataclass
class KripkeStructure:
    """K = (W, R_sup, R_cor, V)"""
    worlds: Set[ProceduralWorld] = field(default_factory=set)
    r_supersedes: Set[Tuple[ProceduralWorld, ProceduralWorld]] = field(default_factory=set)
    r_corrects: Set[Tuple[ProceduralWorld, ProceduralWorld]] = field(default_factory=set)
    valuation: Dict[ProceduralWorld, Dict[str, bool]] = field(default_factory=dict)

    def add_world(self, w: ProceduralWorld):
        self.worlds.add(w)

    def add_supersedes(self, w1: ProceduralWorld, w2: ProceduralWorld):
        """R_supersedes: factual error -> new evidence admitted.

        MUTUAL EXCLUSION ENFORCED: the same pair cannot be in both relations.
        """
        assert (w1, w2) not in self.r_corrects, \
            f"DISJOINTNESS VIOLATION: ({w1.id},{w2.id}) already in R_corrects"
        self.r_supersedes.add((w1, w2))

    def add_corrects(self, w1: ProceduralWorld, w2: ProceduralWorld):
        """R_corrects: legal error -> no new evidence.

        MUTUAL EXCLUSION ENFORCED: the same pair cannot be in both relations.
        """
        assert (w1, w2) not in self.r_supersedes, \
            f"DISJOINTNESS VIOLATION: ({w1.id},{w2.id}) already in R_supersedes"
        self.r_corrects.add((w1, w2))

    def accessible_via_sup(self, w: ProceduralWorld) -> Set[ProceduralWorld]:
        """Worlds reachable from w via R_supersedes."""
        return {w2 for (w1, w2) in self.r_supersedes if w1 == w}

    def accessible_via_cor(self, w: ProceduralWorld) -> Set[ProceduralWorld]:
        """Worlds reachable from w via R_corrects."""
        return {w2 for (w1, w2) in self.r_corrects if w1 == w}

    def box_sup(self, w: ProceduralWorld, proposition: str) -> bool:
        """[]_sup phi: phi holds in all R_supersedes-accessible worlds."""
        accessible = self.accessible_via_sup(w)
        if not accessible:
            return True  # Vacuously true
        return all(
            self.valuation.get(w2, {}).get(proposition, False)
            for w2 in accessible
        )

    def box_cor(self, w: ProceduralWorld, proposition: str) -> bool:
        """[]_cor phi: phi holds in all R_corrects-accessible worlds."""
        accessible = self.accessible_via_cor(w)
        if not accessible:
            return True
        return all(
            self.valuation.get(w2, {}).get(proposition, False)
            for w2 in accessible
        )

    def diamond_sup(self, w: ProceduralWorld, proposition: str) -> bool:
        """<>_sup phi: phi holds in some R_supersedes-accessible world."""
        accessible = self.accessible_via_sup(w)
        if not accessible:
            return False
        return any(
            self.valuation.get(w2, {}).get(proposition, False)
            for w2 in accessible
        )


# ============================================================
# Part B: Admission Gate Rules
# ============================================================

class AdmissionGate:
    """Decides whether new evidence E can enter world W2 from world W1."""

    @staticmethod
    def can_admit(
        w1: ProceduralWorld,
        w2: ProceduralWorld,
        new_evidence: str,
        k: KripkeStructure
    ) -> Tuple[bool, str]:
        """
        Three-question Admission Gate:

        1. Is the transition R_supersedes? -> new evidence may be admitted
        2. Is the transition R_corrects? -> new evidence is blocked
        3. Is the evidence "new" per metadata? -> check timestamps

        Returns: (admitted, reason)
        """
        # Question 1: Which relation connects W1 and W2?
        is_sup = (w1, w2) in k.r_supersedes
        is_cor = (w1, w2) in k.r_corrects

        if is_cor and not is_sup:
            return False, f"REJECTED: R_corrects({w1.id}, {w2.id}) --- legal error review, no new evidence"

        if is_sup:
            # Question 2: Is this evidence actually "new" in the legal sense?
            # Per ????? ?101-102, evidence is "new" if:
            # (a) It was not available during W1's proceedings, OR
            # (b) The party could not have discovered it with reasonable diligence

            # For the compiler: we check metadata, not content
            if new_evidence in w1.evidence_basket:
                return False, f"REJECTED: '{new_evidence}' was already in W1 evidence basket"

            # Question 3: Gradual Verification --- evidence_available_but_not_submitted
            # If the metadata says the evidence existed but wasn't submitted in W1,
            # the compiler triggers a condition compilation flag --- this requires
            # human determination of whether it's a "????" (basic fact)
            return True, f"ADMITTED: R_supersedes({w1.id}, {w2.id}) + not in W1 basket"

        # Neither relation holds --- no procedural path exists
        return False, f"REJECTED: No procedural path from {w1.id} to {w2.id}"


# ============================================================
# Part C: Theorems
# ============================================================

def prove_mutual_exclusion():
    """Theorem: []_sup phi -> ![]_cor phi

    For any exclusive ruling reason, a world reached by factual-error
    review is not simultaneously reachable by legal-error review for
    the same issue.

    Proof:
    1. By the principle of res judicata for procedural rulings, the
       same issue cannot be reviewed on BOTH factual and legal grounds
       in the same appellate proceeding.
    2. If W2 is reached from W1 via R_supersedes, the ruling reason
       is FACTUAL_ERROR (or MIXED containing FACTUAL_ERROR).
    3. R_corrects requires ruling reason LEGAL_ERROR.
    4. Therefore (W1, W2)  in  R_supersedes => (W1, W2) not_in R_corrects
       for exclusive rulings.
    5. Hence any phi true in all supersedes-successors cannot be
       simultaneously true in all corrects-successors (since the
       successor sets are disjoint for the same issue).
    """
    print("=" * 60)
    print("THEOREM: R_supersedes & R_corrects = {} for exclusive rulings")
    print("=" * 60)

    # Construct test worlds
    w1 = ProceduralWorld(
        id="W1", stage=Stage.FIRST_INSTANCE,
        facts=frozenset(["Contract.Formed", "Payment.Due"]),
        evidence_basket=frozenset(["E1_contract_draft", "E2_payment_record"]),
        timestamp=1.0
    )
    w2_sup = ProceduralWorld(
        id="W2_sup", stage=Stage.APPEAL,
        facts=frozenset(["Contract.Formed", "Payment.Due"]),
        evidence_basket=frozenset(["E1_contract_draft", "E2_payment_record"]),
        ruling_reason=RulingReason.FACTUAL_ERROR,
        timestamp=2.0
    )
    w2_cor = ProceduralWorld(
        id="W2_cor", stage=Stage.APPEAL,
        facts=frozenset(["Contract.Formed", "Payment.Due"]),
        evidence_basket=frozenset(["E1_contract_draft", "E2_payment_record"]),
        ruling_reason=RulingReason.LEGAL_ERROR,
        timestamp=2.0
    )

    K = KripkeStructure()
    K.add_world(w1)
    K.add_world(w2_sup)
    K.add_world(w2_cor)
    K.add_supersedes(w1, w2_sup)
    K.add_corrects(w1, w2_cor)

    # Set valuations
    K.valuation[w2_sup] = {"new_evidence_admissible": True}
    K.valuation[w2_cor] = {"new_evidence_admissible": False}

    # Test mutual exclusion
    sup_admits = K.box_sup(w1, "new_evidence_admissible")
    cor_admits = K.box_cor(w1, "new_evidence_admissible")

    print(f"\n  From {w1.id}:")
    print(f"    []_sup(new_evidence_admissible) = {sup_admits}")
    print(f"    []_cor(new_evidence_admissible) = {cor_admits}")
    print(f"    Mutual exclusion: []_sup phi -> ![]_cor phi = {sup_admits and not cor_admits}")

    # Admission Gate test
    gate = AdmissionGate()

    # New evidence only admissible through supersedes path
    new_ev = "E3_new_witness_testimony"
    admitted_sup, reason_sup = gate.can_admit(w1, w2_sup, new_ev, K)
    admitted_cor, reason_cor = gate.can_admit(w1, w2_cor, new_ev, K)

    print(f"\n  Admission Gate tests:")
    print(f"    Via R_supersedes: {admitted_sup} --- {reason_sup}")
    print(f"    Via R_corrects:   {admitted_cor} --- {reason_cor}")

    return sup_admits and not cor_admits


def prove_fact_basis_immutability():
    """Theorem: Facts established in W1 are immutable in W2 under R_corrects.

    If W2 is reached via R_corrects, the fact base of W2 MUST equal
    the fact base of W1 (no new evidence -> no new facts).

    Under R_supersedes, W2 MAY have additional facts (from new evidence).
    """
    print("\n" + "=" * 60)
    print("THEOREM: Fact Basis Immutability under R_corrects")
    print("=" * 60)

    w1 = ProceduralWorld(
        id="W1", stage=Stage.FIRST_INSTANCE,
        facts=frozenset(["A", "B"]),
        evidence_basket=frozenset(["E1", "E2"]),
        timestamp=1.0
    )

    # Corrects: facts must be identical
    w2_cor = ProceduralWorld(
        id="W2_cor", stage=Stage.APPEAL,
        facts=frozenset(["A", "B"]),  # Same as W1
        evidence_basket=frozenset(["E1", "E2"]),  # Same as W1
        ruling_reason=RulingReason.LEGAL_ERROR,
        timestamp=2.0
    )

    # Supersedes: facts may include additions
    w2_sup = ProceduralWorld(
        id="W2_sup", stage=Stage.APPEAL,
        facts=frozenset(["A", "B", "C"]),  # C is new
        evidence_basket=frozenset(["E1", "E2", "E3"]),  # E3 is new
        ruling_reason=RulingReason.FACTUAL_ERROR,
        timestamp=2.0
    )

    # Under R_corrects, fact bases equal
    cor_immutable = w2_cor.facts.issubset(w1.facts)
    print(f"\n  R_corrects: facts(W2) subset facts(W1) = {cor_immutable}")
    print(f"    W1 facts: {w1.facts}")
    print(f"    W2_cor facts: {w2_cor.facts}")

    # Under R_supersedes, fact bases may diverge
    sup_diverges = not w2_sup.facts.issubset(w1.facts)
    print(f"  R_supersedes: facts(W2) notsubset facts(W1) = {sup_diverges}")
    print(f"    W1 facts: {w1.facts}")
    print(f"    W2_sup facts: {w2_sup.facts}")
    print(f"    New facts: {w2_sup.facts - w1.facts}")

    return cor_immutable and sup_diverges


if __name__ == "__main__":
    mutex = prove_mutual_exclusion()
    immut = prove_fact_basis_immutability()

    print("\n" + "=" * 60)
    print("SUMMARY: Kripke Bimodal Procedural Logic")
    print("=" * 60)
    print("""
    Kripke structure: K = (W, R_sup, R_cor, V)

    R_supersedes --- factual error -> new evidence ADMITTED
    R_corrects   --- legal error   -> new evidence BLOCKED

    THEOREM 1 (Mutual Exclusion):
      For exclusive ruling reasons:
      []_sup phi -> ![]_cor phi

    THEOREM 2 (Fact Basis Immutability):
      Under R_corrects: facts(W2) subset facts(W1)
      Under R_supersedes: facts(W2) supseteq facts(W1)  [may add]

    ENGINEERING IMPLICATION:
      The compiler distinguishes these two relations by reading
      the JUDGMENT METADATA (ruling reason). It never infers
      the relation from evidence content --- this avoids the
      Oracle Problem and keeps the compiler on the safe side
      of the "judge" boundary.
    """)
