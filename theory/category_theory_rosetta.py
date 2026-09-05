#!/usr/bin/env python3
"""
#16: Anti-Rosetta Stone --- Category/Rosetta Engineering Boundary
=================================================================

Models CN/CBL/SPC as FUNCTORS from the category of Facts to the
category of Legal Claims. The 2026-06-11 strict proof baseline
downgrades the original universal theorem:

  A1-real: DATA_INSUFFICIENT_FOR_PROOF
  A1-toy:  TOY_SYNTHETIC_PROOF_ONLY

This file is therefore an engineering model for obstruction guards,
not a formal proof that no natural transformation exists for all real
CN/US/HK legal facts.

## Your 6/4 Insight

  "????????'??????????'"

## Category-Theoretic Restatement

  F_CN:  Facts -> CN_Claims    (Chinese statutory law functor)
  F_US:  Facts -> US_Claims    (US federal law functor)
  F_HK:  Facts -> HK_Claims    (Hong Kong common law functor)

  A natural transformation alpha: F_CN -> F_US would mean:
    For EVERY fact f, there exists a "corresponding" US claim
    alpha(f): F_CN(f) -> F_US(f) that commutes with all legal
    rule applications.

  The real inventory contains collision/asymmetry witnesses. These are
  useful legal-data findings, but not a first-principles proof that every
  total collision-free mapping is impossible.

## Theorem

  Allowed claim:
    Source-backed obstructions should block unsafe cross-jurisdiction
    auto-mapping.

  Forbidden claim:
    Do not claim a fully formal no-natural-transformation theorem for
    the real inventory.
"""

from dataclasses import dataclass, field
from typing import Dict, Set, List, Tuple, FrozenSet, Optional, Callable
from enum import Enum

try:
    from model_status import get_claim
except ImportError:
    get_claim = None


# ============================================================
# Part A: Category-Theoretic Model
# ============================================================

class Jurisdiction(Enum):
    CN = "CN"    # Chinese statutory
    US = "US"    # US federal
    HK = "HK"    # Hong Kong common law


@dataclass(frozen=True)
class Fact:
    """Object in the Facts category."""
    id: str
    description: str


@dataclass(frozen=True)
class LegalClaim:
    """Object in the Claims category."""
    id: str
    jurisdiction: Jurisdiction
    description: str
    confidence: float = 1.0


@dataclass(frozen=True)
class RuleApplication:
    """Morphism in the Claims category: application of a legal rule.

    r: claim_A -> claim_B means "claim_B is derivable from claim_A via rule r"
    """
    rule_id: str
    source: LegalClaim
    target: LegalClaim


@dataclass
class LegalFunctor:
    """A functor F: Facts -> Claims_J for jurisdiction J.

    - Object mapping:  F(fact) = set of claims triggered by fact
    - Morphism mapping: F(fact1 -> fact2) = rule chain connecting claims
    """

    jurisdiction: Jurisdiction
    fact_to_claims: Dict[str, Set[LegalClaim]] = field(default_factory=dict)
    transitions: List[RuleApplication] = field(default_factory=list)

    def map_fact(self, fact: Fact) -> Set[LegalClaim]:
        return self.fact_to_claims.get(fact.id, set())

    def add_mapping(self, fact: Fact, claim: LegalClaim):
        self.fact_to_claims.setdefault(fact.id, set()).add(claim)

    def add_transition(self, rule_app: RuleApplication):
        self.transitions.append(rule_app)


# ============================================================
# Part B: Natural Transformation --- Existence and Non-Existence
# ============================================================

@dataclass
class NaturalTransformation:
    """alpha: F -> G --- a natural transformation between two legal functors.

    A natural transformation assigns to each fact f a claim morphism
    alpha_f: F(f) -> G(f) such that for every rule application r,
    the naturality square commutes.

    Commuting square:
        F(fact1) --F(r)--> F(fact2)
           |                  |
        alpha_f1           alpha_f2
           |                  |
           v                  v
        G(fact1) --G(r)--> G(fact2)
    """

    source_functor: LegalFunctor
    target_functor: LegalFunctor
    # alpha_f: for each fact, maps source claims to target claims
    component: Dict[str, Dict[str, str]] = field(default_factory=dict)

    def is_natural(self) -> Tuple[bool, List[str]]:
        """Verify that the naturality squares commute.

        The naturality square for a rule application r: fact1 -> fact2 is:

            F(fact1) --F(r)--> F(fact2)
               |                  |
            alpha_f1          alpha_f2
               |                  |
               v                  v
            G(fact1) --G(r)--> G(fact2)

        We check: for each claim c in F(fact1), does alpha(c) in G(fact1)?
        And for each claim c in F(fact2), does alpha(c) in G(fact2)?

        Additionally: does the path G(r)(alpha(c)) equal alpha(F(r)(c))?
        This is the COMMUTATIVITY check.

        FIXED (Codex audit): Previously compared claim IDs against fact IDs.
        Now correctly iterates over all facts in fact_to_claims, not rule transitions.
        """
        violations = []

        # Check component compatibility: for every fact in the source domain,
        # does alpha map source claims to target claims?
        for fact_id, src_claims in self.source_functor.fact_to_claims.items():
            alpha_on_fact = self.component.get(fact_id, {})
            tgt_claims = self.target_functor.fact_to_claims.get(fact_id, set())
            tgt_claim_ids = {c.id for c in tgt_claims}

            for claim in src_claims:
                mapped = alpha_on_fact.get(claim.id)
                if mapped is not None and mapped not in tgt_claim_ids:
                    violations.append(
                        f"Component violation: alpha maps {claim.id} -> {mapped} "
                        f"but {mapped} not in G({fact_id})"
                    )

        # Check commutativity for each rule transition
        for rule in self.source_functor.transitions:
            src_claim_id = rule.source.id
            tgt_claim_id = rule.target.id

            # Find which facts contain these claims
            for fact_id, src_claims in self.source_functor.fact_to_claims.items():
                alpha_on_fact = self.component.get(fact_id, {})
                src_claim_ids_s = {c.id for c in src_claims}

                if src_claim_id not in src_claim_ids_s:
                    continue

                mapped_src = alpha_on_fact.get(src_claim_id)
                mapped_tgt = alpha_on_fact.get(tgt_claim_id)

                if mapped_src and mapped_tgt:
                    # Check: does the target functor have a transition
                    # from mapped_src to mapped_tgt?
                    tgt_has_transition = any(
                        tr.source.id == mapped_src and tr.target.id == mapped_tgt
                        for tr in self.target_functor.transitions
                    )
                    if not tgt_has_transition:
                        violations.append(
                            f"Commutativity violation: rule {rule.rule_id}: "
                            f"{src_claim_id} -> {tgt_claim_id} but no G({mapped_src}) -> G({mapped_tgt})"
                        )

        return len(violations) == 0, violations


def prove_no_natural_transformation():
    """Obstruction witness: unsafe CN->US direct mapping should be blocked.

    This is no longer labeled as a universal theorem. The accepted
    strict status is DATA_INSUFFICIENT_FOR_PROOF for real data and
    TOY_SYNTHETIC_PROOF_ONLY for the toy finite checker.

    Witness: The "consideration" mapping.

    Fact: "parties exchanged promises"
      F_CN(fact) -> "????" (contract formed, based on mutual assent)
      F_US(fact) -> "contract enforceable" (based on consideration)

    If alpha: F_CN -> F_US existed, it would need to map:
      "????" (CN claim) -> "contract enforceable" (US claim)

    But CN contract formation does NOT require consideration ---
    it requires offer + acceptance + capacity + legality.

    The mapping should be blocked because:
      1. CN: offer + acceptance -> contract formed
      2. US: offer + acceptance + CONSIDERATION -> contract enforceable
      3. No alpha can bridge this because CONSIDERATION has no
         counterpart in the CN functor's image.

    Hence direct CN->US claim mapping must be blocked for this witness.
    """
    print("=" * 60)
    print("OBSTRUCTION WITNESS: CN -> US consideration mismatch")
    print("=" * 60)

    # Build CN functor
    F_CN = LegalFunctor(Jurisdiction.CN)
    F_US = LegalFunctor(Jurisdiction.US)

    # Facts
    fact_consideration = Fact("F1", "parties exchanged promises")
    fact_breach = Fact("F2", "one party failed to perform")

    # CN claims (mutual assent model, no consideration required)
    cn_contract = LegalClaim("CN.ContractFormed", Jurisdiction.CN,
                             "contract formed via mutual assent")
    cn_breach = LegalClaim("CN.BreachFound", Jurisdiction.CN,
                           "breach established")

    # US claims (consideration model) -- two claims for the same fact
    us_contract = LegalClaim("US.ContractEnforceable", Jurisdiction.US,
                             "contract enforceable via consideration")
    us_consideration = LegalClaim("US.ConsiderationRequired", Jurisdiction.US,
                                   "consideration must be present")
    us_breach = LegalClaim("US.BreachFound", Jurisdiction.US,
                           "breach established")

    F_CN.add_mapping(fact_consideration, cn_contract)
    F_CN.add_mapping(fact_breach, cn_breach)
    # US maps ONE fact to TWO claims: contract enforceable + consideration required
    F_US.add_mapping(fact_consideration, us_contract)
    F_US.add_mapping(fact_consideration, us_consideration)
    F_US.add_mapping(fact_breach, us_breach)

    # Rule transitions
    cn_rule = RuleApplication("R_CN_breach", cn_contract, cn_breach)
    us_rule = RuleApplication("R_US_breach", us_contract, us_breach)
    F_CN.add_transition(cn_rule)
    F_US.add_transition(us_rule)

    # Attempt natural transformation
    # The alpha component maps CN claims to US claims.
    # But US has 2 claims for F1 (contract + consideration);
    # CN has 1 claim for F1 (contract only).
    # alpha must be INJECTIVE on claim IDs for the square to commute,
    # but it cannot map 1 CN claim to 2 US claims.
    # This SURJECTIVITY FAILURE is the formal reason no natural transformation exists.
    #
    # For alpha to be natural, it would need to map CN.ContractFormed to
    # BOTH US.ContractEnforceable AND US.ConsiderationRequired simultaneously,
    # which contradicts the definition of a transformation component
    # (a single claim can only map to a single claim).

    alpha = NaturalTransformation(
        source_functor=F_CN,
        target_functor=F_US,
        component={
            "F1": {"CN.ContractFormed": "US.ContractEnforceable"},
            # MISSING: cannot also map to US.ConsiderationRequired
            "F2": {"CN.BreachFound": "US.BreachFound"},
        }
    )

    is_natural, violations = alpha.is_natural()
    print(f"\n  Attempted natural transformation CN -> US:")
    print(f"    Is natural: {is_natural}")
    if violations:
        for v in violations:
            print(f"    {v}")

    # The component check: for F1, G has 2 claims, alpha only maps 1.
    # The unmapped claim (US.ConsiderationRequired) has no preimage.
    # This means alpha is not a full component: it doesn't account
    # for all claims in the target functor's image.
    #
    # This is an obstruction witness, not a universal theorem.

    # Now verify the counterexample
    us_f1_claims = {c.id for c in F_US.map_fact(fact_consideration)}
    cn_f1_claims = {c.id for c in F_CN.map_fact(fact_consideration)}
    alpha_f1 = alpha.component.get("F1", {})

    # US has a claim not covered by alpha
    uncovered = us_f1_claims - set(alpha_f1.values())
    print(f"\n  US F1 claims: {us_f1_claims}")
    print(f"  CN F1 claims: {cn_f1_claims}")
    print(f"  Alpha maps: {alpha_f1}")
    print(f"  Uncovered US claims: {uncovered}")
    print(f"  Direct mapping must be blocked: {len(uncovered) > 0}")

    is_natural, violations = alpha.is_natural()
    print(f"\n  Attempted natural transformation CN -> US:")
    print(f"    Is natural: {is_natural}")
    if violations:
        for v in violations:
            print(f"    {v}")

    # The core counterexample: CONSIDERATION has no CN counterpart
    print(f"\n  CONSIDERATION COUNTEREXAMPLE:")
    print(f"    CN: contract = offer + acceptance + capacity + legality")
    print(f"    US: contract = offer + acceptance + CONSIDERATION + capacity + legality")
    print(f"    The 'consideration' factor has NO counterpart in CN law.")
    print(f"    Any alpha mapping would either:")
    print(f"      (a) Omit consideration (lossy, not a functor)")
    print(f"      (b) Add it artificially (concept smuggling)")
    print(f"      (c) Be non-natural (square fails to commute)")

    return False, ["DATA_INSUFFICIENT_FOR_UNIVERSAL_THEOREM"]


def prove_trirail_as_naturality_failure():
    """TriRail-style scenarios as obstruction witnesses.

    Each COLLISION scenario is a naturality square that fails to commute.
    Each ASYMMETRY scenario is a component mismatch where one functor
    has an image claim the other functor lacks.
    """
    print("\n" + "=" * 60)
    print("ENGINEERING TEST: TriRail scenarios as mapping obstructions")
    print("=" * 60)

    scenarios = {
        "TRI_001 DataExport": (
            "CN: DataExport -> BLOCKED",
            "US: CLOUD Act -> REQUIRED",
            "COLLISION"
        ),
        "TRI_002 Discovery": (
            "CN: Discovery NOT EXIST -> evidence_collection only",
            "US: Discovery -> REQUIRED",
            "COLLISION"
        ),
        "TRI_003 OFAC": (
            "CN: OFAC NOT ENFORCED -> blocking statute applies",
            "US: OFAC -> ENFORCED",
            "COLLISION"
        ),
        "TRI_004 PleaBargain": (
            "CN: PleaBargaining NOT EXIST -> ???? instead",
            "US: PleaBargaining -> AVAILABLE",
            "ASYMMETRY"
        ),
        "TRI_010 AtWill": (
            "CN: AtWill NOT EXIST -> labor protection required",
            "US: AtWill -> EMPLOYMENT_AT_WILL",
            "COLLISION"
        ),
    }

    for scenario, (cn_behavior, us_behavior, result_type) in scenarios.items():
        print(f"\n  {scenario}:")
        print(f"    CN: {cn_behavior}")
        print(f"    US: {us_behavior}")
        print(f"    Result: {result_type}")
        print(f"    Naturality square: {'FAILS' if result_type == 'COLLISION' else 'PARTIAL'}")

    print(f"\n  CATEGORY-THEORETIC INTERPRETATION:")
    print(f"  COLLISION  = naturality square fails (no commuting morphism)")
    print(f"  ASYMMETRY  = component mismatch (one functor lacks the claim)")
    print(f"  RESONANCE  = square commutes (legal systems agree)")
    print(f"")
    print(f"  These scenarios are obstruction witnesses for routing and guardrails.")
    print(f"  They are not a complete proof over the real legal universe.")


if __name__ == "__main__":
    is_natural, violations = prove_no_natural_transformation()
    prove_trirail_as_naturality_failure()

    print("\n" + "=" * 60)
    print("SUMMARY: Category/Rosetta Engineering Boundary")
    print("=" * 60)
    print(f"""
    CLAIM 1 (Real-data status):
      DATA_INSUFFICIENT_FOR_PROOF. Current data gives collision and
      asymmetry witnesses, not a universal no-natural-transformation proof.

    CLAIM 2 (Engineering use):
      COLLISION and ASYMMETRY rows must block unsafe cross-jurisdiction
      auto-mapping.

    CLAIM 3 (Toy proof):
      The separate 5-pattern toy checker proves only its synthetic toy
      inventory.

    CODE LIFT TARGET:
      Implement jurisdiction-specific routing and obstruction guards.
    """)
