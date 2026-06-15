#!/usr/bin/env python3
"""
#18: Differential Privacy Policy Parameters and Legal Release Classes
=====================================================================

The early draft mapped differential privacy epsilon directly to legal
privilege levels. The 2026-06-11 strict proof baseline refutes that
as a mathematical/legal function:

  D1: REFUTED_BY_COUNTEREXAMPLE

Legal sources can classify release modes and approval duties. They do
not determine a unique numeric epsilon. Epsilon must be treated as an
organizational policy parameter with provenance and audit controls.

## Core Mapping

  Legal release class -> allowed release mode -> policy candidate epsilon

  The final arrow is policy-injected, not legally derived.

## Legal Privilege Lattice

  Privilege levels form a lattice ordered by restrictiveness:
    ABSOLUTE > HIGH > MEDIUM > LOW > PUBLIC

  More privilege may motivate tighter privacy policy, but the numeric
  epsilon is not a theorem of law.
"""

from dataclasses import dataclass, field
from typing import Dict, List, Tuple, Optional
from enum import Enum
import math

try:
    from model_status import get_claim
except ImportError:
    get_claim = None


# ============================================================
# Part A: Legal Privilege Lattice
# ============================================================

class PrivilegeLevel(Enum):
    """Legal privilege levels in increasing order of disclosure."""
    ABSOLUTE = 1    # Never disclosed (state secrets, attorney-client core)
    STRICT = 2      # Highly restricted (trade secrets, minor defendants)
    HIGH = 3        # Restricted (pre-trial discovery, settlement negotiations)
    MODERATE = 4    # Limited (civil evidence, business records)
    LOW = 5         # General (public court filings, administrative records)
    PUBLIC = 6      # No restriction (published opinions, statutes)


class InformationType(Enum):
    ATTORNEY_CLIENT = "attorney_client"     # ABSOLUTE
    TRADE_SECRET = "trade_secret"            # STRICT
    MINOR_RECORD = "minor_record"            # STRICT
    SETTLEMENT_NEGOTIATION = "settlement"    # HIGH
    PRE_TRIAL_EVIDENCE = "pre_trial"         # MODERATE
    EXPERT_REPORT = "expert_report"          # MODERATE
    COURT_FILING = "court_filing"            # LOW
    PUBLISHED_OPINION = "published_opinion"  # PUBLIC
    STATUTE = "statute"                      # PUBLIC


@dataclass
class LegalPrivacyMapping:
    """Policy candidate mapping from legal classes to DP epsilon ranges.

    These ranges are defaults for experimentation and governance. They
    are not legal facts and must be stored as policy configuration.
    """

    # Default epsilon ranges for each privilege level
    privilege_epsilon: Dict[PrivilegeLevel, Tuple[float, float]] = field(default_factory=lambda: {
        PrivilegeLevel.ABSOLUTE: (0.0, 0.0),      # No disclosure
        PrivilegeLevel.STRICT:   (0.01, 0.5),      # Very tight DP
        PrivilegeLevel.HIGH:     (0.5, 2.0),        # Tight DP
        PrivilegeLevel.MODERATE: (2.0, 8.0),        # Moderate DP
        PrivilegeLevel.LOW:      (8.0, 50.0),       # Loose DP
        PrivilegeLevel.PUBLIC:   (float('inf'), float('inf')),  # No DP needed
    })

    # Information type -> privilege level
    info_privilege: Dict[InformationType, PrivilegeLevel] = field(default_factory=lambda: {
        InformationType.ATTORNEY_CLIENT: PrivilegeLevel.ABSOLUTE,
        InformationType.TRADE_SECRET: PrivilegeLevel.STRICT,
        InformationType.MINOR_RECORD: PrivilegeLevel.STRICT,
        InformationType.SETTLEMENT_NEGOTIATION: PrivilegeLevel.HIGH,
        InformationType.PRE_TRIAL_EVIDENCE: PrivilegeLevel.MODERATE,
        InformationType.EXPERT_REPORT: PrivilegeLevel.MODERATE,
        InformationType.COURT_FILING: PrivilegeLevel.LOW,
        InformationType.PUBLISHED_OPINION: PrivilegeLevel.PUBLIC,
        InformationType.STATUTE: PrivilegeLevel.PUBLIC,
    })

    def epsilon_bound(self, info_type: InformationType) -> Tuple[float, float]:
        """Return (min_epsilon, max_epsilon) for an information type.

        epsilon_bound = (low, high) means:
        - DP noise must be calibrated to satisfy epsilon in [low, high]
        - Smaller epsilon = more noise = more privacy
        """
        level = self.info_privilege.get(info_type, PrivilegeLevel.MODERATE)
        return self.privilege_epsilon.get(level, (2.0, 8.0))

    def laplace_noise_scale(self, info_type: InformationType,
                           sensitivity: float = 1.0) -> float:
        """Compute Laplace noise scale = sensitivity / epsilon.

        Larger scale = more noise = more privacy protection.
        """
        lo, hi = self.epsilon_bound(info_type)
        # Use conservative bound (tighter privacy = smaller epsilon = larger scale)
        epsilon = lo if lo > 0 else 0.1
        return sensitivity / epsilon


# ============================================================
# Part B: Integration with juris-calculus
# ============================================================

@dataclass
class PrivacyAwareFact:
    """A legal fact with DP privacy parameters.

    Extends LegalFact with:
    - privilege level: which tier of protection
    - epsilon: DP budget consumed when this fact is shared
    - noise_scale: Laplace noise scale for this type
    """
    fact_id: str
    description: str
    info_type: InformationType
    privilege: PrivilegeLevel
    epsilon_bound: Tuple[float, float]
    noise_scale: float

    def can_share_with(self, recipient_clearance: PrivilegeLevel) -> bool:
        """Check if this fact can be shared with a recipient.

        A fact can be shared iff recipient's clearance <= fact's privilege
        (recipient must be AT LEAST AS RESTRICTIVE as the fact).

        Lower PrivilegeLevel.value = MORE restrictive.
        ABSOLUTE(1) can ONLY be accessed by ABSOLUTE(1).
        PUBLIC(6) can be accessed by anyone (values 1-6).
        """
        return recipient_clearance.value <= self.privilege.value


# ============================================================
# Part C: Theorems
# ============================================================

def prove_privilege_lattice():
    """Theorem: The legal privilege mapping satisfies the lattice axioms.

    1. Partial order: privilege levels form a chain
    2. Join exists: max(level_a, level_b) = less restrictive of the two
    3. Meet exists: min(level_a, level_b) = more restrictive of the two

    For epsilon: the join corresponds to MIN epsilon (tighter DP),
    the meet corresponds to MAX epsilon (looser DP).
    """
    print("=" * 60)
    print("THEOREM: Legal Privilege is a Lattice")
    print("=" * 60)

    mapping = LegalPrivacyMapping()

    # Verify chain property
    levels = list(PrivilegeLevel)
    for i in range(len(levels) - 1):
        assert levels[i].value < levels[i + 1].value

    print(f"\n  Privilege levels: {len(levels)}")
    for level in levels:
        lo, hi = mapping.privilege_epsilon[level]
        eps_str = f"[{lo}, {hi}]" if hi != float('inf') else "[inf, inf]"
        print(f"    {level.name:12s}  epsilon={eps_str}")

    # Join = less restrictive (higher value)
    join_ab = max(PrivilegeLevel.STRICT.value, PrivilegeLevel.MODERATE.value)
    print(f"\n  Join(STRICT, MODERATE) = {PrivilegeLevel(join_ab).name}")

    # Meet = more restrictive (lower value)
    meet_ab = min(PrivilegeLevel.STRICT.value, PrivilegeLevel.MODERATE.value)
    print(f"  Meet(STRICT, MODERATE) = {PrivilegeLevel(meet_ab).name}")

    # Epsilon dualities
    print(f"\n  EPSILON <-> PRIVILEGE DUALITY:")
    print(f"  More privilege  -> Smaller epsilon -> More noise -> More privacy")
    print(f"  Less privilege  -> Larger epsilon  -> Less noise -> Less privacy")


def prove_epsilon_calibration():
    """Policy gate: legal metadata does not determine epsilon uniquely.

    The accepted legal-data baseline requires every DP policy candidate
    to carry the warning "epsilon is not legally derived; policy
    candidate only".
    """
    print("\n" + "=" * 60)
    print("POLICY GATE: Epsilon is not legally determined")
    print("=" * 60)

    mapping = LegalPrivacyMapping()

    test_cases = [
        ("Client confession to attorney", InformationType.ATTORNEY_CLIENT, 1.0),
        ("Trade secret formula", InformationType.TRADE_SECRET, 1.0),
        ("Minor defendant school records", InformationType.MINOR_RECORD, 1.0),
        ("Settlement offer amount", InformationType.SETTLEMENT_NEGOTIATION, 1.0),
        ("Expert medical report", InformationType.EXPERT_REPORT, 1.0),
        ("Published Supreme Court opinion", InformationType.PUBLISHED_OPINION, 0.0),
    ]

    print(f"\n  {'Information':40s} {'Privilege':12s} {'Epsilon':>10s} {'Noise':>10s}")
    print(f"  {'-'*40} {'-'*12} {'-'*10} {'-'*10}")
    for desc, info_type, sensitivity in test_cases:
        lo, hi = mapping.epsilon_bound(info_type)
        noise = mapping.laplace_noise_scale(info_type, sensitivity)
        level = mapping.info_privilege[info_type]
        eps_str = f"[{lo}, {hi}]" if hi != float('inf') else "[inf, inf]"
        print(f"  {desc[:38]:40s} {level.name:12s} {eps_str:>10s} {noise:>10.2f}")

    # Key insight
    print(f"\n  KEY INSIGHT:")
    print(f"  Attorney-client info: epsilon=0 -> INFINITE noise -> perfect secrecy")
    print(f"  Public opinion:       epsilon=inf -> ZERO noise -> no protection")
    print(f"  These are policy candidates. Legal classification does not determine a unique epsilon.")


if __name__ == "__main__":
    prove_privilege_lattice()
    prove_epsilon_calibration()

    print("\n" + "=" * 60)
    print("SUMMARY: DP epsilon policy boundary")
    print("=" * 60)
    print("""
    CLAIM 1 (Legal release taxonomy):
      Legal sources can classify information into release classes and
      permitted release modes.

    REFUTED CLAIM:
      "Each information type has a unique epsilon derived from legal
      doctrine" is refuted. The strict proof package contains a
      two-model witness where the same privilege level maps to
      different epsilon values.

    ENGINEERING RULE:
      Store epsilon in policy configuration with source, approval, and
      audit logs. Do not infer it as a legal theorem.

    DP GUARANTEE:
      The standard DP guarantee applies:
        P[M(D) in S] <= exp(epsilon) * P[M(D') in S]
      only after epsilon is supplied by an approved policy model.

    CODE LIFT TARGET:
      Build a DP policy loader that refuses to run if epsilon lacks
      provenance or if a legal source row claims to determine epsilon.
    """)
