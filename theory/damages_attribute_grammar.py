#!/usr/bin/env python3
"""
Damages Attribute Grammar (A14)

Formalizes legal damages computation as an attributed grammar where
each variable is a boolean guard computed by the k≤3 Horn engine.

Formula (PRC Civil Code Art. 584):
  Damages = min(ActualLoss + ExpectationInterest, ForeseeabilityLimit)
            × (1 - ContributoryNegligence)
            - FailureToMitigate

Each guard is True/False from the Horn engine:
  - ActualLoss > 0: engine confirms loss occurred
  - ExpectationInterest > 0: engine confirms lost profit
  - ForeseeabilityLimit: engine confirms foreseeability cap applies
  - ContributoryNegligence: engine confirms victim's fault
  - FailureToMitigate: engine confirms failure to mitigate

When a guard is False, its associated value is 0 (does not apply).
When a guard is True, the value is taken from the fact set.
"""
from __future__ import annotations
from dataclasses import dataclass, field
from typing import Dict, Optional
from enum import Enum


class GuardStatus(Enum):
    """Status of a boolean guard from the Horn engine."""
    ACTIVE = "ACTIVE"       # Guard triggered: value applies
    INACTIVE = "INACTIVE"   # Guard not triggered: value = 0
    TAINTED = "TAINTED"     # Guard at k≥4: value uncertain


@dataclass(frozen=True)
class DamageGuard:
    """A single variable in the damages formula, gated by Horn engine."""
    name: str
    status: GuardStatus
    value: float  # Only meaningful when status == ACTIVE
    rule_id: Optional[str] = None  # Which Horn rule fired this guard
    depth: int = 0  # Exception chain depth (k)

    @property
    def effective_value(self) -> float:
        """Return value if active, 0 otherwise."""
        if self.status == GuardStatus.ACTIVE:
            return self.value
        return 0.0


@dataclass
class DamagesComputation:
    """Full damages computation with all guards."""
    actual_loss: DamageGuard
    expectation_interest: DamageGuard
    foreseeability_limit: DamageGuard
    contributory_negligence: DamageGuard
    failure_to_mitigate: DamageGuard

    def compute(self) -> Dict:
        """Compute damages using the attribute grammar formula."""
        al = self.actual_loss.effective_value
        ei = self.expectation_interest.effective_value
        fl = self.foreseeability_limit.effective_value
        cn = self.contributory_negligence.effective_value
        ftm = self.failure_to_mitigate.effective_value

        # Step 1: Base damages = actual loss + expectation interest
        base = al + ei

        # Step 2: Apply foreseeability cap
        if self.foreseeability_limit.status == GuardStatus.ACTIVE and fl > 0:
            capped = min(base, fl)
            cap_applied = True
        else:
            capped = base
            cap_applied = False

        # Step 3: Apply contributory negligence reduction
        if self.contributory_negligence.status == GuardStatus.ACTIVE:
            if not (0.0 <= cn < 1.0):
                raise ValueError(
                    f"Contributory negligence ratio must be in [0, 1), got {cn}"
                )
            reduced = capped * (1 - cn)
            cn_applied = True
        else:
            reduced = capped
            cn_applied = False

        # Step 4: Subtract failure to mitigate
        final = reduced - ftm
        final = max(0, final)  # Damages cannot be negative

        # Check for TAINTED guards
        tainted = []
        for guard in [self.actual_loss, self.expectation_interest,
                      self.foreseeability_limit, self.contributory_negligence,
                      self.failure_to_mitigate]:
            if guard.status == GuardStatus.TAINTED:
                tainted.append(guard.name)

        return {
            "base_damages": base,
            "foreseeability_cap_applied": cap_applied,
            "after_cap": capped,
            "contributory_negligence_applied": cn_applied,
            "after_cn": reduced if cn_applied else capped,
            "failure_to_mitigate_deducted": ftm,
            "final_damages": final,
            "tainted_guards": tainted,
            "is_reliable": len(tainted) == 0,
            "formula_trace": (
                f"min({al}+{ei}, {fl if cap_applied else 'N/A'}) "
                f"× (1-{cn if cn_applied else 0}) "
                f"- {ftm} = {final}"
            ),
        }


def run_test_cases():
    """Run test cases for the damages attribute grammar."""
    print("=" * 72)
    print("DAMAGES ATTRIBUTE GRAMMAR — TEST SUITE")
    print("=" * 72)

    tests = [
        {
            "name": "Basic breach: AL=100, no cap, no CN, no FTM",
            "computation": DamagesComputation(
                actual_loss=DamageGuard("AL", GuardStatus.ACTIVE, 100, "R001", 1),
                expectation_interest=DamageGuard("EI", GuardStatus.ACTIVE, 50, "R002", 1),
                foreseeability_limit=DamageGuard("FL", GuardStatus.INACTIVE, 0, None, 0),
                contributory_negligence=DamageGuard("CN", GuardStatus.INACTIVE, 0, None, 0),
                failure_to_mitigate=DamageGuard("FTM", GuardStatus.INACTIVE, 0, None, 0),
            ),
            "expected_final": 150,
        },
        {
            "name": "With foreseeability cap: AL+EI=200, FL=120",
            "computation": DamagesComputation(
                actual_loss=DamageGuard("AL", GuardStatus.ACTIVE, 120, "R001", 1),
                expectation_interest=DamageGuard("EI", GuardStatus.ACTIVE, 80, "R002", 1),
                foreseeability_limit=DamageGuard("FL", GuardStatus.ACTIVE, 120, "R003", 2),
                contributory_negligence=DamageGuard("CN", GuardStatus.INACTIVE, 0, None, 0),
                failure_to_mitigate=DamageGuard("FTM", GuardStatus.INACTIVE, 0, None, 0),
            ),
            "expected_final": 120,
        },
        {
            "name": "With contributory negligence: CN=0.3",
            "computation": DamagesComputation(
                actual_loss=DamageGuard("AL", GuardStatus.ACTIVE, 100, "R001", 1),
                expectation_interest=DamageGuard("EI", GuardStatus.ACTIVE, 50, "R002", 1),
                foreseeability_limit=DamageGuard("FL", GuardStatus.INACTIVE, 0, None, 0),
                contributory_negligence=DamageGuard("CN", GuardStatus.ACTIVE, 0.3, "R004", 2),
                failure_to_mitigate=DamageGuard("FTM", GuardStatus.INACTIVE, 0, None, 0),
            ),
            "expected_final": 105,
        },
        {
            "name": "Full formula: AL=100, EI=50, FL=120, CN=0.2, FTM=10",
            "computation": DamagesComputation(
                actual_loss=DamageGuard("AL", GuardStatus.ACTIVE, 100, "R001", 1),
                expectation_interest=DamageGuard("EI", GuardStatus.ACTIVE, 50, "R002", 1),
                foreseeability_limit=DamageGuard("FL", GuardStatus.ACTIVE, 120, "R003", 2),
                contributory_negligence=DamageGuard("CN", GuardStatus.ACTIVE, 0.2, "R004", 2),
                failure_to_mitigate=DamageGuard("FTM", GuardStatus.ACTIVE, 10, "R005", 3),
            ),
            "expected_final": 86,  # min(150,120)=120, ×0.8=96, -10=86
        },
        {
            "name": "Tainted guard (k≥4): FL is TAINTED",
            "computation": DamagesComputation(
                actual_loss=DamageGuard("AL", GuardStatus.ACTIVE, 100, "R001", 1),
                expectation_interest=DamageGuard("EI", GuardStatus.ACTIVE, 50, "R002", 1),
                foreseeability_limit=DamageGuard("FL", GuardStatus.TAINTED, 120, "R003", 4),
                contributory_negligence=DamageGuard("CN", GuardStatus.INACTIVE, 0, None, 0),
                failure_to_mitigate=DamageGuard("FTM", GuardStatus.INACTIVE, 0, None, 0),
            ),
            "expected_final": 150,  # TAINTED guard treated as INACTIVE
        },
    ]

    all_pass = True
    for i, test in enumerate(tests, 1):
        result = test["computation"].compute()
        passed = abs(result["final_damages"] - test["expected_final"]) < 0.01
        status = "PASS" if passed else "FAIL"
        if not passed:
            all_pass = False

        print(f"\nTest {i}: {test['name']}")
        print(f"  Formula: {result['formula_trace']}")
        print(f"  Final: {result['final_damages']} (expected {test['expected_final']}) [{status}]")
        if result["tainted_guards"]:
            print(f"  ⚠ TAINTED guards: {result['tainted_guards']}")
        print(f"  Reliable: {result['is_reliable']}")

    print(f"\n{'=' * 72}")
    print(f"RESULT: {'ALL TESTS PASSED' if all_pass else 'SOME TESTS FAILED'}")
    print(f"{'=' * 72}")
    return all_pass


if __name__ == "__main__":
    success = run_test_cases()
    exit(0 if success else 1)
