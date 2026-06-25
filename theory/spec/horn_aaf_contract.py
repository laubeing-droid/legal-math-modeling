#!/usr/bin/env python3
"""Machine-testable Horn -> AAF compilation contract."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, Iterable, List, Sequence, Set, Tuple

from .canonical_semantics import (
    AttackKind,
    CanonicalArgument,
    CanonicalAttack,
    CanonicalProofStep,
)


@dataclass(frozen=True)
class CompilationContractReport:
    """Structured contract verdict for the Horn -> AAF boundary."""

    satisfied: bool
    checks: Tuple[str, ...]
    violations: Tuple[str, ...]


def validate_horn_aaf_contract(
    closure: Set[str],
    arguments: Sequence[CanonicalArgument],
    attacks: Sequence[CanonicalAttack],
    accepted_ids: Iterable[str] = (),
) -> CompilationContractReport:
    """Validate the minimum contract that downstream runtimes must preserve."""

    checks: List[str] = []
    violations: List[str] = []
    argument_ids = {argument.argument_id for argument in arguments}
    accepted = set(accepted_ids)

    for argument in arguments:
        if not set(argument.support_facts).issubset(closure):
            violations.append(
                f"Argument {argument.argument_id} is not traceable to closure facts: "
                f"{sorted(argument.support_facts)}."
            )
    if not violations:
        checks.append("All arguments are traceable to closure facts.")

    for attack in attacks:
        if attack.attacker_id not in argument_ids or attack.target_id not in argument_ids:
            violations.append(
                f"Attack {attack.attack_id} refers to unknown argument ids."
            )
    if not any("unknown argument ids" in violation for violation in violations):
        checks.append("All attacks refer to known argument ids.")

    for attack in attacks:
        if attack.kind == AttackKind.EXCEPTION and "defeats" not in attack.reason:
            violations.append(
                f"Exception attack {attack.attack_id} is missing explicit defeat direction."
            )
    if not any("missing explicit defeat direction" in violation for violation in violations):
        checks.append("Exception attacks carry explicit defeat direction.")

    attack_kinds = {attack.kind for attack in attacks}
    active_exception_facts = {
        fact
        for argument in arguments
        for fact in argument.exception_facts
        if fact in closure
    }
    if AttackKind.EXCEPTION in attack_kinds and AttackKind.REBUTTAL in attack_kinds:
        checks.append("The contract distinguishes ordinary rebuttal from legal exception.")
    elif AttackKind.EXCEPTION in attack_kinds:
        checks.append("The current slice uses legal exception attacks distinctly.")
    elif not active_exception_facts:
        checks.append("No active exception facts were present, so no exception attack was required.")
    else:
        violations.append("Active exception facts were present but no exception attack was produced.")

    priority_pairs = [
        attack for attack in attacks if attack.kind == AttackKind.PRIORITY_DEFEAT
    ]
    if priority_pairs:
        checks.append("Priority defeat is represented explicitly in the AAF attack layer.")

    if accepted and not accepted.issubset(argument_ids):
        violations.append("Accepted-set ids are not a subset of constructed arguments.")
    else:
        checks.append("Accepted-set ids are bounded by constructed arguments.")

    return CompilationContractReport(
        satisfied=not violations,
        checks=tuple(checks),
        violations=tuple(violations),
    )


def extract_contract_steps(report: CompilationContractReport) -> Tuple[CanonicalProofStep, ...]:
    """Expose the contract verdict as trace steps for certificate payloads."""

    steps: List[CanonicalProofStep] = []
    for index, check in enumerate(report.checks):
        steps.append(
            CanonicalProofStep(
                step_index=index,
                phase="contract",
                event="check_passed",
                payload={"message": check},
            )
        )
    base = len(steps)
    for offset, violation in enumerate(report.violations):
        steps.append(
            CanonicalProofStep(
                step_index=base + offset,
                phase="contract",
                event="check_failed",
                payload={"message": violation},
            )
        )
    return tuple(steps)
