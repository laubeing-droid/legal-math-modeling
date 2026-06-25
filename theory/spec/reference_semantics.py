#!/usr/bin/env python3
"""Transparent reference semantics for the first legal vertical slices.

The evaluator here is deliberately simple and fully traceable. It is a
specification oracle for downstream runtime comparison, not a high-performance
system.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, Iterable, List, Sequence, Set, Tuple

from .canonical_semantics import (
    AttackKind,
    CanonicalArgument,
    CanonicalAttack,
    CanonicalClaim,
    CanonicalFact,
    CanonicalNorm,
    CanonicalProofStep,
    CanonicalProofTrace,
    CanonicalRule,
    DecisionStatus,
    Modality,
    RuleKind,
)
from .certificate_schema import CertificatePayload, build_certificate_payload
from .ddl_core import make_contract_breach_bundle
from .horn_aaf_contract import CompilationContractReport, validate_horn_aaf_contract


@dataclass(frozen=True)
class ReferenceModel:
    """Minimal shared container for facts, norms, and rules."""

    facts: Tuple[CanonicalFact, ...]
    norms: Tuple[CanonicalNorm, ...]
    rules: Tuple[CanonicalRule, ...]


def fact_keys(facts: Iterable[CanonicalFact]) -> Set[str]:
    """Project fact objects to the string keys used by rule premises."""

    return {fact.key for fact in facts}


def horn_closure(
    rules: Sequence[CanonicalRule],
    initial_facts: Set[str],
) -> Tuple[Set[str], List[CanonicalProofStep]]:
    """Compute monotone Horn closure with a full firing trace."""

    closure = set(initial_facts)
    steps: List[CanonicalProofStep] = []
    changed = True
    iteration = 0

    horn_rules = [rule for rule in rules if rule.kind == RuleKind.HORN]
    while changed:
        changed = False
        for rule in horn_rules:
            if set(rule.premises).issubset(closure):
                new_items = [c for c in rule.conclusions if c not in closure]
                if new_items:
                    closure.update(new_items)
                    steps.append(
                        CanonicalProofStep(
                            step_index=len(steps),
                            phase="horn",
                            event="rule_fired",
                            payload={
                                "iteration": iteration,
                                "rule_id": rule.rule_id,
                                "premises": list(rule.premises),
                                "derived": new_items,
                            },
                        )
                    )
                    changed = True
        iteration += 1

    return closure, steps


def claims_from_norms(norms: Sequence[CanonicalNorm], closure: Set[str]) -> List[CanonicalClaim]:
    """Turn satisfied norms and violations into claim candidates."""

    claims: List[CanonicalClaim] = []
    for norm in norms:
        if set(norm.condition_facts).issubset(closure):
            if norm.modality == Modality.OBLIGATION:
                claims.append(
                    CanonicalClaim(
                        claim_id=f"claim::{norm.norm_id}::obligation",
                        conclusion=f"{norm.norm_id}::active",
                        basis_rules=(norm.norm_id,),
                    )
                )
            if norm.violation and norm.violation.trigger_fact in closure:
                claims.append(
                    CanonicalClaim(
                        claim_id=f"claim::{norm.violation.violation_id}",
                        conclusion=norm.violation.consequence_fact,
                        basis_rules=(norm.norm_id,),
                    )
                )
    return claims


def compile_arguments(
    norms: Sequence[CanonicalNorm],
    closure: Set[str],
) -> Tuple[List[CanonicalArgument], List[CanonicalAttack], List[CanonicalProofStep]]:
    """Build a tiny AAF for specification-side differential testing."""

    steps: List[CanonicalProofStep] = []
    arguments: List[CanonicalArgument] = []
    attacks: List[CanonicalAttack] = []

    claims = claims_from_norms(norms, closure)
    for idx, claim in enumerate(claims):
        norm = next(n for n in norms if n.norm_id == claim.basis_rules[0])
        argument = CanonicalArgument(
            argument_id=f"arg::{idx}",
            claim_id=claim.claim_id,
            rule_id=norm.norm_id,
            conclusion=claim.conclusion,
            support_facts=tuple(norm.condition_facts),
            exception_facts=tuple(norm.exception_facts),
        )
        arguments.append(argument)
        steps.append(
            CanonicalProofStep(
                step_index=len(steps),
                phase="aaf",
                event="argument_constructed",
                payload={
                    "argument_id": argument.argument_id,
                    "claim_id": argument.claim_id,
                    "conclusion": argument.conclusion,
                },
            )
        )

    argument_by_conclusion = {argument.conclusion: argument for argument in arguments}
    for norm in norms:
        if not norm.violation:
            continue
        if norm.violation.consequence_fact in argument_by_conclusion:
            target = argument_by_conclusion[norm.violation.consequence_fact]
            for exception_fact in norm.exception_facts:
                if exception_fact in closure:
                    attacker = CanonicalArgument(
                        argument_id=f"arg::exception::{exception_fact}",
                        claim_id=f"claim::exception::{exception_fact}",
                        rule_id=f"exception::{norm.norm_id}",
                        conclusion=exception_fact,
                        support_facts=(exception_fact,),
                    )
                    arguments.append(attacker)
                    steps.append(
                        CanonicalProofStep(
                            step_index=len(steps),
                            phase="aaf",
                            event="argument_constructed",
                            payload={
                                "argument_id": attacker.argument_id,
                                "claim_id": attacker.claim_id,
                                "conclusion": attacker.conclusion,
                            },
                        )
                    )
                    attack = CanonicalAttack(
                        attack_id=f"attack::{attacker.argument_id}->{target.argument_id}",
                        attacker_id=attacker.argument_id,
                        target_id=target.argument_id,
                        kind=AttackKind.EXCEPTION,
                        reason=f"{exception_fact} defeats {target.conclusion}",
                    )
                    attacks.append(attack)
                    steps.append(
                        CanonicalProofStep(
                            step_index=len(steps),
                            phase="aaf",
                            event="attack_constructed",
                            payload={
                                "attack_id": attack.attack_id,
                                "attacker_id": attack.attacker_id,
                                "target_id": attack.target_id,
                                "kind": attack.kind.value,
                            },
                        )
                    )

    return arguments, attacks, steps


def grounded_extension(
    arguments: Sequence[CanonicalArgument],
    attacks: Sequence[CanonicalAttack],
) -> Tuple[Set[str], List[CanonicalProofStep]]:
    """Compute the finite grounded set for the tiny reference AAF."""

    attacked_by: Dict[str, Set[str]] = {}
    attacks_by_source: Dict[str, Set[str]] = {}
    for attack in attacks:
        attacked_by.setdefault(attack.target_id, set()).add(attack.attacker_id)
        attacks_by_source.setdefault(attack.attacker_id, set()).add(attack.target_id)

    accepted: Set[str] = set()
    steps: List[CanonicalProofStep] = []
    changed = True
    while changed:
        changed = False
        for argument in arguments:
            attackers = attacked_by.get(argument.argument_id, set())
            if not attackers and argument.argument_id not in accepted:
                accepted.add(argument.argument_id)
                changed = True
            elif attackers and all(
                any(attacker in attacks_by_source.get(defender, set()) for defender in accepted)
                for attacker in attackers
            ):
                if argument.argument_id not in accepted:
                    accepted.add(argument.argument_id)
                    changed = True
        steps.append(
            CanonicalProofStep(
                step_index=len(steps),
                phase="grounded",
                event="iteration",
                payload={"accepted_ids": sorted(accepted)},
            )
        )

    return accepted, steps


def evaluate_contract_breach_reference(model: ReferenceModel) -> CanonicalProofTrace:
    """Run the first contract-breach vertical slice end to end."""

    steps: List[CanonicalProofStep] = []
    initial = fact_keys(model.facts)
    steps.append(
        CanonicalProofStep(
            step_index=0,
            phase="input",
            event="facts_loaded",
            payload={"facts": sorted(initial)},
        )
    )

    closure, horn_steps = horn_closure(model.rules, initial)
    steps.extend(_reindex_steps(steps, horn_steps))

    arguments, attacks, aaf_steps = compile_arguments(model.norms, closure)
    steps.extend(_reindex_steps(steps, aaf_steps))

    accepted_ids, grounded_steps = grounded_extension(arguments, attacks)
    steps.extend(_reindex_steps(steps, grounded_steps))

    breach_argument_ids = {
        argument.argument_id
        for argument in arguments
        if argument.conclusion == "delivery_breach"
    }
    exception_present = any(attack.kind == AttackKind.EXCEPTION for attack in attacks)

    if breach_argument_ids & accepted_ids:
        status = DecisionStatus.PROVED
        fail_reason = None
    elif breach_argument_ids and exception_present:
        status = DecisionStatus.REFUTED
        fail_reason = None
    elif not breach_argument_ids:
        status = DecisionStatus.UNDECIDED
        fail_reason = "No breach argument was constructed from the current facts."
    else:
        status = DecisionStatus.TAINTED
        fail_reason = "The slice failed closed because the grounded status was not decisive."

    steps.append(
        CanonicalProofStep(
            step_index=len(steps),
            phase="output",
            event="decision_status",
            payload={
                "status": status.value,
                "accepted_argument_ids": sorted(accepted_ids),
                "closure": sorted(closure),
            },
        )
    )
    return CanonicalProofTrace(
        trace_id="trace::contract_breach_reference",
        status=status,
        steps=tuple(steps),
        fail_closed_reason=fail_reason,
    )


def evaluate_contract_breach_with_contract(
    model: ReferenceModel,
) -> tuple[CanonicalProofTrace, CompilationContractReport, CertificatePayload]:
    """Evaluate the slice and expose the downstream validation boundary."""

    initial = fact_keys(model.facts)
    closure, _ = horn_closure(model.rules, initial)
    arguments, attacks, _ = compile_arguments(model.norms, closure)
    accepted_ids, _ = grounded_extension(arguments, attacks)
    trace = evaluate_contract_breach_reference(model)
    contract_report = validate_horn_aaf_contract(closure, arguments, attacks, accepted_ids)
    certificate = build_certificate_payload(trace)
    return trace, contract_report, certificate


def build_contract_breach_demo_model(force_majeure: bool = False) -> ReferenceModel:
    """Construct the first reusable vertical-slice fixture."""

    facts = [
        CanonicalFact("f1", "contract_exists"),
        CanonicalFact("f2", "delivery_due"),
        CanonicalFact("f3", "goods_not_delivered"),
    ]
    if force_majeure:
        facts.append(CanonicalFact("f4", "force_majeure"))

    bundle = make_contract_breach_bundle()
    norms = [bundle.norm]
    rules = [
        CanonicalRule(
            rule_id="rule::delivery_obligation",
            kind=RuleKind.HORN,
            premises=("contract_exists", "delivery_due"),
            conclusions=("norm::delivery::active",),
            notes="Monotone activation of the delivery obligation.",
        ),
        CanonicalRule(
            rule_id="rule::failed_delivery",
            kind=RuleKind.HORN,
            premises=("norm::delivery::active", "goods_not_delivered"),
            conclusions=("delivery_breach_candidate",),
            notes="Monotone breach candidate; final defeat remains in the AAF layer.",
        ),
    ]
    return ReferenceModel(
        facts=tuple(facts),
        norms=tuple(norms),
        rules=tuple(rules),
    )


def _reindex_steps(
    existing: Sequence[CanonicalProofStep],
    new_steps: Sequence[CanonicalProofStep],
) -> List[CanonicalProofStep]:
    """Rebase step indices when phases are concatenated."""

    base = len(existing)
    rebased: List[CanonicalProofStep] = []
    for offset, step in enumerate(new_steps):
        rebased.append(
            CanonicalProofStep(
                step_index=base + offset,
                phase=step.phase,
                event=step.event,
                payload=step.payload,
            )
        )
    return rebased


if __name__ == "__main__":
    for force_majeure in (False, True):
        trace, contract_report, certificate = evaluate_contract_breach_with_contract(
            build_contract_breach_demo_model(force_majeure=force_majeure)
        )
        print(f"force_majeure={force_majeure} -> {trace.status.value}")
        print(f"  contract_satisfied={contract_report.satisfied}")
        print(f"  certificate_schema={certificate.schema_version}")
        if trace.fail_closed_reason:
            print(f"  fail_closed_reason={trace.fail_closed_reason}")
