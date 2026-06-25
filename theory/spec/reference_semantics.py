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
    CanonicalPriority,
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
from .ddl_core import (make_admin_bundle, make_contract_breach_bundle, make_criminal_bundle, make_license_permission_priority_bundles, make_tort_bundle)
from .horn_aaf_contract import CompilationContractReport, validate_horn_aaf_contract


@dataclass(frozen=True)
class ReferenceModel:
    """Minimal shared container for facts, norms, and rules."""

    facts: Tuple[CanonicalFact, ...]
    norms: Tuple[CanonicalNorm, ...]
    rules: Tuple[CanonicalRule, ...]
    priorities: Tuple[CanonicalPriority, ...] = ()


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
            if norm.conclusion_fact is not None:
                claims.append(
                    CanonicalClaim(
                        claim_id=f"claim::{norm.norm_id}::conclusion",
                        conclusion=norm.conclusion_fact,
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
    priorities: Sequence[CanonicalPriority] = (),
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
    arguments_by_rule_id = {argument.rule_id: argument for argument in arguments}
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

    for priority in priorities:
        winner_argument = arguments_by_rule_id.get(priority.winner)
        loser_norm = next((norm for norm in norms if norm.norm_id == priority.loser), None)
        if winner_argument is None or loser_norm is None or loser_norm.violation is None:
            continue
        loser_argument = argument_by_conclusion.get(loser_norm.violation.consequence_fact)
        if loser_argument is None:
            continue
        attack = CanonicalAttack(
            attack_id=f"attack::{winner_argument.argument_id}->{loser_argument.argument_id}::priority",
            attacker_id=winner_argument.argument_id,
            target_id=loser_argument.argument_id,
            kind=AttackKind.PRIORITY_DEFEAT,
            reason=priority.reason,
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

    arguments, attacks, aaf_steps = compile_arguments(model.norms, closure, model.priorities)
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
    arguments, attacks, _ = compile_arguments(model.norms, closure, model.priorities)
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


def build_license_permission_demo_model(priority_active: bool = True) -> ReferenceModel:
    """Construct the second slice for constitutive, permission, and priority defeat."""

    facts = [
        CanonicalFact("f1", "license_signed"),
        CanonicalFact("f2", "rights_holder_authorized"),
        CanonicalFact("f3", "used_work"),
        CanonicalFact("f4", "use_within_scope"),
    ]
    bundles = make_license_permission_priority_bundles()
    norms = [bundle.norm for bundle in bundles]
    priorities = tuple(
        priority
        for bundle in bundles
        for priority in bundle.priorities
    )
    if not priority_active:
        priorities = ()
    rules = [
        CanonicalRule(
            rule_id="rule::license_status",
            kind=RuleKind.HORN,
            premises=("license_signed", "rights_holder_authorized"),
            conclusions=("license_status_active",),
            notes="Constitutive activation of license status.",
        ),
        CanonicalRule(
            rule_id="rule::licensed_use_permission",
            kind=RuleKind.HORN,
            premises=("license_status_active", "use_within_scope"),
            conclusions=("use_permitted",),
            notes="Permission conclusion derived from an active in-scope license.",
        ),
        CanonicalRule(
            rule_id="rule::used_work",
            kind=RuleKind.HORN,
            premises=("used_work",),
            conclusions=("unauthorized_use_candidate",),
            notes="Monotone candidate for prohibited use; final defeat remains in AAF.",
        ),
    ]
    return ReferenceModel(
        facts=tuple(facts),
        norms=tuple(norms),
        rules=tuple(rules),
        priorities=priorities,
    )

def build_tort_demo_model(contributory_negligence: bool = False) -> ReferenceModel:
    """Construct the third slice for tort liability."""
    facts = [
        CanonicalFact("f1", "duty_of_care"),
        CanonicalFact("f2", "breach_of_duty"),
        CanonicalFact("f3", "causation"),
        CanonicalFact("f4", "damage"),
    ]
    if contributory_negligence:
        facts.append(CanonicalFact("f5", "contributory_negligence"))
    bundle = make_tort_bundle()
    norms = [bundle.norm]
    rules = [
        CanonicalRule(rule_id="rule::tort_breach", kind=RuleKind.HORN, premises=("duty_of_care", "breach_of_duty", "causation", "damage"), conclusions=("tort_breach_candidate",), notes="Monotone tort breach candidate."),
    ]
    return ReferenceModel(facts=tuple(facts), norms=tuple(norms), rules=tuple(rules))

def build_criminal_demo_model(self_defense: bool = False) -> ReferenceModel:
    """Construct the fourth slice for criminal liability."""
    facts = [
        CanonicalFact("f1", "actus_reus"),
        CanonicalFact("f2", "mens_rea"),
        CanonicalFact("f3", "absence_of_defense"),
    ]
    if self_defense:
        facts.append(CanonicalFact("f4", "self_defense"))
    bundle = make_criminal_bundle()
    norms = [bundle.norm]
    rules = [
        CanonicalRule(rule_id="rule::criminal_breach", kind=RuleKind.HORN, premises=("actus_reus", "mens_rea", "absence_of_defense"), conclusions=("criminal_breach_candidate",), notes="Monotone criminal breach candidate."),
    ]
    return ReferenceModel(facts=tuple(facts), norms=tuple(norms), rules=tuple(rules))

def build_admin_demo_model(priority_active: bool = True) -> ReferenceModel:
    """Construct the fifth slice for administrative illegality with priority override."""
    facts = [
        CanonicalFact("f1", "admin_action"),
        CanonicalFact("f2", "exceeds_authority"),
        CanonicalFact("f3", "no_legal_basis"),
    ]
    if priority_active:
        facts.append(CanonicalFact("f4", "legal_basis_exists"))
    bundles = make_admin_bundle()
    norms = [bundle.norm for bundle in bundles]
    priorities = tuple(dict.fromkeys(priority for bundle in bundles for priority in bundle.priorities))
    if not priority_active:
        priorities = ()
    rules = [
        CanonicalRule(rule_id="rule::admin_breach", kind=RuleKind.HORN, premises=("admin_action", "exceeds_authority", "no_legal_basis"), conclusions=("admin_breach_candidate",), notes="Monotone admin breach candidate."),
        CanonicalRule(rule_id="rule::higher_law_validity", kind=RuleKind.HORN, premises=("legal_basis_exists",), conclusions=("admin_action_valid",), notes="Higher law norm activates when legal basis exists."),
    ]
    return ReferenceModel(facts=tuple(facts), norms=tuple(norms), rules=tuple(rules), priorities=priorities)


def evaluate_license_permission_reference(model: ReferenceModel) -> CanonicalProofTrace:
    """Evaluate the second slice with priority-based defeat."""

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

    arguments, attacks, aaf_steps = compile_arguments(model.norms, closure, model.priorities)
    steps.extend(_reindex_steps(steps, aaf_steps))

    accepted_ids, grounded_steps = grounded_extension(arguments, attacks)
    steps.extend(_reindex_steps(steps, grounded_steps))

    permitted_argument_ids = {
        argument.argument_id for argument in arguments if argument.conclusion == "use_permitted"
    }
    prohibited_argument_ids = {
        argument.argument_id for argument in arguments if argument.conclusion == "unauthorized_use"
    }
    priority_present = any(attack.kind == AttackKind.PRIORITY_DEFEAT for attack in attacks)

    if permitted_argument_ids & accepted_ids and prohibited_argument_ids.isdisjoint(accepted_ids):
        status = DecisionStatus.PROVED
        fail_reason = None
    elif prohibited_argument_ids & accepted_ids and not priority_present:
        status = DecisionStatus.REFUTED
        fail_reason = None
    elif permitted_argument_ids.isdisjoint(accepted_ids) and prohibited_argument_ids.isdisjoint(accepted_ids):
        status = DecisionStatus.UNDECIDED
        fail_reason = "Neither permission nor prohibition reached an accepted grounded status."
    else:
        status = DecisionStatus.TAINTED
        fail_reason = "The permission/prohibition interaction failed closed."

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
        trace_id="trace::license_permission_reference",
        status=status,
        steps=tuple(steps),
        fail_closed_reason=fail_reason,
    )


def evaluate_license_permission_with_contract(
    model: ReferenceModel,
) -> tuple[CanonicalProofTrace, CompilationContractReport, CertificatePayload]:
    """Evaluate the second slice and expose the downstream validation boundary."""

    initial = fact_keys(model.facts)
    closure, _ = horn_closure(model.rules, initial)
    arguments, attacks, _ = compile_arguments(model.norms, closure, model.priorities)
    accepted_ids, _ = grounded_extension(arguments, attacks)
    trace = evaluate_license_permission_reference(model)
    contract_report = validate_horn_aaf_contract(closure, arguments, attacks, accepted_ids)
    certificate = build_certificate_payload(trace)
    return trace, contract_report, certificate


def evaluate_tort_reference(model: ReferenceModel) -> CanonicalProofTrace:
    """Evaluate the tort-breach vertical slice end to end."""
    steps: List[CanonicalProofStep] = []
    initial = fact_keys(model.facts)
    steps.append(CanonicalProofStep(step_index=0, phase="input", event="facts_loaded", payload={"facts": sorted(initial)}))
    closure, horn_steps = horn_closure(model.rules, initial)
    steps.extend(_reindex_steps(steps, horn_steps))
    arguments, attacks, aaf_steps = compile_arguments(model.norms, closure, model.priorities)
    steps.extend(_reindex_steps(steps, aaf_steps))
    accepted_ids, grounded_steps = grounded_extension(arguments, attacks)
    steps.extend(_reindex_steps(steps, grounded_steps))
    tort_argument_ids = {argument.argument_id for argument in arguments if argument.conclusion == "tort_liability"}
    exception_present = any(attack.kind == AttackKind.EXCEPTION for attack in attacks)
    if tort_argument_ids & accepted_ids:
        status, fail_reason = DecisionStatus.PROVED, None
    elif tort_argument_ids and exception_present:
        status, fail_reason = DecisionStatus.REFUTED, None
    elif not tort_argument_ids:
        status, fail_reason = DecisionStatus.UNDECIDED, "No tort liability argument was constructed."
    else:
        status, fail_reason = DecisionStatus.TAINTED, "Tort slice failed closed."
    steps.append(CanonicalProofStep(step_index=len(steps), phase="output", event="decision_status", payload={"status": status.value, "accepted_argument_ids": sorted(accepted_ids), "closure": sorted(closure)}))
    return CanonicalProofTrace(trace_id="trace::tort_reference", status=status, steps=tuple(steps), fail_closed_reason=fail_reason)


def evaluate_tort_with_contract(model: ReferenceModel) -> tuple[CanonicalProofTrace, CompilationContractReport, CertificatePayload]:
    """Evaluate the tort slice and expose the downstream validation boundary."""
    initial = fact_keys(model.facts)
    closure, _ = horn_closure(model.rules, initial)
    arguments, attacks, _ = compile_arguments(model.norms, closure, model.priorities)
    accepted_ids, _ = grounded_extension(arguments, attacks)
    trace = evaluate_tort_reference(model)
    contract_report = validate_horn_aaf_contract(closure, arguments, attacks, accepted_ids)
    certificate = build_certificate_payload(trace)
    return trace, contract_report, certificate

def evaluate_criminal_reference(model: ReferenceModel) -> CanonicalProofTrace:
    """Evaluate the criminal-breach vertical slice end to end."""
    steps: List[CanonicalProofStep] = []
    initial = fact_keys(model.facts)
    steps.append(CanonicalProofStep(step_index=0, phase="input", event="facts_loaded", payload={"facts": sorted(initial)}))
    closure, horn_steps = horn_closure(model.rules, initial)
    steps.extend(_reindex_steps(steps, horn_steps))
    arguments, attacks, aaf_steps = compile_arguments(model.norms, closure, model.priorities)
    steps.extend(_reindex_steps(steps, aaf_steps))
    accepted_ids, grounded_steps = grounded_extension(arguments, attacks)
    steps.extend(_reindex_steps(steps, grounded_steps))
    criminal_argument_ids = {argument.argument_id for argument in arguments if argument.conclusion == "criminal_liability"}
    exception_present = any(attack.kind == AttackKind.EXCEPTION for attack in attacks)
    if criminal_argument_ids & accepted_ids:
        status, fail_reason = DecisionStatus.PROVED, None
    elif criminal_argument_ids and exception_present:
        status, fail_reason = DecisionStatus.REFUTED, None
    elif not criminal_argument_ids:
        status, fail_reason = DecisionStatus.UNDECIDED, "No criminal liability argument was constructed."
    else:
        status, fail_reason = DecisionStatus.TAINTED, "Criminal slice failed closed."
    steps.append(CanonicalProofStep(step_index=len(steps), phase="output", event="decision_status", payload={"status": status.value, "accepted_argument_ids": sorted(accepted_ids), "closure": sorted(closure)}))
    return CanonicalProofTrace(trace_id="trace::criminal_reference", status=status, steps=tuple(steps), fail_closed_reason=fail_reason)


def evaluate_criminal_with_contract(model: ReferenceModel) -> tuple[CanonicalProofTrace, CompilationContractReport, CertificatePayload]:
    """Evaluate the criminal slice and expose the downstream validation boundary."""
    initial = fact_keys(model.facts)
    closure, _ = horn_closure(model.rules, initial)
    arguments, attacks, _ = compile_arguments(model.norms, closure, model.priorities)
    accepted_ids, _ = grounded_extension(arguments, attacks)
    trace = evaluate_criminal_reference(model)
    contract_report = validate_horn_aaf_contract(closure, arguments, attacks, accepted_ids)
    certificate = build_certificate_payload(trace)
    return trace, contract_report, certificate

def evaluate_admin_reference(model: ReferenceModel) -> CanonicalProofTrace:
    """Evaluate the admin-breach vertical slice end to end."""
    steps: List[CanonicalProofStep] = []
    initial = fact_keys(model.facts)
    steps.append(CanonicalProofStep(step_index=0, phase="input", event="facts_loaded", payload={"facts": sorted(initial)}))
    closure, horn_steps = horn_closure(model.rules, initial)
    steps.extend(_reindex_steps(steps, horn_steps))
    arguments, attacks, aaf_steps = compile_arguments(model.norms, closure, model.priorities)
    steps.extend(_reindex_steps(steps, aaf_steps))
    accepted_ids, grounded_steps = grounded_extension(arguments, attacks)
    steps.extend(_reindex_steps(steps, grounded_steps))
    admin_argument_ids = {argument.argument_id for argument in arguments if argument.conclusion == "admin_illegality"}
    valid_argument_ids = {argument.argument_id for argument in arguments if argument.conclusion == "admin_action_valid"}
    priority_present = any(attack.kind == AttackKind.PRIORITY_DEFEAT for attack in attacks)
    if valid_argument_ids & accepted_ids and priority_present:
        status, fail_reason = DecisionStatus.REFUTED, None
    elif admin_argument_ids & accepted_ids:
        status, fail_reason = DecisionStatus.PROVED, None
    elif not admin_argument_ids:
        status, fail_reason = DecisionStatus.UNDECIDED, "No admin illegality argument was constructed."
    else:
        status, fail_reason = DecisionStatus.TAINTED, "Admin slice failed closed."
    steps.append(CanonicalProofStep(step_index=len(steps), phase="output", event="decision_status", payload={"status": status.value, "accepted_argument_ids": sorted(accepted_ids), "closure": sorted(closure)}))
    return CanonicalProofTrace(trace_id="trace::admin_reference", status=status, steps=tuple(steps), fail_closed_reason=fail_reason)


def evaluate_admin_with_contract(model: ReferenceModel) -> tuple[CanonicalProofTrace, CompilationContractReport, CertificatePayload]:
    """Evaluate the admin slice and expose the downstream validation boundary."""
    initial = fact_keys(model.facts)
    closure, _ = horn_closure(model.rules, initial)
    arguments, attacks, _ = compile_arguments(model.norms, closure, model.priorities)
    accepted_ids, _ = grounded_extension(arguments, attacks)
    trace = evaluate_admin_reference(model)
    contract_report = validate_horn_aaf_contract(closure, arguments, attacks, accepted_ids)
    certificate = build_certificate_payload(trace)
    return trace, contract_report, certificate

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
    for priority_active in (True, False):
        trace, contract_report, certificate = evaluate_license_permission_with_contract(
            build_license_permission_demo_model(priority_active=priority_active)
        )
        print(f"priority_active={priority_active} -> {trace.status.value}")
        print(f"  contract_satisfied={contract_report.satisfied}")
        print(f"  certificate_schema={certificate.schema_version}")
        if trace.fail_closed_reason:
            print(f"  fail_closed_reason={trace.fail_closed_reason}")
