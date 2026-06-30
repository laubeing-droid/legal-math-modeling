from theory.spec.certificate_schema import (
    build_certificate_payload,
    check_certificate_payload,
    payload_to_dict,
)
from theory.spec.ddl_core import (
    BurdenOfProof,
    ExceptionKind,
    list_defense_targets,
    make_contract_breach_bundle,
    make_license_permission_priority_bundles,
    make_permission_conflict_bundles,
    make_priority_decision_bundles,
    summarize_reparation_modes,
    validate_minimal_ddl_bundle,
)
from theory.spec.horn_aaf_contract import validate_horn_aaf_contract
from theory.spec.reference_semantics import (
    build_permission_conflict_demo_model,
    build_license_permission_demo_model,
    build_contract_breach_demo_model,
    build_priority_decision_demo_model,
    compile_arguments,
    evaluate_contract_breach_reference,
    evaluate_license_permission_reference,
    evaluate_permission_reference,
    evaluate_priority_reference,
    fact_keys,
    grounded_extension,
    horn_closure,
)
from theory.spec.canonical_semantics import DecisionStatus, ReparationMode
from theory.spec.runtime_differential import build_report


def test_contract_breach_bundle_encodes_minimal_ddl_core():
    bundle = make_contract_breach_bundle()
    validate_minimal_ddl_bundle(bundle)

    assert bundle.norm.modality.value == "OBLIGATION"
    assert bundle.norm.violation is not None
    assert summarize_reparation_modes((bundle,)) == (ReparationMode.ORDERED_CHAIN.value,)
    assert list_defense_targets((bundle,)) == ("delivery_breach",)
    assert bundle.defenses[0].exception_kind == ExceptionKind.EXCUSE
    assert bundle.defenses[0].burden_of_proof == BurdenOfProof.RESPONDENT


def test_license_permission_priority_bundles_extend_ddl_core():
    bundles = make_license_permission_priority_bundles()
    for bundle in bundles:
        validate_minimal_ddl_bundle(bundle)

    modalities = tuple(bundle.norm.modality.value for bundle in bundles)
    assert modalities == ("CONSTITUTIVE", "PERMISSION", "PROHIBITION")
    assert "ALTERNATIVE" in summarize_reparation_modes(bundles)


def test_horn_to_aaf_contract_is_satisfied_for_plain_breach_slice():
    model = build_contract_breach_demo_model(force_majeure=False)
    closure, _ = horn_closure(model.rules, fact_keys(model.facts))
    arguments, attacks, _ = compile_arguments(model.norms, closure)
    accepted_ids, _ = grounded_extension(arguments, attacks)
    report = validate_horn_aaf_contract(closure, arguments, attacks, accepted_ids)

    assert report.satisfied is True
    assert not report.violations


def test_reference_trace_can_be_certified_and_checked():
    trace = evaluate_contract_breach_reference(
        build_contract_breach_demo_model(force_majeure=False)
    )
    payload = build_certificate_payload(trace)
    verdict = check_certificate_payload(payload_to_dict(payload))

    assert trace.status == DecisionStatus.PROVED
    assert verdict.ok is True
    assert not verdict.errors


def test_force_majeure_yields_refuted_not_proved():
    trace = evaluate_contract_breach_reference(
        build_contract_breach_demo_model(force_majeure=True)
    )
    payload = build_certificate_payload(trace)
    verdict = check_certificate_payload(payload_to_dict(payload))

    assert trace.status == DecisionStatus.REFUTED
    assert verdict.ok is True


def test_priority_defeat_contract_is_satisfied_for_second_slice():
    model = build_license_permission_demo_model(priority_active=True)
    closure, _ = horn_closure(model.rules, fact_keys(model.facts))
    arguments, attacks, _ = compile_arguments(model.norms, closure, model.priorities)
    accepted_ids, _ = grounded_extension(arguments, attacks)
    report = validate_horn_aaf_contract(closure, arguments, attacks, accepted_ids)

    assert report.satisfied is True
    assert any("Priority defeat" in check for check in report.checks)


def test_license_permission_reference_flips_with_priority_activation():
    with_priority = evaluate_license_permission_reference(
        build_license_permission_demo_model(priority_active=True)
    )
    without_priority = evaluate_license_permission_reference(
        build_license_permission_demo_model(priority_active=False)
    )

    assert with_priority.status == DecisionStatus.PROVED
    assert without_priority.status == DecisionStatus.REFUTED


def test_permission_and_priority_bundles_are_independent_slices():
    permission_bundles = make_permission_conflict_bundles()
    priority_bundles = make_priority_decision_bundles()

    for bundle in (*permission_bundles, *priority_bundles):
        validate_minimal_ddl_bundle(bundle)

    assert tuple(bundle.norm.modality.value for bundle in permission_bundles) == (
        "PERMISSION",
        "PROHIBITION",
    )
    assert tuple(bundle.norm.modality.value for bundle in priority_bundles) == (
        "PERMISSION",
        "PROHIBITION",
    )


def test_license_scope_and_termination_fail_closed():
    outside_scope = evaluate_license_permission_reference(
        build_license_permission_demo_model(priority_active=True, within_scope=False)
    )
    terminated = evaluate_license_permission_reference(
        build_license_permission_demo_model(priority_active=True, terminated=True)
    )

    assert outside_scope.status == DecisionStatus.REFUTED
    assert terminated.status == DecisionStatus.REFUTED


def test_permission_slice_does_not_force_conflict_to_proved():
    condition_missing = evaluate_permission_reference(
        build_permission_conflict_demo_model(
            condition_satisfied=False,
            prohibition_candidate=False,
            override_active=True,
        )
    )
    unresolved_conflict = evaluate_permission_reference(
        build_permission_conflict_demo_model(
            condition_satisfied=True,
            prohibition_candidate=True,
            override_active=False,
        )
    )

    assert condition_missing.status == DecisionStatus.UNDECIDED
    assert unresolved_conflict.status == DecisionStatus.UNDECIDED


def test_priority_slice_missing_and_cycle_cases_fail_closed():
    priority_wins = evaluate_priority_reference(
        build_priority_decision_demo_model(priority_active=True)
    )
    missing_priority = evaluate_priority_reference(
        build_priority_decision_demo_model(priority_active=False)
    )
    priority_cycle = evaluate_priority_reference(
        build_priority_decision_demo_model(priority_active=True),
        priority_cycle=True,
    )
    self_attack = evaluate_priority_reference(
        build_priority_decision_demo_model(priority_active=True),
        self_attack=True,
    )

    assert priority_wins.status == DecisionStatus.PROVED
    assert missing_priority.status == DecisionStatus.UNDECIDED
    assert priority_cycle.status == DecisionStatus.UNDECIDED
    assert self_attack.status == DecisionStatus.UNDECIDED


def test_four_slice_runtime_differential_report_is_green():
    report = build_report()

    assert report.passed is True
    assert not report.blocked
    assert {case.slice_name for case in report.cases} == {
        "contract_breach",
        "license",
        "permission",
        "priority",
    }
