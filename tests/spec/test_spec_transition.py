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
    summarize_reparation_modes,
    validate_minimal_ddl_bundle,
)
from theory.spec.horn_aaf_contract import validate_horn_aaf_contract
from theory.spec.reference_semantics import (
    build_license_permission_demo_model,
    build_contract_breach_demo_model,
    compile_arguments,
    evaluate_contract_breach_reference,
    evaluate_license_permission_reference,
    fact_keys,
    grounded_extension,
    horn_closure,
)
from theory.spec.canonical_semantics import DecisionStatus, ReparationMode


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
