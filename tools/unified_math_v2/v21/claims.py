"""Capability-specific evidence requirements. Empirical evidence is conditional."""
from types import MappingProxyType

REQUIRED=MappingProxyType({
    'reference_model_result':frozenset({'reference_checks'}),
    'lean_specification':frozenset({'lean_compilation','axiom_audit','subject_binding'}),
    'runtime_refinement':frozenset({'lean_compilation','axiom_audit','subject_binding','runtime_correspondence'}),
    'source_reviewed_legal_slice':frozenset({'source_snapshot','applicability_review','rule_translation_review'}),
    'model_conditional_forecast':frozenset({'reference_checks','target_definition','model_parameter_binding'}),
    'externally_validated_forecast':frozenset({'reference_checks','target_definition','model_parameter_binding',
        'cluster_time_split','heldout_evaluation','population_scope','validation_approval'}),
})


def claim_check(claim, expected_subject, evidence):
    if claim not in REQUIRED: return {'accepted':False,'missing':['unknown_claim']}
    missing=[]
    for item in REQUIRED[claim]:
        report=evidence.get(item)
        if (type(report) is not dict or report.get('status')!='PASS'
                or report.get('subject')!=expected_subject): missing.append(item)
    # This report verifier consumes already-authenticated evidence records.
    # It cannot authenticate an arbitrary caller's JSON by itself.
    return {'accepted':not missing,'missing':sorted(missing),'claim':claim}
