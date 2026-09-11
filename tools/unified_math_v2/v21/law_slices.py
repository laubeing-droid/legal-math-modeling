"""Small source-mapped rule slices; fixed conditions, not automatic fact-finding.

All source applicability and findings in reference fixtures are assumptions.
Full field coverage is tracked separately and NEVER inferred from these slices.
"""
from dataclasses import dataclass
from .context import ContextKey

@dataclass(frozen=True)
class LegalSlice:
    identity: str
    field: str
    source_id: str
    article: str
    required: tuple[str,...]
    consequence: str
    legal_review: str = 'TRANSLATION_PENDING_PROFESSIONAL_REVIEW'

SLICES=(
 LegalSlice('civil-burden-90','civil','L-CIVPROC-2022','90',
    ('rule_applicable','stage_ready','proof_assessment_completed','bearer_identified','fact_unproved'),
    'burden_bearer_suffers_declared_issue_consequence'),
 LegalSlice('criminal-200-3','criminal','L-CRIMPROC-2018','200(3)',
    ('rule_applicable','trial_ready_for_judgment','proof_assessment_completed','charge_not_established_due_to_insufficient_evidence'),
    'conditional_evidence_insufficient_acquittal'),
 LegalSlice('administrative-37','administrative','L-ADMIN-2017','37',
    ('rule_applicable','plaintiff_illegality_evidence_not_established'),
    'defendant_burden_not_discharged_by_plaintiff_failure'),
 LegalSlice('labor-evidence-6','labor','L-LABOR-2007','6',
    ('rule_applicable','evidence_relevant','evidence_controlled_by_employer','employer_failed_to_produce'),
    'employer_bears_applicable_adverse_consequence'),
 LegalSlice('civil-limitation-193','civil','L-CIVIL-CODE','193',
    ('rule_applicable','limitation_issue'),
    'court_must_not_apply_limitation_ex_officio'),
 LegalSlice('plea-standard-2026','criminal','L-PLEA-2026','3',
    ('rule_applicable','plea_case'),
    'plea_does_not_lower_statutory_proof_standard'),
)


def evaluate_slice(context: ContextKey, slice_id, findings):
    selected=[s for s in SLICES if s.identity==slice_id]
    if not selected: raise ValueError('No supported source slice')
    s=selected[0]
    if any(type(v) is not str or v not in {'true','false','unknown'} for v in findings.values()):
        raise ValueError('Explicit tri-state findings required')
    if set(findings)-set(s.required):raise ValueError('Unexpected finding keys')
    missing=tuple(k for k in s.required if findings.get(k,'unknown')=='unknown')
    negative=tuple(k for k in s.required if findings.get(k)=='false')
    status='not_triggered' if negative else 'pending' if missing else 'conditional_consequence'
    return {'context':context.canonical_json(),'slice':slice_id,'field':s.field,
            'status':status,'consequence':s.consequence if status=='conditional_consequence' else None,
            'source':s.source_id,'article':s.article,'missing':missing,'explicit_false':negative,
            'assumptions':tuple(k for k in s.required if findings.get(k)=='true'),
            'legal_review':s.legal_review,'institutional_act':False,'fact_promotions':0}
