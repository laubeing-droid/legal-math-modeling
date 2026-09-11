"""Audit-delta projection checks; reuses, rather than replaces, the BR calculator.

Input custody is an explicit host responsibility. This module never asserts
institutional approval, real-world truth, Python/Lean refinement, or real win-rate
validation. The Lean successor models the normalized observations built here;
byte decoding and their correspondence remain a separately audited TCB boundary.
"""
from __future__ import annotations
from dataclasses import asdict, dataclass
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
import json
import sys
from typing import Any, Mapping

REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO / 'tools/business_relations/reference'))
from business import (demo_spec, DecisionInputs, solve, derive_analytics, render,
                      WARNING, FOOTER)  # noqa:E402
from delivery_bundle import (snapshot_inputs, check_business_bundle,
    render_calculation_json, FILES, SCHEMA, REQUIREMENT, SCOPE, NOTICE)  # noqa:E402


class ObservationError(ValueError):
    pass


def unique_object(pairs):
    obj = {}
    for k, v in pairs:
        if k in obj:
            raise ObservationError('DUPLICATE_KEY:' + k)
        obj[k] = v
    return obj


def parse_json(text: str) -> Any:
    def reject(value):
        raise ObservationError('NONFINITE_JSON:' + value)
    return json.loads(text, object_pairs_hook=unique_object, parse_constant=reject)


def canonical(value: Any) -> str:
    return json.dumps(value, ensure_ascii=False, sort_keys=True,
                      separators=(',', ':'), allow_nan=False)


def main_fixture():
    """Explicitly synthetic frozen input, not a default legal policy."""
    s = demo_spec()
    yes, no = ((('payment_recognized', True),), (('payment_recognized', False),))
    m = DecisionInputs(s.context, ((yes, Fraction(2, 5)), (no, Fraction(3, 5))),
                       Fraction(800), tuple(map(Fraction, (100, 60, 10, 10))),
                       tuple(map(Fraction, (600, 850, 1100))))
    return s, m


def expected_doc_metadata(spec) -> dict:
    """Independent task observations: no renderer or submitted document read."""
    return {
        'case': spec.context.request, 'issue': spec.context.issue,
        'creditor': spec.creditor, 'debtor': spec.debtor, 'debt': spec.debt_id,
        'source_ids': [s.source_id for s in spec.sources],
        'due': spec.due_day.isoformat(), 'asof': spec.asof_day.isoformat(),
        'assumptions': list(spec.context.assumptions),
        'context': parse_json(spec.context.canonical_json()),
        'title': '# 条件性本金分析', 'warning': WARNING, 'footer': FOOTER,
        'mode': 'EXACT_FINITE_SCENARIOS',
    }


def read_doc_metadata(text: str) -> dict:
    lines = text.splitlines()
    if len(lines) < 14:
        raise ObservationError('INCOMPLETE_DOCUMENT')
    pairs = [
        ('案件','case',True), ('争点','issue',True), ('权利人','creditor',True),
        ('义务人','debtor',True), ('债项','debt',True), ('依据','source_ids',True),
        ('到期日','due',False), ('观察日','asof',False),
        ('假设','assumptions',True), ('共同语境','context',True),
        ('结论状态','mode',False),
    ]
    out = {'title':lines[0], 'warning':lines[1], 'footer':lines[-1]}
    for ln,(label,key,is_json) in zip(lines[2:13],pairs):
        prefix = label + '：'
        if not ln.startswith(prefix):
            raise ObservationError('DOCUMENT_FIELD:' + label)
        value = ln[len(prefix):]
        out[key] = parse_json(value) if is_json else value
    return out


def expected_json_metadata(spec, model) -> dict:
    """Complete observable input parameters, not outputs dressed as inputs."""
    return {
        'schema':SCHEMA, 'requirement':REQUIREMENT, 'scope':SCOPE,
        'warning':NOTICE, 'principal_document':FILES[0],
        'context':parse_json(spec.context.canonical_json()),
        'basis':[{'source_id':s.source_id,'version':s.version,
                  'start':s.start,'end':s.end,'quoted':s.quoted} for s in spec.sources],
        'relation': {'relation_id':spec.relation_id,'creditor':spec.creditor,
            'debtor':spec.debtor,'debt_id':spec.debt_id,'principal':str(spec.principal),
            'due_day':spec.due_day.isoformat(),'asof_day':spec.asof_day.isoformat()},
        'decision_inputs': {
            'model_version':model.context.model_version,'basis':model.basis,
            'weights':[{'world':[[k,v] for k,v in w], 'probability':str(p)}
                       for w,p in model.weights],
            'threshold':str(model.threshold),'costs':[str(x) for x in model.costs],
            'legal_options':[str(x) for x in model.legal_options],
        },
    }


def read_json_metadata(text: str) -> dict:
    obj=parse_json(text)
    expected={'schema','requirement','scope','warning','context','principal_document',
              'basis','relation','result','decision_inputs','analytics'}
    if type(obj) is not dict or set(obj)!=expected:
        raise ObservationError('TOP_LEVEL_SCHEMA')
    return {k:v for k,v in obj.items() if k not in {'result','analytics'}}


@dataclass(frozen=True)
class ProjectionVerdict:
    accepted: bool
    reason: str
    guarantee: str = 'REFERENCE_BYTE_CHECKS_AND_TYPED_PROJECTION_ONLY'


def verify_full_observations(selected, spec, result, model, analytics,
                             artifacts: Mapping[str, bytes]) -> ProjectionVerdict:
    """No producer-supplied semantics callback. Same selected input throughout.

    Candidate seven-axis wrapper in the SAME reference path. It proves nothing
    about producer permissions; caller must obtain `selected` from host storage.
    """
    try:
        if selected != snapshot_inputs(spec, model):
            return ProjectionVerdict(False,'SELECTED_INPUTS_CHANGED')
        if set(artifacts)!=set(FILES) or any(type(v) is not bytes for v in artifacts.values()):
            return ProjectionVerdict(False,'ACTUAL_TWO_FILES_REQUIRED')
        doc=artifacts[FILES[0]].decode('utf-8',errors='strict')
        js=artifacts[FILES[1]].decode('utf-8',errors='strict')
        if read_doc_metadata(doc)!=expected_doc_metadata(spec):
            return ProjectionVerdict(False,'DOCUMENT_PROTECTED_METADATA')
        if read_json_metadata(js)!=expected_json_metadata(spec,model):
            return ProjectionVerdict(False,'JSON_PROTECTED_INPUTS')
        verdict=check_business_bundle(selected,spec,result,model,analytics,artifacts)
        return ProjectionVerdict(verdict.accepted,verdict.reason)
    except (ValueError,TypeError,KeyError,AttributeError,UnicodeError,OverflowError):
        return ProjectionVerdict(False,'INVALID_OBSERVATION')


def materialize(directory: Path) -> dict:
    """Write actual artifacts, read once, and check precisely those bytes."""
    spec,model=main_fixture();selected=snapshot_inputs(spec,model)
    result=solve(spec);analytics=derive_analytics(spec,result,model)
    directory.mkdir(parents=True,exist_ok=True)
    (directory/FILES[0]).write_text(render(spec,result),encoding='utf-8')
    (directory/FILES[1]).write_text(render_calculation_json(spec,result,model,analytics),encoding='utf-8')
    actual={name:(directory/name).read_bytes() for name in FILES}
    verdict=verify_full_observations(selected,spec,result,model,analytics,actual)
    report={'accepted':verdict.accepted,'reason':verdict.reason,
            'observed_doc':read_doc_metadata(actual[FILES[0]].decode()),
            'observed_json':read_json_metadata(actual[FILES[1]].decode()),
            'artifacts':{n:sha256(b).hexdigest() for n,b in actual.items()},
            'lean':'NOT_EXECUTED','production':'NOT_INTEGRATED',
            'empirical':'SYNTHETIC_NOT_VALIDATED'}
    (directory/'observation-report.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    if not verdict.accepted:
        raise ObservationError(verdict.reason)
    return report


def normalized_observations(spec, model, result, analytics, artifacts) -> dict:
    """Emit semantic vectors read from actual files AFTER independent checking.

    Canonical scenario order is true-first for the existing frozen Lean fixture.
    Original order is not asserted to be semantically significant. Parsing and
    normalization are explicitly on the Python side of the trust boundary.
    """
    from re import fullmatch
    selected=snapshot_inputs(spec,model)
    if not verify_full_observations(selected,spec,result,model,analytics,artifacts).accepted:
        raise ObservationError('NO_ACCEPTED_OBSERVATIONS')
    text=artifacts[FILES[0]].decode();j=parse_json(artifacts[FILES[1]].decode())
    rows=[]
    for line in text.splitlines()[13:-1]:
        m=fullmatch(r'情景：(.+)；本金余额：(-?\d+(?:/\d+)?) 元；超付残差：(-?\d+(?:/\d+)?) 元；性质：条件计算',line)
        if not m:raise ObservationError('CLOSED_EXACT_SCENARIO_ROW')
        w=parse_json(m[1]);rows.append((sorted(w.items()),str(Fraction(m[2])),str(Fraction(m[3]))))
    rows.sort(key=lambda r:tuple((k,v) for k,v in r[0]),reverse=True)
    # Normalization cannot conceal duplicate positions.
    if len({tuple(map(tuple,x[0])) for x in rows})!=len(rows):raise ObservationError('DUPLICATE_WORLD')
    weights=[(sorted(x['world']),x['probability']) for x in j['decision_inputs']['weights']]
    weights.sort(key=lambda x:tuple(map(tuple,x[0])),reverse=True)
    jrows=[(sorted(x['world']),x['principal_balance'],x['overpayment_residual']) for x in j['result']['outcomes']]
    jrows.sort(key=lambda x:tuple(map(tuple,x[0])),reverse=True)
    a=j['analytics']
    payload={'requirement':j['requirement'],'principal':j['relation']['principal'],
       'rows':jrows,'pending':j['result']['pending'],'weights':weights,
       'expectedC':a['expected'],
       'expectedU':str(sum((Fraction(p)*Fraction(next(x[2] for x in jrows if x[0]==w)) for w,p in weights),Fraction(0))),
       'eventProbability':a['event_probability'],'lower':a['lower'],'upper':a['upper'],
       'eligible':a['mutually_acceptable'],'selected':a['selected'],
       'notice':'SYNTHETIC_CONDITIONAL_MODEL_NOT_LITIGATION_FORECAST'}
    return {'doc_metadata':read_doc_metadata(text),'doc_rows':rows,
            'json_metadata':read_json_metadata(artifacts[FILES[1]].decode()),
            'json_values':payload,
            'normalization':'EXACT_PARSED_SET_NO_DUPLICATES_THEN_TRUE_FIRST',
            'expectedU_origin':'DERIVED_FROM_PARSED_OUTCOME_ROWS_AND_WEIGHTS_NOT_A_SEPARATE_JSON_FIELD'}
