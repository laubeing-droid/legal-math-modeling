"""Additive two-file checker for the finite SYNTHETIC principal reference.

The host supplies InputSnapshot from the previously selected request, NOT from
producer output. This is content/requirement binding, not legal approval or a
signature. Existing ContextKey.model_version is reused. Arbitrary prose/DOCX and
real forecasts remain outside this module's claim.
"""
from __future__ import annotations

from dataclasses import dataclass, fields, is_dataclass
from datetime import date
from fractions import Fraction as Q
from hashlib import sha256
import json
from pathlib import Path
from typing import Any, Mapping

from business import (
    PrincipalSpec, Result, Outcome, World, DecisionInputs, Analytics,
    check, check_analytics, verify_document,
)
from context import ContextKey

SCHEMA = 'br/reference-two-file-delivery/1'
REQUIREMENT = 'SYNTHETIC_EXACT_PRINCIPAL_ANALYTICS_TWO_FILES/1'
FILES = ('conditional_principal.txt', 'calculation.json')
SCOPE = 'SYNTHETIC_CONDITIONAL_MODEL_NOT_LITIGATION_FORECAST'
NOTICE = ('本文件只核对已选合成模型的条件本金、概率和行动格；'
          '不构成事实认定、机构批准、真实胜率校准或任意法律业务验收。')


def _snapshot_value(value: Any) -> Any:
    """Typed, lossless input encoding; hashes are not used as equality proofs."""
    if type(value) is Q:
        return {'fraction': [value.numerator, value.denominator]}
    if type(value) is date:
        return {'date': value.isoformat()}
    if is_dataclass(value):
        return {'type': type(value).__name__, 'fields': {
            f.name: _snapshot_value(getattr(value, f.name)) for f in fields(value)}}
    if type(value) is tuple:
        return {'tuple': [_snapshot_value(x) for x in value]}
    if value is None or type(value) in (str, bool, int):
        return value
    raise ValueError('UNSUPPORTED_INPUT_ENCODING')


def _canonical(value: Any) -> str:
    return json.dumps(value, ensure_ascii=False, sort_keys=True,
                      separators=(',', ':'), allow_nan=False)


@dataclass(frozen=True)
class InputSnapshot:
    context: ContextKey
    requirement: str
    exact_inputs: str
    basis_status: str = 'EXPLICIT_SYNTHETIC_INPUT_NOT_EXTERNAL_APPROVAL'


def snapshot_inputs(spec: PrincipalSpec, model: DecisionInputs) -> InputSnapshot:
    """Call at request selection and store outside the submitted certificate.

    This does not approve a model. A changed parameter set may be a legitimate
    NEW request, but cannot be passed off as this previously selected input.
    """
    spec.validate()
    if type(model) is not DecisionInputs or model.context != spec.context:
        raise ValueError('INPUT_SUBJECT_MISMATCH')
    if model.basis != 'SYNTHETIC-SETTLEMENT-GRID/1':
        raise ValueError('UNSUPPORTED_REFERENCE_MODEL_BASIS')
    exact = _canonical({'requirement': REQUIREMENT,
                        'spec': _snapshot_value(spec),
                        'decision_inputs': _snapshot_value(model)})
    return InputSnapshot(spec.context, REQUIREMENT, exact)


def _world_out(w: World) -> list[list[Any]]:
    return [[key, value] for key, value in w]


def _analytics_out(a: Analytics) -> dict[str, Any]:
    obj: dict[str, Any] = {}
    for f in fields(a):
        value = getattr(a, f.name)
        if f.name == 'context':
            obj[f.name] = json.loads(value.canonical_json())
        elif f.name == 'weights':
            obj[f.name] = [{'world': _world_out(w), 'probability': str(p)}
                           for w, p in value]
        elif f.name in ('legal_options', 'mutually_acceptable'):
            obj[f.name] = [str(q) for q in value]
        else:
            obj[f.name] = None if value is None else str(value)
    return obj


def render_calculation_json(spec: PrincipalSpec, result: Result,
                            model: DecisionInputs, analytics: Analytics) -> str:
    if not check_analytics(spec, result, model, analytics):
        raise ValueError('UNCHECKED_ANALYTICS')
    obj = {
        'schema': SCHEMA, 'requirement': REQUIREMENT,
        'scope': SCOPE, 'warning': NOTICE,
        'context': json.loads(spec.context.canonical_json()),
        'principal_document': FILES[0],
        'basis': [{'source_id': s.source_id, 'version': s.version,
                   'start': s.start, 'end': s.end, 'quoted': s.quoted}
                  for s in spec.sources],
        'relation': {'relation_id': spec.relation_id, 'creditor': spec.creditor,
                     'debtor': spec.debtor, 'debt_id': spec.debt_id,
                     'principal': str(spec.principal),
                     'due_day': spec.due_day.isoformat(),
                     'asof_day': spec.asof_day.isoformat()},
        'result': {'mode': result.mode, 'pending': [_world_out(w) for w in result.pending],
                   'outcomes': [{'world': _world_out(o.world),
                                 'principal_balance': str(o.principal_balance),
                                 'overpayment_residual': str(o.overpayment_residual)}
                                for o in result.outcomes]},
        'decision_inputs': {
            'model_version': model.context.model_version, 'basis': model.basis,
            'weights': [{'world': _world_out(w), 'probability': str(p)}
                        for w, p in model.weights],
            'threshold': str(model.threshold), 'costs': [str(q) for q in model.costs],
            'legal_options': [str(q) for q in model.legal_options]},
        'analytics': _analytics_out(analytics),
    }
    return json.dumps(obj, ensure_ascii=False, sort_keys=True, indent=2,
                      allow_nan=False) + '\n'


def _reject_constant(value: str) -> None:
    raise ValueError('NONFINITE_JSON_CONSTANT')


def _unique_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    obj: dict[str, Any] = {}
    for key, value in pairs:
        if key in obj:
            raise ValueError('DUPLICATE_JSON_KEY')
        obj[key] = value
    return obj


def _keys(value: Any, expected: set[str]) -> dict[str, Any]:
    if type(value) is not dict or set(value) != expected:
        raise ValueError('CLOSED_SCHEMA_MISMATCH')
    return value


def _rational(value: Any) -> Q:
    if type(value) is not str:
        raise ValueError('RATIONAL_MUST_BE_STRING')
    parsed = Q(value)
    # Exact, canonical rational format; no floats or bool-as-int coercions.
    if str(parsed) != value:
        raise ValueError('NONCANONICAL_RATIONAL')
    return parsed


def _array(value: Any) -> list[Any]:
    if type(value) is not list:
        raise ValueError('ARRAY_REQUIRED')
    return value


def _world(value: Any) -> World:
    arr = _array(value)
    pairs = []
    for pair in arr:
        if (type(pair) is not list or len(pair) != 2 or type(pair[0]) is not str
                or type(pair[1]) is not bool):
            raise ValueError('WORLD_SCHEMA')
        pairs.append((pair[0], pair[1]))
    if len(pairs) != len({k for k, _ in pairs}):
        raise ValueError('DUPLICATE_WORLD_ATOM')
    return tuple(pairs)


def _weights(value: Any) -> tuple[tuple[World, Q], ...]:
    ans = []
    for item in _array(value):
        item = _keys(item, {'world', 'probability'})
        ans.append((_world(item['world']), _rational(item['probability'])))
    return tuple(ans)


def verify_calculation_json(spec: PrincipalSpec, result: Result,
                            model: DecisionInputs, analytics: Analytics,
                            text: str) -> bool:
    """Parse actual JSON and reconstruct typed objects. Never calls the renderer.

    Both parsed and in-memory values must validate against the SAME independent
    model input. No field saying 'already verified' is trusted as evidence.
    """
    try:
        if type(text) is not str or not check_analytics(spec, result, model, analytics):
            return False
        obj = json.loads(text, object_pairs_hook=_unique_pairs,
                         parse_constant=_reject_constant)
        _keys(obj, {'schema','requirement','scope','warning','context',
                    'principal_document','basis','relation','result',
                    'decision_inputs','analytics'})
        if (obj['schema'],obj['requirement'],obj['scope'],obj['warning'],obj['principal_document']) != (
                SCHEMA,REQUIREMENT,SCOPE,NOTICE,FILES[0]):
            return False
        ctx = ContextKey.from_json(_canonical(obj['context']))
        if ctx != spec.context:
            return False
        source_rows = _array(obj['basis'])
        if len(source_rows) != len(spec.sources):
            return False
        for row, source in zip(source_rows, spec.sources):
            _keys(row, {'source_id','version','start','end','quoted'})
            if type(row['start']) is not int or type(row['end']) is not int:
                return False
            if (row['source_id'],row['version'],row['start'],row['end'],row['quoted']) != (
                    source.source_id,source.version,source.start,source.end,source.quoted):
                return False
        rel = _keys(obj['relation'], {'relation_id','creditor','debtor','debt_id',
                                     'principal','due_day','asof_day'})
        if (rel['relation_id'],rel['creditor'],rel['debtor'],rel['debt_id'],
            _rational(rel['principal']),rel['due_day'],rel['asof_day']) != (
                spec.relation_id,spec.creditor,spec.debtor,spec.debt_id,spec.principal,
                spec.due_day.isoformat(),spec.asof_day.isoformat()):
            return False
        rr = _keys(obj['result'], {'mode','pending','outcomes'})
        outcomes = []
        for row in _array(rr['outcomes']):
            _keys(row, {'world','principal_balance','overpayment_residual'})
            outcomes.append(Outcome(ctx,spec.relation_id,spec.creditor,spec.debtor,spec.debt_id,
                tuple(s.source_id for s in spec.sources),spec.asof_day,_world(row['world']),
                _rational(row['principal_balance']),_rational(row['overpayment_residual'])))
        parsed_result = Result(ctx,rr['mode'],tuple(outcomes),
                               tuple(_world(w) for w in _array(rr['pending'])))
        if (not check(spec, parsed_result) or parsed_result.mode != result.mode
                or frozenset(parsed_result.outcomes) != frozenset(result.outcomes)
                or frozenset(parsed_result.pending) != frozenset(result.pending)):
            return False
        mm = _keys(obj['decision_inputs'], {'model_version','basis','weights',
                                           'threshold','costs','legal_options'})
        if mm['model_version'] != spec.context.model_version:
            return False
        parsed_model = DecisionInputs(ctx,_weights(mm['weights']),_rational(mm['threshold']),
            tuple(_rational(q) for q in _array(mm['costs'])),
            tuple(_rational(q) for q in _array(mm['legal_options'])),mm['basis'])
        if parsed_model != model:
            return False
        aa = _keys(obj['analytics'], {f.name for f in fields(Analytics)})
        vals = {}
        for f in fields(Analytics):
            value = aa[f.name]
            if f.name == 'context':
                vals[f.name] = ContextKey.from_json(_canonical(value))
            elif f.name == 'weights':
                vals[f.name] = _weights(value)
            elif f.name in ('legal_options','mutually_acceptable'):
                vals[f.name] = tuple(_rational(q) for q in _array(value))
            elif f.name == 'selected' and value is None:
                vals[f.name] = None
            else:
                vals[f.name] = _rational(value)
        parsed_analytics = Analytics(**vals)
        return (parsed_analytics == analytics
                and check_analytics(spec, parsed_result, model, parsed_analytics))
    except (ValueError,TypeError,KeyError,AttributeError,ZeroDivisionError,OverflowError):
        return False


@dataclass(frozen=True)
class BundleVerdict:
    accepted: bool
    status: str
    scope: str
    reason: str
    # Integrity locators for the exact bytes read; not external attestations.
    checked_artifacts: tuple[tuple[str,str], ...] = ()


def check_business_bundle(expected: InputSnapshot, spec: PrincipalSpec, result: Result,
                          model: DecisionInputs, analytics: Analytics,
                          artifact_bytes: Mapping[str, bytes]) -> BundleVerdict:
    """Only this reference requirement: exact finite scenarios + both closed files.

    Does not grant claims for partial solving, arbitrary prose, DOCX, learned
    forecasts, source-language correctness, institutional approval or 134 tasks.
    """
    def reject(reason: str) -> BundleVerdict:
        return BundleVerdict(False,'REJECT_REFERENCE_BUNDLE',SCOPE,reason)
    try:
        if type(expected) is not InputSnapshot or expected.requirement != REQUIREMENT:
            return reject('EXPECTED_REQUIREMENT')
        if expected != snapshot_inputs(spec, model):
            return reject('SELECTED_INPUTS_CHANGED')
        if (type(result) is not Result or type(result.outcomes) is not tuple
                or type(result.pending) is not tuple):
            return reject('IMMUTABLE_RESULT_REQUIRED')
        if not check(spec, result):
            return reject('PRINCIPAL_CHECK')
        if result.mode != 'EXACT_FINITE_SCENARIOS':
            return reject('REQUIREMENT_NOT_COMPLETE')
        if not check_analytics(spec, result, model, analytics):
            return reject('ANALYTICS_CHECK')
        if set(artifact_bytes) != set(FILES):
            return reject('EXACT_ARTIFACT_SET')
        raw = {name: artifact_bytes[name] for name in FILES}
        if any(type(b) is not bytes for b in raw.values()):
            return reject('ARTIFACT_BYTES_REQUIRED')
        text = raw[FILES[0]].decode('utf-8', errors='strict')
        calculation = raw[FILES[1]].decode('utf-8', errors='strict')
        if not verify_document(spec, result, text):
            return reject('PRINCIPAL_FILE_READBACK')
        if not verify_calculation_json(spec, result, model, analytics, calculation):
            return reject('ANALYTICS_FILE_READBACK')
        return BundleVerdict(True,'ACCEPT_REFERENCE_TWO_FILE_REQUIREMENT',SCOPE,
            'Same selected input; both actual file snapshots checked. Lean/JC not certified.',
            tuple((name,sha256(raw[name]).hexdigest()) for name in FILES))
    except (ValueError,TypeError,KeyError,AttributeError,UnicodeError,ZeroDivisionError):
        return reject('INVALID_INPUT_OR_ENCODING')


def read_artifacts(directory: Path) -> dict[str, bytes]:
    """Read known files once. Guarantee refers to these bytes, not later mutations."""
    data = {}
    for name in FILES:
        path = directory / name
        if path.is_symlink() or not path.is_file():
            raise ValueError('REGULAR_ARTIFACT_FILE_REQUIRED')
        data[name] = path.read_bytes()
    return data
