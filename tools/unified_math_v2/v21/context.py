"""Lossless structured identities. Digests are locators, never equality proofs."""
from __future__ import annotations
from dataclasses import dataclass, asdict, fields
import json


@dataclass(frozen=True)
class ContextKey:
    request: str
    jurisdiction: str
    event_time: str
    decision_time: str
    procedure: str
    stage: str
    party: str
    issue: str
    scenario: str
    profile: str
    law_version: str
    interpretation: str
    rulepack_version: str
    engine_version: str
    model_version: str
    evidence_version: str
    target: str
    semantic_scope: str
    assumptions: tuple[str, ...]
    max_depth: int

    def __post_init__(self):
        for field in fields(self):
            if field.name not in {'assumptions', 'max_depth'}:
                value = getattr(self, field.name)
                if type(value) is not str or not value:
                    raise ValueError(f'Missing context: {field.name}')
        if type(self.max_depth) is not int or self.max_depth < 0:
            raise ValueError('Explicit nonnegative semantic depth required')
        if (type(self.assumptions) is not tuple
                or any(type(a) is not str or not a for a in self.assumptions)
                or len(set(self.assumptions)) != len(self.assumptions)):
            raise ValueError('Assumptions must be unique string identifiers')
        object.__setattr__(self, 'assumptions', tuple(sorted(self.assumptions)))

    def canonical_json(self) -> str:
        return json.dumps(asdict(self), ensure_ascii=False, sort_keys=True,
                          separators=(',', ':'))

    @classmethod
    def from_json(cls, text: str) -> 'ContextKey':
        def no_duplicate(pairs):
            result = {}
            for key, value in pairs:
                if key in result:
                    raise ValueError('Duplicate JSON key')
                result[key] = value
            return result
        obj = json.loads(text, object_pairs_hook=no_duplicate)
        if type(obj) is not dict or set(obj) != {f.name for f in fields(cls)}:
            raise ValueError('Context schema mismatch')
        if type(obj['assumptions']) is not list:
            raise ValueError('assumptions must be an array')
        obj['assumptions'] = tuple(obj['assumptions'])
        return cls(**obj)

    def structural_key(self) -> tuple:
        return tuple(getattr(self, f.name) for f in fields(self))


def require_same_context(*contexts: ContextKey) -> ContextKey:
    if not contexts or any(type(c) is not ContextKey for c in contexts):
        raise ValueError('Typed context required')
    if any(c != contexts[0] for c in contexts[1:]):
        raise ValueError('Cross-subject/issue/version/model/scope composition rejected')
    return contexts[0]


def synthetic_context(**changes) -> ContextKey:
    """Only a labelled fixture factory, never a current-law default."""
    base = dict(request='synthetic-1', jurisdiction='TEST', event_time='2026-01-01',
                decision_time='2026-09-01', procedure='conditional_analysis', stage='analysis',
                party='claimant', issue='payment', scenario='declared-scenarios', profile='grounded',
                law_version='source-snapshot-example', interpretation='explicit-reference',
                rulepack_version='test-1', engine_version='reference-2.1',
                model_version='synthetic-model-1', evidence_version='test-evidence-1',
                target='award_at_least_threshold', semantic_scope='height_bounded',
                assumptions=('conditional-model',), max_depth=2)
    base.update(changes)
    return ContextKey(**base)
