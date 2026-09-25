#!/usr/bin/env python3
"""L0 meta-concept contracts (P-002, P-003, P-010, P-009).

Concept-as-dataset-plus-rule (P-002): a concept is its definition record
bound to a computation rule id — same pair, same concept; different pair,
different concept. Legal term binding (P-003): one canonical term per
definition per jurisdiction; translation preserves the definition id, so
meaning survives language change. Versioned concept admission (P-009):
new objects enter by registration with a concept version. Personal
information family (P-010): identification/relating paths, anonymization
removing identifiability, and the triple-consent requirement.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import FrozenSet, Optional, Tuple


@dataclass(frozen=True)
class ConceptRecord:
    """P-002 A14: definition record (intension, extension enumeration)."""

    concept_id: str
    intension: str
    extension: Tuple[str, ...]


@dataclass(frozen=True)
class ConceptAsDataset:
    """P-002: concept = definition dataset + computation rule binding."""

    definition: ConceptRecord
    computation_rule_id: str

    @property
    def identity(self) -> Tuple[str, str]:
        return (self.definition.concept_id, self.computation_rule_id)


def concepts_identical(a: ConceptAsDataset, b: ConceptAsDataset) -> bool:
    """Identity is the (definition, rule) pair — nothing looser."""

    return a.identity == b.identity


@dataclass(frozen=True)
class LegalTermBinding:
    """P-003 A18: canonical term bound to a definition within a jurisdiction."""

    term: str
    definition_id: str
    jurisdiction: str


def canonical_term(
    bindings: Tuple[LegalTermBinding, ...], definition_id: str, jurisdiction: str
) -> Optional[str]:
    """At most one canonical term per (definition, jurisdiction)."""

    matches = [b.term for b in bindings if b.definition_id == definition_id and b.jurisdiction == jurisdiction]
    if len(matches) != 1:
        return None  # zero or duplicate bindings: not canonical
    return matches[0]


@dataclass(frozen=True)
class TermTranslation:
    """P-003: translation preserves the definition id (meaning is carried)."""

    term_from: str
    term_to: str
    definition_id: str


def translation_preserves_meaning(
    t: TermTranslation, source_binding: LegalTermBinding, target_binding: LegalTermBinding
) -> bool:
    return (
        source_binding.definition_id == t.definition_id
        and target_binding.definition_id == t.definition_id
    )


@dataclass(frozen=True)
class ConceptVersionEntry:
    """P-009 A19: registered concept change with an explicit version."""

    concept_id: str
    version: int
    registered_object: str


def register_concept_version(
    registry: Tuple[ConceptVersionEntry, ...], entry: ConceptVersionEntry
) -> Tuple[ConceptVersionEntry, ...]:
    """New objects enter by registration with a strictly increasing version."""

    existing = [e for e in registry if e.concept_id == entry.concept_id]
    if existing and max(e.version for e in existing) >= entry.version:
        raise ValueError("concept version must strictly increase")
    return registry + (entry,)


class InfoPath(str, Enum):
    """P-010 A20: personal-information identification paths."""

    IDENTIFICATION = "IDENTIFICATION"
    RELATION = "RELATION"


@dataclass(frozen=True)
class PersonalInfo:
    """P-010: an information item with its paths, sensitivity, consents."""

    item_id: str
    paths: FrozenSet[InfoPath]
    anonymized: bool = False
    sensitive: bool = False
    consents: FrozenSet[str] = frozenset()

    @property
    def is_personal(self) -> bool:
        """Personal iff identifiable (un-anonymized) via any path."""

        return bool(self.paths) and not self.anonymized


def anonymize(info: PersonalInfo) -> PersonalInfo:
    """Anonymization removes identifiability — the item leaves the personal set."""

    from dataclasses import replace

    return replace(info, anonymized=True)


TRIPLE_CONSENT = frozenset({"inform", "express_intent", "lawful_purpose"})


def processing_requires_triple_consent(info: PersonalInfo) -> bool:
    """Sensitive personal information requires the full triple consent."""

    if not info.is_personal:
        return False
    return info.sensitive and info.consents >= TRIPLE_CONSENT


class RelationKind(str, Enum):
    """P-036 A34: the relation-type spectrum (债/物/亲属/劳动/继承)."""

    OBLIGATIONAL = "OBLIGATIONAL"
    REAL = "REAL"
    FAMILY = "FAMILY"
    LABOR = "LABOR"
    INHERITANCE = "INHERITANCE"


def classify_relation(kind: RelationKind, against_person: bool, against_world: bool) -> str:
    """Cross-check the declared family against its structural signature:
    obligational rights are against persons, real rights against the world;
    a mismatch flags the classification rather than silently passing."""

    if kind is RelationKind.OBLIGATIONAL and not against_person:
        return "MISMATCH"
    if kind is RelationKind.REAL and not against_world:
        return "MISMATCH"
    return "OK"
