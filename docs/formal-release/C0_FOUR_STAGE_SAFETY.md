# C0: Four-Stage No-Uncertainty-Upgrade Specification

**Date:** 2026-06-28
**Status:** FROZEN
**Authority:** `legal-math-modeling` (this repo)

---

## 1. Purpose

This document specifies the safety invariant that governs the four-stage
reasoning pipeline: **no stage may produce output more certain than its
input**. If an upstream stage is incomplete, truncated, or errored, the
downstream stage MUST NOT produce a definitive result.

---

## 2. CompletionStatus Enum

```python
from enum import Enum

class CompletionStatus(Enum):
    COMPLETE = "complete"
    TRUNCATED = "truncated"
    UNKNOWN = "unknown"
    ERROR = "error"
    INCOMPATIBLE = "incompatible"
    VERIFICATION_FAILED = "verification_failed"
```

---

## 3. StageResult

```python
from dataclasses import dataclass
from typing import Generic, TypeVar

T = TypeVar("T")
C = TypeVar("C")

@dataclass(frozen=True)
class StageResult(Generic[T, C]):
    status: CompletionStatus
    value: T | None
    certificate: C | None
    assumptions: tuple[str, ...]
    limitations: tuple[str, ...]
    input_digest: str
    producer_version: str
```

---

## 4. Core Property: no_uncertainty_upgrade

```
upstream status != COMPLETE
  => downstream MUST NOT produce definitive output
```

This is the central safety invariant. It ensures that uncertainty propagates
forward through the pipeline and is never silently discarded.

---

## 5. Trust Label Mapping

| Condition | Output Trust Label |
|-----------|-------------------|
| All stages COMPLETE, all certs valid | ALLOWED / FORBIDDEN / UNDECIDED |
| Horn TRUNCATED | INCOMPLETE_REASONING |
| AAF incomplete (missing args/attacks) | INCOMPLETE_ATTACK_GRAPH |
| Grounded unconverged | COMPUTATION_UNKNOWN |
| Certificate verification failed | VERIFICATION_FAILED |
| Source missing | UNGROUNDED_SOURCE |
| Protocol incompatible | INCOMPATIBLE_RESULT |

---

## 6. Prohibited Transitions

The following combinations are explicitly prohibited:

| Upstream Status | Prohibited Downstream Output |
|----------------|------------------------------|
| TRUNCATED | ALLOWED |
| UNKNOWN | HIGH_CONFIDENCE |
| VERIFICATION_FAILED | Silently ignored |
| Any non-COMPLETE | Definitive status via numerical score |

**Critical rule:** A numerical confidence score MUST NOT be used to upgrade
a logical status. If the logic layer says UNDECIDED, no numerical override
may promote it to ALLOWED.

---

## 7. Relationship to Lean Proven Properties

The four-stage pipeline composition itself is NOT Lean-proven. Each individual
stage has separate Lean proofs or Python verification:

| Stage | Lean-Proven? | Foundation |
|-------|-------------|------------|
| Horn Closure | YES | `HornFixedPoint.lean` (10 core theorems), `FiniteMonotoneIteration.lean` (9 core) |
| AAF Construction | Python-verified | `validate_horn_aaf_contract()` |
| Grounded Extension | YES | `DungFixedPoint.lean` (17 core theorems) |
| Certificate/Checker | Python-verified | Checker boundary spec (`certificate_checker_boundary.md`) |

The no-uncertainty-upgrade property is enforced by engineering contract,
not by a Lean theorem. The pipeline composition is an engineering invariant
that depends on the correct implementation of each stage's boundary checks.

---

## 8. Verification

```bash
# Verify Python CompletionStatus and StageResult exist
python -c "
from theory.spec.canonical_semantics import CompletionStatus, StageResult
print('CompletionStatus:', [e.name for e in CompletionStatus])
print('StageResult fields:', list(StageResult.__dataclass_fields__))
"

# Verify Lean stages build independently
cd proofs/lean/juris_lean && lake build JurisLean
```
