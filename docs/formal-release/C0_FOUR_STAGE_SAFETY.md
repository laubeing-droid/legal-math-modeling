# CompletionStatus & StageResult -- Track C0 Four-Stage No-Uncertainty-Upgrade

## Specification

### CompletionStatus Enum

`python
from enum import Enum

class CompletionStatus(Enum):
    COMPLETE = "complete"
    TRUNCATED = "truncated"
    UNKNOWN = "unknown"
    ERROR = "error"
    INCOMPATIBLE = "incompatible"
    VERIFICATION_FAILED = "verification_failed"
`

### StageResult

`python
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
`

### Core Property: no_uncertainty_upgrade

`
upstream status != COMPLETE
=> downstream MUST NOT produce definitive output
`

### Trust Label Mapping

| Condition | Output |
|---|---|
| All stages COMPLETE, all certs valid | ALLOWED / FORBIDDEN / UNDECIDED |
| Horn TRUNCATED | INCOMPLETE_REASONING |
| AAF incomplete (missing args/attacks) | INCOMPLETE_ATTACK_GRAPH |
| Grounded unconverged | COMPUTATION_UNKNOWN |
| Certificate verification failed | VERIFICATION_FAILED |
| Source missing | UNGROUNDED_SOURCE |
| Protocol incompatible | INCOMPATIBLE_RESULT |

### Prohibited

- Upstream TRUNCATED + downstream ALLOWED
- Grounded UNKNOWN + Trust Label HIGH_CONFIDENCE
- Certificate mismatch silently ignored
- Numerical score used to upgrade logical status
