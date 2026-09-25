#!/usr/bin/env python3
"""PR-01/PR-02/PR-03: win-rate event contract, retrieved-cohort estimation,
and forward/reverse comparison with flip witnesses.

PR-01 pins the five-element event definition (identity/cluster/objective/
group plus a temporal protocol) with target population, outcome variable and
observation mechanism explicit; anything missing is UNKNOWN, never a guessed
probability. PR-02 uses exactly the retrieved observed cohort as its
population and delegates the Beta interval to the existing
tools/unified_math_v2/unified/win_model.py (no interval mathematics is
copied here; the adapter is mechanical wiring over the real signature
``latent_rate_interval(model: WinModel, group: str, tail, steps)``).
PR-03 recomputes flipped scores through the scoring function; a flip
without a real feature change is rejected.
"""

from __future__ import annotations

import importlib
import sys
from dataclasses import dataclass
from enum import Enum
from fractions import Fraction
from pathlib import Path
from typing import Callable, Dict, Optional, Sequence, Tuple

from theory.spec.retrieval_v4 import ComparisonDirection, StructuralComparison

SYNTHETIC_IDENTITY = "SYNTHETIC_NOT_VALIDATED"
RETRIEVED_IDENTITY = "RETRIEVED_COHORT"
WIN_MODEL_PATH = Path("tools/unified_math_v2")
_WIN_MODEL_MODULE = None


class IdentificationStatus(str, Enum):
    IDENTIFIED = "IDENTIFIED"
    UNKNOWN = "UNKNOWN"


@dataclass(frozen=True)
class TemporalProtocol:
    """Time discipline mirroring win_model.Row's anti-leakage ordering."""

    split: str
    cutoff: str
    feature_latest: str
    outcome_time: str


@dataclass(frozen=True)
class WinEventDefinition:
    identity: str
    cluster: str
    objective: str
    group: str
    temporal: TemporalProtocol
    target_population: str
    outcome_variable: str
    observation_mechanism: str


@dataclass(frozen=True)
class IdentificationResult:
    status: IdentificationStatus
    reasons: Tuple[str, ...]


def identify_event(event: WinEventDefinition) -> IdentificationResult:
    """Five elements plus the three explicit observability fields; any gap
    means UNKNOWN — the pipeline must never guess a probability."""

    missing = [
        name
        for name, value in (
            ("identity", event.identity),
            ("cluster", event.cluster),
            ("objective", event.objective),
            ("group", event.group),
            ("split", event.temporal.split),
            ("cutoff", event.temporal.cutoff),
            ("feature_latest", event.temporal.feature_latest),
            ("outcome_time", event.temporal.outcome_time),
            ("target_population", event.target_population),
            ("outcome_variable", event.outcome_variable),
            ("observation_mechanism", event.observation_mechanism),
        )
        if not value.strip()
    ]
    if missing:
        return IdentificationResult(
            status=IdentificationStatus.UNKNOWN, reasons=tuple(missing)
        )
    return IdentificationResult(status=IdentificationStatus.IDENTIFIED, reasons=())


@dataclass(frozen=True)
class RetrievedOutcome:
    """One row of the retrieved cohort; unobserved rows never enter counts."""

    case_id: str
    observed: bool
    success: bool
    synthetic: bool = False


@dataclass(frozen=True)
class CohortFrequency:
    successes: int
    observed_total: int

    @property
    def frequency(self) -> Optional[Fraction]:
        if self.observed_total == 0:
            return None
        return Fraction(self.successes, self.observed_total)


@dataclass(frozen=True)
class ProbabilityEstimate:
    status: IdentificationStatus
    successes: int
    observed_total: int
    frequency: Optional[Fraction]
    interval_low: Optional[object]
    interval_high: Optional[object]
    identity: str


def observed_frequency(rows: Sequence[RetrievedOutcome]) -> CohortFrequency:
    """Population is exactly the retrieved observed rows."""

    observed = [row for row in rows if row.observed]
    return CohortFrequency(
        successes=sum(1 for row in observed if row.success),
        observed_total=len(observed),
    )


def load_win_model_module(repo_root: Path):
    """Import the existing win_model by path; interval math stays there."""

    global _WIN_MODEL_MODULE
    if _WIN_MODEL_MODULE is not None:
        return _WIN_MODEL_MODULE
    tools_root = (repo_root / WIN_MODEL_PATH).resolve()
    if str(tools_root) not in sys.path:
        sys.path.insert(0, str(tools_root))
    _WIN_MODEL_MODULE = importlib.import_module("unified.win_model")
    return _WIN_MODEL_MODULE


def call_existing_latent_rate_interval(
    *,
    event: WinEventDefinition,
    rows: Sequence[RetrievedOutcome],
    repo_root: Path,
):
    """Thin adapter over win_model.fit + latent_rate_interval.

    Builds training Rows from the retrieved observed cohort (labels are the
    observed outcomes), fits the existing model, and asks the existing
    interval function for the event's group. No Beta mathematics here.
    """

    win = load_win_model_module(repo_root)
    train_rows = tuple(
        win.Row(
            identity=row.case_id,
            cluster=f"cohort::{row.case_id}",
            objective=event.objective,
            group=event.group,
            split="train",
            cutoff=event.temporal.cutoff,
            feature_latest=event.temporal.feature_latest,
            outcome_time=event.temporal.outcome_time,
            label=1 if row.success else 0,
            source="retrieved_cohort",
            synthetic=row.synthetic,
        )
        for row in rows
        if row.observed
    )
    if not train_rows:
        raise ValueError("no observed rows to fit")
    model = win.fit(train_rows)
    return win.latent_rate_interval(model, event.group)


def estimate_retrieved_cohort(
    *,
    event: WinEventDefinition,
    rows: Sequence[RetrievedOutcome],
    repo_root: Path,
) -> ProbabilityEstimate:
    """Retrieved population -> realized frequency -> existing Beta interval.

    Unknown event or an empty observed cohort returns UNKNOWN with no
    interval; any synthetic row hard-marks the identity.
    """

    identification = identify_event(event)
    identity = (
        SYNTHETIC_IDENTITY
        if any(row.synthetic for row in rows)
        else RETRIEVED_IDENTITY
    )
    if identification.status is IdentificationStatus.UNKNOWN:
        return ProbabilityEstimate(
            status=IdentificationStatus.UNKNOWN,
            successes=0,
            observed_total=0,
            frequency=None,
            interval_low=None,
            interval_high=None,
            identity=identity,
        )

    freq = observed_frequency(rows)
    if freq.observed_total == 0:
        return ProbabilityEstimate(
            status=IdentificationStatus.UNKNOWN,
            successes=0,
            observed_total=0,
            frequency=None,
            interval_low=None,
            interval_high=None,
            identity=identity,
        )

    interval = call_existing_latent_rate_interval(
        event=event, rows=rows, repo_root=repo_root
    )
    return ProbabilityEstimate(
        status=IdentificationStatus.IDENTIFIED,
        successes=freq.successes,
        observed_total=freq.observed_total,
        frequency=freq.frequency,
        interval_low=interval["lo"],
        interval_high=interval["hi"],
        identity=identity,
    )


@dataclass(frozen=True)
class FlipWitness:
    """A flipped factor: it must name the feature, its before value (which
    must actually be present), and its after value."""

    factor: str
    before: object
    after: object


@dataclass(frozen=True)
class ComparisonReport:
    direction: ComparisonDirection
    base_score: object
    flipped_score: object
    flip_witnesses: Tuple[FlipWitness, ...]
    structural_comparison: StructuralComparison


def build_comparison_report(
    *,
    direction: ComparisonDirection,
    structural_comparison: StructuralComparison,
    base_features: Dict[str, object],
    flip_witnesses: Sequence[FlipWitness],
    score_fn: Callable[[Dict[str, object]], object],
) -> ComparisonReport:
    """Forward/reverse comparison; flipped scores are recomputed, not asserted."""

    base_score = score_fn(dict(base_features))
    changed = dict(base_features)
    for witness in flip_witnesses:
        if witness.factor not in changed:
            raise ValueError(f"flip factor not present: {witness.factor}")
        if changed[witness.factor] != witness.before:
            raise ValueError(f"flip witness before-value mismatch: {witness.factor}")
        changed[witness.factor] = witness.after
    flipped_score = score_fn(changed) if flip_witnesses else base_score
    return ComparisonReport(
        direction=direction,
        base_score=base_score,
        flipped_score=flipped_score,
        flip_witnesses=tuple(flip_witnesses),
        structural_comparison=structural_comparison,
    )
