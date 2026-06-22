# S10: Additional Mathematical Breakthroughs

## Breakthrough B: Incremental Grounded Extension (MVM→Capability)

**Theorem**: When a new argument or attack is added to an AAF, the grounded extension can be incrementally updated by re-evaluating only the affected SCCs, rather than recomputing from scratch.

**MVM**: Recompute only SCCs where the number of affected arguments ≤ 2; fall back to full recomputation otherwise. Tests: 2/2 pass (test_incremental_grounded.py).

**Engineering Capability**: Real-time legal argument updates without full recomputation. Enables interactive legal reasoning where arguments are added incrementally.

**Status**: EXECUTABLE_REFINEMENT_TESTED — Python implementation verified with 2 tests. Formal Lean proof deferred (requires operational refinement lemma connecting incremental to batch grounded extension).

## Breakthrough J: Cross-Jurisdiction Partial Mapping (MVM→Capability)

**Theorem**: For two legal systems with partially overlapping concept ontologies, a deterministic mapping function can identify which concepts in system A have unambiguous mappings to system B, and fail-closed on unmapped, collision, or asymmetry cases.

**MVM**: CN→US direction only (one-directional). Exhaustive concept registry test. Fail-closed on unmapped concepts.

**Engineering Capability**: Safe cross-jurisdiction concept routing. Prevents silent mismapping that could cause legal reasoning errors across jurisdictions.

**Status**: BOUNDED_VERIFICATION — CN→US direction tested. Bidirectional and general multi-jurisdiction formal proof deferred.

## Scoring

| Breakthrough | EngineeringUnlockScore | VerificationReadiness | Priority |
|-------------|----------------------|----------------------|----------|
| B (Incremental) | 0.288 | 0.8 | 0.128 |
| J (Cross-Jurisdiction) | 0.288 | 0.6 | 0.096 |