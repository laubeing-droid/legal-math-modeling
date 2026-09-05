import JurisLean.HornDefinitions
import JurisLean.HornFixedPoint

/-!
Horn operational refinement boundary.

The Lean Horn specification proves finite fixed-point properties. It does not prove that
an external Python evaluator implements those properties. A cross-implementation claim
requires a `RuntimeRefinementReceipt` produced by the external runtime's formal entrypoint
and independently checked against a content-addressed expected fixture.

Missing receipts, commit or digest mismatches, execution failures, unknown status mappings,
timeouts, and truncated results are fail-closed. A successful receipt is limited to the
named LMM commit, runtime commit, fixture, source snapshot, rule pack, and output digest.
It cannot be generalized into a claim of complete runtime refinement.
-/
