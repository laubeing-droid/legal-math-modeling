# Runtime Refinement Cases (M9)

Three-party separation:

1. LMM generates content-addressed expected fixtures, formal semantics
   versions, and reference results (this directory).
2. JC executes the same cases through its formal public entry and emits
   actual runtime receipts bound to its own commit/tree/build. Receipts
   are CI artifacts; they are never committed here.
3. LMM's independent verifier (`scripts/verify_runtime_refinement_receipt.py`)
   compares expected and actual. Deli may propose new counterexamples but
   cannot rewrite either side.

Rules:

- Never modify an expected fixture to match an actual result; mismatches
  become classified counterexamples with an authority owner and a
  regression test.
- Missing receipts, commit/digest mismatches, unknown mappings, and
  execution errors are blocked (fail-closed), never green.
- `subject_commit_binding` fields marked `CI_SUBJECT_SHA` are bound by CI
  at materialization time to the exact subject commit; local placeholders
  are not evidence.

Mismatch classification: `SPEC_MISMATCH`, `IMPLEMENTATION_MISMATCH`,
`TRANSLATION_MISMATCH`, `PROJECTION_MISMATCH`, `ORACLE_UNRESOLVED`,
`ENVIRONMENT_BLOCKED`.

Fixture manifest:

| File | Coverage |
|---|---|
| `contract_breach.expected.json` | positive/negative contract slice (P03/P04) |
| `fact_admission.expected.json` | three-gate admission and revocation (P09) |
| `unknown_timeout.expected.json` | UNKNOWN/TIMEOUT fail-closed mapping (P04) |
