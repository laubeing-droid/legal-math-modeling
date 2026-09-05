# Program Plan

This is a durable work map, not a live release dashboard. Exact current status comes from source and commit-bound CI artifacts.

## Closed in the documented release subject

- ULM01–ULM16 module elaboration and clean build;
- all-theorem and core-composition axiom audits;
- certificate timing, subject binding, independent verification, and final gate;
- controlled checker-input mutation gate;
- executable receipt generation and verification for three runtime-refinement fixtures.

Evidence: [Final Formal Release Report](../docs/formal-release/FINAL_FORMAL_RELEASE_REPORT.md).

## Open research and engineering work

- add representative counterexamples and runtime fixtures without broadening existing claims;
- prove or refute additional translation, incremental-computation, minimal-support, and Banach propositions as separately named targets;
- expand empirical validation only with provenance and explicit sampling limits;
- preserve v1 compatibility while keeping v2 decisive semantics fail-closed;
- archive durable copies of release evidence before hosted artifacts expire.

## Completion rule

A target closes only when its statement, implementation or proof, independent verification, failure behavior, commit/digest binding, and limitations are all present. Work on one track cannot compensate for a missing gate on another.

Lean runs only in GitHub Actions. Local verification is limited to Python tests, static guards, documentation checks, and Git inspection.
