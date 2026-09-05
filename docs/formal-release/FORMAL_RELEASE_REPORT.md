# Formal Release Protocol

## Purpose

The full-release workflow turns separately produced Lean, Python, mutation, runtime, and provenance evidence into one commit-bound decision. GitHub Actions is the only Lean execution authority for this repository.

## Required sequence

1. Check out the subject commit and record `ci-run-identity.json` before certificate generation.
2. Generate the complete Lean source-module matrix from the checked-out tree.
3. Run every module target and a separate `lake clean && lake build` with shell `pipefail` enabled.
4. Run Lean guards and the base, ULM all-theorem, and ULM core-composition axiom audits.
5. Collect and run the full Python test suite.
6. Run the controlled mutation gate and cross-repository runtime-refinement fixtures.
7. Run the forbidden-claim audit.
8. Generate `formal-release-certificate.json` from the evidence for that subject.
9. Independently verify the certificate and produce `independent-verifier-report.json`.
10. Let the final gate compare the certificate, verifier, job results, and subject identity.

An early certificate, a missing subject SHA, a missing report, a verifier disagreement, a swallowed command failure, or mixed evidence from different commits blocks release.

## Status interpretation

`RELEASE_PASS_PENDING_INDEPENDENT_VERIFICATION` is the certificate generator's successful pre-verifier state. `VERIFIED_PENDING_RELEASE_GATE` is the independent verifier's successful pre-final-gate state. Neither string alone means release. The final gate must confirm their agreement and succeed.

Any `RELEASE_BLOCKED_*`, `VERIFICATION_FAILED`, missing evidence, subject mismatch, skipped mandatory gate, cancelled run, or timed-out run is fail-closed.

## Authority

The implementation is defined by:

- [the workflow](../../.github/workflows/lean-build.yml);
- `scripts/generate_formal_release_certificate.py`;
- `scripts/verify_formal_release_certificate.py`;
- `scripts/run_mutation_property_gate.py`;
- `scripts/verify_runtime_refinement_receipt.py`;
- [certificate schema v2](CERTIFICATE_SCHEMA_V2.md).

The latest documented immutable result is [run 33946211096](FINAL_FORMAL_RELEASE_REPORT.md). Always distinguish that snapshot from the current branch or working tree.
