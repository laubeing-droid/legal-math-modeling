# Program Goal

The repository's long-term goal is an auditable path from typed legal inputs to bounded reasoning outputs, with explicit separation among formal proof, executable verification, source authority, empirical evidence, and accountable legal judgment.

## Current release state

The latest documented formal-release pipeline passed for the exact subject in [run 33946211096](../docs/formal-release/FINAL_FORMAL_RELEASE_REPORT.md). That result covers its generated module inventory, clean build, axiom audits, Python suite, mutation gate, three runtime-refinement fixtures, certificate, independent verifier, and final gate. It is not a rolling status for later commits.

## Continuing tracks

- extend formal results only through explicit theorem statements and CI proof evidence;
- expand runtime-refinement coverage with executable fixtures and independently checked receipts;
- preserve certificate/checker independence and same-subject binding;
- treat incremental verification, minimal support, Banach extensions, privacy, calibration, and cross-jurisdiction mappings as separate claims until individually closed;
- route legal authority and legal correctness to source evidence and accountable human review.

## Rules

No `sorry`, `admit`, custom axiom, vacuous `True` theorem, or conclusion smuggled into premises. UNKNOWN, TIMEOUT, SKIP, missing evidence, and subject mismatch fail closed. Git tags, releases, force pushes, and production claims require separate authorization and evidence.
