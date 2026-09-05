# Certificate Checker Boundary

## Independent recomputation

`CertificateEnvelopeV2` is defined in `theory/spec/certificate_schema.py` and mirrored by `CertificateV2.lean` and `CertificateCheckerV2.lean`. The producer supplies evidence records, not trusted booleans such as `wellFormed`, `requiredFactsPresent`, or `proofObligationsPresent`. The checker recomputes acceptance predicates independently.

The envelope binds:

- expected and used facts;
- expected and discharged proof obligations;
- rules, arguments, attacks, and the accepted set;
- source snapshots and rule packs with recomputable content digests;
- semantics identity and version, a non-empty trace, producer commit, and checker identity.

Empty traces, unknown semantics or checkers, duplicate or unstable identifiers, tampered digests, stale snapshots, candidate evidence, and missing required evidence fail closed. V1 payloads may remain parseable but never gain v2 decisive status.

## Separate evidence domains

`LeanProofReceipt`, `FiniteModelCheckReceipt`, `SolverWitnessReceipt`, `TranslationReceipt`, `RuntimeRefinementReceipt`, `HumanLegalReviewReceipt`, and `FormalReleaseCertificate` have separate subjects, issuers, checkers, and allowed claims. A digest establishes content binding only. Overall status cannot exceed the weakest required evidence domain.

Runtime metadata can explain why an output is accepted, downgraded, blocked, or sent to review. It cannot promote disputed, hypothetical, tainted, user-assumed, or unverified input into a proved result.

## Verified snapshot

The Lean certificate modules, Python checker behavior, controlled mutation cases, certificate generation, independent verification, and final gate were exercised for subject `2a1d33df353a005dffc5d8b95faa591524e2636e` in [run 33946211096](../formal-release/FINAL_FORMAL_RELEASE_REPORT.md). That evidence is commit-bound and does not certify later changes.

Checker acceptance never means legal correctness, source completeness, or full runtime proof.
