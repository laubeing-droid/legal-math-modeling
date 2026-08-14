# Axiom Audit Boundary

`JurisLean/AxiomAudit.lean` is the declaration list for the release gate. The raw
`lake env lean JurisLean/AxiomAudit.lean` output is generated per subject commit and
stored beside its `FormalReleaseCertificate`; raw output is not committed into the
commit it certifies.

The audit covers the finite monotone, Dung, Horn, weighted-distance, DDL,
certificate-checker, Horn-to-AAF, four-slice safety, and end-to-end public boundary.
It does not prove Python, SHA-256, external runtimes, source authority, or legal
correctness.

Allowed trusted Lean foundations are recorded in each certificate. `sorryAx`, an
unlisted audit target, a missing raw log, or a nonzero command exit keeps the release
status fail-closed.
