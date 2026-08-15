# Task Plan: Full Absorption of Frozen Theory (2026-08-15 Construction Plan)

## Goal

Execute `20260815_legal-math-modeling理论成果全量吸收施工方案.md` wave by wave
(M0 through M10). Build the complete formal foundation demanded by frozen research
P01-P09: canonical semantics v2, source/path/temporal contracts, three-gate admission
with taint noninterference, full DDL/argumentation semantics, exact numeric and
multi-backend contracts, the LegalSpec -> Legal-IVL dual IR with per-hop translation
witnesses, authority/proposal noninterference, CertificateEnvelopeV2 with independent
checkers, external runtime refinement, and a commit-bound formal release certificate.

## Success Criteria

- Every wave Gate passes or is explicitly recorded as blocked with its blocker.
- The four pre-existing red test modules close with real implementations.
- Lean modules are written without `sorry`/`admit`/`axiom`/`True`-theorem evasion;
  unproven obligations stay declared with `UNPROVED` status.
- Local Lean execution never happens; GitHub Actions is the only Lean authority.
  Until CI runs on the subject commit, Lean build status is `CI_NOT_RUN` (fail-closed).
- Python contract/mutation suites pass locally and are reproduced in CI.
- No prohibited claim is introduced; evidence domains stay separated.

## Phases

| Phase | Scope | Verification | Status |
|---|---|---|---|
| M0 | Baseline, inventory, red-test triage, authority map, supersession, CI-authority docs | git facts; local collection manifest; guard scan | complete |
| M1 | IDs, digests, well-formedness, canonicalization (Lean + canonical v2) | round-trip/mutation tests; manifest parity | in_progress |
| M2 | P02/P06/P08 source bundle, source path, temporal applicability | boundary/version/retraction mutation tests | pending |
| M3 | P09 three-gate admission, taint noninterference, receipt authority | injection/replay/revocation mutation tests | pending |
| M4 | P03 typed attacks, exceptions, permissions, priorities, cycles | finite enumeration oracle alignment | pending |
| M5 | P04 exact numeric, temporal arithmetic, multi-backend/solver contracts | boundary/rounding/timeout mutation tests | pending |
| M6 | P07 LegalSpec/Legal-IVL dual IR, lowerings, translation refinement | per-hop witness checks; differential tests | pending |
| M7 | P01/P05 authority lattice, human receipts, proposal noninterference | laundering/injection mutation tests | pending |
| M8 | CertificateEnvelopeV2 + independent checkers, evidence domains | v2 mutation suite green; Lean checker theorems | pending |
| M9 | External runtime refinement with three-party separation | receipt binding/mismatch classification | pending |
| M10 | CI reconstruction, FormalReleaseCertificate, release Gate | CI artifacts bound to subject SHA/tree | pending |

## Scope Decisions

- Proven core modules stay untouched; extension happens via new modules and embeddings.
- Lean runs only in GitHub Actions; local static checks are labelled provisional.
- New Lean modules join the root `JurisLean.lean` only after a CI module build passes;
  until then they are built through the CI module matrix.
- No push/tag/release without explicit per-round user authorization.
- Every phase boundary gets a local checkpoint commit; no hard resets.
- UNKNOWN/TIMEOUT/SKIP/NOT_RUN/BACKEND_UNAVAILABLE/ERROR all fail-closed.

## Errors Encountered

| Error | Attempt | Resolution |
|---|---:|---|
| Four test modules failed collection due to missing implementations | 1 | Confirmed the failures are missing-implementation, not environment; implemented the modules |

## Current Decision Point

M0 closed locally: baseline facts recorded, red tests closed (36 passed), guard scan
clean, authority map written, old plan marked superseded. M1 begins with canonical v2
and the identity/digest Lean modules. Lean build evidence remains `CI_NOT_RUN` until
the user authorizes a `ci/**` push or `workflow_dispatch`.
