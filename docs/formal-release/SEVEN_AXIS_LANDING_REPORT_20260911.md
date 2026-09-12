# Immutable Evidence Snapshot — 2026-09-11 Landing

Current documented immutable snapshot: GitHub Actions run [34669383636](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/34669383636), attempt 1, for subject commit `013aadbf289b6f331f625b2aeacdba591fae0a0b` and tree `52add31192dbfd0e3c093bca5c2a6b754528e880` on `main`. The first green run of this same subject (same tree) was run [34648379461](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/34648379461) on branch `ci/ulm-seven-axis-20260911`; its receipt binds the identical commit and tree.

The prior snapshot (run `33946211096`, subject `2a1d33df353a005dffc5d8b95faa591524e2636e`) remains recorded in [FINAL_FORMAL_RELEASE_REPORT.md](FINAL_FORMAL_RELEASE_REPORT.md) as a closed historical record and is not superseded content-wise; it simply no longer describes the repository head.

## Pipeline result

The single-authority workflow ("Lean Authority + Formal Release Pipeline") completed with all seven jobs green; the `changed-modules` job is dispatch-only feedback and skips on push by design:

| Job | Result |
|---|---|
| python-gates | success |
| lean-full-clean-build | success |
| runtime-refinement / produce | success |
| changed-modules | skipped (by design on push) |
| seven-axis-acceptance | success |
| release-certificate | success |
| final-gate | success |

## Certificate inventory

From the release certificate of run 34669383636 (same subject):

- 94 Lean source files and 476 theorem declarations inventoried;
- certificate status `RELEASE_PASS_PENDING_INDEPENDENT_VERIFICATION`;
- independent verifier verdict `VERIFIED_PENDING_RELEASE_GATE` with no error codes;
- the final gate closed the same subject's release pipeline.

## Seven-axis landing scope

This subject adds `JurisLean.BusinessRoot.SevenAxis` (full-input binding around the previously proved numeric root), its typed observation fixture, and a compile-time root-type assertion:

- the seven-axis audit records 206 compiled declarations; 18 required names verified by a compile-time type assertion, not just presence;
- every recorded theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`, no `native_decide`, no additional axioms;
- typed fixtures are regenerated from actual parsed Python fixture bytes in the same run and must diff clean before compilation;
- the Lean build compiled all 121 project modules from a clean project build; mathlib v4.30.0 precompiled artifacts came from the official mathlib cloud cache, with no `lake update`.

## What this run does and does not establish

Kernel-checked: the named statements of the typed observation language and the frozen fixed-input seven-axis root, plus full-field tamper regressions, at the cited commit and tree.

Not established by this run: a generic root over arbitrary inputs; production Juris-Calculus/Harness wiring; legal-authority review of candidate statutes; real win-rate calibration (no real data); a kernel-refined byte parser (Python byte-to-token correspondence remains a declared cross-check/TCB boundary).

Python-side suites (repaired-delta, retained reference, legacy-root cross-check, package/installer checks) ran green in the same run's python-gates job and in pre-push local runs; they remain bounded engineering evidence, not formal proof.
