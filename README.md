# Legal Math Modeling

`legal-math-modeling` is a source-bounded formal specification repository for selected legal-reasoning structures. Lean proves statements about the models written here; it does not prove that an entire legal system, production runtime, or legal conclusion is correct.

## Verified snapshot

The latest immutable full-release evidence described by this documentation is GitHub Actions run [34669383636](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/34669383636), attempt 1, for subject commit `013aadbf289b6f331f625b2aeacdba591fae0a0b` and tree `52add31192dbfd0e3c093bca5c2a6b754528e880`. See the [landing report](docs/formal-release/SEVEN_AXIS_LANDING_REPORT_20260911.md).

That run completed the single-authority release pipeline with all gates green (the dispatch-only `changed-modules` feedback job skips on push by design). Its content-level evidence records:

- 94 Lean source files and 476 theorem declarations in the certificate inventory;
- a clean build of all 121 project modules, with mathlib v4.30.0 precompiled artifacts from the official cloud cache;
- the seven-axis audit recording 206 compiled declarations, with a compile-time root-type assertion over 18 required names, and only `propext`, `Classical.choice`, and `Quot.sound` reported across all recorded theorems (no `sorryAx`, no `native_decide`);
- typed observation fixtures regenerated from actual parsed Python fixture bytes in the same run, diffed clean before compilation;
- Python gates and three cross-repository runtime-refinement fixtures green in the same run;
- certificate status `RELEASE_PASS_PENDING_INDEPENDENT_VERIFICATION`, verifier verdict `VERIFIED_PENDING_RELEASE_GATE` with no error codes, and a successful final gate.

This snapshot adds the seven-axis fixed-input business root and its typed observation language to the previously recorded numeric-root evidence; the earlier snapshot (run `33946211096`, recorded in [FINAL_FORMAL_RELEASE_REPORT.md](docs/formal-release/FINAL_FORMAL_RELEASE_REPORT.md)) remains the closed historical record for its own subject. The final-gate result closes that run's release pipeline; it does not certify later commits. GitHub artifact retention is finite, so the run URL is evidence location, not a permanent archive.

## What is modeled

The repository contains:

- an 11-type v1 compatibility schema and a 48-type layered v2 registry;
- four deontic modalities: obligation, prohibition, permission, and constitutive;
- bounded contract-breach, fact-admission, permission, priority, translation, certificate, and runtime-refinement contracts;
- ULM01–ULM16 Lean theories and explicit axiom-audit entry points;
- a seven-axis fixed-input business root binding complete typed observations of two actual files to the proved numeric root (`JurisLean.BusinessRoot.SevenAxis`);
- Python checkers, release-certificate generators, controlled mutation fixtures, and cross-repository receipt verification;
- a formula-bearing [paper corpus](paper/README.md).

## Evidence boundary

Evidence is separated by layer:

1. Lean source and CI elaboration establish only the named formal statements.
2. Axiom-audit output discloses dependencies; it is not a proof by itself.
3. Python tests, mutation checks, and runtime receipts establish bounded engineering behavior for their fixtures.
4. The certificate and independent verifier bind those artifacts to one subject commit and tree.
5. Legal authority, source completeness, empirical validity, and the correctness of a real legal outcome remain outside the formal certificate unless separately evidenced.

Unknown, skipped, timed-out, unavailable, mismatched, or stale evidence is fail-closed.

## Verification

Local checks may run Python and static guards only:

```bash
python -m pytest -q -p no:cacheprovider
python scripts/scan_lean_guards.py proofs/lean/juris_lean/JurisLean
```

Lean, Elan, and Lake must not run locally for this repository. GitHub Actions is the sole Lean authority:

```bash
gh workflow run lean-build.yml --ref <commit-or-branch> -f mode=full-release
```

Do not infer success from a green workflow alone. Read the certificate subject and status, verifier verdict, axiom output, claim audit, mutation report, runtime receipt, and final-gate result for the same `head_sha`.

## Documentation

- [Chinese README](README_CN.md)
- [Documentation index](docs/INDEX.md)
- [Immutable release evidence](docs/formal-release/FINAL_FORMAL_RELEASE_REPORT.md)
- [Release protocol](docs/formal-release/FORMAL_RELEASE_REPORT.md)
- [Allowed claims](docs/formal-release/ALLOWED_CLAIMS.md) and [forbidden claims](docs/formal-release/FORBIDDEN_CLAIMS.md)
- [Canonical schema](docs/spec/canonical_legal_schema.md)
- [DDL core](docs/spec/ddl_minimal_core.md)
- [Horn-to-AAF contract](docs/spec/horn_to_aaf_contract.md)
- [Certificate checker boundary](docs/spec/certificate_checker_boundary.md)
- [Public/private boundary](docs/disclosure/PUBLIC_PRIVATE_BOUNDARY.md)

## Repository layout

```text
docs/          current documentation, release evidence, and bounded specifications
paper/         rewritten formula-bearing manuscripts and LaTeX sources
proofs/        Lean sources and engineering proof artifacts
runtime/       machine-readable refinement fixtures
scripts/       audit, certificate, mutation, and CI helpers
tests/         Python tests
theory/        executable schema and semantics modules
verification/  verification helpers
reports/       archived generated reports; not current authority
```

The repository is licensed under [CC BY 4.0](LICENSE). Cite the exact commit used; see [CITATION.cff](CITATION.cff).
