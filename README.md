# Legal Math Modeling

Status: release-bounded public specification repository, rewritten on 2026-07-01.

## What This Repository Is

`legal-math-modeling` is the mathematical companion and specification boundary for selected legal-reasoning structures. It is not a runtime certificate for a complete deployed system.

## Current Public Boundary

The public boundary covers:

- 11 canonical legal types: LegalFact, LegalRule, LegalNorm, LegalClaim, Argument, Attack, Priority, Violation, Reparation, DecisionStatus, ProofTrace.
- 4 DDL modalities: OBLIGATION, PROHIBITION, PERMISSION, CONSTITUTIVE.
- 4 slices: contract breach, license, permission, priority.
- A minimal DDL core, a Horn-to-AAF compiler contract, and a certificate/checker boundary.
- Lean source inventory under `proofs/lean/juris_lean/JurisLean/`.

At rewrite time the Lean source tree contains 32 files and 126 theorem declarations. This is a source inventory fact, not a current-head release certificate.

## Evidence Discipline

Formal claims require Lean source plus current build evidence. Engineering claims require tests or certificate-checker evidence. Narrative papers and generated reports are explanatory only. Unknown, skipped, timed-out, unavailable, or stale evidence is fail-closed.

## Read Order

1. `docs/formal-release/FORMAL_RELEASE_REPORT.md`
2. `docs/formal-release/theorem_manifest.json`
3. `docs/spec/canonical_legal_schema.md`
4. `docs/spec/ddl_minimal_core.md`
5. `docs/spec/horn_to_aaf_contract.md`
6. `docs/spec/certificate_checker_boundary.md`
7. `docs/disclosure/PUBLIC_PRIVATE_BOUNDARY.md`
8. `paper/README.md`

## Repository Layout

```text
docs/          rewritten public documentation and manifests
paper/         rewritten papers and LaTeX sources
proofs/        Lean and engineering proof artifacts
runtime/       machine runtime fixtures; not prose documentation
scripts/       helper scripts
tests/         Python tests
theory/        Python theory/spec modules
verification/  verification helpers
reports/       archived generated analysis reports
```

## Public/Private Split

The public repository keeps the auditable specification kernel and public explanatory material. Customer data, commercial rule libraries, lawyer workflows, litigation strategy, and private benchmarks stay out of the public repository by default.

## Commands

```bash
python -m pytest -q
python scripts/scan_lean_guards.py proofs/lean/juris_lean/JurisLean
cd proofs/lean/juris_lean && lake build
```

Run commands on the relevant commit before making release claims.
