# Proof Artifacts

This directory separates formal Lean sources, bounded engineering checks, and historical verification records.

| Directory | Role | Correct interpretation |
|---|---|---|
| `lean/juris_lean/` | Lean project and theorem sources | Formal statements are authoritative only at a cited commit with CI elaboration evidence |
| `engineering_proof_artifacts/` | Python, SMT, symbolic, and finite-enumeration artifacts | Bounded engineering evidence; not automatically a Lean proof |
| `strict_proof_baseline/` | Earlier theorem statements, counterexamples, and executable baselines | Scope-specific research record; check each artifact's status |
| `formal_verification_logs/` | 2026-06 experiment plans and reports | Historical evidence, not current release authority |

## Local checks

Python artifacts may be run locally according to their own README and dependency contract. Static Lean guards may also run locally:

```bash
python scripts/scan_lean_guards.py proofs/lean/juris_lean/JurisLean
```

Lean, Elan, and Lake must not be installed or executed locally for this repository. Module elaboration, clean build, and axiom audits run only in GitHub Actions. The latest documented immutable CI result is [run 33946211096](../docs/formal-release/FINAL_FORMAL_RELEASE_REPORT.md).

## Trust rule

Finite enumeration, SMT, symbolic algebra, regression tests, and receipts retain their own evidence class. None may be relabeled as a universal Lean theorem or as legal correctness. When a historical count or status conflicts with current source-bound CI evidence, use the latter.
