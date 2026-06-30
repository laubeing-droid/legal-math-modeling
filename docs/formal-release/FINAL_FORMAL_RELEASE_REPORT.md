# FINAL_FORMAL_RELEASE_REPORT

**Date:** 2026-07-01
**Release ID:** `formal-core-v1-plus-four-slices`
**Status:** `spec-first-transition-ready-plus-four-slices`

## Release Conclusion

Current approved public status:

| Dimension | Status |
|---|---|
| `formal_core_modules_status` | COMPLETE |
| `four_slice_vertical_status` | COMPLETE_IN_FORMAL_MODEL |
| `repository_formal_release_status` | LOCAL_EVIDENCE_COMPLETE |
| `banach_status` | UNPROVED_TRACK_B |
| `privacy_guarantee_status` | NOT_ESTABLISHED |
| `full_jc_runtime_lean_proof` | NOT_CLAIMED |

## Current Ground Truth Source

| Item | Value |
|---|---|
| Branch | `master` |
| Verification scope | Local-only Playbook scope; no push/tag/release |
| Lean source guard | 0 sorry / 0 admit / 0 custom axiom / 0 `theorem : True`; Lean built-in axiom dependencies disclosed by `AxiomAudit` |
| `lake build JurisLean` | 2961 jobs, 0 errors |
| Four-slice differential evidence | `runtime/legal_math_four_slice_differential.json` |

## Counting Policy

| Metric | Value | Source |
|---|---:|---|
| Lean source files | 32 | `theorem_manifest.json` |
| Core theorem declarations | 42 | `theorem_manifest.json` |
| Supporting theorem declarations | 84 | `theorem_manifest.json` |
| Total theorem declarations | 126 | `theorem_manifest.json` |
| Four-slice vertical results | 32 | `theorem_manifest.json` |

## Core Theorem Distribution

| File | Core theorems |
|---|---:|
| `DungFixedPoint.lean` | 16 |
| `HornFixedPoint.lean` | 10 |
| `FiniteMonotoneIteration.lean` | 9 |
| `WeightedSupNorm.lean` | 4 |
| `HornDefinitions.lean` | 2 |
| `ContractionCondition.lean` | 1 |
| **Total** | **42** |

## Four-Slice Modules

| File | Role |
|---|---|
| `LegalSyntax.lean` | canonical Lean types, stable serialization, DecisionStatus mapping, trust-label non-promotion |
| `DDLDefinitions.lean` | obligation/permission/prohibition/constitutive core, direct violation and priority ordering |
| `HornAAFContract.lean` | Horn derivation to argument, exception attack, priority defeat, unsupported-argument rejection |
| `AttackDecision.lean` | priority active/evidence/cycle/self-attack properties |
| `CertificateChecker.lean` | fail-closed certificate checker |
| `SafetyTheorems.lean` | candidate/tainted/missing-evidence safety layer |
| `EndToEnd.lean` | contract breach, license, permission, priority slice gates |

## Closed Release Gates

- Repository-level local `lake build` evidence gate
- `AxiomAudit` reproducibility gate
- Lean source guard gate
- Theorem manifest alignment gate
- Formal release documentation consistency gate
- Four-slice reference/shadow differential fixture gate

## Boundary

The following remain outside the release boundary:

- Full Lean proof of the `juris-calculus` Python runtime
- Full ASPIC+ formalization
- Banach complete fixed-point closure as a runtime claim
- Differential privacy guarantees
- Empirical calibration guarantees
- Litigation automation by this repository

## Recommended Public Statement

> This repository has completed repository-level formal release closure for the
> finite monotone iteration kernel, Dung grounded fixed-point layer, finite Horn
> closure layer, and four Lean vertical slices for contract breach, license,
> permission, and priority. The full `juris-calculus` runtime is not claimed as
> end-to-end Lean-proven.

## Related Documents

- [`FORMAL_RELEASE_REPORT.md`](FORMAL_RELEASE_REPORT.md)
- [`FORBIDDEN_CLAIMS.md`](FORBIDDEN_CLAIMS.md)
- [`ALLOWED_CLAIMS.md`](ALLOWED_CLAIMS.md)
- [`SPEC_FIRST_TRANSITION_READY.md`](SPEC_FIRST_TRANSITION_READY.md)
