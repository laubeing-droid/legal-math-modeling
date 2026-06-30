# FINAL_FORMAL_RELEASE_REPORT

**Date:** 2026-06-28
**Release ID:** `formal-core-v1`
**Status:** `spec-first-transition-ready`

---

## 1. Release Conclusion

Current approved public status:

| Dimension | Status |
|-----------|--------|
| `formal_core_modules_status` | COMPLETE |
| `repository_formal_release_status` | COMPLETE |
| `banach_status` | UNPROVED_TRACK_B |
| `empirical_calibration_status` | DATA_BLOCKED |
| `privacy_guarantee_status` | NOT_ESTABLISHED |

This means:

1. The formal core modules (finite monotone iteration, Dung grounded fixed-point,
   finite Horn closure) are complete and released.
2. The repository-level formal release gate is closed.
3. Banach is NOT mixed into the formal core completion claim.

---

## 2. Current Ground Truth Source

| Item | Value |
|------|-------|
| Public branch model | `master` only |
| Last verified source head | `f671a6e` |
| Last clean rebuild evidence | `f671a6e` |
| GitHub Actions clean build | PASS at `f671a6e` |
| Lean source guard | 0 sorry / 0 admit / 0 custom axiom / 0 `theorem : True`; Lean built-in axiom dependencies disclosed by `AxiomAudit` |
| `AxiomAudit` | Reproducible |
| `lake build JurisLean` | 2954 jobs, 0 errors |

---

## 3. Counting Policy

| Metric | Value | Source |
|--------|-------|--------|
| Unique theorem names | 94 | `theorem_manifest.json` |
| Core theorems | 43 | `theorem_manifest.json` |
| Supporting unique theorem names | 51 | `theorem_manifest.json` |
| Supporting manifest records | 57 | `theorem_manifest.json` |
| Total manifest entries | 100 | `theorem_manifest.json` |
| `formal_core_module_theorems` | 43 | `theorem_manifest.json` |

### Core theorem distribution by file:

| File | Core theorems |
|------|--------------|
| `DungFixedPoint.lean` | 17 |
| `HornFixedPoint.lean` | 10 |
| `FiniteMonotoneIteration.lean` | 9 |
| `WeightedSupNorm.lean` | 4 |
| `HornDefinitions.lean` | 2 |
| `ContractionCondition.lean` | 1 |
| **Total** | **43** |

---

## 4. Closed Release Gates

The following gates are closed:

- Repository-level clean build evidence gate
- `AxiomAudit` reproducibility gate
- Lean source guard gate (0 sorry / 0 admit / 0 custom axiom, with Lean built-in axiom dependencies disclosed by `AxiomAudit`)
- Theorem manifest alignment gate
- Formal release documentation consistency gate

---

## 5. Five Spec-First Transition Gates

| Gate | Document | Status |
|------|----------|--------|
| M1: Canonical Schema | `docs/spec/canonical_legal_schema.md` | SUBSTANTIAL_PARTIAL |
| M2: DDL Minimal Core | `docs/spec/ddl_minimal_core.md` | SUBSTANTIAL_PARTIAL |
| M3: Horn -> AAF Contract | `docs/spec/horn_to_aaf_contract.md` | SUBSTANTIAL_PARTIAL |
| M4: Certificate/Checker Boundary | `docs/spec/certificate_checker_boundary.md` | PARTIAL |
| M5: Unified Stopping Statement | `SPEC_FIRST_TRANSITION_READY.md` | CLOSED |

Overall: All five gates are ACCEPTABLE or CLOSED.

---

## 6. Boundary: What Must NOT Be Claimed

The following remain outside the release boundary:

- Banach complete fixed-point closure
- Full Lean proof of the `juris-calculus` Python runtime
- Differential privacy guarantees
- Empirical calibration of constants
- Litigation automation by this repository

See `FORBIDDEN_CLAIMS.md` for the complete list.

---

## 7. Banach Correct Position

Banach is currently in archived research status only:

- NOT part of `formal-core-v1`
- No active release branch retained
- Historical traceability preserved via archive tags only

Archive tags:

- `archive/banach-track-b-d23e8f2`
- `archive/track-c-prod-f43e273`

---

## 8. Existing Lean Files (25 Files)

All 25 Lean files that exist in `proofs/lean/juris_lean/JurisLean/`:

| File | Core | Supporting | Category |
|------|------|-----------|----------|
| `AxiomAudit.lean` | 0 | 0 | Audit infrastructure |
| `BanachCertificate.lean` | 0 | 0 | Banach (archived) |
| `BanachComplete.lean` | 0 | 0 | Banach (archived) |
| `BanachContraction.lean` | 0 | 2 | Banach (archived) |
| `BanachEffectiveNodes.lean` | 0 | 8 | Banach (archived) |
| `BanachFixedPoint.lean` | 0 | 1 | Banach (archived) |
| `BanachScratch.lean` | 0 | 0 | Banach (archived) |
| `BanachWeightedNorm.lean` | 0 | 0 | Banach (archived) |
| `Basic.lean` | 0 | 0 | Shared utilities |
| `ContractionCondition.lean` | 1 | 0 | Core |
| `DungAAF.lean` | 0 | 0 | AAF definitions |
| `DungDefinitions.lean` | 0 | 0 | Dung definitions |
| `DungFixedPoint.lean` | 17 | 0 | Core |
| `FiniteGaloisAdjunction.lean` | 0 | 2 | Supporting |
| `FiniteMonotoneIteration.lean` | 9 | 0 | Core |
| `FiniteRosetta.lean` | 0 | 9 | Supporting |
| `HornDefinitions.lean` | 2 | 0 | Core |
| `HornFixedPoint.lean` | 10 | 0 | Core |
| `HornOperationalRefinement.lean` | 0 | 0 | Supporting |
| `JC_Formalization.lean` | 0 | 12 | Supporting |
| `ScratchApi.lean` | 0 | 0 | Utilities |
| `SupZeroLemma.lean` | 0 | 1 | Supporting |
| `TemporalKripke.lean` | 0 | 6 | Supporting |
| `UnifiedModel.lean` | 0 | 16 | Standalone (NOT canonical) |
| `WeightedSupNorm.lean` | 4 | 0 | Core |

---

## 9. Recommended Public Statement

> This repository has completed repository-level formal release closure for
> the finite monotone iteration kernel, Dung grounded fixed-point layer, and
> finite Horn closure layer. Banach remains an independent unproved research track.

---

## 10. Related Documents

- [`FORMAL_RELEASE_REPORT.md`](FORMAL_RELEASE_REPORT.md)
- [`FORBIDDEN_CLAIMS.md`](FORBIDDEN_CLAIMS.md)
- [`ALLOWED_CLAIMS.md`](ALLOWED_CLAIMS.md)
- [`SPEC_FIRST_TRANSITION_READY.md`](SPEC_FIRST_TRANSITION_READY.md)
