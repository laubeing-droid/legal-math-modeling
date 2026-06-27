# Formal Core Release Report

**Date:** 2026-06-28
**Release ID:** `formal-core-v1`

---

## 1. Spec-First Transition Status

**Status:** `spec-first-transition-ready`

The five gates required for spec-first transition:

| Gate | Document | Status |
|------|----------|--------|
| M1: Canonical Schema | [`docs/spec/canonical_legal_schema.md`](../spec/canonical_legal_schema.md) | SUBSTANTIAL_PARTIAL |
| M2: DDL Minimal Core | [`docs/spec/ddl_minimal_core.md`](../spec/ddl_minimal_core.md) | SUBSTANTIAL_PARTIAL |
| M3: Horn -> AAF Contract | [`docs/spec/horn_to_aaf_contract.md`](../spec/horn_to_aaf_contract.md) | SUBSTANTIAL_PARTIAL |
| M4: Certificate/Checker Boundary | [`docs/spec/certificate_checker_boundary.md`](../spec/certificate_checker_boundary.md) | PARTIAL |
| M5: Unified Stopping Statement | This document + [`SPEC_FIRST_TRANSITION_READY.md`](SPEC_FIRST_TRANSITION_READY.md) | CLOSED |

After this point, main engineering effort shifts to `juris-calculus`.
New math work in this repo only as "support for JC new capabilities."

---

## 2. Public State

| Item | State |
|------|-------|
| Public branch model | `master` only |
| Repository head | `12470ac` |
| Last full clean rebuild evidence | `12470ac` |
| GitHub Actions clean build | PASS at `12470ac` |
| Local `lake build` evidence | PASS (2954 jobs, 0 errors) |
| Local `lake build +JurisLean.AxiomAudit` evidence | PASS |
| Lean source guard | PASS |

Lean source guard means:

- `0 sorry`
- `0 admit`
- `0 custom axiom`
- `0 theorem : True`

---

## 3. Counting Policy

| Metric | Value |
|--------|-------|
| Unique theorem names | 94 |
| Core theorems | 43 |
| Supporting theorems | 51 |
| Total manifest entries | 100 |
| `formal_core_module_theorems` | 43 |

Interpretation:

- `43` core theorems cover: `FiniteMonotoneIteration.lean` (9), `DungFixedPoint.lean` (17),
  `HornFixedPoint.lean` (10), `WeightedSupNorm.lean` (4), `HornDefinitions.lean` (2),
  `ContractionCondition.lean` (1).
- `51` supporting theorems span: `UnifiedModel.lean` (16), `JC_Formalization.lean` (12),
  `FiniteRosetta.lean` (9), `BanachEffectiveNodes.lean` (8), `TemporalKripke.lean` (6),
  and others.
- `94` unique theorem names across `100` manifest entries (some theorems appear
  in multiple records).

Canonical machine-readable source:

- [`theorem_manifest.json`](theorem_manifest.json)

---

## 4. Core Theorem Distribution

| File | Core theorems | Key theorems |
|------|--------------|-------------|
| `DungFixedPoint.lean` | 17 | `grounded_is_least_fixed_point`, `groundedSpec_unique_least_fixed_point`, `finite_termination`, `in_soundness`, `out_soundness` |
| `HornFixedPoint.lean` | 10 | `horn_completeness`, `horn_result_is_minimal_model`, `horn_finite_termination`, `horn_soundness` |
| `FiniteMonotoneIteration.lean` | 9 | `exists_fixpoint_le_card`, `fixed_at_card`, `iter_mono`, `iter_stable` |
| `WeightedSupNorm.lean` | 4 | `weightedSupDist_complete`, `weightedSupDist_triangle` |
| `HornDefinitions.lean` | 2 | `TH_monotone`, `TH_subset_univ` |
| `ContractionCondition.lean` | 1 | `lipschitz_coupling_implies_weighted_contraction` |
| **Total** | **43** | |

---

## 5. Release Boundary

### Released

- Finite monotone iteration kernel (`FiniteMonotoneIteration.lean`, 9 core theorems)
- Dung grounded fixed-point layer (`DungFixedPoint.lean`, 17 core theorems)
- Finite Horn closure layer (`HornFixedPoint.lean` + `HornDefinitions.lean`, 12 core theorems)
- Weighted sup-norm metric foundation (`WeightedSupNorm.lean`, 4 core theorems)
- Contraction bridge (`ContractionCondition.lean`, 1 core theorem)
- Reproducible `AxiomAudit`
- Repository-level release gate closure for `formal-core-v1`

### Not Released

- Full Banach fixed-point closure
- Full Lean proof of the `juris-calculus` Python runtime
- Empirical calibration of constants
- Privacy (differential privacy) guarantees
- Litigation automation

---

## 6. Axiom Audit Boundary

Audited core theorems and their axiom dependencies:

| Theorem | Dependencies |
|---------|-------------|
| `FiniteMonotoneSystem.exists_fixpoint_le_card` | `propext`, `Classical.choice`, `Quot.sound` |
| `FiniteMonotoneSystem.fixed_at_card` | `propext`, `Classical.choice`, `Quot.sound` |
| `DungAAF.grounded_is_least_fixed_point` | `propext`, `Classical.choice`, `Quot.sound` |
| `HornSystem.horn_completeness` | `propext`, `Classical.choice`, `Quot.sound` |
| `HornSystem.horn_result_is_minimal_model` | `propext`, `Classical.choice`, `Quot.sound` |
| `weightedSupDist_complete` | `propext`, `Classical.choice`, `Quot.sound` |

No project-defined axioms are part of the released core boundary.

Audit artifact: [`axiom_audit.txt`](axiom_audit.txt)

---

## 7. Deferred Domain Axioms

Three domain axioms are registered in `SORRY_LEDGER.md` as non-blocking:

| Axiom | Reason | Blocking? |
|-------|--------|-----------|
| `violation_implies_norm_active` | RuleId != NormId structural gap | NO |
| `permission_no_direct_violation` | PERMISSION has no rule-level violation path | NO |
| `constitutive_no_direct_violation` | CONSTITUTIVE has no rule-level violation path | NO |

These axioms target `DDLDefinitions.lean`, which does not yet exist. They
are domain axioms, not engineering failures.

---

## 8. Banach Status

Banach is NOT part of `formal-core-v1`.

Current public status: `UNPROVED_TRACK_B`

Historical side-track references preserved as archive tags:

- `archive/banach-track-b-d23e8f2`
- `archive/track-c-prod-f43e273`

These tags are archival only. They do NOT expand the public release claim.

---

## 9. Allowed Claims

- The finite monotone iteration kernel, Dung grounded fixed-point layer, and
  finite Horn closure layer are repository-level released formal artifacts.
- The core release boundary has reproducible Lean build evidence and reproducible
  axiom-audit evidence.
- Banach remains outside the released formal core.
- The weighted sup-norm metric and contraction bridge are released as supporting
  formal artifacts.

See [`ALLOWED_CLAIMS.md`](ALLOWED_CLAIMS.md) for the full list.

---

## 10. Forbidden Claims

- "The whole `juris-calculus` Python implementation is formally proved by Lean."
- "Banach fixed-point closure is complete."
- "Formal-core-v1 includes the Banach track."
- "Privacy guarantees have already been established."
- "Empirical calibration is complete."
- "The four-stage pipeline composition is formally proven end-to-end."
- "`UnifiedModel.lean` equals production end-to-end correctness."

See [`FORBIDDEN_CLAIMS.md`](FORBIDDEN_CLAIMS.md) for the full list.

---

## 11. Cross-Repo Reference Heads

| Repo | Branch | Head |
|------|--------|------|
| `legal-math-modeling` | `master` | `12470ac` |
| `juris-calculus` | `main` | `c18b478` |
| `deli-autoresearch` | `main` | `b35dbb1` |
