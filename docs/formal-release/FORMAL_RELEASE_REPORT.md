# Formal Core Release Report

**Date:** 2026-06-28
**Release ID:** `formal-core-v1`

---

## 1. Spec-First Transition Status

**Status:** `spec-first-transition-ready-plus-four-slices`

The five gates required for spec-first transition:

| Gate | Document | Status |
|------|----------|--------|
| M1: Canonical Schema | [`docs/spec/canonical_legal_schema.md`](../spec/canonical_legal_schema.md) | CLOSED_FOR_FOUR_SLICES |
| M2: DDL Minimal Core | [`docs/spec/ddl_minimal_core.md`](../spec/ddl_minimal_core.md) | CLOSED_FOR_FOUR_SLICES |
| M3: Horn -> AAF Contract | [`docs/spec/horn_to_aaf_contract.md`](../spec/horn_to_aaf_contract.md) | CLOSED_FOR_FOUR_SLICES |
| M4: Certificate/Checker Boundary | [`docs/spec/certificate_checker_boundary.md`](../spec/certificate_checker_boundary.md) | CLOSED_FOR_FOUR_SLICES |
| M5: Unified Stopping Statement | This document + [`SPEC_FIRST_TRANSITION_READY.md`](SPEC_FIRST_TRANSITION_READY.md) | CLOSED |

After this point, main engineering effort shifts to `juris-calculus`.
New math work in this repo only as "support for JC new capabilities."

---

## 2. Public State

| Item | State |
|------|-------|
| Public branch model | `master` only |
| Last verified source head | Local pending commit for four-slice closure |
| Last full clean rebuild evidence | Local `lake build` evidence for four-slice closure |
| GitHub Actions clean build | Not rerun; local-only Playbook scope |
| Local `lake build` evidence | PASS (2961 jobs, 0 errors) |
| Local `lake build +JurisLean.AxiomAudit` evidence | PASS |
| Lean source guard | PASS |

Lean source guard means:

- `0 sorry`
- `0 admit`
- `0 custom axiom` (Lean built-in axiom dependencies are disclosed by `AxiomAudit`)
- `0 theorem : True`

---

## 3. Counting Policy

| Metric | Value |
|--------|-------|
| Lean source files | 32 |
| Unique theorem names | 126 |
| Core theorems | 42 |
| Supporting unique theorem names | 84 |
| Supporting manifest records | 84 |
| Total manifest entries | 126 |
| Four-slice vertical results | 32 |
| `formal_core_module_theorems` | 42 |

Interpretation:

- `42` core theorems cover: `FiniteMonotoneIteration.lean` (9), `DungFixedPoint.lean` (16),
  `HornFixedPoint.lean` (10), `WeightedSupNorm.lean` (4), `HornDefinitions.lean` (2),
  `ContractionCondition.lean` (1).
- `84` supporting theorems span: four-slice files (`LegalSyntax.lean`,
  `DDLDefinitions.lean`, `HornAAFContract.lean`, `CertificateChecker.lean`,
  `AttackDecision.lean`, `SafetyTheorems.lean`, `EndToEnd.lean`) plus
  `UnifiedModel.lean`, `JC_Formalization.lean`, `FiniteRosetta.lean`,
  `BanachEffectiveNodes.lean`, `TemporalKripke.lean`, and others.
- `126` theorem declarations are tracked in the current manifest.

Canonical machine-readable source:

- [`theorem_manifest.json`](theorem_manifest.json)

---

## 4. Core Theorem Distribution

| File | Core theorems | Key theorems |
|------|--------------|-------------|
| `DungFixedPoint.lean` | 16 | `grounded_is_least_fixed_point`, `groundedSpec_unique_least_fixed_point`, `finite_termination`, `in_soundness`, `out_soundness` |
| `HornFixedPoint.lean` | 10 | `horn_completeness`, `horn_result_is_minimal_model`, `horn_finite_termination`, `horn_soundness` |
| `FiniteMonotoneIteration.lean` | 9 | `exists_fixpoint_le_card`, `fixed_at_card`, `iter_mono`, `iter_stable` |
| `WeightedSupNorm.lean` | 4 | `weightedSupDist_complete`, `weightedSupDist_triangle` |
| `HornDefinitions.lean` | 2 | `TH_monotone`, `TH_subset_univ` |
| `ContractionCondition.lean` | 1 | `lipschitz_coupling_implies_weighted_contraction` |
| **Total** | **42** | |

---

## 5. Release Boundary

### Released

- Finite monotone iteration kernel (`FiniteMonotoneIteration.lean`, 9 core theorems)
- Dung grounded fixed-point layer (`DungFixedPoint.lean`, 17 core theorems)
- Finite Horn closure layer (`HornFixedPoint.lean` + `HornDefinitions.lean`, 12 core theorems)
- Weighted sup-norm metric foundation (`WeightedSupNorm.lean`, 4 core theorems)
- Contraction bridge (`ContractionCondition.lean`, 1 core theorem)
- Four vertical-slice specification modules for contract breach, license,
  permission, and priority (`LegalSyntax.lean`, `DDLDefinitions.lean`,
  `HornAAFContract.lean`, `CertificateChecker.lean`, `AttackDecision.lean`,
  `SafetyTheorems.lean`, `EndToEnd.lean`)
- Local four-slice differential evidence:
  `runtime/legal_math_four_slice_differential.json`
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

## 7. Closed Domain-Axiom Targets

Three former domain-axiom targets are closed in `DDLDefinitions.lean`:

| Axiom | Reason | Blocking? |
|-------|--------|-----------|
| `violation_implies_norm_active` | Direct violation requires an active norm in the minimal DDL model | NO |
| `permission_no_direct_violation` | Permission has no direct violation path in the minimal DDL model | NO |
| `constitutive_no_direct_violation` | Constitutive status rules have no direct violation path in the minimal DDL model | NO |

These are now Lean theorems for the four-slice minimal DDL model. They do not
prove full runtime correctness.

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
- The four vertical slices are Lean-checked within the formal model, and the
  Python reference fixtures pass local differential checks against same-name JC
  shadow fixtures.

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

These heads record the verified inputs for this documentation sync. The
current git HEAD may advance after the documentation-only commit that contains
this report.

| Repo | Branch | Head |
|------|--------|------|
| `legal-math-modeling` | `master` | `f671a6e` |
| `juris-calculus` | `main` | `3ff27875` |
| `deli-autoresearch` | `main` | `4270263` |
