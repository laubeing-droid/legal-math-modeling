# ALLOWED CLAIMS

**Date:** 2026-06-28
**Authority:** `legal-math-modeling` (this repo)
**Release ID:** `formal-core-v1`

---

## 1. Mathematical Proof Layer

The following claims are supported by Lean-proven theorems in files that exist
in this repo. `lake build JurisLean` passes with 0 errors and 0 sorry.

### Finite Monotone Iteration (FiniteMonotoneIteration.lean)

- Finite monotone systems converge to a fixed point in at most |universe| iterations.
- `exists_fixpoint_le_card`: fixed point exists within cardinality bound.
- `fixed_at_card`: fixed point is reached at the cardinality of the universe.
- The iteration is monotone (`iter_mono`), stable at fixed point (`iter_stable`),
  and strictly increases until fixed (`iter_ssubset_of_ne`).

### Dung Grounded Extension (DungFixedPoint.lean)

- The grounded extension exists, is unique, and is the least fixed point of the
  characteristic function (`groundedSpec_unique_least_fixed_point`).
- The grounded extension is a fixed point (`grounded_is_fixed_point`).
- The grounded extension is the least fixed point (`grounded_is_least_fixed_point`).
- The specification-based and computation-based definitions agree
  (`grounded_eq_groundedSpec`).
- The computation terminates in finite iterations (`finite_termination`) bounded
  by the argument count (`iteration_bound`).
- IN arguments are sound (`in_soundness`), OUT arguments are sound
  (`out_soundness`), and undecided arguments are correctly characterized
  (`undecided_characterization`).
- Self-attacking arguments are excluded from the grounded extension
  (`self_attack_not_in_grounded`).

### Finite Horn Closure (HornFixedPoint.lean + HornDefinitions.lean)

- The Horn operator `TH` is monotone (`TH_monotone`) and bounded by the universe
  (`TH_subset_univ`).
- Horn closure converges to a fixed point (`horn_finite_termination`) bounded by
  the universe size (`horn_iteration_bound`).
- The closure result is the least fixed point (`horn_result_least_fixed_point`)
  and the minimal model (`horn_result_is_minimal_model`).
- Horn soundness (`horn_soundness`) and completeness (`horn_completeness`) hold.

### Weighted Sup-Norm (WeightedSupNorm.lean)

- The weighted sup-distance is non-negative (`weightedSupDist_nonneg`), satisfies
  the triangle inequality (`weightedSupDist_triangle`), and is symmetric
  (`weightedSupDist_symm`).
- The metric is complete (`weightedSupDist_complete`).

### Contraction Bridge (ContractionCondition.lean)

- Lipschitz coupling implies weighted contraction
  (`lipschitz_coupling_implies_weighted_contraction`).

---

## 2. Counting Policy

| Metric | Value | Source |
|--------|-------|--------|
| Unique theorem names | 94 | `theorem_manifest.json` |
| Core theorems | 43 | `theorem_manifest.json` |
| Supporting theorems | 51 | `theorem_manifest.json` |
| Total manifest entries | 100 | `theorem_manifest.json` |
| `formal_core_module_theorems` | 43 | `theorem_manifest.json` |

Note: 94 unique names across 100 manifest entries (some theorems appear in
multiple manifest records). The `formal_core_module_theorems = 43` count
covers: `FiniteMonotoneIteration.lean` (9), `DungFixedPoint.lean` (17),
`HornFixedPoint.lean` (10), `WeightedSupNorm.lean` (4), `HornDefinitions.lean` (2),
`ContractionCondition.lean` (1).

---

## 3. Specification Freeze Layer

- 11 canonical types are frozen with unique definitions (`canonical_legal_schema.md`)
- DDL minimal core is frozen: 4 modalities, 4 reparation modes, 3 exception kinds
  (`ddl_minimal_core.md`)
- Horn -> AAF compilation contract is frozen: 6 machine-verifiable checks
  (`horn_to_aaf_contract.md`)
- Certificate/Checker boundary is frozen: DecisionStatus, TAINTED semantics,
  checker responsibilities (`certificate_checker_boundary.md`)
- 5 DDL slices implemented: contract breach, license + priority, tort, criminal, admin
- 3 deferred domain axioms registered (non-blocking): `violation_implies_norm_active`,
  `permission_no_direct_violation`, `constitutive_no_direct_violation`

---

## 4. Engineering Layer

- `lake build JurisLean` passes with 0 errors and 0 sorry (2954 jobs)
- `AxiomAudit` is reproducible; only Lean 4 built-in axioms in core boundary
  (`propext`, `Classical.choice`, `Quot.sound`)
- Lean source guard passes: 0 sorry, 0 admit, 0 custom axiom, 0 `theorem : True`
- `juris-calculus` grounded engine outputs `derived_bound` / `convergent` / `truncated`
- Fail-closed behavior on truncation, non-convergence, and protocol incompatibility

---

## 5. Five Gate Status

| Gate | Document | Status |
|------|----------|--------|
| M1: Canonical Schema | `docs/spec/canonical_legal_schema.md` | SUBSTANTIAL_PARTIAL |
| M2: DDL Minimal Core | `docs/spec/ddl_minimal_core.md` | SUBSTANTIAL_PARTIAL |
| M3: Horn -> AAF Contract | `docs/spec/horn_to_aaf_contract.md` | SUBSTANTIAL_PARTIAL |
| M4: Certificate/Checker Boundary | `docs/spec/certificate_checker_boundary.md` | PARTIAL |
| M5: Unified Stopping Statement | `docs/formal-release/SPEC_FIRST_TRANSITION_READY.md` | CLOSED |

---

## 6. Recommended Public Statement

> This repository has completed repository-level formal release closure for the
> finite monotone iteration kernel, Dung grounded fixed-point layer, and finite
> Horn closure layer. Banach remains an independent unproved research track.
