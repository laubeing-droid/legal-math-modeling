# Final Closure Baseline

**Date:** 2026-06-27

## Repository State

| Repo | Status |
|------|--------|
| legal-math-modeling | 25 Lean files, 94 theorems, 0 sorry, `lake build` 2954 jobs 0 errors |

## Lean Formalization

| Item | Value |
|---|---|
| Lean version | 4.30.0 |
| Mathlib version | v4.30.0 (rev c5ea003) |
| Lean files | 25 |
| Core theorems | 43 |
| Supporting theorems | 51 |
| Total unique theorems | 94 |
| sorry count | 0 |
| `lake build` jobs | 2954, 0 errors |
| AxiomAudit | PASS |

## JC_Formalization.lean Status Register

| Set | Card | Lean proof |
|---|---|---|
| proved_theorems | 7 | `proved_theorems_card : .card = 7 := by decide` |
| empirical_proxy_theorems | 2 | `empirical_proxy_card : .card = 2 := by decide` |
| refuted_theorems | 1 | `refuted_theorems_card : .card = 1 := by decide` |
| pending_theorems | 0 | `pending_theorems_card : .card = 0 := by decide` |

## Gate Status

| Gate | Name | Status |
|---|---|---|
| M1 | Canonical Semantic Types | SUBSTANTIAL_PARTIAL |
| M2 | Minimal DDL Core | SUBSTANTIAL_PARTIAL |
| M3 | Horn->AAF Contract | SUBSTANTIAL_PARTIAL |
| M4 | Reference Interpreter | PARTIAL |
| M5 | Certificate/Checker | CLOSED |

## Core Theorem Distribution by File

| File | Theorems | Key results |
|---|---|---|
| FiniteMonotoneIteration.lean | 10 | iter_mono, iter_stable, fixed_at_card, exists_fixpoint_le_card |
| HornFixedPoint.lean | 10 | horn_soundness, horn_completeness, horn_result_is_minimal_model |
| DungFixedPoint.lean | 13 | grounded_is_fixed_point, grounded_is_least_fixed_point, labelling_partition |
| FiniteGaloisAdjunction.lean | 1 | galois_connection_of_residuated |
| FiniteRosetta.lean | 8 | no_total_functor, obstruction_density_gt_two_thirds |
| TemporalKripke.lean | 2 | temporal_guard_always, litigation_always_guard |
| UnifiedModel.lean | 11 | full_chain, unified_composition_v2, soundness_aaf, soundness_banach |
| BanachEffectiveNodes.lean | 3 | pricingFn_contraction, pricingFn_fixed_point, pricingFn_unique_fixed_point |
| BanachComplete.lean | 1 | weightedMetricSpace_dist |
| BanachContraction.lean | 2 | weighted_contraction_bound |
| BanachFixedPoint.lean | 1 | weightedContractionData_of_coupling |
| ContractionCondition.lean | 1 | lipschitz_coupling_implies_weighted_contraction |
| WeightedSupNorm.lean | 4 | weightedSupDist_nonneg, _triangle, _symm, _complete |
| JC_Formalization.lean | 6 | status register cardinality proofs, advance properties |
| DungAAF.lean | supporting | AAF structural definitions |
| HornDefinitions.lean | 2 | TH_monotone, TH_subset_univ |

## Proof Artifact Summary

| Status | Count |
|---|---|
| PROVED | 10 |
| REFUTED | 3 |
| PENDING_TOOLCHAIN | 4 |
| FAILED | 0 |
| **Total** | **17** |

## Ghost Files (Do Not Exist)

The following files have been falsely referenced in historical documents. They do not exist in the repository and must never be cited as existing artifacts:

`LegalSyntax.lean`, `DDLDefinitions.lean`, `CertificateChecker.lean`, `AttackDecision.lean`, `SafetyTheorems.lean`, `argmin_polytime.lean`, `EndToEnd.lean`, `HornCanonical.lean`, `ArgumentCompiler.lean`, `LegalIds.lean`, `LegalModel.lean`, `LegalWellFormed.lean`
