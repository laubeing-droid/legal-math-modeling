# Theorem Status Matrix (Based on 94 Unique Lean Theorems)

> **Date:** 2026-06-27
> **Project:** legal-math-modeling
> **Lean files:** 25 files in `proofs/lean/juris_lean/JurisLean/`
> **Total unique theorems:** 94 (43 core + 51 supporting)
> **sorry count:** 0
> **`lake build JurisLean`:** 2954 jobs, 0 errors

---

## Summary

| Status | Count |
|---|---|
| Core theorems | 43 |
| Supporting theorems | 51 |
| Total unique theorems | 94 |
| sorry | 0 |

### JC_Formalization.lean Status Register

| Set | Card | Lean proof |
|---|---|---|
| proved_theorems | 7 | `proved_theorems_card` |
| empirical_proxy_theorems | 2 | `empirical_proxy_card` |
| refuted_theorems | 1 | `refuted_theorems_card` |
| pending_theorems | 0 | `pending_theorems_card` |

---

## Core Theorems by File

### FiniteMonotoneIteration.lean (10 theorems)

| # | Theorem | Scope |
|---|---|---|
| 1 | iter_zero | iter sys 0 = empty |
| 2 | iter_succ | iter sys (n+1) = step (iter sys n) |
| 3 | iter_subset_univ | iter sys n subset of sys.univ |
| 4 | iter_mono | iter sys n subset of iter sys (n+1) |
| 5 | iter_stable | Stability: if iter n = iter (n+1), then iter (n+k) = iter n |
| 6 | iter_ssubset_of_ne | Strict subset if not equal |
| 7 | iter_card_lt_of_ne | Strict card inequality |
| 8 | iter_card_le_univ | Card bounded by univ card |
| 9 | exists_fixpoint_le_card | Fixpoint exists at or before card |
| 10 | fixed_at_card | iter (card) = iter (card + 1) |

### HornDefinitions.lean (2 theorems)

| # | Theorem | Scope |
|---|---|---|
| 11 | TH_monotone | TH operator is monotone on subsets |
| 12 | TH_subset_univ | TH result is subset of univ |

### HornFixedPoint.lean (10 theorems)

| # | Theorem | Scope |
|---|---|---|
| 13 | horn_operator_subset_univ | TH S subset of univ |
| 14 | horn_operator_monotone | TH is monotone |
| 15 | horn_iteration_monotone | Iteration is monotone |
| 16 | horn_finite_termination | Termination within card steps |
| 17 | horn_iteration_bound | Iteration bounded by card |
| 18 | horn_result_fixed_point | Result is fixed point |
| 19 | horn_result_least_fixed_point | Result is least fixed point |
| 20 | horn_soundness | Soundness of derivation |
| 21 | horn_completeness | Completeness of derivation |
| 22 | horn_result_is_minimal_model | Result is minimal model |

### DungFixedPoint.lean (13 theorems)

| # | Theorem | Scope |
|---|---|---|
| 23 | F_monotone | Characteristic function is monotone |
| 24 | iteration_monotone | Iteration is monotone |
| 25 | finite_termination | Terminates within args.card steps |
| 26 | iteration_bound | Iteration bounded by args.card + 1 |
| 27 | groundedSpec_is_fixed_point | Spec-based grounded is fixed point |
| 28 | grounded_is_fixed_point | Computed grounded is fixed point |
| 29 | groundedSpec_is_least_fixed_point | Spec-based grounded is least |
| 30 | grounded_is_least_fixed_point | Computed grounded is least |
| 31 | grounded_is_least_complete | Least completeness |
| 32 | groundedSpec_unique_least_fixed_point | Unique least fixed point |
| 33 | labelling_partition | IN/OUT/UNDECIDED partition |
| 34 | in_soundness | IN labels are sound |
| 35 | out_soundness | OUT labels are sound |
| 36 | undecided_characterization | UNDECIDED characterization |
| 37 | self_attack_precise_theorem | Self-attack precise analysis |
| 38 | self_attack_not_in_grounded | Self-attacking args not in grounded |

### DungAAF.lean (supporting lemmas for AAF structure)

Supporting definitions and lemmas for the Dung argumentation framework.

### FiniteGaloisAdjunction.lean (1 theorem)

| # | Theorem | Scope |
|---|---|---|
| 39 | galois_connection_of_residuated | Galois connection from residuated maps |

### FiniteRosetta.lean (8 theorems)

| # | Theorem | Scope |
|---|---|---|
| 40 | cnOnly_eq_30 | cnOnlyCount = 30 |
| 41 | collision_eq_4 | collisionCount = 4 |
| 42 | asymmetry_eq_3 | asymmetryCount = 3 |
| 43 | obstruction_eq_37 | obstructionCount = 37 |
| 44 | cnOnly_exceeds_half | cnOnlyCount > 44/2 |
| 45 | obstruction_exceeds_half | obstructionCount > 44/2 |
| 46 | no_total_functor | No total cross-jurisdiction functor |
| 47 | obstruction_density_gt_two_thirds | Obstruction density > 2/3 |
| 48 | pure_obstruction_majority | Pure obstructions are majority |

### TemporalKripke.lean (2 theorems)

| # | Theorem | Scope |
|---|---|---|
| 49 | temporal_guard_always | Temporal guard holds at all time points |
| 50 | litigation_always_guard | Litigation guard always holds |

### UnifiedModel.lean (11 theorems)

| # | Theorem | Scope |
|---|---|---|
| 51 | horn_step_mono | Horn step is monotone |
| 52 | unattacked_in_ge | Unattacked args in grounded extension |
| 53 | unattacked_in_lfp | Unattacked args in least fixpoint |
| 54 | banach_bounded | Banach pricing bounded |
| 55 | soundness_aaf | AAF soundness in unified model |
| 56 | soundness_banach | Banach soundness in unified model |
| 57 | gc2_completeness | Completeness of GC2 |
| 58 | unified_composition_v2 | Unified composition theorem |
| 59 | full_chain | Full chain theorem |
| 60 | horn_monotone | Horn monotonicity in unified model |
| 61 | banach_bound_uniform | Uniform Banach bound |

### BanachComplete.lean (1 theorem)

| # | Theorem | Scope |
|---|---|---|
| 62 | weightedMetricSpace_dist | Weighted metric space distance properties |

### BanachContraction.lean (2 theorems)

| # | Theorem | Scope |
|---|---|---|
| 63 | weighted_contraction_bound | Weighted contraction bound |
| 64 | weighted_contraction_bound_nnreal | NNReal version |

### BanachEffectiveNodes.lean (3 theorems)

| # | Theorem | Scope |
|---|---|---|
| 65 | pricingFn_contraction | Pricing function contraction |
| 66 | pricingFn_fixed_point | Pricing function fixed point |
| 67 | pricingFn_unique_fixed_point | Uniqueness of fixed point |

### BanachFixedPoint.lean (1 theorem)

| # | Theorem | Scope |
|---|---|---|
| 68 | weightedContractionData_of_coupling | Coupling to weighted contraction |

### ContractionCondition.lean (1 theorem)

| # | Theorem | Scope |
|---|---|---|
| 69 | lipschitz_coupling_implies_weighted_contraction | Lipschitz coupling implies contraction |

### WeightedSupNorm.lean (4 theorems)

| # | Theorem | Scope |
|---|---|---|
| 70 | weightedSupDist_nonneg | Non-negativity |
| 71 | weightedSupDist_triangle | Triangle inequality |
| 72 | weightedSupDist_symm | Symmetry |
| 73 | weightedSupDist_complete | Completeness |

### JC_Formalization.lean (6 theorems)

| # | Theorem | Scope |
|---|---|---|
| 74 | proved_theorems_card | proved_theorems.card = 7 |
| 75 | empirical_proxy_card | empirical_proxy_theorems.card = 2 |
| 76 | refuted_theorems_card | refuted_theorems.card = 1 |
| 77 | pending_theorems_card | pending_theorems.card = 0 |
| 78 | advance_preserves_domain_bound | Domain bound preserved under advance |
| 79 | advance_cannot_revive_refuted | Refuted status is permanent |

---

## Supporting Theorems and Lemmas (51)

The remaining 51 theorems are distributed across `Basic.lean`, `ScratchApi.lean`, `SupZeroLemma.lean`, `BanachScratch.lean`, `BanachWeightedNorm.lean`, `BanachCertificate.lean`, `HornOperationalRefinement.lean`, and structural lemmas within the files listed above. All compile with 0 sorry.

---

## Proof Artifact Status (17 artifacts, separate from Lean)

| ID | Name | Status | Evidence |
|---|---|---|---|
| ART-001 | Finite Galois Adjunction | PROVED | EXHAUSTIVE_FINITE_PROOF |
| ART-003 | Bounded Horn Correctness | PROVED | EXHAUSTIVE_FINITE_PROOF |
| ART-004 | Horn Termination Measure | PROVED | EXHAUSTIVE_FINITE_PROOF |
| ART-006 | Production Bounded Termination | PROVED | EXHAUSTIVE_FINITE_PROOF |
| ART-008 | Dung Grounded Extension | PROVED | EXHAUSTIVE_FINITE_PROOF |
| ART-009 | Stratified Correspondence | PROVED | EXHAUSTIVE_FINITE_PROOF |
| ART-010 | Graph Similarity Range | PROVED | SYMBOLIC_PROVED |
| ART-011 | Graph Similarity Range (Z3) | PROVED | SMT_PROVED_FINITE |
| ART-015 | Siegel Repeated Median | PROVED | EXHAUSTIVE_FINITE_PROOF |
| ART-016 | Banach Effective Nodes | PROVED | SYMBOLIC_PROVED |
| ART-012 | Graph Metric Counterexamples | REFUTED | REFUTED_BY_COUNTEREXAMPLE |
| ART-013 | DP Floor Clipping Analysis | REFUTED | REFUTED_BY_COUNTEREXAMPLE |
| ART-014 | Clipped Theil-Sen Refutation | REFUTED | REFUTED_BY_COUNTEREXAMPLE |
| ART-005 | Bounded Horn (Z3 .smt2) | PENDING | PENDING_TOOLCHAIN |
| ART-002 | Finite Galois Adjunction (Lean) | PENDING | PENDING_TOOLCHAIN |
| ART-017 | Banach Effective Nodes (Lean) | PENDING | PENDING_TOOLCHAIN |
| ART-007 | Evaluator Termination (TLA+) | PENDING | PENDING_TOOLCHAIN |

---

## Gate Fix Rules

- Any `FAILED` artifact causes `overall = FAIL`.
- Lean artifacts with `sorry` are excluded from proven count (0 sorry is current state).
- PENDING_TOOLCHAIN items require tool chain installation before upgrade.
- refuted status is permanent: `advance_cannot_revive_refuted` is a Lean-proven theorem.
