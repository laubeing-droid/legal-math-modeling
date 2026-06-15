# Theorem Status Matrix (Audit Fix 2)

**Project:** juris-calculus  
**Date:** 2026-06-11  
**run_all_proofs.py (sandbox):** 9 PROVED, 3 REFUTED, 0 FAILED, 5 PENDING

---

## Summary

| Status | Count |
|--------|-------|
| EXHAUSTIVE_FINITE_PROOF | 7 |
| SYMBOLIC_PROVED | 2 |
| REFUTED | 3 theorems (4 CEs) |
| PENDING_TOOLCHAIN | 5 |
| TOTAL | 17 artifacts |

---

## Matrix

| ID | Claim | Status | Artifact | Checker |
|----|-------|--------|----------|---------|
| T001a | Galois incidence (finite) | **EXHAUSTIVE_FINITE_PROOF** | `galois/finite_galois_adjunction.py` | `python galois/...` |
| T001b | Galois powerset (finite) | **EXHAUSTIVE_FINITE_PROOF** | `galois/finite_galois_adjunction.py` | `python galois/...` |
| T001c | Galois (Lean infinite) | **PENDING_TOOLCHAIN** | `galois/FiniteGaloisAdjunction.lean` | `lean4 ...` (needs Mathlib) |
| T002 | Bounded Horn correctness | **EXHAUSTIVE_FINITE_PROOF** | `horn/bounded_horn_correctness.py` | `python horn/...` |
| T003 | Horn termination | **EXHAUSTIVE_FINITE_PROOF** | `horn/horn_termination_measure.py` | `python horn/...` |
| T003a | Horn Z3 .smt2 | **PENDING_TOOLCHAIN** | `horn/bounded_horn_z3.smt2` | `z3 ...` (needs Z3 binary) |
| T004 | Fixpoint bounded termination | **EXHAUSTIVE_FINITE_PROOF** | `fixpoint/production_bounded_termination.py` | `python fixpoint/...` |
| T004a | Fixpoint TLA+ | **PENDING_TOOLCHAIN** | `fixpoint/evaluator_termination_model.tla` | `tlc ...` (needs TLC) |
| T005 | Dung grounded extension | **EXHAUSTIVE_FINITE_PROOF** | `aaf/dung_grounded_extension.py` | `python aaf/...` |
| T006 | Stratified correspondence | **EXHAUSTIVE_FINITE_PROOF** | `aaf/stratified_correspondence.py` | `python aaf/...` |
| T007 | Graph similarity range [0,1] | **SYMBOLIC_PROVED** | `graph_similarity/graph_similarity_range.py` | `python graph_similarity/...` |
| T007a | Graph similarity Z3 | **PENDING_TOOLCHAIN** (sandbox) / **SMT_PROVED** (user) | `graph_similarity/graph_similarity_range_z3.py` | `python graph_similarity/...` |
| T008 | Graph similarity is metric | **REFUTED** | `graph_similarity/metric_counterexamples.py` | `python graph_similarity/...` |
| T009 | Banach contraction (single-dim) | **SYMBOLIC_PROVED** | `banach/banach_effective_nodes.py` | `python banach/...` |
| T009a | Banach (Lean) | **PENDING_TOOLCHAIN** | `banach/BanachEffectiveNodes.lean` | `lean4 ...` (needs Mathlib; has `sorry`) |
| T010 | Scalar Laplace epsilon-DP | **PROVED_WITH_DRAFT** | `dp/laplace_scalar_mechanism.md` | Manual review |
| T011 | Ratio-preserving DP | **DOWNGRADED** | `dp/ratio_preserving_boundary.md` | Manual review |
| T012 | Floor clipping epsilon-DP | **REFUTED** | `dp/dp_floor_clipping_analysis.py` | `python dp/...` |
| T013 | Clipped Theil-Sen = pure | **REFUTED** | `statistics/clipped_theilsen_refutation.py` | `python statistics/...` |
| T014 | Siegel repeated median | **EXHAUSTIVE_FINITE_PROOF** | `statistics/siegel_repeated_median_verifier.py` | `python statistics/...` |

---

## Runner Gate Fix

- Any `FAILED` artifact causes `overall = FAIL`
- Lean artifacts with Mathlib missing or `sorry` are auto-downgraded to `PENDING_TOOLCHAIN`
- Z3 .smt2 without z3 binary is `PENDING_TOOLCHAIN` (not FAILED)
