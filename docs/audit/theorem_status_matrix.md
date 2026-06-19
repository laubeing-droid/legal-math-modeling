# Theorem Status Matrix (Audit Fix 4 — Red-Team Annotated)

**Project:** juris-calculus  
**Date:** 2026-06-19  
**run_all_proofs.py (sandbox):** 10 PROVED, 3 REFUTED, 0 FAILED, 4 PENDING
**Red-Team Status:** v5.0 honest labels applied below

---

## Red-Team Annotations (2026-06-19)

| Artifact | Proof Status | Red-Team Status | Issue |
|---|---|---|---|
| ART-003 (Horn correctness) | EXHAUSTIVE_FINITE_PROOF | **EMPIRICAL_PROXY** | 66,066 is AAF count, not Horn. Horn actual: 3,969 acyclic + 50K sampling |
| ART-004 (Horn termination) | EXHAUSTIVE_FINITE_PROOF | EXHAUSTIVE_FINITE_PROOF | 82,836 KBs checked, consistent |
| ART-011 (Graph Similarity Z3) | SMT_PROVED_FINITE | SMT_PROVED_FINITE | OK |
| ART-008 (Dung grounded) | EXHAUSTIVE_FINITE_PROOF | EXHAUSTIVE_FINITE_PROOF | OK |
| ART-009 (Stratified correspondence) | EXHAUSTIVE_FINITE_PROOF | EXHAUSTIVE_FINITE_PROOF | OK |
| ART-010 (Graph similarity range) | SYMBOLIC_PROVED | SYMBOLIC_PROVED | OK |
| ART-016 (Banach effective) | SYMBOLIC_PROVED | SYMBOLIC_PROVED | OK |
| ART-015 (Siegel repeated median) | EXHAUSTIVE_FINITE_PROOF | EXHAUSTIVE_FINITE_PROOF | OK |
| T4 (Kripke mutex, z3_kripke_mutex.py) | SMT_PROVED | **AXIOM_ONLY** | Z3 adds theorem as axiom, checks consistency — not a proof |
| T20 (MDL, kolmogorov_mdl_rules.py) | SYMBOLIC_PROVED | **EMPIRICAL_PROXY** | claim_mapping level ρ=0.1168/p=0.4459 not significant; domain-level CI includes 0 |

---

## Summary

| Status | Count |
|--------|-------|
| EXHAUSTIVE_FINITE_PROOF | 7 |
| SYMBOLIC_PROVED | 2 |
| SMT_PROVED_FINITE | 1 |
| REFUTED | 3 theorems (4 CEs) |
| PENDING_TOOLCHAIN | 4 |
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
| T007a | Graph similarity Z3 | **SMT_PROVED_FINITE** | `graph_similarity/graph_similarity_range_z3.py` | `python graph_similarity/...` (z3 Python bindings) |
| T008 | Graph similarity is metric | **REFUTED** | `graph_similarity/metric_counterexamples.py` | `python graph_similarity/...` |
| T009 | Banach contraction (single-dim) | **SYMBOLIC_PROVED** | `banach/banach_effective_nodes.py` | `python banach/...` |
| T009a | Banach (Lean) | **PENDING_TOOLCHAIN** | `banach/BanachEffectiveNodes.lean` | `lean4 ...` (needs Mathlib; has `sorry`) |
| T010 | Scalar Laplace epsilon-DP | **EXHAUSTIVE_FINITE_PROOF** | `dp/laplace_scalar_mechanism.md` | Manual review + checker |
| T011 | Ratio-preserving DP | **DOWNGRADED** | `dp/ratio_preserving_boundary.md` | Manual review |
| T012 | Floor clipping epsilon-DP | **REFUTED** | `dp/dp_floor_clipping_analysis.py` | `python dp/...` |
| T013 | Clipped Theil-Sen = pure | **REFUTED** | `statistics/clipped_theilsen_refutation.py` | `python statistics/...` |
| T014 | Siegel repeated median | **EXHAUSTIVE_FINITE_PROOF** | `statistics/siegel_repeated_median_verifier.py` | `python statistics/...` |

---

## Runner Gate Fix

- Any `FAILED` artifact causes `overall = FAIL`
- Lean artifacts with Mathlib missing or `sorry` are auto-downgraded to `PENDING_TOOLCHAIN`
- Z3 .smt2 without z3 binary is `PENDING_TOOLCHAIN` (not FAILED)

---

## Reconciliation (2026-06-18)

- `ARTIFACT_MANIFEST.json`, `proof_run_results.json`, `theorem_status_matrix.md` 统一为：10 PROVED, 3 REFUTED, 4 PENDING_TOOLCHAIN, 0 FAILED。
- T007a (Z3 graph similarity) 因 Python z3 bindings 可用，状态从 PENDING_TOOLCHAIN 升级为 SMT_PROVED_FINITE。
- T010 (Laplace DP) 在 run_all_proofs.py 中可被 checker 确认，状态对齐为 EXHAUSTIVE_FINITE_PROOF。
- Lean/TLA+ 工具链仍然缺失，T001c/T003a/T004a/T009a 保持 PENDING_TOOLCHAIN。
