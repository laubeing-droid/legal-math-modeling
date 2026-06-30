# Papers

This directory contains the mathematical papers of the `legal-math-modeling` project.

**Last full rewrite:** 2026-06-27 (aligned with `spec-first-transition-ready` status)

**Important:** All papers now reference only Lean theorems that actually exist in the codebase. Work that is PLANNED but not yet formalized is explicitly marked. See `docs/formal-release/FORBIDDEN_CLAIMS.md` for claims that must not appear in these papers.

## Core Paper

| File | Language | Description |
|------|----------|-------------|
| [main.md](main.md) | English | Full 13-chapter core paper with KaTeX-rendered formulas |
| [main_cn.md](main_cn.md) | Chinese | Complete Chinese version of the core paper |
| [main.tex](main.tex) + [sections/](sections/) | LaTeX | LaTeX source for PDF generation (13 section files) |

## Consolidated Submission

| File | Description |
|------|-------------|
| [icail_full_paper.md](icail_full_paper.md) | ICAIL 2026 consolidated submission (14 chapters) |

## Topic Papers

| File | Topic | Key Contribution |
|------|-------|-----------------|
| [explainable_legal_reasoning.md](explainable_legal_reasoning.md) | Explainable legal reasoning | Stratified architecture for explainability through formal methods |
| [non_monotonicity.md](non_monotonicity.md) | Non-monotonicity | Formal counterexample proving unified evaluator is non-monotone |
| [dp_impossibility.md](dp_impossibility.md) | DP impossibility | Counterexample: privilege level does not determine unique epsilon |
| [graph_similarity_topology.md](graph_similarity_topology.md) | Graph similarity | Topological counterexamples: similarity is not a metric |
| [multi_ai_formalization.md](multi_ai_formalization.md) | Multi-AI methodology | Adversarial multi-AI formal verification methodology |
| [argumentation_frameworks.md](argumentation_frameworks.md) | Argumentation | Dung AF vs ASPIC+ comparison |
| [legal_reasoning_paradigms.md](legal_reasoning_paradigms.md) | Reasoning paradigms | Four paradigms formalized as composable modules |
| [probabilistic_legal_reasoning.md](probabilistic_legal_reasoning.md) | Probabilistic reasoning | Bayesian evidence evaluation under standards of proof |
| [argument_strength.md](argument_strength.md) | Argument strength | Impossibility theorem for argument strength functions |
| [legal_analogy.md](legal_analogy.md) | Legal analogy | Case-based reasoning; distinguishing is NP-hard |
| [mathematical_structures.md](mathematical_structures.md) | Mathematical structures | Lattices, fixpoints, Kripke models, and functors |
| [ai_liability_infrastructure.md](ai_liability_infrastructure.md) | AI liability | Trust labels as AI liability infrastructure under EU AI Act |

## Formalization Status Legend

In the papers, theorems are marked with their verification status:

| Mark | Meaning |
|------|---------|
| **PROVEN (Lean)** | Machine-checked in Lean 4 (0 sorry, 0 custom axiom; Lean built-in axiom dependencies disclosed by AxiomAudit) |
| **VERIFIED (Python)** | Verified by Python tests/exhaustive enumeration |
| **PLANNED** | Target formalization exists as a design but Lean file does not yet exist |
| **REFUTED** | Explicit counterexample constructed |

## Reading Order

For newcomers:

1. Start with `main.md` or `main_cn.md` for the complete mathematical framework
2. Read `non_monotonicity.md` for the key architectural insight (stratification requirement)
3. Read `mathematical_structures.md` for the survey of underpinning structures
4. Explore topic papers based on interest

## Key Lean Files Referenced

| Lean File | Content | Status |
|-----------|---------|--------|
| `FiniteMonotoneIteration.lean` | Generic finite monotone iteration kernel (9 theorems) | PROVEN |
| `DungFixedPoint.lean` | Dung grounded extension (17 theorems) | PROVEN |
| `HornFixedPoint.lean` | Horn closure (10 theorems) | PROVEN |
| `WeightedSupNorm.lean` | Weighted sup metric (4 theorems) | PROVEN |
| `BanachEffectiveNodes.lean` | Pricing contraction (8 theorems) | PROVEN |
| `UnifiedModel.lean` | Unified composition (16 theorems) | PROVEN |
| `FiniteRosetta.lean` | Cross-jurisdiction obstruction (9 theorems) | PROVEN |
| `FiniteGaloisAdjunction.lean` | Galois connection (2 theorems) | PROVEN |
| `TemporalKripke.lean` | Temporal invariants (6 theorems) | PROVEN |
| `JC_Formalization.lean` | Proof-status registry (12 theorems) | PROVEN |
