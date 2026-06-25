# Papers

This directory contains the mathematical papers of the `legal-math-modeling` project.

## Core Paper

| File | Language | Description |
|------|----------|-------------|
| [main.md](main.md) | English | Full 13-chapter core paper with KaTeX-rendered formulas |
| [main_cn.md](main_cn.md) | Chinese | Complete Chinese version of the core paper |
| [main.tex](main.tex) | LaTeX | LaTeX source for PDF generation |

## Consolidated Submission

| File | Description |
|------|-------------|
| [icail_full_paper.md](icail_full_paper.md) | Consolidated ICAIL submission unifying all topic papers |

## Topic Papers

| File | Topic | Key Contribution |
|------|-------|-----------------|
| [explainable_legal_reasoning.md](explainable_legal_reasoning.md) | Explainable legal reasoning | Overview of how the system achieves explainability through formal methods |
| [non_monotonicity.md](non_monotonicity.md) | Non-monotonicity | Proof that the unified evaluator is non-monotone and must be split into stages |
| [dp_impossibility.md](dp_impossibility.md) | DP impossibility | Counterexample proving privilege level does not determine unique epsilon |
| [graph_similarity_topology.md](graph_similarity_topology.md) | Graph similarity | Topological properties and counterexamples of graph similarity measures |
| [multi_ai_formalization.md](multi_ai_formalization.md) | Multi-AI methodology | Methodology paper on adversarial multi-AI formal verification |
| [argumentation_frameworks.md](argumentation_frameworks.md) | Argumentation | ASPIC+ framework formalization for structured legal argumentation |
| [legal_reasoning_paradigms.md](legal_reasoning_paradigms.md) | Reasoning paradigms | Four paradigms formalized as composable modules |
| [probabilistic_legal_reasoning.md](probabilistic_legal_reasoning.md) | Probabilistic reasoning | Bayesian evidence evaluation and damages quantification |
| [argument_strength.md](argument_strength.md) | Argument strength | Partial order on argument strength in adversarial settings |
| [legal_analogy.md](legal_analogy.md) | Legal analogy | Case-based analogical reasoning with formal retrieval |
| [mathematical_structures.md](mathematical_structures.md) | Mathematical structures | Lattice theory, fixpoint theory, sheaf theory applied to law |
| [ai_liability_infrastructure.md](ai_liability_infrastructure.md) | AI liability | Trust labels as infrastructure for AI liability allocation |

## Reading Order

For newcomers:

1. Start with `main.md` or `main_cn.md` for the complete mathematical framework
2. Read `non_monotonicity.md` for the key architectural insight
3. Read `dp_impossibility.md` for the privacy impossibility results
4. Explore topic papers based on your interest

## Paper Status

As of 2026-06-25, the formal core (`formal-core-v1`) has been released. The papers
capture the mathematical state at release. Banach and empirical calibration topics
remain at research-track status (not part of the released formal core).
