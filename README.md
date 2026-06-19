# Legal Math Modeling

> **Clone and read**: `git clone` this repo → open `paper/main.md` on GitHub → KaTeX renders formal definitions/theorems/counterexamples natively. For a consolidated paper, see `paper/icail_full_paper.md`.
>
> This repository is the **mathematical companion** to [juris-calculus](https://github.com/laubeing-droid/juris-calculus) — a deterministic symbolic legal reasoning engine operating across PRC, Hong Kong, and US jurisdictions. It contains the formal mathematical framework, 59 runnable theory modules, machine-reproducible verification artifacts, and a 7-level *evidence-calibrated trust label system* that prevents unverified AI-generated claims from propagating to engineering decisions.
>
> **Current status (v5.0, Playbook v5.0)**: 20 core theorems identified; **5 PROVED_BY_ARTIFACT**, 2 EMPIRICAL_PROXY, 1 AXIOM_ONLY, 2 PENDING_TOOLCHAIN, 1 REFUTED, 9 excluded (INVALID_CLAIM / MISSING_ARTIFACT). Lean `lake build` 2948 jobs with 0 sorry, 0 axiom in build files. 42 adversarial tests pass. 4/4 Z3 verification pass.
>
> **Start here**: Run `python -m theory` to see the trust label status of all core mathematical claims. Then read `paper/explainable_legal_reasoning.md` for the formal treatment.

[English](#1-overview) | [中文](README_CN.md)

---

# Technical Documentation

> This document records the complete technical report for the Legal Math Modeling project: problem definition, system design, formal verification results, and open problems.

# 1. Overview

Existing computational legal systems rely on probabilistic retrieval-augmented generation (RAG) — they produce plausible-sounding legal analysis but offer no formal guarantees about soundness, completeness, or cross-jurisdictional consistency. When an AI system says "this contract is valid," there is no way to verify whether the reasoning chain is logically sound or merely a confident hallucination.

This repository presents a fundamentally different approach: **law as mathematics**. We formalize legal reasoning as a system of Horn clauses, abstract argumentation frameworks, Kripke temporal models, and category-theoretic mappings — then *prove* properties about these formalisms using exhaustive enumeration, SMT solvers, symbolic computation, and property-based testing.

The key innovation is not the individual mathematical models, but the **evidence-calibrated trust label system** that tracks every claim through its proof lifecycle. When a claim is refuted by counterexample, we record the counterexample. When data is insufficient, we say so. When a proof only works on toy models, we label it `TOY_SYNTHETIC_PROOF_ONLY` and forbid downstream systems from treating it as production truth.

> **The strongest claim you can make is the one your evidence supports — and no stronger.**

## 1.1 What These Models Actually Mean for Legal Practice

Each mathematical model in this repository solves a concrete legal problem that current AI systems cannot handle:

**Horn Closure Monotonicity (proved)** — The engine never "forgets" a fact it has already established. In contract review, once the system determines that a contract was formed (offer + acceptance + consideration), this conclusion cannot be retracted by adding more evidence. This is *not* how LLM-based systems work: a probabilistic system can flip its conclusion if you rephrase the question. The monotonicity proof guarantees that legal reasoning is *stable* under information accumulation.

**Dung AAF Grounded Extension (proved for n ≤ 4)** — Legal arguments attack each other. The plaintiff argues breach; the defendant argues force majeure; the plaintiff counters that the force majeure clause has a carve-out. The grounded extension finds the set of arguments that *survive all attacks* — the arguments that are "legally defensible" regardless of what the opposing side does. This is the mathematical backbone of adversarial legal reasoning: not "what is true?" but "what is defensible?"

**Kripke Temporal Invariant □(t\_fact < t\_proced) (proved)** — A court cannot reference a fact that has not yet been established. This seems obvious, but AI systems routinely violate it: they mix evidence from different procedural stages, cite post-judgment developments in pre-trial analysis, or conflate the plaintiff's alleged facts with the court's findings. The temporal guard makes this *impossible* in the formal engine — it is a structural guarantee, not a guideline.

**CBL Non-Interference (proved)** — US legal concepts like "discovery" and "plea bargaining" have no equivalent in PRC law. If these concepts "smuggle" into a Chinese legal analysis, the output is legally meaningless. The 60 CBL blocking rules act as a firewall: no US concept can influence PRC reasoning without passing through a formal alignment gate. This is not a translation layer — it is a *security property* proved using Bell-LaPadula information-flow theory.

**Counterexamples (10 refuted claims)** — The most valuable outputs in this repository are the *failures*. When we proved that the original evaluator is not monotone (Counterexample 6.2: adding fact `b` causes the system to retract its conclusion about `a`), we did not hide this result — we *split the engine* into a monotone Horn stage and a non-monotone AAF stage. When we proved that legal privilege cannot determine a unique DP ε (Counterexample 10.3: same privilege level, different ε in CN vs US), we redesigned ε as a policy parameter. Each counterexample made the system more honest and more architecturally sound.

**Trust Labels** — A lawyer using this system sees not just a conclusion, but a confidence label: "This contract analysis is based on exhaustive verification over 66,066 argument structures" vs. "This pricing estimate is a toy model that only works on synthetic data." This transforms the AI from an oracle that may hallucinate into a *reasoning assistant that tells you exactly how much to trust it*.

## 1.2 The Core Question This Repository Answers

> **Can we build a legal AI system that is mathematically honest about what it knows and what it doesn't?**

The answer is yes — but only if we accept that some claims will be labeled `DATA_INSUFFICIENT` or `REFUTED` instead of pretending everything is `PROVED`. The evidence-calibrated trust label system is the mechanism that makes this possible. It turns every mathematical claim into a *falsifiable engineering decision* with explicit allowed claims, forbidden claims, and engineering actions.

## 1.3 Historical Significance

### What came before

Legal AI has gone through three generations, each with a fundamental limitation:

| Generation | Approach | Limitation |
|-----------|----------|-----------|
| **Gen 1** (2015–2020) | Rule-based expert systems | Brittle, no formal guarantees, no cross-jurisdiction |
| **Gen 2** (2020–2024) | LLM + RAG (ChatGPT, legal chatbots) | Probabilistic, hallucination-prone, no audit trail |
| **Gen 3** (2024–2025) | LLM + structured prompts + tool use | Better output, still no formal soundness guarantees |

All three generations share the same blind spot: **they cannot tell you how much to trust their own output**. A Gen 2 system will confidently state "this contract is valid" even when its reasoning chain contains a logical error. There is no mechanism to distinguish "proved by exhaustive enumeration" from "plausible but unverified."

### What this repository introduces

This work represents a **paradigm shift** from "legal chatbot" to "legal compiler with formal verification":

**1. Law as a formal system, not a prompt engineering problem.**

For the first time, legal reasoning is formalized as a complete mathematical framework — Horn clauses for forward reasoning, Dung argumentation for adversarial reasoning, Kripke models for temporal reasoning, category theory for cross-jurisdictional mapping — with *machine-reproducible proofs* for each component. This is not a theoretical paper that proposes a framework; it is a *working system* with 59 runnable proof modules and 66,066 enumerated attack graphs.

**2. The evidence-calibrated trust label system: a new standard for AI honesty.**

Previous legal AI systems made binary claims: "the system can do X" or "the system cannot do X." This repository introduces a 7-level evidence ladder that tracks every mathematical claim from conjecture to proof (or refutation). When a claim is refuted by counterexample, the counterexample is *preserved as a first-class artifact*, not deleted or hidden. This inverts the traditional incentive structure: instead of hiding failures to look competent, the system *celebrates* counterexamples because each one makes the architecture more honest.

**3. The k ≤ 3 boundary: a principled answer to "where does formal verification stop?"**

H.L.A. Hart's "penumbra of doubt" — the observation that legal concepts have a core of certainty surrounded by a penumbra of ambiguity — has resisted formalization for 60 years. This repository proposes a concrete engineering answer: formalize everything up to depth k ≤ 3 (where Horn closure is provably monotone), and flag everything beyond as `TAINTED` requiring human review. This is not a theoretical compromise; it is a *deployment-ready architecture* that balances computational soundness with legal utility.

**4. Multi-AI adversarial verification: a new methodology for mathematical research.**

This is the first mathematical framework verified through an adversarial multi-AI pipeline: Claude generates proofs, Codex audits them with 7 tool chains, Kimi produces independent proof reworks, and a second Codex audit downgrades overstated claims. The result is not "AI proved these theorems" but "AI proved these theorems, *and here is the evidence trail showing exactly what was proved, what was refuted, and what remains uncertain*."

**5. Counterexamples as scientific contributions.**

Traditional mathematical papers celebrate theorems and bury failed attempts. This repository inverts that convention: the 10 counterexamples (evaluator non-monotonicity, DP ε non-determinability, graph non-metricity, ...) are treated as *equally important* as the 18 positive results. Each counterexample triggered an architectural redesign that made the system more robust. The counterexample registry (`docs/audit/counterexample_registry.json`) is a permanent, machine-readable record of what the system learned from its failures.

### Why this matters for the future of legal AI

The legal industry is at an inflection point. Courts are beginning to use AI for case analysis. Law firms are deploying AI for contract review. Regulators are asking: "How do we know these systems are reliable?" 

Current legal AI systems cannot answer that question. They can say "our system achieved 94% accuracy on our test set" — but they cannot say "our system's reasoning is *provably monotone* up to depth 3" or "this specific claim was *refuted by counterexample* on June 9, 2026."

This repository provides the vocabulary and the machinery for a different kind of answer: **not "trust us" but "here is the evidence, here are the limitations, and here is what we do when we discover we are wrong."**

That is the real contribution — not any individual theorem, but the *system of intellectual honesty* in which the theorems, counterexamples, and open problems coexist.

# 2. System Design

## 2.1 Core Paradigm: Bounded Formal Verification

Legal reasoning is fundamentally *open-textured* — concepts like "reasonable," "fairness," and "proportionality" resist full formalization. Therefore, our goal is not a "fully provably correct legal compiler" (which is impossible), but a **bounded formal verification system**:

```
┌─────────────────────────────────────────────────────────────┐
│                    USER CONSTRAINTS                         │
│  Jurisdiction + Case Type + Evidence Set + Legal Questions   │
└──────────────────────────┬──────────────────────────────────┘
                           │
                           ▼
┌─────────────────────────────────────────────────────────────┐
│              LAYER 1: Legal Ontology (L0/L1/L2)              │
│                                                              │
│  L0 Primitives: Agent, Asset, Act, Status, Power, Defect     │
│  L1 Meta-Ontology: 15 abstract legal categories              │
│  L2 Domain Concepts: 20+ jurisdiction-specific atoms          │
│                                                              │
│  core_ontology.yaml (1,298 lines)                            │
└──────────────────────────┬──────────────────────────────────┘
                           │
                           ▼
┌─────────────────────────────────────────────────────────────┐
│         LAYER 2: Two-Stage Reasoning Engine                  │
│                                                              │
│  ┌──────────────────┐     ┌───────────────────────┐        │
│  │  Stage 1: Horn    │ ──→ │  Stage 2: Dung AAF    │        │
│  │  Closure (k ≤ 3)  │     │  Grounded Extension   │        │
│  │                    │     │                       │        │
│  │  2,117 PRC rules  │     │  Rebuttal, Exception, │        │
│  │  Forward chaining  │     │  Counter-rebuttal     │        │
│  │  Monotone ✓ Proved │     │  Verified n ≤ 4 ✓     │        │
│  └──────────────────┘     └───────────────────────┘        │
│                                                              │
│  If exception chain k ≥ 4: TAINTED flag (soft boundary)     │
│  If cyclic dependency: REJECT (hard boundary)                │
└──────────────────────────┬──────────────────────────────────┘
                           │
                           ▼
┌─────────────────────────────────────────────────────────────┐
│         LAYER 3: Evidence-Calibrated Trust Labels            │
│                                                              │
│  Every output carries a trust label:                         │
│    PROVED → REFUTED → PARTIAL → INSUFFICIENT → TOY → PENDING│
│                                                              │
│  model_status.py (20 core theorems registered)               │
│  Forbidden tags enforced in CI/CD                            │
└──────────────────────────┬──────────────────────────────────┘
                           │
                           ▼
┌─────────────────────────────────────────────────────────────┐
│         LAYER 4: Cross-Jurisdiction Collider                 │
│                                                              │
│  Tri-Rail: PRC × HK × US parallel reasoning traces          │
│  12 conflict classes detected                                │
│  60 CBL blocking rules (= Bell-LaPadula non-interference)    │
│  23 SPC judicial tendency guards                             │
└─────────────────────────────────────────────────────────────┘
```

## 2.2 Why This Is Different

| Dimension | Legal RAG (Most Systems) | Legal Math Modeling |
|-----------|-------------------------|---------------------|
| Logic | Probabilistic (LLM) | Deterministic (Horn + Fixpoint) |
| Audit | Blackbox (prompt) | Whitebox (DAG trace + proof artifact) |
| Cross-jurisdiction | None | Tri-Rail Collider (12 conflict classes) |
| Hallucination risk | High | Low (honest refusal + trust labels) |
| Paradigm | Chatbot | Symbolic AI / Computational Law |
| Mathematical claims | Unverified | 7-level evidence calibration |
| Counterexamples | Not tracked | Explicitly registered and preserved |

## 2.3 The k ≤ 3 Boundary

The reasoning engine operates under a strict depth bound:

> **k ≤ 3** is the **provably safe zone**: Horn closure is monotone, fixpoint convergence is guaranteed, and all properties are formally verified.
>
> **k ≥ 4** is the **operable but not fully verifiable zone**: the engine still runs, but every output is flagged with a `TAINTED` degradation notice.

This is not a limitation — it is a *design choice*. In regulatory contexts, saying "this legal structure is too complex for deterministic evaluation, requires human review" is defensible. Saying "the AI hallucinated an invalid contract because it stack-overflowed in an exception chain" is not.

## 2.4 Multi-AI Verification Pipeline

This work was produced through an iterative multi-AI formalization pipeline — each agent contributed a different verification modality:

```
┌───────────────┐     ┌───────────────┐     ┌───────────────┐
│    Claude      │ ──→ │    Codex       │ ──→ │    Kimi        │
│  (Anthropic)   │     │   (OpenAI)     │     │ (Moonshot AI)  │
│                │     │                │     │                │
│ Math modeling  │     │ 7 tool chains  │     │ Legal data     │
│ 47 formulas    │     │ Hypothesis     │     │ collection     │
│ 23 algorithms  │     │ Z3, Lean 4     │     │ Strict proof   │
│ 38 constants   │     │ TLA+, Alloy    │     │ rework         │
│ 20 theorem     │     │ CrossHair      │     │ 8/8 proofs     │
│ skeletons      │     │ Dafny          │     │ pass           │
└───────┬───────┘     └───────┬───────┘     └───────┬───────┘
        │                     │                     │
        └─────────────────────┼─────────────────────┘
                              │
                              ▼
                   ┌───────────────────┐
                   │   Codex Audit     │
                   │                   │
                   │ Found: 7 FAIL     │
                   │ 4 repair rounds   │
                   │ Result: 46/46 ✓   │
                   │                   │
                   │ Established       │
                   │ trust label system│
                   └───────────────────┘
```

# 3. Formal Verification Results

> **v5.0 Honesty Note**: After a Codex red-team audit, all claims were re-evaluated. Several previously claimed "PROVED" results were downgraded to EMPIRICAL_PROXY or AXIOM_ONLY. See `docs/audit/theorem_status_matrix.md` for the full audit trail.

## 3.1 Proved by Artifact (5)

These theorems have runnable checkers that produce PASS:

| Theorem | Statement | Method | Evidence Scale |
|---------|-----------|--------|---------------|
| T1_GaloisConnection | Finite join-semilattice residuated map admits Galois connection | Lean 4 + Mathlib (0 sorry) | FinitePoset class |
| T3_EvidenceCredibility | S(e) = r × i × a (credibility formula) | Design axiom + SymPy | Syntactic properties |
| T9_HornDungBridge | Horn rules constructively map to Dung AF | Exhaustive enumeration | 66,066 attack graphs |
| T16_CategoryRosetta | CN_ONLY dominates claim mapping (30/44) | Exhaustive on real data | 44 Supreme Court claims |
| T17_BanachContraction | Banach contraction for scalar pricing | Lean 4 + Mathlib (0 sorry) | Effective nodes |

## 3.2 Empirical Proxy (2 — correlation, not causation)

| Theorem | Statement | Evidence | Limitation |
|---------|-----------|----------|-----------|
| T2_HornCorrectness | Horn closure = LFP for finite acyclic KB | 3,969 acyclic KB exhaustive + 50K sampling | Only acyclic domain; not universal proof |
| T20_MDLRuleComplexity | MDL correlates with cross-domain FP risk | Domain-level ρ=0.4272, p=0.0022 | Claim-level ρ=0.1168 not significant; bootstrap CI includes 0 |

## 3.3 Axiom-Only (1 — Z3 consistency check, not proof)

| Theorem | Statement | Why not proved |
|---------|-----------|---------------|
| T4_KripkeProgram | R_supersedes / R_corrects mutually exclusive | Z3 asserts the axiom and checks consistency; does not derive from independent premises |

## 3.4 Refuted (permanent exclusion)

| ID | Claim | Counterexample |
|----|-------|---------------|
| CE6.2 | Original evaluator is monotone | A={a} ⊂ B={a,b}, E(A)={a}, E(B)=∅ |
| CE10.4 | Floor clipping satisfies ε-DP | Privacy ratio → ∞ |
| T18_DPPrivilege | Privilege mechanism satisfies ε-DP | Infinite privacy ratio counterexample |

## 3.5 Pending / Excluded

| Status | Count | Theorems |
|--------|-------|----------|
| PENDING_TOOLCHAIN | 2 | T5_TemporalKripke, T15_CBLNonInterference |
| INVALID_CLAIM (product scope) | 6 | T6, T8, T10, T11, T13, T14, T19 |
| MISSING_ARTIFACT | 1 | T7_GradualVerification |

## 3.6 Engineering Verification

| Check | Result |
|-------|--------|
| Lean `lake build` | 2948 jobs, 0 sorry, 0 axiom (in build files) |
| Z3 verification | 4/4 PASS (constraint consistency, LFP monotonicity, π_legal equivalence, DP smoothing) |
| Adversarial tests | 13/13 PASS (8 core + 5 extended) |
| Benchmark cases | 25 cases across 6 domains |
| Graph metric | All 3 axioms verified (identity, symmetry, triangle inequality) |

# 4. Repository Structure

```
legal-math-modeling/                          322 files, 7.4 MB
├── README.md                                 # This file (English)
├── README_CN.md                              # Chinese version
├── LICENSE                                   # CC BY 4.0
├── CITATION.cff                              # Academic citation
├── .gitignore
├── requirements.txt                          # hypothesis, z3-solver, sympy, numpy
│
├── paper/                                    # ★ Formal mathematical paper
│   ├── main.md                               # GitHub-native (KaTeX rendered)
│   ├── main.tex                              # LaTeX source
│   ├── references.bib                        # 21 references
│   └── sections/                             # 13 chapters
│       ├── 01_introduction.tex
│       ├── 02_preliminaries.tex
│       ├── 03_ontology.tex
│       ├── 04_horn_closure.tex
│       ├── 05_aaf_argumentation.tex
│       ├── 06_stratified_evaluator.tex
│       ├── 07_kripke_temporal.tex
│       ├── 08_category_rosetta.tex
│       ├── 09_banach_contraction.tex
│       ├── 10_dp_privilege.tex
│       ├── 11_non_interference.tex
│       ├── 12_evidence_calibrated.tex
│       └── 13_conclusion.tex
│
├── theory/                                   # 59 Python theory modules
│   ├── model_status.py                       # ★ Trust label system
│   ├── argumentation_horn_unification.py     # Dung AAF + Horn stratified
│   ├── category_theory_rosetta.py            # Cross-jurisdiction functor
│   ├── banach_pricing_contraction.py         # Pricing contraction
│   ├── dp_legal_privilege.py                 # DP ε vs legal privilege + SmoothClipper
│   ├── temporal_kripke_ltl.py                # Temporal Kripke + LTL
│   ├── graph_metric.py                       # MCS-based graph distance metric
│   ├── judgment_deviation.py                 # 3D deviation checker (D_bayes+D_mdl+D_aaf)
│   ├── bayesian_calibration.py               # Bayesian calibration with LOO-CV
│   ├── mdl_fp_analysis.py                    # MDL vs FP risk analysis
│   ├── temporal_integration.py               # Temporal law integration
│   ├── jurisdiction_guard.py                 # Cross-jurisdiction routing guard
│   ├── evidence_evaluation.py                # Evidence evaluation with word-boundary matching
│   └── ... (59 total)
│
├── proofs/                                   # Machine-run proof artifacts
│   ├── strict_proof_baseline/                # Canonical strict baseline (8/8 pass)
│   ├── engineering_proof_artifacts/          # Engineering proofs + adversarial tests
│   │   ├── adversarial/                      # 13 adversarial tests (8+5)
│   │   └── cross_jurisdiction/               # Cross-jurisdiction guard tests
│   ├── lean/juris_lean/                      # ★ Lean 4 formalization (lake build 2948 jobs)
│   │   ├── JurisLean/JC_Formalization.lean   # Core theorem metadata (0 sorry)
│   │   ├── JurisLean/FiniteGaloisAdjunction.lean # Galois connection (0 sorry)
│   │   ├── JurisLean/FiniteRosetta.lean      # Rosetta real data (0 sorry)
│   │   └── JurisLean/BanachEffectiveNodes.lean # Banach contraction (0 sorry)
│   └── formal_verification_logs/             # Codex 7-tool-chain verification
│
├── verification/                             # Z3 SMT verification engine
│   └── verification_engine.py                # 4 checks: consistency, LFP, π_legal, DP
│
├── data/                                     # Legal validation datasets
│   ├── benchmarks/                           # 25 benchmark cases (6 domains)
│   ├── external/                             # External data
│   │   ├── compas_scores_two_years.csv       # 7214 COMPAS records
│   │   ├── legalbench/                       # 2529 items (11 tasks)
│   │   └── supreme_court/extracted_rules.json # 310 rules (20 volumes)
│   ├── cn_legal/                             # PRC legal claims (6 categories)
│   ├── us_legal/                             # US legal generation
│   └── ... (other datasets)
│
├── reports/                                  # Verification reports
│   ├── mdl_fp/                               # MDL vs FP analysis (v1/v2/v3)
│   ├── bayesian_calibration/                 # LOO-CV + COMPAS results
│   └── verification/verification_results.json # Z3 verification results
│
├── docs/                                     # Documentation
│   ├── modeling/                             # 8 modeling documents
│   ├── audit/                                # Trust label schema, theorem status matrix
│   │   ├── theorem_status_matrix.md          # Full theorem status with red-team annotations
│   │   ├── proof_ledger.json                 # Proof artifact ledger
│   │   └── codex_audit_report_20260619.md    # Codex red-team audit report
│   └── history/development_log_*.md          # Development journal
```
```

## 4.1 Paper Structure

The repository contains 13 papers covering the full formalization. `main.md` is the core paper (13 chapters); the remaining 12 are standalone deep-dives on specific topics.

| Paper | Content | Key Results |
|-------|---------|-------------|
| `main.md` | Core formal paper (Ch1--13): ontology, Horn closure, AAF, Kripke temporal, category-theoretic Rosetta, Banach contraction, DP privilege, CBL non-interference, trust labels | 18 proved claims, 10 counterexamples, 7-level trust label system, k <= 3 safe boundary |
| `icail_full_paper.md` | Consolidated ICAIL conference submission combining all papers into a single manuscript | Full formalization with unified bibliography; subsumes all other papers |
| `non_monotonicity.md` | Formal treatment of non-monotonicity in the two-stage evaluator (Horn + AAF) | CE6.2: original evaluator non-monotone; architectural split into monotone Horn stage + non-monotone AAF stage |
| `dp_impossibility.md` | Differential privacy impossibility results for legal privilege lattices | CE10.3: privilege level does not determine unique epsilon; CE10.4: floor clipping violates epsilon-DP |
| `graph_similarity_topology.md` | Graph similarity measures and their topological properties for legal citation networks | Counterexamples to reflexivity, identity of indiscernibles, and metric axioms |
| `multi_ai_formalization.md` | Methodology paper on adversarial multi-AI proof verification (Claude + Codex + Kimi) | Pipeline design, 46/46 verification pass, 4 repair rounds, trust label calibration protocol |
| `argumentation_frameworks.md` | ASPIC+ framework formalization for structured legal argumentation | Extended argumentation with preferences, defeat relations, and proof standards |
| `legal_reasoning_paradigms.md` | Survey and formalization of four legal reasoning paradigms | Analogical reasoning, precedent reasoning, statutory interpretation, interest balancing formalized as composable modules |
| `probabilistic_legal_reasoning.md` | Bayesian approaches to legal evidence evaluation and damages quantification | Bayesian network for evidence aggregation, Theil-Sen robust estimation, probabilistic damages model |
| `argument_strength.md` | Partial order on argument strength in adversarial legal settings | Argument strength ordering with formal lattice structure; connects to AAF grounded extension |
| `legal_analogy.md` | Case-based analogical reasoning with formal retrieval | Analogical reasoning engine + case retrieval by factor similarity; Searle-style institutional fact mapping |
| `ai_liability_infrastructure.md` | Formal framework for AI liability as infrastructure-level risk allocation | Model status tracking, evidence dependency chains, liability allocation across deployer/developer/infrastucture layers |

# 5. Quick Start

```bash
git clone https://github.com/laubeing-droid/legal-math-modeling.git
cd legal-math-modeling

# Install dependencies
pip install -r requirements.txt

# Run the trust label system
python -m theory

# Run Z3 verification (4 checks)
python verification/verification_engine.py

# Run adversarial tests
python -m pytest proofs/engineering_proof_artifacts/adversarial/

# Run all strict proofs
python proofs/strict_proof_baseline/run_all_proofs.py

# Build Lean formalization (requires Lean 4 + Mathlib)
cd proofs/lean/juris_lean && lake build
```

### Read the paper

```bash
# GitHub-native (recommended): open paper/main.md — KaTeX renders all formulas
# LaTeX PDF: cd paper && xelatex main.tex && biber main && xelatex main.tex && xelatex main.tex
```

# 6. Extended Theoretical Foundations

The `theory/` directory contains 59 formalization modules beyond the core paper. These provide theoretical scaffolding for the main results:

| Module | Mathematical Framework | Status |
|--------|----------------------|--------|
| `galois_reverse_index.py` | Galois connection (keyword ↔ atom) | Exhaustive (74,954 fixtures) |
| `evidence_credibility_axioms.py` | S(e) = r × i × a (Cobb-Douglas) | Symbolic proofs |
| `kripke_supersedes_corrects.py` | Kripke dual accessibility relations | Z3 UNSAT |
| `graph_metric.py` | MCS-based graph distance metric | All 3 axioms verified |
| `judgment_deviation.py` | 3D deviation (D_bayes + D_mdl + D_aaf) | Runnable, 11 properties proved |
| `bayesian_calibration.py` | Bayesian calibration with LOO-CV | Brier=0.2209 (n=13) |
| `mdl_fp_analysis.py` | MDL vs FP risk analysis | Domain-level ρ=0.4272 |
| `temporal_integration.py` | Temporal law integration (dual timestamp) | Runnable |
| `jurisdiction_guard.py` | Cross-jurisdiction routing guard | 44 claim mappings |
| `non_interference_cbl.py` | Bell-LaPadula for concept smuggling | Proved |
| `kolmogorov_mdl_rules.py` | Exception chain depth ↔ Kolmogorov complexity | Empirical proxy |
| `abstract_interpretation_unified.py` | Cousot & Cousot abstract interpretation | Engineering baseline |
| `hierarchical_bayes_alpha.py` | Hierarchical Bayes for Theil-Sen α | Engineering baseline |

All modules are runnable Python with embedded assertions. Run any module directly to verify its claims.

# 7. License

[CC BY 4.0](LICENSE) — You are free to share and adapt this material for any purpose, provided you give appropriate credit.

# 8. Citation

See [CITATION.cff](CITATION.cff).

```bibtex
@software{legal_math_modeling_2026,
  title   = {Legal Math Modeling: A Formal Framework for Cross-Jurisdictional
             Symbolic Legal Reasoning with Evidence-Calibrated Trust Labels},
  author  = {Laupinco},
  year    = {2026},
  url     = {https://github.com/laubeing-droid/legal-math-modeling},
  license = {CC-BY-4.0}
}
```
