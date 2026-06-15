# Legal Math Modeling

> **Clone and read**: `git clone` this repo → open `paper/main.md` on GitHub → KaTeX renders all 70 formal definitions/theorems/counterexamples natively.
>
> This repository is the **mathematical companion** to [juris-calculus](https://github.com/laubeing-droid/juris-calculus) — a deterministic symbolic legal reasoning engine operating across PRC, Hong Kong, and US jurisdictions. It contains the formal mathematical framework, 30 runnable proof modules, machine-reproducible verification artifacts, and a 7-level *evidence-calibrated trust label system* that prevents unverified AI-generated claims from propagating to engineering decisions.
>
> **Start here**: Run `python -m theory` to see the trust label status of all 7 core mathematical claims. Then read `paper/main.md` for the full formal treatment.

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

For the first time, legal reasoning is formalized as a complete mathematical framework — Horn clauses for forward reasoning, Dung argumentation for adversarial reasoning, Kripke models for temporal reasoning, category theory for cross-jurisdictional mapping — with *machine-reproducible proofs* for each component. This is not a theoretical paper that proposes a framework; it is a *working system* with 30 runnable proof modules and 66,066 enumerated attack graphs.

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
│  model_status.py (7 core claims registered)                  │
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

## 3.1 Proved Claims (18)

| ID | Theorem | Method | Evidence Scale |
|----|---------|--------|---------------|
| T4.2 | Bounded Horn compilation correctness | Exhaustive enumeration | 3,965 acyclic KBs |
| T4.3 | Horn closure monotonicity | Analytic proof | — |
| T4.5 | Horn 5 operational properties | Hypothesis PBT | 82,836 random KBs |
| T5.3 | Dung AAF grounded extension (n ≤ 4) | Exhaustive enumeration | 66,066 attack graphs |
| T6.4 | Stage 1 (Horn) is monotone | Analytic proof | — |
| T6.5 | Stage 2 (AAF construction) is deterministic | Enumeration | 10 fixtures |
| T7.3 | Kripke R_supersedes ∩ R_corrects = ∅ | Z3 SMT UNSAT | — |
| T7.4 | □(t_fact < t_procedure) temporal guard | Z3 SMT induction | — |
| T8.3 | Toy Rosetta: no collision-free functor | Exhaustive enumeration | 243 assignments |
| T9.2 | Scalar Banach contraction (β < 1) | SymPy symbolic | — |
| T10.2 | CN lattice: no monotone ε function | Z3 SMT UNSAT | — |
| T11.2 | 60 CBL rules = Bell-LaPadula non-interference | Structural analysis | 60 rules |
| T12.4 | Trust label internal consistency | Programmatic validation | — |
| — | Galois incidence (finite) | Exhaustive | 74,954 fixtures |
| — | Galois powerset (finite) | Exhaustive | 74,954 fixtures |
| — | Bounded Horn correctness | Exhaustive | 3,965 acyclic KBs |
| — | Horn termination (5 properties) | Exhaustive | 82,836 KBs |
| — | Fixpoint bounded termination | Exhaustive | 5 configs |

## 3.2 Refuted Claims (10)

| ID | Claim | Counterexample |
|----|-------|---------------|
| CE6.2 | Original evaluator is monotone | A={a} ⊂ B={a,b}, E(A)={a}, E(B)=∅ |
| CE6.7 | Cross-graph monotonicity | Adding fact shrinks grounded extension |
| CE9.4 | Full-dimensional Banach contraction | Metric space undefined; mapping_status is discrete |
| CE10.3 | Privilege determines DP ε | Two-model witness: CN=1.0, US=2.5 |
| CE10.4 | Floor clipping satisfies ε-DP | Privacy ratio → ∞ |
| — | Graph similarity reflexivity | sim(∅,∅) = 0.4 ≠ 1.0 |
| — | Graph similarity identity of indiscernibles | C4 cycle vs star+edge, both score 1.0 |
| — | Graph similarity is a metric | Reflexivity/identity counterexamples |
| — | Clipped Theil-Sen = pure Theil-Sen | 5/6 datasets differ |
| — | 18 theorems derivable from Galois | 17 in independent domains |

## 3.3 Data-Insufficient / Toy-Only / Pending (12)

| ID | Claim | Status | Bottleneck |
|----|-------|--------|-----------|
| T8.5 | Real Rosetta functor | DATA_INSUFFICIENT | 44 rows, 7 witnesses; need ≥2,000 |
| T9.4 | Real Banach contraction | DATA_INSUFFICIENT | 225 proxy observations, 0 real timesheets |
| — | Galois Lean proof | PENDING_TOOLCHAIN | Needs Mathlib, contains `sorry` |
| — | Banach Lean proof | PENDING_TOOLCHAIN | Needs Mathlib, contains `sorry` |
| — | Rosetta Lean proof | PENDING_TOOLCHAIN | Needs Mathlib, contains `sorry` |
| — | Horn Z3 .smt2 | PENDING_TOOLCHAIN | Needs Z3 binary |
| — | Fixpoint TLA+ | PENDING_TOOLCHAIN | Needs TLC |

# 4. Repository Structure

```
legal-math-modeling/                          290 files, 5.2 MB
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
├── theory/                                   # 30 Python theory modules
│   ├── model_status.py                       # ★ Trust label system
│   ├── argumentation_horn_unification.py     # Dung AAF + Horn stratified
│   ├── category_theory_rosetta.py            # Cross-jurisdiction functor
│   ├── banach_pricing_contraction.py         # Pricing contraction
│   ├── dp_legal_privilege.py                 # DP ε vs legal privilege
│   ├── temporal_kripke_ltl.py                # Temporal Kripke + LTL
│   ├── z3_kripke_mutex.py                    # Z3 mutual exclusion
│   ├── z3_temporal_induction.py              # Z3 temporal induction
│   ├── sympy_evidence_proofs.py              # SymPy symbolic proofs
│   ├── hypothesis_horn_pbt.py                # Hypothesis PBT
│   └── ... (30 total)
│
├── proofs/                                   # Machine-run proof artifacts
│   ├── strict_proof_baseline/                # Canonical strict baseline (8/8 pass)
│   ├── engineering_proof_artifacts/          # Kimi engineering proofs (17 artifacts)
│   └── formal_verification_logs/             # Codex 7-tool-chain verification
│
├── data/                                     # Legal validation datasets
│   ├── cn_legal/                             # PRC legal claims (6 categories)
│   ├── us_legal/                             # US legal generation
│   ├── hk_legal/                             # HK obstruction + privilege lattice
│   ├── aaf_legal/                            # AAF validation (13 files)
│   ├── banach_pricing/                       # Pricing evidence (4 files)
│   ├── category_rosetta/                     # Rosetta corpus (29 files)
│   ├── dp_privilege/                         # DP jurisdiction lattices
│   └── galois_semantics/                     # Galois audit + dependency graph
│
├── docs/                                     # Documentation
│   ├── modeling/                             # 8 modeling documents
│   ├── audit/                                # Trust label schema, counterexample registry
│   ├── ontology/core_ontology.yaml           # L0/L1/L2 ontology (1,298 lines)
│   └── history/development_log_*.md          # 22-day development journal
│
└── prompts/                                  # Reproducible AI prompts
    ├── claude_math_audit_prompt.md
    └── kimi_playbook.md
```

# 5. Quick Start

```bash
git clone https://github.com/laubeing-droid/legal-math-modeling.git
cd legal-math-modeling

# Install dependencies
pip install -r requirements.txt

# Run the trust label system
python -m theory

# Run a specific proof
python proofs/strict_proof_baseline/p1e_aaf/dung_grounded_extension.py

# Run all strict proofs
python proofs/strict_proof_baseline/run_all_proofs.py
```

### Read the paper

```bash
# GitHub-native (recommended): open paper/main.md — KaTeX renders all formulas
# LaTeX PDF: cd paper && xelatex main.tex && biber main && xelatex main.tex && xelatex main.tex
```

# 6. Extended Theoretical Foundations

The `theory/` directory contains 30 formalization modules beyond the core paper. These provide theoretical scaffolding for the main results:

| Module | Mathematical Framework | Status |
|--------|----------------------|--------|
| `galois_reverse_index.py` | Galois connection (keyword ↔ atom) | Exhaustive (74,954 fixtures) |
| `evidence_credibility_axioms.py` | S(e) = r × i × a (Cobb-Douglas) | Symbolic proofs |
| `kripke_supersedes_corrects.py` | Kripke dual accessibility relations | Z3 UNSAT |
| `policy_expressiveness.py` | Policy layer = stratifiable CTRS (P-complete) | Analytic |
| `gradual_verification_soundness.py` | "Compiler is not a judge" | Analytic |
| `trirail_complexity.py` | TriRail joint satisfiability | Analytic |
| `counts_as_institutional_facts.py` | Searle's X counts-as Y in context C | Engineering baseline |
| `rough_set_discretionary.py` | Pawlak rough sets for discretionary concepts | Engineering baseline |
| `paradigm_incommensurability.py` | Stevens measurement theory (ordinal vs ratio) | Engineering baseline |
| `deontic_procedural_justice.py` | Standard Deontic Logic + temporal operators | Engineering baseline |
| `non_interference_cbl.py` | Bell-LaPadula for concept smuggling | Proved |
| `kolmogorov_mdl_rules.py` | Exception chain depth ↔ Kolmogorov complexity | Conjecture |
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
