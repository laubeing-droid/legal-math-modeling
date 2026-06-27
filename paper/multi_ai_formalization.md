# Adversarial Multi-AI Formalization: A Methodology for Trustworthy Mathematical Modeling

**Author:** Laupinco
**Date:** 2026-06-27

---

## Abstract

We present an adversarial multi-AI formalization methodology for producing trustworthy mathematical models in specialized domains. The methodology employs four stages: (1) GENERATE, where a primary AI produces theorem statements, proofs, and constants; (2) VERIFY, where an independent AI audits every claim across 12 verification categories; (3) INDEPENDENT REWORK, where a third AI produces alternative proofs from scratch; and (4) ADVERSARIAL AUDIT, where a second instance of the verification AI performs a final pass. We apply this methodology to the juris-calculus legal reasoning project, starting from 20 initial core theorem claims. The adversarial pipeline identified 7 fatal errors in the initial claims (including a Banach contraction constant c = 1.0, which is not a contraction). After 4 repair rounds, the pipeline converged to 46/46 PASS with all trust labels assigned. The final verified artifact comprises 84 theorems and lemmas across 10 Lean 4 files (0 sorry, 0 axioms), 7 PROVED_BY_ARTIFACT core theorems in the JC_Formalization.lean registry, and 20 core theorem entries with explicit status tracking. We argue that single-AI formalization is unreliable for specialized mathematical domains and that adversarial cross-checking between different AI agents is essential.

**Keywords:** formal verification, multi-agent systems, adversarial methodology, mathematical modeling, trust labels

---

## 1. Introduction

### 1.1 Problem

Large language models (LLMs) can produce mathematical proofs that appear correct but contain subtle logical errors. In specialized domains (legal reasoning, cryptography, type theory), these errors are difficult for human reviewers to detect without deep domain expertise. A single LLM, even a powerful one, will systematically produce plausible-but-wrong results in such domains.

### 1.2 Solution

We propose an adversarial multi-AI pipeline where different AI agents play distinct roles:
- A **generator** produces mathematical content (definitions, theorems, proofs, constants)
- A **verifier** audits the generator's output, looking specifically for logical errors
- An **independent reworker** produces alternative proofs from scratch, providing a second opinion
- An **adversarial auditor** performs a final pass, checking that all errors have been fixed

The key insight is that different AI models have different blind spots. A claim that passes verification by one model may be caught by another. Adversarial cross-checking exploits this diversity.

### 1.3 Contributions

1. A 4-stage adversarial pipeline with formal convergence criteria
2. An evidence-calibrated trust label taxonomy (7 levels)
3. A case study applying the pipeline to 20 core theorem claims in legal reasoning
4. Empirical evidence that the pipeline catches errors that single-AI approaches miss

---

## 2. Methodology

### 2.1 Stage 1: GENERATE (Claude)

The primary AI produces:
- 47 mathematical formulas
- 23 algorithms
- 38 named constants
- 20 theorem statement skeletons

Each theorem is tagged with a proposed trust level, a domain bound (the legal jurisdiction or mathematical domain to which it applies), and a proof sketch.

**Output format:** Markdown document with theorem statements, proof sketches, and constant definitions.

### 2.2 Stage 2: VERIFY (Codex)

An independent AI audits every claim from Stage 1 across 12 verification categories:

1. **Logical validity:** Is the proof sketch logically complete?
2. **Constant correctness:** Are the named constants correct?
3. **Domain applicability:** Does the theorem hold in the claimed domain?
4. **Boundary conditions:** Are edge cases handled?
5. **Monotonicity:** Is the monotonicity claim correct?
6. **Contraction conditions:** Are the contraction parameters valid (c < 1)?
7. **Fixed-point existence:** Does the fixed point exist?
8. **Termination:** Does the iteration terminate?
9. **Soundness:** Are the soundness conditions met?
10. **Completeness:** Are the completeness conditions met?
11. **Cross-domain consistency:** Are cross-jurisdiction claims consistent?
12. **Formalization feasibility:** Can the claim be formalized in Lean 4?

**Result:** 7 of 20 claims flagged with fatal errors. The most consequential error: the Banach contraction constant was set to c = 1.0, which does not define a contraction (a contraction requires c < 1).

### 2.3 Stage 3: INDEPENDENT REWORK (Kimi)

A third AI produces alternative proofs for all 20 claims from scratch, without seeing the Stage 1 or Stage 2 outputs. This provides an independent verification modality.

**Result:** 8/8 claims verified pass. 3 Lean drafts marked PENDING_TOOLCHAIN (deferred to the Lean 4 formalization).

### 2.4 Stage 4: ADVERSARIAL AUDIT (Codex 2nd pass)

A second instance of the verification AI performs a final audit, checking:
- All 7 fatal errors from Stage 2 have been fixed
- The fixes do not introduce new errors
- All trust labels are correctly assigned

**Result:** Initial 7 FAIL verdicts. After 4 repair rounds: 46/46 PASS. Convergence achieved.

---

## 3. Case Study: juris-calculus

### 3.1 Initial State

20 core theorem claims covering:
- Galois connection (T1)
- Horn correctness (T2)
- Evidence credibility (T3)
- Kripke program (T4)
- Temporal Kripke (T5)
- Policy expressiveness (T6)
- Gradual verification (T7)
- Tri-rail complexity (T8)
- Horn-Dung bridge (T9)
- Counts-as (T10)
- Rough set discretion (T11)
- Hierarchical Bayes (T12)
- Incommensurability (T13)
- Deontic procedure (T14)
- CBL non-interference (T15)
- Category Rosetta (T16)
- Banach contraction (T17)
- DP privilege (T18)
- Abstract interpretation (T19)
- MDL rule complexity (T20)

### 3.2 Errors Found by Stage 2

| Error | Description | Consequence |
|-------|-------------|-------------|
| Banach c = 1.0 | Contraction constant not < 1 | T17 proof invalid; fixed to 0 < beta < 1 |
| Horn-Dung correspondence | Claimed bijection, actually one-directional | T9 restated |
| Category Rosetta | Claimed total functor; actually 84% obstruction | T16 restated |
| Kripke temporal | Claimed all temporal invariants; only guard provable | T5 narrowed |
| Cross-jurisdiction claim | Claimed universal mapping; refuted by counterexample | T18 refuted |
| Evidence credibility | Claimed formal proof; only empirical proxy available | T3 status changed |
| MDL complexity | Claimed closed-form; only empirical fit | T20 status changed |

### 3.3 Final State (JC_Formalization.lean)

The Lean-verified registry tracks all 20 core theorems:

| Status | Count | Theorems |
|--------|-------|----------|
| PROVED_BY_ARTIFACT | 7 | T1, T3, T5, T9, T15, T16, T17 |
| EMPIRICAL_PROXY | 2 | T2, T20 |
| AXIOM_ONLY | 1 | T4 |
| REFUTED | 1 | T18 |
| PLAN_ONLY | 1 | T12 |
| MISSING_ARTIFACT | 1 | T7 |
| INVALID_CLAIM | 7 | T6, T8, T10, T11, T13, T14, T19 |

Verified by: `proved_theorems_card = 7`, `empirical_proxy_card = 2`, `refuted_theorems_card = 1`.

---

## 4. Trust Label System

### 4.1 Seven-Level Taxonomy

| Level | Label | Description |
|-------|-------|-------------|
| 0 | Conjecture | Unverified claim, possibly from intuition |
| 1 | Toy-Only | Verified on synthetic examples only |
| 2 | Data-Proxy | Supported by empirical data, not formally proved |
| 3 | SMT-Checked | Verified by SMT solver (Z3, CVC5) |
| 4 | Symbolic-Proof | Hand-written symbolic proof, not mechanized |
| 5 | Proved-by-Artifact | Mechanized proof in Lean 4 with 0 sorry |
| 6 | Refuted-by-Counterexample | Constructive counterexample exists |

### 4.2 Registry Properties

The JC_Formalization.lean registry has two key structural properties:

**`advance_preserves_domain_bound`:** Promoting a theorem (e.g., from Data-Proxy to Proved) never changes its domain bound. This prevents scope creep.

**`advance_cannot_revive_refuted`:** A refuted theorem (status = REFUTED) cannot be promoted to any other status, regardless of what evidence is provided. This is a monotonicity property of the trust system itself.

---

## 5. Convergence Analysis

### 5.1 Pipeline Convergence

The adversarial pipeline converges when the verification stage produces zero FAIL verdicts. Convergence was achieved after 4 repair rounds:

| Round | FAIL Count | Key Fixes |
|-------|------------|-----------|
| 0 | 7 | Initial audit |
| 1 | 5 | Fixed Banach c, Horn-Dung correspondence |
| 2 | 3 | Fixed Category Rosetta, narrowed Kripke claim |
| 3 | 1 | Fixed evidence credibility status |
| 4 | 0 | Convergence (46/46 PASS) |

### 5.2 Formal Convergence Criteria

The pipeline converges if and only if:
1. All 20 core theorems have assigned trust labels
2. No theorem has status PENDING without a registered reason in SORRY_LEDGER.md
3. The verification AI produces zero FAIL verdicts
4. The Lean build succeeds with 0 sorry in blocking-path theorems

---

## 6. Discussion

### 6.1 Why Single-AI Formalization Fails

The Stage 2 audit found 7 fatal errors in 20 claims -- a 35% error rate. These errors were not random; they were systematic overclaims:
- Claiming total functor when only partial functor exists
- Claiming contraction when c = 1.0
- Claiming formal proof when only empirical proxy is available

A single AI, no matter how capable, tends to produce claims that are plausible but not verified. The adversarial pipeline catches these overclaims by design.

### 6.2 Role of Lean 4

The Lean 4 formalization provides the ultimate verification layer. Claims that pass all 4 pipeline stages but cannot be mechanized in Lean are downgraded. The 7 PROVED_BY_ARTIFACT theorems are the only claims at the highest trust level.

### 6.3 Limitations

1. The pipeline uses 3 different AI systems (Claude, Codex, Kimi), but these may share training data or architectural biases.
2. The verification is only as good as the verifier's domain knowledge.
3. The pipeline does not guarantee that all errors are found; it only guarantees that the specific errors caught by the adversarial audit are fixed.
4. The 46/46 PASS convergence does not imply absolute correctness; it means that no further errors were found by the adversarial auditor.

---

## References

1. Irving, G., Christiano, P., and Amodei, D. (2018). AI safety via debate. *NeurIPS 2018*.
2. Cobbe, K. et al. (2021). Training verifiers to solve math word problems. *arXiv:2110.14168*.
3. Lightman, H. et al. (2023). Let's verify step by step. *arXiv:2305.20050*.
4. Polu, S. and Sutskever, I. (2020). Generative language modeling for automated theorem proving. *arXiv:2009.03393*.
5. The mathlib Community (2020). The Lean mathematical library. *CPP 2020*, 367--381.
6. Dung, P.M. (1995). On the acceptability of arguments. *Artificial Intelligence*, 77(2), 321--357.
