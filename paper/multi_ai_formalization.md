# Adversarial Multi-AI Formalization: A Methodology for Trustworthy Mathematical Modeling

**Author:** Laupinco — Hokkien Computational Jurisprudence Enthusiast

**Case study:** juris-calculus legal math modeling | **Companion repo:** [legal-math-modeling](https://github.com/laubeing-droid/legal-math-modeling)

---

## Abstract

We present *adversarial multi-AI formalization*, a methodology for producing trustworthy mathematical models using multiple AI agents in an adversarial pipeline. The methodology consists of four stages: (1) a generator AI produces mathematical definitions, theorems, and proof code; (2) a formal verification AI audits the proofs using 7 independent tool chains; (3) an independent AI produces alternative proofs and data validation; (4) a second audit pass downgrades overstated claims. We demonstrate this methodology on a legal reasoning framework, where 20 initial mathematical claims were audited down to 18 verified positive results and 10 counterexamples through 4 rounds of adversarial repair. The key contribution is not any individual proof but the *evidence-calibrated trust label system* that tracks each claim through its lifecycle.

**Keywords:** AI-assisted mathematics, formal verification, adversarial audit, multi-agent systems, trust calibration, computational law

---

## 1. Introduction

Large language models (LLMs) can generate mathematical proofs that *look correct* but contain logical errors. A single AI reviewing its own work has inherent blind spots — it is likely to reproduce the same reasoning patterns that led to the error in the first place.

This paper proposes a solution: **adversarial multi-AI formalization**, where different AI agents with different verification modalities cross-check each other's work. The methodology is demonstrated on a real-world case study: building a formal mathematical framework for cross-jurisdictional legal reasoning.

---

## 2. The Methodology

### 2.1 Four-Stage Pipeline

```
Stage 1: GENERATE (Claude, Anthropic)
  → Mathematical modeling and reverse engineering
  → Output: 47 formulas, 23 algorithms, 38 constants, 20 theorem skeletons

Stage 2: VERIFY (Codex, OpenAI)
  → Formal verification with 7 tool chains
  → Hypothesis (PBT), Z3 (SMT), CrossHair, TLA+, Alloy, Lean 4, Dafny
  → Output: 12 verification categories, 1 counterexample found

Stage 3: INDEPENDENT REWORK (Kimi, Moonshot AI)
  → Legal data collection + independent proof construction
  → Output: 8/8 runnable proofs pass, 3 Lean drafts PENDING

Stage 4: ADVERSARIAL AUDIT (Codex, second pass)
  → Downgrade overstated claims
  → Output: 7 FAIL → 4 repair rounds → 46/46 PASS
```

### 2.2 The Adversarial Principle

Each AI agent is given a *different verification modality*:

| Agent | Modality | What It Catches |
|-------|----------|----------------|
| Claude | Code generation + assertion checking | Syntactic errors, missing edge cases |
| Codex | Line-by-line audit of "declared vs proved" | Logical gaps, false premises |
| Kimi | Independent proof + data validation | Different proof strategies, data issues |
| Codex (2nd) | Re-audit after repairs | Regressions, newly introduced errors |

The adversarial structure ensures that **no single AI's failure mode goes undetected**.

---

## 3. Case Study: 46/46 Convergence

### 3.1 Initial State: 20 Claims

Claude generated 20 mathematical theory modules, each claiming to prove a theorem about legal reasoning. All 20 modules ran without errors and printed "PASS" or "VERIFIED."

### 3.2 Codex Audit: 7 FAIL

The first Codex audit found 7 fatal errors:

| # | Module | Error |
|---|--------|-------|
| 1 | Banach contraction | Compression factor c=1.0 (not c<1) |
| 2 | Horn-Dung correspondence | Test output contradicts theorem |
| 3 | Category Rosetta | is_natural returns True (claim says False) |
| 4 | Gradual verification | Proof runs on simplified model, not actual engine |
| 5 | DP privilege mapping | can_share_with direction reversed |
| 6 | Non-interference | allows_flow direction reversed |
| 7 | Counts-as institutional | Missing gradual verification rule pre-queuing |

### 3.3 Four Rounds of Repair

| Round | Actions | Result |
|-------|---------|--------|
| 1 | Fix Banach (c<1 analytic), TriRail (non-empty evaluator), Galois (⇐ direction) | 3 FAIL → fixed |
| 2 | Fix Horn-Dung (exception attack direction), Rosetta (US extra claim injection) | 2 FAIL → fixed |
| 3 | Strengthen abstract interpretation, MDL (CONJECTURE label), GV (assertion gating) | 3 SUSPECT → strengthened |
| 4 | Fix DP (direction), non-interference (direction), counts-as (GV pre-queuing) | 3 FAIL → fixed |

**Final state**: 20/20 PASS, 0 FAIL. Plus 4 additional verification files (Z3, SymPy, Hypothesis, mutation testing). Total: 46/46 PASS.

### 3.4 What Changed: Not Just Bug Fixes

The repair process did not just fix bugs — it *improved the mathematical framework*:

- **Banach**: The failure (c=1.0) revealed that the pricing model needed a proper Lipschitz constant analysis, not just a smoothing parameter.
- **Graph similarity**: The reflexivity counterexample led to renaming from "metric" to "similarity function" — a more honest mathematical characterization.
- **DP privilege**: The direction reversal revealed a fundamental impossibility result — legal privilege cannot determine ε.
- **Evaluator monotonicity**: The counterexample led to the stratified Horn+AAF architecture — a better system design.

---

## 4. The Evidence-Calibrated Trust Label System

### 4.1 Motivation

The 46/46 convergence is impressive, but "all PASS" is not enough. Different claims have different levels of mathematical certainty. A system that treats them all equally is overconfident.

### 4.2 Seven-Level Status Lattice

Every claim is assigned one of seven statuses:

| Status | Epistemic Meaning |
|--------|-------------------|
| PROVED_BY_EXHAUSTIVE_ENUMERATION | All cases checked |
| REFUTED_BY_COUNTEREXAMPLE | Explicit counterexample exists |
| PARTIAL_PROVED | Some stages proved, others open |
| DATA_INSUFFICIENT_FOR_PROOF | Data exists but is incomplete |
| TOY_SYNTHETIC_PROOF_ONLY | Only works on constructed examples |
| PENDING_TOOLCHAIN | Proof script exists, tool not available |
| ENGINEERING_BASELINE | Design assumption, not a proof |

### 4.3 The Core Innovation

The trust label system is not just documentation — it is **code**. Each claim is registered in `model_status.py` with:
- `allowed_claim`: the strongest assertion the evidence supports
- `forbidden_claim`: assertions that must never be made
- `engineering_action`: what to do with the result
- `evidence_paths`: where to find the proof artifacts

This transforms every mathematical claim into a *falsifiable engineering decision* with explicit boundaries.

---

## 5. Generality of the Methodology

The adversarial multi-AI formalization methodology is not specific to legal reasoning. It applies to any domain where:

1. Mathematical claims are generated by AI
2. Independent verification is possible (code can be run, proofs can be checked)
3. Different verification modalities exist (testing, proving, model checking, data validation)

**Candidate domains:**
- Drug discovery (molecular property predictions)
- Financial modeling (risk calculations)
- Engineering design (structural integrity proofs)
- Scientific computing (numerical method convergence)

The key requirement is that **the output must be machine-checkable**. Pure prose arguments cannot be adversarially verified.

---

## 6. Limitations

1. **The methodology reduces but does not eliminate errors.** Two AIs can miss the same bug. More audit passes reduce the probability but cannot guarantee zero.

2. **Cost.** Running 4 AI agents across 20+ modules with 7 tool chains is expensive. The case study consumed approximately $50-100 in API costs.

3. **The human is still needed.** The methodology produces a *trust-calibrated* set of claims, not a set of *unconditionally true* claims. Human judgment is required to interpret the trust labels and make deployment decisions.

---

## 7. Conclusion

The adversarial multi-AI formalization methodology demonstrates that **multiple AI agents in adversarial configuration produce more trustworthy mathematical models than any single agent alone**. The case study shows a concrete path from 7/20 FAIL to 20/20 PASS through 4 rounds of adversarial repair, with the evidence-calibrated trust label system tracking every claim's epistemic status.

The strongest claim a mathematical framework can make is the one its evidence supports. This methodology provides the machinery to make that principle operational.

---

## References

1. Dung, P.M. (1995). On the acceptability of arguments. *AIJ*, 77(2).
2. Tarski, A. (1955). A lattice-theoretical fixpoint theorem. *PJM*, 5(2).
3. Kleene, S.C. (1952). *Introduction to Metamathematics*.
4. de Moura, L. & Ullrich, S. (2021). The Lean 4 Theorem Prover. *CADE 2021*.
5. de Moura, L. & Bjørner, N. (2008). Z3: An Efficient SMT Solver. *TACAS 2008*.
