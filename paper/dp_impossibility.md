# The Impossibility of Legal Determination of Differential Privacy Epsilon

**Author:** Laupinco
**Date:** 2026-06-27

---

## Abstract

We prove that legal privilege classification cannot uniquely determine differential privacy epsilon across jurisdictions. A two-jurisdiction counterexample suffices: attorney-client privilege maps to epsilon = 1.0 under PRC law (Lawyers Law, Art. 38) and epsilon = 2.5 under US law (Upjohn v. United States, 1981). This result is registered in the JC_Formalization.lean theorem registry as T18 (DPPrivilege) with status REFUTED and evidence type COUNTEREXAMPLE. The registry property `refuted_theorems_card = 1` confirms exactly one refuted core theorem, and `advance_cannot_revive_refuted` guarantees that a refuted theorem cannot be promoted to any higher status. We further show that floor-clipping privacy mechanisms (a common engineering pattern) violate epsilon-differential privacy for any finite epsilon. The impossibility result has practical consequences: privacy-preserving legal systems must calibrate epsilon per jurisdiction rather than deriving it from legal categories.

**Keywords:** differential privacy, legal privilege, impossibility, cross-jurisdiction, formal verification

---

## 1. Introduction

### 1.1 Problem

Modern privacy-preserving legal systems need a numerical privacy parameter epsilon that governs the noise injected into query results. A natural engineering question arises: can the legal classification of data sensitivity (e.g., attorney-client privilege, medical confidentiality, state secrets) uniquely determine epsilon?

Within a single jurisdiction, the answer is trivially yes: a policy maker can assign epsilon = 1.0 to privileged data and epsilon = 5.0 to non-privileged data. But this assignment is a *policy judgment*, not a *legal derivation*. The law says "this data is privileged"; it does not say "this data requires epsilon = 1.0."

Across jurisdictions, the question becomes sharper and the answer is no. We prove:

**Theorem 1.** There is no cross-jurisdiction epsilon function that is both consistent with each jurisdiction's privilege lattice and yields a unique epsilon for each privilege class.

### 1.2 Connection to Formal Verification

The JC_Formalization.lean registry tracks 20 core theorems. T18 (DPPrivilege) is the only theorem with status REFUTED. The Lean-verified property `refuted_theorems_card = 1` confirms this count, and `advance_cannot_revive_refuted` ensures that once a claim is refuted by counterexample, no amount of additional evidence can promote it. This is the formal mechanism that prevents a refuted claim from being laundered into proved status.

### 1.3 Scope

This paper addresses a narrow but important claim: that legal categories *determine* epsilon. We do not claim that legal categories are *irrelevant* to epsilon selection (they are clearly relevant as policy inputs). We claim only that the mapping is not a function.

---

## 2. Definitions

### 2.1 Differential Privacy

**Definition 1 (epsilon-DP).** A randomized mechanism M satisfies epsilon-differential privacy if for all datasets D, D' differing in one record, and all subsets S of the output space:

Pr[M(D) in S] <= exp(epsilon) * Pr[M(D') in S]

The parameter epsilon controls the privacy-utility tradeoff: smaller epsilon means stronger privacy but less utility.

### 2.2 Legal Privilege Lattice

**Definition 2 (Privilege Lattice).** A privilege lattice for jurisdiction J is a finite partially ordered set (L_J, <=) where elements represent privilege classes and the ordering represents information sensitivity. The bottom element represents the least sensitive class (no privilege) and the top represents the most sensitive.

For PRC: {non-privileged < commercial-secret < personal-privacy < attorney-client < state-secret}.
For US: {non-privileged < business-confidential < attorney-client < work-product < classified}.

### 2.3 Monotone Epsilon Function

**Definition 3 (Monotone Epsilon).** An epsilon function for jurisdiction J is a mapping e_J : L_J -> R^+ such that for all x <= y in L_J, e_J(x) >= e_J(y) (more privilege implies smaller epsilon, hence stronger privacy).

### 2.4 Cross-Jurisdiction Epsilon Function

**Definition 4 (Cross-Jurisdiction Epsilon).** A cross-jurisdiction epsilon function is a mapping e : L_PRC x L_US -> R^+ that agrees with each jurisdiction's monotone epsilon function when restricted to that jurisdiction's lattice.

---

## 3. Main Results

### 3.1 Theorem 1: Cross-Jurisdiction Impossibility

**Theorem 1.** There exists no cross-jurisdiction epsilon function that is simultaneously monotone on both the PRC and US privilege lattices and yields a unique epsilon for each privilege class.

**Proof (by counterexample).** Consider the privilege class "attorney-client privilege," which exists in both jurisdictions.

Under PRC law (Lawyers Law, Art. 38), attorney-client privilege is narrower: it covers communications between a lawyer and client for the purpose of legal consultation, but does not extend to the work-product doctrine. A reasonable policy calibration yields epsilon_PRC(attorney-client) = 1.0.

Under US law (Upjohn v. United States, 1981), attorney-client privilege is broader: it extends to corporate communications with counsel for the purpose of obtaining legal advice, and interacts with the work-product doctrine. A reasonable policy calibration yields epsilon_US(attorney-client) = 2.5.

Now suppose a cross-jurisdiction epsilon function e exists that assigns a unique epsilon to "attorney-client privilege" independent of jurisdiction. Then e("attorney-client") must equal both 1.0 (to be consistent with PRC calibration) and 2.5 (to be consistent with US calibration). Since 1.0 != 2.5, no such function exists. QED.

### 3.2 Theorem 2: Floor-Clipping Violation

**Theorem 2.** A floor-clipping mechanism (which clips query outputs to a domain-specific minimum) violates epsilon-DP for any finite epsilon.

**Proof sketch.** Let D and D' differ in one record such that D contains a privileged entry and D' does not. The clipping mechanism maps certain outputs to the same floor value, making the output distributions on D and D' differ by more than a factor of exp(epsilon) for any finite epsilon, because the floor creates a point mass that is either present or absent depending on the privileged record. QED.

### 3.3 Practical Consequence

The impossibility result implies that privacy-preserving legal systems must:
1. Calibrate epsilon per jurisdiction, not derive it from privilege categories
2. Treat epsilon as a policy parameter, not a legal fact
3. Document the calibration basis for each jurisdiction separately

---

## 4. Formal Verification Status

| Component | Status | Evidence |
|-----------|--------|----------|
| T18 (DPPrivilege) claim | REFUTED | JC_Formalization.lean, `theorem_metadata .T18_DPPrivilege` |
| `refuted_theorems_card = 1` | Proved (0 sorry) | JC_Formalization.lean |
| `advance_cannot_revive_refuted` | Proved (0 sorry) | JC_Formalization.lean |
| Cross-jurisdiction counterexample | Constructive | PRC epsilon=1.0 vs US epsilon=2.5 |
| Floor-clipping violation | Proof sketch | Not mechanized in Lean |

**Trust Labels:**
- T18 (DPPrivilege): Refuted-by-Counterexample
- Cross-jurisdiction counterexample: Constructive (not Lean-mechanized)
- Floor-clipping violation: Proof sketch (pending mechanization)

**What is NOT claimed:**
- We do not claim that epsilon *cannot* be chosen based on legal categories (it can, as a policy judgment).
- We do not claim that all cross-jurisdiction mappings are impossible (only the epsilon-function claim is refuted).
- We do not claim that the counterexample extends to all privacy definitions (it applies to epsilon-DP specifically).

---

## 5. Related Work

**Dwork et al. (2006).** The foundational definition of differential privacy. Our work addresses the question of whether legal categories can parameterize this definition.

**Nissim et al. (2007).** The sensitivity framework for calibrating noise. Our floor-clipping counterexample shows that certain domain-specific mechanisms violate the standard DP framework.

**Hart (1961).** The concept of legal categories as rules of recognition. Our impossibility result can be interpreted as showing that Hart's rules of recognition do not determine the epsilon parameter of differential privacy.

---

## References

1. Dwork, C., McSherry, F., Nissim, K., and Smith, A. (2006). Calibrating noise to sensitivity in private data analysis. *TCC 2006*, 265--284.
2. Nissim, K., Raskhodnikova, S., and Smith, A. (2007). Smooth sensitivity and sampling in private data analysis. *STOC 2007*, 75--84.
3. Upjohn Co. v. United States, 449 U.S. 383 (1981).
4. PRC Lawyers Law (2017 revision), Article 38.
5. Hart, H.L.A. (1961). *The Concept of Law*. Oxford University Press.
6. The mathlib Community (2020). The Lean mathematical library. *CPP 2020*, 367--381.
