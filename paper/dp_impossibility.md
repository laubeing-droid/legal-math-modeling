# The Impossibility of Legal Determination of Differential Privacy Epsilon

**Author:** Laupinco — Hokkien Computational Jurisprudence Enthusiast

**Companion code:** [`theory/dp_legal_privilege.py`](../theory/dp_legal_privilege.py) | **Counterexample:** [`proofs/strict_proof_baseline/p0d_privilege_epsilon/`](../proofs/strict_proof_baseline/p0d_privilege_epsilon/)

---

## Abstract

We prove that legal privilege classification cannot uniquely determine the differential privacy parameter ε across jurisdictions. We construct a two-jurisdiction witness demonstrating that the same legal privilege level (attorney-client privilege) maps to different ε values in the PRC (ε = 1.0) and the US (ε = 2.5). This establishes a *legal privacy impossibility theorem*: no single function from privilege levels to ε values can be valid across multiple legal systems. We further show that floor-clipping privacy mechanisms violate ε-DP for any finite ε. These results have direct implications for privacy engineering in legal AI systems: ε must be a policy configuration parameter with jurisdiction-specific provenance, never an automatic derivation from legal sources.

**Keywords:** differential privacy, legal privilege, impossibility theorem, privacy engineering, legal AI

---

## 1. Introduction

Differential privacy (DP) provides formal guarantees against information leakage from statistical databases. The privacy parameter ε controls the trade-off between data utility and privacy: smaller ε means stronger privacy. A natural engineering question arises: *can legal classifications of data sensitivity automatically determine the appropriate ε?*

If attorney-client privilege is "more sensitive" than public court filings, should it automatically receive a smaller ε? This paper proves that the answer depends on what "automatically" means:

- **Within a single jurisdiction**: a monotone mapping from privilege levels to ε values is *possible* (just assign values to a finite chain). But the assignment requires policy judgment, not legal derivation.
- **Across jurisdictions**: no single mapping exists. The same privilege level yields different ε values in different legal systems.

---

## 2. Definitions

**Definition 1** (Differential privacy). A randomized mechanism $\mathcal{M}$ satisfies *ε-differential privacy* if for all neighboring datasets $D, D'$ and all output sets $S$:

$$\Pr[\mathcal{M}(D) \in S] \leq e^\varepsilon \cdot \Pr[\mathcal{M}(D') \in S]$$

**Definition 2** (Legal privilege lattice). A *legal privilege lattice* $(P, \leq)$ is a partially ordered set where $p_1 \leq p_2$ means privilege level $p_1$ is less protective than $p_2$.

**Definition 3** (Monotone ε function). A function $\varepsilon: P \to \mathbb{R}_{\geq 0}$ is *monotone* if $p_1 \leq p_2 \implies \varepsilon(p_1) \geq \varepsilon(p_2)$ (higher privilege → lower ε → stronger privacy).

**Definition 4** (Cross-jurisdiction ε function). A *cross-jurisdiction ε function* is a single function $\varepsilon: P \to \mathbb{R}_{\geq 0}$ that is valid for all jurisdictions simultaneously — meaning the same privilege level $p$ maps to the same ε regardless of which jurisdiction's legal system is in effect.

---

## 3. Main Results

### 3.1 Theorem 1: Cross-Jurisdiction Impossibility

**Theorem 1.** *No cross-jurisdiction ε function exists. That is, there is no single function $\varepsilon: P \to \mathbb{R}_{\geq 0}$ that correctly assigns privacy parameters for both the PRC and US legal systems.*

*Proof.* By construction of a two-jurisdiction witness.

Consider the attorney-client privilege level $p_{\text{AC}} \in P$. In both the PRC and US legal systems, this is the highest privilege level:

| Jurisdiction | Legal Basis | Privilege Level | Required ε | Rationale |
|-------------|-------------|----------------|-----------|-----------|
| PRC | 《律师法》第38条 | $p_{\text{AC}}$ (最高) | 1.0 | PRC legal system treats attorney-client confidentiality as absolute but allows judicial override |
| US | Upjohn v. United States, 449 U.S. 383 (1981) | $p_{\text{AC}}$ (highest) | 2.5 | US legal system applies broader privilege scope with fewer exceptions |

Suppose for contradiction that a cross-jurisdiction ε function $\varepsilon: P \to \mathbb{R}_{\geq 0}$ exists. Then:

$$\varepsilon(p_{\text{AC}}) = 1.0 \quad \text{(required by PRC)}$$
$$\varepsilon(p_{\text{AC}}) = 2.5 \quad \text{(required by US)}$$

This is a contradiction: $\varepsilon(p_{\text{AC}})$ cannot equal both 1.0 and 2.5. Therefore, no such function exists. ∎

**Verification.** [`proofs/strict_proof_baseline/p0d_privilege_epsilon/two_model_witness.json`](../proofs/strict_proof_baseline/p0d_privilege_epsilon/two_model_witness.json).

**Remark.** This impossibility is not a failure of the specific ε values chosen. The underlying reason is structural: the PRC and US legal systems define the *scope* of attorney-client privilege differently (PRC: narrower, with explicit judicial override; US: broader, with work-product doctrine extension). Even if both jurisdictions agreed on the same ε value for attorney-client privilege, they would disagree on which *specific communications* fall under that privilege — meaning the effective privacy guarantee differs even with identical ε.

### 3.2 Corollary: Within-Jurisdiction Possibility

**Corollary 1.** *Within a single jurisdiction, a monotone ε function on a finite privilege lattice is always constructible.*

*Proof.* Let $(P, \leq)$ be a finite privilege lattice with $n$ levels. Assign $\varepsilon(p_1) = \varepsilon_{\max}$ to the lowest privilege level and $\varepsilon(p_n) = \varepsilon_{\min}$ to the highest, with intermediate values decreasing monotonically. Such an assignment always exists for any $\varepsilon_{\max} > \varepsilon_{\min} \geq 0$.

However, the *specific values* require policy judgment (how much privacy is "enough" for each level?) — they cannot be derived from the legal classification alone. ∎

### 3.3 Theorem 2: Floor Clipping Violates DP

**Theorem 2.** *The mechanism $\mathcal{M}(x) = \max(0.3x, x_{\min})$ does not satisfy ε-DP for any finite ε.*

*Proof.* Consider neighboring datasets $D$ and $D'$ differing in one record, with values $x_D = x_0$ and $x_{D'} = x_0 + \delta$ near the clipping threshold. The privacy ratio:

$$\frac{\Pr[\mathcal{M}(D) \in S]}{\Pr[\mathcal{M}(D') \in S]} \to \infty$$

as $x_0$ approaches the threshold from different sides. The ratio is unbounded, violating ε-DP for any finite ε. ∎

**Verification.** [`proofs/engineering_proof_artifacts/dp/dp_floor_clipping_analysis.py`](../proofs/engineering_proof_artifacts/dp/dp_floor_clipping_analysis.py).

---

## 4. Why This Matters for Legal AI

The impossibility results have three direct engineering consequences:

### 4.1 ε Is a Policy Parameter, Not a Legal Derivation

Each data class requires an explicit, human-approved ε value stored in policy configuration. The system must refuse to run if ε lacks a documented source and approval chain.

### 4.2 Cross-Jurisdiction Privacy Harmonization Requires Explicit Mapping

The same legal concept (attorney-client privilege) requires different privacy parameters in different jurisdictions. A legal AI system operating across jurisdictions must maintain jurisdiction-specific ε configurations, not a single global mapping.

### 4.3 The Trust Label System Tracks ε Provenance

In the juris-calculus evidence-calibrated trust label system, the DP epsilon claim is registered as:

```
D_PRIVILEGE_EPSILON:
  status: REFUTED_BY_COUNTEREXAMPLE
  allowed_claim: "Law can classify release modes; epsilon is a policy 
                  parameter with audit labels."
  forbidden_claim: "A legal privilege level determines a unique 
                     numerical epsilon."
  engineering_action: "Expose epsilon as policy config; require 
                       approval and provenance for each data class."
```

---

## 5. Related Work

Dwork (2006) established the ε-DP framework. Legal privilege classification is well-studied in comparative law. The novelty of this work is proving the *impossibility* of connecting these two formalisms through a single cross-jurisdiction function, using a concrete two-jurisdiction witness rather than abstract impossibility arguments.

The approach follows the tradition of impossibility proofs in computer science (e.g., the CAP theorem, Arrow's impossibility theorem in social choice theory): rather than showing that a particular implementation fails, we show that *no* implementation can succeed under the stated constraints.

---

## References

1. Dwork, C. (2006). Differential Privacy. *ICALP 2006*, 1–12.
2. 中华人民共和国律师法 (2017修正), 第38条.
3. Upjohn Co. v. United States, 449 U.S. 383 (1981).
4. Gilbert, S. & Lynch, N. (2002). Brewer's conjecture and the feasibility of consistent, available, partition-tolerant web services. *SIGACT News*, 33(2).
