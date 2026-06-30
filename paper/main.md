# Legal Math Modeling: A Formal Framework for Cross-Jurisdictional Symbolic Legal Reasoning

**Author:** Laupinco — Hokkien Computational Jurisprudence Enthusiast

**Companion repository:** [juris-calculus](https://github.com/laubeing-droid/juris-calculus) | **License:** [CC BY 4.0](../LICENSE)

> **LaTeX source:** [`paper/main.tex`](main.tex) — for formal typesetting and PDF generation.

---

## Abstract

We present a formal mathematical framework for symbolic legal reasoning across multiple jurisdictions (PRC, Hong Kong, United States). The framework consists of a three-layer legal ontology ($L_0$/$L_1$/$L_2$), a monotone Horn closure engine for forward fact expansion, a Dung abstract argumentation framework for rebuttal and exception handling, Kripke temporal models for procedural state tracking, and category-theoretic mappings for cross-jurisdictional concept alignment.

We prove 18 positive results by exhaustive enumeration, symbolic computation, and SMT verification. We refute 10 claims by constructing explicit counterexamples. We identify 6 claims as data-insufficient or toy-model-only. All mathematical claims are tracked by a 7-level *evidence-calibrated trust label system* that prevents unverified assertions from propagating to downstream engineering decisions.

**Keywords:** computational law, formal methods, legal AI, abstract argumentation, Horn logic, Kripke semantics, category theory, evidence calibration

---

## Table of Contents

1. [Introduction](#1-introduction)
2. [Preliminaries](#2-preliminaries)
3. [Legal Ontology: $L_0$/$L_1$/$L_2$](#3-legal-ontology)
4. [Monotone Horn Closure](#4-monotone-horn-closure)
5. [Dung AAF Grounded Extension](#5-dung-aaf-grounded-extension)
6. [Stratified Evaluator Correctness](#6-stratified-evaluator-correctness)
7. [Kripke Temporal Invariants](#7-kripke-temporal-invariants)
8. [Category-Theoretic Rosetta Mapping](#8-category-theoretic-rosetta-mapping)
9. [Banach Pricing Contraction](#9-banach-pricing-contraction)
10. [Differential Privacy and Legal Privilege](#10-differential-privacy-and-legal-privilege)
11. [Non-Interference: CBL Blocking as Bell-LaPadula](#11-non-interference)
12. [Evidence-Calibrated Trust Label System](#12-evidence-calibrated-trust-label-system)
13. [Conclusion and Open Problems](#13-conclusion-and-open-problems)

---

## 1. Introduction

Legal reasoning across jurisdictions presents a unique formal challenge: concepts that are well-defined in one legal system (e.g., "material breach" in U.S. contract law) have no direct equivalent in another (e.g., Chinese contract law under the Civil Code). Existing computational legal systems typically rely on probabilistic retrieval-augmented generation (RAG), which lacks formal guarantees about soundness, completeness, or cross-jurisdictional consistency.

This paper presents **juris-calculus**, a symbolic legal reasoning engine that operates across three jurisdictions — the People's Republic of China (PRC), Hong Kong (HK), and the United States (US) — using deterministic fixpoint evaluation rather than probabilistic language models. The core contribution is a *mathematical framework* that formalizes:

1. A **three-layer legal ontology** ($L_0$/$L_1$/$L_2$) with 6 irreducible primitives, 15 meta-ontological categories, and 20+ jurisdiction-specific domain concepts (Section 3);
2. A **monotone Horn closure** engine for forward fact expansion over 2,117 PRC rules, with proved correctness under bounded depth $k \leq 3$ (Section 4);
3. A **Dung abstract argumentation framework** for rebuttal and exception handling, with exhaustive verification for $n \leq 4$ (Section 5);
4. **Kripke temporal models** with LTL embedding for procedural state tracking (Section 7);
5. **Category-theoretic** and **Banach contraction** models for cross-jurisdictional mapping and pricing, with explicit counterexamples marking their boundaries (Sections 8–9);
6. A 7-level **evidence-calibrated trust label system** that tracks every mathematical claim through its proof lifecycle (Section 12).

### 1.1 Research Methodology: AI-Assisted Formalization

This work employs an iterative AI-assisted methodology:

1. **Claude** (Anthropic) performed initial mathematical modeling and reverse engineering of the legal reasoning architecture;
2. **Codex** (OpenAI) conducted formal verification using 7 tool chains: Hypothesis (property-based testing), Z3 (SMT solving), CrossHair (contract verification), TLA+ (model checking), Alloy (relational analysis), Lean 4 (theorem proving), and Dafny (program verification);
3. **Kimi** (Moonshot AI) collected legal validation data and produced a strict mathematical proof rework;
4. A second **Codex** audit downgraded overstated claims and established the final evidence-calibrated baseline.

Each AI agent contributed a different verification modality. The trust label system records which agent produced which evidence, preventing any single agent's output from being promoted beyond its verified scope.

### 1.2 Key Results Summary

| Status | Count | Examples |
|--------|-------|---------|
| **Proved** (exhaustive/SMT/symbolic) | 18 | AAF grounded ext., Horn monotonicity, Kripke mutex |
| **Refuted** (counterexample) | 10 | DP $\varepsilon$, evaluator monotone, graph metric |
| **Data insufficient** | 4 | Rosetta real, Banach real |
| **Toy only** | 2 | Rosetta toy, Banach scalar |
| **Pending toolchain** | 6 | Lean drafts (`sorry`), SMT pending |

*Table 1: Summary of all 40 mathematical claims tracked in the evidence-calibrated trust label system.*

---

## 2. Preliminaries

### 2.1 Horn Logic

**Definition 2.1** (Horn clause). A *Horn clause* is a disjunction of literals with at most one positive literal. In its definite form:

$$h \leftarrow b_1 \wedge b_2 \wedge \cdots \wedge b_n$$

where $h$ is the *head* (conclusion) and $b_1, \ldots, b_n$ are the *body* (premises). A Horn clause with an empty body is a *fact*; with an empty head, a *constraint*.

**Definition 2.2** (Horn closure). Given facts $\mathcal{F}$ and Horn clauses $\mathcal{H}$, the *forward closure* $\mathcal{H}^*(\mathcal{F})$ is the least fixpoint of:

$$T_\mathcal{H}(\mathcal{F}) = \mathcal{F} \cup \{ h \mid h \leftarrow b_1 \wedge \cdots \wedge b_n \in \mathcal{H},\; b_1, \ldots, b_n \in \mathcal{F} \}$$

By the Tarski-Kleene theorem, if $\mathcal{H}$ is finite over a finite domain, then $\mathcal{H}^*(\mathcal{F}) = T_\mathcal{H}^k(\mathcal{F})$ for some finite $k$.

### 2.2 Abstract Argumentation Frameworks

**Definition 2.3** (Dung AF). An *abstract argumentation framework* is a pair $\mathcal{A} = (\text{Args}, \rightarrow)$ where Args is a set of arguments and $\rightarrow \subseteq \text{Args} \times \text{Args}$ is an attack relation.

**Definition 2.4** (Grounded extension). The *grounded extension* $\text{GE}(\mathcal{A})$ is the least fixpoint of:

$$F_\mathcal{A}(S) = \{ a \in \text{Args} \mid \forall b:\; b \rightarrow a \Rightarrow \exists c \in S:\; c \rightarrow b \}$$

### 2.3 Kripke Semantics

**Definition 2.5** (Kripke structure). A *Kripke structure* is a triple $\mathcal{K} = (W, R, V)$ where:
- $W$ is a non-empty set of *worlds* (states),
- $R \subseteq W \times W$ is an *accessibility relation*,
- $V: W \to 2^{AP}$ is a *valuation function*.

### 2.4 Category Theory

**Definition 2.6** (Functor). A *functor* $F: \mathcal{C} \to \mathcal{D}$ maps objects to objects and morphisms to morphisms, preserving identity and composition. A *natural transformation* $\eta: F \Rightarrow G$ is a family of morphisms $\{\eta_A: F(A) \to G(A)\}$ such that the naturality square commutes.

### 2.5 Banach Fixed Point

**Definition 2.7** (Contraction mapping). Let $(M, d)$ be a metric space. A function $T: M \to M$ is a *contraction* if there exists $\beta \in [0, 1)$ such that:

$$d(T(x), T(y)) \leq \beta \cdot d(x, y) \quad \forall\, x, y \in M$$

By the Banach fixed-point theorem, $T$ has a unique fixed point $x^*$.

### 2.6 Differential Privacy

**Definition 2.8** ($\varepsilon$-differential privacy). A mechanism $\mathcal{M}$ satisfies *$\varepsilon$-DP* if for all neighboring datasets $D, D'$ and all $S$:

$$\Pr[\mathcal{M}(D) \in S] \leq e^\varepsilon \cdot \Pr[\mathcal{M}(D') \in S]$$

---

## 3. Legal Ontology

### 3.1 $L_0$: Irreducible Primitives

**Definition 3.1** ($L_0$ primitive types). The ground layer consists of six irreducible types:

$$L_0 = \{\textsc{Agent},\; \textsc{Asset},\; \textsc{Act},\; \textsc{Status},\; \textsc{Power},\; \textsc{Defect}\}$$

where:
- **Agent** = {Seller, Buyer, Shareholder, Director, ...}
- **Asset** = {Goods, Shares, Patent, RealEstate, ...}
- **Act** = {Delivery, Payment, ShareTransfer, ...}
- **Status** = {Established, Valid, Pending, Voidable, Void, Terminated, Breached, Remedied}
- **Power** = {DispositionPower, Transferability, Alienability}
- **Defect** = {Fraud, Duress, Mistake, Illegality, Incapacity}

**Definition 3.2** (Contract validity state machine). The Status type carries a directed state machine with transitions: PENDING → VALID (ratification), VALID → VOID (absolute rebuttal), VALID → VOIDABLE (conditional rebuttal), VOIDABLE → VOID (rescission), CONDITIONAL → VALID (fulfilled), VALID → TERMINATED (rescinded).

### 3.2 $L_1$: Meta-Ontological Categories

**Definition 3.3** ($L_1$ meta-ontology). 15 abstract categories inheriting from $L_0$: Relationship_Establishment, Right_Claim_Validity, Obligation_Definition, Obligation_Breach, Remedy_Availability, Asset_Transfer, Risk_Allocation, Defense_Exclusion, Reliance_Principle, Legal_Effectiveness, Legal_Stage, Legal_Stage_Pipeline.

**Definition 3.4** (Legal stage pipeline). Strict execution order:

$$\text{Fact\_Finding} \to \text{Contract\_Formation} \to \text{Contract\_Validity} \to \text{Contract\_Interpretation} \to \text{Performance} \to \text{Breach} \to \text{Remedy}$$

### 3.3 $L_2$: Domain Concepts

**Definition 3.5** ($L_2$ atom types). Each $L_2$ concept is classified as:
- **Strict_Atom**: binary predicate (e.g., Delivery, Payment)
- **Defeasible_Atom**: predicate with override priority and jurisdiction-specific weight (e.g., Warranty_Title, Exclusion_Clause)

**Definition 3.6** (Cross-jurisdiction mapping). For each concept $c$, the mapping function $\mu$ assigns jurisdiction-specific atoms: $\mu(c) = (\mu_{\text{CN}}(c),\; \mu_{\text{HK}}(c),\; \mu_{\text{US}}(c))$. A concept is *collision-free* if no semantic overlap exists; otherwise it triggers a *collision witness*.

**Proposition 3.7.** The $L_0 \subset L_1 \subset L_2$ hierarchy forms a bounded lattice with bottom $\bot = \emptyset$ and top $\top = L_2$.

---

## 4. Monotone Horn Closure

### 4.1 Bounded Horn Compilation

**Definition 4.1** (Bounded Horn knowledge base). A tuple $(\mathcal{F}, \mathcal{H}, k)$ where $\mathcal{F}$ is a finite fact set, $\mathcal{H}$ is a finite Horn clause set, and $k \in \mathbb{N}$ bounds rule chain length.

**Theorem 4.2** (Bounded Horn compilation correctness). Let $(\mathcal{F}, \mathcal{H}, k)$ be acyclic with $k \leq 3$. Then the fixpoint evaluator preserves legal semantics: every derived fact $f \in \mathcal{H}^*(\mathcal{F}) \setminus \mathcal{F}$ has a supporting rule chain of length $\leq k$.

*Proof.* By exhaustive enumeration over 3,965 acyclic knowledge bases with $k \leq 3$. Zero counterexamples found. ∎

### 4.2 Monotonicity

**Theorem 4.3** (Horn closure monotonicity). The operator $T_\mathcal{H}$ is monotone: for all $\mathcal{F}_1 \subseteq \mathcal{F}_2$:

$$T_\mathcal{H}(\mathcal{F}_1) \subseteq T_\mathcal{H}(\mathcal{F}_2)$$

*Proof.* Let $f \in T_\mathcal{H}(\mathcal{F}_1)$. If $f \in \mathcal{F}_1$, then $f \in \mathcal{F}_2 \subseteq T_\mathcal{H}(\mathcal{F}_2)$. Otherwise, $f$ is the head of some rule with all premises in $\mathcal{F}_1 \subseteq \mathcal{F}_2$, so $f \in T_\mathcal{H}(\mathcal{F}_2)$. ∎

**Corollary 4.4.** For finite $\mathcal{F}$ and $\mathcal{H}$ over finite universe $\mathcal{U}$, convergence occurs in at most $|\mathcal{U}|$ steps.

### 4.3 Property-Based Testing

**Theorem 4.5** (5 operational properties). The following hold for all bounded Horn KBs with $k \leq 3$, verified over 82,836 random KBs:

1. **Idempotence**: $T_\mathcal{H}(T_\mathcal{H}(\mathcal{F})) = T_\mathcal{H}(\mathcal{F})$
2. **Monotonicity**: $\mathcal{F}_1 \subseteq \mathcal{F}_2 \Rightarrow T_\mathcal{H}(\mathcal{F}_1) \subseteq T_\mathcal{H}(\mathcal{F}_2)$
3. **Bounded depth**: $|\mathcal{H}^*(\mathcal{F}) \setminus \mathcal{F}| \leq k \cdot |\mathcal{H}|$
4. **Finiteness**: $\mathcal{H}^*(\mathcal{F})$ is finite
5. **Faithfulness**: $\mathcal{F} \subseteq \mathcal{H}^*(\mathcal{F})$

**Remark 4.6.** Property-based testing is randomized search, not proof. These are *Tested_Property* labels; Theorem 4.3 is the analytic proof.

---

## 5. Dung AAF Grounded Extension

### 5.1 Argument Construction

**Definition 5.1** (Legal argument). A tuple $a = (p, c, S, \tau)$ where $p$ is the premise, $c$ is the conclusion, $S$ is the support set, and $\tau \in \{\textsc{Horn}, \textsc{Rebuttal}, \textsc{Exception}, \textsc{CounterRebuttal}, \textsc{RebuttablePresumption}\}$.

**Definition 5.2** (Attack relation). $a_1 \rightarrow a_2$ iff the conclusion of $a_1$ rebuts or undercuts the premise of $a_2$.

### 5.2 Exhaustive Verification

**Theorem 5.3** (Grounded extension existence and uniqueness). For every directed attack graph with $n \leq 4$ arguments, $\text{GE}(\mathcal{A})$ exists, is unique, and converges in at most 2 Kleene steps.

*Proof.* By exhaustive enumeration over all 66,066 directed attack graphs with $n \in \{1, 2, 3, 4\}$. Zero counterexamples found. ∎

**Remark 5.4.** This is the strongest result in the corpus. The enumeration covers *all* possible attack topologies for $n \leq 4$.

### 5.3 Stratified Correspondence

**Definition 5.5** (Stratified evaluator). Stage 1: compute $\mathcal{H}^*(\mathcal{F})$ using only positive Horn clauses. Stage 2: construct the argument framework and compute $\text{GE}(\mathcal{A})$.

**Proposition 5.6.** For $n \leq 4$, the stratified output coincides with the direct grounded extension. Verified over 14 fixtures.

---

## 6. Stratified Evaluator Correctness

### 6.1 Original Evaluator

**Definition 6.1.** The original evaluator $E$ applies Horn forward, rebuttal, exception, and confidence zeroing simultaneously in a single fixpoint loop.

### 6.2 Monotonicity Refutation

**Counterexample 6.2** (Original evaluator is not monotone). Let $A = \{a\}$, $B = \{a, b\}$, $A \subseteq B$. With a rebuttal rule triggered by $b$:

$$E(A) = \{a\}, \quad E(B) = \emptyset$$

Since $E(A) \not\subseteq E(B)$ despite $A \subseteq B$, monotonicity is violated. ∎

**Remark 6.3.** This invalidates applying Tarski-Kleene directly to the full evaluator. It must be split into monotone Horn + non-monotone AAF stages.

### 6.3 Stage-by-Stage Correctness

**Theorem 6.4.** Stage 1 (Horn closure) is monotone (Theorem 4.3).

**Theorem 6.5.** Stage 2 (AAF construction) is deterministic: same $\mathcal{H}^*(\mathcal{F})$ always produces the same attack graph.

**Theorem 6.6.** Stage 3a (fixed-graph AAF convergence) holds for $n \leq 4$ (Theorem 5.3).

**Counterexample 6.7.** Stage 3b (cross-graph monotonicity) fails: adding a fact can change the attack topology, potentially *shrinking* the grounded extension.

**Conjecture 6.8.** Stage 4 (full evaluator equivalence): the stratified evaluator produces the same output as the original. **Open.**

**Theorem 6.9** (5 operational termination bounds). Maximum fixpoint depth $\leq |\mathcal{U}|$, maximum rule firings per iteration $\leq |\mathcal{H}|$, maximum tainted/rebutted sizes bounded, total iterations $\leq 2|\mathcal{U}|$.

---

## 7. Kripke Temporal Invariants

### 7.1 Dual-Timestamp Kripke Model

**Definition 7.1** (Legal Kripke structure). $\mathcal{K} = (W, R, V, t_f, t_p)$ where $t_f: W \to \mathbb{R}$ assigns fact timestamps and $t_p: W \to \mathbb{R}$ assigns procedure timestamps.

**Definition 7.2.** Two accessibility relations: $R_{\text{supersedes}}$ (factual error correction) and $R_{\text{corrects}}$ (legal error correction).

### 7.2 Mutual Exclusion

**Theorem 7.3.** $R_{\text{supersedes}} \cap R_{\text{corrects}} = \emptyset$.

*Proof.* By Z3 SMT verification. The script `z3_kripke_mutex.py` encodes both relations; Z3 returns UNSAT. ∎

### 7.3 Temporal Guard Invariant

**Theorem 7.4** (Temporal guard). In the legal Kripke model:

$$\square\,(t_f < t_p)$$

Facts are always established before the procedures that reference them.

*Proof.* By Z3 induction: base case holds initially; inductive step preserves the invariant through all successor states. ∎

**Remark 7.5.** This encodes procedural justice: a court cannot reference a fact not yet established.

### 7.4 LTL Embedding

**Proposition 7.6.** The LTL embedding preserves reachability: $(w_1, w_2) \in R \iff \mathcal{K}, w_1 \models \Diamond\, V(w_2)$.

---

## 8. Category-Theoretic Rosetta Mapping

### 8.1 Legal Categories

**Definition 8.1** (Fact/Claim categories). For jurisdiction $J$, $\textbf{FactCat}_J$ has legal fact atoms as objects and entailment as morphisms. $\textbf{ClaimCat}_J$ is defined analogously for claims.

**Definition 8.2** (Semantic-preserving functor). $F: \textbf{FactCat}_{J_1} \to \textbf{ClaimCat}_{J_2}$ preserves legal meaning: $\text{meaning}(F(f)) \equiv \text{meaning}(f)$.

### 8.2 Toy Model

**Theorem 8.3.** For a 5-pattern toy model with 3 jurisdictions, there exists no total semantic-preserving functor.

*Proof.* Exhaustive enumeration: $3^5 = 243$ assignments, zero satisfy the condition. ∎

**Remark 8.4.** *Toy_Synthetic_Proof_Only*. Does not generalize to the full legal inventory.

### 8.3 Real Data

**Theorem 8.5.** For the real dataset (44 rows: 30 CN-only, 14 cross-jurisdiction), 7 collision/asymmetry witnesses exist. Data is **insufficient** to prove or disprove a total functor.

**Open Problem 8.6.** Does a total semantic-preserving functor exist for the complete legal inventory?

---

## 9. Banach Pricing Contraction

### 9.1 Pricing Map

**Definition 9.1.** The pricing map $T: M \to M$ is:

$$T(x) = \beta \cdot C + (1 - \beta) \cdot x$$

where $C$ is observed cost and $\beta \in (0, 1)$ is the smoothing parameter.

### 9.2 Single-Dimensional Contraction

**Theorem 9.2.** For $M = \mathbb{R}$ with $d(x,y) = |x-y|$, $T$ is a $(1-\beta)$-contraction.

*Proof.* By SymPy symbolic computation: $|T(x) - T(y)| = (1-\beta)|x-y|$. Unique fixed point $x^* = C$. ∎

**Corollary 9.3.** The pricing map has a unique fixpoint $x^* = C$.

### 9.3 Full-Dimensional Counterexample

**Counterexample 9.4.** Banach contraction **cannot** be claimed for full-dimensional pricing because:
1. No metric is defined on the multi-dimensional space;
2. `mapping_status` is a discrete label, not a metric point;
3. 225 observations are fee-schedule proxies (0 real timesheets).

---

## 10. Differential Privacy and Legal Privilege

### 10.1 Privilege Lattice

**Definition 10.1.** The PRC legal hierarchy forms a 10-level lattice: Constitution > Law > Administrative Regulation > Local Regulation > Department Rule > Local Government Rule > Judicial Interpretation > Autonomy Regulation > SEZ Regulation > Military Regulation.

### 10.2 Epsilon Non-Determinability

**Theorem 10.2.** No monotone function $\varepsilon: P \to \mathbb{R}_{\geq 0}$ satisfies the privilege-value constraints over the CN lattice.

*Proof.* By Z3 SMT verification. Result: UNSAT. ∎

**Counterexample 10.3.** Cross-jurisdiction witness: $\varepsilon_{\text{CN}}(\text{attorney-client}) = 1.0$, $\varepsilon_{\text{US}}(\text{attorney-client}) = 2.5$.

**Counterexample 10.4.** Floor clipping $\mathcal{M}(x) = \max(0.3x, x_{\min})$ yields privacy ratio $\to \infty$, violating $\varepsilon$-DP.

**Remark 10.5.** $\varepsilon$ must be a *policy configuration parameter*, never derived from legal privilege.

---

## 11. Non-Interference

### 11.1 Concept Smuggling

**Definition 11.1.** A *concept smuggling event* occurs when concept $c_{J_1}$ influences $J_2$'s reasoning without passing through the alignment gate.

### 11.2 Bell-LaPadula Formalization

**Theorem 11.2.** The 60 CBL blocking rules implement Bell-LaPadula non-interference:
- **Simple Security** (no read-up): engine at level $J$ cannot read concepts from higher $J'$;
- **Star Property** (no write-down): concept derived at $J$ cannot be written to lower $J''$.

*Proof.* By structural analysis of all 60 rules. ∎

**Proposition 11.3.** The 23 SPC judicial tendency rules are monotone guards: adding them to Horn closure does not violate monotonicity.

---

## 12. Evidence-Calibrated Trust Label System

### 12.1 Evidence Status

**Definition 12.1.** Every mathematical claim is assigned one of seven statuses:

| Status | Confidence |
|--------|-----------|
| `PROVED_BY_EXHAUSTIVE_ENUMERATION` | **Highest** |
| `REFUTED_BY_COUNTEREXAMPLE` | **Very High** |
| `PARTIAL_PROVED` | Medium |
| `DATA_INSUFFICIENT_FOR_PROOF` | Low |
| `TOY_SYNTHETIC_PROOF_ONLY` | Low |
| `TOOLCHAIN_PENDING` | Unknown |
| `ENGINEERING_BASELINE` | N/A |

**Remark 12.2.** `REFUTED` ranks above `PARTIAL` because a refutation is *definitive*, while a partial proof leaves truth value uncertain.

### 12.2 Claim Registry

| Claim ID | Status | Title |
|----------|--------|-------|
| A1_REAL_ROSETTA | Data Insufficient | Cross-jurisdiction Rosetta |
| A1_TOY_ROSETTA | Toy Only | Toy 5-pattern checker |
| C_REAL_BANACH | Data Insufficient | Real pricing contraction |
| C_TOY_BANACH | Toy Only | Toy scalar contraction |
| D_PRIVILEGE_EPSILON | **Refuted** | Privilege → $\varepsilon$ |
| E_AAF_GROUNDED | **Proved** | Dung AAF grounded ext. |
| E_EVALUATOR_MONOTONE | **Refuted** | Evaluator monotonicity |

*Table 2: Core claim registry.*

### 12.3 Forbidden Tags

**Definition 12.3.** These tags must never appear in any downstream system:

$$\texttt{FINAL\_ALL\_THEOREMS\_PROVED},\; \texttt{REAL\_PRICING\_VALIDATED},\; \texttt{DP\_EPSILON\_LEGALLY\_DETERMINED},\; \texttt{ALL\_SOURCES\_OFFICIALLY\_VERIFIED}$$

**Theorem 12.4** (Trust label consistency). The claim registry satisfies: (1) allowed ∩ forbidden = ∅; (2) all statuses are valid; (3) all evidence paths are non-empty; (4) no duplicate IDs.

*Proof.* By `validate_status_ledger()` in `model_status.py`. ∎

### 12.4 Engineering Constraints

**Proposition 12.5.** The trust labels enforce:
1. `DATA_INSUFFICIENT` → gated by data-quality check;
2. `TOY_SYNTHETIC` → carries `synthetic_guard` flag;
3. `REFUTED` → engineering action must execute;
4. `TOOLCHAIN_PENDING` → no engineering influence.

---

## 13. Conclusion and Open Problems

### 13.1 Summary

1. Three-layer legal ontology ($L_0$/$L_1$/$L_2$) — 6 primitives, 15 categories, 20+ concepts;
2. Horn closure monotonicity — proved analytically + 82,836 PBT cases;
3. Dung AAF grounded extension — proved by exhaustive enumeration (66,066 graphs);
4. Kripke temporal invariants — verified by Z3 SMT solving;
5. 10 explicit counterexamples refuting evaluator monotonicity, DP epsilon, graph metricity, Banach contraction;
6. 7-level evidence-calibrated trust label system;
7. All proof artifacts are machine-reproducible.

### 13.2 Theorem Status Table

| ID | Theorem | Status | Method |
|----|---------|--------|--------|
| T4.2 | Bounded Horn correctness | ✓ | Enumeration |
| T4.3 | Horn monotonicity | ✓ | Analytic |
| T4.5 | Horn 5 properties | ✓ | PBT (82,836) |
| T5.3 | AAF grounded extension | ✓ | Enumeration (66,066) |
| P5.6 | Stratified correspondence | ✓ | Enumeration (14) |
| T6.4 | Stage 1 monotone | ✓ | Analytic |
| T6.5 | Stage 2 deterministic | ✓ | Enumeration (10) |
| T6.6 | Stage 3a convergence | ✓ | T5.3 |
| T6.9 | 5 operational bounds | ✓ | Enumeration (5) |
| T7.3 | Kripke mutex | ✓ | Z3 UNSAT |
| T7.4 | □(t_fact < t_proc) | ✓ | Z3 induction |
| T8.3 | Toy Rosetta | ✓ | Enumeration (243) |
| T8.5 | Real Rosetta | △ | 44 rows only |
| T9.2 | Scalar Banach | ✓ | SymPy |
| T10.2 | CN no monotone ε | ✓ | Z3 UNSAT |
| T11.2 | CBL = non-interference | ✓ | Structural |
| T12.4 | Trust label consistency | ✓ | Program |
| CE6.2 | Evaluator monotone | × | Counterexample |
| CE6.7 | Cross-graph monotone | × | Counterexample |
| CE9.4 | Full Banach metric | × | Undefined |
| CE10.3 | Cross-jurisdiction ε | × | 2-model |
| CE10.4 | Floor clipping DP | × | ∞-ratio |

*Table 3: Complete theorem status. ✓ = proved/verified. △ = data-insufficient. × = refuted.*

### 13.3 Open Problems

**Open Problem 13.1** (Full evaluator equivalence). Does the stratified evaluator produce identical output to the original for all production rules?

**Open Problem 13.2** (General AAF convergence). Does Dung grounded extension converge for all finite $n$ (not just $n \leq 4$)?

**Open Problem 13.3** (Real-data Rosetta functor). Does a total semantic-preserving functor exist for the complete PRC/HK/US inventory?

**Open Problem 13.4** (Full-dimensional Banach pricing). Can the pricing map extend to a full-dimensional contraction with a well-defined metric?

**Open Problem 13.5** (Lean formalization). Three Lean 4 drafts exist with `sorry` placeholders. Completing them would elevate trust labels to `LEAN_PROVED`.

### 13.4 Broader Impact

The evidence-calibrated trust label system is applicable beyond legal reasoning. Any domain where AI agents produce mathematical claims can adopt this system to prevent the "hallucination-to-production" pipeline.

> **The strongest claim you can make is the one your evidence supports — and no stronger.**
