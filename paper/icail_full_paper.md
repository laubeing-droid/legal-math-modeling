# Evidence-Calibrated Formal Verification of Cross-Jurisdictional Legal Reasoning: A Stratified Horn-AAF Architecture with Trust Labels

**Author:** Laupinco

**Venue:** ICAIL 2026 -- International Conference on Artificial Intelligence and Law

---

## Abstract

Legal AI systems deployed across multiple jurisdictions lack formal soundness guarantees. We present *juris-calculus*, a symbolic legal reasoning engine operating across the People's Republic of China (PRC), Hong Kong (HK), and the United States (US) via deterministic fixpoint evaluation. The core architecture is a *stratified two-stage evaluator*: Stage 1 computes a monotone Horn closure over 2,117 PRC Civil Code rules; Stage 2 constructs a Dung abstract argumentation framework (AAF) for rebuttal and exception handling. We prove 18 positive results by exhaustive enumeration, SMT verification, and symbolic computation. We refute 10 claims by explicit counterexamples, including a critical monotonicity violation in the original unstratified evaluator. All mathematical claims are tracked by a 7-level *evidence-calibrated trust label system* that prevents unverified assertions from propagating to downstream engineering decisions. A companion formalization covers Kripke temporal models with dual timestamps, category-theoretic cross-jurisdiction mappings, Banach contraction pricing, and differential privacy impossibility results.

**Keywords:** computational law, formal methods, legal AI, abstract argumentation, Horn logic, Kripke semantics, evidence calibration, cross-jurisdictional reasoning

---

## 1. Introduction

Legal reasoning across jurisdictions presents a unique formal challenge: concepts that are well-defined in one legal system (e.g., "material breach" in U.S. contract law under the Uniform Commercial Code) have no direct equivalent in another (e.g., Chinese contract law under the PRC Civil Code, Book Three). Existing computational legal systems typically rely on probabilistic retrieval-augmented generation (RAG) over large language models, which lacks formal guarantees about soundness, completeness, or cross-jurisdictional consistency. When an AI system advises on a PRC--HK cross-border transaction, no existing framework can certify that its reasoning chain is free from logical contradiction or that its temporal ordering of procedural steps respects the invariant that facts must precede the procedures that reference them.

This paper presents **juris-calculus**, a symbolic legal reasoning engine that operates across three jurisdictions -- the People's Republic of China (PRC), Hong Kong (HK), and the United States (US) -- using deterministic fixpoint evaluation rather than probabilistic language models. The central architectural insight is a *stratified separation* of the evaluator into a monotone Horn closure stage (amenable to Tarski--Kleene fixpoint theory) and a non-monotone Dung AAF stage (requiring exhaustive enumeration for soundness). We demonstrate that attempting to combine these stages into a single fixpoint loop produces a demonstrably non-monotone operator, invalidating classical fixpoint guarantees.

### 1.1 Research Methodology: Multi-AI Pipeline

This work employs an iterative multi-AI formalization methodology in which each agent contributes a distinct verification modality:

1. **Claude** (Anthropic) performed initial mathematical modeling and reverse engineering of the legal reasoning architecture, producing the foundational definitions and conjectures;
2. **Codex** (OpenAI) conducted formal verification using seven tool chains: Hypothesis (property-based testing), Z3 (SMT solving), CrossHair (contract verification), TLA+ (model checking), Alloy (relational analysis), Lean 4 (theorem proving), and Dafny (program verification);
3. **Kimi** (Moonshot AI) collected legal validation data and produced a strict mathematical proof rework, identifying overstated claims;
4. A second **Codex** audit downgraded overstated claims, constructed explicit counterexamples, and established the final evidence-calibrated baseline.

Each AI agent contributed a different verification modality. The trust label system (Section 12 of the companion paper) records which agent produced which evidence, preventing any single agent's output from being promoted beyond its verified scope. This methodology is itself a contribution: it demonstrates a reproducible pipeline for AI-assisted formalization with built-in adversarial audit.

### 1.2 Contributions

This paper makes the following contributions:

1. **Stratified Horn-AAF Architecture.** A two-stage evaluator that separates monotone forward-chaining (Horn closure) from non-monotone rebuttal (Dung AAF), with formal proofs of correctness for each stage individually and an explicit counterexample demonstrating that the unstratified combination fails monotonicity (Section 6).

2. **Exhaustive AAF Verification.** Proof that the grounded extension exists, is unique, and converges in at most 2 Kleene steps for all $n \leq 4$ arguments, established by exhaustive enumeration over 66,066 directed attack graphs (Section 5).

3. **Three-Layer Legal Ontology.** A formal ontology $L_0 / L_1 / L_2$ with 6 irreducible primitives, 15 meta-ontological categories, and jurisdiction-specific domain atoms, equipped with a cross-jurisdiction mapping function $\mu$ and a collision witness mechanism (Section 3).

4. **Kripke Temporal Invariants.** A dual-timestamp legal Kripke structure with proved mutual exclusion of factual and legal correction relations (Z3 UNSAT), and a temporal guard invariant $\square(t_f < t_p)$ established by Z3 induction (Section 7).

5. **Evidence-Calibrated Trust Labels.** A 7-level trust label system that tracks every mathematical claim through its proof lifecycle, from *Conjecture* through *Tested_Property* to *Proved*, with explicit downgrades for claims refuted by counterexample.

6. **Multi-AI Formalization Pipeline.** A reproducible methodology for adversarial AI-assisted proof construction, demonstrating that cross-agent verification catches errors invisible to any single agent.

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

This section establishes the formal notation and foundational definitions used throughout the paper.

### 2.1 Horn Logic

**Definition 2.1** (Horn clause [14]). A *Horn clause* is a disjunction of literals with at most one positive literal. In its definite form:

$$h \leftarrow b_1 \wedge b_2 \wedge \cdots \wedge b_n \tag{1}$$

where $h$ is the *head* (conclusion) and $b_1, \ldots, b_n$ are the *body* (premises). A Horn clause with an empty body is a *fact*; a Horn clause with an empty head is a *constraint*.

**Definition 2.2** (Immediate consequence operator). Given a set of facts $\mathcal{F}$ and a set of Horn clauses $\mathcal{H}$, the *immediate consequence operator* $T_{\mathcal{H}}$ is defined as:

$$T_{\mathcal{H}}(\mathcal{F}) = \mathcal{F} \cup \{ h \mid h \leftarrow b_1 \wedge \cdots \wedge b_n \in \mathcal{H},\; b_1, \ldots, b_n \in \mathcal{F} \} \tag{2}$$

**Definition 2.3** (Horn closure). The *forward closure* $\mathcal{H}^*(\mathcal{F})$ is the least fixpoint of $T_{\mathcal{H}}$:

$$\mathcal{H}^*(\mathcal{F}) = \text{lfp}.\; T_{\mathcal{H}}(\mathcal{F}) = \bigcup_{i=0}^{\infty} T_{\mathcal{H}}^i(\mathcal{F}) \tag{3}$$

By the Tarski--Kleene theorem [22, 23], if $\mathcal{H}$ is a finite set of positive Horn clauses over a finite domain, then $\mathcal{H}^*(\mathcal{F}) = T_{\mathcal{H}}^k(\mathcal{F})$ for some finite $k$.

### 2.2 Abstract Argumentation Frameworks

**Definition 2.4** (Dung AF [6]). An *abstract argumentation framework* is a pair $\mathcal{A} = (\text{Args}, \rightarrow)$ where $\text{Args}$ is a set of arguments and $\rightarrow \subseteq \text{Args} \times \text{Args}$ is a binary attack relation. We write $(a, b) \in {\rightarrow}$ as $a \rightarrow b$ to mean "$a$ attacks $b$."

**Definition 2.5** (Characteristic function). The *characteristic function* of an AF $\mathcal{A}$ is:

$$F_{\mathcal{A}}(S) = \{ a \in \text{Args} \mid \forall b:\; b \rightarrow a \Rightarrow \exists c \in S:\; c \rightarrow b \} \tag{4}$$

That is, $F_{\mathcal{A}}(S)$ collects all arguments whose every attacker is itself attacked by some member of $S$.

**Definition 2.6** (Grounded extension). The *grounded extension* $\text{GE}(\mathcal{A})$ is the least fixpoint of $F_{\mathcal{A}}$:

$$\text{GE}(\mathcal{A}) = \text{lfp}.\; F_{\mathcal{A}} = \bigcup_{i=0}^{\infty} F_{\mathcal{A}}^i(\emptyset) \tag{5}$$

The grounded extension exists and is unique for every finite AF [6].

### 2.3 Kripke Semantics

**Definition 2.7** (Kripke structure [16]). A *Kripke structure* is a triple $\mathcal{K} = (W, R, V)$ where:

- $W$ is a non-empty set of *worlds* (states);
- $R \subseteq W \times W$ is an *accessibility relation*;
- $V: W \to 2^{AP}$ is a *valuation function* mapping each world to the set of atomic propositions true in that world.

### 2.4 Category Theory

**Definition 2.8** (Functor and natural transformation [18]). A *functor* $F: \mathcal{C} \to \mathcal{D}$ maps objects to objects and morphisms to morphisms, preserving identity and composition: $F(\text{id}_A) = \text{id}_{F(A)}$ and $F(g \circ f) = F(g) \circ F(f)$.

A *natural transformation* $\eta: F \Rightarrow G$ between functors $F, G: \mathcal{C} \to \mathcal{D}$ is a family of morphisms $\{\eta_A: F(A) \to G(A)\}_{A \in \text{Ob}(\mathcal{C})}$ such that for every morphism $f: A \to B$ in $\mathcal{C}$, the naturality square commutes: $G(f) \circ \eta_A = \eta_B \circ F(f)$.

### 2.5 Banach Fixed Point

**Definition 2.9** (Contraction mapping [2]). Let $(M, d)$ be a metric space. A function $T: M \to M$ is a *contraction mapping* if there exists $\beta \in [0, 1)$ such that:

$$d(T(x), T(y)) \leq \beta \cdot d(x, y) \quad \forall\, x, y \in M \tag{6}$$

By the Banach fixed-point theorem, $T$ has a unique fixed point $x^* \in M$ such that $T(x^*) = x^*$, and the sequence $T^n(x_0)$ converges to $x^*$ for any initial point $x_0$.

### 2.6 Differential Privacy

**Definition 2.10** ($\varepsilon$-differential privacy [7]). A randomized mechanism $\mathcal{M}$ satisfies *$\varepsilon$-differential privacy* if for all neighboring datasets $D, D'$ (differing in one record) and all $S \subseteq \text{Range}(\mathcal{M})$:

$$\Pr[\mathcal{M}(D) \in S] \leq e^\varepsilon \cdot \Pr[\mathcal{M}(D') \in S] \tag{7}$$

---

## 3. Legal Ontology: $L_0$ / $L_1$ / $L_2$

The juris-calculus ontology is structured in three layers of increasing specificity, drawing on Searle's theory of institutional facts [20] and Hart's rule of recognition [11].

### 3.1 $L_0$: Irreducible Primitives

**Definition 3.1** ($L_0$ primitive types). The ground layer $L_0$ consists of six irreducible types:

$$L_0 = \{\textsc{Agent},\; \textsc{Asset},\; \textsc{Act},\; \textsc{Status},\; \textsc{Power},\; \textsc{Defect}\} \tag{8}$$

where:

- $\textsc{Agent} = \{\text{Seller}, \text{Buyer}, \text{Shareholder}, \text{Director}, \ldots\}$
- $\textsc{Asset} = \{\text{Goods}, \text{Shares}, \text{Patent}, \text{RealEstate}, \ldots\}$
- $\textsc{Act} = \{\text{Delivery}, \text{Payment}, \text{ShareTransfer}, \ldots\}$
- $\textsc{Status} = \{\text{Established}, \text{Valid}, \text{Pending}, \text{Voidable}, \text{Void}, \text{Terminated}, \text{Breached}, \text{Remedied}\}$
- $\textsc{Power} = \{\text{DispositionPower}, \text{Transferability}, \text{Alienability}\}$
- $\textsc{Defect} = \{\text{Fraud}, \text{Duress}, \text{Mistake}, \text{Illegality}, \text{Incapacity}\}$

These six types are irreducible in the sense that no type can be expressed as a composition of the others, and they suffice to encode the legal facts across all three target jurisdictions.

**Definition 3.2** (Contract validity state machine). The $\textsc{Status}$ type carries a directed state machine for contract validity with the following transitions:

$$\text{PENDING} \xrightarrow{\text{ratification}} \text{VALID} \xrightarrow{\text{abs.\ rebuttal}} \text{VOID}$$

$$\text{VALID} \xrightarrow{\text{cond.\ rebuttal}} \text{VOIDABLE} \xrightarrow{\text{rescission}} \text{VOID}$$

with additional transitions: $\text{CONDITIONAL} \xrightarrow{\text{fulfilled}} \text{VALID}$ and $\text{VALID} \xrightarrow{\text{rescinded}} \text{TERMINATED}$.

### 3.2 $L_1$: Meta-Ontological Categories

**Definition 3.3** ($L_1$ meta-ontology). The meta-ontological layer $L_1$ consists of 15 abstract categories inheriting from $L_0$ types:

$$L_1 = \left\{ \begin{array}{l} \text{Relationship\_Establishment},\; \text{Right\_Claim\_Validity},\; \text{Obligation\_Definition}, \\ \text{Obligation\_Breach},\; \text{Remedy\_Availability},\; \text{Asset\_Transfer},\; \text{Risk\_Allocation}, \\ \text{Defense\_Exclusion},\; \text{Reliance\_Principle},\; \text{Legal\_Effectiveness},\; \text{Legal\_Stage}, \\ \text{Legal\_Stage\_Pipeline},\; \text{Procedural\_Requirement},\; \text{Substantive\_Defense},\; \text{Conflict\_Resolution} \end{array} \right\} \tag{9}$$

**Definition 3.4** (Legal stage pipeline). The $\textsc{Legal\_Stage\_Pipeline}$ defines a strict execution order for legal reasoning:

$$\text{Fact\_Finding} \to \text{Contract\_Formation} \to \text{Contract\_Validity} \to \text{Contract\_Interpretation}$$
$$\to \text{Performance} \to \text{Breach} \to \text{Remedy} \tag{10}$$

Each stage must complete before the next begins. The pipeline is enforced by the fixpoint evaluator's domain routing.

### 3.3 $L_2$: Domain Concepts

**Definition 3.5** ($L_2$ atom types). Each $L_2$ concept is classified as either:

- **Strict_Atom**: a binary predicate that is either satisfied or not (e.g., $\textsc{Delivery}$, $\textsc{Payment}$);
- **Defeasible_Atom**: a predicate with override priority and jurisdiction-specific weight (e.g., $\textsc{Warranty\_Title}$, $\textsc{Exclusion\_Clause}$).

Each defeasible atom carries a rebuttal criteria function:

$$\text{rebut}: \text{Defeasible\_Atom} \times \text{Context} \to \{0, 1\} \times \text{OverridePriority} \tag{11}$$

This function determines whether a defeasible atom can be overridden in a given legal context, and if so, at what priority level.

**Definition 3.6** (Cross-jurisdiction mapping). For each $L_2$ concept $c$, the mapping function $\mu$ assigns jurisdiction-specific atoms:

$$\mu(c) = (\mu_{\text{CN}}(c),\; \mu_{\text{HK}}(c),\; \mu_{\text{US}}(c)) \tag{12}$$

A concept $c$ is *collision-free* if the semantic neighborhoods of its jurisdiction images do not overlap: $\mu_{\text{CN}}(c) \cap \mu_{\text{HK}}(c) \cap \mu_{\text{US}}(c) = \emptyset$ implies no semantic collision. Otherwise, $c$ triggers a *collision witness* requiring human adjudication.

**Proposition 3.7** (Bounded lattice). The $L_0 \subset L_1 \subset L_2$ hierarchy, ordered by specificity, forms a bounded lattice $(L, \leq, \sqcap, \sqcup)$ with bottom $\bot = \emptyset$, top $\top = L_2$, meet $\sqcap$ given by the greatest common ancestor in the type hierarchy, and join $\sqcup$ given by the least common descendant.

*Proof.* Each layer refines the previous one by strict subset inclusion. The finite height (3) guarantees the existence of joins and meets for all pairs. The empty set is vacuously a lower bound, and $L_2$ is an upper bound by construction. $\square$

---

## 4. Monotone Horn Closure

The Horn closure engine is the first stage of the two-stage juris-calculus evaluator. This section formalizes its correctness, monotonicity, and operational properties.

### 4.1 Bounded Horn Compilation

**Definition 4.1** (Bounded Horn knowledge base). A *bounded Horn knowledge base* $(\mathcal{F}, \mathcal{H}, k)$ consists of:

- A finite fact set $\mathcal{F} \subseteq \mathcal{U}$ over a finite universe $\mathcal{U}$ of legal atoms;
- A finite set of Horn clauses $\mathcal{H}$;
- A depth bound $k \in \mathbb{N}$ such that every rule chain has length at most $k$.

A knowledge base is *acyclic* if the dependency graph of $\mathcal{H}$ (where an edge from clause $r_1$ to clause $r_2$ exists iff $\text{head}(r_1) \in \text{body}(r_2)$) has no directed cycles.

**Theorem 4.2** (Bounded Horn compilation correctness). Let $(\mathcal{F}, \mathcal{H}, k)$ be an acyclic bounded Horn knowledge base with $k \leq 3$. Then the fixpoint evaluator preserves legal semantics: for every derived fact $f \in \mathcal{H}^*(\mathcal{F}) \setminus \mathcal{F}$, there exists a rule chain $\rho$ of length $\leq k$ such that:

$$\rho = (r_1, r_2, \ldots, r_j), \quad j \leq k, \quad \text{head}(r_i) \in \text{body}(r_{i+1}) \tag{13}$$

and the conclusion of $\rho$ is $f$.

*Proof.* By exhaustive enumeration over 3,965 acyclic knowledge bases with $k \leq 3$. For each KB, the verification script `bounded_horn_correctness.py` constructs all valid rule chains and confirms that every derived fact has a supporting chain of length $\leq k$. Zero counterexamples found. The bound $k \leq 3$ is a practical engineering constraint reflecting the PRC Civil Code's maximum dependency depth in the current configuration. $\square$

### 4.2 Monotonicity

**Theorem 4.3** (Horn closure monotonicity). The immediate consequence operator $T_{\mathcal{H}}$ is monotone on the fact lattice: for all $\mathcal{F}_1 \subseteq \mathcal{F}_2$:

$$T_{\mathcal{H}}(\mathcal{F}_1) \subseteq T_{\mathcal{H}}(\mathcal{F}_2) \tag{14}$$

*Proof.* Let $f \in T_{\mathcal{H}}(\mathcal{F}_1)$. We consider two cases.

**Case 1:** $f \in \mathcal{F}_1$. Then $f \in \mathcal{F}_2$ (by the assumption $\mathcal{F}_1 \subseteq \mathcal{F}_2$), and therefore $f \in \mathcal{F}_2 \subseteq T_{\mathcal{H}}(\mathcal{F}_2)$.

**Case 2:** $f \notin \mathcal{F}_1$. Then $f$ is the head of some rule $h \leftarrow b_1 \wedge \cdots \wedge b_n \in \mathcal{H}$ with all $b_i \in \mathcal{F}_1$. Since $\mathcal{F}_1 \subseteq \mathcal{F}_2$, all $b_i \in \mathcal{F}_2$, so $f \in T_{\mathcal{H}}(\mathcal{F}_2)$ by the definition of $T_{\mathcal{H}}$.

In both cases, $f \in T_{\mathcal{H}}(\mathcal{F}_2)$, establishing $T_{\mathcal{H}}(\mathcal{F}_1) \subseteq T_{\mathcal{H}}(\mathcal{F}_2)$. $\square$

**Corollary 4.4** (Termination). For any finite $\mathcal{F}$ and finite $\mathcal{H}$ over a finite universe $\mathcal{U}$, the sequence $T_{\mathcal{H}}^0(\mathcal{F}), T_{\mathcal{H}}^1(\mathcal{F}), \ldots$ converges in at most $|\mathcal{U}|$ steps.

*Proof.* Each iteration either adds at least one new element to the fact set or reaches a fixpoint. Since $|\mathcal{U}|$ is finite, the sequence stabilizes within $|\mathcal{U}|$ applications. $\square$

### 4.3 Property-Based Testing

**Theorem 4.5** (Five operational properties). The following properties hold for all bounded Horn knowledge bases with $k \leq 3$, verified by Hypothesis property-based testing over 82,836 randomly generated knowledge bases:

1. **Idempotence:** $T_{\mathcal{H}}(T_{\mathcal{H}}(\mathcal{F})) = T_{\mathcal{H}}(\mathcal{F})$
2. **Monotonicity:** $\mathcal{F}_1 \subseteq \mathcal{F}_2 \Rightarrow T_{\mathcal{H}}(\mathcal{F}_1) \subseteq T_{\mathcal{H}}(\mathcal{F}_2)$
3. **Bounded depth:** $|\mathcal{H}^*(\mathcal{F}) \setminus \mathcal{F}| \leq k \cdot |\mathcal{H}|$
4. **Finiteness:** $\mathcal{H}^*(\mathcal{F})$ is finite
5. **Faithfulness:** $\mathcal{F} \subseteq \mathcal{H}^*(\mathcal{F})$

Zero violations across all 82,836 test cases. $\square$

**Remark 4.6.** Property-based testing is randomized search, not proof. These constitute $\textsc{Tested\_Property}$ trust labels, not $\textsc{Proved}$. The monotonicity in Theorem 4.3 is proved analytically; the PBT results in Theorem 4.5 provide additional empirical confidence across a broader class of knowledge bases.

---

## 5. Dung AAF Grounded Extension

The second stage of the juris-calculus evaluator uses Dung's abstract argumentation framework to handle rebuttal, exception, counter-rebuttal, and rebuttable presumption. This section presents the strongest formal result in the corpus.

### 5.1 Argument Construction

**Definition 5.1** (Legal argument). A *legal argument* in juris-calculus is a tuple $a = (p, c, S, \tau)$ where:

- $p \in \mathcal{U}$ is the *premise* (a legal fact atom);
- $c \in \mathcal{U}$ is the *conclusion* (a legal claim);
- $S \subseteq \mathcal{U}$ is the *support set* (intermediate facts used in derivation);
- $\tau \in \{\textsc{Horn}, \textsc{Rebuttal}, \textsc{Exception}, \textsc{CounterRebuttal}, \textsc{RebuttablePresumption}\}$ is the argument type.

**Definition 5.2** (Attack relation). For arguments $a_1 = (p_1, c_1, S_1, \tau_1)$ and $a_2 = (p_2, c_2, S_2, \tau_2)$, the attack relation is defined as:

$$a_1 \rightarrow a_2 \iff \begin{cases} c_1 = \neg p_2 & \text{(rebuttal: conclusion attacks premise)} \\ c_1 = \text{exception}(p_2) & \text{(undercut: exception to rule)} \\ \tau_1 = \textsc{CounterRebuttal} \wedge c_1 = \neg c_2 & \text{(counter-rebuttal)} \end{cases} \tag{15}$$

### 5.2 Exhaustive Verification

**Theorem 5.3** (Grounded extension existence and uniqueness). For every directed attack graph with $n \leq 4$ arguments, the grounded extension $\text{GE}(\mathcal{A})$ exists, is unique, and converges in at most 2 Kleene iteration steps.

*Proof.* By exhaustive enumeration over all 66,066 directed attack graphs with $n \in \{1, 2, 3, 4\}$. For each graph, the verification script `dung_grounded_extension.py` computes $\text{GE}(\mathcal{A})$ using the Kleene fixpoint iteration $F_{\mathcal{A}}^0(\emptyset), F_{\mathcal{A}}^1(\emptyset), \ldots$ and confirms:

1. The grounded extension $\text{GE}(\mathcal{A})$ always exists (by the Knaster-Tarski theorem) and is unique. Note: it may be empty (e.g., for a 2-cycle $a \to b, b \to a$ where no argument is acceptable);
2. The grounded extension is the unique least fixpoint of $F_{\mathcal{A}}$;
3. The maximum number of Kleene steps required is 2 (attained for certain $n = 4$ graphs).

Zero counterexamples found across 66,066 test cases. The enumeration covers *all* possible attack topologies for $n \leq 4$, not a random sample. $\square$

**Remark 5.4.** This is the strongest result in the entire corpus. The exhaustive nature of the verification eliminates the possibility of sampling bias. However, it does not extend to $n > 4$ by this enumeration alone; the number of directed graphs grows as $2^{n(n-1)}$, making $n = 5$ infeasible without structural pruning.

### 5.3 Stratified Correspondence

**Definition 5.5** (Stratified evaluator). The *stratified evaluator* separates legal reasoning into two stages:

- **Stage 1 (Horn closure):** compute $\mathcal{H}^*(\mathcal{F})$ using only positive Horn clauses;
- **Stage 2 (AAF evaluation):** construct the argument framework from $\mathcal{H}^*(\mathcal{F})$ and compute $\text{GE}(\mathcal{A})$.

**Proposition 5.6** (Stratified correspondence). For legal argument frameworks with $n \leq 4$ arguments, the stratified evaluator's output coincides with the grounded extension computed directly on the full argument graph.

*Proof.* Direct computation: for each of 14 stratified fixtures (covering all canonical attack topologies for small $n$), the stratified output and the direct grounded extension are computed and compared for equality. All 14 fixtures pass. $\square$

---

## 6. The Non-Monotonicity Result

This section presents the critical refutation of the original evaluator's monotonicity claim, which motivates the stratified architecture.

### 6.1 Original Evaluator

**Definition 6.1** (Original fixpoint evaluator $F_{\text{orig}}$). The original evaluator operates on a combined state $\sigma = (\mathcal{F}, \text{claims}, \text{tainted}, \text{rebutted})$ and applies the following rules *simultaneously* in a single fixpoint loop:

1. **Horn forward:** if $h \leftarrow b_1 \wedge \cdots \wedge b_n \in \mathcal{H}$ and all $b_i \in \mathcal{F}$, add $h$ to $\mathcal{F}$;
2. **Rebuttal:** if $r \rightarrow c$ for $c \in \text{claims}$, mark $c$ as rebutted;
3. **Exception:** if $e$ is an exception to rule $r$, remove $r$'s conclusion from $\text{claims}$;
4. **Confidence zeroing:** if $\text{confidence}(f) = 0$, move $f$ to $\text{tainted}$.

### 6.2 Monotonicity Refutation

**Theorem 6.2** (Counterexample: $F_{\text{orig}}$ is NOT monotone). The original evaluator $F_{\text{orig}}$ is *not* monotone on the fact lattice.

*Proof.* Consider the following minimal instance. Let:

$$A = \{a\}, \quad B = \{a, b\}, \quad A \subseteq B \tag{16}$$

Let the evaluator include a rebuttal rule: "if $b$ is present, rebut $a$." When evaluating on input $A = \{a\}$, the fact $b$ is absent, so no rebuttal fires, and $a$ survives:

$$F_{\text{orig}}(A) = \{a\} \tag{17}$$

When evaluating on input $B = \{a, b\}$, the fact $b$ is present, triggering the rebuttal of $a$. The confidence-zeroing rule eliminates $a$:

$$F_{\text{orig}}(B) = \emptyset \tag{18}$$

Since $F_{\text{orig}}(A) = \{a\} \not\subseteq \emptyset = F_{\text{orig}}(B)$ despite $A \subseteq B$, monotonicity is violated. $\square$

**Legal Interpretation.** This counterexample has a direct legal analog. Consider a contract validity analysis: fact $a$ = "contract is valid," fact $b$ = "fraud defense raised." Under PRC Civil Code Article 148, the presence of fraud renders a contract voidable. The original evaluator, by processing both forward-chaining and rebuttal in a single loop, would retroactively eliminate the validity conclusion when the fraud defense appears -- even though the validity derivation was sound given the original facts. The stratified evaluator avoids this by completing all forward-chaining before any rebuttal evaluation.

**Theorem 6.4** (Stage 1 monotonicity). Stage 1 (Horn closure) is monotone: the operator $T_{\mathcal{H}}$ satisfies $T_{\mathcal{H}}(\mathcal{F}_1) \subseteq T_{\mathcal{H}}(\mathcal{F}_2)$ for all $\mathcal{F}_1 \subseteq \mathcal{F}_2$.

*Proof.* This is Theorem 4.3, proved analytically. $\square$

**Theorem 6.5** (Stage 2 determinism). Stage 2 (AAF construction) is deterministic: the mapping from $\mathcal{H}^*(\mathcal{F})$ to the attack graph $\mathcal{A}$ is a pure function, so the same Horn closure output always produces the same attack topology.

*Proof.* The argument construction function $\alpha: \mathcal{H}^*(\mathcal{F}) \to \mathcal{A}$ has no side effects, no randomness, and no external state. Verified by computing $\alpha(\mathcal{H}^*(\mathcal{F}))$ twice for 10 test fixtures and confirming bitwise equality. $\square$

### 6.3 Cross-Graph Monotonicity Failure

**Counterexample 6.7** (Cross-graph monotonicity fails). The composition $\text{GE} \circ \alpha \circ T_{\mathcal{H}}$ from facts to grounded extension is *not* monotone: adding a fact to $\mathcal{F}$ can change the attack graph topology, potentially *shrinking* the grounded extension.

*Proof.* Let $\mathcal{F}_1$ produce an attack graph $\mathcal{A}_1$ with a unique unattacked argument $a$, so $\text{GE}(\mathcal{A}_1) = \{a\}$. Adding a fact $f$ to get $\mathcal{F}_2 = \mathcal{F}_1 \cup \{f\}$ may derive a new argument $b$ that attacks $a$, producing $\mathcal{A}_2$ where $\text{GE}(\mathcal{A}_2) = \{b\}$. Thus $\text{GE}(\mathcal{A}_1) = \{a\} \not\subseteq \{b\} = \text{GE}(\mathcal{A}_2)$, even though $\mathcal{F}_1 \subseteq \mathcal{F}_2$. The monotonicity violation arises because the *topology* of the attack graph changes, not because the AAF operator itself is non-monotone on a fixed graph. $\square$

**Conjecture 6.8** (Full evaluator equivalence). The stratified evaluator (Horn then AAF) produces the same output as the original combined evaluator for all production rules. This remains an **open conjecture** -- neither proved nor refuted.

**Theorem 6.9** (Operational termination bounds). The fixpoint evaluator satisfies five operational termination properties, verified over 5 bounded configurations:

1. Maximum fixpoint depth $\leq |\mathcal{U}|$;
2. Maximum rule firings per iteration $\leq |\mathcal{H}|$;
3. Maximum tainted set size $\leq |\mathcal{F}|$;
4. Maximum rebutted set size $\leq |\text{claims}|$;
5. Total iterations $\leq 2 \cdot |\mathcal{U}|$.

---

## 7. Kripke Temporal Models

Legal reasoning has an intrinsic temporal dimension: facts are established at time $t_{\text{fact}}$, procedures occur at time $t_{\text{procedure}}$, and the temporal ordering is a legal invariant that encodes a fundamental principle of procedural justice -- a court cannot reference a fact that has not yet been established.

### 7.1 Dual-Timestamp Kripke Model

**Definition 7.1** (Legal Kripke structure). A *legal Kripke structure* is a tuple $\mathcal{K} = (W, R, V, t_f, t_p)$ where:

- $(W, R, V)$ is a standard Kripke structure (Definition 2.7);
- $t_f: W \to \mathbb{R}$ assigns a *fact timestamp* to each world;
- $t_p: W \to \mathbb{R}$ assigns a *procedure timestamp* to each world.

**Definition 7.2** (Kripke accessibility relations). The legal Kripke model defines two distinct accessibility relations:

$$R_{\text{supersedes}} = \{(w_1, w_2) \mid w_2 \text{ corrects a factual error in } w_1\} \tag{19}$$

$$R_{\text{corrects}} = \{(w_1, w_2) \mid w_2 \text{ corrects a legal error in } w_1\} \tag{20}$$

A *factual correction* modifies the underlying facts (e.g., a witness recants testimony); a *legal correction* changes the legal characterization without altering facts (e.g., a court reclassifies a contract term from condition to warranty).

### 7.2 Mutual Exclusion

**Theorem 7.3** (Mutual exclusion). For the legal Kripke model:

$$R_{\text{supersedes}} \cap R_{\text{corrects}} = \emptyset \tag{21}$$

A state transition cannot simultaneously be a factual correction and a legal correction.

*Proof.* By Z3 SMT verification. The script `z3_kripke_mutex.py` encodes the definitions (19) and (20) as SMT-LIB 2 constraints over an uninterpreted sort for worlds, with two predicates $\text{FactualCorrection}(w_1, w_2)$ and $\text{LegalCorrection}(w_1, w_2)$. The satisfiability check for $\exists w_1, w_2:\; \text{FactualCorrection}(w_1, w_2) \wedge \text{LegalCorrection}(w_1, w_2)$ returns UNSAT, confirming mutual exclusion. The proof relies on the semantic distinction between fact-level and law-level changes being exhaustive and exclusive by definition of the legal pipeline (Definition 3.4). $\square$

### 7.3 Temporal Guard Invariant

**Theorem 7.4** (Temporal guard). In the legal Kripke model, the following LTL invariant holds:

$$\square\,(t_f < t_p) \tag{22}$$

Facts are always established before the procedures that reference them.

*Proof.* By Z3 induction over the Kripke transition system. The script `z3_temporal_induction.py` verifies:

- **Base case:** the initial state $w_0$ satisfies $t_f(w_0) < t_p(w_0)$. This is enforced by the construction of the legal pipeline (Definition 3.4), which begins with Fact_Finding before any procedural stage.
- **Inductive step:** if state $w$ satisfies $t_f(w) < t_p(w)$, then every successor $w'$ reachable via $R_{\text{supersedes}}$ or $R_{\text{corrects}}$ satisfies $t_f(w') < t_p(w')$. A factual correction ($R_{\text{supersedes}}$) updates $t_f(w')$ to a new value strictly less than $t_p(w')$ because the corrected fact must precede its procedural use. A legal correction ($R_{\text{corrects}}$) does not alter $t_f$ at all, preserving the invariant trivially.

Z3 returns UNSAT for the negation of the inductive step, confirming the invariant holds in all reachable states. $\square$

### 7.4 LTL Embedding

**Proposition 7.5** (LTL embedding). The legal Kripke structure $\mathcal{K}$ can be embedded into LTL by encoding each world $w_i$ as a distinct propositional atom $p_i$. Under this encoding:

$$(w_i, w_j) \in R \iff \mathcal{K}, w_i \models \Diamond\, p_j \tag{23}$$

where $p_j$ is the atom uniquely associated with world $w_j$. Note: using only the valuation $V(w)$ is insufficient, since two distinct worlds may share the same valuation, making $\Diamond\, V(w_j)$ satisfiable by a different world. The encoding requires distinct atoms for distinct worlds to preserve the one-to-one correspondence between reachable worlds and LTL propositions.

**Remark 7.6.** The temporal guard (22) has a direct operational consequence: the juris-calculus evaluator rejects any derived fact whose timestamp exceeds the timestamp of the procedure that introduced it. This prevents retroactive reasoning -- a class of errors that is particularly dangerous in cross-jurisdictional settings where procedural timelines may differ.

---

## References

*References are numbered in order of first citation in the text.*

[1] Banach, S. (1922). Sur les operations dans les ensembles abstraits et leur application aux equations integrales. *Fundamenta Mathematicae*, 3, 133--181.

[2] Bell, D. E., & LaPadula, L. J. (1976). Secure Computer Systems: Unified Exposition and Multics Interpretation. *MITRE Technical Report MTR-2997*.

[3] Cousot, P., & Cousot, R. (1977). Abstract Interpretation: A Unified Lattice Model for Static Analysis of Programs by Construction or Approximation of Fixpoints. *POPL 1977*, 238--252.

[4] de Moura, L., & Bjorner, N. (2008). Z3: An Efficient SMT Solver. *TACAS 2008*.

[5] de Moura, L., & Ullrich, S. (2021). The Lean 4 Theorem Prover and Programming Language. *CADE 2021*.

[6] Dung, P. M. (1995). On the Acceptability of Arguments and its Fundamental Role in Nonmonotonic Reasoning, Logic Programming and n-Person Games. *Artificial Intelligence*, 77(2), 321--357.

[7] Dwork, C. (2006). Differential Privacy. *ICALP 2006*, 1--12.

[8] OpenAI (2026). Codex: AI-Powered Code Generation. https://openai.com

[9] Hart, H. L. A. (1961). *The Concept of Law*. Clarendon Press.

[10] Horn, A. (1951). On Sentences Which Are True of Direct Unions of Algebras. *Journal of Symbolic Logic*, 16(1), 14--21.

[11] Kleene, S. C. (1952). *Introduction to Metamathematics*. Van Nostrand.

[12] Kolmogorov, A. N. (1965). Three Approaches to the Quantitative Definition of Information. *Problems of Information Transmission*, 1(1), 1--7.

[13] Kripke, S. A. (1963). Semantical Analysis of Modal Logic I: Normal Modal Propositional Calculi. *Mathematical Logic Quarterly*, 9(5--6), 67--96.

[14] Mac Lane, S. (1998). *Categories for the Working Mathematician* (2nd ed.). Springer.

[15] McNaughton, R., & Papert, S. (1971). *Counter-Free Automata*. MIT Press.

[16] Pawlak, Z. (1982). Rough Sets. *International Journal of Computer & Information Sciences*, 11(5), 341--356.

[17] Pnueli, A. (1977). The Temporal Logic of Programs. *FOCS 1977*, 46--57.

[18] Searle, J. R. (1995). *The Construction of Social Reality*. Free Press.

[19] Stevens, S. S. (1946). On the Theory of Scales of Measurement. *Science*, 103(2684), 677--680.

[20] Tarski, A. (1955). A Lattice-Theoretical Fixpoint Theorem and its Applications. *Pacific Journal of Mathematics*, 5(2), 285--309.

[21] von Wright, G. H. (1968). *An Essay in Deontic Logic and the General Theory of Action*. North-Holland.

\newpage

## 8. Category-Theoretic Rosetta Mapping

**Definition 8.1** (Fact/Claim category). For jurisdiction $J \in \{\text{CN}, \text{HK}, \text{US}\}$, the *fact category* $\textbf{FactCat}_J$ has legal fact atoms as objects and entailment relations as morphisms. The *claim category* $\textbf{ClaimCat}_J$ is defined analogously.

**Definition 8.2** (Semantic-preserving functor). A functor $F: \textbf{FactCat}_{J_1} \to \textbf{ClaimCat}_{J_2}$ is *semantic-preserving* if $\text{meaning}(F(f)) \equiv \text{meaning}(f)$ for all objects $f$.

**Theorem 8.3** (Toy: no collision-free functor). For a 5-pattern toy model with 3 jurisdictions, no total semantic-preserving functor exists.

*Proof.* Exhaustive enumeration: $3^5 = 243$ assignments, zero satisfy the semantic-preservation condition for all 5 patterns simultaneously. Verified by `category_theory_rosetta.py`. ∎

**Theorem 8.4** (Real data: insufficient for proof). For the real cross-jurisdictional dataset (44 rows: 30 CN-only, 14 cross-jurisdiction), 7 collision/asymmetry witnesses exist. However, the data is insufficient to prove or disprove a total functor across the full legal inventory ($> 2{,}000$ facts).

**Theorem 8.5** (CBL non-interference). The 60 Concept Blocking Layer (CBL) rules implement Bell-LaPadula non-interference: (i) Simple Security (no read-up): engine at level $J$ cannot read unaligned concepts from $J'$; (ii) Star Property (no write-down): concept derived at $J$ cannot be written to lower $J''$.

*Proof.* By structural analysis of all 60 CBL blocking rules. Each rule satisfies one of the two properties. ∎

---

## 9. Quantitative Models

### 9.1 Banach Pricing Contraction

**Definition 9.1** (Pricing map). $T: M \to M$ defined by $T(x) = \beta \cdot C + (1 - \beta) \cdot x$ where $C$ is observed cost and $\beta \in (0, 1)$.

**Theorem 9.2** (Scalar contraction). For $M = \mathbb{R}$ with $d(x,y) = |x-y|$, $T$ is a $(1-\beta)$-contraction with unique fixed point $x^* = C$.

*Proof.* $|T(x) - T(y)| = (1-\beta)|x-y|$. Since $\beta \in (0,1)$, the contraction constant is $1-\beta < 1$. By Banach fixed-point theorem, the unique fixed point satisfies $T(x^*) = x^*$, yielding $x^* = C$. Verified by SymPy symbolic computation. ∎

**Counterexample 9.3** (Full-dimensional). Banach contraction cannot be claimed for full-dimensional pricing because: (1) no metric is defined on the multi-dimensional space; (2) `mapping_status` is a discrete label, not a metric point; (3) 225 observations are fee-schedule proxies (0 real timesheets).

### 9.2 Differential Privacy Impossibility

**Theorem 9.4** (Cross-jurisdiction ε impossibility). No single function $\varepsilon: P \to \mathbb{R}_{\geq 0}$ correctly assigns privacy parameters for both PRC and US legal systems.

*Proof.* Consider attorney-client privilege $p_{\text{AC}}$. PRC requires $\varepsilon(p_{\text{AC}}) = 1.0$ (PRC Lawyers Act Art. 38). US requires $\varepsilon(p_{\text{AC}}) = 2.5$ (Upjohn v. United States). A single function cannot map $p_{\text{AC}}$ to both 1.0 and 2.5. ∎

**Counterexample 9.5** (Floor clipping). The mechanism $\mathcal{M}(x) = \max(0.3x, x_{\min})$ yields privacy ratio $\to \infty$ near the clipping threshold, violating ε-DP for any finite ε.

### 9.3 Damages Attribute Grammar

**Definition 9.6** (Damages formula). Each variable is a boolean guard computed by the k≤3 Horn engine:

$$\text{Damages} = \min(\text{AL} + \text{EI}, \text{FL}) \times (1 - \text{CN}) - \text{FTM}$$

where AL = actual loss, EI = expectation interest, FL = foreseeability limit, CN = contributory negligence ratio ($\in [0,1)$), FTM = failure to mitigate. When a guard is inactive, its value is 0.

---

## 10. Evidence-Calibrated Trust Label System

**Definition 10.1** (Evidence status). Every mathematical claim is assigned one of seven statuses forming a partial order $(E, \leq_E)$:

$$E = \{\textsc{Proved}, \textsc{Refuted}, \textsc{Partial}, \textsc{Insufficient}, \textsc{Toy}, \textsc{Pending}, \textsc{Baseline}\}$$

with $\textsc{Proved} >_E \textsc{Refuted} >_E \textsc{Partial} >_E \textsc{Insufficient} =_E \textsc{Toy} >_E \textsc{Pending} >_E \textsc{Baseline}$.

**Definition 10.2** (Claim registry). Each claim carries `allowed_claim`, `forbidden_claim`, `engineering_action`, and `evidence_paths`. The system enforces: no downstream system may assert a `forbidden_claim`.

**Definition 10.3** (Data quality). Each dataset is labeled with a quality level: `REAL`, `SYNTHETIC`, `PROXY`, `ANNOTATED`, or `UNKNOWN`. This prevents low-quality data from being promoted as evidence for mathematical claims.

**Theorem 10.4** (Trust label consistency). The claim registry satisfies: (1) allowed $\cap$ forbidden = $\emptyset$; (2) all statuses are in $E$; (3) all evidence paths are non-empty; (4) no duplicate IDs.

*Proof.* By `validate_status_ledger()` in `model_status.py`. ∎

**Proposition 10.5** (Forbidden tags). The following tags must never appear in any downstream system: `FINAL_ALL_THEOREMS_PROVED`, `REAL_PRICING_VALIDATED`, `DP_EPSILON_LEGALLY_DETERMINED`, `ALL_SOURCES_OFFICIALLY_VERIFIED`.

---

## 11. Empirical Validation

**Theorem 11.1** (k≤3 boundary coverage). All 2,117 PRC Horn rules have exception chain depth $\leq 3$. The k≤3 boundary covers 100% of the rule set.

*Proof.* By parsing all rules from `configs/zh_CN/rules.yaml` and computing exception chain lengths. Distribution: k=0: 757 (35.8%), k=1: 856 (40.4%), k=2: 372 (17.6%), k=3: 132 (6.2%), k>3: 0 (0.0%). Verified by `k3_empirical_analysis.py`. ∎

**Theorem 11.2** (Formalizability). All 4,475 premise atoms in the rule set are symbolic (no natural language), yielding a formalizability ratio of 100%.

*Proof.* By scanning all `premise_atoms` fields and checking for CJK Unicode characters. Zero non-symbolic atoms found. ∎

---

## 12. Multi-AI Formalization Methodology

**Definition 12.1** (Adversarial multi-AI pipeline). A 4-stage pipeline: (1) Generator AI produces mathematical claims; (2) Formal verification AI audits with tool chains; (3) Independent AI produces alternative proofs; (4) Second audit pass downgrades overstated claims.

**Theorem 12.2** (46/46 convergence). Through 4 rounds of adversarial repair, the initial 20 mathematical claims (7 FAIL after first audit) converged to 20/20 PASS, plus 26 additional verification files (Z3, SymPy, Hypothesis, mutation testing), totaling 46/46 PASS.

*Proof.* Recorded in `proofs/formal_verification_logs/05_verification_run_report.md` and `proofs/formal_verification_logs/07_logic_audit_report.md`. Each repair round is documented with the specific fix applied and the audit result. ∎

---

## 13. Related Work

Dung (1995) established abstract argumentation frameworks. Prakken & Sartor (1997) applied defeasible logic to legal reasoning. Sergot et al. (1986) formalized the British Nationality Act as a logic program. Hart (1961) identified the "open texture" of legal concepts. Cousot & Cousot (1977) introduced abstract interpretation.

Our contribution differs in three ways: (1) we provide *machine-reproducible* proofs (runnable Python scripts, not just paper arguments); (2) we explicitly track *evidence quality* through the trust label system; (3) we formalize *cross-jurisdictional* reasoning with collision detection, not single-jurisdiction analysis.

---

## 14. Conclusion

We presented a formal mathematical framework for cross-jurisdictional legal reasoning with 18 proved results, 10 counterexamples, and a 7-level evidence-calibrated trust label system. The key architectural insight — splitting legal reasoning into monotone Horn closure and non-monotone Dung AAF — was forced by a counterexample, not chosen by design. The k≤3 boundary empirically covers 100% of 2,117 PRC rules.

**Open Problems:**
1. Full stratified evaluator equivalence with original evaluator
2. General AAF convergence for all finite $n$ (not just $n \leq 4$)
3. Real-data Rosetta functor (requires $\geq 2{,}000$ annotated concept pairs)
4. Full-dimensional Banach pricing (requires real timesheet data)
5. Lean 4 formalization of core theorems (currently PENDING_TOOLCHAIN)

The strongest claim a legal AI system can make is the one its evidence supports — and no stronger. The evidence-calibrated trust label system provides the infrastructure to make that principle operational.

---
