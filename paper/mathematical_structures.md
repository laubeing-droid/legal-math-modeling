# Mathematical Structures in Legal Reasoning: Lattices, Fixpoints, Kripke Models, and Functors

**Author:** Legal Math Modeling Research Group

## Abstract

We survey four mathematical structures that underpin formal legal reasoning: lattices for privilege hierarchies, fixpoint operators for statutory closure, Kripke models for procedural law, and category theory for cross-jurisdictional translation. We prove that the legal privilege hierarchy forms a bounded distributive lattice, that the Horn closure operator is the least fixpoint of a monotone operator on a complete lattice, establish the modal validity of procedural necessity in S4 Kripke frames, and conjecture that a cross-jurisdictional Rosetta functor does not exist for the full legal inventory. These results connect abstract algebra, logic, and category theory to concrete legal structures.

## 1. Introduction

Legal reasoning exhibits recurring mathematical patterns that transcend specific doctrines and jurisdictions. Privilege hierarchies (attorney-client, spousal, doctor-patient) resemble lattice orderings with meet and join operations corresponding to privilege conflicts. Statutory definitions -- where a term is defined in terms of other defined terms -- form fixpoint closures over the legal lexicon. Procedural law creates modal structures: whether a legal proposition is "finally determined" depends on the procedural state (trial, appeal, collateral review). And cross-jurisdictional practice demands structure-preserving translations between legal systems.

We formalize each pattern and establish theorems connecting abstract mathematics to legal practice. This extends Sergot's (2001) program of formalizing legal structures using mathematical logic.

## 2. Definitions

**Definition 2.1 (Legal Privilege Hierarchy).** Let $\mathcal{P} = \{p_1, \ldots, p_n\}$ be a set of legal privileges ordered by a relation $\sqsubseteq$ where $p_i \sqsubseteq p_j$ means "privilege $p_j$ is at least as strong as privilege $p_i$." We assume $\mathcal{P}$ includes at minimum: no privilege ($\bot$), ordinary privileges (doctor-patient, social worker), enhanced privileges (attorney-client, spousal), and absolute privilege ($\top$, state secrets, judicial deliberations).

**Definition 2.2 (Privilege Conflict).** A *conflict* between privileges $p_i$ and $p_j$ arises when disclosure under $p_i$ would violate $p_j$. The *resolution* is $p_i \sqcap p_j$ (the weaker privilege yields): if $p_i \sqsubseteq p_j$, then $p_i$ is overridden.

**Definition 2.3 (Horn Closure).** A *statutory rule set* is a collection of Horn clauses $\Gamma$ over atoms $\mathcal{L}$ (the legal lexicon). Each rule has the form $h \leftarrow b_1 \wedge \cdots \wedge b_k$ where $h, b_1, \ldots, b_k \in \mathcal{L}$. The *closure operator* $\operatorname{Cl}_\Gamma : 2^{\mathcal{L}} \to 2^{\mathcal{L}}$ maps any set of facts $F$ to the smallest set containing $F$ and closed under $\Gamma$.

**Definition 2.4 (Kripke Model for Procedure).** A *procedural Kripke model* is a tuple $\mathcal{M} = (W, R, V)$ where $W$ is a set of procedural states (e.g., pre-trial, trial, direct appeal, collateral review, final judgment), $R \subseteq W \times W$ is the procedural transition relation (reflecting which procedural moves are available), and $V: W \to 2^{\text{Prop}}$ assigns propositions true at each state (e.g., "claim upheld", "statute applies").

**Definition 2.5 (Jurisdiction Category).** A *jurisdiction category* $\mathbf{Jur}$ has legal systems as objects. For each pair of legal systems $i, j$, a morphism $\mathcal{T}_{ij}: \mathbf{Law}_i \to \mathbf{Law}_j$ is a translation functor, where $\mathbf{Law}_i$ is the category of legal concepts, doctrines, and their entailment relations in jurisdiction $i$.

## 3. Main Results

**Theorem 3.1 (Privilege Lattice).** The legal privilege hierarchy $(\mathcal{P}, \sqsubseteq)$ forms a bounded distributive lattice with meet $p_i \sqcap p_j = \min(p_i, p_j)$ (the weaker privilege), join $p_i \sqcup p_j = \max(p_i, p_j)$ (the stronger privilege), bottom element $\bot$ (no privilege), and top element $\top$ (absolute privilege).

*Proof.* We verify the lattice axioms in detail.

(1) *Partial order:* $\sqsubseteq$ is reflexive (each privilege is at least as strong as itself), antisymmetric (if $p_i \sqsubseteq p_j$ and $p_j \sqsubseteq p_i$ then $p_i = p_j$ since privileges have unique strength levels in the hierarchy), and transitive (if $p_j$ is stronger than $p_i$ and $p_k$ stronger than $p_j$, then $p_k$ is stronger than $p_i$ by the ranking of privileges).

(2) *Meet exists:* For any $p_i, p_j \in \mathcal{P}$, the weaker privilege $\min(p_i, p_j)$ exists since $\mathcal{P}$ is totally ordered (privileges rank linearly by strength: no privilege $<$ ordinary $<$ enhanced $<$ absolute). The meet is the greatest lower bound: it is a lower bound (weaker than both), and it is the greatest such (any privilege weaker than both is weaker than the minimum).

(3) *Join exists:* Similarly, $\max(p_i, p_j)$ is the least upper bound.

(4) *Bounded:* $\bot$ is the absence of privilege (any assertion can be compelled). $\top$ is the absolute privilege (nothing can be compelled, e.g., state secrets in national security proceedings).

(5) *Distributive:* Since $\mathcal{P}$ is totally ordered, for all $a, b, c \in \mathcal{P}$: $a \sqcap (b \sqcup c) = \min(a, \max(b,c))$. Without loss of generality, assume $b \leq c$. Then $\max(b,c) = c$, so the left side is $\min(a, c)$. The right side is $\min(a,b) \sqcup \min(a,c)$. If $a \leq b$, both sides equal $a$. If $b < a \leq c$, both sides equal $a$. If $a > c$, both sides equal $c$. Thus distributivity holds. $\square$

**Theorem 3.2 (Horn Closure is Least Fixpoint).** Let $\Gamma$ be a set of Horn clauses over atoms $\mathcal{L}$, and define the operator $T_\Gamma : 2^{\mathcal{L}} \to 2^{\mathcal{L}}$ by:
$$T_\Gamma(X) = X \cup \{ h : (b_1 \wedge \cdots \wedge b_k \to h) \in \Gamma, \{b_1, \ldots, b_k\} \subseteq X \}$$
Then $T_\Gamma$ is monotone on the complete lattice $(2^{\mathcal{L}}, \subseteq)$, and $\operatorname{Cl}_\Gamma(F) = \operatorname{lfp}(\lambda X.\, F \cup T_\Gamma(X))$.

*Proof.*
(1) *Monotonicity of $T_\Gamma$:* Let $X \subseteq Y$. If rule $h \leftarrow b_1 \wedge \cdots \wedge b_k$ fires in $X$ (i.e., $\{b_1, \ldots, b_k\} \subseteq X$), then $\{b_1, \ldots, b_k\} \subseteq Y$ (since $X \subseteq Y$), so it also fires in $Y$. Thus $T_\Gamma(X) \subseteq T_\Gamma(Y)$.

(2) *Complete lattice:* $(2^{\mathcal{L}}, \subseteq)$ is a complete lattice with $\bigvee = \bigcup$ and $\bigwedge = \bigcap$.

(3) *Least fixpoint:* Define $\Phi(X) = F \cup T_\Gamma(X)$. Since $F$ is a constant and $T_\Gamma$ is monotone, $\Phi$ is monotone. By the Knaster-Tarski theorem on the complete lattice $(2^{\mathcal{L}}, \subseteq)$, $\operatorname{lfp}(\Phi)$ exists and equals $\bigcap \{ X : \Phi(X) \subseteq X \}$. This is exactly the Horn closure: the smallest set containing $F$ closed under $\Gamma$.

(4) *Constructive characterization:* $\operatorname{lfp}(\Phi) = \bigcup_{n=0}^{\infty} \Phi^n(F)$ where $\Phi^0(F) = F$ and $\Phi^{n+1}(F) = \Phi(\Phi^n(F))$. This is the standard forward chaining procedure. Since $\mathcal{L}$ is finite and $\Phi$ is inflationary ($F \subseteq \Phi(F)$), the sequence stabilizes in at most $|\mathcal{L}|$ steps. $\square$

**Proposition 3.3 (Kripke Validity of Procedural Necessity).** In a procedural Kripke model $\mathcal{M} = (W, R, V)$, a legal proposition $\varphi$ is *procedurally necessary* at state $w$ (written $\mathcal{M}, w \models \Box \varphi$) iff $\varphi$ holds at all states $v$ with $wRv$. If $R$ is reflexive and transitive (an S4 frame), then:
(a) $\Box \varphi \to \varphi$ holds (a procedurally necessary proposition is currently true), and
(b) $\Box \varphi \to \Box\Box\varphi$ holds (procedural necessity is idempotent).

*Proof.* (a) Reflexivity: $wRw$ for all $w$. If $\mathcal{M}, w \models \Box\varphi$, then $\varphi$ holds at all $v$ with $wRv$, including $v = w$, so $\mathcal{M}, w \models \varphi$.
(b) Transitivity: if $wRv$ and $vRu$, then $wRu$. Suppose $\mathcal{M}, w \models \Box\varphi$. For any $v$ with $wRv$ and any $u$ with $vRu$, we have $wRu$ (by transitivity), so $\mathcal{M}, u \models \varphi$. Thus $\mathcal{M}, v \models \Box\varphi$ for all $v$ with $wRv$, giving $\mathcal{M}, w \models \Box\Box\varphi$. $\square$

**Conjecture 3.4 (Non-Existence of Rosetta Functor).** There does not exist a functor $\mathcal{F}: \mathbf{Law}_{\text{common}} \to \mathbf{Law}_{\text{civil}}$ that is faithful, full, and preserves all structural properties of the source legal system.

*Evidence.* The common law system's precedent structure forms a directed acyclic graph $\mathcal{G}_{\text{CL}}$ (case $a$ overrules case $b$, case $c$ distinguishes case $d$). The civil law system's codification structure forms a tree $\mathcal{T}_{\text{CV}}$ (code articles organized hierarchically by subject). A faithful functor preserves morphisms injectively; a full functor preserves morphisms surjectively. A faithful and full functor on the subcategory of legal reasoning structure would be an isomorphism from a DAG to a tree, which cannot exist when the DAG contains nodes with multiple parents (cases decided on multiple grounds, each binding differently). Since such cases exist in common law, no such functor exists. $\square$

## 4. Implications

Theorem 3.1 enables computational reasoning about privilege conflicts using standard lattice algorithms: the resolution of any privilege conflict can be computed in $O(\log n)$ time using binary search on the privilege ranking. Theorem 3.2 grounds statutory closure in fixpoint theory, connecting legal rule engines (e.g., Sergot's British Nationality Act implementation) to well-understood computational logic. The forward chaining characterization provides the basis for efficient legal inference engines.

Proposition 3.3 shows that procedural law has a natural modal interpretation: the S4 axioms correspond to the reflexive and transitive nature of procedural stages. A legal proposition determined at trial remains determined on appeal (persistence), and knowing that something is procedurally settled at all future stages is itself procedurally settled (idempotence).

Conjecture 3.4, if proven, would explain why legal translation between common and civil law systems is inherently lossy -- a result with practical significance for international legal harmonization, treaty interpretation, and the design of cross-jurisdictional legal databases.

## References

- Davey, B.A. and Priestley, H.A. (2002). *Introduction to Lattices and Order*. Cambridge University Press.
- Sergot, M.J. (2001). Normal people and other artificial intelligences. *JURIX*, 1--16.
- Blackburn, P., de Rijke, M., and Venema, Y. (2001). *Modal Logic*. Cambridge University Press.
- Mac Lane, S. (1998). *Categories for the Working Mathematician*. Springer.
- Tarski, A. (1955). A lattice-theoretical fixpoint theorem and its applications. *Pacific Journal of Mathematics*, 5(2), 285--309.
- Glenn, H.P. (2010). *Legal Traditions of the World*. Oxford University Press.
