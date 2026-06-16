# Argumentation Frameworks Beyond Dung: A Formal Comparison of Dung AF and ASPIC+

**Author:** Legal Math Modeling Research Group

## Abstract

We present a formal comparison of Dung's abstract argumentation frameworks (AF) and the structured argumentation framework ASPIC+. We prove that ASPIC+ strictly subsumes Dung AF: every Dung AF can be encoded as an ASPIC+ instance, but the converse fails. We formalize preference-based defeat and establish that under a strict partial order on preferences, the ASPIC+ grounded extension exists and is unique. These results clarify the expressiveness hierarchy of argumentation formalisms used in legal reasoning.

## 1. Introduction

Dung's abstract argumentation framework (1995) is the dominant paradigm for formal argumentation in AI and law. However, its abstraction discards internal argument structure, conflating fundamentally different attack types such as undercutting, undermining, and rebutting. ASPIC+ (Modgil and Prakken, 2013) restores this by incorporating premises, inference rules, attack classification, and preference orderings. We formally compare the two frameworks, establish strict subsumption, and prove well-behavedness of the grounded semantics under preferences. Our work extends Baroni et al.'s (2011) systematic study of argumentation semantics and has direct implications for computational legal reasoning.

## 2. Definitions

**Definition 2.1 (Dung AF).** A *Dung argumentation framework* is a pair $\mathcal{F} = (A, D)$ where $A$ is a set of arguments and $D \subseteq A \times A$ is a binary defeat relation.

**Definition 2.2 (ASPIC+ Framework).** An *ASPIC+ framework* is a tuple $\mathcal{A} = (\mathcal{K}, \mathcal{R}, \preceq, n)$ where $\mathcal{K}$ is a set of knowledge premises partitioned into $\mathcal{K}_n$ (ordinary), $\mathcal{K}_p$ (premissible), and $\mathcal{K}_a$ (assumptions); $\mathcal{R} = \mathcal{R}_s \cup \mathcal{R}_d$ is a set of strict ($\mathcal{R}_s$) and defeasible ($\mathcal{R}_d$) inference rules; $\preceq$ is a preference ordering on $\mathcal{R}_d$; and $n: \mathcal{R}_d \to \mathcal{L}$ maps defeasible rules to their names for undercutting.

**Definition 2.3 (Arguments in ASPIC+).** An *argument* $A$ in ASPIC+ is a tree where each node is labeled by a formula, leaves are elements of $\mathcal{K}$, and each non-leaf node is derived by an inference rule in $\mathcal{R}$. Let $\operatorname{Prem}(A)$, $\operatorname{Conc}(A)$, $\operatorname{Sub}(A)$, and $\operatorname{Rules}(A)$ denote the premises, conclusion, sub-arguments, and rules of $A$.

**Definition 2.4 (Contraries).** A *contrary function* is a mapping $\overline{\cdot} : \mathcal{L} \to 2^{\mathcal{L}}$ assigning to each formula its set of contraries. Formula $\varphi$ is a contrary of $\psi$ iff $\varphi \in \overline{\psi}$.

**Definition 2.5 (Attack and Defeat).** Argument $A$ *attacks* $B$ iff one of three conditions holds:

1. *Undercut:* $\operatorname{Conc}(A) \in \overline{n(r)}$ for some defeasible rule $r \in \operatorname{Rules}(B)$.
2. *Undermine:* $\operatorname{Conc}(A) \in \overline{p}$ for some premise $p \in \operatorname{Prem}(B) \cap (\mathcal{K}_p \cup \mathcal{K}_a)$.
3. *Rebut:* $\operatorname{Conc}(A) \in \overline{\operatorname{Conc}(B')}$ for some defeasible sub-argument $B' \in \operatorname{Sub}(B)$.

Argument $A$ *defeats* $B$ iff $A$ attacks $B$ and either the attack is an undercut (which is not ordered by $\preceq$) or the last defeasible rule of $A$ is not strictly dominated by the attacked rule in $B$ under $\preceq$.

**Definition 2.6 (Dung Translation).** The *Dung translation* of an ASPIC+ framework $\mathcal{A}$ produces a Dung AF $\mathcal{F}_{\mathcal{A}} = (\operatorname{Args}(\mathcal{A}), \operatorname{Defeat}_{\mathcal{A}})$ where $\operatorname{Args}(\mathcal{A})$ is the set of all constructible arguments and $\operatorname{Defeat}_{\mathcal{A}}$ is the defeat relation from Definition 2.5.

## 3. Main Results

**Lemma 3.0 (Encoding Lemma).** For any finite Dung AF $\mathcal{F} = (A, D)$ with $A = \{a_1, \ldots, a_n\}$, there exists a flat ASPIC+ framework (no inference rules of depth $> 1$) whose Dung translation is isomorphic to $\mathcal{F}$.

*Proof.* Construct $\mathcal{A}$ as follows. For each $a_i \in A$: add a premise $p_i \in \mathcal{K}_n$ and a defeasible rule $r_i : p_i \Rightarrow a_i$ with $n(r_i) = a_i^*$. For each defeat $(a_i, a_j) \in D$: add premise $k_{ij} \in \mathcal{K}_n$ and a strict rule $s_{ij} : k_{ij} \to \overline{a_j^*}$, ensuring $s_{ij}$ produces the name contrary of $r_j$. The resulting arguments are $A_i = (p_i, r_i, a_i)$ for each $i$, and $A_i$ undercuts $A_j$ iff $(a_i, a_j) \in D$. With flat preferences ($\preceq$ is empty), defeat coincides with attack, and the translated AF is isomorphic to $\mathcal{F}$. $\square$

**Theorem 3.1 (Weak Subsumption).** For every Dung AF $\mathcal{F} = (A, D)$, there exists an ASPIC+ framework $\mathcal{A}$ such that $\mathcal{F}_{\mathcal{A}} \cong \mathcal{F}$.

*Proof.* Immediate from Lemma 3.0. $\square$

**Theorem 3.2 (Strict Subsumption).** There exist ASPIC+ frameworks whose generated Dung AF cannot be represented by any Dung AF that preserves both argument structure and preference-sensitivity, i.e., ASPIC+ strictly subsumes Dung AF.

*Proof.* Consider an ASPIC+ framework with premises $p, q \in \mathcal{K}_n$, defeasible rules $r_1 : p \Rightarrow \varphi$ and $r_2 : q \Rightarrow \neg\varphi$, and a preference $r_1 \prec r_2$. The resulting Dung AF is $\{A_1, A_2\}$ with defeat $A_2 \to A_1$. Now change the preference to $r_2 \prec r_1$: the defeat reverses to $A_1 \to A_2$. Both cases produce different Dung AFs from structurally identical argument bases. A single Dung AF cannot represent both simultaneously, since it has no mechanism for encoding preference-dependent defeat. More formally, define the equivalence class $[\mathcal{A}]$ of ASPIC+ frameworks sharing the same arguments but varying preferences. The mapping $\mathcal{A} \mapsto \mathcal{F}_{\mathcal{A}}$ is not injective on $[\mathcal{A}]$: multiple ASPIC+ instances yield the same abstract AF. Conversely, the surjection from $[\mathcal{A}]$ onto possible Dung AFs is non-trivially many-to-one, meaning structural information is lost in translation. Thus no encoding of a preference-sensitive ASPIC+ framework into a single Dung AF can preserve the preference modulation that distinguishes undercutting from preference-ordered rebutting. $\square$

**Theorem 3.3 (Existence and Uniqueness of Grounded Extension).** Let $\mathcal{A}$ be an ASPIC+ framework with a strict partial order $\prec$ on $\mathcal{R}$ (i.e., $\preceq$ is irreflexive and transitive) and a finite set of arguments. Then the ASPIC+ grounded extension exists and is unique.

*Proof.* Under a strict partial order, defeat is well-defined. We show the grounded extension exists and is unique:

(1) *Finiteness:* Since $\mathcal{K}$ and $\mathcal{R}$ are finite, the set of constructible arguments $\operatorname{Args}(\mathcal{A})$ is finite (each argument is a finite tree over finite components).

(2) *Monotone characteristic function:* Define $F_{\mathcal{A}}(S) = \{ A \in \operatorname{Args}(\mathcal{A}) : A \text{ is acceptable w.r.t. } S \}$ where $A$ is acceptable w.r.t. $S$ iff for every $B$ that defeats $A$, there exists $C \in S$ that defeats $B$. The function $F_{\mathcal{A}}$ is monotone: if $S \subseteq T$ and $A \in F_{\mathcal{A}}(S)$, then every defeater of $A$ is defeated by some $C \in S \subseteq T$, so $A \in F_{\mathcal{A}}(T)$. Note: $F_{\mathcal{A}}$ is monotone regardless of whether the defeat relation is cyclic; the Knaster-Tarski theorem does not require well-foundedness.

(3) *Knaster-Tarski application:* On the complete lattice $(2^{\operatorname{Args}}, \subseteq)$, the monotone function $F_{\mathcal{A}}$ has a least fixpoint $\operatorname{lfp}(F_{\mathcal{A}}) = \bigcap \{ S \subseteq \operatorname{Args} : F_{\mathcal{A}}(S) \subseteq S \}$.

(4) *Constructive iteration:* $\operatorname{lfp}(F_{\mathcal{A}}) = \bigcup_{n \geq 0} F_{\mathcal{A}}^n(\emptyset)$, which converges in at most $|\operatorname{Args}|$ steps.

This least fixpoint is the unique grounded extension. $\square$

**Corollary 3.4.** Under the hypotheses of Theorem 3.3, the grounded extension is conflict-free and admissible.

*Proof.* The grounded extension $G = \operatorname{lfp}(F_{\mathcal{A}})$ is conflict-free by the definition of acceptability (no element of $G$ defeats another element of $G$, since each defeater is itself defeated within $G$). Admissibility follows since every $A \in G$ is acceptable w.r.t. $G$ by the fixpoint property $F_{\mathcal{A}}(G) = G$. $\square$

## 4. Implications

The strict subsumption result (Theorem 3.2) has direct consequences for AI and Law. Legal arguments inherently carry internal structure: statutes act as strict rules, precedents as defeasible rules, and judicial preferences modulate attack outcomes. Dung AF discards this structure, potentially leading to loss of legally relevant distinctions. For instance, a court's preference for statutory authority over precedent cannot be encoded in a flat Dung AF without pre-selecting the preferred argument.

Theorem 3.3 guarantees that ASPIC+ grounded semantics are well-behaved under standard preference orderings, supporting computational applications in legal decision support systems. The constructive iteration in the proof provides a direct algorithm: compute the grounded extension level by level, adding at each stage all arguments whose defeaters are already defeated.

Future work should investigate: (1) whether ASPIC+ with contraries also strictly subsumes frameworks with collective attacks (SETAFs); (2) the complexity of computing preferred extensions in ASPIC+; and (3) applications to multi-agent legal argumentation where different agents hold different preference orderings.

## References

- Dung, P.M. (1995). On the acceptability of arguments and its fundamental role in nonmonotonic reasoning, logic programming and n-person games. *Artificial Intelligence*, 77(2), 321--358.
- Modgil, S. and Prakken, H. (2013). A general account of argumentation with preferences. *Artificial Intelligence*, 195, 361--397.
- Besnard, P. and Hunter, A. (2008). *Elements of Argumentation*. MIT Press.
- Baroni, P., Caminada, M., and Giacomin, M. (2011). An introduction to argumentation semantics. *Knowledge Engineering Review*, 26(4), 365--410.
- Prakken, H. (2010). An abstract framework for argumentation with structured arguments. *Argument and Computation*, 1(2), 93--124.
- Tarski, A. (1955). A lattice-theoretical fixpoint theorem and its applications. *Pacific Journal of Mathematics*, 5(2), 285--309.
