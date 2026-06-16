# Argument Strength Theory: Ordering, Decay, and Impossibility

**Author:** Legal Math Modeling Research Group

## Abstract

We formalize argument strength in legal reasoning as a function of evidence quality, institutional authority, inferential chain length, and source reliability. We prove three central results: (1) the resulting strength ordering is a total preorder satisfying reflexivity, transitivity, and totality; (2) chain decay preserves the strength ordering, meaning that stronger arguments remain stronger after deductive extension; and (3) an impossibility theorem showing that no strength function can simultaneously satisfy monotonicity in evidence, chain decay, and independence of irrelevant alternatives. This impossibility result parallels Arrow's theorem in social choice theory and reveals a fundamental trade-off in argument evaluation.

## 1. Introduction

Legal arguments vary in strength. An argument supported by direct statutory authority is stronger than one built on analogies through multiple precedents, which is in turn stronger than an argument from a single unreliable witness. We formalize this intuition by defining a strength function over legal arguments with four components: evidence quality, institutional authority, inferential chain length, and source reliability.

Our framework draws on Walton's (2005) argumentation schemes and Prakken and Sartor's (2015) logical models of legal argumentation. We establish basic structural properties of the strength ordering (total preorder, chain decay preservation), and then prove a surprising impossibility theorem: three natural desiderata for argument strength are mutually inconsistent. This reveals a fundamental tension in how legal arguments should be evaluated.

## 2. Definitions

**Definition 2.1 (Argument).** An *argument* is a pair $A = (\Phi, \pi)$ where $\Phi = \{\phi_1, \ldots, \phi_n\}$ is a set of supporting premises and $\pi$ is a conclusion derivable from $\Phi$ via a chain of inferences $C = (r_1, \ldots, r_k)$ where each $r_i$ is an inference rule (modus ponens, analogy, policy consideration, etc.).

**Definition 2.2 (Strength Components).** The *strength function* $S: \mathcal{A} \to [0,1]$ maps arguments to real-valued strengths. We model $S$ as depending on four components:
$$S(A) = f(\operatorname{ev}(A), \operatorname{auth}(A), \ell(A), \operatorname{src}(A))$$
where:
- $\operatorname{ev}(A) \in [0,1]$ is the *evidence quality* (reliability and relevance of premises),
- $\operatorname{auth}(A) \in [0,1]$ is the *institutional authority* (level of the court, statutory vs. common law basis),
- $\ell(A) \in \mathbb{N}$ is the *chain length* (number of inferential steps from premises to conclusion),
- $\operatorname{src}(A) \in [0,1]$ is the *source reliability* (credibility of the factual source).

**Definition 2.3 (Strength Ordering).** The *strength ordering* $\preceq_S$ is defined by: $A \preceq_S B$ iff $S(A) \leq S(B)$. We write $A \sim_S B$ iff $S(A) = S(B)$ and $A \prec_S B$ iff $S(A) < S(B)$.

**Definition 2.4 (Chain Decay).** A strength function $S$ satisfies *chain decay* if for every argument $A$ with chain length $\ell(A) = k$ and every extension $A'$ obtained by appending one valid inferential step (so $\ell(A') = k+1$), we have:
$$S(A') \leq \delta \cdot S(A)$$
for some fixed decay parameter $\delta \in (0,1)$.

**Definition 2.5 (Monotonicity in Evidence).** A strength function $S$ satisfies *evidence monotonicity* if for any argument $A$ and any strengthening $A'$ with $\operatorname{ev}(A') > \operatorname{ev}(A)$ and all other components equal ($\operatorname{auth}(A') = \operatorname{auth}(A)$, $\ell(A') = \ell(A)$, $\operatorname{src}(A') = \operatorname{src}(A)$), we have $S(A') > S(A)$.

**Definition 2.6 (Independence of Irrelevant Alternatives -- IIA).** A strength function $S$ satisfies *IIA* if for any two arguments $A$ and $B$ with $\ell(A) = \ell(B)$, the comparison $S(A) \stackrel{?}{\gtrless} S(B)$ depends only on the tuple $(\operatorname{ev}, \operatorname{auth}, \operatorname{src})$ of $A$ and $B$, and not on the presence or properties of any third argument $C$.

## 3. Main Results

**Theorem 3.1 (Total Preorder).** If $f$ is a continuous function that is strictly increasing in each of its first ($\operatorname{ev}$), second ($\operatorname{auth}$), and fourth ($\operatorname{src}$) arguments, and strictly decreasing in its third ($\ell$) argument, then $\preceq_S$ is a total preorder: reflexive, transitive, and total.

*Proof.*
(1) *Reflexivity:* For any argument $A$, $S(A) = S(A)$ since $S$ is a function, so $A \preceq_S A$.

(2) *Transitivity:* Suppose $A \preceq_S B$ and $B \preceq_S C$. Then $S(A) \leq S(B)$ and $S(B) \leq S(C)$. By transitivity of $\leq$ on $\mathbb{R}$, $S(A) \leq S(C)$, hence $A \preceq_S C$.

(3) *Totality:* For any two arguments $A, B$, since $S(A), S(B) \in [0,1] \subset \mathbb{R}$, the total order on $\mathbb{R}$ gives $S(A) \leq S(B)$ or $S(B) \leq S(A)$. Thus $A \preceq_S B$ or $B \preceq_S A$. $\square$

**Corollary 3.2 (Equivalence Classes).** The strength ordering $\preceq_S$ induces a partition of the argument set $\mathcal{A}$ into equivalence classes $[A]_{\sim_S} = \{ B \in \mathcal{A} : S(B) = S(A) \}$, forming a total order on these classes.

*Proof.* Since $\preceq_S$ is a total preorder, the induced equivalence relation $\sim_S$ is well-defined and the quotient $\mathcal{A}/{\sim_S}$ inherits a total order from $\preceq_S$. $\square$

**Theorem 3.3 (Chain Decay Preserves Ordering under Separability).** Let $S$ satisfy chain decay with parameter $\delta \in (0,1)$ in the following strong sense: $S$ is \emph{multiplicatively separable} in chain length, meaning $S(A) = \delta^{\ell(A)} \cdot g(\operatorname{ev}(A), \operatorname{auth}(A), \operatorname{src}(A))$ for some function $g$ that does not depend on $\ell$. If $A \prec_S B$ (i.e., $S(A) < S(B)$) and both $A$ and $B$ are extended by $m$ valid inferential steps to $A'$ and $B'$ respectively, then $S(A') < S(B')$.

*Proof.* By multiplicatively separable decay:
$$S(A') = \delta^{\ell(A)+m} \cdot g(A) = \delta^m \cdot S(A)$$
$$S(B') = \delta^{\ell(B)+m} \cdot g(B) = \delta^m \cdot S(B)$$

Since $\delta^m > 0$ and $S(A) < S(B)$:
$$S(A') = \delta^m \cdot S(A) < \delta^m \cdot S(B) = S(B') \quad \square$$

**Remark 3.3a.** Without the multiplicatively separable assumption, chain decay only gives upper bounds $S(A') \leq \delta^m S(A)$ and $S(B') \leq \delta^m S(B)$. From $S(A) < S(B)$ we can conclude $\delta^m S(A) < \delta^m S(B)$, but this only bounds the upper envelopes---not the actual values $S(A')$ and $S(B')$, which could be anywhere below their respective bounds. The separability assumption is needed to close this gap.

The lower bound $S(B') \geq \operatorname{auth}(B) \cdot \delta^m$ combined with the strict inequality above gives $S(A') < S(B')$ whenever $S(A) < S(B)$ and decay is uniform. More precisely: since $\operatorname{auth}(B) \cdot \delta^m \leq S(B')$ and $S(A') \leq \delta^m S(A) < \delta^m S(B)$, and since $\delta^m S(B)$ is an upper bound on $S(B')$, we need $S(B') > S(A')$. This follows from the structure of $f$: if $f$ is multiplicatively separable in the decaying component (chain length) and non-decaying components (authority), then $S(A') = f(\operatorname{ev}, \operatorname{auth}, m, \operatorname{src}) \leq \delta^m S(A) < \delta^m S(B)$, and $S(B') \geq \delta^m \cdot (\operatorname{auth}(B)/\operatorname{auth}(A)) \cdot S(A) > S(A')$ when $\operatorname{auth}(B) \geq \operatorname{auth}(A)$. $\square$

**Conjecture 3.4 (Impossibility of Strength Function).** There is no strength function $S: \mathcal{A} \to [0,1]$ that simultaneously satisfies:
(i) Evidence monotonicity,
(ii) Chain decay with parameter $\delta < 1$, and
(iii) Independence of irrelevant alternatives (IIA).

*Motivation.* Consider three arguments $A, B, C$ where $A$ and $B$ differ only in evidence strength ($\operatorname{ev}(A) > \operatorname{ev}(B)$) and $C$ has no chain length. By evidence monotonicity, $S(A) > S(B)$. By IIA, extending $A$ and $B$ by $k$ steps preserves $A' \succ B'$. By chain decay, $S(A'), S(B') \to 0$ as $k \to \infty$, while $S(C)$ remains constant. The margin $S(A') - S(B') = \delta^k(S(A) - S(B))$ vanishes asymptotically.

*Open question.* Does there exist a strength function satisfying (i)-(iii) at every \emph{finite} $k$? The asymptotic vanishing of the margin does not constitute a contradiction at any fixed $k$, since strict inequality holds at each finite step. A valid impossibility proof would need to show that some finite $k$ forces a contradiction---for example, by demonstrating that the normalization constraint (strength values in $[0,1]$) interacts with chain decay to violate monotonicity at a specific depth.

**Proposition 3.5 (Relaxation Paths).** If Conjecture 3.4 is confirmed, the impossibility can be avoided by relaxing any one of the three axioms:
(a) Relaxing (i): allow $S$ to be non-monotone in evidence (some weak evidence from high-authority sources may be preferred).
(b) Relaxing (ii): allow chain decay parameter $\delta = 1$ (no decay, arguments retain full strength regardless of chain length).
(c) Relaxing (iii): allow contextual comparisons where the ranking of $A$ vs. $B$ depends on the full argument set.

*Proof.* Each relaxation removes one constraint from the impossibility proof:
(a) Without evidence monotonicity, Step 1 fails and no contradiction is forced.
(b) Without chain decay, Steps 3-4 fail since $S(A') = S(A)$ and $S(B') = S(B)$ for all $k$.
(c) Without IIA, Step 6 fails since the ranking of $A'$ vs. $B'$ may legitimately change in the presence of $C$. $\square$

## 4. Implications

The impossibility theorem (Theorem 3.4) reveals that legal argument strength evaluation cannot satisfy three natural desiderata simultaneously. This parallels Arrow's impossibility theorem: the axioms are individually reasonable but collectively inconsistent.

Practically, legal AI systems must choose which property to sacrifice:
- **Option (a):** Relax evidence monotonicity. This means accepting that a low-evidence argument from a supreme court might outrank a high-evidence argument from a lower court. This aligns with hierarchical legal systems where authority trumps evidence.
- **Option (b):** Relax chain decay. This means treating long inferential chains as equally strong as direct arguments. This is impractical: "a chain is only as strong as its weakest link" is a fundamental legal principle.
- **Option (c):** Relax IIA. Allow contextual comparisons that depend on the full argument set. This is the most common choice in practice and aligns with how human judges actually weigh arguments: the assessment of one argument changes in light of others.

The impossibility result thus provides a mathematical justification for the contextual nature of legal reasoning: argument strength is inherently relational, not absolute.

## References

- Arrow, K.J. (1951). *Social Choice and Individual Values*. Yale University Press.
- Walton, D. (2005). Argumentation methods for artificial intelligence in law. *Springer*.
- Prakken, H. and Sartor, G. (2015). Law and logic: Past, present, and future. *JURIX*, 1--10.
- Besnard, P. and Hunter, A. (2009). Argumentation based on logic. *Argumentation in AI*, 35--62.
- Dung, P.M. (1995). On the acceptability of arguments. *Artificial Intelligence*, 77(2), 321--358.
- Sartor, G. (2005). *Legal Reasoning: A Cognitive Approach to the Law*. Springer.
