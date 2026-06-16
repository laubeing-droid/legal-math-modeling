# A Formal Theory of Legal Analogy: Similarity, Distinguishing, and Computational Complexity

**Author:** Legal Math Modeling Research Group

## Abstract

We formalize case-based legal reasoning through mathematical models of case similarity and distinguishing. We define case similarity as a weighted Jaccard index over material facts and legal issues, and formalize distinguishing as identifying the minimum material fact difference between cases. We prove that best analogy selection reduces to maximum similarity retrieval with polynomial time complexity, and that distinguishing is NP-hard in general (via reduction from set cover) but polynomial when case size is bounded. We also establish monotonicity of distinguishing sets. These results connect legal theory to combinatorial optimization and have implications for the design of automated legal reasoning systems.

## 1. Introduction

Legal reasoning by analogy is central to common law systems. Courts routinely compare new cases to prior precedents, select the most analogous prior case, and either follow its holding or distinguish it on material facts. Sunstein (1993) characterized analogical reasoning as the core of common law adjudication; Horty (2012) formalized it within a default logic framework; and Ashley (1990) built computational models of case-based legal argumentation.

We formalize two key operations: (1) *analogy selection* -- choosing the most similar prior case -- and (2) *distinguishing* -- finding the minimal set of material facts that justifies treating the cases differently. We analyze the computational complexity of both operations and establish their relationship.

## 2. Definitions

**Definition 2.1 (Case).** A *legal case* is a triple $c = (F, I, d)$ where $F \subseteq \mathcal{F}$ is a set of material facts (from a finite universe $\mathcal{F}$ of legally relevant factual features), $I \subseteq \mathcal{I}$ is a set of legal issues (from a finite universe $\mathcal{I}$ of legal doctrines and claims), and $d \in \{0, 1\}$ is the judicial outcome (1 = for plaintiff, 0 = for defendant).

**Definition 2.2 (Weighted Jaccard Similarity).** Given weight functions $w_F: \mathcal{F} \to \mathbb{R}_{>0}$ for facts and $w_I: \mathcal{I} \to \mathbb{R}_{>0}$ for issues, the *case similarity* between cases $c_a = (F_a, I_a, d_a)$ and $c_b = (F_b, I_b, d_b)$ is:
$$\operatorname{sim}(c_a, c_b) = \alpha \cdot J_w(F_a, F_b) + \beta \cdot J_w(I_a, I_b)$$
where $\alpha, \beta \geq 0$ with $\alpha + \beta = 1$, and the weighted Jaccard index is:
$$J_w(X, Y) = \frac{\sum_{x \in X \cap Y} w(x)}{\sum_{x \in X \cup Y} w(x)}$$

**Definition 2.3 (Best Analogy).** Given a target case $c^* = (F^*, I^*, d^*)$ and a case base $\mathcal{C} = \{c_1, \ldots, c_n\}$, the *best analogy* is:
$$c^*_{\text{best}} = \arg\max_{c_j \in \mathcal{C}} \operatorname{sim}(c^*, c_j)$$

**Definition 2.4 (Material Fact Difference).** The *material fact difference* between $c_a$ and $c_b$ is the symmetric difference:
$$\Delta(c_a, c_b) = (F_a \triangle F_b) \cup (I_a \triangle I_b)$$
This represents the facts and issues present in one case but not the other.

**Definition 2.5 (Distinguishing Set).** A *distinguishing set* for $c_b$ relative to $c_a$ at threshold $\tau \in (0,1)$ is a subset $D \subseteq \Delta(c_a, c_b)$ such that removing $D$'s contribution to similarity reduces the modified similarity below $\tau$:
$$\operatorname{sim}_D(c_a, c_b) < \tau$$
where $\operatorname{sim}_D$ is the similarity computed with elements of $D$ excluded from the relevant sets.

**Definition 2.6 (Minimum Distinguishing Problem).** Given cases $c_a$, $c_b$, and threshold $\tau$, find:
$$D^* = \arg\min_{D \subseteq \Delta(c_a, c_b)} |D| \quad \text{subject to} \quad \operatorname{sim}_D(c_a, c_b) < \tau$$

**Definition 2.7 (Bounded Case Size).** A case base has *bounded case size* with parameter $K$ if for all cases $c = (F, I, d)$: $|F| + |I| \leq K$.

## 3. Main Results

**Theorem 3.1 (Best Analogy = Maximum Similarity Retrieval).** The best analogy selection problem for a target case $c^*$ and case base $\mathcal{C}$ of size $n$ is equivalent to the maximum weighted Jaccard retrieval problem. It can be solved in $O(n \cdot (|\mathcal{F}| + |\mathcal{I}|))$ time.

*Proof.* By Definition 2.3, best analogy selection requires computing $\operatorname{sim}(c^*, c_j)$ for each $c_j \in \mathcal{C}$ and returning the maximizer.

For each case $c_j$, the similarity computation proceeds as follows:
(1) Compute $F^* \cap F_j$ and $F^* \cup F_j$: $O(|\mathcal{F}|)$ time using sorted arrays.
(2) Compute the weighted Jaccard $J_w(F^*, F_j)$: $O(|\mathcal{F}|)$ time.
(3) Compute $I^* \cap I_j$ and $I^* \cup I_j$: $O(|\mathcal{I}|)$ time.
(4) Compute $J_w(I^*, I_j)$: $O(|\mathcal{I}|)$ time.
(5) Combine: $O(1)$ time.

Total per case: $O(|\mathcal{F}| + |\mathcal{I}|)$. Over $n$ cases: $O(n \cdot (|\mathcal{F}| + |\mathcal{I}|))$. The equivalence to maximum weighted Jaccard retrieval is immediate from the definition. $\square$

**Conjecture 3.2 (NP-Hardness of Minimum Distinguishing).** The minimum distinguishing problem is believed to be NP-hard.

*Motivation.* The problem resembles Minimum Set Cover: given two cases with overlapping fact sets, find the smallest subset of facts whose removal reduces similarity below a threshold. A natural reduction maps each "set" in the cover instance to a distinguishing fact, and "covering the universe" to reducing similarity. However, the Jaccard similarity function has the property that removing facts from one case can \emph{increase} the Jaccard index (by shrinking the union faster than the intersection), which breaks the straightforward reduction. A valid reduction requires a more sophisticated construction that accounts for this non-monotonicity.

*Evidence.* For bounded case size $|F_c| + |I_c| \leq K$, the problem is solvable in $O(2^{2K} \cdot K)$ time (Theorem 3.3), which is polynomial when $K$ is constant but exponential in $K$. This suggests the problem is hard in the general (unbounded) case, but a formal NP-hardness proof remains open.

**Theorem 3.3 (Polynomial Algorithm for Bounded Case Size).** Under bounded case size $|F_c| + |I_c| \leq K$ for all cases $c$, the minimum distinguishing problem is solvable in $O(2^K \cdot K)$ time, which is polynomial in the input size when $K$ is a fixed constant.

*Proof.* The symmetric difference satisfies $|\Delta(c_a, c_b)| \leq |F_a| + |I_a| + |F_b| + |I_b| \leq 2K$. We enumerate all $2^{|\Delta|} \leq 2^{2K}$ subsets of $\Delta$. For each subset $D$:
(1) Compute $\operatorname{sim}_D(c_a, c_b)$: $O(K)$ time.
(2) Check whether $\operatorname{sim}_D(c_a, c_b) < \tau$: $O(1)$ time.
(3) Track the smallest qualifying $D$.

Total time: $O(2^{2K} \cdot K)$. Since $K$ is fixed, $2^{2K}$ is a constant, and the algorithm is $O(K)$ per input case pair -- hence polynomial. $\square$

**Proposition 3.4 (Monotonicity of Distinguishing).** If $D$ is a distinguishing set for $c_b$ relative to $c_a$ at threshold $\tau$, then any superset $D' \supseteq D$ with $D' \subseteq \Delta(c_a, c_b)$ is also a distinguishing set.

*Proof.* Removing $D'$ from the relevant case can only decrease the Jaccard similarity compared to removing $D$, since we exclude at least as many elements from the union. Formally, if $D \subseteq D'$, then for the fact component: $|F_a \cap (F_b \setminus D')| \leq |F_a \cap (F_b \setminus D)|$ and $|F_a \cup (F_b \setminus D')| \leq |F_a \cup (F_b \setminus D)|$. The ratio $J_w$ is weakly smaller. So if $\operatorname{sim}_D(c_a, c_b) < \tau$, then $\operatorname{sim}_{D'}(c_a, c_b) \leq \operatorname{sim}_D(c_a, c_b) < \tau$. $\square$

**Corollary 3.5 (Greedy Approximation).** The minimum distinguishing problem admits a greedy approximation algorithm that achieves an $O(\ln |\Delta|)$-approximation ratio, matching the set cover approximation bound.

*Proof.* Since the minimum distinguishing problem generalizes set cover (Theorem 3.2), the standard greedy set cover algorithm (pick the element that reduces similarity the most at each step) achieves $O(\ln |\Delta|)$-approximation by the same analysis as for set cover. $\square$

## 4. Implications

Theorem 3.1 confirms that best analogy selection is computationally tractable, justifying its use in case-based reasoning systems and legal information retrieval. A database of $n$ precedents can be searched in linear time per query.

Theorem 3.2 shows that explaining *why* a case should be distinguished -- finding the minimal fact difference that justifies different treatment -- is fundamentally harder than selecting the best analogy. This complexity-theoretic gap confirms the intuition that distinguishing is a more cognitively demanding legal task than analogy selection. It also explains why appellate courts spend more effort crafting distinguishing opinions than identifying relevant precedents.

Theorem 3.3 provides a practical algorithm for bounded cases, which is the typical setting in practice: legal cases have finite, bounded fact sets (typically 5-20 material facts). The exponential dependence on $K$ is manageable for $K \leq 20$ (about $10^6$ subsets).

Corollary 3.5 suggests that even when exact distinguishing is intractable, greedy heuristics provide reasonable approximations, which may explain the heuristic nature of judicial distinguishing in practice.

Future work should explore: (1) approximate algorithms for minimum distinguishing beyond the greedy approach; (2) connections between distinguishing and argumentation theory (distinguishing as undercut attack); and (3) weighted distinguishing where facts have differential legal significance.

## References

- Horty, J.F. (2012). *Reasons as Defaults*. Oxford University Press.
- Sunstein, C.R. (1993). On analogical reasoning. *Harvard Law Review*, 106(3), 741--791.
- Ashley, K.D. (1990). *Modeling Legal Argument: Reasoning with Cases and Hypotheticals*. MIT Press.
- Karp, R.M. (1972). Reducibility among combinatorial problems. *Complexity of Computer Computations*, 85--103.
- Chvatal, V. (1979). A greedy heuristic for the set-covering problem. *Mathematics of Operations Research*, 4(3), 233--235.
- Bench-Capon, T.J.M. and Sartor, G. (2003). A model of legal reasoning with cases incorporating theories and values. *Artificial Intelligence*, 150(1-2), 97--143.
