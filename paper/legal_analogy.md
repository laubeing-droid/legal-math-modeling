# A Formal Theory of Legal Analogy: Similarity, Distinguishing, and Computational Complexity

**Authors:** DELI Research Group
**Date:** June 2026
**Artifact:** `legal-math-modeling/theory/analogical_reasoning.py`
         + `proofs/lean/juris_lean/JurisLean/FiniteRosetta.lean`

---

## Abstract

We present a formal computational model of analogical reasoning in legal
case analysis.  A legal case is represented as a triple $C = (F, I, O)$
of material facts, legal issues, and an outcome.  Similarity between
cases is computed as a weighted Jaccard coefficient over facts and issues.
We define analogy strength as a product of similarity, topical relevance,
and institutional authority.  We formalize distinguishing as selection of
a critical fact in the symmetric difference of two case-fact sets.
The Python implementation is executable and tested.  We connect this
framework to a Lean 4 formalization of cross-jurisdiction obstruction:
proved theorems on 44 annotated claim-mapping entries demonstrate that
30/44 Chinese-legal concepts lack foreign equivalents, blocking any
total cross-jurisdiction functor.  The computational complexity of
optimal distinguishing is left as a conjecture (NP-hardness is planned,
not proved).

---

## 1. Introduction

Legal reasoning by analogy is the dominant mode of argument in common-law
jurisdictions [Sunstein 1993, Brewer 1996].  A judge confronting a novel
dispute asks: which prior case is most similar?  Can the opponent
*distinguish* the present case by pointing to a material factual
difference?  These operations -- similarity assessment, analogy strength
ranking, and distinguishing -- are the primitives of case-based legal
argument.

Prior computational models of legal analogy (Ashley 2017, Branting 2000)
treat similarity as a feature of textual or semantic closeness.  We
instead adopt a set-theoretic model grounded in Jaccard similarity,
where facts and issues are discrete, typed elements.  This makes the
model formally verifiable and directly implementable.

We contribute: (1) a Python module `analogical_reasoning.py` with
executable definitions of case similarity, analogy strength, and
distinguishing; (2) a Lean 4 formalization `FiniteRosetta.lean` proving
cross-jurisdiction structural obstruction on real annotated data; and
(3) a claim-status ledger `model_status.py` that honestly distinguishes
proved artifacts from planned work.

---

## 2. Formal Definitions

**Definition 1 (Legal Fact).** A *legal fact* is a triple
$f = (\ell, d, m)$ where $\ell$ is a semantic label, $d \in \{$
`CONTRACT`, `TORT`, `PROPERTY`, `CRIMINAL`, `CONSTITUTIONAL`$\}$ is a
legal domain, and $m \in [0,1]$ is a materiality weight.
Implementation: `LegalFact` dataclass in `analogical_reasoning.py`.

**Definition 2 (Legal Issue).** A *legal issue* $i = (\ell)$ is a
labeled question of law.  Implementation: `LegalIssue`.

**Definition 3 (Case).** A *legal case* is a tuple
$C = (\textit{name}, F, I, O, r, y, j)$ where $F \subseteq$
`LegalFact`, $I \subseteq$ `LegalIssue`, $O$ is a textual outcome,
$r \in \{1,2,3\}$ is the court level (trial/appellate/supreme),
$y$ is the year, and $j$ is the jurisdiction.

**Definition 4 (Similarity).** For cases $C_a, C_b$:

$$\text{sim}(C_a, C_b) = w_f \cdot \frac{|F_a \cap F_b|}{|F_a \cup F_b|}
                        + w_i \cdot \frac{|I_a \cap I_b|}{|I_a \cup I_b|}$$

where $w_f + w_i = 1$ (defaults: $w_f = 0.6$, $w_i = 0.4$).
Each fraction is the Jaccard coefficient on label sets.  When both sets
are empty, Jaccard is defined as 1.0 by convention.

**Definition 5 (Analogy Strength).** The strength of an analogy from
source $C_a$ to target $C_b$ is:

$$\text{strength}(C_a \to C_b)
    = \text{sim}(C_a, C_b) \times \text{relevance}(C_b)
      \times \text{authority}(C_b)$$

where $\text{authority}(C_b) = \frac{\text{court\_level}(C_b)}
         {\max(\text{court\_level}(C_a),\text{court\_level}(C_b),1)}$.
This normalizes authority to $[0,1]$.

**Definition 6 (Distinguishing).** Given cases $C_a, C_b$, the set of
*distinguishing-candidate facts* is the symmetric difference
$F_a \triangle F_b = (F_a \setminus F_b) \cup (F_b \setminus F_a)$.
A critical distinguishing fact $f^*$ is one whose presence or absence
maximally alters the predicted outcome.

---

## 3. Main Results

### 3.1 Executable Similarity Module

The Python module `analogical_reasoning.py` provides an executable
implementation of Definitions 1--6.  The `best_analogy` function
enumerates candidates and returns the one maximizing analogy strength.
`find_distinguishing_facts` computes the symmetric-difference set for
a pair of cases.  The module contains a built-in demo with three
synthetic contract-dispute cases and a query case, confirming that the
Smith v. Jones precedent (appellate, same issues) is correctly ranked
above Green v. Valley Farms (trial, different issues).

### 3.2 Cross-Jurisdiction Obstruction (FiniteRosetta.lean)

**Theorem 1** (`no_total_functor` in `FiniteRosetta.lean`).
*It is not the case that every entry $i : \text{Fin } 44$ in the
claim-mapping data satisfies*
$\texttt{mappingStatus}(i) \neq \texttt{CN\_ONLY}$.
*Proof:* by exhibiting $i = 0$, where $\texttt{mappingStatus}(0) =
\texttt{CN\_ONLY}$, computed by `rfl`.

**Theorem 2** (`cnOnly_eq_30`).
Exactly 30 of the 44 claim-mapping entries have status `CN_ONLY`.
*Proof:* `rfl` (definitional equality on the `mappingStatus` function).

**Theorem 3** (`collision_eq_4`, `asymmetry_eq_3`, `obstruction_eq_37`).
4 entries are `COLLISION`, 3 are `ASYMMETRY`, and
$30 + 4 + 3 = 37$ total entries are "obstructed" (lack a usable foreign
mapping).  Proved by `rfl`.

**Theorem 4** (`obstruction_density_gt_two_thirds`).
$37 \times 3 > 44 \times 2$, i.e. the obstruction density exceeds $2/3$
(approximately 84%).  *Proof:* `by decide`.

These theorems are classified as `PROVED_BY_ARTIFACT` with evidence type
`FINITE_EXHAUST` in `JC_Formalization.lean` (theorem `T16_CategoryRosetta`).
The data source is `data/category_rosetta/claim_mapping.csv`, containing
44 expert-annotated cross-jurisdiction claim-mapping patterns across
Chinese, US, and Hong Kong law.

**Scope limitation.** Per the evidence-calibrated claim ledger
(`model_status.py`, claim `A1_REAL_ROSETTA`): the data supports
collision and asymmetry *witnesses* but does not prove a *universal*
no-functor theorem for all real legal facts.  The forbidden claim is:
"No total natural transformation has been formally proved for all real
legal facts."

### 3.3 Case Retrieval and Precedent Reasoning

The codebase includes two companion modules.  `case_retrieval.py`
implements a multi-factor relevance score combining issue overlap, fact
overlap, jurisdiction match, and recency, with authority-weighted
re-ranking.  `precedent_reasoning.py` defines four precedent actions --
`FOLLOW`, `DISTINGUISH`, `OVERRULE`, `CREATE` -- with binding strength
as a function of authority and factual divergence.  These modules
compose with `analogical_reasoning.py`: similarity feeds into retrieval,
and distinguishing facts feed into the `DISTINGUISH` action.

### 3.4 Conjecture: Computational Complexity of Distinguishing

The problem of finding an *optimal* distinguishing fact $f^*$ that
maximally alters outcome prediction, over all subsets of the symmetric
difference, is *conjectured* to be NP-hard by reduction from
set-cover.  **This is PLANNED WORK, not a proved result.**  The current
implementation enumerates candidates and returns the full symmetric
difference; an optimization-based distinguishing search is future work.

---

## 4. Discussion

Our set-theoretic approach has three advantages: (1) the similarity
function is symmetric, bounded in $[0,1]$, and computable in polynomial
time; (2) the Lean formalization provides machine-checked proofs on
real annotated data, avoiding the pitfall of toy-only validation; (3)
the claim ledger (`model_status.py`) enforces honest scope boundaries,
preventing over-generalization from a 44-entry sample to universal
claims.

The 84% obstruction density across Chinese-US-HK claim mappings has
practical implications: cross-jurisdiction legal analogy cannot be
treated as a simple similarity lookup.  Systems must include
jurisdiction guards and obstruction flags, as implemented in
`jurisdiction_guard.py`.

---

## 5. References

- Ashley, K.D. *Artificial Intelligence and Legal Analytics* (2017).
- Brewer, S. "Exemplary Reasoning." *Harvard Law Review* 109 (1996).
- Branting, L.K. *Reasoning with Rules and Precedents* (2000).
- Dung, P.M. "On the Acceptability of Arguments." *Fundamenta
  Informaticae* 27 (1995).
- Jaccard, P. "Nouvelles recherches sur la distribution florale."
  *Bulletin de la Societe Vaudoise des Sciences Naturelles* 38 (1912).
- Sunstein, C.R. "On Analogical Reasoning." *Harvard Law Review*
  106 (1993).
- Zhong, H. et al. "Legal Case Retrieval: A Survey." *ACM Computing
  Surveys* (2020).

---

**Source files.**
`theory/analogical_reasoning.py` (Python, executable);
`proofs/lean/juris_lean/JurisLean/FiniteRosetta.lean` (Lean 4, machine-checked);
`proofs/lean/juris_lean/JurisLean/JC_Formalization.lean` (Lean 4, theorem metadata);
`theory/model_status.py` (Python, evidence ledger);
`theory/case_retrieval.py` (Python, retrieval);
`theory/precedent_reasoning.py` (Python, precedent actions);
`data/category_rosetta/claim_mapping.csv` (44-entry annotated dataset).
