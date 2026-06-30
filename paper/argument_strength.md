# Argument Strength Theory: Ordering, Decay, and Impossibility

**Legal Math Modeling Research Group**

## Abstract

We formalize legal argument strength as a weighted linear function of four
components: evidence credibility, rule authority, inferential chain length
(with exponential decay), and source reliability. The strength function
defines a total preorder on arguments. We connect this quantitative ordering
to Dung's abstract argumentation framework (AAF), where the grounded
extension acts as a qualitative filter: arguments surviving attack in the
least fixed point of the characteristic function are exactly those defended
against all attackers. Evidence credibility itself is axiomatized as a
multiplicative model S(e) = r x i x a (relevance, integrity, admissibility),
for which we prove the zero property, the sub-minimum bound, and a
generalized Cobb-Douglas extension. We state a planned impossibility result:
no strength function can simultaneously satisfy monotonicity in evidence,
chain decay preservation, and independence of irrelevant alternatives.

## 1. Introduction

Legal arguments vary in strength. A negligence claim supported by expert
testimony and medical records is stronger than one resting on a single
deposition. We model this intuition with a four-component strength function
implemented in Python, then connect it to Dung's AAF formalized in Lean 4
(Mathlib-backed, zero sorry/axiom). The connection is that the grounded
extension, computed as the least fixed point of a monotone characteristic
function, provides a binary acceptability verdict, while the strength
ordering provides a continuous ranking among accepted arguments.

## 2. Formal Definitions

**Definition 2.1 (Argument).** A *legal argument* is a tuple
A = (name, conclusion, E, R, d) where E is a multiset of evidence items,
R is a multiset of defeasible rule references, and d in N is the proof
chain depth (leaf = 0). Source: `LegalArgument` dataclass in
`argument_strength_ordering.py`.

**Definition 2.2 (Evidence).** Each evidence item e in E is a triple
e = (name, credibility, source_reliability) with credibility and
source_reliability in [0, 1].

**Definition 2.3 (Strength Weights).** A weight vector
w = (w_1, w_2, w_3, w_4) with w_i >= 0 and sum = 1, plus a decay
parameter c in (0, 1]. The code defaults are
w = (0.35, 0.25, 0.15, 0.25), c = 0.9.

**Definition 2.4 (Strength Function).** The strength of argument A is:

    S(A) = w_1 * ev(A) + w_2 * ra(A) + w_3 * cl(A) + w_4 * sr(A)

where:
- ev(A) = avg credibility over E (1.0 if E is empty)
- ra(A) = avg authority over R (1.0 if R is empty)
- cl(A) = c^d (exponential chain decay)
- sr(A) = avg source_reliability over E (1.0 if E is empty)

Source: `compute_strength()` in `argument_strength_ordering.py`.

**Definition 2.5 (Strength Ordering).** A <= B iff S(A) <= S(B).
The `compare()` function returns -1, 0, or +1. The `rank_arguments()`
function sorts by strength descending.

**Definition 2.6 (Dung AAF).** A Dung abstract argumentation framework
is a pair (Args, Attacks) where Args is a finite set of arguments and
Attacks is a binary relation over Args. In the Lean formalization
(`DungDefinitions.lean`):

    structure DungAAF where
      args    : Finset Arg
      attacks : Finset (Arg x Arg)

The characteristic function F is:

    F(S) = { a in Args | forall b in attackers(a), attackers(b) intersect S is nonempty }

An argument is *acceptable* w.r.t. S if all its attackers are defeated by S.
The AAF system is instantiated as a `FiniteMonotoneSystem` (`DungDefinitions.lean`, line 35).

**Definition 2.7 (Grounded Extension).** The grounded extension GE is the
least fixed point of F, computed by iterating F from the empty set:

    groundedSpec(aaf) = iter F |Args| starting from empty

Source: `groundedSpec` in `DungFixedPoint.lean`, line 19.

**Definition 2.8 (Evidence Credibility).** For a piece of evidence e,
credibility is S(e) = r x i x a where r = relevance, i = integrity,
a = admissibility, each in [0, 1]. Source: `evidence_credibility_axioms.py`.

## 3. Main Results

### 3.1 Strength Ordering Properties

**Theorem 3.1 (Total Preorder).** The strength ordering <= is a total
preorder on legal arguments: reflexive, transitive, and total.

*Proof.* S maps to [0,1] subset R. Reflexivity: S(A) = S(A). Transitivity:
S(A) <= S(B) and S(B) <= S(C) implies S(A) <= S(C) by transitivity of <= on R.
Totality: for any A, B, either S(A) <= S(B) or S(B) <= S(A) by totality
of R. QED

**Theorem 3.2 (Chain Decay Preserves Ordering under Separability).**
Suppose S is multiplicatively separable in chain depth:
S(A) = c^d * g(ev, ra, sr). If S(A) < S(B) and both are extended by m
valid inferential steps, then S(A') < S(B').

*Proof.* S(A') = c^(d_A + m) * g(A) = c^m * S(A) and similarly S(B') = c^m * S(B).
Since c^m > 0 and S(A) < S(B), we have c^m * S(A) < c^m * S(B). QED

*Remark.* This holds because the decay factor c^d multiplies uniformly.
The default strength function in the codebase has this separable structure.

### 3.2 Dung AAF: Grounded Extension Theorems

All theorems below are proved in Lean 4 with zero sorry and zero
project-defined axioms,
backed by the `FiniteMonotoneSystem` kernel (`FiniteMonotoneIteration.lean`).

**Theorem 3.3 (F is monotone).** If S subseteq T then F(S) subseteq F(T).
Source: `F_monotone` in `DungFixedPoint.lean`, line 44.

**Theorem 3.4 (Grounded Extension is a fixed point).**
F(aaf, groundedSpec(aaf)) = groundedSpec(aaf).
Source: `groundedSpec_is_fixed_point` in `DungFixedPoint.lean`, line 64.

**Theorem 3.5 (Grounded Extension is the least fixed point).**
For any S with F(S) = S, groundedSpec(aaf) subseteq S.
Source: `groundedSpec_is_least_fixed_point` in `DungFixedPoint.lean`, line 74.

**Theorem 3.6 (In-soundness).** If a is in the grounded extension, then
every attacker of a is defeated by the grounded extension.
Source: `in_soundness` in `DungFixedPoint.lean`, line 154.

**Theorem 3.7 (Out-soundness).** If a is labeled OUT, then a has an
attacker in the grounded extension.
Source: `out_soundness` in `DungFixedPoint.lean`, line 163.

**Theorem 3.8 (Undecided characterization).** An argument a in Args is
UNDEC iff a is not in GE and no attacker of a is in GE.
Source: `undecided_characterization` in `DungFixedPoint.lean`, line 169.

**Theorem 3.9 (Self-attack exclusion).** If (a, a) is in Attacks and
attackers(a) = {a}, then a is not in the grounded extension.
Source: `self_attack_not_in_grounded` in `DungFixedPoint.lean`, line 222.

**Theorem 3.10 (Labelling partition).** The three sets (IN, OUT, UNDEC)
are pairwise disjoint and their union is Args.
Source: `labelling_partition` in `DungFixedPoint.lean`, line 104.

**Theorem 3.11 (Finite termination).** The grounded extension computation
terminates within |Args| iterations.
Source: `finite_termination` in `DungFixedPoint.lean`, line 56.

### 3.3 Unified Model: Soundness Chain

**Theorem 3.12 (Unattacked arguments survive).** If a is unattacked in
the AAF, then a is in the grounded extension (both the filter-based
definition and the LFP-based definition).
Source: `soundness_aaf` and `unattacked_in_lfp` in `UnifiedModel.lean`.

**Theorem 3.13 (Banach pricing bound).** For any argument a in the
grounded extension, if the price function is bounded by the Banach iterate,
then price(a) <= max(initial, target).
Source: `unified_composition_v2` in `UnifiedModel.lean`, line 309.

**Theorem 3.14 (Horn monotonicity).** The Horn forward-chaining step is
monotone: F subseteq G implies horn_step(F) subseteq horn_step(G).
Source: `horn_step_mono` in `UnifiedModel.lean`, line 78.

### 3.4 Evidence Credibility

**Theorem 3.15 (Multiplicative Zero Property).** If any dimension
r, i, a equals 0, then S(e) = 0. This captures the legal principle
that a single fatal defect (inadmissibility, broken chain of custody,
or irrelevance) destroys evidentiary value.
Source: `prove_zero_property` in `evidence_credibility_axioms.py`.

**Theorem 3.16 (Sub-minimum Bound).** S_multiplicative(e) <= min(r, i, a).
The multiplicative model is stricter than the additive model
S_additive(e) = (r + i + a) / 3.
Source: `prove_subminimum_bound` in `evidence_credibility_axioms.py`.

**Theorem 3.17 (Generalized Cobb-Douglas).** The credibility model
generalizes to S(e) = r^{w_r} x i^{w_i} x a^{w_a} with w_r + w_i + w_a = 1.
In the log domain, ln S = w_r ln r + w_i ln i + w_a ln a, enabling OLS
estimation of weights from annotated credibility judgments.
Source: `prove_generalized_form` in `evidence_credibility_axioms.py`.

### 3.5 Impossibility Result (Planned)

**Conjecture 3.18 (Strength Function Impossibility).** There is no
strength function S: A -> [0,1] that simultaneously satisfies:
(i) Monotonicity in evidence: higher evidence implies higher strength;
(ii) Chain decay preservation: extending an argument weakens it by at least
     a factor c < 1;
(iii) Independence of irrelevant alternatives (IIA): the comparison of
      A and B depends only on their own components, not on any third argument.

*Status.* This conjecture is PLANNED. The theorem statement is specified
but the proof has not been completed in Lean or Python. The structure
mirrors Arrow's impossibility theorem in social choice theory.

*Sketch of intended approach.* The proof constructs three arguments
A, B, C forming a configuration where (i) forces S(A) > S(B),
(iii) preserves this ranking across extensions, and (ii) drives both
scores toward zero as chain depth grows. The normalization constraint
S in [0,1] combined with the vanishing margin creates a contradiction
at a finite depth. Formal verification is pending.

## 4. Connection to ASPIC+

The ASPIC+ framework (`aspic_plus_framework.py`) extends Dung's AAF with
structured arguments, three attack types (undercut, rebutter, underminer),
and a preference-based defeat relation. An attack becomes a defeat only if
the attacker is not strictly weaker than the attacked argument (by rule
authority). The grounded labeling algorithm in `ASPICFramework.compute_grounded_labeling()`
iterates to a fixed point, assigning IN, OUT, or UNDEC to each argument.
This connects to our strength ordering: the preference check in defeat
resolution uses rule authority, which is one of the four components of S(A).

## 5. References

1. Dung, P.M. (1995). On the acceptability of arguments. *Artificial Intelligence*, 77(2), 321--358.
2. Caminada, M. and Amgoud, L. (2007). On the evaluation of argumentation formalisms. *Artificial Intelligence*, 171(5--6), 286--310.
3. Modgil, S. and Prakken, H. (2013). A general account of argumentation with preferences. *Artificial Intelligence*, 195, 361--397.
4. Arrow, K.J. (1951). *Social Choice and Individual Values*. Yale University Press.
5. Walton, D. (2005). Argumentation methods for artificial intelligence in law. Springer.
6. Prakken, H. and Sartor, G. (2015). Law and logic: Past, present, and future. *JURIX*, 1--10.

## Appendix: Source File Index

| Component | File | Language |
|---|---|---|
| Strength ordering | `theory/argument_strength_ordering.py` | Python |
| Evidence credibility | `theory/evidence_credibility_axioms.py` | Python |
| ASPIC+ framework | `theory/aspic_plus_framework.py` | Python |
| Finite monotone kernel | `JurisLean/FiniteMonotoneIteration.lean` | Lean 4 |
| Dung AAF definitions | `JurisLean/DungDefinitions.lean` | Lean 4 |
| Dung fixed-point proofs | `JurisLean/DungFixedPoint.lean` | Lean 4 |
| Unified model | `JurisLean/UnifiedModel.lean` | Lean 4 |
| AAF exhaustive proof (n<=4) | `p1e_aaf/aaf_grounded_extension_proof.py` | Python |
| Non-monotone counterexample | `p1e_aaf/evaluator_nonmonotone_counterexample.py` | Python |
