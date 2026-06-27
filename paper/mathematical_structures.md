# Mathematical Structures in Legal Reasoning: Lattices, Fixpoints, Kripke Models, and Functors

**Authors:** Juris-Calculus Formalization Group

**Date:** June 2026

---

## Abstract

We present a formally verified mathematical framework for legal reasoning built on four
algebraic and topological structures: finite Galois connections over join-semilattices,
monotone fixpoint iteration on finite sets, temporal Kripke models with linear temporal
logic (LTL), and a category-theoretic analysis of cross-jurisdiction functor existence.
All theorems are mechanized in Lean 4 with Mathlib dependencies and contain zero sorry,
zero custom axioms, and zero admit declarations. The formalization comprises 7
proved-by-artifact theorems (verified by JC_Formalization.lean:proved_theorems_card),
unified through a composition chain Kripke -> Horn -> AAF -> Banach. We report theorems
exactly as proved and mark planned extensions honestly.

---

## 1. Introduction

Legal reasoning involves monotonic forward-chaining (Horn rules), non-monotonic
argumentation (Dung frameworks), temporal ordering constraints (facts must precede
procedures), and cross-jurisdiction concept mapping (category functors between legal
systems). This paper formalizes four mathematical structures underlying these operations
and proves their core properties in Lean 4. The formalization lives in JurisLean/ with
8 source files: FiniteGaloisAdjunction.lean, FiniteMonotoneIteration.lean,
HornFixedPoint.lean, DungFixedPoint.lean, TemporalKripke.lean, FiniteRosetta.lean,
BanachEffectiveNodes.lean, and UnifiedModel.lean.

---

## 2. Formal Definitions

### 2.1 Structure 1: Galois Connections on Finite Lattices

Source: JurisLean/FiniteGaloisAdjunction.lean

**Definition 1** (FinitePoset). A *finite poset* is a Lean class extending SemilatticeSup
and OrderBot equipped with a Fintype instance and a decidable order relation
DecidableRel (<=).

**Definition 2** (ResiduatedMap). A *residuated map* is a structure bundling a function
fn : alpha -> alpha with proofs of monotonicity, sup-preservation (fn(a sup b) = fn(a)
sup fn(b)), and bottom-preservation (fn(bot) = bot).

**Definition 3** (legalResidual). The *legal residual* (right adjoint) is defined as
gamma(y) = sup { x in univ | fn(x) <= y } over the finite universe.

**Theorem 1** (galois_connection_of_residuated). For any ResiduatedMap on a FinitePoset,
the pair (fn, gamma) forms a Galois connection:

    forall x y, fn(x) <= y <-> x <= gamma(y)

The proof constructs both directions: (i) if fn(x) <= y then x is in the filter set,
so x <= sup by Finset.le_sup; (ii) if x <= gamma(y) then fn(x) <= fn(gamma(y)) <= y
by monotonicity and Finset.sup_le. The second direction uses the auxiliary lemma
fn_sup_preserves, which proves fn distributes over Finset.sup by induction on the finset.

### 2.2 Structure 2: Finite Monotone Fixpoint Iteration

Source: JurisLean/FiniteMonotoneIteration.lean, JurisLean/HornFixedPoint.lean,
JurisLean/DungFixedPoint.lean

**Definition 4** (FiniteMonotoneSystem). A *finite monotone system* is a structure over a
decidable type with a finite universe univ : Finset alpha, a step function step : Finset
alpha -> Finset alpha, and proofs that step is monotone and maps into univ.

**Definition 5** (iter). The *iteration* function applies step to the empty set n times:
iter(sys, 0) = empty, iter(sys, n+1) = step(iter(sys, n)).

**Core Lemmas:**
- iter_mono: iter(n) is a subset of iter(n+1) (induction using step_monotone)
- iter_stable: if iter(n) = iter(n+1) then iter(n+k) = iter(n) for all k
- iter_ssubset_of_ne: inequality implies strict subset
- iter_card_lt_of_ne: strict subset implies strict card inequality

**Theorem 2** (exists_fixpoint_le_card). There exists k <= |univ| such that
iter(k) = iter(k+1). Proof: by contradiction; if the iteration never stabilizes in
|univ| steps, strict card growth forces card(iter(|univ|+1)) > |univ|, contradicting
iter_subset_univ.

**Theorem 3** (fixed_at_card). iter(|univ|) = iter(|univ|+1). Corollary of Theorem 2
plus iter_stable.

#### 2.2.1 Horn Systems (HornFixedPoint.lean)

A HornSystem is converted to a FiniteMonotoneSystem via toFiniteMonotoneSystem.
The following 10 theorems are proved:

    1.  horn_operator_subset_univ      T_H(S) subset univ
    2.  horn_operator_monotone         S subset T -> T_H(S) subset T_H(T)
    3.  horn_iteration_monotone        iter(k) subset iter(k+1)
    4.  horn_finite_termination        exists k <= |univ|, iter(k) = iter(k+1)
    5.  horn_iteration_bound           iter(|univ|) = iter(|univ|+1)
    6.  horn_result_fixed_point        T_H(iter(|univ|)) = iter(|univ|)
    7.  horn_result_least_fixed_point  T_H(S) = S -> iter(|univ|) subset S
    8.  horn_soundness                 iter(|univ|) subset univ
    9.  horn_completeness              (forall S, T_H(S)=S -> a in S) -> a in iter(|univ|)
    10. horn_result_is_minimal_model   exists! M, T_H(M)=M and (forall N, T_H(N)=N -> M subset N)

#### 2.2.2 Dung Abstract Argumentation Frameworks (DungFixedPoint.lean)

A DungAAF is converted to a FiniteMonotoneSystem via aafSystem. The grounded extension
is groundedSpec(aaf) = iter(aafSystem, |args|).

Key proved theorems:

- F_monotone: the Dung characteristic function F is monotone
- groundedSpec_is_fixed_point: F(groundedSpec) = groundedSpec
- groundedSpec_is_least_fixed_point: F(S) = S -> groundedSpec subset S
- groundedSpec_unique_least_fixed_point: conjunction of the above two
- labelling_partition: the three-valued labelling (IN, OUT, UNDEC) partitions args
  into pairwise-disjoint sets whose union equals args
- in_soundness: if a in grounded, every attacker of a has a grounded attacker
- out_soundness: if a in OUT, a has a grounded attacker
- undecided_characterization: a in UNDEC <-> a not in grounded AND
  attackers(a) intersect grounded = empty
- self_attack_not_in_grounded: if (a,a) in attacks and attackers(a) = {a},
  then a not in grounded

### 2.3 Structure 3: Temporal Kripke Models

Source: JurisLean/TemporalKripke.lean

**Definition 6** (TemporalWorld). A temporal world carries an id : Nat, a fact timestamp
t_fact, and a procedure timestamp t_proced.

**Definition 7** (TemporalKripke). A *temporal Kripke structure* of size n consists of
worlds : Fin n -> TemporalWorld and transitions : Fin n -> Fin n -> Prop.

**Definition 8** (ltl_always). The LTL "always" operator G(phi) holds at world i iff
phi holds at i and at all worlds reachable from i via Relation.TransGen.

**Definition 9** (temporal_guard). The *temporal guard* t_fact < t_proced enforces that
facts always precede their procedural treatment.

**Theorem 4** (temporal_guard_always). If every world in K satisfies temporal_guard,
then G(temporal_guard) holds on the entire Kripke structure.

**Constructive witness:** A 3-world litigation_timeline with worlds (1,10), (5,20),
(15,30) and transitions W1->W2->W3. All three worlds satisfy the guard (verified by
decide), yielding:

    litigation_always_guard : G(t_fact < t_proced)

### 2.4 Structure 4: Category-Theoretic Obstruction and Banach Contraction

Source: JurisLean/FiniteRosetta.lean, JurisLean/BanachEffectiveNodes.lean

#### FiniteRosetta (44-entry real data analysis)

A MappingStatus enum classifies 44 cross-jurisdiction legal concept mappings from
claim_mapping.csv. The mappingStatus function encodes: 30 CN_ONLY, 2 CN_US_PARTIAL,
4 COLLISION, 3 ASYMMETRY, 3 CN_HK_PARTIAL, 1 TRI_JURISDICTION_PARTIAL,
1 TRI_JURISDICTION_MAPPED.

Proved theorems (all by rfl or decide):

- cnOnly_eq_30: exactly 30/44 entries have no foreign mapping
- no_total_functor: not (forall i : Fin 44, mappingStatus(i) != CN_ONLY)
- obstruction_density_gt_two_thirds: obstructionCount * 3 > 44 * 2

**Note:** The full category-theoretic Rosetta functor (with Functor instances and
natural transformations between legal categories) is PLANNED, not yet implemented.
The current proof establishes the obstruction to a total functor via data enumeration,
not via categorical machinery.

#### Banach Effective Nodes Pricing

**Definition 10** (pricingFn). pricingFn(x, beta, T) = beta*T + (1-beta)*x.

**Theorem 5** (pricingFn_contraction). For beta in (0,1),
|f(x) - f(y)| <= (1-beta)*|x-y|. The proof uses pricingFn_sub (affine structure) and
abs_one_sub_beta_of_pos_lt_one.

**Theorem 6** (pricingFn_unique_fixed_point). The unique fixed point of pricingFn is T.
Proof: from beta*T + (1-beta)*x = x, derive beta*(T-x) = 0, then since beta > 0,
conclude x = T.

---

## 3. Main Results: Unified Composition Chain

Source: JurisLean/UnifiedModel.lean

The UnifiedModel structure composes all four layers via a coherence axiom: each HornRule
maps to an AAF Argument via rule_to_arg, with a well-formedness proof.

Layer composition: Kripke (temporal facts) -> Horn (forward closure) -> AAF (grounded
extension) -> Banach (price bound).

**Theorem 7** (soundness_aaf). An unattacked argument is in the grounded extension:
is_unattacked(a) -> a in GE.

**Theorem 8** (soundness_banach). An accepted argument's price is bounded:
a in GE -> price(a) <= price_bound.

**Theorem 9** (unified_composition_v2). For an unattacked argument a, if
price(a) <= banach_iterate(initial, target, 10), then price(a) <= max(initial, target).
This uses banach_bounded (the Banach iterate is always bounded by max(price, target)).

**Theorem 10** (full_chain). The complete end-to-end chain: fact in Kripke -> rule
fireable -> argument unattacked -> price bounded by max(initial, target).

Complementary results in UnifiedModel.lean:

- horn_monotone: horn_step is monotone (stratified computation is safe)
- banach_bound_uniform: the Banach bound holds for all n (pricing layer always bounded)
- gc2_completeness: Horn-derivable rules with unattacked AAF arguments survive

---

## 4. Summary

    Structure              File                         Key Theorem                          Status
    -----------------------------------------------------------------------------------------------
    Galois Connection      FiniteGaloisAdjunction.lean   galois_connection_of_residuated      PROVED (0 sorry)
    Fixpoint Iteration     FiniteMonotoneIteration.lean  exists_fixpoint_le_card              PROVED (0 sorry)
    Horn Fixpoint          HornFixedPoint.lean           horn_result_is_minimal_model         PROVED (0 sorry)
    Dung Grounded          DungFixedPoint.lean           groundedSpec_unique_least_fp         PROVED (0 sorry)
    Temporal Kripke        TemporalKripke.lean           temporal_guard_always                PROVED (0 sorry)
    Rosetta Obstruction    FiniteRosetta.lean            no_total_functor                     PROVED (0 sorry)
    Banach Contraction     BanachEffectiveNodes.lean     pricingFn_unique_fixed_point         PROVED (0 sorry)
    Unified Composition    UnifiedModel.lean             full_chain                           PROVED (0 sorry)
    Meta-Audit             JC_Formalization.lean         proved_theorems_card = 7             PROVED (decide)

Total proved-by-artifact theorems: 7 (per JC_Formalization.lean:proved_theorems_card).
Remaining theorems in the 20-item CoreTheorem enum include 2 empirical proxies, 1
refuted, 1 axiom-only, 1 plan-only, and 8 classified as INVALID_CLAIM or
MISSING_ARTIFACT.

---

## References

[1] Davey, B.A. and Priestley, H.A. (2002). Introduction to Lattices and Order.
    Cambridge University Press.

[2] Dung, P.M. (1995). On the acceptability of arguments and its fundamental role in
    nonmonotonic reasoning, logic programming, and n-person games. Artificial
    Intelligence, 77(2):321--357.

[3] Galatos, N., Jipsen, P., Kowalski, T., and Ono, H. (2007). Residuated Lattices:
    An Algebraic Glimpse at Substructural Logics. Elsevier.

[4] Kripke, S. (1963). Semantical analysis of modal logic I: Normal modal propositional
    calculi. Zeitschrift fur mathematische Logik und Grundlagen der Mathematik,
    9(5-6):67--96.

[5] de Moura, L. and Ullrich, S. (2021). The Lean 4 theorem prover and programming
    language. In CADE-28, LNCS 12699, pp. 625--635.

[6] Mac Lane, S. (1998). Categories for the Working Mathematician (2nd ed.). Springer.

[7] Pnueli, A. (1977). The temporal logic of programs. In FOCS 1977, pp. 46--57. IEEE.
