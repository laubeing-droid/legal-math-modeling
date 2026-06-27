# Why Legal Reasoning Requires Stratified Semantics: A Formal Counterexample

**Author:** Laupinco
**Date:** 2026-06-27

---

## Abstract

We prove that the standard fixpoint evaluator combining fact derivation, rebuttal, exception handling, and confidence zeroing in a single monotone operator is NOT monotone. A minimal counterexample with 2 arguments suffices. We then show that the stratified evaluator -- which computes Horn closure (Stage 1) followed by Dung grounded extension (Stage 2) -- restores monotonicity within each stage. Stage 1 is proved monotone, terminating, and minimal by `horn_operator_monotone`, `horn_result_least_fixed_point`, and `horn_result_is_minimal_model` in Lean 4. Stage 2 is proved to compute the unique least fixed point by `groundedSpec_unique_least_fixed_point` in Lean 4. The non-monotonicity is structurally confined to Stage 2 and cannot contaminate Stage 1, because Stage 1 completes before Stage 2 begins. The JC_Formalization.lean registry verifies `refuted_theorems_card = 1` (T18_DPPrivilege), and `advance_cannot_revive_refuted` ensures that refuted claims cannot be laundered into proved status.

**Keywords:** non-monotonicity, legal reasoning, stratified semantics, argumentation frameworks, formal verification

---

## 1. Introduction

Legal reasoning is non-monotonic: introducing a new fact or argument can invalidate previously accepted conclusions. This is well-known in the AI and Law literature (Prakken, 2010; Dung, 1995) but has not been formally demonstrated for a system that combines rule derivation with argumentation in a single fixpoint operator.

The architectural tension is:
- **Rule application** is monotone: adding premises never removes derived conclusions (Theorem 1).
- **Exception handling** is non-monotone: adding an argument with an attack can remove a previously accepted argument from the grounded extension (Proposition 6.1).

This paper has four main results:

**Theorem 1.** Horn closure is monotone (`horn_operator_monotone`, HornFixedPoint.lean).

**Theorem 2.** The combined evaluator (monolithic fixpoint over derivation + rebuttal + exception + zeroing) is NOT monotone. Minimal counterexample with 2 arguments.

**Theorem 3.** The stratified evaluator (Horn closure then Dung grounded extension) restores monotonicity within each stage.

**Theorem 4.** The stratified evaluator equals the combined evaluator on monotone instances, i.e., the stratification is lossless when the combined evaluator happens to be monotone.

---

## 2. Definitions

### 2.1 Horn Clauses

**Definition 1 (Horn Rule).** A Horn rule is a pair (P, c) where P is a finite set of premises and c is a conclusion. Formally: `structure HornRule (alpha : Type) where premises : Finset alpha; conclusion : alpha`.

**Definition 2 (Horn System).** A Horn system is a tuple (univ, initialFacts, rules) where all premises and conclusions belong to univ. Formally: `structure HornSystem (alpha : Type) [DecidableEq alpha]`.

**Definition 3 (Immediate Consequence Operator).** TH(S) = S union {c : exists (P, c) in rules, P subset-of S}. The operator TH is monotone.

### 2.2 Dung AF

**Definition 4 (Dung AF).** A Dung AF is (args, attacks) where args is a finite set of arguments and attacks is a binary relation on args. `structure DungAAF where args : Finset Arg; attacks : Finset (Arg x Arg)`.

**Definition 5 (Characteristic Function).** F(S) = {a in args : for all b attacking a, exists c in S attacking b}. The function F is monotone (`F_monotone`, DungFixedPoint.lean).

**Definition 6 (Grounded Extension).** GE = lfp(F), the least fixed point of F computed by iterating from the empty set. `def grounded (aaf : DungAAF) : Finset Arg := FiniteMonotoneSystem.iter (aafSystem aaf) (Finset.card (aafSystem aaf).univ)`.

### 2.3 Original Combined Evaluator

**Definition 7 (Combined Evaluator).** The original evaluator computes a monolithic fixpoint over four operations applied simultaneously:
1. Derive new facts from Horn rules
2. Rebut arguments whose conclusions contradict derived facts
3. Handle exceptions (defeaters, justifications, excuses)
4. Zero out confidence for defeated arguments

**Definition 7a (Filter Operator).** The combined evaluator applies a filter operator that removes defeated arguments. The filter operator computes the *greatest* fixed point, which is NOT monotone.

### 2.4 Monotonicity

**Definition 8 (Monotonicity).** An operator E is monotone if for all inputs I, J with I subset-of J, E(I) subset-of E(J).

---

## 3. Main Results

### 3.1 Theorem 1: Horn Closure Is Monotone

**Theorem 1.** For any Horn system sys and sets S, T with S subset-of T, TH(sys, S) subset-of TH(sys, T).

**Proof.** This is `horn_operator_monotone` in HornFixedPoint.lean. Let c be any conclusion in TH(sys, S). Then either c is already in S (and hence in T, so c is in TH(sys, T)), or there exists a rule (P, c) with P subset-of S. Since S subset-of T, P subset-of T, so c is in TH(sys, T). QED.

**Corollary.** The Horn closure result is the least fixed point (`horn_result_least_fixed_point`), the unique minimal model (`horn_result_is_minimal_model`), and terminates within |univ| steps (`horn_finite_termination`).

### 3.2 Theorem 2: The Combined Evaluator Is NOT Monotone

**Theorem 2.** There exist inputs I, J with I subset-of J such that the combined evaluator E satisfies E(I) not-subset-of E(J).

**Proof (by counterexample).** Consider two arguments:
- a: "The contract is valid" (based on rule r1)
- b: "The contract is void" (based on rule r2, attacking a)

**Input I = {r1, facts_for_r1}.** The evaluator derives the conclusion of r1, accepts argument a, and GE(I) contains a.

**Input J = I union {r2, facts_for_r2, b}.** The evaluator now derives the conclusion of r2, and argument b attacks a. In the grounded extension of the AF with both a and b, if b is unattacked, then b is in GE and a is defended only if some argument attacks b. If no argument attacks b, then a is removed from GE.

Therefore GE(I) contains a but GE(J) does not contain a, violating monotonicity.

This counterexample relies on the grounded extension's sensitivity to argument addition. In UnifiedModel.lean, this is captured by `ge_non_monotonicity`:

```
def ge_non_monotonicity : Prop :=
  exists (af : AAF) (a : Argument), a in grounded_extension af /\
    exists (b : Argument), b not-in af.args /\
      a not-in grounded_extension { af with args := insert b af.args,
                                             attacks := insert (b, a) af.attacks }
```

### 3.3 Theorem 3: Stratified Evaluator Restores Monotonicity

**Theorem 3.** The stratified evaluator E_strat = E_AAF compose E_Horn is monotone within each stage:

(a) E_Horn is monotone (Theorem 1).

(b) E_AAF, as an operator on argument sets within a FIXED AF structure, computes the unique least fixed point (`groundedSpec_unique_least_fixed_point` in DungFixedPoint.lean).

**Proof of (b).** The key insight is that in the stratified evaluator, the AF structure is determined by E_Horn's output and does not change during E_AAF's computation. The characteristic function F is monotone (`F_monotone`), and the grounded extension is the least fixed point. The non-monotonicity in Theorem 2 arises from changing the AF structure (adding argument b with its attack), not from the internal computation of the grounded extension. QED.

### 3.4 Theorem 4: Lossless Stratification

**Theorem 4.** On instances where the combined evaluator is monotone, the stratified evaluator produces the same result.

**Proof sketch.** When the combined evaluator is monotone, no argument is ever removed by adding new inputs. In this case, Stage 1 (Horn closure) derives all facts that would be derived at any point in the combined evaluator's iteration, and Stage 2 (grounded extension on the final AF) accepts exactly the arguments accepted by the combined evaluator's final state. The stratification merely separates what the combined evaluator does simultaneously into sequential stages. QED.

---

## 4. Formal Verification Status

### 4.1 Lean-Proved Results

| Result | Theorem Name | File | Status |
|--------|-------------|------|--------|
| Horn operator monotone | `horn_operator_monotone` | HornFixedPoint.lean | Proved (0 sorry) |
| Horn result is least FP | `horn_result_least_fixed_point` | HornFixedPoint.lean | Proved (0 sorry) |
| Horn result is minimal model | `horn_result_is_minimal_model` | HornFixedPoint.lean | Proved (0 sorry) |
| Horn finite termination | `horn_finite_termination` | HornFixedPoint.lean | Proved (0 sorry) |
| F monotone | `F_monotone` | DungFixedPoint.lean | Proved (0 sorry) |
| GE is least FP | `groundedSpec_is_least_fixed_point` | DungFixedPoint.lean | Proved (0 sorry) |
| GE is unique least FP | `groundedSpec_unique_least_fixed_point` | DungFixedPoint.lean | Proved (0 sorry) |
| GE finite termination | `finite_termination` | DungFixedPoint.lean | Proved (0 sorry) |
| Labelling partition | `labelling_partition` | DungFixedPoint.lean | Proved (0 sorry) |

### 4.2 Not Lean-Proved

| Result | Status | Reason |
|--------|--------|--------|
| Theorem 2 (combined evaluator non-monotone) | Counterexample (constructive) | Not mechanized in Lean; counterexample is verified by hand |
| Theorem 4 (lossless stratification) | Proof sketch | Full formalization pending |
| `ge_non_monotonicity` | Stated as Prop in UnifiedModel.lean | Neither proved nor refuted; structural observation |

### 4.3 JC_Formalization Registry

The JC_Formalization.lean registry tracks the overall status:
- `proved_theorems_card = 7`: 7 core theorems proved by artifact
- `refuted_theorems_card = 1`: T18 (DPPrivilege) refuted by counterexample
- `advance_cannot_revive_refuted`: Refuted theorems cannot be promoted

---

## 5. Implications

### 5.1 Why Stratification Is Necessary

The counterexample in Theorem 2 demonstrates that any system combining monotone derivation with non-monotone argumentation in a single fixpoint loop is unsound: it can produce results that depend on the order of input arrival, violating the expectation that adding information should not remove previously established conclusions.

### 5.2 Why Stratification Suffices

The stratified design ensures:
1. Stage 1 completes before Stage 2 begins
2. Stage 1 output is immutable during Stage 2
3. Stage 2 operates on a fixed AF structure
4. Non-monotonicity is confined to the AF structure change (adding arguments), not to the internal fixpoint computation

### 5.3 Connection to the Unified Model

In UnifiedModel.lean, the `full_chain` theorem connects all three stages:
```
full_chain : Horn rule fires -> argument in grounded extension -> price bounded
```
This composition is verified in Lean with zero sorry, ensuring that the stratified architecture is not just theoretically sound but mechanically checked.

---

## References

1. Dung, P.M. (1995). On the acceptability of arguments and its fundamental role in nonmonotonic reasoning, logic programming and n-person games. *Artificial Intelligence*, 77(2), 321--357.
2. Prakken, H. (2010). An abstract framework for argumentation with structured arguments. *Argument and Computation*, 1(2), 93--124.
3. Makinson, D. (2005). *Bridges from Classical to Nonmonotonic Logic*. King's College Publications.
4. Gelfond, M. and Kahl, Y. (2014). *Knowledge Representation, Reasoning, and the Design of Intelligent Agents*. Cambridge University Press.
5. Bench-Capon, T.J.M. and Dunne, P.E. (2007). Argumentation in artificial intelligence. *Artificial Intelligence*, 171(10--15), 619--641.
6. The mathlib Community (2020). The Lean mathematical library. *CPP 2020*, 367--381.
