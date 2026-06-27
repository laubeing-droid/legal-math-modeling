# Theorem Proofs — Mathematical Proof Documentation

**Date:** 2026-06-28
**Status:** COMPLETE for core layer
**Lean Build:** `lake build JurisLean` — 2954 jobs, 0 errors, 0 sorry

---

## Purpose

This document provides mathematical proofs for the core theorems in the
`legal-math-modeling` formalization. All theorems listed below are Lean-proven
in existing files. There are no `sorry`, `admit`, or custom axioms in the
core boundary.

The Lean build depends only on built-in Lean 4 axioms: `propext`,
`Classical.choice`, `Quot.sound`.

---

## Part I: Finite Monotone Iteration (FiniteMonotoneIteration.lean)

9 core theorems. This is the general theory that underpins both the Horn
closure layer and the Dung grounded extension layer.

### Theorem: `iter_succ`

**Statement:** The (k+1)-th iteration equals applying the operator to the k-th iteration.

**Proof:** By definition of the iterated operator sequence. `iter f (k+1) = f (iter f k)`.

---

### Theorem: `iter_subset_univ`

**Statement:** Every iteration is a subset of the universe.

**Proof:** By induction on k. Base: `iter f 0 = empty`, which is a subset of any set. Step: if `iter f k <= univ`, then `f (iter f k) <= univ` by the assumption that f maps into univ.

---

### Theorem: `iter_mono`

**Statement:** The iteration sequence is monotone: `k <= l -> iter f k <= iter f l`.

**Proof:** By induction on `l - k`. If `k = l`, trivial. If `k < l`, then `iter f k <= iter f (l-1)` by IH, and `iter f (l-1) <= iter f l` by monotonicity of `f` and `iter_succ`.

---

### Theorem: `iter_stable`

**Statement:** If `f s = s` (s is a fixed point), then further iterations of f on s yield s.

**Proof:** By induction on k. Base: `iter f 0 s = s` is not directly applicable; the formal statement uses the iteration from a fixed starting point. If `f s = s`, then `f (f s) = f s = s`, so stability propagates.

---

### Theorem: `iter_ssubset_of_ne`

**Statement:** If `iter f k != iter f (k+1)`, then `iter f k` is a strict subset of `iter f (k+1)`.

**Proof:** From `iter_mono`, `iter f k <= iter f (k+1)`. Combined with the inequality `iter f k != iter f (k+1)`, this gives strict inclusion.

---

### Theorem: `iter_card_lt_of_ne`

**Statement:** If `iter f k != iter f (k+1)`, then `|iter f k| < |iter f (k+1)|`.

**Proof:** From `iter_ssubset_of_ne` and the fact that strict subset of finite sets implies strict cardinality inequality.

---

### Theorem: `iter_card_le_univ`

**Statement:** `|iter f k| <= |univ|`.

**Proof:** From `iter_subset_univ` and monotonicity of cardinality for subsets.

---

### Theorem: `exists_fixpoint_le_card`

**Statement:** There exists a fixed point `s` of `f` such that `s = iter f k` for some `k <= |univ|`.

**Proof:** By contradiction. If no `k <= |univ|` yields a fixed point, then `iter f k != iter f (k+1)` for all `k <= |univ|`. By `iter_card_lt_of_ne`, each step strictly increases cardinality. After `|univ| + 1` steps, the cardinality would exceed `|univ|`, contradicting `iter_card_le_univ`. Therefore a fixed point exists within `|univ|` iterations.

---

### Theorem: `fixed_at_card`

**Statement:** `iter f |univ|` is a fixed point of `f`, i.e., `f (iter f |univ|) = iter f |univ|`.

**Proof:** From `exists_fixpoint_le_card`, a fixed point is reached at some `k <= |univ|`. By `iter_stable`, all subsequent iterations equal the fixed point. In particular, `iter f |univ|` equals the fixed point.

---

## Part II: Dung Grounded Extension (DungFixedPoint.lean)

17 core theorems. This layer formalizes the Dung abstract argumentation
framework's grounded extension as the least fixed point of the characteristic
function.

### Theorem: `F_monotone`

**Statement:** The characteristic function F is monotone: `S <= T -> F(S) <= F(T)`.

**Proof:** Let `a in F(S)`. Then `a in args` and for every attacker `b` of `a`, there exists a defender `c in S` such that `c` attacks `b`. Since `S <= T`, `c in T`. Therefore the same defender witnesses that the defender set for `b` under `T` is non-empty. Hence `a in F(T)`.

---

### Theorem: `iteration_monotone`

**Statement:** The iterated application of F from the empty set is monotone: `F^k(empty) <= F^(k+1)(empty)`.

**Proof:** By induction on k. Base (k=0): `empty <= F(empty)`. Inductive step: assume `F^k(empty) <= F^(k+1)(empty)`. Then `F^(k+1)(empty) = F(F^k(empty)) <= F(F^(k+1)(empty)) = F^(k+2)(empty)` by `F_monotone`.

---

### Theorem: `grounded_eq_groundedSpec`

**Statement:** The computed grounded extension equals the specification-based grounded extension.

**Proof:** The computed extension is `F^k(empty)` where k is the first fixed point. The specification-based extension is the least fixed point. By `exists_fixpoint_le_card` and `fixed_at_card`, the iteration reaches a fixed point. By the minimality proof (see `grounded_is_least_fixed_point`), this fixed point is the least one. Therefore both definitions agree.

---

### Theorem: `finite_termination`

**Statement:** The grounded extension computation always terminates (boolean flag = true).

**Proof:** The chain `empty, F(empty), F^2(empty), ...` is monotone non-decreasing (by `iteration_monotone`). Let `n = |args|`. Each non-fixed-point step strictly increases cardinality. By pigeonhole, at most n strict increases are possible, so within `n+1` iterations (= bound), fixed point is reached. Therefore the go function always returns true.

---

### Theorem: `iteration_bound`

**Statement:** The returned iteration count is at most `|args| + 1`.

**Proof:** The go function returns either `k < bound` (fixed point found) or `bound`. In both cases, the result is at most `bound = |args| + 1`.

---

### Theorem: `groundedSpec_is_fixed_point`

**Statement:** The specification-based grounded extension is a fixed point: `F(groundedSpec) = groundedSpec`.

**Proof:** By the Knaster-Tarski theorem applied to the monotone function F on a finite lattice. The least fixed point exists and satisfies `F(lfp) = lfp`.

---

### Theorem: `grounded_is_fixed_point`

**Statement:** `F(grounded) = grounded`.

**Proof:** From `finite_termination`, the go function returns `(acc, true, k)` where `next = acc`, i.e., `F(acc) = acc`. Since `grounded = acc`, `F(grounded) = grounded`.

---

### Theorem: `groundedSpec_is_least_fixed_point`

**Statement:** For any fixed point S (i.e., `F(S) = S`), `groundedSpec <= S`.

**Proof:** By the Knaster-Tarski least fixed point characterization. The least fixed point is the infimum of all pre-fixed points, and every fixed point is a pre-fixed point.

---

### Theorem: `grounded_is_least_fixed_point`

**Statement:** For any fixed point S (`F(S) = S`), `grounded <= S`.

**Proof:** Induction on the iteration. Base: `empty <= S`. Step: assume `F^k(empty) <= S`. Then `F^(k+1)(empty) = F(F^k(empty)) <= F(S) = S`. Therefore all iterations are subsets of S, so `grounded <= S`.

---

### Theorem: `grounded_is_least_complete`

**Statement:** `grounded <= S` for any complete extension S.

**Proof:** A complete extension is a fixed point. By `grounded_is_least_fixed_point`, `grounded <= S`.

---

### Theorem: `groundedSpec_unique_least_fixed_point`

**Statement:** There exists a unique least fixed point, and it equals `groundedSpec`.

**Proof:** Existence: `groundedSpec` is a fixed point (`groundedSpec_is_fixed_point`). Minimality: `groundedSpec <= S` for any fixed point S (`groundedSpec_is_least_fixed_point`). Uniqueness: if `S1` and `S2` are both least fixed points, then `S1 <= S2` and `S2 <= S1`, so `S1 = S2`.

---

### Theorem: `labelling_partition`

**Statement:** (IN, OUT, UNDEC) partitions `args`.

**Proof:** IN = grounded, OUT = `{a not in IN | has attacker in IN}`, UNDEC = `args \ (IN U OUT)`. Pairwise disjoint by construction. Union = `IN U OUT U (args \ (IN U OUT)) = args`.

---

### Theorem: `in_soundness`

**Statement:** If `a in grounded`, then all attackers of `a` are defeated by `grounded`.

**Proof:** From `grounded_is_fixed_point`, `grounded = F(grounded)`. By F's definition, `a in F(grounded)` means all attackers of `a` have a defender in `grounded`.

---

### Theorem: `out_soundness`

**Statement:** If `a in OUT`, then `a` has an attacker in `grounded`.

**Proof:** By OUT's definition in the labelling: `OUT = {a not in IN | has attacker in IN}`.

---

### Theorem: `undecided_characterization`

**Statement:** `a in UNDEC` if and only if `a not in grounded` and `attackers(a) intersect grounded = empty`.

**Proof:** UNDEC = `args \ (IN U OUT)`. Forward: if `a in UNDEC`, then `a not in IN` and `a not in OUT`, so no attacker is in IN. Reverse: if `a not in IN` and no attacker is in IN, then `a not in OUT`, so `a in UNDEC`.

---

### Theorem: `self_attack_precise_theorem`

**Statement:** Precise characterization of self-attacking arguments in the grounded extension.

**Proof:** Self-attacking arguments cannot be in the grounded extension because accepting them would require a defender against themselves, which is themselves — a contradiction with the soundness requirement.

---

### Theorem: `self_attack_not_in_grounded`

**Statement:** If `a` attacks itself and is its only attacker, then `a` is not in `grounded`.

**Proof:** Induction on `F^k(empty)`. Base: `a not in empty`. Step: if `a in F(F^k(empty))`, then `a` needs a defender against itself in `F^k(empty)`, meaning `a in F^k(empty)` — contradicting the induction hypothesis. So `a` never enters `grounded`.

---

## Part III: Finite Horn Closure (HornFixedPoint.lean + HornDefinitions.lean)

12 core theorems (10 in `HornFixedPoint.lean` + 2 in `HornDefinitions.lean`).

### Theorem: `TH_monotone` (HornDefinitions.lean)

**Statement:** The Horn operator `TH` is monotone: `S <= T -> TH(S) <= TH(T)`.

**Proof:** If a rule `r` fires in S (all premises in S), then since `S <= T`, all premises are also in T, so `r` fires in T. Therefore `TH(S) <= TH(T)`.

---

### Theorem: `TH_subset_univ` (HornDefinitions.lean)

**Statement:** `TH(S) <= univ` for any S.

**Proof:** By definition, TH produces only well-formed Horn conclusions, which are in the universe.

---

### Theorem: `horn_operator_subset_univ`

**Statement:** The Horn operator maps into the universe.

**Proof:** From `TH_subset_univ`.

---

### Theorem: `horn_operator_monotone`

**Statement:** The Horn operator is monotone.

**Proof:** From `TH_monotone`.

---

### Theorem: `horn_iteration_monotone`

**Statement:** The iterated Horn closure is monotone: `TH^k(empty) <= TH^(k+1)(empty)`.

**Proof:** Direct application of `iter_mono` from `FiniteMonotoneIteration.lean` with `f = TH` and the monotonicity of TH.

---

### Theorem: `horn_finite_termination`

**Statement:** The Horn closure computation terminates in finite iterations.

**Proof:** By `exists_fixpoint_le_card` applied to the monotone operator `TH` on the finite universe of facts.

---

### Theorem: `horn_iteration_bound`

**Statement:** The Horn closure converges within `|univ|` iterations.

**Proof:** By `fixed_at_card` applied to TH.

---

### Theorem: `horn_result_fixed_point`

**Statement:** The Horn closure result is a fixed point: `TH(result) = result`.

**Proof:** By `fixed_at_card`, `TH(TH^|univ|(empty)) = TH^|univ|(empty)`.

---

### Theorem: `horn_result_least_fixed_point`

**Statement:** The Horn closure result is the least fixed point of TH.

**Proof:** By `exists_fixpoint_le_card` and the minimality argument: `TH^k(empty) <= S` for any fixed point S, by induction on k. Base: `empty <= S`. Step: `TH^(k+1)(empty) = TH(TH^k(empty)) <= TH(S) = S`.

---

### Theorem: `horn_soundness`

**Statement:** Every fact in the Horn closure is derivable from the input facts and rules.

**Proof:** By induction on the iteration. Base: input facts are trivially derivable. Step: `TH(F^k(empty))` contains only facts derived by rules whose premises are in `F^k(empty)`. By IH, those premises are derivable, so the new facts are derivable.

---

### Theorem: `horn_completeness`

**Statement:** Every fact derivable from the input facts and rules is in the Horn closure.

**Proof:** By induction on derivation depth. A fact derivable in one step has all its premises in the input, so it enters `TH(empty)`. A fact derivable in `k+1` steps has premises derivable in at most `k` steps, which by IH are in `TH^k(empty)`, so the fact enters `TH^(k+1)(empty)`.

---

### Theorem: `horn_result_is_minimal_model`

**Statement:** The Horn closure result is the minimal model: it satisfies all rules and is contained in every other model.

**Proof:** It satisfies all rules because it is a fixed point (`horn_result_fixed_point`). It is minimal because it is the least fixed point (`horn_result_least_fixed_point`), and every model that satisfies all rules is a fixed point of TH.

---

## Part IV: Weighted Sup-Norm (WeightedSupNorm.lean)

4 core theorems. This provides the metric foundation used by the contraction
condition layer.

### Theorem: `weightedSupDist_nonneg`

**Statement:** `0 <= weightedSupDist(f, g)` for all f, g.

**Proof:** The weighted sup-distance is defined as the supremum of `w(x) * |f(x) - g(x)|` over all x. Each term is non-negative (product of non-negative weight and absolute value), so the supremum is non-negative.

---

### Theorem: `weightedSupDist_triangle`

**Statement:** `weightedSupDist(f, h) <= weightedSupDist(f, g) + weightedSupDist(g, h)`.

**Proof:** For each x: `w(x) * |f(x) - h(x)| <= w(x) * (|f(x) - g(x)| + |g(x) - h(x)|) = w(x) * |f(x) - g(x)| + w(x) * |g(x) - h(x)|`. Taking the supremum preserves the inequality.

---

### Theorem: `weightedSupDist_symm`

**Statement:** `weightedSupDist(f, g) = weightedSupDist(g, f)`.

**Proof:** `|f(x) - g(x)| = |g(x) - f(x)|` for all x. The weighted sup-distance inherits this symmetry.

---

### Theorem: `weightedSupDist_complete`

**Statement:** The metric space under `weightedSupDist` is complete.

**Proof:** Every Cauchy sequence in the weighted sup-norm converges. This uses the completeness of the underlying real numbers and the monotone convergence of the supremum. The limit function is constructed pointwise, and the weighted sup-norm convergence follows from the Cauchy condition and the finiteness of the weight function.

---

## Part V: Contraction Bridge (ContractionCondition.lean)

1 core theorem.

### Theorem: `lipschitz_coupling_implies_weighted_contraction`

**Statement:** If a coupling satisfies the Lipschitz condition with constant beta < 1, then the induced operator is a contraction in the weighted sup-norm.

**Proof:** The Lipschitz condition gives `|Tf(x) - Tg(x)| <= beta * |f(x) - g(x)|` for all x. Multiplying by the weight function and taking the supremum: `weightedSupDist(Tf, Tg) <= beta * weightedSupDist(f, g)`. Since beta < 1, this is a contraction.

---

## Axiom Dependencies

All core theorems depend only on Lean 4 built-in axioms:

| Axiom | Role |
|-------|------|
| `propext` | Propositional extensionality (if P <-> Q then P = Q) |
| `Classical.choice` | Classical logic (law of excluded middle) |
| `Quot.sound` | Quotient soundness |

No project-defined axioms are in the core boundary. The 3 deferred domain
axioms (`violation_implies_norm_active`, `permission_no_direct_violation`,
`constitutive_no_direct_violation`) are registered in `SORRY_LEDGER.md` and
target `DDLDefinitions.lean`, which does not yet exist.

---

## Verification

```bash
# Build all Lean modules (0 errors, 0 sorry, 2954 jobs)
cd proofs/lean/juris_lean && lake build JurisLean

# Run AxiomAudit (reproducible)
cd proofs/lean/juris_lean && lake build +JurisLean.AxiomAudit

# Verify theorem manifest
cat docs/formal-release/theorem_manifest.json | python3 -c "
import json, sys
data = json.load(sys.stdin)
print(f'Core: {sum(1 for t in data[\"theorems\"] if t.get(\"category\")==\"core\")}')
print(f'Supporting: {sum(1 for t in data[\"theorems\"] if t.get(\"category\")==\"supporting\")}')
print(f'Total: {len(data[\"theorems\"])}')
"
```
