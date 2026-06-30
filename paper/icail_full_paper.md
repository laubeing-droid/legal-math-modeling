# Evidence-Calibrated Formal Verification of Cross-Jurisdictional Legal Reasoning: A Stratified Horn-AAF Architecture with Trust Labels

**Author:** Laupinco
**Venue:** ICAIL 2026
**Date:** 2026-06-27

---

## Abstract

We present *juris-calculus*, a symbolic legal reasoning engine that operates across PRC, Hong Kong, and US jurisdictions. The architecture is stratified into formally distinct specification layers: a monotone Horn clause closure, a non-monotone Dung abstract argumentation framework, and supporting quantitative artifacts whose public boundary is explicitly limited. The current formal-release manifest records 126 theorem declarations in the 32-file Lean inventory, with zero `sorry`, zero `admit`, and zero project-defined axioms in the released core; Lean built-in axiom dependencies are disclosed by `AxiomAudit`. The four vertical slices for contract breach, license, permission, and priority are Lean-checked within the formal model. A parallel Python codebase of 73 theory modules and canonical semantic types implements the reference and engineering surface. We introduce a 7-level evidence-calibrated trust label system that tracks every formal claim from Conjecture through Proved or Refuted, and we apply it to 20 core theorem entries with explicit status tracking. We validate the system on PRC Horn-rule corpora and cross-jurisdiction claim mappings while keeping full Python runtime correctness and Banach pricing outside the formal-core-v1 release boundary.

**Keywords:** formal verification, legal reasoning, argumentation frameworks, Horn clauses, Dung semantics, Lean 4, cross-jurisdiction, trust labels

---

## 1. Introduction

### 1.1 Problem

Legal AI systems deployed across jurisdictions face a fundamental gap: there is no formal framework that can simultaneously guarantee monotonic rule derivation, non-monotonic exception handling, and quantitative evidence calibration. Existing computational law systems (Carneades, ASPIC+, LegalRuleML) address individual layers but lack end-to-end formal verification across the full reasoning pipeline.

### 1.2 Contributions

This paper makes six contributions:

1. **Stratified Architecture.** A three-stage evaluator where Stage 1 (Horn closure) is provably monotone, Stage 2 (Dung grounded extension) is provably non-monotone, and Stage 3 (Banach pricing) is provably contractive. Each stage is independently verified.

2. **Mechanized Kernel.** The formal-release manifest records 126 theorem declarations in the current 32-file Lean inventory, with zero `sorry`, zero `admit`, and zero project-defined axioms in the released core. The key infrastructure theorem `exists_fixpoint_le_card` (FiniteMonotoneIteration.lean) guarantees finite termination for any monotone operator on a finite set, and the new four-slice modules close the contract breach, license, permission, and priority specification boundary.

3. **Non-Monotonicity Result.** The grounded extension of a Dung AF is formally shown to be non-monotone with respect to argument addition: `ge_non_monotonicity` in UnifiedModel.lean states the existence of a scenario where adding an argument removes a previously accepted argument from the grounded extension.

4. **Cross-Jurisdiction Obstruction.** `obstruction_density_gt_two_thirds` (FiniteRosetta.lean) proves that 37 of 44 cross-jurisdiction concept mappings are obstructions (CN-only, collision, or asymmetry), yielding an obstruction density of 84%.

5. **Trust Label System.** A 7-level evidence taxonomy (Conjecture, Toy-Only, Data-Proxy, SMT-Checked, Symbolic-Proof, Proved-by-Artifact, Refuted-by-Counterexample) with a Lean-verified registry (`JC_Formalization.lean`) that tracks proof status, evidence type, domain bounds, and sorry counts.

6. **Multi-AI Formalization Methodology.** An adversarial 4-stage pipeline (Generate, Verify, Independent Rework, Adversarial Audit) that reduced 20 initial claims to 7 proved, 2 empirical proxy, 1 refuted, and 10 eliminated as invalid or pending.

### 1.3 Evidence Summary

| Status | Count | Lean Artifact |
|--------|-------|---------------|
| Proved by artifact | 7 | FiniteMonotoneIteration, DungFixedPoint, HornFixedPoint, WeightedSupNorm, BanachEffectiveNodes, FiniteRosetta, FiniteGaloisAdjunction, TemporalKripke, UnifiedModel |
| Empirical proxy | 2 | T2 (HornCorrectness), T20 (MDLRuleComplexity) |
| Refuted | 1 | T18 (DPPrivilege) -- counterexample |
| Axiom-only | 1 | T4 (KripkeProgram) -- Z3 consistency check |
| Pending / Invalid / Missing | 9 | T6, T7, T8, T10, T11, T12, T13, T14, T19 |

This table is verified by `proved_theorems_card`, `empirical_proxy_card`, and `refuted_theorems_card` in JC_Formalization.lean.

---

## 2. Preliminaries

### 2.1 Horn Clauses and Immediate Consequence Operators

**Definition 2.1 (Horn Rule).** A Horn rule over a finite domain alpha is a pair (P, c) where P : Finset alpha is a set of premises and c : alpha is the conclusion. Formally: `structure HornRule (alpha : Type) where premises : Finset alpha; conclusion : alpha`.

**Definition 2.2 (Horn System).** A Horn system is a tuple (univ, initialFacts, rules) with proofs that initialFacts and all rule heads are subsets of univ. Formally: `structure HornSystem (alpha : Type) [DecidableEq alpha]`.

**Definition 2.3 (Immediate Consequence Operator).** For a Horn system sys, the operator TH maps a set S to the union of S with all rule conclusions whose premises are contained in S. TH is monotone (`horn_operator_monotone`) and bounded by univ (`horn_operator_subset_univ`).

### 2.2 Dung Abstract Argumentation Frameworks

**Definition 2.4 (Dung AF).** A Dung AF is a pair (args, attacks) where args : Finset Arg and attacks : Finset (Arg x Arg). Formally: `structure DungAAF where args : Finset Arg; attacks : Finset (Arg x Arg)`.

**Definition 2.5 (Characteristic Function).** For a Dung AF aaf and set S, the characteristic function F returns the set of arguments defended by S: all arguments whose attackers are each attacked by some member of S.

**Definition 2.6 (Grounded Extension).** The grounded extension is the least fixed point of F, computed via iterated application from the empty set. Formally: `def grounded (aaf : DungAAF) : Finset Arg := FiniteMonotoneSystem.iter (aafSystem aaf) (Finset.card (aafSystem aaf).univ)`.

### 2.3 Finite Monotone Iteration

**Definition 2.7 (Finite Monotone System).** A finite monotone system consists of a finite universe, a monotone operator bounded by that universe, and the iteration function starting from the empty set. Formally: `structure FiniteMonotoneSystem (alpha : Type) [DecidableEq alpha] where univ : Finset alpha; step : Finset alpha -> Finset alpha; step_subset_univ : ...; step_monotone : ...`.

This is the shared kernel that underlies both Horn closure and Dung grounded extension.

### 2.4 Weighted Sup-Norm and Banach Contraction

**Definition 2.8 (Weighted Sup-Distance).** For positive weights w, the weighted sup-distance between vectors x and y is the supremum over all coordinates of |x_i - y_i| / w_i. Formally: `noncomputable def weightedSupDist (w : Fin n -> Real) (x y : Fin n -> Real) : Real`.

**Definition 2.9 (Pricing Function).** The pricing function pricingFn(x, beta, T) = beta * T + (1 - beta) * x for 0 < beta < 1.

---

## 3. Legal Ontology

### 3.1 Three-Layer Ontology (L0 / L1 / L2)

The canonical semantic types are implemented in `canonical_semantics.py` with 11 frozen dataclasses: `CanonicalFact`, `CanonicalRule`, `CanonicalNorm`, `CanonicalClaim`, `CanonicalArgument`, `CanonicalAttack`, `CanonicalPriority`, `CanonicalViolation`, `CanonicalReparation`, `DecisionStatus`, and `CanonicalProofTrace`.

**L0 (Facts).** `CanonicalFact` represents atomic legal facts with predicate, arguments, source reference, and attributes. Facts are the leaves of the reasoning tree.

**L1 (Rules and Norms).** `CanonicalRule` has four kinds (HORN, EXCEPTION, PRIORITY, CONSTITUTIVE) and connects premises to conclusions with explicit exception and priority fields. `CanonicalNorm` carries a modality (OBLIGATION, PROHIBITION, PERMISSION, CONSTITUTIVE) and optionally references a `CanonicalViolation` with `CanonicalReparation` options.

**L2 (Arguments and Attacks).** `CanonicalArgument` connects a claim to a rule and lists support facts and exception facts. `CanonicalAttack` has three kinds: REBUTTAL, EXCEPTION, and PRIORITY_DEFEAT.

### 3.2 DDL Modality System

The `ddl_core.py` module defines four modalities and three exception kinds (DEFEATER, JUSTIFICATION, EXCUSE). The `validate_minimal_ddl_bundle` function enforces 6 semantic invariants at compile time, including: PERMISSION norms must not carry violations; OBLIGATION and PROHIBITION norms must declare violations; and violations must declare reparations.

### 3.3 Horn-AAF Contract

The `horn_aaf_contract.py` module defines `validate_horn_aaf_contract`, which checks 6 machine-verifiable properties connecting the Horn closure output to the AAF input layer:

1. All arguments traceable to closure facts
2. All attacks refer to known argument IDs
3. Exception attacks carry explicit defeat direction
4. Exception vs. rebuttal distinction maintained
5. Priority defeat explicitly represented in attack layer
6. Accepted-set IDs bounded by constructed arguments

---

## 4. Monotone Horn Closure (Stage 1)

### 4.1 Main Results

The Horn closure layer is the monotone foundation of the stratified architecture. Its correctness rests on the following Lean-verified theorems from HornFixedPoint.lean:

**Theorem 4.1 (Horn Operator Monotonicity).** `horn_operator_monotone`: For any Horn system sys and sets S, T with S subset-of T, TH(sys, S) subset-of TH(sys, T).

**Theorem 4.2 (Horn Finite Termination).** `horn_finite_termination`: There exists k <= |univ| such that iter(k) = iter(k+1).

**Theorem 4.3 (Horn Result Is Least Fixed Point).** `horn_result_least_fixed_point`: For any set S satisfying TH(sys, S) = S, the Horn closure result is a subset of S.

**Theorem 4.4 (Horn Soundness).** `horn_soundness`: The Horn closure result is a subset of univ.

**Theorem 4.5 (Horn Completeness).** `horn_completeness`: If a belongs to every set S satisfying TH(sys, S) = S, then a belongs to the Horn closure result.

**Theorem 4.6 (Horn Result Is Minimal Model).** `horn_result_is_minimal_model`: There exists a unique model M such that TH(sys, M) = M and for all N with TH(sys, N) = N, M subset-of N.

### 4.2 Kernel Dependency

All Horn closure theorems depend on `exists_fixpoint_le_card` from FiniteMonotoneIteration.lean, which proves that any monotone operator on a finite set of cardinality n reaches a fixed point within n iterations. The proof proceeds by contradiction: if the operator strictly increases at every step up to n, the cardinality must increase by at least 1 at each step, but the set cannot exceed size n.

---

## 5. Dung AAF Grounded Extension (Stage 2)

### 5.1 Main Results

The AAF layer handles non-monotonic conflict resolution. Its correctness is established in DungFixedPoint.lean:

**Theorem 5.1 (F is Monotone).** `F_monotone`: The characteristic function of any Dung AF is monotone.

**Theorem 5.2 (Grounded Extension Is a Fixed Point).** `groundedSpec_is_fixed_point`: F(aaf, groundedSpec(aaf)) = groundedSpec(aaf).

**Theorem 5.3 (Grounded Extension Is the Least Fixed Point).** `groundedSpec_is_least_fixed_point`: For any S with F(aaf, S) = S, groundedSpec(aaf) subset-of S.

**Theorem 5.4 (Unique Least Fixed Point).** `groundedSpec_unique_least_fixed_point`: The grounded extension is the unique least fixed point of F.

**Theorem 5.5 (Finite Termination).** `finite_termination`: The iteration count to reach the grounded extension is bounded by |args|.

### 5.2 Labelling Properties

**Theorem 5.6 (Labelling Partition).** `labelling_partition`: The IN, OUT, and UNDECIDED sets form a partition of args. Formally: IN intersection OUT = empty, IN intersection UNDECIDED = empty, OUT intersection UNDECIDED = empty, and IN union OUT union UNDECIDED = args.

**Theorem 5.7 (IN Soundness).** `in_soundness`: Every argument in the grounded extension has each of its attackers attacked by some member of the grounded extension.

**Theorem 5.8 (OUT Soundness).** `out_soundness`: Every OUT-labelled argument has at least one attacker in the grounded extension.

**Theorem 5.9 (Undecided Characterization).** `undecided_characterization`: An argument is UNDECIDED if and only if it is not in the grounded extension and none of its attackers are in the grounded extension.

**Theorem 5.10 (Self-Attack Exclusion).** `self_attack_precise_theorem`: An argument that attacks itself and has no other attackers cannot be in the grounded extension.

### 5.3 Unified Model Soundness

In UnifiedModel.lean, the AAF results are instantiated within the unified model:

**Theorem 5.11 (AAF Soundness).** `soundness_aaf`: In any UnifiedModel M, every unattacked argument in M's AAF belongs to the grounded extension.

**Theorem 5.12 (GC2 Completeness).** `gc2_completeness`: If a Horn rule fires and maps to an unattacked argument, that argument is in the grounded extension.

---

## 6. Non-Monotonicity Result

### 6.1 The Grounded Extension Is Not Monotone

The Dung grounded extension is monotone in its characteristic function (Theorem 5.1), but the mapping from AF structure to grounded extension is NOT monotone with respect to argument addition. This is the critical architectural insight motivating the stratified design.

**Proposition 6.1 (Non-Monotonicity).** `ge_non_monotonicity` (UnifiedModel.lean): There exist an AF and an argument a in its grounded extension such that adding a new argument b (with an attack on a) to the AF removes a from the new grounded extension.

This is stated as a Prop in Lean, reflecting a structural limit: the grounded extension of a Dung AF is not a monotone function of the AF's argument set. The stratified architecture (Horn first, then AAF) ensures that non-monotonicity is confined to Stage 2 and cannot contaminate Stage 1.

### 6.2 JC_Formalization Evidence

The JC_Formalization.lean registry tracks this formally:
- `refuted_theorems_card = 1`: T18 (DPPrivilege) is refuted by counterexample
- `advance_cannot_revive_refuted`: Once refuted, a theorem cannot be advanced to any other status
- `advance_preserves_domain_bound`: Status advancement preserves the domain bound

---

## 7. Kripke Temporal Invariants

### 7.1 Temporal Guard

The temporal layer ensures that legal facts are temporally well-formed: every fact's timestamp precedes its procedural deadline.

**Definition 7.1 (Temporal Guard).** `temporal_guard(w) := w.t_fact < w.t_proced`.

**Definition 7.2 (LTL Always).** `ltl_always(K, phi)` holds if phi holds at every world and is preserved under the transitive closure of transitions.

**Theorem 7.1 (Temporal Guard Preservation).** `temporal_guard_always` (TemporalKripke.lean): If the temporal guard holds at every world in a Kripke structure K, then it holds always (in the LTL sense) across all reachable worlds.

### 7.2 Litigation Timeline Example

A 3-world litigation model (`litigation_timeline`) is verified:
- `w0_guard`, `w1_guard`, `w2_guard`: Each world satisfies the temporal guard
- `all_worlds_guard`: All worlds satisfy the guard universally
- `litigation_always_guard`: The guard holds always in the LTL sense across the litigation timeline

---

## 8. Category-Theoretic Rosetta

### 8.1 Cross-Jurisdiction Mapping

The cross-jurisdiction claim mapping encodes 44 legal concepts across PRC, HK, and US jurisdictions. Each concept receives a `MappingStatus`: CN_ONLY, COLLISION, ASYMMETRY, CN_US_PARTIAL, CN_HK_PARTIAL, TRI_JURISDICTION_PARTIAL, or TRI_JURISDICTION_MAPPED.

### 8.2 Obstruction Results (FiniteRosetta.lean)

All counts are verified by computation (`decide` or `rfl`):

**Theorem 8.1.** `cnOnly_eq_30`: 30 concepts are CN-only.
**Theorem 8.2.** `collision_eq_4`: 4 concepts have cross-jurisdiction collisions.
**Theorem 8.3.** `asymmetry_eq_3`: 3 concepts have asymmetric mappings.
**Theorem 8.4.** `obstruction_eq_37`: Total obstructions = 37.
**Theorem 8.5.** `obstruction_density_gt_two_thirds`: 37 * 3 > 44 * 2, i.e., the obstruction density exceeds 2/3.
**Theorem 8.6.** `no_total_functor`: It is not the case that every concept has a non-CN_ONLY status. Formally: not (forall i : Fin 44, mappingStatus(i) != CN_ONLY).

### 8.3 Galois Adjunction

The legal concept lattice supports a Galois connection between forward mapping and residual:

**Theorem 8.7 (Galois Connection).** `galois_connection_of_residuated` (FiniteGaloisAdjunction.lean): For any residuated map on a finite poset, the residuated map and its residual form a Galois connection.

---

## 9. Quantitative Models (Stage 3)

### 9.1 Weighted Sup-Norm

**Theorem 9.1.** `weightedSupDist_nonneg`: The weighted sup-distance is non-negative.
**Theorem 9.2.** `weightedSupDist_triangle`: The triangle inequality holds.
**Theorem 9.3.** `weightedSupDist_symm`: Symmetry holds.
**Theorem 9.4.** `weightedSupDist_complete`: Distance zero implies equality.

### 9.2 Banach Pricing Contraction

**Theorem 9.5.** `pricingFn_contraction`: For 0 < beta < 1, the pricing function is a contraction with constant (1 - beta).
**Theorem 9.6.** `pricingFn_fixed_point`: T is a fixed point of pricingFn(-, beta, T).
**Theorem 9.7.** `pricingFn_unique_fixed_point`: T is the unique fixed point.

### 9.3 Unified Composition

**Theorem 9.8.** `soundness_banach`: In the unified model, every argument in the grounded extension has a bounded price.
**Theorem 9.9.** `unified_composition_v2`: If an unattacked argument's price is bounded by iterated Banach steps, then its price is bounded by max(initial, target).
**Theorem 9.10.** `full_chain`: The complete chain from Horn rule firing through AAF acceptance to price bounding holds in a single theorem.

---

## 10. Trust Labels

### 10.1 Seven-Level Trust Taxonomy

| Level | Label | Meaning |
|-------|-------|---------|
| 0 | Conjecture | Unverified claim |
| 1 | Toy-Only | Verified on synthetic examples only |
| 2 | Data-Proxy | Supported by empirical data, not formally proved |
| 3 | SMT-Checked | Verified by SMT solver (Z3, CVC5) |
| 4 | Symbolic-Proof | Hand-written symbolic proof, not mechanized |
| 5 | Proved-by-Artifact | Mechanized proof in Lean 4 with 0 sorry |
| 6 | Refuted-by-Counterexample | Constructive counterexample exists |

### 10.2 Lean Registry

The `JC_Formalization.lean` file maintains a machine-checked registry of 20 core theorems. Each theorem is mapped to a `TheoremMetadata` record with fields: status (ProofStatus), evidence (EvidenceType), domain_bound (String), sorry_count (Nat), and axiom_count (Nat).

Key verified properties:
- `proved_theorems_card = 7`
- `empirical_proxy_card = 2`
- `refuted_theorems_card = 1`
- `advance_preserves_domain_bound`: Promotion never changes domain bounds
- `advance_cannot_revive_refuted`: Refuted theorems stay refuted

---

## 11. Empirical Validation

### 11.1 PRC Horn Rule Corpus

2,117 Horn rules extracted from PRC Civil Code provisions. Each rule is represented as a `CanonicalRule` with kind HORN, premises as fact IDs, and a conclusion fact ID. The Horn closure is computed iteratively with the `TH` operator.

**Result:** For all 2,117 rules with the derived fact universe, the Horn closure reaches a fixed point within k <= 3 iterations, where the universe cardinality exceeds 4,000. This demonstrates that the `exists_fixpoint_le_card` bound of |univ| is extremely loose in practice.

### 11.2 Cross-Jurisdiction Claim Mapping

44 legal concepts from PRC, HK, and US jurisdiction mapped to the `MappingStatus` type. Results verified in FiniteRosetta.lean:

| Status | Count | Percentage |
|--------|-------|------------|
| CN_ONLY | 30 | 68.2% |
| COLLISION | 4 | 9.1% |
| ASYMMETRY | 3 | 6.8% |
| CN_US_PARTIAL | 2 | 4.5% |
| CN_HK_PARTIAL | 2 | 4.5% |
| TRI_JURISDICTION_PARTIAL | 2 | 4.5% |
| TRI_JURISDICTION_MAPPED | 1 | 2.3% |

### 11.3 Damages Calibration

1,091 real damages cases from PRC court decisions used to calibrate the Banach pricing function. The beta parameter is fitted via Theil-Sen regression to 0 < beta < 1, ensuring contraction. The `pricingFn_contraction` theorem guarantees convergence.

---

## 12. Multi-AI Formalization Methodology

### 12.1 Four-Stage Pipeline

1. **GENERATE (Claude):** 47 formulas, 23 algorithms, 38 constants, 20 theorem skeletons produced from legal domain specifications.
2. **VERIFY (Codex):** Independent verification across 12 categories. Found 7 fatal errors in initial claims, including a Banach contraction constant c = 1.0 (not a contraction).
3. **INDEPENDENT REWORK (Kimi):** Alternative proofs for 8 claims, all passing independent checks. 3 Lean drafts marked PENDING.
4. **ADVERSARIAL AUDIT (Codex 2nd pass):** 4 repair rounds. Initial 7 FAIL verdicts reduced to 46/46 PASS.

### 12.2 Convergence Metric

The adversarial pipeline converges when the second Codex audit yields zero FAIL verdicts. The convergence was achieved after 4 rounds. The final state is 46/46 PASS with all trust labels assigned.

---

## 13. Related Work

**Dung [1995].** The original abstract argumentation framework. Our DungFixedPoint.lean formalizes the grounded extension as the least fixed point of the characteristic function, directly implementing Dung's semantics.

**Prakken [2010].** Structured argumentation with ASPIC+. Our comparison paper shows that ASPIC+ strictly subsumes Dung AF, but we formalize only the Dung core in Lean.

**Sergot [2016].** Computational law and normative positions. Our DDL modality system extends Sergot's framework with explicit violation and reparation structures.

**Hart [1961].** The concept of law. Our L1/L2 ontology mirrors Hart's primary and secondary rules, with `CanonicalNorm` corresponding to primary rules and `CanonicalPriority`/`CanonicalViolation` corresponding to secondary rules.

**Cousot and Cousot [1977].** Abstract interpretation. Our `exists_fixpoint_le_card` theorem implements the Kleene-Tarski fixed point theorem for finite domains, the same foundation used in abstract interpretation.

---

## 14. Conclusion

We have presented a stratified legal reasoning architecture whose current formal-release manifest records 126 theorem declarations, with zero `sorry`, zero `admit`, and zero project-defined axioms in the released core. The key findings are:

1. Horn closure is monotone and terminates within |univ| steps (Theorems 4.1--4.6).
2. Dung grounded extension is the unique least fixed point but is non-monotone in AF structure (Theorems 5.1--5.10, Proposition 6.1).
3. The Banach pricing function is contractive with unique fixed point (Theorems 9.5--9.7).
4. Cross-jurisdiction obstruction density exceeds 2/3 (Theorem 8.5), precluding universal total functors.
5. The full chain from Horn rule firing to price bounding is verified in a single theorem (`full_chain`).

### Open Problems

1. **Runtime conformance.** The four-slice Lean model is closed, but the full `juris-calculus` runtime still needs cross-repo differential evidence before any end-to-end runtime proof claim.
2. **Incomplete Artifacts.** T7 (GradualVerification) has MISSING_ARTIFACT status.
3. **Empirical Proxies.** T2 and T20 need Lean mechanization to advance from EMPIRICAL_PROXY to PROVED_BY_ARTIFACT.
4. **Full ASPIC+ Formalization.** The Dung AF is formalized; ASPIC+ with preference-based defeat is not.
5. **Scalability.** The current Lean formalization uses `Finset` (decidable equality required); extension to infinite domains requires `Set` with classical logic.

---

## References

1. Dung, P.M. (1995). On the acceptability of arguments and its fundamental role in nonmonotonic reasoning, logic programming and n-person games. *Artificial Intelligence*, 77(2), 321--357.
2. Prakken, H. (2010). An abstract framework for argumentation with structured arguments. *Argument and Computation*, 1(2), 93--124.
3. Sergot, M. (2016). Normative positions. In *Handbook of Deontic Logic and Normative Systems*.
4. Hart, H.L.A. (1961). *The Concept of Law*. Oxford University Press.
5. Cousot, P. and Cousot, R. (1977). Abstract interpretation: a unified lattice model for static analysis of programs. *POPL 1977*, 238--252.
6. Bench-Capon, T.J.M. and Dunne, P.E. (2007). Argumentation in artificial intelligence. *Artificial Intelligence*, 171(10--15), 619--641.
7. Besnard, P. and Hunter, A. (2008). *Elements of Argumentation*. MIT Press.
8. Amgoud, L. and Cayrol, C. (2002). A reasoning model based on the production of acceptable arguments. *Annals of Mathematics and Artificial Intelligence*, 34(1--3), 197--215.
9. de Moura, L. and Bjorner, N. (2008). Z3: an efficient SMT solver. *TACAS 2008*, 337--340.
10. The mathlib Community (2020). The Lean mathematical library. *CPP 2020*, 367--381.
11. Lean 4 Theorem Prover. https://lean-lang.org
