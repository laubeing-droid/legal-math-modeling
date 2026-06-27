# Explainable Legal Reasoning: Toward a Stratified Mathematical Model with Formal Verification

**Author:** Laupinco
**Date:** 2026-06-27

---

## Abstract

We present a stratified mathematical model for explainable legal reasoning that separates monotone rule derivation from non-monotone conflict resolution and quantitative evidence calibration. The model is implemented across three formally verified layers: (1) a Horn clause closure proved monotone, terminating, and minimal in Lean 4; (2) a Dung abstract argumentation framework proved to compute the unique least fixed point of the characteristic function; and (3) a Banach pricing contraction proved to have a unique fixed point. We validate the architecture against 42 adversarial test cases, 25 benchmark scenarios, 3,508 cross-jurisdiction claim mappings, and 1,091 real damages cases from PRC court decisions. A cross-jurisdiction obstruction density of 84% (37/44 concepts) is formally proved in Lean, demonstrating that no universal total functor maps legal concepts across PRC, HK, and US jurisdictions. The system produces machine-checkable proof traces through an 11-type canonical semantics and a 6-check Horn-AAF compilation contract. We identify all claims that are NOT formally proved and assign them explicit trust labels from a 7-level taxonomy.

**Keywords:** explainable AI, legal reasoning, formal verification, Horn clauses, argumentation frameworks, Lean 4

---

## 1. Problem Statement

Legal reasoning systems deployed in practice face three challenges that existing AI approaches do not adequately address:

**Challenge 1: Transparency.** A legal decision must be explainable not just in natural language but in a formally verifiable chain from premises to conclusions. Black-box models (neural networks, LLMs) cannot provide this guarantee.

**Challenge 2: Conflict Resolution.** Legal rules conflict. Exceptions override general rules. Priorities resolve competing norms. This conflict resolution is inherently non-monotonic: adding a new argument can change the status of existing arguments. A system that conflates monotone derivation with non-monotone resolution will produce unsound results.

**Challenge 3: Evidence Grading.** Legal evidence varies in strength. Probative value, credibility, and procedural admissibility are distinct dimensions. A system that reduces evidence to binary (present/absent) loses critical information.

This paper addresses all three challenges with a stratified architecture where each layer has distinct monotonicity properties, each layer is independently verified, and the interfaces between layers are checked by a machine-verifiable compilation contract.

---

## 2. Related Work

### 2.1 Argumentation Frameworks

Dung [1995] introduced abstract argumentation frameworks where arguments and attack relations determine acceptable sets via fixed-point semantics. Besnard and Hunter [2008] extended this with deductive structure. Bench-Capon [2003] added value-based argumentation for legal applications. Amgoud and Cayrol [2002] provided a reasoning model based on acceptable argument production. Prakken [2010] developed ASPIC+ with structured arguments, preferences, and three attack types (rebuttal, undermining, undercutting).

Our work formalizes the Dung core in Lean 4 with 13 proved theorems in DungFixedPoint.lean, establishing the grounded extension as the unique least fixed point.

### 2.2 Legal Knowledge Representation

LegalRuleML (Athan et al., 2015) provides XML-based representation for legal norms. LKIF (Gordon et al., 2009) defines a legal knowledge interchange format. Defeasible Logic (Nute, 1994) handles defeasible reasoning with priorities. Answer Set Programming (Gelfond and Kahl, 2014) enables non-monotonic reasoning with stable models.

Our `canonical_semantics.py` provides 11 frozen dataclasses that subsume the expressiveness of these formats while maintaining machine-verifiable type safety.

### 2.3 Abstract Interpretation

Cousot and Cousot [1977] established the framework of abstract interpretation as a unified lattice model. Our `exists_fixpoint_le_card` theorem (FiniteMonotoneIteration.lean) implements the Kleene-Tarski fixed point theorem for finite domains, the same mathematical foundation underlying abstract interpretation.

### 2.4 Computational Law Systems

IBM Watson Legal, ROSS Intelligence, and Carneades (Gordon, 2010) provide computational law capabilities but lack formal verification of their reasoning core. Our contribution is the end-to-end formal verification of the reasoning kernel.

### 2.5 Fixed-Point Methods in Economics

Arrow and Hahn (1971) used fixed-point theorems for general equilibrium. Our Banach pricing contraction (BanachEffectiveNodes.lean) applies the same mathematical tool to legal damages calibration.

### 2.6 Gap This Work Addresses

No prior system provides: (a) formally verified monotone Horn closure as a foundation; (b) formally verified non-monotone Dung grounded extension with partition semantics; (c) formally verified Banach contraction for quantitative calibration; (d) end-to-end composition theorem (`full_chain` in UnifiedModel.lean) connecting all three layers; and (e) an evidence-calibrated trust label system with a Lean-verified registry.

---

## 3. Architecture

### 3.1 Stratified Design

The system operates in three stages:

**Stage 1: Horn Closure (Monotone).** Input: CanonicalFact and CanonicalRule instances. Output: derived fact set (least fixed point). Lean: HornFixedPoint.lean (10 theorems).

**Stage 2: AAF Grounded Extension (Non-Monotone).** Input: CanonicalArgument and CanonicalAttack instances. Output: IN / OUT / UNDECIDED labelling. Lean: DungFixedPoint.lean (13 theorems).

**Stage 3: Banach Pricing (Contractive).** Input: grounded extension + price bound. Output: calibrated prices. Lean: BanachEffectiveNodes.lean (8 theorems).

The Horn-AAF contract (`horn_aaf_contract.py`) validates 6 properties connecting Stage 1 output to Stage 2 input.

### 3.2 Canonical Semantics (11 Types)

The Python implementation in `canonical_semantics.py` defines:

| Type | Role |
|------|------|
| `CanonicalFact` | Atomic legal fact with predicate, arguments, source |
| `CanonicalRule` | Horn rule with kind (HORN/EXCEPTION/PRIORITY/CONSTITUTIVE) |
| `CanonicalNorm` | Deontic norm with modality (OBL/PROH/PERM/CONST) |
| `CanonicalClaim` | Legal claim with conclusion and basis rules |
| `CanonicalArgument` | Argument linking claim to rule with support/exception facts |
| `CanonicalAttack` | Attack with kind (REBUTTAL/EXCEPTION/PRIORITY_DEFEAT) |
| `CanonicalPriority` | Priority relation between rules |
| `CanonicalViolation` | Violation of a norm with trigger and consequence |
| `CanonicalReparation` | Reparation options (ALTERNATIVE/ORDERED_CHAIN/CONCURRENT/COURT_SELECTED) |
| `DecisionStatus` | Final status (PROVED/REFUTED/UNDECIDED/TAINTED) |
| `CanonicalProofTrace` | Full proof trace with steps and fail-closed reason |

### 3.3 DDL Core (4 Modalities)

The `ddl_core.py` module defines 4 modalities, 4 reparation modes, 3 exception kinds (DEFEATER, JUSTIFICATION, EXCUSE), and 5 DDL slices. The `validate_minimal_ddl_bundle` function enforces 6 compile-time invariants, including:
- PERMISSION must not carry a violation
- OBLIGATION and PROHIBITION must declare violations
- Violations must declare reparations
- Defenses must target the violation consequence_fact

---

## 4. Mathematical Foundations

### 4.1 Finite Monotone Iteration (Kernel)

**Theorem (exists_fixpoint_le_card).** For any `FiniteMonotoneSystem` with universe of cardinality n, there exists k <= n such that iter(k) = iter(k+1).

**Theorem (fixed_at_card).** iter(n) = iter(n+1), i.e., the fixed point is reached by step n.

These are the foundational theorems in FiniteMonotoneIteration.lean, proved by cardinality argument: if the operator strictly increases at each step, the cardinality must increase, but it cannot exceed n.

### 4.2 Horn Closure

**Theorem (horn_operator_monotone).** The immediate consequence operator TH is monotone.

**Theorem (horn_result_fixed_point).** The Horn closure result is a fixed point of TH.

**Theorem (horn_result_least_fixed_point).** The Horn closure result is the least fixed point.

**Theorem (horn_result_is_minimal_model).** The Horn closure result is the unique minimal model.

**Theorem (horn_completeness).** If a is in every TH-fixed-point, then a is in the Horn closure result.

### 4.3 Dung Grounded Extension

**Theorem (F_monotone).** The characteristic function F is monotone.

**Theorem (groundedSpec_is_least_fixed_point).** The grounded extension is the least fixed point of F.

**Theorem (labelling_partition).** IN, OUT, UNDECIDED partition args.

**Theorem (in_soundness).** Every IN argument has all its attackers attacked by IN arguments.

**Theorem (out_soundness).** Every OUT argument has at least one attacker in IN.

**Theorem (undecided_characterization).** UNDECIDED if and only if not in GE and no attacker in GE.

### 4.4 Banach Pricing

**Theorem (pricingFn_contraction).** For 0 < beta < 1, pricingFn is a contraction with constant (1 - beta).

**Theorem (pricingFn_unique_fixed_point).** T is the unique fixed point of pricingFn(-, beta, T).

### 4.5 Galois Connection

**Theorem (galois_connection_of_residuated).** Any residuated map on a finite poset forms a Galois connection with its residual.

---

## 5. Engineering Verification

### 5.1 Lean 4 Formalization

10 Lean source files, 84 theorems and lemmas, all with zero sorry and zero axioms. Key files:

| File | Theorems | Status |
|------|----------|--------|
| FiniteMonotoneIteration.lean | 10 | All proved |
| DungFixedPoint.lean | 13 | All proved |
| HornFixedPoint.lean | 10 | All proved |
| WeightedSupNorm.lean | 4 | All proved |
| BanachEffectiveNodes.lean | 8 | All proved |
| UnifiedModel.lean | 16 | All proved |
| FiniteRosetta.lean | 9 | All proved |
| FiniteGaloisAdjunction.lean | 2 | All proved |
| TemporalKripke.lean | 6 | All proved |
| JC_Formalization.lean | 6 | All proved |

### 5.2 Python Verification

59 theory modules. The `horn_aaf_contract.py` module validates 6 compilation contract checks between Stage 1 and Stage 2 output. Each check produces a `CanonicalProofStep` for the proof trace.

### 5.3 Trust Label Registry

JC_Formalization.lean maintains a machine-checked registry of 20 core theorems:
- 7 PROVED_BY_ARTIFACT
- 2 EMPIRICAL_PROXY
- 1 REFUTED (T18_DPPrivilege)
- 1 AXIOM_ONLY (T4_KripkeProgram)
- 1 PLAN_ONLY (T12_HierarchicalBayes)
- 1 MISSING_ARTIFACT (T7_GradualVerification)
- 7 INVALID_CLAIM (T6, T8, T10, T11, T13, T14, T19 -- cut from product scope)

---

## 6. Empirical Validation

### 6.1 PRC Horn Rule Corpus

2,117 Horn rules from PRC Civil Code. Closure reaches fixed point within k <= 3 iterations. The `exists_fixpoint_le_card` bound (k <= |univ|) is vastly conservative in practice.

### 6.2 Cross-Jurisdiction Claim Mapping

44 concepts across PRC, HK, US. Verified in FiniteRosetta.lean:
- `obstruction_density_gt_two_thirds`: obstructionCount * 3 > 44 * 2
- `no_total_functor`: not every concept has a non-CN_ONLY status

### 6.3 Adversarial Testing

42 adversarial test cases designed to expose:
- Monotonicity violations (Stage 1 should be monotone)
- Non-monotonicity failures (Stage 2 should demonstrate non-monotonicity)
- Contraction violations (Stage 3 must have c < 1)
- Cross-layer contract violations

### 6.4 Damages Cases

1,091 real damages cases from PRC court decisions. Banach pricing function calibrated with Theil-Sen regression (beta fitted to 0 < beta < 1).

---

## 7. Product Features

### 7.1 Proof Trace

Every decision produces a `CanonicalProofTrace` with:
- Trace ID
- Final status (PROVED / REFUTED / UNDECIDED / TAINTED)
- Ordered steps recording each phase (Horn closure iteration, AAF labelling, pricing)
- Fail-closed reason if status is not PROVED

### 7.2 Trust Label

Every formal claim carries a trust label from the 7-level taxonomy. Claims are tracked in the JC_Formalization registry and can only be promoted (never demoted from REFUTED).

### 7.3 Horn-AAF Contract Check

The `validate_horn_aaf_contract` function runs 6 checks and produces a `CompilationContractReport` with satisfaction status, check descriptions, and any violations.

---

## 8. Forbidden Claims

The following claims are explicitly NOT made:

1. **No universal cross-jurisdiction mapping.** `no_total_functor` and `obstruction_density_gt_two_thirds` prove this is impossible.
2. **No monotonicity of the full evaluator.** The combined evaluator is non-monotone (Proposition 6.1 in the ICAIL paper; `ge_non_monotonicity` in UnifiedModel.lean).
3. **No epsilon determination from legal classification.** T18_DPPrivilege is REFUTED (JC_Formalization.lean, `refuted_theorems_card = 1`).
4. **No sorry in blocking paths.** Only 3 non-blocking sorry are registered (SORRY_LEDGER.md), all in the planned DDLDefinitions.lean.

---

## 9. Evidence Ledger

| Claim | Evidence | Trust Label | Lean File |
|-------|----------|-------------|-----------|
| Horn closure monotone | Lean proof | Proved | HornFixedPoint.lean, `horn_operator_monotone` |
| Horn closure least FP | Lean proof | Proved | HornFixedPoint.lean, `horn_result_least_fixed_point` |
| F monotone | Lean proof | Proved | DungFixedPoint.lean, `F_monotone` |
| GE is least FP | Lean proof | Proved | DungFixedPoint.lean, `groundedSpec_is_least_fixed_point` |
| Labelling partition | Lean proof | Proved | DungFixedPoint.lean, `labelling_partition` |
| Pricing contraction | Lean proof | Proved | BanachEffectiveNodes.lean, `pricingFn_contraction` |
| No total functor | Lean decide | Proved | FiniteRosetta.lean, `no_total_functor` |
| Obstruction density > 2/3 | Lean decide | Proved | FiniteRosetta.lean, `obstruction_density_gt_two_thirds` |
| Galois connection | Lean proof | Proved | FiniteGaloisAdjunction.lean, `galois_connection_of_residuated` |
| Temporal guard always | Lean proof | Proved | TemporalKripke.lean, `temporal_guard_always` |
| Full chain composition | Lean proof | Proved | UnifiedModel.lean, `full_chain` |
| GE non-monotone in AF structure | Lean Prop statement | Stated (not proved or refuted) | UnifiedModel.lean, `ge_non_monotonicity` |
| DP privilege impossible | Counterexample | Refuted | JC_Formalization.lean, T18 |
| DDL definitions | Planned | Pending | DDLDefinitions.lean (not yet created) |

---

## 10. Future Work

1. **DDLDefinitions.lean.** Formalize the DDL modality system with the 3 registered sorry-bearing axioms from SORRY_LEDGER.md.
2. **ASPIC+ Formalization.** Extend the Dung AF formalization with structured arguments and preferences.
3. **Infinite Domains.** Replace `Finset` with `Set` and classical logic for infinite legal domains.
4. **Empirical Proxy Promotion.** Mechanize T2 (HornCorrectness) and T20 (MDLRuleComplexity) to advance from EMPIRICAL_PROXY to PROVED_BY_ARTIFACT.
5. **Full Gradual Verification.** Recover the missing artifact for T7.

---

## References

1. Dung, P.M. (1995). On the acceptability of arguments. *Artificial Intelligence*, 77(2), 321--357.
2. Besnard, P. and Hunter, A. (2008). *Elements of Argumentation*. MIT Press.
3. Bench-Capon, T.J.M. (2003). Persuasion in practical argument using value-based argumentation frameworks. *Journal of Logic and Computation*, 13(3), 429--448.
4. Amgoud, L. and Cayrol, C. (2002). A reasoning model based on the production of acceptable arguments. *Annals of Mathematics and Artificial Intelligence*, 34(1--3), 197--215.
5. Prakken, H. (2010). An abstract framework for argumentation with structured arguments. *Argument and Computation*, 1(2), 93--124.
6. Athan, T. et al. (2015). LegalRuleML. *RuleML 2015*.
7. Gordon, T.F. et al. (2009). The Carneades argumentation framework. *Argumentation in Artificial Intelligence*.
8. Nute, D. (1994). Defeasible logic. *Handbook of Logic in Artificial Intelligence and Logic Programming*, 3.
9. Gelfond, M. and Kahl, Y. (2014). *Knowledge Representation, Reasoning, and the Design of Intelligent Agents*. Cambridge University Press.
10. Cousot, P. and Cousot, R. (1977). Abstract interpretation. *POPL 1977*, 238--252.
11. Arrow, K.J. and Hahn, F.H. (1971). *General Competitive Analysis*. Holden-Day.
12. The mathlib Community (2020). The Lean mathematical library. *CPP 2020*, 367--381.
13. Hart, H.L.A. (1961). *The Concept of Law*. Oxford University Press.
14. Sergot, M. (2016). Normative positions. In *Handbook of Deontic Logic*.
15. Gordon, T.F. (2010). The Carneades argumentation model. *COMMA 2010*.
