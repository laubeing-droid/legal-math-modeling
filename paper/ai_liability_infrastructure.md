# Evidence-Calibrated Trust Labels as AI Liability Infrastructure

**Author:** Legal Math Modeling Research Group

**Keywords:** AI liability, trust labels, evidence calibration, formal verification, Banach fixed-point, Dung argumentation, EU AI Act

---

## Abstract

The EU AI Act classifies entire AI systems by risk tier but provides no mechanism for differentiating the evidentiary status of individual outputs. We present a formal trust-label system that assigns each AI-generated claim one of seven evidence statuses, backed by a dataset-quality provenance registry, a multiplicative evidence-credibility model S(e) = r x i x a, and a Lean 4 formal verification layer with an explicit formal-release boundary. Key results include released Horn/Dung/finite-iteration artifacts, supporting cross-jurisdictional and trust-label artifacts, and public limitations for runtime correctness, Banach pricing, and DDL domain axioms. We define an `advance` operator in the trust-label registry and prove that it preserves domain bounds and cannot revive refuted claims; this operator is a status-governance theorem, not a public claim that pending runtime or DDL work has become production-proven. We map the 7-level label system to EU AI Act conformity-assessment requirements and argue that claim-level trust labels serve as technical documentation for liability allocation under Article 6(2) high-risk classifications.

---

## 1. Introduction

The EU AI Act (Regulation 2024/1689) classifies AI systems into four risk tiers. A high-risk system must undergo conformity assessment, maintain technical documentation, and implement post-market monitoring. However, this classification operates at the system level. When a legal reasoning AI produces claims backed by formal proofs alongside claims produced by pattern matching on synthetic data, the Act's risk tier treats them identically.

Under Article 82, a person who suffers damage from an AI system may claim compensation. But when claims carry heterogeneous evidence quality, the question "which claim caused the damage?" cannot be answered by system-level risk classification alone.

We present a four-layer trust-label infrastructure implemented in Python (labeling and credibility layers) and Lean 4 (formal verification). The system is operational: Python modules register datasets with explicit quality labels, and Lean files contain compiled theorems with stated sorry counts. The system includes an honest accounting: 7 theorems proved, 2 empirically approximated, 1 refuted, and the remainder planned. This honesty is a design goal -- a liability infrastructure that overstates its certainty undermines its purpose.

---

## 2. Formal Definitions

**Definition 1 (Evidence Status).** The 7-element enum `EvidenceStatus` in `model_status.py`:

    {PROVED_BY_EXHAUSTIVE_ENUMERATION, REFUTED_BY_COUNTEREXAMPLE,
     DATA_INSUFFICIENT_FOR_PROOF, TOY_SYNTHETIC_PROOF_ONLY,
     PARTIAL_PROVED, TOOLCHAIN_PENDING, ENGINEERING_BASELINE}

Each claim is a `ModelClaim` dataclass with fields: `claim_id`, `title`, `status`, `data_quality`, `allowed_claim`, `forbidden_claim`, `engineering_action`, `evidence_paths`.

**Definition 2 (Data Quality).** The 5-element enum `DataQuality = {REAL, SYNTHETIC, PROXY, ANNOTATED, UNKNOWN}`. The module `data_quality_label.py` registers 8 datasets via `DataQualityLabel` dataclasses with mandatory `limitations` fields: cn_legal (ANNOTATED, n=56), us_legal (SYNTHETIC, n=100), hk_legal (ANNOTATED, n=30), aaf_legal (SYNTHETIC, n=50), banach_pricing (PROXY, n=200), category_rosetta (ANNOTATED, n=44), dp_privilege (ANNOTATED, n=15), galois_semantics (SYNTHETIC, n=40).

**Definition 3 (Evidence Credibility).** The score function S(e) = r x i x a in `evidence_credibility_axioms.py`, where r (relevance), i (integrity), a (admissibility) each range over [0,1]. Proven properties: EC-1 Zero Property (any dimension zero implies S=0), EC-2 Sub-minimum Bound (S <= min(r,i,a)), EC-3 Independence Boundary (multiplicative form exact iff dimensions conditionally independent), EC-4 Cobb-Douglas Generalization (weighted form S = r^{w_r} x i^{w_i} x a^{w_a} is log-linear for OLS). Encoded formally as T3_EvidenceCredibility with status PROVED_BY_ARTIFACT in `JC_Formalization.lean`.

---

## 3. Formal Verification Results

### 3.1 Theorem Catalogue

`JC_Formalization.lean` defines `CoreTheorem` (T1--T20) with `TheoremMetadata` (status, evidence, domain_bound, sorry_count, axiom_count). Honest accounting:

**Proved (7):** T1_GaloisConnection (`FiniteGaloisAdjunction.lean`, 0 sorry), T3_EvidenceCredibility, T5_TemporalKripke (`TemporalKripke.lean`, 0 sorry), T9_HornDungBridge, T15_CBLNonInterference, T16_CategoryRosetta (`FiniteRosetta.lean`, 0 sorry), T17_BanachContraction (`BanachEffectiveNodes.lean`, 0 sorry). **Empirical proxy (2):** T2_HornCorrectness, T20_MDLRuleComplexity. **Refuted (1):** T18_DPPrivilege (counterexample found). **Remaining 10:** INVALID_CLAIM, PLAN_ONLY, or MISSING_ARTIFACT.

### 3.2 Banach Contraction

`BanachEffectiveNodes.lean` defines pricingFn(x, beta, T) = beta*T + (1-beta)*x. Proved: pricingFn_contraction (Lipschitz constant 1-beta < 1), pricingFn_fixed_point (T is fixed point), pricingFn_unique_fixed_point (uniqueness by algebraic manipulation).

### 3.3 Weighted Sup-Norm

`WeightedSupNorm.lean` defines weightedSupDist(w, x, y) = max_i |x_i - y_i| / w_i on Fin n -> R with strictly positive weights. Proved: nonnegativity, triangle inequality, symmetry, completeness (d=0 iff x=y). All 0 sorry.

### 3.4 Composition Chain

`UnifiedModel.lean` (388 lines, 0 sorry, 0 axiom) proves: Kripke temporal semantics -> Horn forward chaining (horn_lfp with monotonicity) -> Dung AAF grounded extension (dungs_char_fn) -> Banach fixed-point pricing (banach_bounded).

**Theorem (unified_composition_v2).** If argument a is unattacked in the grounded extension, then price(a) <= max(initial, target).

**Theorem (full_chain).** The complete Kripke -> Horn -> AAF -> Banach pipeline is sound.

### 3.5 Cross-Jurisdiction Obstruction

`FiniteRosetta.lean` on 44 annotated entries: CN_ONLY=30, COLLISION=4, ASYMMETRY=3, total obstruction=37. Proved: no_total_functor (entry 0 is CN_ONLY), obstruction_density_gt_two_thirds (37/44 > 2/3).

---

## 4. The Advance Operator

`JC_Formalization.lean` defines `advance` for trust-label governance over theorem metadata. It does not by itself upgrade DDL domain-axiom targets, empirical proxies, or the Python runtime into Lean-proven production correctness.

**Theorem (advance_preserves_domain_bound).** Domain bounds are invariant under advance.

**Theorem (advance_cannot_revive_refuted).** A REFUTED theorem is immune to advance. A counterexample is permanent -- no future toolchain improvement can erase a refutation.

---

## 5. Regulatory Connection: EU AI Act

The EU AI Act requires high-risk AI systems (Article 6(2)) to undergo conformity assessment (Article 43), maintain technical documentation (Annex IV), and implement quality management (Article 17). Trust labels map to these obligations:

- **PROVED_BY_EXHAUSTIVE_ENUMERATION:** Conformity assessment satisfied; proof artifact serves as Annex IV evidence.
- **REFUTED_BY_COUNTEREXAMPLE:** Triggers corrective action under Article 21; counterexample is mandatory disclosure.
- **PARTIAL_PROVED:** Conditional acceptance with limitation disclosure.
- **DATA_INSUFFICIENT_FOR_PROOF:** Non-compliance risk; monitoring required.
- **TOY_SYNTHETIC_PROOF_ONLY:** Cannot support high-risk deployment; explicit limitation in technical file.
- **TOOLCHAIN_PENDING:** Deferred verification with timeline; toolchain dependency in quality management.
- **ENGINEERING_BASELINE:** Minimum documentation only; baseline assessment under Article 9.

Article 9(2) requires "appropriate levels of accuracy, robustness and cybersecurity." Trust labels make this operational: accuracy is not a system-level aggregate but a claim-level evidence status. Under Article 82, when damage results from reliance on a specific claim, the trust label determines the responsible party.

---

## 6. Limitations

1. **No checker executable.** `BanachCertificate.lean` defines a certificate data structure with `verifyCertificate` schema check, but no standalone binary exists. Certificate verification is PLANNED.
2. **No real-world validation.** `bayesian_calibration.py` documents that all 180 calibration claims have positive_control=True (100%), making calibration trivially perfect. This is a proxy.
3. **Refuted claims stay refuted.** T18 (DP privilege) is formally refuted by counterexample.
4. **Empirical proxies are not proofs.** T2 and T20 have status EMPIRICAL_PROXY; they pass tests but lack formal proofs.

---

## References

[1] Regulation (EU) 2024/1689. EU AI Act. Official Journal of the European Union, 2024.
[2] Dung, P.M. "On the Acceptability of Arguments." *Artificial Intelligence*, 77(2):321--357, 1995.
[3] Banach, S. "Sur les operations dans les ensembles abstraits." *Fundamenta Mathematicae*, 3:133--181, 1922.
[4] Galois, E. Manuscript, 1832. Modern ref: Birkhoff, G. *Lattice Theory*. AMS, 1940.
[5] Mitchell, M. et al. "Model Cards for Model Reporting." *FAT*, 2019.
[6] NIST. "AI Risk Management Framework (AI RMF 1.0)." NIST AI 100-1, 2023.
[7] Lean Community. "The Lean 4 Theorem Prover." https://lean-lang.org, 2024.
