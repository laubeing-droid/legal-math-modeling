# Paper-to-Theory Alignment Matrix

This document maps each paper in the repository to its corresponding theory module(s) and proof artifact(s).

## Alignment Table

| Paper | Theory Module(s) | Proof Artifact(s) |
|-------|------------------|-------------------|
| main.md Ch4 (Horn) | `bounded_horn_correctness.py`, `hypothesis_horn_pbt.py` | `proofs/strict_proof_baseline/p1e_aaf/` |
| main.md Ch5 (AAF) | `argumentation_horn_unification.py` | `proofs/strict_proof_baseline/p1e_aaf/` |
| main.md Ch7 (Kripke) | `temporal_kripke_ltl.py`, `kripke_supersedes_corrects.py` | `proofs/strict_proof_baseline/smt/` |
| main.md Ch8 (Rosetta) | `category_theory_rosetta.py` | `proofs/strict_proof_baseline/p0a_category/` |
| main.md Ch9 (Banach) | `banach_pricing_contraction.py` | `proofs/strict_proof_baseline/p0c_banach/` |
| main.md Ch10 (DP) | `dp_legal_privilege.py` | `proofs/strict_proof_baseline/p0d_privilege_epsilon/` |
| main.md Ch11 (CBL) | `non_interference_cbl.py` | -- |
| main.md Ch12 (Trust) | `model_status.py`, `data_quality_label.py`, `evidence_dependency_manager.py` | -- |
| non_monotonicity.md | `argumentation_horn_unification.py` | `proofs/strict_proof_baseline/p1e_aaf/` |
| dp_impossibility.md | `dp_legal_privilege.py` | `proofs/strict_proof_baseline/p0d_privilege_epsilon/` |
| graph_similarity_topology.md | -- | `proofs/engineering_proof_artifacts/graph_similarity/` |
| multi_ai_formalization.md | -- | `proofs/formal_verification_logs/` |
| argumentation_frameworks.md | `aspic_plus_framework.py` | -- |
| legal_reasoning_paradigms.md | `analogical_reasoning.py`, `precedent_reasoning.py`, `legal_interpretation.py`, `interest_balancing.py` | -- |
| probabilistic_legal_reasoning.md | `bayesian_legal_reasoning.py`, `evidence_evaluation.py`, `probabilistic_damages.py` | -- |
| argument_strength.md | `argument_strength_ordering.py` | -- |
| legal_analogy.md | `analogical_reasoning.py`, `case_retrieval.py` | -- |
| ai_liability_infrastructure.md | `model_status.py`, `evidence_dependency_manager.py` | -- |
| icail_full_paper.md | (all of the above) | (all of the above) |

## Notes

- Papers with `--` in the Proof Artifact column have no dedicated machine-run proof directory; their claims are either structural/analytic or verified inline within the theory module itself.
- Papers with `--` in the Theory Module column are standalone formalization exercises that contribute proof artifacts but do not correspond to a single runnable module.
- `icail_full_paper.md` is the consolidated conference submission that subsumes all papers above.
