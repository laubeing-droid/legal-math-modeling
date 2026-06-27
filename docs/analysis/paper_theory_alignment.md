# Paper-to-Theory Alignment Matrix

This document maps each paper in the repository to its corresponding theory module(s) and proof artifact(s).

## Alignment Table

| Paper | Theory Module(s) | Proof Artifact(s) |
|-------|------------------|-------------------|
| main.md Ch4 (Horn) | `bounded_horn_correctness.py`, `hypothesis_horn_pbt.py` | `proofs/strict_proof_baseline/p1e_aaf/`, `HornFixedPoint.lean` |
| main.md Ch5 (AAF) | `argumentation_horn_unification.py` | `proofs/strict_proof_baseline/p1e_aaf/`, `DungFixedPoint.lean` |
| main.md Ch7 (Kripke) | `temporal_kripke_ltl.py`, `kripke_supersedes_corrects.py` | `proofs/strict_proof_baseline/smt/`, `TemporalKripke.lean` |
| main.md Ch8 (Rosetta) | `category_theory_rosetta.py` | `proofs/strict_proof_baseline/p0a_category/`, `FiniteRosetta.lean` |
| main.md Ch9 (Banach) | `banach_pricing_contraction.py` | `proofs/strict_proof_baseline/p0c_banach/`, `BanachEffectiveNodes.lean` |
| main.md Ch10 (DP) | `dp_legal_privilege.py` | `proofs/strict_proof_baseline/p0d_privilege_epsilon/` |
| main.md Ch11 (CBL) | `non_interference_cbl.py` | -- |
| main.md Ch12 (Trust) | `model_status.py`, `data_quality_label.py`, `evidence_dependency_manager.py` | `JC_Formalization.lean` |
| non_monotonicity.md | `argumentation_horn_unification.py` | `proofs/strict_proof_baseline/p1e_aaf/` |
| dp_impossibility.md | `dp_legal_privilege.py` | `proofs/strict_proof_baseline/p0d_privilege_epsilon/` |
| graph_similarity_topology.md | -- | `proofs/engineering_proof_artifacts/graph_similarity/` |
| multi_ai_formalization.md | -- | `proofs/formal_verification_logs/` |
| argumentation_frameworks.md | `aspic_plus_framework.py` | `DungAAF.lean` |
| legal_reasoning_paradigms.md | `analogical_reasoning.py`, `precedent_reasoning.py`, `legal_interpretation.py`, `interest_balancing.py` | -- |
| probabilistic_legal_reasoning.md | `bayesian_legal_reasoning.py`, `evidence_evaluation.py`, `probabilistic_damages.py` | -- |
| argument_strength.md | `argument_strength_ordering.py` | -- |
| legal_analogy.md | `analogical_reasoning.py`, `case_retrieval.py` | -- |
| ai_liability_infrastructure.md | `model_status.py`, `evidence_dependency_manager.py` | `JC_Formalization.lean` |
| icail_full_paper.md | (all of the above) | (all of the above) |

## Lean Formalization Coverage

The following Lean files in `proofs/lean/juris_lean/JurisLean/` provide formal proofs for the core paper chapters:

| Lean File | Paper Chapter | Theorems |
|---|---|---|
| `HornFixedPoint.lean` | Ch4 (Horn) | 10 theorems (monotonicity, termination, soundness, completeness, minimal model) |
| `DungFixedPoint.lean` | Ch5 (AAF) | 13 theorems (monotonicity, termination, grounded fixed point, labelling, soundness) |
| `TemporalKripke.lean` | Ch7 (Kripke) | 2 theorems (temporal guard, litigation guard) |
| `FiniteRosetta.lean` | Ch8 (Rosetta) | 8 theorems (obstruction analysis, no total functor) |
| `BanachEffectiveNodes.lean` | Ch9 (Banach) | 3 theorems (contraction, fixed point, uniqueness) |
| `UnifiedModel.lean` | Multiple | 11 theorems (full chain, composition, soundness) |
| `JC_Formalization.lean` | Ch12 (Trust) | 6 theorems (status register, advance properties) |

## Notes

- Papers with `--` in the Proof Artifact column have no dedicated machine-run proof directory; their claims are either structural/analytic or verified inline within the theory module itself.
- Papers with `--` in the Theory Module column are standalone formalization exercises that contribute proof artifacts but do not correspond to a single runnable module.
- `icail_full_paper.md` is the consolidated conference submission that subsumes all papers above.
- The Lean formalization adds 94 theorems (43 core + 51 supporting) with 0 sorry across 25 files.
