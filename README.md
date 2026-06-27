# Legal Math Modeling

> Formal mathematical companion for cross-jurisdictional legal reasoning.
>
> Companion repo: [juris-calculus](https://github.com/laubeing-droid/juris-calculus) |
> Research framework: [deli-autoresearch](https://github.com/laubeing-droid/deli-autoresearch) |
> License: [CC BY 4.0](LICENSE)

## What This Is

This repository is the **mathematical specification companion** to
[juris-calculus](https://github.com/laubeing-droid/juris-calculus) -- a
deterministic symbolic legal reasoning engine operating across PRC, Hong Kong,
and US jurisdictions.

It contains:

- A formal mathematical framework for cross-jurisdictional legal reasoning
- 59 runnable Python theory modules with embedded assertions
- Lean 4 formal proofs for the core specification layer (94 verified results: 43 core + 51 supporting)
- Z3 SMT verification for constraint-based properties
- A 7-level evidence-calibrated trust label system
- 13 mathematical papers
- Machine-reproducible audit and proof artifacts

## Architecture

```
+-------------------------------------------------------------------+
|                      User Constraints                             |
|      Jurisdiction + Case Type + Evidence Set + Questions          |
+----------------------------+--------------------------------------+
                             |
                             v
+-------------------------------------------------------------------+
|          Layer 1: Legal Ontology (L0/L1/L2)                      |
|  L0: Agent, Asset, Act, Status, Power, Defect (6 primitives)     |
|  L1: 15 meta-ontological categories                              |
|  L2: 20+ jurisdiction-specific domain concepts                   |
|  Source: core_ontology.yaml                                       |
+----------------------------+--------------------------------------+
                             |
                             v
+-------------------------------------------------------------------+
|         Layer 2: Two-Stage Reasoning Engine                      |
|                                                                  |
|  Stage 1: Horn Closure       Stage 2: Dung AAF                  |
|  (forward fact expansion)    (rebuttal + exception handling)     |
|  Monotone (proved)           Grounded extension (proved)         |
+----------------------------+--------------------------------------+
                             |
                             v
+-------------------------------------------------------------------+
|         Layer 3: Evidence-Calibrated Trust Labels                |
|  PROVED > REFUTED > PARTIAL > INSUFFICIENT > TOY > PENDING       |
|  Every claim tracked through its proof lifecycle                 |
|  Counterexamples preserved as first-class artifacts              |
+----------------------------+--------------------------------------+
                             |
                             v
+-------------------------------------------------------------------+
|         Layer 4: Cross-Jurisdiction Collider                     |
|  Tri-Rail: PRC x HK x US parallel reasoning                     |
|  12 conflict classes detected                                    |
|  60 CBL blocking rules (= Bell-LaPadula non-interference)        |
+-------------------------------------------------------------------+
```

## Formal Core (Lean 4)

The formal core is the **mathematically verified specification layer**:

- **Finite Monotone Iteration Kernel** -- general-purpose fixed-point layer
- **Dung Grounded Extension** -- argumentation framework fixed-point
- **Horn Closure** -- forward reasoning closure
- **Weighted Sup-Norm Completeness** -- metric foundation for contraction arguments

### Build Status

| Metric | Value |
|--------|-------|
| `lake build JurisLean` | 2954 jobs, 0 error, 0 sorry |
| Core theorems | 43 |
| Supporting results | 51 |
| Total verified results | 94 |
| Deferred axioms | 3 (non-blocking, registered in SORRY_LEDGER.md) |
| Toolchain | Lean 4.30.0 + Mathlib v4.30.0 |

Canonical machine-readable source: [theorem_manifest.json](docs/formal-release/theorem_manifest.json)

### Core Theorem Distribution

| File | Count | Key Theorems |
|------|-------|-------------|
| DungFixedPoint.lean | 17 | `F_monotone`, `grounded_eq_groundedSpec`, `finite_termination`, `grounded_is_least_fixed_point`, `grounded_is_least_complete`, `self_attack_precise_theorem` |
| HornFixedPoint.lean | 10 | `horn_operator_monotone`, `horn_finite_termination`, `horn_result_fixed_point`, `horn_soundness`, `horn_completeness`, `horn_result_is_minimal_model` |
| FiniteMonotoneIteration.lean | 9 | `iter_mono`, `iter_stable`, `iter_card_lt_of_ne`, `exists_fixpoint_le_card`, `fixed_at_card` |
| WeightedSupNorm.lean | 4 | `weightedSupDist_triangle`, `weightedSupDist_symm`, `weightedSupDist_complete` |
| HornDefinitions.lean | 2 | `TH_monotone`, `TH_subset_univ` |
| ContractionCondition.lean | 1 | `lipschitz_coupling_implies_weighted_contraction` |

### Lean Source Files (25)

The Lean workspace contains the following files in `proofs/lean/juris_lean/JurisLean/`:

`AxiomAudit.lean`, `BanachCertificate.lean`, `BanachComplete.lean`, `BanachContraction.lean`, `BanachEffectiveNodes.lean`, `BanachFixedPoint.lean`, `BanachScratch.lean`, `BanachWeightedNorm.lean`, `Basic.lean`, `ContractionCondition.lean`, `DungAAF.lean`, `DungDefinitions.lean`, `DungFixedPoint.lean`, `FiniteGaloisAdjunction.lean`, `FiniteMonotoneIteration.lean`, `FiniteRosetta.lean`, `HornDefinitions.lean`, `HornFixedPoint.lean`, `HornOperationalRefinement.lean`, `JC_Formalization.lean`, `ScratchApi.lean`, `SupZeroLemma.lean`, `TemporalKripke.lean`, `UnifiedModel.lean`, `WeightedSupNorm.lean`

Lean is a **proof assistant** (interactive theorem prover). It verifies mathematical statements by type-checking proof terms. In this project, Lean proves the **mathematical specifications** -- the properties that the reasoning engine should satisfy. The Python implementation passes tests and has certificates, but is not itself formally proved by Lean.

See [proofs/lean/juris_lean/](proofs/lean/juris_lean/) for the Lean workspace.

## Spec-First Transition Gates

| Gate | Status | Document |
|------|--------|----------|
| M1: Canonical Schema | SUBSTANTIAL_PARTIAL | [canonical_legal_schema.md](docs/spec/canonical_legal_schema.md) |
| M2: DDL Minimal Core | SUBSTANTIAL_PARTIAL | [ddl_minimal_core.md](docs/spec/ddl_minimal_core.md) |
| M3: Horn-to-AAF Contract | SUBSTANTIAL_PARTIAL | [horn_to_aaf_contract.md](docs/spec/horn_to_aaf_contract.md) |
| M4: Certificate/Checker Boundary | PARTIAL | [certificate_checker_boundary.md](docs/spec/certificate_checker_boundary.md) |
| M5: Unified Stopping Statement | CLOSED | [FORMAL_RELEASE_REPORT.md](docs/formal-release/FORMAL_RELEASE_REPORT.md) |

## Canonical Types (11)

`LegalFact`, `LegalRule`, `LegalNorm`, `LegalClaim`, `Argument`, `Attack`, `Priority`, `Violation`, `Reparation`, `DecisionStatus`, `ProofTrace`

## DDL Modalities

4 modalities: OBLIGATION, PROHIBITION, PERMISSION, CONSTITUTIVE.
4 repair modes. 3 exception classes.

Canonical Python source: `theory/canonical_semantics.py` (type definitions authoritative)

## Repository Structure

```
legal-math-modeling/
+-- paper/                              # 13 mathematical papers
|   +-- main.md                         #   Core paper (13 chapters, KaTeX)
|   +-- main.tex                        #   LaTeX source
|   +-- icail_full_paper.md             #   ICAIL consolidated submission
|   +-- ... (12 topic-specific papers)
|
+-- theory/                             # 59 Python theory modules
|   +-- canonical_semantics.py          #   Canonical type definitions (authoritative)
|   +-- model_status.py                 #   Trust label system
|   +-- argumentation_horn_unification.py # Dung AAF + Horn unification
|   +-- bounded_horn_correctness.py     #   Horn correctness proof
|   +-- temporal_kripke_ltl.py          #   Kripke temporal models
|   +-- non_interference_cbl.py         #   CBL non-interference
|   +-- ... (53 more modules)
|
+-- proofs/                             # Machine-reproducible proofs
|   +-- engineering_proof_artifacts/    #   Engineering proof artifacts
|   +-- strict_proof_baseline/          #   Strict baseline proofs
|   +-- lean/juris_lean/JurisLean/     #   Lean 4 formalization (25 files)
|   +-- formal_verification_logs/       #   Codex 7-tool-chain audit
|
+-- verification/                       # Z3 SMT verification
|   +-- verification_engine.py          #   Checks: consistency, LFP, pi_legal, DP
|
+-- data/                               # Legal validation datasets
|   +-- cn_legal/                       #   PRC claims (6 domains)
|   +-- us_legal/                       #   US legal data
|   +-- hk_legal/                       #   Hong Kong legal data
|   +-- aaf_legal/                      #   AAF rebuttal patterns
|   +-- banach_pricing/                 #   Banach pricing data
|   +-- external/                       #   COMPAS, LegalBench, SPC
|
+-- docs/                               # Documentation
    +-- formal-release/                 #   Release boundary (canonical truth)
    +-- final-closure/                  #   Closure and audit summary
    +-- audit/                          #   Theorem matrix, proof ledger
    +-- modeling/                       #   Modeling documents
    +-- history/                        #   Archival development logs
```

## Quick Start

```bash
git clone https://github.com/laubeing-droid/legal-math-modeling.git
cd legal-math-modeling
pip install -r requirements.txt

# Run the trust label system
python -m theory

# Run Z3 verification
python verification/verification_engine.py

# Run adversarial tests
python -m pytest proofs/engineering_proof_artifacts/adversarial/

# Run all strict proofs
python proofs/strict_proof_baseline/run_all_proofs.py

# Build Lean formalization (requires Lean 4 + Mathlib)
cd proofs/lean/juris_lean && lake build
```

## Read This First

For current truth, read in this order:

1. [FORMAL_RELEASE_REPORT.md](docs/formal-release/FORMAL_RELEASE_REPORT.md) -- release boundary and build evidence
2. [theorem_manifest.json](docs/formal-release/theorem_manifest.json) -- canonical machine-readable theorem list
3. [canonical_legal_schema.md](docs/spec/canonical_legal_schema.md) -- M1 gate
4. [ddl_minimal_core.md](docs/spec/ddl_minimal_core.md) -- M2 gate
5. [horn_to_aaf_contract.md](docs/spec/horn_to_aaf_contract.md) -- M3 gate
6. [certificate_checker_boundary.md](docs/spec/certificate_checker_boundary.md) -- M4 gate
7. [FORBIDDEN_CLAIMS.md](docs/formal-release/FORBIDDEN_CLAIMS.md) -- claims that cannot be made
8. [ALLOWED_CLAIMS.md](docs/formal-release/ALLOWED_CLAIMS.md) -- claims that can be made
9. [SORRY_LEDGER.md](SORRY_LEDGER.md) -- deferred axiom tracking

## Repository Role

This repository is the **specification source and formalization boundary**
for `juris-calculus`. It is NOT the runtime implementation.

**Current status:** `spec-first-transition-ready` -- the five gates
(canonical schema, DDL minimal core, Horn-to-AAF contract, certificate/checker
boundary, unified stopping statement) are acceptably closed for transition.

**After this point:** main engineering effort shifts to `juris-calculus`.
New math work in this repo only as "support for JC new capabilities" --
not as independent research expansion.

**Public boundary:** See [PUBLIC_PRIVATE_BOUNDARY.md](docs/disclosure/PUBLIC_PRIVATE_BOUNDARY.md).
This repo continues public. `juris-calculus` public scope is narrowed to
the auditable kernel; commercial layers stop expanding publicly.

## Precise Claim Language

**For this repository:**
> The finite monotone system, Dung grounded fixed-point layer, and finite
> Horn closure layer have completed repository-level release sealing. Banach
> remains an independent incomplete research track.

**For the engineering layer:**
> Lean has proved the mathematical specification boundary. The Python
> engineering implementation is validated through tests, certificate checks,
> and refinement baselines, but has not been formally proved as a whole by
> this repository.

**For Banach:**
> Banach-related work is retained as an archived research track and is not
> part of `formal-core-v1`.

**For UnifiedModel:**
> `UnifiedModel.lean` is an independent composition proof (Kripke -> Horn ->
> AAF -> Banach). It is not on the blocking path and does not represent
> production end-to-end correctness.

## Cross-Repo Relationship

| Repo | Role | Branch |
|------|------|--------|
| `legal-math-modeling` (this repo) | Mathematical companion | `master` |
| `juris-calculus` | Production runtime | `main` |
| `deli-autoresearch` | Research orchestrator | `main` |

- `legal-math-modeling` proves the **specifications**
- `juris-calculus` implements the **runtime**
- `deli-autoresearch` orchestrates **long-horizon research**

## License

[CC BY 4.0](LICENSE)
