# Legal Math Modeling

> 形式化法律推理的数学配套仓库
>
> Companion repo: [juris-calculus](https://github.com/laubeing-droid/juris-calculus) |
> Research framework: [deli-autoresearch](https://github.com/laubeing-droid/deli-autoresearch) |
> License: [CC BY 4.0](LICENSE)

## What This Is

This repository is the **mathematical companion** to [juris-calculus](https://github.com/laubeing-droid/juris-calculus) -- a deterministic symbolic legal reasoning engine operating across PRC, Hong Kong, and US jurisdictions.

It contains:
- A formal mathematical framework for cross-jurisdictional legal reasoning
- 59 runnable Python theory modules with embedded assertions
- Lean 4 formal proofs for the core specification layer
- Z3 SMT verification for constraint-based properties
- A 7-level evidence-calibrated trust label system
- 13 mathematical papers
- Machine-reproducible audit and proof artifacts

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                    User Constraints                             │
│        Jurisdiction + Case Type + Evidence Set + Questions      │
└──────────────────────────┬──────────────────────────────────────┘
                           │
                           ▼
┌─────────────────────────────────────────────────────────────────┐
│              Layer 1: Legal Ontology (L0/L1/L2)                │
│   L0: Agent, Asset, Act, Status, Power, Defect (6 primitives)  │
│   L1: 15 meta-ontological categories                           │
│   L2: 20+ jurisdiction-specific domain concepts                │
│   Source: core_ontology.yaml (1,298 lines)                     │
└──────────────────────────┬──────────────────────────────────────┘
                           │
                           ▼
┌─────────────────────────────────────────────────────────────────┐
│         Layer 2: Two-Stage Reasoning Engine                    │
│                                                                │
│  Stage 1: Horn Closure        Stage 2: Dung AAF               │
│  (forward fact expansion)     (rebuttal + exception handling)  │
│  2,117 PRC rules              Exhaustive for n ≤ 4             │
│  Monotone (proved)            Grounded extension (proved)      │
│                                                                │
│  k ≤ 3: provably safe zone    k ≥ 4: TAINTED (needs review)   │
└──────────────────────────┬──────────────────────────────────────┘
                           │
                           ▼
┌─────────────────────────────────────────────────────────────────┐
│         Layer 3: Evidence-Calibrated Trust Labels              │
│   PROVED → REFUTED → PARTIAL → INSUFFICIENT → TOY → PENDING   │
│   Every claim tracked through its proof lifecycle              │
│   Counterexamples preserved as first-class artifacts           │
└──────────────────────────┬──────────────────────────────────────┘
                           │
                           ▼
┌─────────────────────────────────────────────────────────────────┐
│         Layer 4: Cross-Jurisdiction Collider                   │
│   Tri-Rail: PRC x HK x US parallel reasoning                  │
│   12 conflict classes detected                                 │
│   60 CBL blocking rules (= Bell-LaPadula non-interference)     │
└─────────────────────────────────────────────────────────────────┘
```

## Key Results

These counts track the paper-level 40-claim ledger, not the released
`formal-core-v1` boundary. For the public Lean release boundary
(`39` core theorems, `0 sorry`, `0 custom axiom`), see
[FORMAL_RELEASE_REPORT.md](docs/formal-release/FORMAL_RELEASE_REPORT.md).

| Status | Count | Examples |
|--------|-------|---------|
| **Proved** | 18 | AAF grounded extension, Horn monotonicity, Kripke temporal guard |
| **Refuted** | 10 | DP epsilon determinability, evaluator monotonicity, graph metric |
| **Data insufficient** | 4 | Rosetta real data, Banach real data |
| **Toy only** | 2 | Rosetta toy, Banach scalar |
| **Pending toolchain** | 6 | Lean drafts with `sorry`, SMT pending |

## Formal Core (Lean 4)

The formal core is the **mathematically verified specification layer**:

- **Finite Monotone Iteration Kernel**: general-purpose fixed-point layer (12 theorems)
- **Dung Grounded Extension**: argumentation framework fixed-point (13 theorems)
- **Horn Closure**: forward reasoning closure (10 theorems)

Total: **39 core theorems**, 0 sorry, 0 custom axiom.

Lean is a **proof assistant** (interactive theorem prover). It verifies that mathematical statements are correct by type-checking proof terms. In this project, Lean proves the **mathematical specifications** -- the properties that the reasoning engine should satisfy. The Python implementation passes tests and has certificates, but is not itself formally proved by Lean.

Toolchain: Lean 4.30.0 + Mathlib v4.30.0.

See [proofs/lean/juris_lean/](proofs/lean/juris_lean/) for the Lean workspace.

## Repository Structure

```
legal-math-modeling/
├── paper/                              # 13 mathematical papers
│   ├── main.md                         #   Core paper (13 chapters, KaTeX)
│   ├── main.tex                        #   LaTeX source
│   ├── icail_full_paper.md             #   ICAIL consolidated submission
│   └── ... (12 topic-specific papers)
│
├── theory/                             # 59 Python theory modules
│   ├── model_status.py                 #   Trust label system
│   ├── argumentation_horn_unification.py # Dung AAF + Horn unification
│   ├── bounded_horn_correctness.py     #   Horn correctness proof
│   ├── temporal_kripke_ltl.py          #   Kripke temporal models
│   ├── non_interference_cbl.py         #   CBL non-interference
│   └── ... (54 more modules)
│
├── proofs/                             # Machine-reproducible proofs
│   ├── engineering_proof_artifacts/    #   17 engineering proof artifacts
│   ├── strict_proof_baseline/          #   8 strict baseline proofs
│   ├── lean/juris_lean/               #   Lean 4 formalization (22 files)
│   └── formal_verification_logs/       #   Codex 7-tool-chain audit
│
├── verification/                       # Z3 SMT verification
│   └── verification_engine.py          #   4 checks: consistency, LFP, pi_legal, DP
│
├── data/                               # Legal validation datasets
│   ├── cn_legal/                       #   PRC claims (6 domains)
│   ├── us_legal/                       #   US legal data
│   ├── hk_legal/                       #   Hong Kong legal data
│   ├── aaf_legal/                      #   AAF rebuttal patterns
│   ├── banach_pricing/                 #   Banach pricing data
│   └── external/                       #   COMPAS, LegalBench, SPC
│
└── docs/                               # Documentation
    ├── formal-release/                 #   Release boundary (canonical truth)
    ├── final-closure/                  #   Closure and audit summary
    ├── audit/                          #   Theorem matrix, proof ledger
    ├── modeling/                       #   8 modeling documents
    └── history/                        #   Archival development logs
```

## Quick Start

```bash
git clone https://github.com/laubeing-droid/legal-math-modeling.git
cd legal-math-modeling
pip install -r requirements.txt

# Run the trust label system
python -m theory

# Run Z3 verification (4 checks)
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

1. [FORMAL_RELEASE_REPORT.md](docs/formal-release/FORMAL_RELEASE_REPORT.md)
2. [FORBIDDEN_CLAIMS.md](docs/formal-release/FORBIDDEN_CLAIMS.md)
3. [final-report.md](docs/final-closure/final-report.md)
4. [theorem_status_matrix.md](docs/audit/theorem_status_matrix.md)
5. [next-stage-spec-first-roadmap.md](docs/analysis/next-stage-spec-first-roadmap.md)
6. [contract-breach-vertical-slice.md](docs/analysis/contract-breach-vertical-slice.md)
7. [jc-transition-gate-status.md](docs/analysis/jc-transition-gate-status.md)

The current transition rule is:

- this repository remains the specification and oracle source
- `juris-calculus` should become the main engineering focus only after the
  canonical semantic types, minimal DDL core, Horn -> AAF contract, reference
  interpreter, and differential-validation boundary are closed

## Cross-Repo Relationship

| Repo | Role | Branch | Head |
|------|------|--------|------|
| `legal-math-modeling` (this repo) | Mathematical companion | `master` | `5f4d635` |
| `juris-calculus` | Production runtime | `main` | `c18b478` |
| `deli-autoresearch` | Research orchestrator | `main` | `e3e1c1f` |

- `legal-math-modeling` proves the **specifications**
- `juris-calculus` implements the **runtime**
- `deli-autoresearch` orchestrates **long-horizon research**

## License

[CC BY 4.0](LICENSE)
