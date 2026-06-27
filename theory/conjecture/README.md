# Conjectures

Files in this directory contain mathematical conjectures awaiting empirical validation or formal proof.

## Status

Conjectures in this directory are **not** part of the 94 formally verified theorems. They represent research directions that may eventually be formalized.

## Current Formal Baseline

The project's verified mathematical core consists of:

- 94 Lean theorems (43 core + 51 supporting), 0 sorry
- 25 Lean source files
- `lake build JurisLean` producing 2954 jobs
- AxiomAudit passing via `lake build +JurisLean.AxiomAudit`

## Conjecture Lifecycle

1. **Proposed**: Initial mathematical claim with informal justification
2. **Explored**: Python module in `theory/` with computational evidence
3. **Formalized**: Lean proof in `proofs/lean/juris_lean/`
4. **Verified**: Part of the 94-theorem core with 0 sorry

## Key Areas

| Area | Formalized | Exploring |
|------|------------|-----------|
| Horn closure monotonicity | HornFixedPoint.lean | Operational variants |
| Dung grounded extension | DungFixedPoint.lean | Argument schemes |
| Banach fixed point | BanachFixedPoint.lean | Complete space bridge |
| Finite Galois adjunction | FiniteGaloisAdjunction.lean | Infinite extensions |
| Finite Rosetta | FiniteRosetta.lean | Cross-jurisdiction mapping |
| Temporal Kripke | TemporalKripke.lean | Modal extensions |

## Rules

- Conjectures must not be cited as proven theorems
- Conjectures must be clearly separated from the 94 verified theorems
- Conjectures promoted to formal proof must be audited via AxiomAudit
