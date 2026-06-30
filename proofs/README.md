# Proofs — Machine-Reproducible Proof Artifacts

This directory contains all machine-reproducible proof artifacts for the legal-math-modeling project. Every artifact is designed to be re-executed independently, producing deterministic results across machines.

## Structure

| Directory | Role | Content |
|-----------|------|---------|
| `strict_proof_baseline/` | Canonical Lean proofs | Lean 4 formalization: 94 theorems, 0 `sorry`, full `lake build` pass (2954 jobs) |
| `engineering_proof_artifacts/` | Complementary verification | Python exhaustive proofs, Z3 SMT proofs, Hypothesis property-based tests |
| `formal_verification_logs/` | Audit infrastructure | Experiment plan, trust-label audit reports, CI verification logs |

## Re-run Instructions

### Python proofs (no external tools needed)

```bash
cd strict_proof_baseline
python run_all_proofs.py
# Expected: all runnable proofs/refutations pass
```

### Z3 SMT proofs

```bash
pip install z3-solver
python strict_proof_baseline/smt/cn_privilege_lattice_z3.py
# Expected: UNSAT (no monotone epsilon exists)
```

### Lean 4 (`lake build JurisLean`)

```bash
cd proofs/lean/juris_lean
lake build
# Expected: 2954 jobs, 0 sorry, 0 errors
```

## Trust Labels

Each proof artifact carries a trust label indicating its verification strength. See `../docs/audit/trust_label_schema.json` for the formal schema.

| Label | Confidence | Meaning |
|-------|-----------|---------|
| `EXHAUSTIVE_FINITE_PROOF` | HIGH | All finite cases enumerated and verified |
| `SMT_PROVED_FINITE` | HIGH | SMT solver confirms UNSAT/validity over bounded domain |
| `SYMBOLIC_PROVED` | HIGH | SymPy analytic proof with closed-form verification |
| `LEAN_PROVED` | VERY_HIGH | Lean 4 verified, 94 theorems, 0 `sorry`, 0 custom axiom |
| `REFUTED` | VERY_HIGH | Explicit counterexample provided and validated |
| `TOOLCHAIN_PENDING` | UNKNOWN | Script exists but required toolchain not yet available |
