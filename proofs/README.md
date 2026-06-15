# Proofs — Machine-Run Formal Verification Artifacts

This directory contains all machine-reproducible proof scripts and their outputs.

## Structure

| Directory | Source | Content |
|-----------|--------|---------|
| `strict_proof_baseline/` | Kimi strict math proof rework (2026-06-11) | Canonical baseline: 8/8 runnable proofs pass, 3 Lean PENDING |
| `engineering_proof_artifacts/` | Kimi engineering delivery (2026-06-11) | 17 proof artifacts: 7 exhaustive, 2 symbolic, 3 refuted, 5 pending |
| `formal_verification_logs/` | Codex formal verification (2026-06-09) | 7-tool-chain experiment plan and audit reports |

## Re-run Instructions

### Python proofs (no external tools needed)

```bash
cd strict_proof_baseline
python run_all_proofs.py
# Expected: 8/8 runnable proofs/refutations pass
```

### With Z3 (SMT proofs)

```bash
pip install z3-solver
python strict_proof_baseline/smt/cn_privilege_lattice_z3.py
# Expected: UNSAT (no monotone epsilon exists)
```

### With Lean 4 (requires lake + Mathlib)

```bash
cd strict_proof_baseline/lean
lake build
# Note: contains `sorry` placeholders — not yet verified
```

## Trust Labels

Each proof artifact carries a trust label. See `../docs/audit/trust_label_schema.json` for the formal schema.

| Label | Confidence | Meaning |
|-------|-----------|---------|
| EXHAUSTIVE_FINITE_PROOF | HIGH | All cases enumerated |
| SMT_PROVED_FINITE | HIGH | SMT solver confirms UNSAT |
| SYMBOLIC_PROVED | HIGH | SymPy analytic proof |
| LEAN_PROVED | VERY_HIGH | Lean 4 verified (no `sorry`) |
| REFUTED | VERY_HIGH | Explicit counterexample |
| PENDING_TOOLCHAIN | UNKNOWN | Script exists, toolchain not available |
