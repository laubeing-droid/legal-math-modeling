# Codex Handoff: Code Elevation Task Book

Date: 2026-06-11

## 1. Current State

The mathematical model has been upgraded from early drafts to an evidence-calibrated baseline. The next phase is not to continue writing proof reports, but to enter code elevation.

The verified formal state is:

- **94 unique theorems** across 25 Lean files, **0 sorry**
- `lake build JurisLean` passes 2954 jobs with 0 errors
- **JC_Formalization.lean** status register: proved_theorems_card=7, empirical_proxy_card=2, refuted_theorems_card=1, pending_theorems_card=10
- **5 gates:** M1-M4 SUBSTANTIAL_PARTIAL/PARTIAL, M5 CLOSED

## 2. Handoff Inputs

1. `theory/model_status.py`
2. `proofs/lean/juris_lean/JurisLean/JC_Formalization.lean`
3. `proofs/engineering_proof_artifacts/` (17 proof artifacts)
4. `data/cn_legal/` (structured claims and statutes)
5. `data/aaf_legal/` (AAF validation data)
6. `data/benchmarks/multi_model_cases.jsonl` (13 benchmark cases)

## 3. Code Elevation P0

1. Implement `EvidenceStatus` / `TrustLabel` unified enum.
2. Split evaluator:
   - `horn_closure`
   - `build_attack_graph`
   - `grounded_extension`
3. Add source manifest validator.
4. Add pricing data-quality gate.
5. Add DP policy loader.

## 4. Non-Violable Boundaries

1. Do not label a toy proof as a real proof.
2. Do not label fee_schedule as real_timesheet.
3. Do not derive epsilon automatically from legal privilege.
4. Do not label the original evaluator as monotone.
5. Do not label a Lean draft as a Lean proof (0 sorry is required).
6. Do not reference ghost Lean files (e.g., LegalSyntax.lean, DDLDefinitions.lean) as existing.

## 5. Acceptance Commands

Post-elevation verification must include:

```bash
python -m theory --summary
python run_all_math_proofs.py
python run_legal_validation_experiments.py
```

And must add:

1. Evaluator nonmonotone counterexample regression.
2. AAF 100-case fixture validation.
3. Pricing proxy downgrade test.
4. DP epsilon policy test.
5. Lean: `lake build JurisLean` must remain 0 errors, 0 sorry.
