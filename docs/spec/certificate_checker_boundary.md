# Certificate / Checker Boundary — Frozen Specification

**Date:** 2026-06-28
**Status:** FROZEN (spec-first-transition-ready)
**Gate M4:** PARTIAL
**Authority:** `legal-math-modeling` (this repo)
**Implementation:** `juris-calculus` runtime checker

---

## 1. Purpose

This document freezes the **boundary between what is certified and what is
checked** in the JC runtime. A certificate is a machine-readable trace of the
reasoning pipeline. A checker is an independent verifier that validates the
certificate against the frozen contracts.

The principle: **prove once, check many**. The math repo proves the
specifications. The runtime produces certificates. The checker verifies
certificates without re-running the proofs.

---

## 2. Certificate Structure (ProofTrace)

A certificate is a `CanonicalProofTrace`:

```
ProofTrace:
  trace_id: str               -> unique identifier
  status: DecisionStatus      -> PROVED / REFUTED / UNDECIDED / TAINTED
  steps: [ProofStep]          -> ordered sequence of reasoning steps
  fail_closed_reason: str?    -> why the result was TAINTED (if applicable)
```

Each step is a `CanonicalProofStep`:

```
ProofStep:
  step_index: int             -> position in the trace
  phase: str                  -> which pipeline stage produced this step
  event: str                  -> what happened
  payload: dict               -> stage-specific data
```

### 2.1 Pipeline Phases

| Phase | Description | Steps produced |
|-------|-------------|----------------|
| `horn` | Forward-chaining closure | Iteration events, derived facts, blocked claims |
| `contract` | Horn->AAF contract validation | Checks passed / failed |
| `argument` | Argument construction | Arguments built from closure |
| `attack` | Attack graph construction | Rebuttal, exception, priority attacks |
| `grounded` | Grounded extension computation | Accepted / rejected / undecided arguments |
| `decision` | Final status assignment | DecisionStatus per argument |

### 2.2 Contract Step (from `extract_contract_steps`)

The contract validation step is produced by `horn_aaf_contract.py`:

```python
def extract_contract_steps(report: CompilationContractReport) -> Tuple[CanonicalProofStep, ...]
```

Each check produces a `check_passed` step; each violation produces a
`check_failed` step. The checker MUST reject any trace with `check_failed`
steps.

---

## 3. DecisionStatus and TAINTED Semantics

```
DecisionStatus:
  PROVED    -> argument is in the grounded extension (accepted)
  REFUTED   -> argument is attacked by an accepted argument
  UNDECIDED -> neither accepted nor refuted (incomplete information)
  TAINTED   -> fail-closed: always rejected by checker
```

### 3.1 When TAINTED Applies

| Condition | Status |
|-----------|--------|
| Attack count <= 3, grounded extension computed | PROVED or REFUTED |
| Attack count >= 4 | TAINTED (fail-closed) |
| Contract validation failed | TAINTED (fail-closed) |
| Missing required fields | TAINTED (fail-closed) |
| Unsupported attack kind | TAINTED (fail-closed) |

### 3.2 Fail-Closed Rule

TAINTED is **always rejected** by the checker. The checker does not attempt
to "recover" a tainted result. The user must review the case manually.

This is the critical safety property: **if the system is unsure, it says so.**

---

## 4. Checker Responsibilities

The checker is an **independent verifier** that runs on the certificate
(the ProofTrace) without re-running the reasoning pipeline.

### 4.1 What the Checker Verifies

| Check | Rejects if | Severity |
|-------|-----------|----------|
| Trace has all required fields | Missing trace_id, status, or steps | FATAL -> TAINTED |
| Steps are sequentially indexed | Step indices are not 0, 1, 2, ... | FATAL -> TAINTED |
| Contract steps all passed | Any `check_failed` step present | FATAL -> TAINTED |
| DecisionStatus is valid enum | Status not in {PROVED, REFUTED, UNDECIDED, TAINTED} | FATAL -> TAINTED |
| Grounded extension is consistent | Accepted argument is attacked by another accepted argument | FATAL -> TAINTED |
| Attack count classification | Attack count >= 4 but status != TAINTED | FATAL -> TAINTED |
| Fail-closed reason present | Status = TAINTED but no fail_closed_reason | WARNING |

### 4.2 What the Checker Does NOT Verify

- The checker does NOT re-derive facts from rules (that is the Horn layer's job)
- The checker does NOT re-compute the grounded extension (that is the AAF layer's job)
- The checker does NOT validate the input facts/rules (that is the parser's job)
- The checker does NOT check cross-jurisdiction conflicts (that is the CBL layer's job)

### 4.3 Checker Output

```
CheckerResult:
  passed: bool               -> True if all checks pass
  status: DecisionStatus     -> The certified status (may be TAINTED if checks failed)
  violations: [str]          -> Human-readable list of failures
  warnings: [str]            -> Non-fatal issues
```

---

## 5. Lean-Proven vs Contract-Only Boundary

### 5.1 Lean-Proven (Mathematical Guarantee) — Existing Files

The following properties ARE Lean-proven in files that exist in this repo.
The Lean build passes with 0 errors and 0 sorry (`lake build JurisLean`).

| Property | Theorem | File |
|----------|---------|------|
| Grounded extension exists and is unique | `groundedSpec_unique_least_fixed_point` | `DungFixedPoint.lean` |
| Grounded extension is a fixed point | `grounded_is_fixed_point` | `DungFixedPoint.lean` |
| Grounded extension is the least fixed point | `grounded_is_least_fixed_point` | `DungFixedPoint.lean` |
| Grounded specification equals computed | `grounded_eq_groundedSpec` | `DungFixedPoint.lean` |
| Finite termination of grounded computation | `finite_termination` | `DungFixedPoint.lean` |
| Iteration bounded by cardinality | `iteration_bound` | `DungFixedPoint.lean` |
| IN arguments are sound | `in_soundness` | `DungFixedPoint.lean` |
| OUT arguments are sound | `out_soundness` | `DungFixedPoint.lean` |
| Undecided characterization | `undecided_characterization` | `DungFixedPoint.lean` |
| Self-attack excluded from grounded | `self_attack_not_in_grounded` | `DungFixedPoint.lean` |
| Horn operator monotone | `horn_operator_monotone` | `HornFixedPoint.lean` |
| Horn finite termination | `horn_finite_termination` | `HornFixedPoint.lean` |
| Horn result is least fixed point | `horn_result_least_fixed_point` | `HornFixedPoint.lean` |
| Horn soundness | `horn_soundness` | `HornFixedPoint.lean` |
| Horn completeness | `horn_completeness` | `HornFixedPoint.lean` |
| Horn result is minimal model | `horn_result_is_minimal_model` | `HornFixedPoint.lean` |
| Finite monotone iteration convergence | `exists_fixpoint_le_card` | `FiniteMonotoneIteration.lean` |
| Fixed point reached at cardinality | `fixed_at_card` | `FiniteMonotoneIteration.lean` |

All dependencies are on Lean 4 built-in axioms only: `propext`, `Classical.choice`, `Quot.sound`.
No project-defined axioms in the core boundary.

### 5.2 PLANNED Lean Formalization (Files Do Not Yet Exist)

| Property | Target File | Status |
|----------|------------|--------|
| Certificate checker soundness | `CertificateChecker.lean` | PLANNED — file does not exist |
| Reparation modes well-defined | `DDLDefinitions.lean` | PLANNED — file does not exist |
| Norm-violation bridge axioms | `DDLDefinitions.lean` | PLANNED — 3 deferred domain axioms |

The 3 deferred domain axioms registered in `SORRY_LEDGER.md`:
- `violation_implies_norm_active`
- `permission_no_direct_violation`
- `constitutive_no_direct_violation`

These are non-blocking. They reflect the RuleId != NormId structural gap.

### 5.3 Contract-Only (Engineering Guarantee, Not Lean-Proven)

| Property | Enforcement |
|----------|------------|
| Arguments trace to closure facts | `validate_horn_aaf_contract()` |
| Attacks refer to known arguments | `validate_horn_aaf_contract()` |
| Exception attacks carry defeat direction | `validate_horn_aaf_contract()` |
| Priority defeat is explicit in AAF | `validate_horn_aaf_contract()` |
| Proof trace is well-formed | Checker validation (this document) |
| TAINTED is always rejected | Checker implementation |
| Four-stage pipeline composition | Engineering integration, not formal proof |

### 5.4 What "Contract-Only" Means

A contract-only property is **enforced by code and tests**, not by a Lean
proof. If the code has a bug, the property can be violated. This is the
formalization gap that separates "mathematically proven" from "engineering
verified."

The goal is to keep this gap **visible and small**, not to pretend it
doesn't exist.

---

## 6. Certificate Flow

```
Input facts + rules
       |
       v
  +-------------+
  | Horn Closure |  -> HornClosureState (claims, derivations, blocked)
  +------+------+
         |
         v
  +---------------------+
  | Contract Validation |  -> CompilationContractReport
  +------+--------------+
         |
         v
  +------------------+
  | Argument Build   |  -> [Argument]
  +------+-----------+
         |
         v
  +------------------+
  | Attack Graph     |  -> [Attack]
  +------+-----------+
         |
         v
  +----------------------+
  | Grounded Extension   |  -> grounded_set, DecisionStatus
  +------+---------------+
         |
         v
  +------------------+
  | ProofTrace Build |  -> CanonicalProofTrace (the certificate)
  +------+-----------+
         |
         v
  +------------------+
  | Checker          |  -> CheckerResult (pass/fail + violations)
  +------------------+
```

The certificate captures the output of every stage. The checker validates
the certificate. The Lean proofs guarantee the mathematical properties
of the individual stages (Horn closure, grounded extension).

---

## 7. Verification

```bash
# Verify Python certificate types exist
python -c "
from theory.spec.canonical_semantics import CanonicalProofTrace, CanonicalProofStep, DecisionStatus
print('ProofTrace fields:', list(CanonicalProofTrace.__dataclass_fields__))
print('DecisionStatus:', [e.name for e in DecisionStatus])
"

# Verify contract extraction works
python -c "
from theory.spec.horn_aaf_contract import CompilationContractReport, extract_contract_steps
r = CompilationContractReport(satisfied=True, checks=('ok',), violations=())
steps = extract_contract_steps(r)
print('Steps:', len(steps), '- all passed')
"

# Verify Lean umbrella build (existing modules — CertificateChecker.lean not yet present)
cd proofs/lean/juris_lean && lake build JurisLean

# Verify AxiomAudit
cd proofs/lean/juris_lean && lake build +JurisLean.AxiomAudit
```

---

## 8. Gate Status

**M4: Certificate / Checker Boundary** — PARTIAL

- Certificate payload schema: FROZEN (Python)
- Checker verdict schema: FROZEN (Python)
- Fail-closed / no-upgrade: FROZEN (Python, test-verified)
- Lean checker soundness: PLANNED (`CertificateChecker.lean` does not exist)
- Close condition: Checker boundary is documented and Python checker is independent of production evaluator. Currently MET (for transition).
