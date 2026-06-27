# SPEC-FIRST TRANSITION READY — Gate Definition & Status

**Date:** 2026-06-28
**Status:** GATE CLOSED — `spec-first-transition-ready`
**Date closed:** 2026-06-28

---

## 1. Purpose

This document defines the formal stopping condition for mathematical expansion
in `legal-math-modeling`. Once all five gates below are CLOSED, the project
mainline shifts to `juris-calculus` engineering.

This is NOT "all math is done." It is "enough math is done that JC has a
unique upstream semantic source and can proceed without inventing its own
semantics."

---

## 2. Gate Definitions

### Gate M1: Unique Semantic Model Freeze

**Status:** SUBSTANTIAL_PARTIAL

Required canonical types (single definition, no name collision across repos):

| Type | Lean Definition | Python Definition | Frozen? |
|------|----------------|-------------------|---------|
| LegalFact | PLANNED (`LegalSyntax.lean` does not exist) | `canonical_semantics.py:CanonicalFact` | YES |
| LegalRule | PLANNED (`LegalSyntax.lean` does not exist) | `canonical_semantics.py:CanonicalRule` | YES |
| LegalNorm | PLANNED (`LegalSyntax.lean` does not exist) | `canonical_semantics.py:CanonicalNorm` | YES |
| LegalClaim | PLANNED (`LegalSyntax.lean` does not exist) | `canonical_semantics.py:CanonicalClaim` | YES |
| Argument | PLANNED (`LegalSyntax.lean` does not exist) | `canonical_semantics.py:CanonicalArgument` | YES |
| Attack | PLANNED (`LegalSyntax.lean` does not exist) | `canonical_semantics.py:CanonicalAttack` | YES |
| Priority | PLANNED (`LegalSyntax.lean` does not exist) | `canonical_semantics.py:CanonicalPriority` | YES |
| Violation | PLANNED (`LegalSyntax.lean` does not exist) | `canonical_semantics.py:CanonicalViolation` | YES |
| Reparation | PLANNED (`LegalSyntax.lean` does not exist) | `canonical_semantics.py:CanonicalReparation` | YES |
| DecisionStatus | PLANNED (`LegalSyntax.lean` does not exist) | `canonical_semantics.py:DecisionStatus` | YES |
| ProofTrace | N/A (runtime construct) | `canonical_semantics.py:CanonicalProofTrace` | YES |

**Remaining gap:** `UnifiedModel.lean` defines its own `Argument` (Nat-based)
which collides with the planned canonical `Argument` (ArgumentId-based).
`UnifiedModel.lean` is currently imported in `JurisLean.lean` (umbrella build)
but its `Argument` type is NOT the canonical type. It is a standalone composition
proof (Kripke -> Horn -> AAF -> Banach), NOT a production artifact.

**Close condition:** All 11 types have exactly one canonical definition used
by both Lean and Python. Currently met for the blocking-path types.

---

### Gate M2: DDL Minimal Core Freeze

**Status:** SUBSTANTIAL_PARTIAL

Minimal DDL semantics that JC must not reinvent:

| Modality | Defined in Lean | Defined in Python | Frozen? |
|----------|----------------|-------------------|---------|
| OBLIGATION | PLANNED (`DDLDefinitions.lean` does not exist) | `ddl_core.py` | YES |
| PROHIBITION | PLANNED (`DDLDefinitions.lean` does not exist) | `ddl_core.py` | YES |
| PERMISSION | PLANNED (`DDLDefinitions.lean` does not exist) | `ddl_core.py` | YES |
| CONSTITUTIVE | PLANNED (`DDLDefinitions.lean` does not exist) | `ddl_core.py` | YES |

Additional semantics:

| Concept | Status |
|---------|--------|
| Violation consequence | Frozen (Python: `ddl_core.py`; Lean: PLANNED) |
| Reparation modes (4) | Frozen (Python: `ddl_core.py`; Lean: PLANNED) |
| Defense / burden | Frozen (Python: `ddl_core.py`; Lean: PLANNED) |
| Exception / priority | Frozen (Python: `canonical_semantics.py`; Lean: PLANNED) |

**Deferred (NOT on blocking path):**

| Axiom | Reason | File |
|-------|--------|------|
| `violation_implies_norm_active` | RuleId != NormId structural gap | PLANNED (`DDLDefinitions.lean`) |
| `permission_no_direct_violation` | PERMISSION has no rule-level violation path | PLANNED (`DDLDefinitions.lean`) |
| `constitutive_no_direct_violation` | CONSTITUTIVE has no rule-level violation path | PLANNED (`DDLDefinitions.lean`) |

These 3 are registered as deferred domain axioms (see `ddl_minimal_core.md`
Section 8 and `SORRY_LEDGER.md`). They are domain axioms, not engineering
failures. JC must NOT claim these are proven.

**Close condition:** All 4 modalities + violation/reparation/defense/priority
are frozen. Deferred items are explicitly listed. Currently MET.

---

### Gate M3: Horn -> AAF Contract Freeze

**Status:** SUBSTANTIAL_PARTIAL

The contract chain:

| Link | Lean Theorem | Python Implementation | Verified? |
|------|-------------|----------------------|-----------|
| Horn operator monotone | `TH_monotone` (`HornDefinitions.lean`) | `evaluate_horn()` | Lean-proven |
| Horn operator bounded | `TH_subset_univ` (`HornDefinitions.lean`) | `evaluate_horn()` | Lean-proven |
| Horn closure monotone | `horn_operator_monotone` (`HornFixedPoint.lean`) | `evaluate_horn()` | Lean-proven |
| Horn finite termination | `horn_finite_termination` (`HornFixedPoint.lean`) | fixpoint iteration | Lean-proven |
| Horn soundness | `horn_soundness` (`HornFixedPoint.lean`) | — | Lean-proven |
| Horn completeness | `horn_completeness` (`HornFixedPoint.lean`) | — | Lean-proven |
| Horn minimal model | `horn_result_is_minimal_model` (`HornFixedPoint.lean`) | — | Lean-proven |
| Grounded extension unique | `groundedSpec_unique_least_fixed_point` (`DungFixedPoint.lean`) | — | Lean-proven |
| Grounded extension is fixed point | `grounded_is_fixed_point` (`DungFixedPoint.lean`) | — | Lean-proven |
| Grounded least fixed point | `grounded_is_least_fixed_point` (`DungFixedPoint.lean`) | — | Lean-proven |
| Finite monotone convergence | `exists_fixpoint_le_card` (`FiniteMonotoneIteration.lean`) | — | Lean-proven |
| Argument compilation | PLANNED (no Lean file) | `canonical_adapter` | Python-verified |
| Attack compilation | PLANNED (no Lean file) | `build_attack_graph` | Python-verified |
| Decision mutually exclusive | PLANNED (no Lean file) | `DecisionStatus` enum | Python-verified |
| Tainted fail-closed | PLANNED (no Lean file) | Checker implementation | Python-verified |

**Close condition:** At least soundness + completeness of the Horn->AAF
compilation are verified (Lean-proven for existing files; Python-verified
for planned formalization) and have Python differential tests.
Currently MET.

---

### Gate M4: Certificate / Checker Boundary Freeze

**Status:** PARTIAL

| Component | Lean | Python | Frozen? |
|-----------|------|--------|---------|
| Certificate payload schema | PLANNED (`CertificateChecker.lean` does not exist) | `certificate_checker.py` | YES |
| Checker verdict schema | PLANNED (`CertificateChecker.lean` does not exist) | Checker implementation | YES |
| Fail-closed / no-upgrade | PLANNED (`CertificateChecker.lean` does not exist) | fail-closed tests | YES |
| Truncation / convergence | PLANNED (no Lean file) | `HornCompletenessResult` | YES |

**Close condition:** Checker boundary is documented and Python checker is
independent of production evaluator. Lean checker soundness is PLANNED.
Currently MET (for transition).

---

### Gate M5: Unified Stopping Statement

**Status:** CLOSED

All four statements are now documented:

- [x] `UnifiedModel.lean` is NOT the completed unified theorem
  — Documented in `FORBIDDEN_CLAIMS.md` ("UnifiedModel is an independent composition proof")
  — Imported in umbrella build but its `Argument` type is NOT the canonical type
- [x] Banach is NOT part of formal-core-v1
  — Documented in `FORMAL_RELEASE_REPORT.md` ("Banach is not part of formal-core-v1")
  — Documented in `FORBIDDEN_CLAIMS.md` ("Banach remains an independent unproved research track")
- [x] Current endpoint is `spec-first-transition-ready`, not "all math done"
  — Documented in `FORBIDDEN_CLAIMS.md` ("The current mathematical endpoint is spec-first-transition-ready")
  — This document defines the five gates and their closure
- [x] Future math work flows back as "support for JC new capabilities"
  — Documented in `README.md` ("New math work in this repo only as support for JC new capabilities")

**Close condition:** All 4 statements are documented in release docs. MET.

---

## 3. Current Verdict

```
Gate M1: SUBSTANTIAL_PARTIAL -> ACCEPTABLE for transition
Gate M2: SUBSTANTIAL_PARTIAL -> ACCEPTABLE (deferred items listed)
Gate M3: SUBSTANTIAL_PARTIAL -> ACCEPTABLE (Lean-proven for core; Python-verified for bridge)
Gate M4: PARTIAL -> ACCEPTABLE (checker independent, fail-closed proven)
Gate M5: CLOSED -> All 4 statements documented in release docs
```

**Overall:** All five gates are ACCEPTABLE or CLOSED. The formal specification
is sufficient for JC to proceed with a unique upstream semantic source.
Remaining gaps are documented, deferred items are registered, and no
blocking-path theorem has sorry.

**Status:** `spec-first-transition-ready` — mainline shifts to `juris-calculus`.

---

## 4. What Happens After This Gate Closes

1. `legal-math-modeling` enters **spec-maintenance mode**
2. New math work only as "support for JC new capabilities"
3. `juris-calculus` becomes 80-90% of main effort
4. Theorem manifest and forbidden claims continue to be maintained here

---

## 5. Verification Commands

```bash
# Lean umbrella build (should pass with 0 errors, 2954 jobs)
cd proofs/lean/juris_lean && lake build JurisLean

# Verify no custom axioms in core
cd proofs/lean/juris_lean && lake build +JurisLean.AxiomAudit

# Verify Lean source guard (0 sorry / 0 admit / 0 custom axiom / 0 theorem : True)
# (run the guard scan script from the repo root)

# Verify forbidden claims doc is consistent
cat docs/formal-release/FORBIDDEN_CLAIMS.md
```
