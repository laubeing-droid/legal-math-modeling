# DDL Minimal Core — Frozen Semantic Specification

**Date:** 2026-06-28
**Status:** FROZEN (spec-first-transition-ready)
**Gate M2:** SUBSTANTIAL_PARTIAL
**Authority:** `legal-math-modeling` (this repo)
**Implementation:** `juris-calculus` must use these semantics, not invent its own.

---

## 1. Purpose

This document freezes the minimal deontic logic (DDL) semantics that
`juris-calculus` must implement. It defines what the four modalities mean,
how violations arise, how reparations compose, and how exceptions and
priorities work. JC must NOT reinvent these semantics.

---

## 2. Four Core Modalities

| Modality | Meaning | Violation? | Example |
|----------|---------|------------|---------|
| **OBLIGATION** | Actor MUST do action under conditions | YES — breach triggers violation | "Seller must deliver goods" |
| **PROHIBITION** | Actor MUST NOT do action under conditions | YES — commission triggers violation | "User must not use without license" |
| **PERMISSION** | Actor MAY do action under conditions | NO — permission != obligation | "Licensee may use work within scope" |
| **CONSTITUTIVE** | Defines legal status, not conduct | NO — constitutive != liability | "License signing activates license status" |

### Key invariants (enforced by `validate_minimal_ddl_bundle()`):

- PERMISSION norms MUST NOT carry violation consequences.
- CONSTITUTIVE norms MUST NOT carry violation consequences.
- OBLIGATION/PROHIBITION norms MUST define violation consequences.
- Violation consequences MUST declare at least one reparation structure.
- PERMISSION/CONSTITUTIVE norms MUST declare a positive `conclusion_fact`.

---

## 3. Violation Semantics

A **violation** is the consequence of an unexcused norm breach.

```
Violation:
  violation_id: str
  norm_id: str           -> which norm was breached
  trigger_fact: str      -> what fact triggered the violation
  consequence_fact: str  -> what legal consequence follows
  reparations: [Reparation]
```

The violation is attached to the norm, not to the rule. A rule fires and
derives facts; a norm activates and, if unexcused, produces a violation.

---

## 4. Reparation Modes

Once liability is established, reparations compose in one of four modes:

| Mode | Status | Meaning |
|------|--------|---------|
| **ALTERNATIVE** | PLANNED (`DDLDefinitions.lean` does not exist) | Claimant picks one remedy. No order required. |
| **ORDERED_CHAIN** | PLANNED (`DDLDefinitions.lean` does not exist) | Remedies tried in sequence. Next requires prior failure. |
| **CONCURRENT** | PLANNED (`DDLDefinitions.lean` does not exist) | Multiple remedies available simultaneously. No ordering. |
| **COURT_SELECTED** | PLANNED (`DDLDefinitions.lean` does not exist) | Court decides remedy. Not auto-applied. |

All four are defined in Python (`ddl_core.py`). Lean theorems in
`DDLDefinitions.lean` are PLANNED — the file does not yet exist in this repo.

---

## 5. Defenses and Burden of Proof

A **defense** can defeat or suspend a violation consequence.

```
Defense:
  defense_id: str
  label: str
  exception_kind: ExceptionKind  -> DEFEATER / JUSTIFICATION / EXCUSE
  trigger_facts: [str]
  defeats_conclusion: str        -> must match the violation's consequence_fact
  burden_of_proof: BurdenOfProof -> CLAIMANT / RESPONDENT / COURT / PRESUMED_UNLESS_REBUTTED
```

### Exception kinds:

| Kind | Meaning | Effect |
|------|---------|--------|
| **DEFEATER** | Defeats the liability conclusion | Liability vanishes |
| **JUSTIFICATION** | Justifies the act itself | Act was lawful |
| **EXCUSE** | Excuses the actor | Actor not blameworthy |

### Burden of proof:

| Burden | Meaning |
|--------|---------|
| **CLAIMANT** | Claimant must prove the condition |
| **RESPONDENT** | Respondent must prove the condition |
| **COURT** | Court determines |
| **PRESUMED_UNLESS_REBUTTED** | Presumed true unless rebutted |

### Defense invariant:

The defense's `defeats_conclusion` MUST match the bundle's violation
`consequence_fact`. A defense that targets a different conclusion is
semantically invalid.

---

## 6. Priority Relations

A **priority** relation determines which of two conflicting norms wins.

```
Priority:
  priority_id: str
  winner: str   -> norm_id of the winning norm
  loser: str    -> norm_id of the losing norm
  reason: str
```

When both the winner and loser norms activate, the winner's conclusion
survives and the loser's conclusion is defeated in the AAF.

Example: "A valid in-scope license defeats the general unauthorized-use
prohibition."

---

## 7. Exception and Priority Entering the AAF

Exceptions and priorities are not just annotations — they become **attack
edges** in the Dung AAF:

- **Exception attacks**: If argument A supports conclusion C, and defense D
  defeats C, then D's argument attacks A in the AAF.
- **Priority attacks**: If argument A supports norm N1, and priority P says
  N2 > N1, then N2's argument attacks A in the AAF.

This is the Horn -> AAF bridge for deontic semantics.

---

## 8. Deferred Items (NOT Proven, Registered)

The following are structural gaps in the current model. They would be
`sorry`-bearing domain axioms in `DDLDefinitions.lean` (PLANNED — file does
not yet exist), registered here as deferred items:

| Axiom | Reason | Status | Blocking? |
|-------|--------|--------|-----------|
| `violation_implies_norm_active` | RuleId != NormId — rule firing doesn't directly imply norm activation | DEFERRED | NO |
| `permission_no_direct_violation` | Same structural gap — PERMISSION has no rule-level violation path | DEFERRED | NO |
| `constitutive_no_direct_violation` | Same structural gap | DEFERRED | NO |

These 3 axioms are also registered in `SORRY_LEDGER.md`.

**JC must NOT claim these are Lean-proven.** They are registered domain axioms,
not blocking-path theorems.

---

## 9. Five DDL Slices (Implemented)

| Slice | Domain | Modalities | Defenses | Reparation Mode |
|-------|--------|------------|----------|-----------------|
| Contract breach | Civil | OBLIGATION | force_majeure (EXCUSE) | ORDERED_CHAIN |
| License + priority | IP | CONSTITUTIVE, PERMISSION, PROHIBITION | — | ALTERNATIVE |
| Tort liability | Civil | OBLIGATION | contributory_negligence (DEFEATER) | ORDERED_CHAIN |
| Criminal liability | Criminal | PROHIBITION | self_defense (JUSTIFICATION) | ORDERED_CHAIN |
| Admin illegality | Admin | OBLIGATION, CONSTITUTIVE | — | ORDERED_CHAIN |

All slices pass `validate_minimal_ddl_bundle()`.

---

## 10. Existing Lean Foundation

While `DDLDefinitions.lean` does not yet exist, the following Lean files
provide the mathematical foundation for DDL semantics:

| Lean File | Relevance to DDL |
|-----------|-----------------|
| `HornDefinitions.lean` | Defines the Horn operator `TH` that underpins rule firing. 2 core theorems: `TH_monotone`, `TH_subset_univ`. |
| `HornFixedPoint.lean` | Proves Horn closure is the least fixed point. 10 core theorems including `horn_completeness` and `horn_result_is_minimal_model`. |
| `DungFixedPoint.lean` | Proves grounded extension properties. 17 core theorems. The grounded extension is where DDL violations are ultimately resolved via AAF semantics. |
| `FiniteMonotoneIteration.lean` | The general finite monotone iteration theory. 9 core theorems. Both Horn and Dung layers depend on this. |

These files establish that the mathematical objects underlying DDL (Horn closures,
grounded extensions, monotone iterations) are sound and free of `sorry`.

---

## 11. Verification

```bash
# Verify DDL core Python module
python -c "
from theory.spec.ddl_core import (
    make_contract_breach_bundle, make_license_permission_priority_bundles,
    make_tort_bundle, make_criminal_bundle, make_admin_bundle,
    summarize_reparation_modes, validate_minimal_ddl_bundle
)
b1 = make_contract_breach_bundle()
b2 = make_license_permission_priority_bundles()
b3 = make_tort_bundle()
b4 = make_criminal_bundle()
b5 = make_admin_bundle()
print('All DDL bundles valid')
print('Reparation modes:', summarize_reparation_modes([b1, *b2, b3, b4, *b5]))
"

# Verify Lean umbrella builds (DDLDefinitions.lean does not yet exist)
cd proofs/lean/juris_lean && lake build JurisLean

# Verify AxiomAudit
cd proofs/lean/juris_lean && lake build +JurisLean.AxiomAudit
```

---

## 12. Gate Status

**M2: DDL Minimal Core** — SUBSTANTIAL_PARTIAL

- 4 modalities: FROZEN (Python); Lean PLANNED
- 4 reparation modes: FROZEN (Python); Lean PLANNED
- Violation/defense/burden: FROZEN (Python); Lean PLANNED
- 3 deferred domain axioms: registered, non-blocking
- Close condition: All 4 modalities + violation/reparation/defense/priority are frozen. Deferred items are explicitly listed. Currently MET.
