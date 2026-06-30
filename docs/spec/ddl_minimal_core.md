# DDL Minimal Core

**Date:** 2026-07-01
**Status:** CLOSED_FOR_FOUR_SLICES
**Gate M2:** CLOSED_FOR_FOUR_SLICES
**Authority:** `legal-math-modeling`

## Purpose

This document records the minimal deontic logic layer that `juris-calculus`
must consume rather than reinvent. The closed scope is the current Playbook
scope: contract breach, license, permission, and priority.

## Lean Artifacts

`proofs/lean/juris_lean/JurisLean/DDLDefinitions.lean` defines the minimal
DDL interface:

| Concept | Lean artifact |
|---|---|
| obligation | `isObligation`, `Obligation` |
| permission | `isPermission`, `Permission` |
| prohibition | `isProhibition`, `Prohibition` |
| constitutive status rule | `isConstitutive` |
| violation | `directViolation`, `Violation` |
| defense / exception | `defenseApplies`, `exceptionApplies` |
| remedial consequence | `remedialConsequence`, `Reparation` |
| priority ordering | `priorityOrdering`, `Priority` |

## Proven DDL Properties

`DDLDefinitions.lean` proves:

- `violation_implies_norm_active`
- `permission_no_direct_violation`
- `constitutive_no_direct_violation`
- `permission_does_not_imply_obligation`
- `contract_breach_direct_violation_shape`
- `license_permission_not_direct_violation`
- `permission_slice_permission_not_obligation`
- `priority_ordering_requires_verified_evidence`
- `remedial_consequence_same_norm`

These are Lean theorems in the four-slice minimal DDL model. They do not prove
the complete runtime implementation.

## Python Reference Artifacts

`theory/spec/ddl_core.py` defines the reference bundles:

| Bundle | Purpose |
|---|---|
| `make_contract_breach_bundle()` | obligation + force-majeure defense + ordered repair |
| `make_license_permission_priority_bundles()` | license status + permission + prohibition + priority defeat |
| `make_permission_conflict_bundles()` | permission/prohibition conflict requiring explicit override priority |
| `make_priority_decision_bundles()` | rule A / rule B priority decision and missing-priority fail-closed cases |

Historical tort/criminal/admin bundles remain in the file, but they are not the
four-slice Playbook closure target.

## Four Required Slices

| Slice | Closed path |
|---|---|
| contract breach | obligation -> nonperformance -> breach argument -> defense fail-closed |
| license | license grant/scope -> permission/prohibition interaction -> outside-scope rejection |
| permission | permission source + condition -> no automatic obligation -> conflict can remain `UNDECIDED` |
| priority | priority evidence -> defeat relation; missing evidence/cycle/self-attack fail-closed |

## Runtime Differential Evidence

The local reference/shadow fixture report is:

`runtime/legal_math_four_slice_differential.json`

It covers:

- contract breach: `breach_proved`, `defense_present`, `malformed_certificate`
- license: `within_scope`, `outside_scope`, `terminated`
- permission: `permission_source_condition_satisfied`, `condition_missing`, `override_conflict`
- priority: `priority_wins`, `missing_priority`, `priority_cycle`, `self_attack`

## Boundary

- Permission never creates a direct violation by itself.
- Constitutive rules define status, not liability.
- Missing priority evidence does not default to either side.
- Cycles and self-attacks are fail-closed/`UNDECIDED`.
- These properties are closed for the four-slice formal model only.

## Verification

```powershell
cd proofs/lean/juris_lean
lake build JurisLean

cd ..\..\..
python -m pytest tests\spec\test_spec_transition.py -q
python -m theory.spec.runtime_differential --output runtime\legal_math_four_slice_differential.json
```
