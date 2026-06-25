# JC Transition Gate Status

## Purpose

This file records the current answer to the question:

```text
Can the project fully shift its main effort to juris-calculus now?
```

The answer must be evidence-based and tied to the five gates defined in
`next-stage-spec-first-roadmap.md`.

## Current Status

### Gate 1: Canonical Semantic Types

Status: `PARTIAL`

Evidence:

- [canonical_semantics.py](D:/Claude/数学证明/legal-math-modeling/theory/spec/canonical_semantics.py)
  defines canonical fact, rule, norm, claim, argument, attack, priority,
  violation, reparation, decision-status, and proof-trace structures.
- `Canonical*` naming avoids collision with older theory modules that already
  define `LegalFact`, `LegalRule`, and `Argument` differently.

Remaining gap:

- the schema is established for the first slice, but not yet adopted as the
  single semantic truth source across all adjacent theory modules

### Gate 2: Minimal DDL Core

Status: `PARTIAL`

Evidence:

- [ddl_core.py](D:/Claude/数学证明/legal-math-modeling/theory/spec/ddl_core.py)
  defines modality, defense, burden-of-proof, violation, and reparation
  semantics for the contract-breach slice.

Remaining gap:

- only the first contract-breach slice is encoded
- no second slice yet validates permission, constitutive rules, or priority
  interaction under a different domain pattern

### Gate 3: Horn -> AAF Machine-Testable Contract

Status: `PARTIAL`

Evidence:

- [horn_aaf_contract.py](D:/Claude/数学证明/legal-math-modeling/theory/spec/horn_aaf_contract.py)
  validates traceability, known-node references, exception direction, and
  accepted-set boundedness.
- [test_spec_transition.py](D:/Claude/数学证明/legal-math-modeling/tests/spec/test_spec_transition.py)
  exercises the contract against the first slice.

Remaining gap:

- the contract currently covers the breach/exception slice only
- no priority-defeat fixture is yet encoded

### Gate 4: Reference Interpreter

Status: `PARTIAL`

Evidence:

- [reference_semantics.py](D:/Claude/数学证明/legal-math-modeling/theory/spec/reference_semantics.py)
  provides a transparent Horn -> AAF -> grounded -> decision pipeline with full
  trace output.

Remaining gap:

- the reference interpreter currently covers the contract-breach slice only
- no cross-slice fixture pack or broader semantic coverage exists yet

### Gate 5: Certificate / Checker / Differential Boundary

Status: `PARTIAL`

Evidence:

- [certificate_schema.py](D:/Claude/数学证明/legal-math-modeling/theory/spec/certificate_schema.py)
  defines `spec-cert-v1` payloads and an independent checker.
- the contract+certificate boundary is exercised in
  [test_spec_transition.py](D:/Claude/数学证明/legal-math-modeling/tests/spec/test_spec_transition.py).

Remaining gap:

- no downstream `juris-calculus` shadow output is being compared yet
- no schema round-trip or differential harness exists across repositories

## Decision

Current answer:

```text
Not yet ready for a full repository-wide shift.
Ready for a staged shift once one or two additional slices and a real
differential harness are added.
```

Interpretation:

- it is now reasonable to treat `legal-math-modeling` as a specification
  upstream
- it is not yet honest to say that the shift gate is fully closed
- the next highest-value work is to add one more semantic slice and then build
  the actual shadow comparison boundary
