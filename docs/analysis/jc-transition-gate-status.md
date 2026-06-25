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

Status: `SUBSTANTIAL_PARTIAL`

Evidence:

- [ddl_core.py](D:/Claude/数学证明/legal-math-modeling/theory/spec/ddl_core.py)
  defines modality, defense, burden-of-proof, violation, and reparation
  semantics for the contract-breach slice.
- [license-permission-priority-slice.md](D:/Claude/数学证明/legal-math-modeling/docs/analysis/license-permission-priority-slice.md)
  adds constitutive, permission, and priority-defeat semantics as a second
  specification slice.

Remaining gap:

- the minimal DDL core now covers two slices, but is not yet demonstrated across
  a broader domain family
- no separate burden-conditioned priority fixture exists beyond the current
  licensed-use slice

### Gate 3: Horn -> AAF Machine-Testable Contract

Status: `SUBSTANTIAL_PARTIAL`

Evidence:

- [horn_aaf_contract.py](D:/Claude/数学证明/legal-math-modeling/theory/spec/horn_aaf_contract.py)
  validates traceability, known-node references, exception direction, and
  accepted-set boundedness.
- [test_spec_transition.py](D:/Claude/数学证明/legal-math-modeling/tests/spec/test_spec_transition.py)
  exercises the contract against both the contract-breach slice and the
  license-permission-priority slice.

Remaining gap:

- the contract now covers exception defeat and priority defeat
- it still lacks a broader multi-fixture differential harness and a cross-file
  round-trip check

### Gate 4: Reference Interpreter

Status: `SUBSTANTIAL_PARTIAL`

Evidence:

- [reference_semantics.py](D:/Claude/数学证明/legal-math-modeling/theory/spec/reference_semantics.py)
  provides a transparent Horn -> AAF -> grounded -> decision pipeline with full
  trace output for two distinct slices.

Remaining gap:

- the reference interpreter now covers contract-breach and licensed-use
  priority defeat
- it still lacks a broader fixture pack and any cross-repository differential
  comparison

### Gate 5: Certificate / Checker / Differential Boundary

Status: `PARTIAL`

Evidence:

- [certificate_schema.py](D:/Claude/数学证明/legal-math-modeling/theory/spec/certificate_schema.py)
  defines `spec-cert-v1` payloads and an independent checker.
- the contract+certificate boundary is exercised in
  [test_spec_transition.py](D:/Claude/数学证明/legal-math-modeling/tests/spec/test_spec_transition.py)
  for both slices.

Remaining gap:

- no downstream `juris-calculus` shadow output is being compared yet
- no schema round-trip or differential harness exists across repositories

## Decision

Current answer:

```text
Not yet ready for a full repository-wide shift.
Ready for a staged shift once the cross-repository differential harness is
added.
```

Interpretation:

- it is now reasonable to treat `legal-math-modeling` as a specification
  upstream
- it is not yet honest to say that the shift gate is fully closed
- the next highest-value work is to build the actual shadow comparison boundary
  against `juris-calculus`
