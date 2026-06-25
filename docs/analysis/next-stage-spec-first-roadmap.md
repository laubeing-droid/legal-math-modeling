# Next-Stage Spec-First Roadmap

## Position

This repository should continue as the **specification upstream** of
`juris-calculus`, not as a second production runtime.

The correct next-stage chain is:

```text
legal semantics
→ Lean formal specification
→ reference interpreter
→ juris-calculus shadow implementation
→ differential validation
→ production enablement
```

This is not a license to keep expanding mathematics indefinitely.
The goal is to finish the smallest executable, testable, boundary-explicit
semantic core that `juris-calculus` can implement without inventing its own
meaning.

## What Is Already Closed

`formal-core-v1` is already closed for:

- finite monotone iteration kernel
- Dung grounded fixed-point layer
- finite Horn closure layer

This is enough to support a spec-first engineering transition, but it is **not**
enough to claim that the entire unified legal reasoning model is formally
closed.

## What Must Be Closed Before Full JC Focus

The project can shift its main effort to `juris-calculus` after the following
five gates are closed.

### Gate 1: Canonical Semantic Types

The repository must expose one canonical semantic vocabulary for at least the
following conceptual entities:

- `LegalFact`
- `LegalRule`
- `LegalNorm`
- `LegalClaim`
- `Argument`
- `Attack`
- `Priority`
- `Violation`
- `Reparation`
- `DecisionStatus`
- `ProofTrace`

No parallel definitions with different meanings should survive across the
specification, reference interpreter, and `juris-calculus`.

Implementation note:

- the current Python specification layer uses `Canonical*` class names to avoid
  collisions with historical theory modules that already define `LegalFact`,
  `LegalRule`, and `Argument` differently

### Gate 2: Minimal DDL Core

The specification must fix the meaning of:

- `OBLIGATION`
- `PROHIBITION`
- `PERMISSION`
- `CONSTITUTIVE`
- violation consequences
- reparation semantics
- exception semantics
- priority semantics
- burden-conditioned defenses

At this stage, the goal is not full legal philosophy. The goal is to prevent
the runtime from improvising semantic behavior.

### Gate 3: Horn -> AAF Compilation Contract

The repository must define a machine-testable contract for:

```text
Compile(KB, Facts) -> AAF
```

At minimum, the contract must preserve:

- traceability from argument to rules and supporting facts
- exception-to-defeat direction
- distinction between ordinary conflict and legal exception
- priority-sensitive defeat handling
- stable meanings of `accepted`, `rejected`, and `undecided`

### Gate 4: Reference Interpreter

This repository must provide a transparent reference evaluator with these
properties:

- direct correspondence to the formal specification
- no performance hacks
- no caching assumptions
- no concurrency assumptions
- full trace output

The reference evaluator is the oracle for `juris-calculus`, not a competitor to
it.

### Gate 5: Differential Validation Boundary

The engineering transition is not complete when `juris-calculus` "passes its
own tests". It is complete when the runtime is checked against the reference
boundary:

```text
formal specification
→ reference evaluator
→ shadow implementation
→ differential report
```

The comparison must cover:

- schema round-tripping
- Horn single-step agreement
- Horn final closure agreement
- AAF construction agreement
- grounded-status agreement
- proof-trace certificate agreement

## Explicit Non-Goals For This Stage

Do not use this stage to claim:

- the full unified legal reasoning model is complete
- all Python runtime behavior is formally proved
- Banach is now part of the released core
- empirical calibration is complete
- privacy guarantees are complete
- litigation automation is complete

Those items remain separate tracks.

## First Vertical Slice

The first semantic slice should be **contract breach liability**:

```text
contract formation
→ obligation
→ non-performance / defective performance
→ exemption defense
→ breach finding
→ remedy semantics
→ decision status + trace
```

This slice is narrow enough to formalize and rich enough to surface real
semantic issues:

- permission is not the negation of obligation
- exemption defeats violation, not the underlying contract fact
- remedies may be ordered, alternative, concurrent, or court-selected
- the runtime must preserve uncertainty and fail-closed behavior

## Repository Deliverables For This Stage

This repository should now produce four kinds of artifacts:

1. Canonical semantic schema
2. Reference evaluator
3. Vertical-slice semantic documents
4. Release-boundary statements about what is and is not proved

## Transition Rule

Once the five gates above are closed, the project should shift its **main**
engineering effort to `juris-calculus`.

Recommended allocation after that point:

- `juris-calculus`: 80%-90%
- `legal-math-modeling`: 10%-20%

At that stage this repository becomes:

- the semantic truth source
- the differential oracle source
- the formal release boundary source
- the anti-drift guard for runtime semantics
