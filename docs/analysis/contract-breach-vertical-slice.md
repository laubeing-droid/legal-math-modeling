# Contract Breach Vertical Slice

## Scope

This document defines the first narrow semantic slice that should be closed
before the project fully shifts its main effort to `juris-calculus`.

The target is not "all contract law". The target is one auditable chain:

```text
contract_exists
→ delivery_obligation
→ non_delivery
→ exemption defense
→ breach finding
→ remedy selection
→ decision status and proof trace
```

## Canonical Entities

The slice uses the canonical semantic vocabulary defined in
`theory/spec/canonical_semantics.py`.

Required entities in this slice:

- `LegalFact`
- `LegalNorm`
- `LegalRule`
- `Argument`
- `Attack`
- `Violation`
- `Reparation`
- `DecisionStatus`
- `ProofTrace`

## Minimal Fact Vocabulary

Suggested fact keys for the first slice:

- `contract_exists`
- `delivery_due`
- `goods_delivered`
- `goods_not_delivered`
- `force_majeure`
- `buyer_accepted_delay`
- `seller_failed_delivery`
- `delivery_obligation_active`
- `delivery_breach`
- `remedy_continue_performance`
- `remedy_cure`
- `remedy_damages`

This list is intentionally small. The purpose is to stabilize semantics first,
not to maximize legal coverage.

## Norm Layer

The minimal DDL layer should be able to express:

1. Obligation

```text
if contract_exists and delivery_due
then seller has OBLIGATION to deliver goods
```

2. Violation

```text
if delivery_obligation_active and goods_not_delivered
then delivery_breach
```

3. Exemption

```text
if force_majeure
then defeat the breach argument
```

4. Remedy relation

```text
if delivery_breach
then remedy = continue performance / cure / damages
```

The slice must also state whether remedies are:

- ordered
- alternative
- concurrent
- court-selected

The initial recommended choice for this slice is:

- `continue performance` and `cure` as ordered repair steps when still possible
- `damages` as available after breach, potentially concurrent with residual loss
  compensation where the governing rule allows it

If the governing law does not justify that ordering, the reference model must
say so explicitly rather than hard-coding a procedural preference.

## Horn Layer

The Horn layer should only derive monotone facts such as:

- `delivery_obligation_active`
- `seller_failed_delivery`
- `delivery_breach_candidate`

It should not collapse non-monotone defenses into Horn closure.

That means:

- exemption facts may be derived in Horn
- exemption *effect* belongs to the AAF layer

## AAF Layer

The AAF layer resolves:

- ordinary rebuttal
- legal exception
- priority-based defeat

For this slice, the key attack pattern is:

```text
force_majeure_argument -> delivery_breach_argument
```

The specification must preserve the direction:

- the exemption defeats the breach conclusion
- it does not erase the contract fact
- it does not erase the existence of the delivery obligation

## Decision Output

The minimal decision-status space for this slice should include:

- `PROVED`
- `REFUTED`
- `UNDECIDED`
- `TAINTED`

Interpretation:

- `PROVED`: the breach conclusion survives grounded evaluation
- `REFUTED`: the breach conclusion is defeated by a stronger accepted argument
- `UNDECIDED`: the claim is neither accepted nor defeated under the current
  finite grounded evaluation
- `TAINTED`: the evaluator cannot safely claim convergence or completeness and
  must fail closed

## Proof Trace Requirements

Every evaluation should emit a trace with at least:

1. input facts
2. Horn firings
3. derived facts
4. constructed arguments
5. attacks / defeats
6. grounded accepted set
7. final decision status
8. fail-closed cause when applicable

## What Counts As "Closed Enough"

This slice is closed enough to move downstream when all of the following exist:

1. canonical schema in this repository
2. transparent reference evaluator in this repository
3. at least one fixture for:
   - plain breach
   - force majeure defense
   - conflicting remedy availability
4. a stable certificate payload format
5. a differential comparison target for `juris-calculus`

## What This Slice Does Not Claim

This slice does not claim:

- the full contract law domain is complete
- every remedy ordering is universally formalized
- the runtime is already proved correct
- all exemptions and burdens are modeled

It only establishes the first reusable semantic slice for downstream shadow
implementation.
