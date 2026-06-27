# License Permission Priority Slice

## Scope

This document defines the second semantic slice for the specification-first
transition gate. Its purpose is to cover the three semantic elements that were
not exercised by the contract-breach slice:

- `CONSTITUTIVE`
- `PERMISSION`
- `PRIORITY_DEFEAT`

The slice is intentionally narrow and centers on licensed use:

```text
license_signed
-> rights_holder_authorized
-> license_status_active
-> use_within_scope
-> use_permitted
-> used_work
-> unauthorized_use
-> priority defeat by valid license
```

## Why This Slice Exists

The first slice proved that the specification layer could model:

- obligation
- violation
- exception defeat
- remedy structure

But it did not test whether the reference boundary could distinguish:

- constitutive status creation
- positive permission claims
- priority-based defeat rather than exception-based defeat

This slice closes that gap.

## Gate Alignment

This slice contributes primarily to:

| Gate | Contribution |
|---|---|
| Gate 1 (Canonical Types) | Exercises CanonicalPriority, canonical permission semantics |
| Gate 2 (Minimal DDL) | Exercises CONSTITUTIVE, PERMISSION, PRIORITY_DEFEAT |
| Gate 3 (Horn->AAF Contract) | Exercises priority defeat direction |
| Gate 4 (Reference Interpreter) | Licensed-use fixture for reference evaluator |
| Gate 5 (Certificate/Checker) | Second slice exercised in test_spec_transition.py |

## Canonical Entities Used

The slice uses the canonical semantic vocabulary in
`theory/spec/canonical_semantics.py`.

Required entities:

- `CanonicalFact`
- `CanonicalNorm`
- `CanonicalRule`
- `CanonicalPriority`
- `CanonicalArgument`
- `CanonicalAttack`
- `CanonicalProofTrace`

## Minimal Fact Vocabulary

Suggested fact keys:

- `license_signed`
- `rights_holder_authorized`
- `license_status_active`
- `use_within_scope`
- `used_work`
- `use_permitted`
- `unauthorized_use`

## DDL Semantics

### 1. Constitutive status

```text
if license_signed and rights_holder_authorized
then license_status_active
```

This is a constitutive rule. It creates a legal status rather than a breach
consequence.

### 2. Permission

```text
if license_status_active and use_within_scope
then use_permitted
```

This is a permission rule. It does not carry a violation consequence.

### 3. General prohibition

```text
if used_work
then unauthorized_use
```

This is a prohibition rule with alternative remedies. It represents the general
ban on unlicensed use.

### 4. Priority defeat

```text
licensed_use_permission > unauthorized_use_prohibition
```

This priority does not erase the prohibition from the semantic model. It causes
the permission-backed argument to defeat the prohibition-backed violation
argument when both are present.

## Horn Layer

The Horn layer derives:

- `license_status_active`
- `use_permitted`
- `unauthorized_use_candidate`

It does not resolve normative conflict. That remains in the AAF layer.

## AAF Layer

The AAF layer must explicitly encode:

- permission-backed argument
- prohibition-backed argument
- priority defeat from the permission-backed argument to the prohibition-backed
  violation argument

The defeat must be represented as `PRIORITY_DEFEAT`, not collapsed into a
generic exception.

## Expected Decision Behavior

Two reference fixtures are required:

1. `priority_active=True`
   expected result: `PROVED`
   interpretation: the licensed in-scope use defeats the general prohibition

2. `priority_active=False`
   expected result: `REFUTED`
   interpretation: without the priority relation, the general prohibition is not
   defeated

## Contract Points Tested

This slice is specifically used to test:

1. constitutive conclusions can be represented without violation semantics
2. permission conclusions can be represented without violation semantics
3. priority defeat is explicit in the attack layer
4. certificate payloads preserve priority-based attacks
5. the checker can validate the second slice without relying on contract-breach
   assumptions
