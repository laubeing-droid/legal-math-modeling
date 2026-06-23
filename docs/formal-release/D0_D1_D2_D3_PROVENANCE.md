# Track D0: Provenance Dependency Graph

## Dependency Chain

`
Fact -> Rule -> Claim -> Argument -> Attack -> Grounded Label -> Trust Label
`

## Reverse Indices

- rules_by_premise: fact_id -> [rule_ids]
- claims_by_rule: rule_id -> [claim_ids]
- arguments_by_claim: claim_id -> [argument_ids]
- attacks_by_argument: argument_id -> [(src, tgt, kind)]
- labels_by_attack: edge_id -> [(label_type, value)]
- trust_by_label: label_id -> [trust_levels]

## Key Theorems (to prove)

### D1: Rule Change Impact
`
x in impact(change)
=> observable_before(x) != observable_after(x)
`

Syntactic may-change vs semantic changed: two-layer output.
Allow false positives (may-change), forbid false negatives (must detect all true changes).

### D2: Incremental Grounded Affected Region
Change types: add argument, remove argument, add attack, remove attack.
Affected region includes: attack successors, defence dependents, SCC successors, iteration closure.

`
outside affected region => label unchanged
`

### D3: Incremental Equals Full (single-edge delta first)
`
incrementalGrounded(AF, delta) == groundedSpec(applyDelta(AF, delta))
`
Order: single add edge -> single delete edge -> add arg+edges -> delete arg -> batch.

Fallback: if incremental fails, full recompute.

## Status
- D0 provenance graph: SPECIFIED (this document)
- D1 safe impact: MVM target (syntactic may-change)
- D2 affected region: MVM target (attack successors + closure)
- D3 incremental = full: MVM target (single edge first)
