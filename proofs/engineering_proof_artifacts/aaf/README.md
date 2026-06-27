# Dung AAF Grounded Extension -- Engineering Verification Artifacts

> **Nature of artifact:** Python exhaustive enumeration, NOT a Lean formal proof.

## What is verified

For every finite Abstract Argumentation Framework A = (Ar, att) with up to
4 arguments, eight properties of the grounded extension GE(A) are checked by
brute-force enumeration of all possible attack graphs.

| # | Property | Method |
|---|----------|--------|
| 1 | **Existence** -- GE(A) exists | Iterating F from empty set reaches a fixpoint |
| 2 | **Uniqueness** -- GE(A) is the unique least fixpoint of F | If S, T are both least fixpoints, S = T |
| 3 | **Determinism** -- GE(A) is deterministically computable | S_0 = empty, S_{i+1} = F(S_i) is deterministic |
| 4 | **Finite convergence** -- fixpoint in at most |Ar|+1 iterations | Chain has at most |Ar| strict increases |
| 5 | **Conflict-free** -- GE(A) contains no attacking pair | Follows from admissibility |
| 6 | **Admissible** -- GE(A) defends all its members | GE(A) = F(GE(A)), so every member is defended |
| 7 | **Fixpoint** -- GE(A) = F(GE(A)) | By construction, iteration stops at S = F(S) |
| 8 | **Monotonicity** -- S1 subset S2 implies F(S1) subset F(S2) | Any argument defended by S1 is also defended by S2 |

## Exhaustive verification results

| n (arguments) | Total AAFs checked | All 8 properties |
|---------------|--------------------|------------------|
| 1 | 2 | PASS |
| 2 | 16 | PASS |
| 3 | 512 | PASS |
| 4 | 65,536 | PASS |
| **Total** | **66,066** | **ALL PASS** |

Special cases also analyzed (10 total): empty attacks, self-attack, mutual
attack, defense chain, odd/even cycles, complete graph, isolated arguments,
complex defense, etc.

## Stratified pipeline correspondence

Each pipeline claim is mapped to an AAF argument; each attack relation maps
to an AAF attack edge.

| Test category | Count | Matches |
|---------------|-------|---------|
| Legal fixtures (8 cases) | 8 | 8 |
| Exhaustive small pipelines | 6 | 6 |

**Correspondence: FULL** -- no counterexamples found.

### Corrected claim

The original claim ("pipeline accepted claims == AAF grounded extension") is
overly strong. The corrected version:

> For **legal** stratified pipelines (attacks only from level L to level L-1,
> acyclic level graph, every non-base claim has exactly one parent),
> pipeline-accepted claims EQUAL the AAF grounded extension.
> For general pipelines, GE(AAF(P)) subset pipeline_accepted(P).

## Artifacts

| File | Description |
|------|-------------|
| `dung_grounded_extension.py` | Exhaustive AAF enumeration + grounded extension verification |
| `stratified_correspondence.py` | Stratified pipeline to AAF mapping and correspondence check |

## Running

```bash
python dung_grounded_extension.py
python stratified_correspondence.py
```

## Lean formalization

The Lean formal proof lives in **`DungFixedPoint.lean`** (17 core theorems),
separate from these Python engineering artifacts.

## References

Dung, V.M. (1995). "On the acceptability of arguments and its fundamental
role in nonmonotonic reasoning, logic programming and n-person games."
*Artificial Intelligence*, 77(2), 321-357.
