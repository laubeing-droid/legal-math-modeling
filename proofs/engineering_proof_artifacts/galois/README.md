# Finite-Domain Galois Connection -- Engineering Verification Artifacts

> **Nature of artifact:** Python exhaustive enumeration on finite domains,
> NOT a Lean formal proof. The result holds for all tested cases but does
> NOT constitute a general proof for arbitrary (possibly infinite) domains.

## Problem statement

### Incidence structure

Given finite sets D (domain) and Atom, and an arbitrary function:

```
alpha_one : D -> P(Atom)
```

Define the reverse-index operator:

```
gamma_one(a) = { d in D | a in alpha_one(d) }
```

### Theorem 1: Incidence

```
forall d in D, forall a in Atom:
    a in alpha_one(d)  <=>  d in gamma_one(a)
```

### Theorem 2: Powerset Galois connection

Define the lifted operators on power sets:

```
Alpha(S) = union { alpha_one(d) | d in S }          for S subseteq D
Gamma(B) = { d in D | alpha_one(d) subseteq B }     for B subseteq Atom
```

The Galois connection property:

```
forall S subseteq D, forall B subseteq Atom:
    Alpha(S) subseteq B  <=>  S subseteq Gamma(B)
```

## Verification strategy

For each domain size pair (|D|, |Atom|) with |D| <= 4 and |Atom| <= 4:

1. Label D = {0, ..., |D|-1} and Atom = {0, ..., |Atom|-1}
2. Enumerate ALL possible alpha_one functions
   - Count: 2^(|D| * |Atom|)
3. For each alpha_one:
   - Compute gamma_one from the definition
   - Verify Theorem 1 (incidence) for every (d, a) pair
   - Compute Alpha and Gamma
   - Verify Theorem 2 (Galois connection) for every (S, B) pair
4. Assert on failure; non-zero exit on any violation

### Domain sizes checked

| |D| | |Atom| | alpha_one count | Fixtures |
|-----|--------|-----------------|----------|
| 1 | 1 | 2 | 2 |
| 1 | 2 | 4 | 4 |
| 1 | 3 | 8 | 8 |
| 1 | 4 | 16 | 16 |
| 2 | 1 | 4 | 4 |
| 2 | 2 | 16 | 16 |
| 2 | 3 | 64 | 64 |
| 2 | 4 | 256 | 256 |
| 3 | 1 | 8 | 8 |
| 3 | 2 | 64 | 64 |
| 3 | 3 | 512 | 512 |
| 3 | 4 | 4,096 | 4,096 |
| 4 | 1 | 16 | 16 |
| 4 | 2 | 256 | 256 |
| 4 | 3 | 4,096 | 4,096 |
| 4 | 4 | 65,536 | 65,536 |

**TOTAL FIXTURES VERIFIED: 74,954 -- ALL PASSED, zero failures.**

## Results

### Theorem 1 (Incidence)

**VERIFIED** for all 74,954 fixtures. This is essentially definitional:
`a in alpha_one(d)` is equivalent to `d in gamma_one(a)` by the definition
of `gamma_one`. The exhaustive check confirms consistency across all possible
incidence structures within the bounded domain sizes.

### Theorem 2 (Powerset Galois connection)

**VERIFIED** for all 74,954 fixtures. For every possible subset S of D and
every possible subset B of Atom, the equivalence
`Alpha(S) subseteq B <=> S subseteq Gamma(B)` holds.

### Why this matters

A Galois connection between two partially ordered sets consists of two
monotone functions (here Alpha and Gamma) satisfying the adjointness property
(Theorem 2). Galois connections are fundamental in:

- Abstract interpretation (static program analysis)
- Formal concept analysis
- Database theory (reverse-index structures)
- Lattice theory

## Lean formalization

**`FiniteGaloisAdjunction.lean`** contains 2 supporting theorems for the
Lean formalization (separate from these Python artifacts).

## Limitations

1. **Finite domains only:** Checked up to |D| <= 4 and |Atom| <= 4. Does
   NOT constitute a proof for arbitrary (potentially infinite) domains.
2. **Small domain sizes:** Enumeration scales as 2^(|D| * |Atom|). For
   |D| = 5, |Atom| = 5, this would be 2^25 = 33,554,432 fixtures (feasible
   but not included in this run).
3. **Integer labels:** Domain elements are abstracted as {0, 1, ..., n-1}.
   The proof is independent of the specific labeling.
4. **No Lean verification:** The Lean formalization is provided as a draft
   with proof sketches. Actual Lean checking is pending toolchain availability.

## Artifacts

| File | Description |
|------|-------------|
| `finite_galois_adjunction.py` | Python exhaustive verification script |
| `FiniteGaloisAdjunction.lean` | Lean formal specification draft (TOOLCHAIN_PENDING) |

## Running

```bash
python3 finite_galois_adjunction.py
```

Expected output: `Status: EXHAUSTIVE_FINITE_PROOF` with exit code 0.
