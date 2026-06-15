# Finite-Domain Galois Connection Proof

## Status: EXHAUSTIVE_FINITE_PROOF

**Date**: 2025-06-11  
**Author**: Proof Agent  
**Toolchain**: Python 3.12 (available), Lean (PENDING_TOOLCHAIN), Z3 (unavailable)

---

## Problem Statement

### Incidence Structure

Given finite sets `D` (domain) and `Atom`, and an arbitrary function:

```
alpha_one : D -> P(Atom)
```

Define the reverse-index operator:

```
gamma_one(a) = { d in D | a in alpha_one(d) }
```

### Theorem 1: Incidence Theorem

```
forall d in D, forall a in Atom:
    a in alpha_one(d)  <=>  d in gamma_one(a)
```

### Theorem 2: Powerset Galois Connection

Define the lifted operators on power sets:

```
Alpha(S) = U { alpha_one(d) | d in S }      for S subseteq D
Gamma(B) = { d in D | alpha_one(d) subseteq B }  for B subseteq Atom
```

The Galois connection property:

```
forall S subseteq D, forall B subseteq Atom:
    Alpha(S) subseteq B  <=>  S subseteq Gamma(B)
```

---

## Verification Strategy

### Exhaustive Enumeration

For each domain size pair `(|D|, |Atom|)` with `|D| <= 4` and `|Atom| <= 4`:

1. Label `D = {0, ..., |D|-1}` and `Atom = {0, ..., |Atom|-1}`
2. Enumerate **ALL** possible `alpha_one` functions
   - Count: `(2^|Atom|)^|D| = 2^(|D| * |Atom|)`
3. For each `alpha_one`:
   - Compute `gamma_one` from the definition
   - Verify Theorem 1 (incidence) for every `(d, a)` pair
   - Compute `Alpha` and `Gamma`
   - Verify Theorem 2 (Galois connection) for every `(S, B)` pair
4. Assert on failure; non-zero exit on any violation

### Domain Sizes Checked

| |D| | |Atom| | alpha_one count (2^|D|*|Atom|) | Fixtures |
|---|------|-------------------------------|----------|
| 1 | 1    | 2^1  = 2                      | 2        |
| 1 | 2    | 2^2  = 4                      | 4        |
| 1 | 3    | 2^3  = 8                      | 8        |
| 1 | 4    | 2^4  = 16                     | 16       |
| 2 | 1    | 2^2  = 4                      | 4        |
| 2 | 2    | 2^4  = 16                     | 16       |
| 2 | 3    | 2^6  = 64                     | 64       |
| 2 | 4    | 2^8  = 256                    | 256      |
| 3 | 1    | 2^3  = 8                      | 8        |
| 3 | 2    | 2^6  = 64                     | 64       |
| 3 | 3    | 2^9  = 512                    | 512      |
| 3 | 4    | 2^12 = 4096                   | 4096     |
| 4 | 1    | 2^4  = 16                     | 16       |
| 4 | 2    | 2^8  = 256                    | 256      |
| 4 | 3    | 2^12 = 4096                   | 4096     |
| 4 | 4    | 2^16 = 65536                  | 65536    |

**TOTAL FIXTURES VERIFIED: 74,954**

**ALL PASSED: Zero failures detected.**

---

## Results Summary

### Theorem 1 (Incidence Theorem)
**VERIFIED** for all 74,954 fixtures. This theorem is essentially definitional:
`a in alpha_one(d)` is equivalent to `d in gamma_one(a)` by the definition of
`gamma_one`. The exhaustive check confirms this holds consistently across all
possible incidence structures within the bounded domain sizes.

### Theorem 2 (Powerset Galois Connection)
**VERIFIED** for all 74,954 fixtures. The Galois connection property is the
fundamental relationship between the two lifted operators `Alpha` and `Gamma`.
For every possible subset `S` of `D` and every possible subset `B` of `Atom`,
the equivalence `Alpha(S) subseteq B <=> S subseteq Gamma(B)` holds.

### Why This Matters

A **Galois connection** between two partially ordered sets consists of two
monotone functions (here `Alpha` and `Gamma`) satisfying the adjointness
property (Theorem 2). Galois connections are fundamental in:

- Abstract interpretation (static program analysis)
- Formal concept analysis
- Database theory (reverse-index structures)
- Lattice theory

The reverse-index incidence structure is a canonical example where the
Galois connection arises naturally from a binary relation (encoded here
by `alpha_one`).

---

## File Artifacts

| File | Description | Status |
|------|-------------|--------|
| `finite_galois_adjunction.py` | Python exhaustive verification script | COMPLETE |
| `FiniteGaloisAdjunction.lean` | Lean formal specification draft | PENDING_TOOLCHAIN |
| `README.md` | This file | COMPLETE |

---

## Limitations and Assumptions

1. **Finite Domains Only**: This is an exhaustive check over finite domains
   with `|D| <= 4` and `|Atom| <= 4`. It does **NOT** constitute a proof for
   arbitrary (potentially infinite) domains.

2. **Small Domain Sizes**: The enumeration scales as `2^(|D| * |Atom|)`. For
   `|D| = 5, |Atom| = 5`, this would be `2^25 = 33,554,432` fixtures, which
   is still feasible but was not included in this run.

3. **Integer Labels**: Domain elements are abstracted as integers
   `{0, 1, ..., n-1}`. The proof is independent of the specific labeling.

4. **No Lean Verification**: The Lean formalization is provided as a draft
   with proof sketches. Actual Lean checking is pending toolchain availability.

5. **No Z3 Integration**: SMT-based verification was not available.

---

## Mathematical Notes

### Structure of the Proof

The incidence structure `alpha_one : D -> P(Atom)` encodes a binary relation
`R subseteq D x Atom` where `(d, a) in R` iff `a in alpha_one(d)`.

The operator `gamma_one` is the **transposed relation**: `(a, d) in R^T` iff
`(d, a) in R`. Theorem 1 states the obvious: `R(d, a) <=> R^T(a, d)`.

The operators `Alpha` and `Gamma` are the **polar maps** of the relation `R`:
- `Alpha(S) = { a | exists d in S, R(d, a) }` (direct image)
- `Gamma(B) = { d | forall a, R(d, a) -> a in B }` (universal pre-image)

Theorem 2 is the defining property of the Galois connection induced by the
polar maps of a binary relation. In the Lean draft, the proof follows
straightforwardly from the definitions:
- Forward: `Alpha(S) subseteq B` means every element reachable from `S` is in
  `B`, hence each `d in S` has `alpha_one(d) subseteq B`, i.e., `d in Gamma(B)`.
- Reverse: `S subseteq Gamma(B)` means every `d in S` has `alpha_one(d) subseteq
  `B`, so any `a in Alpha(S)` comes from some `d in S` with `a in alpha_one(d)`,
  hence `a in B`.

---

## Running the Proof

```bash
python3 finite_galois_adjunction.py
```

Expected output: `Status: EXHAUSTIVE_FINITE_PROOF` with exit code 0.

If any assertion fails, the script exits with code 1 and prints the
counterexample to stderr.

---

*Generated by Proof Agent, 2025-06-11*
