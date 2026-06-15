# Theorem C1 and C2: Metric Space — Incompleteness and Finite Lipschitz Exhaustion

## Scope
- **C1**: cross-jurisdiction; multi-dimensional (claim-consequence vectors).
- **C2**: finite inventory only; single-dimension (pricing map).

---

## 1. Metric Space Definition (C1)

### 1.1 Underlying Set

Let `X` be the set of **defined claim-consequence vectors**:

```
X = { (c_C, c_U, c_H) ∈ Claim_C × Claim_U × Claim_H |
      c_J is defined (not DATA_UNAVAILABLE) for at least one J }
```

From the data (`claim_mapping.csv`), `X` is finite but not fully populated: many entries are `DATA_UNAVAILABLE`.

### 1.2 Distance Function

Define the **consequence-distance** function:

```
d: X × X → ℝ_{
≥ 0}
```

For two vectors `x = (c_C, c_U, c_H)` and `y = (c'_C, c'_U, c'_H)`:

```
d(x, y) = Σ_{J ∈ {C,U,H}} d_J(c_J, c'_J)
```

where:

```
d_J(c, c') = {
    0                         if c = c' (same claim text)
    1                         if c ≠ c' and both are defined
    +∞                        if exactly one of {c, c'} is DATA_UNAVAILABLE
    undefined                 if both are DATA_UNAVAILABLE
}
```

**Note**: The `+∞` and `undefined` cases arise because the mapping is partial. This makes `d` not a proper metric on the full product space.

### 1.3 Restricted Metric Space

Define the **defined subspace**:

```
X_def = { x ∈ X | ∀J: c_J ≠ DATA_UNAVAILABLE }
```

On `X_def`, define the discrete metric:

```
d_def(x, y) = {
    0   if x = y
    1   if x ≠ y
}
```

Then `(X_def, d_def)` is a **finite metric space** and is trivially complete (all Cauchy sequences are eventually constant).

However, the **claim-consequence space** `(X, d)` is **not complete** because Cauchy sequences in `X` may converge to points in `Claim_C × Claim_U × Claim_H` that are not in `X` (i.e., points with `DATA_UNAVAILABLE` components).

---

## 2. Theorem C1 Statement (Incompleteness — Contraction Proof Refuted)

> **Theorem C1 (Option 1)**: Let `(X, d)` be the metric space of legal-claim vectors as defined above. Then `(X, d)` is **not** a complete metric space. Consequently, the Banach Fixed-Point Theorem does not apply to operators on `(X, d)`, and no proof of pricing-operator convergence via contraction mapping is valid without additional structure (e.g., restricting to `X_def` or completing the space).

Formally:

```
¬Complete(X, d)
```

**Proof sketch**: Consider a sequence `x_n` where the US component alternates between defined claims and approaches a limit point `x*` with `c*_U = DATA_UNAVAILABLE`. Then `x_n` is Cauchy (distances between defined points are bounded), but `x* ∉ X`, so the limit is not in the space.

**Corollary**: For any operator `T: X → X`, even if `T` is a contraction (`∃k < 1: d(Tx, Ty) ≤ k·d(x, y)`), the Banach theorem does not guarantee a fixed point in `X`.

---

## 3. Finite Metric Space and Lipschitz Ratio (C2)

### 3.1 Finite Metric Space of Patterns

Let `P = {p₁, …, p_n}` be the set of `n = 44` claim-mapping rows from `claim_mapping.csv`.

Define a **Hamming-like distance** on mapping-status labels:

```
d_P(p_i, p_j) = | { J ∈ {C, U, H} | status_i(J) ≠ status_j(J) } |
```

where `status_i(J) ∈ {CN_ONLY, US_ONLY, HK_ONLY, CN_US_PARTIAL, CN_HK_PARTIAL, TRI_JURISDICTION_PARTIAL, COLLISION, ASYMMETRY, DATA_UNAVAILABLE}`.

Then `(P, d_P)` is a finite metric space with `d_P ∈ {0, 1, 2, 3}`.

### 3.2 Pricing Map

Let `T: P → ℝ` be a **pricing map** assigning a real-valued price to each pattern row. **Note**: No explicit pricing map is provided in the data; `T` must be externally defined.

### 3.3 Lipschitz Ratio

Define the **global Lipschitz ratio**:

```
L(T) = max_{i, j ∈ {1,…,n}, i≠j}  |T(p_i) − T(p_j)| / d_P(p_i, p_j)
```

with the convention that if `d_P(p_i, p_j) = 0` and `T(p_i) ≠ T(p_j)`, then `L(T) = +∞`.

---

## 4. Theorem C2 Statement (Finite Exhaustion)

> **Theorem C2 (Option 2)**: Let `M = (P, d_P)` be the finite metric space of 44 claim-mapping rows with Hamming distance on mapping-status labels. Let `T: P → ℝ` be a pricing map. Then exactly one of the following holds:
> 1. `L(T) < 1` (contraction-like behavior on `M`).
> 2. `∃(p_i, p_j) ∈ P × P` with `i ≠ j` such that `|T(p_i) − T(p_j)| / d_P(p_i, p_j) ≥ 1` (non-contraction witnessed).

This is resolved by exhaustive enumeration of all `C(44, 2) = 946` pairs.

Formally:

```
∀T: P → ℝ:
    (L(T) < 1)  ∨  (∃i≠j: |T(p_i) − T(p_j)| / d_P(p_i, p_j) ≥ 1)
```

**Computational verification**: A Python script can enumerate all 946 pairs, compute `d_P` and `|T(p_i) − T(p_j)|`, and determine which disjunct holds.

---

## 5. Status and Allowed Final States

### C1
- **Status**: `REFUTED_AS_LOGICAL_DERIVATION` (Banach proof is invalid) / `PROVED_FORMAL` (incompleteness of consequence space)
- **Allowed Final States**: `REFUTED_AS_LOGICAL_DERIVATION`, `PROVED_FORMAL`, `OPEN_CONJECTURE`

### C2-toy (Toy Model)
- **Status**: `TOY_SYNTHETIC_PROOF_ONLY`
- **Reason**: Exhaustive enumeration of 15 synthetic items with linear pricing map `f(T,e)=0.6T+0.4e` and L1 metric shows sup Lipschitz ratio = 0.600 < 1.0. **Applies ONLY to the toy model; real legal pricing is DATA_INSUFFICIENT_FOR_PROOF because metric space is undefined.**
- **Allowed Final States**: `TOY_SYNTHETIC_PROOF_ONLY`

---

## 6. Key Definitions Summary

| Symbol | Type | Definition |
|--------|------|------------|
| `X` | set | claim-consequence vectors (partially defined) |
| `X_def` | set | fully-defined claim-consequence vectors |
| `d` | distance (partial) | consequence-distance with `+∞` for undefined |
| `d_def` | metric | discrete metric on `X_def` |
| `P` | finite set | 44 claim-mapping rows |
| `d_P` | metric | Hamming distance on mapping-status labels |
| `T` | function (external) | pricing map `P → ℝ` |
| `L(T)` | real number | global Lipschitz ratio |
| `Complete(X,d)` | predicate | all Cauchy sequences converge in `X` |
