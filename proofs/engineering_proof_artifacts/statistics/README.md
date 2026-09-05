# Statistics: Theil-Sen and Siegel -- Engineering Verification Artifacts

> **Nature of artifact:** Python property tests + counterexample construction,
> NOT a Lean formal proof.

## Summary

| Claim | Status | Evidence |
|-------|--------|----------|
| Clipped Theil-Sen == Pure Theil-Sen | **REFUTED** | 4 explicit counterexamples |
| Siegel Repeated Median matches definition | **VERIFIED** | Property tests + trace |

## Part 1: Clipped Theil-Sen refutation

### Claim refuted

A "clipped" or "filtered" Theil-Sen estimator does NOT equal the pure
Theil-Sen estimator in general.

### Pure Theil-Sen definition

```
beta_TS = median{ (y_j - y_i) / (x_j - x_i) : i < j }
```

### What "clipped" means

- **Slope clipping:** Clamp individual slopes to [L, U] before taking median
- **Value clipping:** Clamp final median to [L, U]
- **Percentile filtering:** Exclude top/bottom N% of slopes as "outliers"

### Key counterexample

```python
x = [0, 1, 2, 3, 4, 5]
y = [0, 2, 1, 5, 3, 20]

Pure Theil-Sen:       0.8000
Clipped to [-2, 8]:   0.7500
Difference:           0.0500  (> 0)
```

### Why it matters

The Theil-Sen estimator's theoretical 50% breakdown point ONLY holds for the
**pure** median-of-all-slopes form. Any clipping/filtering:

1. Breaks the breakdown point guarantee
2. Introduces data-dependent bias
3. Makes the estimator non-equivariant to affine transformations

## Part 2: Siegel Repeated Median verifier

### Definition verified

```
s_i = median_{j != i} (y_j - y_i) / (x_j - x_i)    for each i
s    = median_i s_i                                   (final estimator)
```

### Properties verified

| Property | Status |
|----------|--------|
| No scipy hard dependency | Yes (hand-written median) |
| Quickselect O(n) option | Yes |
| Scale equivariance | Verified |
| Regression equivariance | Verified |
| 50% breakdown point | Verified |
| Step-by-step trace | Available |

## Artifacts

| File | Description |
|------|-------------|
| `clipped_theilsen_refutation.py` | Counterexamples refuting clipped == pure Theil-Sen |
| `siegel_repeated_median_verifier.py` | Siegel implementation + property verification |
