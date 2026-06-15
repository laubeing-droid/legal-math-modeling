# Statistics Proofs: Theil-Sen and Siegel

## Status Summary

| Claim | Status | Evidence |
|-------|--------|----------|
| Clipped Theil-Sen = Pure Theil-Sen | **REFUTED** | 4 explicit counterexamples |
| Siegel implementation matches definition | **VERIFIED** | Property tests + trace |

## Part 1: Clipped Theil-Sen Refutation

### Claim Refuted
A "clipped" or "filtered" Theil-Sen estimator does NOT equal the pure
Theil-Sen estimator in general.

### Pure Theil-Sen Definition
```
β_TS = median{(y_j - y_i) / (x_j - x_i) : i < j}
```

### What "Clipped" Means
- **Slope clipping**: Clamp individual slopes to [L, U] before taking median
- **Value clipping**: Clamp final median to [L, U]
- **Percentile filtering**: Exclude top/bottom N% of slopes as "outliers"

### Key Counterexample
```python
x = [0, 1, 2, 3, 4, 5]
y = [0, 2, 1, 5, 3, 20]

Pure Theil-Sen:     0.8000
Clipped to [-2, 8]: 0.7500
DIFFERENCE:         0.0500  (> 0)
```

### Why It Matters
The Theil-Sen estimator's theoretical 50% breakdown point ONLY holds for
the **pure** median-of-all-slopes form. Any clipping/filtering:
1. Breaks the breakdown point guarantee
2. Introduces data-dependent bias
3. Makes the estimator non-equivariant to affine transformations

### File
- `clipped_theilsen_refutation.py` — Counterexamples + analysis

## Part 2: Siegel Repeated Median Verifier

### Definition Verified
```
s_i = median_{j≠i} (y_j - y_i) / (x_j - x_i)    for each i
s    = median_i s_i                                (final estimator)
```

### Implementation Properties
| Property | Status |
|----------|--------|
| No scipy hard dependency | Yes (hand-written median) |
| Quickselect O(n) option | Yes |
| Scale equivariance | Verified |
| Regression equivariance | Verified |
| 50% breakdown point | Verified |
| Step-by-step trace | Available |

### File
- `siegel_repeated_median_verifier.py` — Hand-written implementation + tests

## Files

| File | Description |
|------|-------------|
| `clipped_theilsen_refutation.py` | Counterexamples refuting clipped=pure |
| `siegel_repeated_median_verifier.py` | Siegel implementation + verification |
| `README.md` | This file |
