# Standard Scalar Laplace Mechanism: Proof of ε-Differential Privacy

## Theorem (Standard Laplace Mechanism)

Let f: D → R be a scalar-valued query function with L1-sensitivity:

```
Δ₁(f) = max_{D~D'} |f(D) - f(D')|
```

where D ~ D' denotes neighboring datasets (differing in at most one record).

The mechanism M defined as:

```
M(D) = f(D) + Lap(Δ₁(f)/ε)
```

satisfies **ε-differential privacy**, where Lap(b) denotes the Laplace
distribution with scale parameter b and PDF:

```
Lap(b; x) = (1/2b) · exp(-|x|/b)
```

## Assumptions

1. **Scalar output**: f(D) ∈ R (single real value)
2. **Finite sensitivity**: Δ₁(f) < ∞
3. **Neighboring relation**: D and D' differ in exactly one record
   (replacement or addition/deletion model)
4. **Privacy parameter**: ε > 0
5. **Standard Laplace noise**: Independent noise drawn from Lap(Δ/ε)

## Proof

### Step 1: PDF Ratio for Neighboring Datasets

For any output y ∈ R and neighboring datasets D ~ D':

```
PDF[M(D) = y]     (1/2b) · exp(-|y - f(D)|/b)
-------------  =  --------------------------------
PDF[M(D') = y]    (1/2b) · exp(-|y - f(D')|/b)

                = exp((|y - f(D')| - |y - f(D)|) / b)
```

where b = Δ₁(f)/ε.

### Step 2: Apply the Triangle Inequality

```
|y - f(D')| - |y - f(D)| ≤ |f(D) - f(D')|    (reverse triangle inequality)
```

By definition of sensitivity:

```
|f(D) - f(D')| ≤ Δ₁(f)
```

### Step 3: Bound the Ratio

```
PDF[M(D) = y]
------------- ≤ exp(Δ₁(f) / b) = exp(Δ₁(f) / (Δ₁(f)/ε)) = exp(ε) = e^ε
PDF[M(D') = y]
```

### Step 4: Integrate Over Any Event S

For any measurable set S ⊆ R:

```
Pr[M(D) ∈ S]   ∫_S PDF[M(D)=y] dy
------------ = --------------------- ≤ max_y PDF[M(D)=y] / PDF[M(D')=y] ≤ e^ε
Pr[M(D') ∈ S]  ∫_S PDF[M(D')=y] dy
```

Therefore: **Pr[M(D) ∈ S] ≤ e^ε · Pr[M(D') ∈ S]** for all measurable S.

∎

## Sensitivity in Different Models

| Model | Neighboring Definition | Δ₁ for sum query |
|-------|----------------------|-----------------|
| Add/Delete | D' = D ∪ {x} or D \\{x} | max_x \|x\| |
| Replace | D' replaces one element | 2 · max_x \|x\| |

## Key Properties

1. **Privacy-utility tradeoff**: Smaller ε → larger noise → less accuracy
2. **Scale calibration**: Noise scale b = Δ/ε is TIGHT (optimal for single query)
3. **Post-processing immunity**: Any deterministic function g applied to M(D)
   preserves ε-DP (by post-processing theorem)

## Reference

- Dwork & Roth, "The Algorithmic Foundations of Differential Privacy",
  Theorem 3.6 (Laplace Mechanism)
- Original result: Dwork, McSherry, Nissim, Smith (2006)
