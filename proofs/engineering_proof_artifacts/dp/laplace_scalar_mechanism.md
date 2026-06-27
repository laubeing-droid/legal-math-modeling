# Standard Scalar Laplace Mechanism: Proof of epsilon-Differential Privacy

> **Nature of artifact:** Mathematical proof written as documentation, verified
> by reference to Dwork & Roth Theorem 3.6.

## Theorem

Let f: D -> R be a scalar-valued query function with L1-sensitivity:

```
Delta_1(f) = max_{D ~ D'} |f(D) - f(D')|
```

where D ~ D' denotes neighboring datasets (differing in at most one record).

The mechanism M defined as:

```
M(D) = f(D) + Lap(Delta_1(f) / epsilon)
```

satisfies **epsilon-differential privacy**, where Lap(b) denotes the Laplace
distribution with scale parameter b and PDF:

```
Lap(b; x) = (1 / 2b) * exp(-|x| / b)
```

## Assumptions

1. **Scalar output:** f(D) in R (single real value)
2. **Finite sensitivity:** Delta_1(f) < infinity
3. **Neighboring relation:** D and D' differ in exactly one record
   (replacement or addition/deletion model)
4. **Privacy parameter:** epsilon > 0
5. **Standard Laplace noise:** Independent noise drawn from Lap(Delta / epsilon)

## Proof

### Step 1: PDF ratio for neighboring datasets

For any output y in R and neighboring datasets D ~ D':

```
Pr[M(D) = y]     (1/2b) * exp(-|y - f(D)| / b)
------------  =  --------------------------------  =  exp((|y - f(D')| - |y - f(D)|) / b)
Pr[M(D') = y]    (1/2b) * exp(-|y - f(D')| / b)
```

where b = Delta_1(f) / epsilon.

### Step 2: Apply the reverse triangle inequality

```
|y - f(D')| - |y - f(D)|  <=  |f(D) - f(D')|
```

By definition of sensitivity:

```
|f(D) - f(D')|  <=  Delta_1(f)
```

### Step 3: Bound the ratio

```
Pr[M(D) = y]
------------  <=  exp(Delta_1(f) / b)
Pr[M(D') = y]

             =  exp(Delta_1(f) / (Delta_1(f) / epsilon))

             =  exp(epsilon)

             =  e^epsilon
```

### Step 4: Integrate over any event S

For any measurable set S subset R:

```
Pr[M(D) in S]     integral_S Pr[M(D) = y] dy
--------------  =  -----------------------------  <=  max_y (Pr[M(D)=y] / Pr[M(D')=y])  <=  e^epsilon
Pr[M(D') in S]    integral_S Pr[M(D') = y] dy
```

Therefore: **Pr[M(D) in S] <= e^epsilon * Pr[M(D') in S]** for all measurable S. QED.

## Sensitivity in different models

| Model | Neighboring definition | Delta_1 for sum query |
|-------|------------------------|-----------------------|
| Add/Delete | D' = D union {x} or D \ {x} | max_x |x| |
| Replace | D' replaces one element | 2 * max_x |x| |

## Key properties

1. **Privacy-utility tradeoff:** Smaller epsilon -> larger noise -> less accuracy
2. **Scale calibration:** Noise scale b = Delta / epsilon is TIGHT (optimal for single query)
3. **Post-processing immunity:** Any deterministic function g applied to M(D)
   preserves epsilon-DP (by post-processing theorem)

## Reference

- Dwork & Roth, "The Algorithmic Foundations of Differential Privacy",
  Theorem 3.6 (Laplace Mechanism)
- Original result: Dwork, McSherry, Nissim, Smith (2006)
