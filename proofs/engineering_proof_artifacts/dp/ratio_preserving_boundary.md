# Ratio-Preserving Boundary: Post-Processing vs. Structure Leakage

> **Nature of artifact:** Engineering analysis of a specific DP mechanism
> variant, with formal privacy ratio argument.

## Problem statement

Given a DP mechanism M(D) = f(D) + Lap(Delta / epsilon), consider a
deterministic "ratio-preserving boundary" transformation:

```
g(y) = max(0.3 * f(D), y)
```

where y = M(D) = f(D) + noise. This ensures the output is at least 30% of
the original (non-private) query value f(D).

**Question:** Does g preserve differential privacy? Or does the dependency on
f(D) leak structure and break the DP guarantee?

## Analysis

### Case 1: g depends on the NOISY output only -- PRESERVES DP

If the boundary is computed from the noisy output alone:

```
g(y) = max(0.3 * y, y) = y     (trivial)
```

This is post-processing and preserves epsilon-DP by the post-processing
theorem.

### Case 2: g depends on the TRUE f(D) -- BREAKS DP

If the boundary depends on the true (non-private) query value:

```
g(y; f(D)) = max(0.3 * f(D), y)
```

where y = f(D) + Lap(Delta / epsilon), this creates a **privacy risk**.

### Why Case 2 leaks information

Consider two neighboring datasets D ~ D' with f(D) = 100 and f(D') = 200.

**For dataset D (f(D) = 100):**
- Floor = 0.3 * 100 = 30
- Output: max(30, 100 + noise)
- If we observe output = 30, we know 100 + noise <= 30, i.e., noise <= -70

**For dataset D' (f(D') = 200):**
- Floor = 0.3 * 200 = 60
- Output: max(60, 200 + noise)
- Output = 30 is **impossible** (minimum is 60)

### The problem

The floor value **depends on f(D) itself**, which differs between neighboring
datasets. The supports diverge:

```
Support(M*(D))  = [0.3 * f(D),  infinity)
Support(M*(D')) = [0.3 * f(D'), infinity)
```

If f(D) != f(D'), the supports differ. An output in the gap between
0.3 * min(f(D), f(D')) and 0.3 * max(f(D), f(D')) reveals which dataset was
used with **certainty**.

### Formal privacy ratio analysis

For output y where the floor binds (y = 0.3 * f(D)):

```
Pr[M*(D) = y]  = Pr[Lap = y - f(D)]    when y >= 0.3 * f(D)
Pr[M*(D') = y] = 0                       when y <  0.3 * f(D')
```

The ratio is **infinite**, violating the e^epsilon bound for any finite
epsilon.

## Verdict

The ratio-preserving floor max(0.3 * f(D), y) that depends on f(D) is
**NOT valid post-processing**. It breaks epsilon-DP because the floor itself
is a function of the sensitive data, not just the mechanism output.

**The current form must be downgraded.**

## Possible remedies

### Option A: Private floor (restricted DP)

Compute the floor with DP as well:

```
M_floor(D) = 0.3 * f(D) + Lap(0.3 * Delta / epsilon_floor)
M_val(D)   = f(D) + Lap(Delta / epsilon_val)
Output     = max(M_floor(D), M_val(D))
```

With composition: total epsilon = epsilon_floor + epsilon_val.
Result: epsilon-DP is preserved but the guarantee requires accounting for
the privacy cost of the floor computation.

### Option B: Fixed public floor (preserves DP)

Use a fixed, data-independent floor F:

```
Output = max(F, f(D) + Lap(Delta / epsilon))
```

This is valid post-processing (F is public, independent of D).
Result: epsilon-DP preserved, but may not provide the desired ratio guarantee.

### Option C: Smooth private floor (approximate DP)

Use a smooth (Lipschitz) approximation of the max operation that does not
create hard boundaries:

```
Output = smooth_max(0.3 * M_f(D), M_val(D))
```

where smooth_max is a soft maximum with bounded sensitivity.

## Summary

| Approach | Privacy | Ratio guarantee |
|----------|---------|-----------------|
| max(0.3 * f(D), noisy) | **BREAKS DP** | Strong |
| max(0.3 * noisy_f, noisy) | Preserves DP | Weak (noisy floor) |
| Fixed public floor | Preserves DP | None (fixed) |
| Private floor + composition | (epsilon_1 + epsilon_2)-DP | Moderate |
| Smooth approximation | Approximate DP | Moderate |

## Recommendation

Either:
1. Account for the privacy cost of computing the floor, OR
2. Use a fixed public floor, OR
3. Accept that the ratio guarantee is not achievable under pure epsilon-DP
