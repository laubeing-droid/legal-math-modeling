# Banach Contraction Proof for Effective Nodes (Single Dimension)

## Status: PROVED (narrow)

## Proposition

For a single effective_node dimension with fixed target T:

```
f(x) = βT + (1-β)x,   where 0 < β <= 1
d(x,y) = |x - y|
```

**Theorem:** f is a contraction with factor c = |1-β|.

- When 0 < β < 1: c = 1-β ∈ (0,1), **strict contraction**
- When β = 1: c = 0, constant map (**strong contraction**)

**Fixed point:** x* = T (unique)

## Proof Summary

```
d(f(x), f(y)) = |f(x) - f(y)|
               = |βT + (1-β)x - βT - (1-β)y|
               = |(1-β)(x - y)|
               = |1-β| · |x - y|
               = |1-β| · d(x,y)
               < d(x,y)    when 0 < β < 1
```

## Files

| File | Description |
|------|-------------|
| `banach_effective_nodes.py` | SymPy symbolic proof + numeric verification |
| `BanachEffectiveNodes.lean` | Lean 4 formal proof draft (PENDING_TOOLCHAIN) |

## Verification

Run the Python proof:
```bash
python banach_effective_nodes.py
```

## CRITICAL LIMITATION

**This is a NARROW result for a SINGLE dimension only.**

The full pricing vector update involves:
1. Multi-dimensional coupling through max/min constraints
2. Non-linear ratio-based adjustments
3. Boundary clipping operations

These do NOT preserve contraction across the full vector automatically.
**Do NOT claim full pricing vector contraction** without a separate proof.

## Convergence

The Banach iteration x_{n+1} = f(x_n) converges geometrically:

```
|x_n - T| = (1-β)^n · |x_0 - T|
```

Steps to tolerance ε: n > log(ε/|x_0 - T|) / log(1-β)
