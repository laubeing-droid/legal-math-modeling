# Banach Contraction for Effective Nodes (Single Dimension) -- Engineering Verification

> **Nature of artifact:** Python SymPy symbolic proof + numeric verification,
> NOT a Lean formal proof.

## Proposition

For a single effective_node dimension with fixed target T:

```
f(x) = beta * T + (1 - beta) * x,    0 < beta <= 1
d(x, y) = |x - y|
```

**Theorem:** f is a contraction with factor c = |1 - beta|.

- 0 < beta < 1: c = 1 - beta in (0, 1), **strict contraction**
- beta = 1: c = 0, constant map (**strong contraction**)

**Fixed point:** x* = T (unique).

## Proof

```
d(f(x), f(y)) = |f(x) - f(y)|
               = |beta*T + (1-beta)*x - beta*T - (1-beta)*y|
               = |(1-beta)(x - y)|
               = |1-beta| * |x - y|
               = |1-beta| * d(x, y)
               < d(x, y)            when 0 < beta < 1
```

## Convergence

The Banach iteration x_{n+1} = f(x_n) converges geometrically:

```
|x_n - T| = (1 - beta)^n * |x_0 - T|
```

Steps to tolerance epsilon: n > log(epsilon / |x_0 - T|) / log(1 - beta)

## CRITICAL LIMITATION

**This is a NARROW result for a SINGLE dimension only.**

The full pricing vector update involves:

1. Multi-dimensional coupling through max/min constraints
2. Non-linear ratio-based adjustments
3. Boundary clipping operations

These do **NOT** preserve contraction across the full pricing vector
automatically. **Do NOT claim full pricing vector contraction** without a
separate proof addressing the coupled multi-dimensional case.

## Lean formalization

**`BanachEffectiveNodes.lean`** contains 8 supporting theorems for the Lean
formalization of this result (separate from these Python artifacts).

## Artifacts

| File | Description |
|------|-------------|
| `banach_effective_nodes.py` | SymPy symbolic proof + numeric verification |

## Running

```bash
python banach_effective_nodes.py
```
