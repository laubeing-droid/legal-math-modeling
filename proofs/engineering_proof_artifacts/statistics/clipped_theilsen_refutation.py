"""
Clipped Theil-Sen Refutation
==============================

REFUTES the claim that a "clipped" Theil-Sen estimator equals
the pure Theil-Sen estimator.

The pure Theil-Sen estimator:
    β_TS = median{(y_j - y_i) / (x_j - x_i) : i < j}

A "clipped" implementation may:
1. Filter out slopes outside a valid range (e.g., exclude NaN, inf)
2. Clamp (clip) extreme slope values to bounds
3. Apply additional preprocessing

This module proves via explicit counterexample that these operations
change the estimator output.
"""

# Encoding safety for Windows GBK consoles
import sys
if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
if hasattr(sys.stderr, "reconfigure"):
    sys.stderr.reconfigure(encoding="utf-8", errors="replace")


import math

# ============================================================================
# 0. HAND-WRITTEN MEDIAN (no external dependencies)
# ============================================================================

def _median(vals):
    """Hand-written median. Pure Python, no scipy/numpy required."""
    if not vals:
        return 0.0
    s = sorted(vals)
    n = len(s)
    mid = n // 2
    if n % 2 == 1:
        return float(s[mid])
    return (s[mid - 1] + s[mid]) / 2.0


# ============================================================================
# 1. PURE THEIL-SEN ESTIMATOR (reference)
# ============================================================================

def pure_theil_sen_slope(x, y):
    """
    Pure Theil-Sen estimator: median of ALL pairwise slopes.
    Reference implementation with no clipping or filtering.
    """
    n = len(x)
    if n < 2:
        return 0.0
    slopes = []
    for i in range(n):
        for j in range(i + 1, n):
            dx = x[j] - x[i]
            if abs(dx) > 1e-15:
                slope = (y[j] - y[i]) / dx
                slopes.append(slope)
    if not slopes:
        return 0.0
    return _median(slopes)


# ============================================================================
# 2. CLIPPED THEIL-SEN ESTIMATOR
# ============================================================================

def clipped_theil_sen_slope(x, y, slope_clip=None, value_clip=None):
    """
    Clipped Theil-Sen: applies slope and/or value clipping.
    """
    n = len(x)
    if n < 2:
        return 0.0
    slopes = []
    for i in range(n):
        for j in range(i + 1, n):
            dx = x[j] - x[i]
            if abs(dx) > 1e-15:
                slope = (y[j] - y[i]) / dx
                slopes.append(slope)
    if not slopes:
        return 0.0
    if slope_clip is not None:
        lo, hi = slope_clip
        slopes = [max(lo, min(hi, s)) for s in slopes]
    result = _median(slopes)
    if value_clip is not None:
        v_lo, v_hi = value_clip
        result = max(v_lo, min(v_hi, result))
    return result


# ============================================================================
# 3. FILTERED THEIL-SEN
# ============================================================================

def filtered_theil_sen_slope(x, y, pct_low=0.0, pct_high=100.0):
    """
    Filtered Theil-Sen: excludes slopes outside percentiles.
    """
    n = len(x)
    if n < 2:
        return 0.0
    slopes = []
    for i in range(n):
        for j in range(i + 1, n):
            dx = x[j] - x[i]
            if abs(dx) > 1e-15:
                slope = (y[j] - y[i]) / dx
                slopes.append(slope)
    if not slopes:
        return 0.0
    # Compute percentiles by sorting
    s_sorted = sorted(slopes)
    n_slopes = len(s_sorted)
    lo_idx = int(n_slopes * pct_low / 100.0)
    hi_idx = int(n_slopes * pct_high / 100.0)
    lo_idx = max(0, min(lo_idx, n_slopes - 1))
    hi_idx = max(lo_idx, min(hi_idx, n_slopes - 1))
    filtered = s_sorted[lo_idx:hi_idx + 1]
    if not filtered:
        return _median(slopes)
    return _median(filtered)


# ============================================================================
# 4. SHOW ALL PAIRWISE SLOPES (for analysis)
# ============================================================================

def all_pairwise_slopes(x, y):
    """Return sorted list of all pairwise slopes."""
    slopes = []
    details = []
    n = len(x)
    for i in range(n):
        for j in range(i + 1, n):
            dx = x[j] - x[i]
            if abs(dx) > 1e-15:
                s = (y[j] - y[i]) / dx
                slopes.append(s)
                details.append((i, j, s))
    return sorted(slopes), details


# ============================================================================
# 5. COUNTEREXAMPLES
# ============================================================================

print("=" * 72)
print("  CLIPPED THEIL-SEN ≠ PURE THEIL-SEN: REFUTATION")
print("=" * 72)

results = []

# -------------------------------------------------------------------------
# COUNTEREXAMPLE 1: VALUE CLIPPING (always works when pure > clip bound)
# -------------------------------------------------------------------------
print("\n" + "─" * 72)
print("COUNTEREXAMPLE 1: Value Clipping Changes Output")
print("─" * 72)

# Dataset: quadratic-like, pure median slope will be large
x1 = [1.0, 2.0, 3.0, 4.0, 5.0]
y1 = [1.0, 10.0, 30.0, 60.0, 100.0]
slopes_1, _ = all_pairwise_slopes(x1, y1)
pure1 = pure_theil_sen_slope(x1, y1)
clip1 = clipped_theil_sen_slope(x1, y1, value_clip=(-10.0, 10.0))

print(f"x = {x1}")
print(f"y = {y1}")
print(f"All slopes: {[round(s, 2) for s in slopes_1]}")
print(f"Pure Theil-Sen:        {pure1:.4f}")
print(f"Value clipped to ±10:  {clip1:.4f}")
diff1 = abs(pure1 - clip1)
print(f"DIFFERENCE:            {diff1:.4f}")
if diff1 > 1e-10:
    print("  ★ VALUE-CLIPPED ≠ PURE: REFUTED ★")
results.append(("CE1: Value clip", pure1, clip1, diff1))

# -------------------------------------------------------------------------
# COUNTEREXAMPLE 2: SLOPE CLIPPING (median itself is outside clip bounds)
# -------------------------------------------------------------------------
print("\n" + "─" * 72)
print("COUNTEREXAMPLE 2: Slope Clipping Changes Median")
print("─" * 72)

# KEY DESIGN: 5 points → 10 slopes. Make the 5th/6th slopes (median) > 10.
# Use a concave shape: starts flat, then shoots up steeply.
# Slopes should be: small, small, small, BIG, BIG, BIG, BIG, BIG, BIG, BIG
# Pure median = average of 5th+6th (for 10 slopes) = should be BIG
# Clip to [-2, 5]: all BIG slopes become 5, shifting median down.
x2 = [0.0, 1.0, 2.0, 3.0, 4.0, 5.0]
y2 = [0.0, 0.5, 1.0, 2.0, 50.0, 100.0]
# Slopes: 0.5, 0.5, 0.67, 16.67, 25, 0.5, 16.67, 24.83, 49.5, 50

slopes_2, _ = all_pairwise_slopes(x2, y2)
sorted_s2 = sorted(slopes_2)
pure2 = pure_theil_sen_slope(x2, y2)
clip2 = clipped_theil_sen_slope(x2, y2, slope_clip=(-2.0, 5.0))

print(f"x = {x2}")
print(f"y = {y2}")
print(f"All {len(slopes_2)} slopes (sorted): {[round(s, 2) for s in sorted_s2]}")
print(f"Pure Theil-Sen:         {pure2:.4f}")
print(f"Clipped slopes [-2,5]:  {clip2:.4f}")
diff2 = abs(pure2 - clip2)
print(f"DIFFERENCE:             {diff2:.4f}")
if diff2 > 1e-10:
    print("  ★ SLOPE-CLIPPED ≠ PURE: REFUTED ★")
results.append(("CE2: Slope clip", pure2, clip2, diff2))

# -------------------------------------------------------------------------
# COUNTEREXAMPLE 3: PERCENTILE FILTERING
# -------------------------------------------------------------------------
print("\n" + "─" * 72)
print("COUNTEREXAMPLE 3: Percentile Filtering Changes Median")
print("─" * 72)

# Design: 7 points → 21 slopes. Make the median (11th) depend on extremes.
# Removing top/bottom 25% (5 slopes each) changes the median position.
x3 = [0.0, 1.0, 2.0, 3.0, 4.0, 5.0, 6.0]
y3 = [0.0, 10.0, -8.0, 30.0, -5.0, 50.0, 3.0]

slopes_3, _ = all_pairwise_slopes(x3, y3)
sorted_s3 = sorted(slopes_3)
pure3 = pure_theil_sen_slope(x3, y3)
filt3_1090 = filtered_theil_sen_slope(x3, y3, pct_low=10.0, pct_high=90.0)

print(f"x = {x3}")
print(f"y = {y3}")
print(f"All {len(slopes_3)} slopes (sorted): {[round(s, 2) for s in sorted_s3]}")
print(f"Pure Theil-Sen:           {pure3:.4f}")
print(f"Filtered (10-90%):        {filt3_1090:.4f}")
diff3 = abs(pure3 - filt3_1090)
print(f"DIFFERENCE:               {diff3:.4f}")
if diff3 > 1e-10:
    print("  ★ FILTERED ≠ PURE: REFUTED ★")
results.append(("CE3: Filter 10-90%", pure3, filt3_1090, diff3))

# -------------------------------------------------------------------------
# COUNTEREXAMPLE 4: EXTREME OUTLIER WITH TIGHT CLIP
# -------------------------------------------------------------------------
print("\n" + "─" * 72)
print("COUNTEREXAMPLE 4: Extreme Outlier with Tight Slope Clip")
print("─" * 72)

# Design: median slope must be > upper clip bound.
# 6 points → 15 slopes. Need 8th slope > 3.
# Create asymmetric data: gentle left side, explosive right side.
x4 = [0.0, 1.0, 2.0, 3.0, 4.0, 5.0]
y4 = [0.0, 1.0, 3.0, 6.0, 50.0, 120.0]
# Many pairwise slopes involve the last point and will be huge.

slopes_4, _ = all_pairwise_slopes(x4, y4)
sorted_s4 = sorted(slopes_4)
pure4 = pure_theil_sen_slope(x4, y4)
clip4_tight = clipped_theil_sen_slope(x4, y4, slope_clip=(-1.0, 3.0))

print(f"x = {x4}")
print(f"y = {y4}")
print(f"All {len(slopes_4)} slopes (sorted): {[round(s, 2) for s in sorted_s4]}")
print(f"Pure Theil-Sen:       {pure4:.4f}")
print(f"Clipped [-1, 3]:      {clip4_tight:.4f}")
diff4 = abs(pure4 - clip4_tight)
print(f"DIFFERENCE:           {diff4:.4f}")
if diff4 > 1e-10:
    print("  ★ CLIPPED ≠ PURE: REFUTED ★")
results.append(("CE4: Tight clip", pure4, clip4_tight, diff4))

# -------------------------------------------------------------------------
# COUNTEREXAMPLE 5: BOTH VALUE AND SLOPE CLIPPING
# -------------------------------------------------------------------------
print("\n" + "─" * 72)
print("COUNTEREXAMPLE 5: Both Slope AND Value Clipping")
print("─" * 72)

# Design: pure median is ~15, which exceeds both slope clip [−3,3] and value clip ±5
x5 = [0.0, 1.0, 2.0, 3.0, 4.0, 5.0]
y5 = [0.0, 5.0, 15.0, 35.0, 60.0, 90.0]
# Steep increasing sequence

slopes_5, _ = all_pairwise_slopes(x5, y5)
sorted_s5 = sorted(slopes_5)
pure5 = pure_theil_sen_slope(x5, y5)
clip5 = clipped_theil_sen_slope(x5, y5, slope_clip=(-3.0, 3.0), value_clip=(-5.0, 5.0))

print(f"x = {x5}")
print(f"y = {y5}")
print(f"All {len(slopes_5)} slopes (sorted): {[round(s, 2) for s in sorted_s5]}")
print(f"Pure Theil-Sen:                {pure5:.4f}")
print(f"Slope clip [-3,3] + val ±5:    {clip5:.4f}")
diff5 = abs(pure5 - clip5)
print(f"DIFFERENCE:                    {diff5:.4f}")
if diff5 > 1e-10:
    print("  ★ DOUBLE-CLIPPED ≠ PURE: REFUTED ★")
results.append(("CE5: Both clips", pure5, clip5, diff5))

# -------------------------------------------------------------------------
# COUNTEREXAMPLE 6: CONSTRUCTED EXACT CASE
# -------------------------------------------------------------------------
print("\n" + "─" * 72)
print("COUNTEREXAMPLE 6: Exact Construction")
print("─" * 72)

# 8 points → 28 slopes. Design so median is pulled high by extreme points.
# Use a "fan" shape: one anchor point, others spread far apart.
# The slopes from the anchor to far points will be huge.
x6 = [0.0, 1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0]
y6 = [0.0, 0.0, 0.0, 0.0, 100.0, 100.0, 100.0, 100.0]
# Slopes between {0,1,2,3} and {4,5,6,7} will be very large (100/1 to 100/7)
# Slopes within each group will be 0

slopes_6, _ = all_pairwise_slopes(x6, y6)
sorted_s6 = sorted(slopes_6)
pure6 = pure_theil_sen_slope(x6, y6)
clip6 = clipped_theil_sen_slope(x6, y6, slope_clip=(-5.0, 5.0))

print(f"x = {x6}")
print(f"y = {y6}")
print(f"All {len(slopes_6)} slopes (sorted): {[round(s, 2) for s in sorted_s6]}")
print(f"Pure Theil-Sen:       {pure6:.4f}")
print(f"Clipped [-5, 5]:      {clip6:.4f}")
diff6 = abs(pure6 - clip6)
print(f"DIFFERENCE:           {diff6:.4f}")
if diff6 > 1e-10:
    print("  ★ CLIPPED ≠ PURE: REFUTED ★")
results.append(("CE6: Exact construction", pure6, clip6, diff6))


# ============================================================================
# 6. SUMMARY
# ============================================================================

print("\n" + "=" * 72)
print("  SUMMARY OF ALL COUNTEREXAMPLES")
print("=" * 72)

print(f"\n{'Counterexample':<28} {'Pure':>10} {'Clipped':>10} {'Diff':>10}  Verdict")
print("─" * 72)
all_refuted = True
for name, pure, clipped, diff in results:
    verdict = "REFUTED" if diff > 1e-10 else "coincident"
    if diff <= 1e-10:
        all_refuted = False
    print(f"{name:<28} {pure:>10.4f} {clipped:>10.4f} {diff:>10.4f}  {verdict}")

print("\n" + "=" * 72)
print("  FORMAL ARGUMENT")
print("=" * 72)
print("""
Theorem: For any clipping bounds [L, U] and any dataset D where at
least one pairwise slope lies outside [L, U], the clipped Theil-Sen
estimator differs from the pure Theil-Sen estimator with positive
probability (over the choice of dataset).

Proof:
  1. Let S = {s_1, ..., s_N} be all pairwise slopes, sorted.
  2. Let S' = {clip(s_i, L, U)} where clip(s) = max(L, min(U, s)).
  3. If ∃i: s_i < L or s_i > U, then S ≠ S' as multisets.
  4. The median is a non-constant function of the sorted multiset.
  5. Therefore median(S) ≠ median(S') for generic datasets.

Corollary: The ONLY case where clipping preserves the estimator is
when ALL slopes naturally fall within [L, U], making clipping a no-op.
""")

print("=" * 72)
print("  FINAL VERDICT")
print("=" * 72)

if any(diff > 1e-10 for _, _, _, diff in results):
    print("""
╔══════════════════════════════════════════════════════════════════════╗
║         CLAIM REFUTED: Clipped Theil-Sen ≠ Pure Theil-Sen           ║
╠══════════════════════════════════════════════════════════════════════╣
║                                                                      ║
║  At least one counterexample shows a non-zero difference.            ║
║  Clipping/filtering slopes changes the estimator output.             ║
║                                                                      ║
║  The pure Theil-Sen estimator (median of ALL slopes) is the         ║
║  ONLY form with the theoretical 50% breakdown point guarantee.       ║
╚══════════════════════════════════════════════════════════════════════╝
""")
else:
    print("All cases coincident — this is unusual; verify datasets.")

print("\nRefutation complete.")
