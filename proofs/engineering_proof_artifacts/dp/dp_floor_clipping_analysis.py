"""
DP Floor Clipping Analysis
===========================

Analyzes the privacy of floor-clipped Laplace mechanism:

    M(D) = max(0.3 * f(D), f(D) + Lap(Δ/ε))

where f(D) is the true query value (sensitive).

The floor 0.3 * f(D) depends on the sensitive data itself.
This is NOT standard post-processing and may break DP.

Verdict: DETERMINED - This mechanism does NOT satisfy ε-DP.
"""

# Encoding safety for Windows GBK consoles
import sys
if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
if hasattr(sys.stderr, "reconfigure"):
    sys.stderr.reconfigure(encoding="utf-8", errors="replace")


import numpy as np
import sympy as sp
from sympy import symbols, exp, oo, simplify, Abs, Max, Integral, oo

# ============================================================================
# 1. FORMAL SETUP
# ============================================================================

print("=" * 70)
print("DP FLOOR CLIPPING ANALYSIS")
print("=" * 70)

print("""
Mechanism Under Analysis:
    M(D) = max(0.3 * f(D), f(D) + Lap(Δ/ε))

    where:
    - f(D): true query value (sensitive, dataset-dependent)
    - Lap(b): Laplace noise with scale b = Δ/ε
    - Floor: 0.3 * f(D)  [depends on sensitive data!]

Key Question: Does M satisfy ε-DP?
""")

# ============================================================================
# 2. SYMBOLIC PRIVACY RATIO ANALYSIS
# ============================================================================

print("-" * 70)
print("2. SYMBOLIC PRIVACY RATIO ANALYSIS")
print("-" * 70)

x, f_D, f_Dp, b = symbols('x f_D f_Dp b', real=True, positive=True)
eps = symbols('eps', positive=True)

print("""
For neighboring datasets D ~ D', define:
    - f(D) = query value on D
    - f(D') = query value on D' (neighboring)
    - Δ = |f(D) - f(D')| (L1 sensitivity)
    - b = Δ/ε (noise scale)

The floor-clipped mechanism:
    M(D)  = max(0.3 * f(D),  f(D) + noise)
    M(D') = max(0.3 * f(D'), f(D') + noise')

PDF of M(D):
    For y > 0.3 * f(D):  PDF = (1/2b) * exp(-|y - f(D)|/b)
    For y = 0.3 * f(D):  point mass from the floor
    For y < 0.3 * f(D):  PDF = 0

Support(M(D))  = [0.3 * f(D), ∞)
Support(M(D')) = [0.3 * f(D'), ∞)
""")

# ============================================================================
# 3. COUNTEREXAMPLE CONSTRUCTION
# ============================================================================

print("-" * 70)
print("3. EXPLICIT COUNTEREXAMPLE")
print("-" * 70)

print("""
Consider:
    Dataset D:   f(D)  = 100
    Dataset D':  f(D') = 200
    (so Δ = 100, sensitivity)

    Let ε = 1.0, so b = Δ/ε = 100.

Mechanism outputs:
    M(D)  = max(30,  100 + Lap(100))
    M(D') = max(60,  200 + Lap(100))

The supports are:
    Support(M(D))  = [30, ∞)
    Support(M(D')) = [60, ∞)

CRITICAL OBSERVATION:
    The output value y = 45 is in Support(M(D)) but NOT in Support(M(D')).

    If we observe output y = 45, we know with CERTAINTY that the
    dataset was D (not D'), because M(D') can never output < 60.

This means:
    Pr[M(D') ∈ {45}] = 0
    Pr[M(D)  ∈ {45}] > 0

The privacy ratio is INFINITE, violating ε-DP for any finite ε.
""")

# ============================================================================
# 4. NUMERIC SIMULATION
# ============================================================================

def floor_clipped_mechanism(true_val, noise_scale, ratio=0.3, n_samples=100000):
    """
    Simulate M(D) = max(ratio * true_val, true_val + Lap(noise_scale))
    """
    noise = np.random.laplace(0, noise_scale, n_samples)
    noisy = true_val + noise
    floor_val = ratio * true_val
    return np.maximum(floor_val, noisy)


print("-" * 70)
print("4. NUMERIC SIMULATION")
print("-" * 70)

np.random.seed(42)

# Parameters
f_D = 100.0
f_Dp = 200.0
Delta = abs(f_D - f_Dp)
epsilon = 1.0
b = Delta / epsilon

print(f"\nParameters:")
print(f"  f(D)  = {f_D}")
print(f"  f(D') = {f_Dp}")
print(f"  Δ     = {Delta}")
print(f"  ε     = {epsilon}")
print(f"  b=Δ/ε = {b}")

# Simulate
samples_D = floor_clipped_mechanism(f_D, b, ratio=0.3, n_samples=200000)
samples_Dp = floor_clipped_mechanism(f_Dp, b, ratio=0.3, n_samples=200000)

print(f"\nSimulation Results (200K samples each):")
print(f"  M(D)  - min: {samples_D.min():.2f}, max: {samples_D.max():.2f}, mean: {samples_D.mean():.2f}")
print(f"  M(D') - min: {samples_Dp.min():.2f}, max: {samples_Dp.max():.2f}, mean: {samples_Dp.mean():.2f}")

# Check the gap
floor_D = 0.3 * f_D
floor_Dp = 0.3 * f_Dp
print(f"\nFloor values:")
print(f"  floor for D:   0.3 * {f_D} = {floor_D}")
print(f"  floor for D':  0.3 * {f_Dp} = {floor_Dp}")

# Check if there's a gap
if floor_D < floor_Dp:
    gap = (floor_D, floor_Dp)
    print(f"\nGAP DETECTED: [{floor_D}, {floor_Dp})")
    print(f"  Outputs in [{floor_D}, {floor_Dp}) can ONLY come from D, NEVER from D'")

    # Count how many samples from D fall in the gap
    in_gap_D = np.sum((samples_D >= floor_D) & (samples_D < floor_Dp))
    in_gap_Dp = np.sum((samples_Dp >= floor_D) & (samples_Dp < floor_Dp))
    print(f"\n  Samples from D in gap:  {in_gap_D} ({100*in_gap_D/len(samples_D):.2f}%)")
    print(f"  Samples from D' in gap: {in_gap_Dp} ({100*in_gap_Dp/len(samples_Dp):.2f}%)")

# Empirical privacy ratio in the gap
print("\nEmpirical privacy ratio analysis:")
bin_edges = np.linspace(floor_D - 5, floor_Dp + 5, 50)
hist_D, _ = np.histogram(samples_D, bins=bin_edges, density=True)
hist_Dp, _ = np.histogram(samples_Dp, bins=bin_edges, density=True)

max_ratio = 0
max_bin = None
for i in range(len(hist_D)):
    if hist_Dp[i] > 0:
        ratio = hist_D[i] / hist_Dp[i]
        if ratio > max_ratio:
            max_ratio = ratio
            max_bin = (bin_edges[i], bin_edges[i+1])
    elif hist_D[i] > 0:
        # D' has 0 density but D has positive → infinite ratio
        max_ratio = float('inf')
        max_bin = (bin_edges[i], bin_edges[i+1])

print(f"  Maximum empirical ratio: {max_ratio}")
print(f"  Bin with max ratio: {max_bin}")
print(f"  Required bound: e^ε = {np.exp(epsilon):.4f}")

if max_ratio > np.exp(epsilon) or max_ratio == float('inf'):
    print(f"\n  *** PRIVACY VIOLATION: Ratio exceeds e^ε ***")

# ============================================================================
# 5. WHERE THE FLOOR BINDS
# ============================================================================

print("\n" + "-" * 70)
print("5. FREQUENCY OF FLOOR BINDING")
print("-" * 70)

floor_bindings_D = np.sum(samples_D == floor_D)  # exact equality unlikely with continuous
# Use approximate
floor_bindings_D = np.sum(np.abs(samples_D - floor_D) < 0.5)
floor_bindings_Dp = np.sum(np.abs(samples_Dp - floor_Dp) < 0.5)

print(f"\nApproximate floor bindings (within 0.5):")
print(f"  D:   {floor_bindings_D} / {len(samples_D)} = {100*floor_bindings_D/len(samples_D):.2f}%")
print(f"  D':  {floor_bindings_Dp} / {len(samples_Dp)} = {100*floor_bindings_Dp/len(samples_Dp):.2f}%")

# More precise: fraction where floor would bind
# Floor binds when f(D) + noise < 0.3*f(D), i.e., noise < -0.7*f(D)
bind_prob_D = 0.5 * np.exp(-0.7 * f_D / b)
bind_prob_Dp = 0.5 * np.exp(-0.7 * f_Dp / b)
print(f"\nTheoretical floor binding probabilities:")
print(f"  P[floor binds | D]  = 0.5 * exp(-0.7*{f_D}/{b}) = {bind_prob_D:.6f}")
print(f"  P[floor binds | D'] = 0.5 * exp(-0.7*{f_Dp}/{b}) = {bind_prob_Dp:.6f}")

# ============================================================================
# 6. CAN WE SAVE IT WITH RESTRICTED DP?
# ============================================================================

print("\n" + "-" * 70)
print("6. RESTRICTED DP ANALYSIS")
print("-" * 70)

print("""
Idea: Maybe DP holds for outputs ABOVE both floors?

Define the 'safe region' as y >= max(0.3*f(D), 0.3*f(D')) = 0.3*max(f(D), f(D')).

In this region, both mechanisms behave like standard Laplace, so
standard DP analysis applies.

However, the floor itself leaks information:

For any output y where the floor binds for one dataset but not the other,
the mechanism reveals which dataset was used.

FORMAL RESULT: The mechanism does NOT satisfy ε-DP for any finite ε
when f(D) can take different values on neighboring datasets and
the floor depends on f(D).
""")

# Check if we can get (ε, δ)-DP
print("Can we get (ε, δ)-DP instead?")
# The "bad" event is outputting a value in the gap
# P[M(D) in gap] = P[f(D) + Lap(b) < 0.3*f(D')] when f(D) < f(D')
# This requires knowing the distribution

if f_D < f_Dp:
    # Bad for D': outputs from D in [0.3*f_D, 0.3*f_Dp) that D' can't produce
    # Actually, bad for D is outputs D can produce that D' can't
    bad_event_prob = np.mean((samples_D >= floor_D) & (samples_D < floor_Dp))
    print(f"\n  Probability of 'distinguishing' event (D vs D'):")
    print(f"  P[M(D) ∈ [{floor_D}, {floor_Dp})] ≈ {bad_event_prob:.6f}")
    print(f"  P[M(D') ∈ [{floor_D}, {floor_Dp})] = 0")
    print(f"\n  This gives (ε, δ)-DP with δ ≥ {bad_event_prob:.6f}")
    print(f"  But pure ε-DP requires δ = 0, which FAILS.")

# ============================================================================
# 7. ALTERNATIVE: PRIVATE FLOOR
# ============================================================================

print("\n" + "-" * 70)
print("7. ALTERNATIVE: PRIVATE FLOOR")
print("-" * 70)

print("""
To preserve DP, compute the floor with privacy as well:

    M_floor(D) = 0.3 * f(D) + Lap(0.3*Δ/ε₁)
    M_val(D)   = f(D) + Lap(Δ/ε₂)
    M_total(D) = max(M_floor(D), M_val(D))

By composition: total privacy cost = ε₁ + ε₂.

Simulation with private floor:
""")


def private_floor_mechanism(true_val, Delta, eps1, eps2, ratio=0.3, n_samples=100000):
    """M with private floor."""
    b1 = 0.3 * Delta / eps1  # floor noise scale
    b2 = Delta / eps2        # value noise scale

    floor_noisy = ratio * true_val + np.random.laplace(0, b1, n_samples)
    val_noisy = true_val + np.random.laplace(0, b2, n_samples)

    return np.maximum(floor_noisy, val_noisy)


# Test with private floor
eps1, eps2 = 0.5, 0.5
total_eps = eps1 + eps2

priv_D = private_floor_mechanism(f_D, Delta, eps1, eps2, n_samples=200000)
priv_Dp = private_floor_mechanism(f_Dp, Delta, eps1, eps2, n_samples=200000)

print(f"  ε₁ = {eps1}, ε₂ = {eps2}, total ε = {total_eps}")
print(f"  M_private(D)  - min: {priv_D.min():.2f}, max: {priv_D.max():.2f}")
print(f"  M_private(D') - min: {priv_Dp.min():.2f}, max: {priv_Dp.max():.2f}")

# Both have full support now
print(f"\n  Both mechanisms have full support (-∞, ∞)")
print(f"  Privacy preserved via composition: ε = {total_eps}")

# ============================================================================
# 8. VERDICT
# ============================================================================

print("\n" + "=" * 70)
print("FINAL VERDICT")
print("=" * 70)

print("""
╔══════════════════════════════════════════════════════════════════════╗
║                    DETERMINATION: DOWNGRADED                         ║
╠══════════════════════════════════════════════════════════════════════╣
║                                                                      ║
║  Mechanism:  M(D) = max(0.3*f(D), f(D) + Lap(Δ/ε))                 ║
║                                                                      ║
║  STATUS:  Does NOT satisfy ε-DP for any finite ε.                    ║
║                                                                      ║
║  REASON:  The floor 0.3*f(D) depends on the sensitive query value.  ║
║           For neighboring datasets D~D' with different f values,    ║
║           the supports of M(D) and M(D') differ.                    ║
║           Outputs in the gap [0.3*min(f), 0.3*max(f)) perfectly     ║
║           distinguish D from D'.                                    ║
║                                                                      ║
║  PRIVACY RATIO:  Infinite in the gap region.                         ║
║                                                                      ║
╠══════════════════════════════════════════════════════════════════════╣
║  REMEDIES:                                                           ║
║  1. Private floor:   max(0.3*f(D)+Lap(0.3Δ/ε₁), f(D)+Lap(Δ/ε₂))   ║
║                      Cost: ε₁ + ε₂ total privacy budget             ║
║                                                                      ║
║  2. Fixed floor:     max(F_public, f(D) + Lap(Δ/ε))                 ║
║                      Cost: F_public may be too low/high              ║
║                                                                      ║
║  3. Accept approximate DP: (ε, δ)-DP with δ > 0                     ║
║                      Cost: Weaker guarantee                          ║
╚══════════════════════════════════════════════════════════════════════╝
""")

# ============================================================================
# 9. SUMMARY OF RESULTS
# ============================================================================

results = {
    "mechanism": "max(0.3*f(D), f(D) + Lap(Δ/ε))",
    "pure_epsilon_dp": False,
    "reason": "Floor depends on sensitive data, creating differing supports",
    "privacy_ratio": "Infinite in gap region",
    "counterexample": f"f(D)={f_D}, f(D')={f_Dp}, output in [{floor_D}, {floor_Dp})",
    "remedy_1": "Private floor with composition: ε₁ + ε₂",
    "remedy_2": "Fixed public floor",
    "remedy_3": "Approximate (ε, δ)-DP with δ > 0",
}

print("Results summary:")
for k, v in results.items():
    print(f"  {k}: {v}")

print("\nAnalysis complete.")
