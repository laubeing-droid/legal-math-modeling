/-
External port (EXTERNAL-PORT-PROVENANCE-V1).
Upstream: https://github.com/elazarg/GameTheory
Revision: 107085bc4a0306672f2f35fce1abc1345d7975ed
Upstream file: GameTheory/Concepts/ZeroSumNash.lean
License: MIT (see JurisLean/External/PROVENANCE.md for the notice).

This copy differs from the revision above in exactly two ways: this
header block, and `import` module paths rewritten to the
`JurisLean.External.*` roots. Statements and proofs are unchanged;
tests/spec/test_external_port_provenance.py re-derives the upstream
bytes from this file and checks the recorded sha256.
No build attestation is claimed here: the first compile of this port
is booked in PENDING_CI_MODULES (scripts/ci/check_import_reachability.py)
and only a green CI run of a commit containing this file can attest it.
-/
/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import JurisLean.External.GameTheory.Concepts.ZeroSum
import JurisLean.External.GameTheory.Concepts.ConstantSum
import JurisLean.External.GameTheory.Math.Probability
import JurisLean.External.GameTheory.Concepts.SolutionConcepts

/-!
# Zero-Sum Nash Properties

Interactions between zero-sum / constant-sum structure and Nash equilibria
in 2-player kernel games.

Provides:
- `IsZeroSum.nash_eu_sum_zero` — at any Nash equilibrium of a 2-player zero-sum game,
  the sum of expected utilities is zero
- `IsConstantSum.nash_eu_sum` — at any profile of a 2-player constant-sum game,
  the sum of expected utilities equals the constant
- `IsZeroSum.eu_nonneg_iff_nonpos` — in a 2-player zero-sum game, player 0 has
  non-negative EU iff player 1 has non-positive EU
- `IsZeroSum.deviation_eu_neg` — in a 2-player zero-sum game, a unilateral
  deviation's gain for player 0 is exactly the loss for player 1
-/

namespace GameTheory

open Math.Probability
namespace KernelGame

variable {ι : Type}

/-- In a 2-player zero-sum game with bounded utility, the sum of expected utilities
    at any Nash equilibrium is zero. -/
theorem IsZeroSum.nash_eu_sum_zero_of_bounded {G : KernelGame (Fin 2)}
    (hzs : G.IsZeroSum) {σ : Profile G} (_hN : G.IsNash σ)
    {C : Fin 2 → ℝ} (hbd : ∀ i ω, |G.utility ω i| ≤ C i) :
    G.eu σ 0 + G.eu σ 1 = 0 := by
  have h := hzs.eu_neg_of_bounded σ hbd
  linarith

/-- In a 2-player zero-sum game, at any Nash equilibrium the sum of expected
    utilities is zero. -/
theorem IsZeroSum.nash_eu_sum_zero {G : KernelGame (Fin 2)} [Finite G.Outcome]
    (hzs : G.IsZeroSum) {σ : Profile G} (hN : G.IsNash σ) :
    G.eu σ 0 + G.eu σ 1 = 0 := by
  classical
  choose C hbd using fun i =>
    Math.Probability.exists_abs_bound_of_finite (fun ω => G.utility ω i)
  exact hzs.nash_eu_sum_zero_of_bounded hN hbd

/-- In a 2-player constant-sum game with bounded utility, the sum of expected
    utilities at any profile equals `c`. -/
theorem IsConstantSum.nash_eu_sum_of_bounded {G : KernelGame (Fin 2)}
    {c : ℝ} (hcs : G.IsConstantSum c) (σ : Profile G)
    {C : Fin 2 → ℝ} (hbd : ∀ i ω, |G.utility ω i| ≤ C i) :
    G.eu σ 0 + G.eu σ 1 = c := by
  have h := hcs.eu_determined_of_bounded σ hbd
  linarith

/-- In a 2-player constant-sum game, at any profile the sum of expected
    utilities equals the constant `c`. -/
theorem IsConstantSum.nash_eu_sum {G : KernelGame (Fin 2)} [Finite G.Outcome]
    {c : ℝ} (hcs : G.IsConstantSum c) (σ : Profile G) :
    G.eu σ 0 + G.eu σ 1 = c := by
  classical
  choose C hbd using fun i =>
    Math.Probability.exists_abs_bound_of_finite (fun ω => G.utility ω i)
  exact hcs.nash_eu_sum_of_bounded σ hbd

/-- In a 2-player zero-sum game with bounded utility, player 0 has non-negative EU
    iff player 1 has non-positive EU. -/
theorem IsZeroSum.eu_nonneg_iff_nonpos_of_bounded {G : KernelGame (Fin 2)}
    (hzs : G.IsZeroSum) (σ : Profile G)
    {C : Fin 2 → ℝ} (hbd : ∀ i ω, |G.utility ω i| ≤ C i) :
    G.eu σ 0 ≥ 0 ↔ G.eu σ 1 ≤ 0 := by
  have h := hzs.eu_neg_of_bounded σ hbd
  constructor
  · intro h0; linarith
  · intro h1; linarith

/-- In a 2-player zero-sum game, player 0 has non-negative expected utility
    if and only if player 1 has non-positive expected utility. -/
theorem IsZeroSum.eu_nonneg_iff_nonpos {G : KernelGame (Fin 2)} [Finite G.Outcome]
    (hzs : G.IsZeroSum) (σ : Profile G) :
    G.eu σ 0 ≥ 0 ↔ G.eu σ 1 ≤ 0 := by
  classical
  choose C hbd using fun i =>
    Math.Probability.exists_abs_bound_of_finite (fun ω => G.utility ω i)
  exact hzs.eu_nonneg_iff_nonpos_of_bounded σ hbd

open Classical in
/-- In a 2-player zero-sum game with bounded utility, the change in player 0's EU
    from a unilateral deviation equals the negation of the change in player 1's EU. -/
theorem IsZeroSum.deviation_eu_neg_of_bounded {G : KernelGame (Fin 2)}
    (hzs : G.IsZeroSum) (σ : Profile G) (s' : G.Strategy 0)
    {C : Fin 2 → ℝ} (hbd : ∀ i ω, |G.utility ω i| ≤ C i) :
    G.eu (Function.update σ 0 s') 0 - G.eu σ 0 =
    -(G.eu (Function.update σ 0 s') 1 - G.eu σ 1) := by
  have h1 := hzs.eu_neg_of_bounded σ hbd
  have h2 := hzs.eu_neg_of_bounded (Function.update σ 0 s') hbd
  linarith

open Classical in
/-- In a 2-player zero-sum game, the change in player 0's expected utility from
    a unilateral deviation is exactly the negation of the change in player 1's
    expected utility. -/
theorem IsZeroSum.deviation_eu_neg {G : KernelGame (Fin 2)} [Finite G.Outcome]
    (hzs : G.IsZeroSum) (σ : Profile G) (s' : G.Strategy 0) :
    G.eu (Function.update σ 0 s') 0 - G.eu σ 0 =
    -(G.eu (Function.update σ 0 s') 1 - G.eu σ 1) := by
  classical
  choose C hbd using fun i =>
    Math.Probability.exists_abs_bound_of_finite (fun ω => G.utility ω i)
  exact hzs.deviation_eu_neg_of_bounded σ s' hbd

end KernelGame
end GameTheory
