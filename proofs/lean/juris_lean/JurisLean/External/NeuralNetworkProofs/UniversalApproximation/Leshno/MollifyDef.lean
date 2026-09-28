/-
External backport (NEURAL-BACKPORT-PROVENANCE-V1).
Upstream: https://github.com/davorrunje/neural-network-proofs
Revision: f90942517be8b66dd34574212ada69b2130a48e5
Upstream file: NeuralNetworkProofs/UniversalApproximation/Leshno/MollifyDef.lean
License: Apache-2.0 (see JurisLean/External/NeuralNetworkProofs/PROVENANCE.md
and the LICENSE copy beside it).

This copy starts byte-identical to the revision above except for this header
and the `import` roots rewritten to JurisLean.External.NeuralNetworkProofs.*.
Unlike the same-pin ports, the upstream pin (mathlib v4.32.0-rc1) differs from
this repository's (v4.30.0): mathlib API drift is repaired here edit by edit,
and every edit is logged per file in PROVENANCE.json (`adaptations`).
No build attestation is claimed: first compile pending in PENDING_CI_MODULES
(scripts/ci/check_import_reachability.py); only a green CI run of a commit
containing this file can attest it.
-/
/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Convolution
import JurisLean.External.NeuralNetworkProofs.UniversalApproximation.Leshno.ClassM

/-! # Mollification: definition and the convolution identity.

Split out of `Mollify.lean` so the consumer `Mollify.exists_nonpoly_mollify` can refer to `mollify`
and bridge to the decoupled `ConvolutionDegreeBound.exists_uniform_degree_bound` (stated over plain
`convolution`) without a circular import. -/

namespace UniversalApproximation.Leshno

open MeasureTheory

open scoped ContDiff

/-- Mollification of `σ` by a smooth compactly-supported kernel `φ` (convolution). -/
noncomputable def mollify (σ φ : ℝ → ℝ) : ℝ → ℝ :=
  fun x => ∫ y, σ (x - y) * φ y

/-- `mollify σ φ` is the Mathlib (scalar-multiplication) convolution `φ ⋆ σ`: indeed
`(φ ⋆ σ) x = ∫ t, φ t * σ (x - t)`, whose integrand agrees with `σ (x - t) * φ t` by `mul_comm`. -/
theorem mollify_eq_convolution (σ φ : ℝ → ℝ) :
    mollify σ φ = convolution φ σ (ContinuousLinearMap.mul ℝ ℝ) volume := by
  funext x
  rw [convolution_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp [mul_comm]

end UniversalApproximation.Leshno
