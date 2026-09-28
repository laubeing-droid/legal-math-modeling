/-
External backport (NEURAL-BACKPORT-PROVENANCE-V1).
Upstream: https://github.com/davorrunje/neural-network-proofs
Revision: f90942517be8b66dd34574212ada69b2130a48e5
Upstream file: NeuralNetworkProofs/ForMathlib/ConvolutionIteratedDeriv.lean
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

import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Iterated derivative of a convolution (smooth, compactly-supported left factor).
Intended Mathlib home: `Mathlib/Analysis/Calculus/ContDiff/Convolution`
(confirm with maintainers). -/

namespace ConvolutionIteratedDeriv

open MeasureTheory

open scoped ContDiff

/-- For a `C^∞` compactly-supported `f` and a locally integrable `g`, the `n`-th derivative of the
real convolution `f ⋆ g` (with scalar multiplication) is the convolution of `f`'s `n`-th derivative
with `g`. (Differentiation falls on the smooth factor.) -/
theorem iteratedDeriv_convolution_left {f g : ℝ → ℝ} (n : ℕ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (hg : LocallyIntegrable g volume) :
    iteratedDeriv n (convolution f g (ContinuousLinearMap.mul ℝ ℝ) volume)
      = convolution (iteratedDeriv n f) g (ContinuousLinearMap.mul ℝ ℝ) volume := by
  -- Each iterated derivative of `f` is again `C^∞` with compact support.
  have hsmooth : ∀ m, ContDiff ℝ ∞ (iteratedDeriv m f) := by
    intro m
    rw [iteratedDeriv_eq_iterate]
    exact hf.iterate_deriv m
  have hsupp : ∀ m, HasCompactSupport (iteratedDeriv m f) := by
    intro m
    induction m with
    | zero => rwa [iteratedDeriv_zero]
    | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv
  induction n with
  | zero => rw [iteratedDeriv_zero, iteratedDeriv_zero]
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    -- `deriv (convolution (iteratedDeriv k f) g …) = convolution (deriv (iteratedDeriv k f)) g …`.
    have hderiv : deriv (convolution (iteratedDeriv k f) g (ContinuousLinearMap.mul ℝ ℝ) volume)
        = convolution (deriv (iteratedDeriv k f)) g (ContinuousLinearMap.mul ℝ ℝ) volume := by
      funext x
      exact (HasCompactSupport.hasDerivAt_convolution_left (ContinuousLinearMap.mul ℝ ℝ)
        (hsupp k) ((hsmooth k).of_le (by exact_mod_cast le_top)) hg x).deriv
    rw [hderiv, iteratedDeriv_succ]

end ConvolutionIteratedDeriv
