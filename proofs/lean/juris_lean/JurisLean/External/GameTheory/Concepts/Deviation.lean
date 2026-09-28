/-!
External port (EXTERNAL-PORT-PROVENANCE-V1).
Upstream: https://github.com/elazarg/GameTheory
Revision: 107085bc4a0306672f2f35fce1abc1345d7975ed
Upstream file: GameTheory/Concepts/Deviation.lean
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

import JurisLean.External.GameTheory.Core.KernelGame

/-!
# GameTheory.Concepts.Deviation

Minimal first-class deviation operators for kernel games.

This file introduces profile-transformers (`Deviation`) and canonical unilateral
deviation constructors, with small algebraic lemmas for reuse.
-/

namespace GameTheory

namespace KernelGame

variable {ι : Type}

/-- A deviation is a profile transformer. -/
abbrev Deviation (G : KernelGame ι) : Type _ := Profile G → Profile G

/-- Unilateral deviation induced by a recommendation-dependent map. -/
noncomputable def unilateralDeviation (G : KernelGame ι) (who : ι)
    [DecidableEq ι]
    (dev : G.Strategy who → G.Strategy who) : Deviation G :=
  fun σ => Function.update σ who (dev (σ who))

/-- Unilateral deviation to a fixed strategy. -/
noncomputable def constantDeviation (G : KernelGame ι) (who : ι)
    [DecidableEq ι]
    (s' : G.Strategy who) : Deviation G :=
  fun σ => Function.update σ who s'

/-- Player-`who` EU after applying a deviation to `σ`. -/
noncomputable def euAfterDeviation (G : KernelGame ι) (who : ι)
    (d : Deviation G) (σ : Profile G) : ℝ :=
  G.eu (d σ) who

/-- Push a profile distribution through an arbitrary profile deviation map. -/
noncomputable def deviationDistribution (G : KernelGame ι)
    (μ : PMF (Profile G)) (d : Deviation G) : PMF (Profile G) :=
  μ.bind (fun σ => PMF.pure (d σ))

/-- Push through a unilateral recommendation-dependent deviation. -/
noncomputable def unilateralDeviationDistribution (G : KernelGame ι)
    [DecidableEq ι]
    (μ : PMF (Profile G)) (who : ι)
    (dev : G.Strategy who → G.Strategy who) : PMF (Profile G) :=
  G.deviationDistribution μ (G.unilateralDeviation who dev)

/-- Push through a unilateral constant deviation. -/
noncomputable def constantDeviationDistribution (G : KernelGame ι)
    [DecidableEq ι]
    (μ : PMF (Profile G)) (who : ι) (s' : G.Strategy who) : PMF (Profile G) :=
  G.deviationDistribution μ (G.constantDeviation who s')

@[simp] theorem deviationDistribution_apply (G : KernelGame ι)
    (μ : PMF (Profile G)) (d : Deviation G) :
    G.deviationDistribution μ d = μ.bind (fun σ => PMF.pure (d σ)) := rfl

@[simp] theorem deviationDistribution_id (G : KernelGame ι) (μ : PMF (Profile G)) :
    G.deviationDistribution μ _root_.id = μ := by
  simp [deviationDistribution]

end KernelGame

end GameTheory
