/-
External port (EXTERNAL-PORT-PROVENANCE-V1).
Upstream: https://github.com/elazarg/GameTheory
Revision: 107085bc4a0306672f2f35fce1abc1345d7975ed
Upstream file: GameTheory/Theorems/Kuhn/BehavioralToMixed.lean
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

import JurisLean.External.GameTheory.Theorems.Kuhn.ObsModel
import JurisLean.External.GameTheory.Theorems.Kuhn.BehavioralToMixedCore

/-! # Behavioral -> Mixed direction of Kuhn's theorem for `ObsModel`

This file provides the `ObsModel` wrapper around the core behavioral-to-mixed
theorem.

The main core theorem is stated for `ObsModelCore` under the hypothesis
`NoNontrivialInfoStateRepeat`. For `ObsModel`, this condition holds
automatically because snapshot-refined information states cannot repeat along a
trace unless their action space is trivial.

The theorem `ObsModel.kuhn_behavioral_to_mixed` is therefore obtained by
instantiating the core theorem on `O.toCore`.
-/

set_option autoImplicit false

namespace ObsModel

variable {ι σ : Type} {Obs : ι → Type} {Act : (i : ι) → Obs i → Type}
variable {O : ObsModel ι σ Obs Act}

section CoreInstances

variable [hInfo : ∀ i, Fintype (O.InfoState i)]

noncomputable instance infoStateFintype_toCore :
    ∀ i, Fintype (O.toCore.InfoState i) := by
  intro i
  simpa [ObsModel.toCore, ObsModelCore.InfoState, ObsModel.InfoState] using
    (hInfo i)

end CoreInstances

section Definitions

variable [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]
variable [∀ i, Fintype (O.InfoState i)]

open Classical in
/-- Convert a behavioral profile to per-player mixed strategies by taking the
independent product over information states for each player. -/
noncomputable abbrev behavioralToMixed
    (β : BehavioralProfile O) : ∀ i, PMF (O.LocalStrategy i) :=
  O.toCore.behavioralToMixed β

open Classical in
/-- The full product mixed strategy: first over information states per player,
then over players. -/
noncomputable abbrev behavioralToMixedJoint
    [∀ i, Fintype (O.LocalStrategy i)]
    (β : BehavioralProfile O) : PMF (PureProfile O) :=
  O.toCore.behavioralToMixedJoint β

end Definitions

section NoNontrivialInfoStateRepeat

/-- Snapshot-refined information states satisfy the core non-repetition
condition required for the behavioral-to-mixed theorem. -/
theorem noNontrivialInfoStateRepeat_toCore
    [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]
    (O : ObsModel ι σ Obs Act) :
    O.toCore.NoNontrivialInfoStateRepeat := by
  intro i π k ss hreach j₁ j₂ hjlt hjlen hEq
  have hdepth :
      O.stateDepth i (O.toCore.projectStates i (ss.take (j₁ + 1))) =
      O.stateDepth i (O.toCore.projectStates i (ss.take (j₂ + 1))) := by
    simpa [ObsModel.toCore, ObsModelCore.InfoState, ObsModel.InfoState] using
      congrArg (O.stateDepth i) hEq
  have hlenEq : j₁ + 1 = j₂ + 1 := by
    rw [O.stateDepth_projectStates i (ss.take (j₁ + 1)),
        O.stateDepth_projectStates i (ss.take (j₂ + 1))] at hdepth
    have hj₁len : j₁ + 1 ≤ ss.length := by omega
    have hj₂len : j₂ + 1 ≤ ss.length := by omega
    simpa [List.length_take, hj₁len, hj₂len] using hdepth
  omega

end NoNontrivialInfoStateRepeat

section HorizonSeparation

/-- Snapshot-refined information states cannot recur at different horizons. -/
theorem horizonSeparation_toCore (O : ObsModel ι σ Obs Act) :
    O.toCore.HorizonSeparation := by
  intro i ss ss' hEq hlt
  have hlen : ss.length = ss'.length := by
    simpa [O.stateDepth_projectStates i ss, O.stateDepth_projectStates i ss'] using
      congrArg (O.stateDepth i) hEq
  omega

end HorizonSeparation

section MainTheorem

variable [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]
variable [∀ i, Fintype (O.InfoState i)]

open Classical in
/-- **Kuhn's theorem, behavioral-to-mixed direction for `ObsModel`.**
Every behavioral profile induces the same bounded trace distribution as the
corresponding product mixed strategy. -/
theorem kuhn_behavioral_to_mixed
    [∀ i, Fintype (O.LocalStrategy i)]
    (β : BehavioralProfile O) (k : Nat) :
    O.runDist k β =
      (O.behavioralToMixedJoint β).bind (fun π => O.runDistPure k π) := by
  simpa [ObsModel.runDist, ObsModel.runDistPure, ObsModel.behavioralToMixedJoint,
    ObsModel.behavioralToMixed, ObsModel.toCore] using
    (ObsModelCore.kuhn_behavioral_to_mixed (O := O.toCore)
      (hNontriv := O.noNontrivialInfoStateRepeat_toCore) β k)

end MainTheorem

end ObsModel
