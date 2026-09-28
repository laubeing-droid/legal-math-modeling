/-
External port (EXTERNAL-PORT-PROVENANCE-V1).
Upstream: https://github.com/elazarg/GameTheory
Revision: 107085bc4a0306672f2f35fce1abc1345d7975ed
Upstream file: GameTheory/Theorems/Kuhn.lean
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

import JurisLean.External.GameTheory.Theorems.Kuhn.BehavioralToMixed
import JurisLean.External.GameTheory.Theorems.Kuhn.BehavioralToMixedCore
import JurisLean.External.GameTheory.Theorems.Kuhn.CorrelatedRealization
import JurisLean.External.GameTheory.Theorems.Kuhn.KuhnModel
import JurisLean.External.GameTheory.Theorems.Kuhn.MixedToBehavioralCore
import JurisLean.External.GameTheory.Theorems.Kuhn.ObsModel

/-!
# GameTheory.Theorems.Kuhn

Kuhn's theorem: behavioral and mixed strategy equivalence.

The semantic core lives on `KuhnModel`/`ObsModelCore`:
- **B→M** (`ObsModelCore.kuhn_behavioral_to_mixed` in
  `BehavioralToMixedCore.lean`): no recall needed, but requires the semantic
  horizon-separation condition used to fold sequential randomization into an
  ex-ante product distribution.
- **M→B** (`ObsModelCore.kuhn_mixed_to_behavioral_semantic` in
  `MixedToBehavioralCore.lean`): stated over semantic step/locality
  assumptions.

`ObsModel` is the stronger snapshot-refined compatibility layer. It is
useful when a client naturally has faithful observation-history snapshots and
wants syntactic recall corollaries such as
`kuhn_mixed_to_behavioral_pspr` or automatic `HorizonSeparation`.

This file re-exports the Kuhn model, the core theorems, the migration wrappers,
and the generic outcome-equality schema types used by language-specific Kuhn
reductions.
-/

namespace GameTheory
namespace Theorems

/-- Generic behavioral -> mixed outcome-equality schema. -/
def KuhnBehavioralToMixedOutcome
    (Behavioral Pure Outcome : Type)
    (mixedOfBehavioral : Behavioral → PMF Pure)
    (evalBehavioral : Behavioral → PMF Outcome)
    (evalPure : Pure → PMF Outcome) : Prop :=
  ∀ σ : Behavioral, (mixedOfBehavioral σ).bind evalPure = evalBehavioral σ

/-- Generic mixed -> behavioral realization schema. -/
def KuhnMixedToBehavioralViaOutcome
    (Behavioral Mixed Pure Outcome : Type)
    (joint : Mixed → PMF Pure)
    (evalBehavioral : Behavioral → PMF Outcome)
    (evalPure : Pure → PMF Outcome) : Prop :=
  ∀ μ : Mixed, ∃ σ : Behavioral, evalBehavioral σ = (joint μ).bind evalPure

/-- Complete Kuhn statement (both directions) at outcome-distribution level. -/
def KuhnCompleteViaOutcome
    (Behavioral Mixed Pure Outcome : Type)
    (mixedOfBehavioral : Behavioral → PMF Pure)
    (joint : Mixed → PMF Pure)
    (evalBehavioral : Behavioral → PMF Outcome)
    (evalPure : Pure → PMF Outcome) : Prop :=
  (∀ σ : Behavioral, (mixedOfBehavioral σ).bind evalPure = evalBehavioral σ) ∧
  (∀ μ : Mixed, ∃ σ : Behavioral, evalBehavioral σ = (joint μ).bind evalPure)

end Theorems
end GameTheory
