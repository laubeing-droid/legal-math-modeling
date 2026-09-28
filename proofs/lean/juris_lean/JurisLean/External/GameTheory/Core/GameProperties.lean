/-
External port (EXTERNAL-PORT-PROVENANCE-V1).
Upstream: https://github.com/elazarg/GameTheory
Revision: 107085bc4a0306672f2f35fce1abc1345d7975ed
Upstream file: GameTheory/Core/GameProperties.lean
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

import Mathlib.Algebra.BigOperators.Ring.Finset
import JurisLean.External.GameTheory.Core.GameForm
import JurisLean.External.GameTheory.Math.Probability

/-!
# GameTheory.Core.GameProperties
-/

open scoped BigOperators

namespace GameTheory

open Math.Probability

namespace KernelGame

variable {ι : Type}

/-- Profile `σ` Pareto-dominates profile `τ`. -/
def ParetoDominates (G : KernelGame ι) (σ τ : Profile G) : Prop :=
  (∀ i : ι, G.eu σ i ≥ G.eu τ i) ∧ ∃ i : ι, G.eu σ i > G.eu τ i

/-- Profile `σ` is Pareto-efficient (no Pareto improvement exists). -/
def IsParetoEfficient (G : KernelGame ι) (σ : Profile G) : Prop :=
  ¬ ∃ τ : Profile G, G.ParetoDominates τ σ

/-- `KernelGame.ParetoDominatesFor` delegates to `GameForm.ParetoDominatesFor`. -/
def ParetoDominatesFor (G : KernelGame ι)
    (pref spref : ι → PMF G.Outcome → PMF G.Outcome → Prop)
    (σ τ : Profile G) : Prop :=
  G.toGameForm.ParetoDominatesFor pref spref σ τ

/-- `KernelGame.IsParetoEfficientFor` delegates to `GameForm.IsParetoEfficientFor`. -/
def IsParetoEfficientFor (G : KernelGame ι)
    (pref spref : ι → PMF G.Outcome → PMF G.Outcome → Prop)
    (σ : Profile G) : Prop :=
  G.toGameForm.IsParetoEfficientFor pref spref σ

/-- EU Pareto dominance is exactly Pareto dominance with `euPref`/`euStrictPref`. -/
theorem ParetoDominates_iff_ParetoDominatesFor_eu (G : KernelGame ι)
    (σ τ : Profile G) :
    G.ParetoDominates σ τ ↔ G.ParetoDominatesFor
      (fun who d₁ d₂ => expect d₁ (fun ω => G.utility ω who) ≥ expect d₂ (fun ω => G.utility ω who))
      (fun who d₁ d₂ => expect d₁ (fun ω => G.utility ω who) > expect d₂ (fun ω => G.utility ω who))
      σ τ := by
  simp [ParetoDominates, ParetoDominatesFor, GameForm.ParetoDominatesFor, KernelGame.eu]

/-- Individual rationality w.r.t. reservation utility `r`. -/
def IsIndividuallyRational (G : KernelGame ι)
    (r : ι → ℝ) (σ : Profile G) : Prop :=
  ∀ i : ι, G.eu σ i ≥ r i

/-- Exact potential game (in expected-utility form). -/
def IsExactPotential (G : KernelGame ι) [DecidableEq ι] (Φ : Profile G → ℝ) : Prop :=
  ∀ (who : ι) (σ : Profile G) (s' : G.Strategy who),
    G.eu (Function.update σ who s') who - G.eu σ who =
      (Φ (Function.update σ who s') - Φ σ)

/-- Ordinal potential game (in expected-utility form). -/
def IsOrdinalPotential (G : KernelGame ι) [DecidableEq ι] (Φ : Profile G → ℝ) : Prop :=
  ∀ (who : ι) (σ : Profile G) (s' : G.Strategy who),
    (G.eu (Function.update σ who s') who > G.eu σ who) ↔
      (Φ (Function.update σ who s') > Φ σ)

section FinitePlayers

variable [Fintype ι]

/-- Social welfare at profile `σ` as sum of expected utilities. -/
noncomputable def socialWelfare (G : KernelGame ι) (σ : Profile G) : ℝ :=
  ∑ i : ι, G.eu σ i

/-- Constant-sum game property at the outcome-utility level. -/
def IsConstantSum (G : KernelGame ι) (c : ℝ) : Prop :=
  ∀ ω : G.Outcome, (∑ i : ι, G.utility ω i) = c

/-- Zero-sum game property at the outcome-utility level. -/
def IsZeroSum (G : KernelGame ι) : Prop :=
  G.IsConstantSum 0

/-- Team game / identical-interest property at the outcome-utility level. -/
def IsTeamGame (G : KernelGame ι) : Prop :=
  ∀ (ω : G.Outcome) (i j : ι), G.utility ω i = G.utility ω j

end FinitePlayers

end KernelGame

end GameTheory
