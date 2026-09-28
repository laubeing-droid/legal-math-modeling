/-
External port (EXTERNAL-PORT-PROVENANCE-V1).
Upstream: https://github.com/elazarg/GameTheory
Revision: 107085bc4a0306672f2f35fce1abc1345d7975ed
Upstream file: Semantics/DSMachine.lean
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

import JurisLean.External.GameTheory.Math.ProbabilityMassFunction

/-! ## Dependent-alphabet stochastic machine

A `DSMachine` is a stochastic state machine whose label (input) type depends on
the current state. This is the minimal abstraction for systems where the set of
available actions varies with state — e.g., observation-indexed actions in game
theory.
-/

/-- Dependent-alphabet stochastic machine. The label type may vary with the state. -/
structure DSMachine (σ : Type) (Label : σ → Type) where
  /-- Initial state. -/
  init : σ
  /-- Stochastic transition: given state `s` and label `l : Label s`,
  produce a distribution over next states. -/
  step : (s : σ) → Label s → PMF σ
