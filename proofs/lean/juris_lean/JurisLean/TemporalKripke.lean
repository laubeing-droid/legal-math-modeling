-- TemporalKripke.lean
-- Formal verification that in a finite temporal Kripke structure,
-- if every world satisfies t_fact < t_procedural, then the
-- LTL "always" operator □(t_fact < t_procedural) holds.
--
-- This formalizes the dual-timestamp invariant:
--   K ⊨ G(t_fact < t_procedure)
-- guaranteeing that facts always precede their procedural treatment.

import Mathlib.Data.Finset.Basic
import Mathlib.Order.RelClasses

universe u

-- ============================================================
-- Temporal World: a Kripke world with dual timestamps
-- ============================================================

structure TemporalWorld where
  id : Nat
  t_fact : Nat        -- date when facts occurred
  t_proced : Nat      -- date when procedural stage began
  deriving DecidableEq, Repr

-- ============================================================
-- Temporal Kripke Structure: finite worlds + transitions
-- ============================================================

structure TemporalKripke (n : Nat) where
  worlds : Fin n → TemporalWorld
  transitions : Fin n → Fin n → Prop

-- ============================================================
-- LTL "Always" operator via TransGen (transitive closure)
-- G(φ) holds at world i iff φ holds at i and at all
-- worlds reachable from i via the transition relation.
-- ============================================================

def ltl_always {n : Nat} (K : TemporalKripke n)
    (φ : Fin n → Prop) : Prop :=
  ∀ i, φ i ∧ ∀ j, Relation.TransGen K.transitions i j → φ j

-- ============================================================
-- Temporal Guard: t_fact < t_procedural
-- ============================================================

def temporal_guard (w : TemporalWorld) : Prop :=
  w.t_fact < w.t_proced

-- ============================================================
-- THEOREM: If every world satisfies the guard,
-- then G(guard) holds on the entire Kripke structure.
-- ============================================================

theorem temporal_guard_always {n : Nat} (K : TemporalKripke n)
    (h_all : ∀ i, temporal_guard (K.worlds i)) :
    ltl_always K (fun i => temporal_guard (K.worlds i)) := by
  intro i
  constructor
  · exact h_all i
  · intro j _
    exact h_all j

-- ============================================================
-- CONSTRUCTIVE: 3-world litigation timeline
-- ============================================================

-- World 1: facts on day 1, procedure on day 10
-- World 2: facts on day 5, procedure on day 20
-- World 3: facts on day 15, procedure on day 30

def litigation_worlds : Fin 3 → TemporalWorld
  | ⟨0, _⟩ => ⟨1, 1, 10⟩
  | ⟨1, _⟩ => ⟨2, 5, 20⟩
  | ⟨2, _⟩ => ⟨3, 15, 30⟩

def litigation_transitions : Fin 3 → Fin 3 → Prop
  | ⟨0, _⟩, ⟨1, _⟩ => True    -- W1 → W2
  | ⟨1, _⟩, ⟨2, _⟩ => True    -- W2 → W3
  | _, _ => False

def litigation_timeline : TemporalKripke 3 where
  worlds := litigation_worlds
  transitions := litigation_transitions

-- All 3 worlds satisfy the guard
lemma w0_guard : temporal_guard (litigation_timeline.worlds ⟨0, by omega⟩) := by
  exact (by decide : 1 < 10)

lemma w1_guard : temporal_guard (litigation_timeline.worlds ⟨1, by omega⟩) := by
  exact (by decide : 5 < 20)

lemma w2_guard : temporal_guard (litigation_timeline.worlds ⟨2, by omega⟩) := by
  exact (by decide : 15 < 30)

lemma all_worlds_guard :
    ∀ i, temporal_guard (litigation_timeline.worlds i) := by
  intro i
  match i with
  | ⟨0, _⟩ => exact w0_guard
  | ⟨1, _⟩ => exact w1_guard
  | ⟨2, _⟩ => exact w2_guard

-- THEOREM: The 3-world litigation timeline satisfies □(t_fact < t_proced)
theorem litigation_always_guard :
    ltl_always litigation_timeline
      (fun i => temporal_guard (litigation_timeline.worlds i)) :=
  temporal_guard_always litigation_timeline all_worlds_guard
