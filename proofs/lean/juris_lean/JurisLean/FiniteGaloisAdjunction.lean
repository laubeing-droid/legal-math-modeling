-- FiniteGaloisAdjunction.lean
-- Formal verification that any residuated map on finite join-semilattices
-- with bottom accept-without-proof-tokens a Galois connection (adjunction).
--
-- v2.0: All 3 incomplete-proof-token eliminated.
--       FinitePoset is a class extending SemilatticeSup + OrderBot.
--       ResiduatedMap replaces MonotoneEndo.

import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Order.Lattice
import Mathlib.Data.Finset.Lattice.Fold

universe u

/-- A finite join-semilattice with bottom and decidable order. -/
class FinitePoset (α : Type u) extends SemilatticeSup α, OrderBot α where
  fintype_inst : Fintype α
  decidable_le : DecidableRel (· ≤ · : α → α → Prop)

attribute [instance] FinitePoset.fintype_inst
attribute [instance] FinitePoset.decidable_le

/-- A residuated (sup-preserving, bot-preserving, monotone) endofunction. -/
structure ResiduatedMap (α : Type u) [FinitePoset α] where
  fn : α → α
  mono : ∀ x y : α, x ≤ y → fn x ≤ fn y
  map_sup : ∀ a b : α, fn (a ⊔ b) = fn a ⊔ fn b
  map_bot : fn ⊥ = ⊥

/-- The legal residual (right adjoint): gamma(y) = sup { x | fn(x) ≤ y }. -/
noncomputable def legalResidual {α : Type u} [FinitePoset α]
    (a : ResiduatedMap α) (y : α) : α :=
  (Finset.univ.filter (fun x => decide (a.fn x ≤ y))).sup id

/-- Key lemma: fn distributes over Finset.sup. -/
lemma fn_sup_preserves {α : Type u} [FinitePoset α]
    (a : ResiduatedMap α) (s : Finset α) :
    a.fn (s.sup id) = s.sup a.fn := by
  induction s using Finset.cons_induction with
  | empty => simp [a.map_bot]
  | cons x s _ ih =>
    rw [Finset.sup_cons, Finset.sup_cons, a.map_sup, ih]
    simp [id]

def IsGaloisConnection {α : Type u} [FinitePoset α]
    (a : ResiduatedMap α) (g : α → α) : Prop :=
  ∀ x y : α, a.fn x ≤ y ↔ x ≤ g y

theorem galois_connection_of_residuated
    {α : Type u} [FinitePoset α]
    (a : ResiduatedMap α) :
    IsGaloisConnection a (legalResidual a) := by
  intro x y
  constructor
  · -- (⟹) fn(x) ≤ y → x ≤ legalResidual(y)
    intro h
    have hx : x ∈ Finset.univ.filter (fun z => decide (a.fn z ≤ y)) := by
      simp [Finset.mem_filter]; exact h
    exact Finset.le_sup (f := id) hx
  · -- (⟸) x ≤ legalResidual(y) → fn(x) ≤ y
    intro h
    have h1 : a.fn x ≤ a.fn (legalResidual a y) := a.mono _ _ h
    suffices h2 : a.fn (legalResidual a y) ≤ y from le_trans h1 h2
    unfold legalResidual
    rw [fn_sup_preserves a]
    exact Finset.sup_le (fun z hz => by simp [Finset.mem_filter] at hz; exact hz)
