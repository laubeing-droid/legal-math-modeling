import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import JurisLean.FiniteMonotoneIteration

open Finset

/-! Dung AAF Definitions — arguments, attacks, characteristic function, labelling.

Provides the basic Dung abstract argumentation framework definitions
and instantiates the FiniteMonotoneSystem typeclass for the characteristic
function F. All proofs are in DungFixedPoint.lean.
-/

abbrev Arg : Type := String

structure DungAAF where
  args : Finset Arg
  attacks : Finset (Arg × Arg)
deriving DecidableEq, Inhabited

namespace DungAAF

/-- The set of attackers of argument a in the AAF. -/
def attackers (aaf : DungAAF) (a : Arg) : Finset Arg :=
  aaf.args.filter (fun b => (b, a) ∈ aaf.attacks)

/-- The characteristic function F: an argument is acceptable w.r.t. S
    if all its attackers are defeated by S (i.e., every attacker has
    at least one attacker in S). -/
def F (aaf : DungAAF) (S : Finset Arg) : Finset Arg :=
  aaf.args.filter (fun a =>
    ∀ b ∈ attackers aaf a, ((attackers aaf b).filter (fun c => c ∈ S)) ≠ ∅)

/-- The AAF system as a FiniteMonotoneSystem for the generic fixpoint kernel. -/
def aafSystem (aaf : DungAAF) : FiniteMonotoneSystem Arg := {
  universe := aaf.args
  step := F aaf
  step_subset_universe := by
    intro S
    rw [F]
    exact Finset.filter_subset _ _
  step_monotone := by
    intro S T hST
    rw [F, F]
    intro a ha
    rw [Finset.mem_filter] at ha ⊢
    rcases ha with ⟨ha_args, ha_cond⟩
    refine ⟨ha_args, ?_⟩
    intro b hb
    have h_prev : ((attackers aaf b).filter (fun c => c ∈ S)) ≠ ∅ := ha_cond b hb
    intro h_empty
    apply h_prev
    apply (Finset.eq_empty_iff_forall_not_mem _).mpr
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hx_att, hx_S⟩
    have hx_T : x ∈ ((attackers aaf b).filter (fun c => c ∈ T)) :=
      Finset.mem_filter.mpr ⟨hx_att, hST hx_S⟩
    rw [h_empty] at hx_T
    simp at hx_T
}

end DungAAF
