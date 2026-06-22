import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-! G9A: Dung Grounded Semantics — B1 formal objects, B2 theorem signatures.
  Proofs marked sorry are pending Lean proof completion. -/

open Finset

abbrev Arg : Type := String

structure DungAAF where
  args : Finset Arg
  attacks : Finset (Arg × Arg)
deriving DecidableEq, Inhabited

namespace DungAAF

def attackers (aaf : DungAAF) (a : Arg) : Finset Arg :=
  aaf.args.filter (fun b => (b, a) ∈ aaf.attacks)

def F (aaf : DungAAF) (S : Finset Arg) : Finset Arg :=
  aaf.args.filter (fun a =>
    ∀ b ∈ attackers aaf a, ((attackers aaf b).filter (fun c => c ∈ S)) ≠ ∅)

def groundedExtension (aaf : DungAAF) : Finset Arg × Bool × Nat :=
  let bound := aaf.args.card + 1
  let rec go (k : Nat) (acc : Finset Arg) : Finset Arg × Bool × Nat :=
    if h : k < bound then
      let next := F aaf acc
      if next = acc then (acc, true, k) else go (k+1) next
    else (acc, false, bound)
  go 0 ∅

def grounded (aaf : DungAAF) : Finset Arg := (groundedExtension aaf).1

def labelling (aaf : DungAAF) : Finset Arg × Finset Arg × Finset Arg :=
  let ge := grounded aaf
  let out := aaf.args.filter (fun a => a ∉ ge ∧ (attackers aaf a).filter (fun b => b ∈ ge) ≠ ∅)
  let undec := aaf.args \ (ge ∪ out)
  (ge, out, undec)


/-- Iterate F k times from the empty set. -/
def iterF (aaf : DungAAF) : Nat → Finset Arg
  | 0 => ∅
  | n+1 => F aaf (iterF aaf n)

/-! 13 Core Theorems (all proofs pending) -/

theorem F_monotone (aaf : DungAAF) (S T : Finset Arg) (hST : S ⊆ T) : F aaf S ⊆ F aaf T := by
  sorry

theorem iteration_monotone (aaf : DungAAF) (k : Nat) : iterF aaf k ⊆ iterF aaf (k+1) := by
  sorry

theorem finite_termination (aaf : DungAAF) : (groundedExtension aaf).2.1 := by
  sorry

theorem iteration_bound (aaf : DungAAF) : (groundedExtension aaf).2.2 ≤ aaf.args.card + 1 := by
  sorry

theorem grounded_is_fixed_point (aaf : DungAAF) : F aaf (grounded aaf) = grounded aaf := by
  sorry

theorem grounded_is_least_fixed_point (aaf : DungAAF) (S : Finset Arg) (hS : F aaf S = S) :
    grounded aaf ⊆ S := by
  sorry

theorem grounded_is_least_complete (aaf : DungAAF) (S : Finset Arg) (hS : F aaf S = S) :
    grounded aaf ⊆ S := by
  sorry

theorem grounded_unique (aaf : DungAAF) : ∃! ge, F aaf ge = ge := by
  sorry

theorem labelling_partition (aaf : DungAAF) :
    let (ge, out, undec) := labelling aaf
    ge ∩ out = ∅ ∧ ge ∩ undec = ∅ ∧ out ∩ undec = ∅ ∧ ge ∪ out ∪ undec = aaf.args := by
  sorry

theorem in_soundness (aaf : DungAAF) (a : Arg) (h : a ∈ grounded aaf) :
    ∀ b ∈ attackers aaf a, ((attackers aaf b).filter (fun c => c ∈ grounded aaf)) ≠ ∅ := by
  sorry

theorem out_soundness (aaf : DungAAF) (a : Arg) (h : a ∈ (labelling aaf).2.1) :
    (attackers aaf a).filter (fun b => b ∈ grounded aaf) ≠ ∅ := by
  sorry

theorem undecided_characterization (aaf : DungAAF) (a : Arg) :
    a ∈ (labelling aaf).2.2.1 ↔ a ∉ grounded aaf ∧ (attackers aaf a).filter (fun b => b ∈ grounded aaf) = ∅ := by
  sorry

theorem self_attack_undecided (aaf : DungAAF) (a : Arg) (hself : (a, a) ∈ aaf.attacks) (honly : attackers aaf a = {a}) :
    a ∉ grounded aaf := by
  sorry

end DungAAF