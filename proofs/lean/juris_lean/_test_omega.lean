import Mathlib.Tactic
example (a b : Nat) (h : a <= b) : a <= b + 1 := by
  omega
