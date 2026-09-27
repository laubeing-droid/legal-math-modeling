import Mathlib

/-!
# Mandate kernel — the algebra the mandate modules share

Audit judgement 1 found that the "unified" line was not unified: `Genealogy/`
declares 295 carriers for 300 theorems, its import graph is a single chain
(Part0 -> Part1 -> ... -> Batch4) rather than a shared core, and exactly one of
its modules imports Mathlib. Every concept brought its own miniature model, so
nothing was proved *about* the others.

This kernel is the counter-example, deliberately scoped to the new work: the
rate algebra, the max-selection facts and the structural signature are declared
once here, and the mandate modules import them instead of restating them. The
gate in `tests/spec/test_mandate_modules.py` measures the ratio and refuses a
regression back to one-carrier-per-theorem.

Status: NOT imported by `JurisLean.lean`, NOT in `AxiomAudit.lean`; CI_NOT_RUN.
-/

namespace JurisLean.Mandate.Kernel

/-! ## Exact rates (win-rate step two and any later comparison layer) -/

/-- Successes in a cohort, structural recursion so the equations are ours. -/
def successes : List Bool → Nat
  | [] => 0
  | true :: rest => successes rest + 1
  | false :: rest => successes rest

/-- A rate: exact counts, denominator nonzero by construction. -/
structure Rate where
  num : Nat
  den : Nat
  denPos : 0 < den

/-- Comparison by cross-multiplication; division is never formed. -/
/-- Cross-multiplication order, named so the notation below is only a symbol. -/
def rateLe (a b : Rate) : Prop := a.num * b.den ≤ b.num * a.den

-- An `infix` body is quoted, so field projections inside it do not elaborate even
-- with ascribed binders; point the notation at a definition instead.
infix:50 " ≤ₛ " => rateLe

theorem rate_le_self (r : Rate) : r ≤ₛ r := Nat.le_refl _

theorem successes_le_length (obs : List Bool) : successes obs ≤ obs.length := by
  induction obs with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
      cases x with
      | true => simp [successes]; omega
      | false => simp [successes]; omega

/-- A rate built from a cohort never exceeds its own unit bound. -/
theorem rate_num_le_den (obs : List Bool) : successes obs ≤ obs.length :=
  successes_le_length obs

/-! ## Selection: the `max` facts every best-response layer needs -/

theorem le_max_l (a b : ℕ) : a ≤ max a b := by
  rw [Nat.max_def]
  split <;> omega

theorem le_max_r (a b : ℕ) : b ≤ max a b := by
  rw [Nat.max_def]
  split <;> omega

theorem max_zero (a : ℕ) : max a 0 = a := by
  rw [Nat.max_def]
  split <;> omega

/-- Selecting over an appended list never loses the left-hand options. -/
theorem best_le_best_append (f : Nat → Nat) (xs ys : List Nat) :
    (xs.foldr (fun x a => max (f x) a) 0)
      ≤ (xs ++ ys).foldr (fun x a => max (f x) a) 0 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      show max (f x) (xs.foldr (fun a b => max (f a) b) 0)
           ≤ max (f x) ((xs ++ ys).foldr (fun a b => max (f a) b) 0)
      omega

/-! ## Structure signatures (case comparison layer) -/

/-- A case as structure: issue codes, element codes, asserted incidences. -/
structure CaseStructure where
  issues : List Nat
  elements : List Nat
  incidences : List (Nat × Nat)

/-- The coarse invariant of a case: counts, independent of vocabulary. -/
def sig3 (s : CaseStructure) : Nat × Nat × Nat :=
  (s.issues.length, s.elements.length, s.incidences.length)

/-- Structural sum: disjoint union of two cases' material. -/
def sum (s t : CaseStructure) : CaseStructure :=
  { issues := s.issues ++ t.issues
    elements := s.elements ++ t.elements
    incidences := s.incidences ++ t.incidences }

theorem sig3_relabel_fst (s : CaseStructure) (f : Nat → Nat) :
    (sig3 { s with issues := s.issues.map f }).1 = (sig3 s).1 := by
  simp [sig3]

theorem sig3_relabel_snd (s : CaseStructure) (f : Nat → Nat) :
    (sig3 { s with elements := s.elements.map f }).2.1 = (sig3 s).2.1 := by
  simp [sig3]

theorem sig3_relabel_edges (s : CaseStructure) (f g : Nat → Nat) :
    (sig3 { s with incidences := s.incidences.map (fun p => (f p.1, g p.2)) }).2.2
      = (sig3 s).2.2 := by
  simp [sig3]

theorem sig3_sum (s t : CaseStructure) :
    sig3 (sum s t) =
      ((sig3 s).1 + (sig3 t).1, (sig3 s).2.1 + (sig3 t).2.1, (sig3 s).2.2 + (sig3 t).2.2) := by
  simp [sig3, sum, List.length_append]

theorem sig3_fst_le_sum (s t : CaseStructure) : (sig3 s).1 ≤ (sig3 (sum s t)).1 := by
  simp [sig3, sum]

theorem sig3_edges_le_sum (s t : CaseStructure) : (sig3 s).2.2 ≤ (sig3 (sum s t)).2.2 := by
  simp [sig3, sum]

end JurisLean.Mandate.Kernel
