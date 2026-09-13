import JurisLean.FullMath.Core.Foundations

/-!
B02 — Readiness and unknown facts: an incomplete assessment is pending; a
completed-but-unproven assessment yields a declared adverse effect, not a
historical negation of the fact; the independent fact state carries the
original finding; a lawyer's conditional opinion is never a court judgment.
-/

namespace JurisLean.FullMath.Burden

/-- Readiness gates for a terminal legal effect. -/
structure Gate where
  stageReady : Bool
  assessmentComplete : Bool
  authorityValid : Bool

def terminal (g : Gate) : Bool := g.stageReady && g.assessmentComplete && g.authorityValid

/-- B02(a): any false gate blocks every terminal effect. -/
theorem no_terminal_when_incomplete (g : Gate) (h : terminal g = true) :
    g.stageReady = true ∧ g.assessmentComplete = true ∧ g.authorityValid = true := by
  simp only [terminal, Bool.and_eq_true] at h
  exact h

def terminalEffect (g : Gate) (r : Ruling) : Option Ruling :=
  if terminal g then some r else none

/-- B02(b): with an incomplete gate there is no terminal effect at all. -/
theorem incomplete_no_terminal_effect (g : Gate) (r : Ruling)
    (h : ¬ (terminal g = true)) : terminalEffect g r = none := by
  simp only [terminalEffect]
  rw [if_neg h]

/-- The independent fact state: original findings survive any legal
consequence computed on top of them. -/
inductive Finding where
  | established (factId : ℕ)
  | adverseEffect (factId : ℕ)
  | lawyerOpinion (assumptionId : ℕ)
  | courtJudgment (assumptionId : ℕ)

/-- B02(c): a lawyer's conditional opinion is a different constructor from
a court judgment; assumptions never become adjudicated facts. -/
theorem opinion_not_judgment (a : ℕ) :
    Finding.lawyerOpinion a ≠ Finding.courtJudgment a := by
  intro h
  cases h

/-- Assessment states: incomplete, or completed with a declared adverse
effect for the failing party. -/
inductive Assessment where
  | incomplete
  | completedUnproven (adverse : String)
  | completedMet

/-- B02(d): an unproven completed assessment carries a declared adverse
effect — it never asserts the historical falsehood of the fact. -/
def adverseOf : Assessment → Option String
  | .incomplete => none
  | .completedUnproven adv => some adv
  | .completedMet => none

theorem unproven_declares_adverse (adv : String) :
    adverseOf (.completedUnproven adv) = some adv := rfl

theorem incomplete_declares_nothing : adverseOf .incomplete = none := rfl

end JurisLean.FullMath.Burden
