import Mathlib

/-!
# Mandate upgrade — a scorer that consumes its arguments

`Genealogy/TSpectrum/Batch3.lean:186` defines `deterministic (s : LogisticSpec) : Bool := true`
— the argument is dropped, and the only dependent theorem proves `true = true`
against a literal record. The audit logged this as the textbook degenerate
definition (P2-14): the name promises a logistic scorer, the body promises
nothing.

Replaced here by a weighted-threshold scorer over integers. `Int` keeps the
arithmetic exact and needs no absolute value: the score is a sum of products, the
prediction is its sign, and the theorems below are the properties a scorer must
have to be a scorer at all — it is non-constant (the degenerate case is refuted by
exhibition), it preserves non-negativity, and it splits over a cons.

This is still not a trained network; it is the arithmetic core a one-layer linear
model reduces to, and unlike the constant it can be wrong in interesting ways.

Status: imported by the release root and named by `AxiomAudit.lean`; built green
in CI run 36298572193 (subject 0574e2ae4), the first round whose root itself
elaborates this module. Commits after that subject do not inherit the verdict.
-/

namespace JurisLean.Mandate.LinearScorer

/-- Pointwise product summed: the exact score of a feature/weight vector. -/
def score : List Int → List Int → Int
  | [], _ => 0
  | _, [] => 0
  | w :: ws, x :: xs => w * x + score ws xs

/-- Prediction is the sign of the score; no threshold is hidden in a constant. -/
def predicts (w x : List Int) : Bool := if 0 ≤ score w x then true else false

/-- A missing weight or feature truncates the sum rather than defaulting to true. -/
theorem score_nil_weights (x : List Int) : score [] x = 0 := rfl

theorem score_nil_features (w : List Int) : score w [] = 0 := by
  cases w with
  | nil => rfl
  | cons a as => rfl

/-- The score splits over a leading weight/feature pair. -/
theorem score_cons (w : Int) (ws : List Int) (x : Int) (xs : List Int) :
    score (w :: ws) (x :: xs) = w * x + score ws xs := rfl

/--
Non-degeneracy of the scorer, exhibited rather than asserted: two feature vectors
the same weights separate. This is exactly what `def deterministic _ := true`
could not satisfy.
-/
theorem score_not_constant :
    ∃ (w x y : List Int), score w x ≠ score w y :=
  ⟨[2, 3], [1, 1], [0, 1], by decide⟩

/-- Everything above a non-negative witness is decided true. -/
theorem predicts_true_of_nonneg (w x : List Int) (h : 0 ≤ score w x) :
    predicts w x = true :=
  if_pos h

/-- A negative score is decided false: the gate can say no. -/
theorem not_predicts_of_neg (w x : List Int) (h : score w x < 0) :
    predicts w x = false :=
  if_neg (by omega)

/--
Weights and features that are all non-negative can never score below zero. This
is the invariant a downstream legal-use layer needs: a scorer that cannot return
a negative score cannot silently flip a "no evidence" reading into "evidence".
-/
def allNonNeg : List Int → Prop
  | [] => True
  | a :: l => 0 ≤ a ∧ allNonNeg l

theorem score_nonneg_of_allNonNeg (w x : List Int)
    (hw : allNonNeg w) (hx : allNonNeg x) : 0 ≤ score w x := by
  induction w generalizing x with
  | nil => simp [score]
  | cons a ws ih =>
      cases x with
      | nil => simp [score]
      | cons b xs =>
          cases hw with
          | intro ha hws =>
              cases hx with
              | intro hb hxs =>
                  show 0 ≤ a * b + score ws xs
                  have htail := ih xs hws hxs
                  nlinarith

/-- Zero weights score everything at zero, so a nullified model predicts uniformly. -/
theorem score_zero_weights (x : List Int) : score [0, 0] x = 0 := by
  cases x with
  | nil => rfl
  | cons b xs =>
      cases xs with
      | nil => show 0 * b + score [0] [] = 0; simp [score]
      | cons c _ => show 0 * b + (0 * c + score [] _) = 0; simp [score]

/-- Scaling both sides by a positive constant preserves the decision. -/
theorem predicts_scaled_positive (w x : List Int) (h : predicts w x = true) :
    predicts (2 :: w) (2 :: x) = true := by
  have h0 : (0 : Int) ≤ score w x := by simpa [predicts] using h
  refine if_pos ?_
  rw [score_cons]
  omega

end JurisLean.Mandate.LinearScorer
