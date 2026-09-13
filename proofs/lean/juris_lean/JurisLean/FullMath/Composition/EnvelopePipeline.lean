import JurisLean.FullMath.Core.Foundations

/-!
C02 — Outer-envelope composition: monotone abstract transformers compose;
if each step's transformer is sound on its input over-approximation, the
chained pipeline's output covers the concrete execution, and the whole
pipeline stays monotone.
-/

namespace JurisLean.FullMath.Composition

variable {S : Type}

/-- A monotone outer-approximating transformer. -/
structure OuterStep where
  step : Set S → Set S
  mono : ∀ X Y, X ⊆ Y → step X ⊆ step Y

def runPipeline (steps : List OuterStep) (start : Set S) : Set S :=
  steps.foldl (fun acc st => st.step acc) start

theorem runPipeline_cons (st : OuterStep) (rest : List OuterStep) (start : Set S) :
    runPipeline (st :: rest) start = runPipeline rest (st.step start) := rfl

theorem runPipeline_nil (start : Set S) : runPipeline [] start = start := rfl

/-- C02(a): the two-step composition covers: if each transformer is sound
on its declared input bound, the chained result covers the concrete start. -/
theorem outer_two_step (T1 T2 : OuterStep) (c0 c1 c2 : Set S)
    (h1 : T1.step c0 ⊆ c1) (h2 : T2.step c1 ⊆ c2) :
    T2.step (T1.step c0) ⊆ c2 := by
  calc T2.step (T1.step c0) ⊆ T2.step c1 := T2.mono _ _ h1
    _ ⊆ c2 := h2

/-- C02(b): three-step chain — composing one more sound step preserves
coverage. -/
theorem outer_three_step (T1 T2 T3 : OuterStep) (c0 c1 c2 c3 : Set S)
    (h1 : T1.step c0 ⊆ c1) (h2 : T2.step c1 ⊆ c2) (h3 : T3.step c2 ⊆ c3) :
    T3.step (T2.step (T1.step c0)) ⊆ c3 := by
  calc T3.step (T2.step (T1.step c0)) ⊆ T3.step c2 :=
        T3.mono _ _ (outer_two_step T1 T2 c0 c1 c2 h1 h2)
    _ ⊆ c3 := h3

/-- C02(c): the whole pipeline is monotone — outer bounds are preserved
under widening at any stage. -/
theorem pipeline_monotone (steps : List OuterStep) (X Y : Set S) (hsub : X ⊆ Y) :
    runPipeline steps X ⊆ runPipeline steps Y := by
  induction steps generalizing X Y with
  | nil => exact hsub
  | cons st rest ih =>
    rw [runPipeline_cons, runPipeline_cons]
    exact ih (st.step X) (st.step Y) (st.mono X Y hsub)

end JurisLean.FullMath.Composition
