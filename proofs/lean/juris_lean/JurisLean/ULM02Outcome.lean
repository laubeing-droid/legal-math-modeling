import JurisLean.ULM01NormalForm

/-! Subject-local result/failure algebra with non-empty partial obligations. -/

namespace JurisLean.ULM

structure OpenObligation where
  code : String
  detail : String
deriving DecidableEq, Repr

/-- A partial result must disclose at least one still-open obligation. -/
structure PartialPayload (α : Type*) where
  value : α
  open : Finset OpenObligation
  open_nonempty : open.Nonempty

inductive FailureTag where
  | unsupported
  | recoverable
  | hardFail
deriving DecidableEq, Repr

structure FailureCore where
  tag : FailureTag
  reason : String
  request : RequestKey
deriving DecidableEq, Repr

inductive Outcome (α : Type*) where
  | complete (value : α)
  | partialResult (payload : PartialPayload α)
  | failure (failure : FailureCore)

namespace Outcome

protected def map (f : α → β) : Outcome α → Outcome β
  | .complete x => .complete (f x)
  | .partialResult p => .partialResult
      { value := f p.value
        open := p.open
        open_nonempty := p.open_nonempty }
  | .failure e => .failure e

@[simp] theorem map_complete (f : α → β) (x : α) :
    Outcome.map f (.complete x) = .complete (f x) := rfl

@[simp] theorem map_partial (f : α → β) (p : PartialPayload α) :
    Outcome.map f (.partialResult p) =
      .partialResult
        { value := f p.value
          open := p.open
          open_nonempty := p.open_nonempty } := rfl

@[simp] theorem map_failure (f : α → β) (e : FailureCore) :
    Outcome.map f (.failure e) = .failure e := rfl

theorem failure_ne_complete (e : FailureCore) (x : α) :
    (Outcome.failure e : Outcome α) ≠ Outcome.complete x := by
  intro h
  cases h

theorem partial_ne_complete (p : PartialPayload α) (x : α) :
    (Outcome.partialResult p : Outcome α) ≠ Outcome.complete x := by
  intro h
  cases h

theorem map_never_upgrades_failure (f : α → β) (e : FailureCore) :
    Outcome.map f (.failure e) = (.failure e : Outcome β) := rfl

end Outcome

end JurisLean.ULM
