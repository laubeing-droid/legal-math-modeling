import JurisLean.UnifiedV2.FiniteContract

namespace JurisLean.ULM.UnifiedV2

inductive InputOrigin where
  | reviewedFact | hypothesis | prediction
  deriving DecidableEq

structure PremiseInput where
  binding : Binding
  origin : InputOrigin
  sourceChecked : Bool
  authorityChecked : Bool

/-- These checks are supplied by explicitly scoped source/authority adapters.
Their Boolean result is NOT a theorem about historical truth or authenticity. -/
def strictPremiseAllowed (expected : Binding) (i : PremiseInput) : Bool :=
  decide (i.binding = expected) && decide (i.origin = .reviewedFact) &&
    i.sourceChecked && i.authorityChecked

theorem prediction_never_strict (b : Binding) (i : PremiseInput)
    (h : i.origin = .prediction) : strictPremiseAllowed b i = false := by
  simp [strictPremiseAllowed, h]

theorem assumption_never_strict (b : Binding) (i : PremiseInput)
    (h : i.origin = .hypothesis) : strictPremiseAllowed b i = false := by
  simp [strictPremiseAllowed, h]

theorem unapproved_never_strict (b : Binding) (i : PremiseInput)
    (h : i.authorityChecked = false) : strictPremiseAllowed b i = false := by
  simp [strictPremiseAllowed, h]

inductive Finding where
  | established | notEstablished | undetermined
  deriving DecidableEq
inductive BurdenAnswer where
  | successEffect | failureEffect | pending
  deriving DecidableEq

def decideBurden (stageReady assessmentComplete authorityValid : Bool)
    (finding : Finding) : BurdenAnswer :=
  if stageReady && assessmentComplete && authorityValid then
    match finding with
    | .established => .successEffect
    | .notEstablished | .undetermined => .failureEffect
  else .pending

theorem unfinished_burden_is_pending (r a : Bool) (f : Finding) :
    decideBurden r false a f = .pending := by simp [decideBurden]

theorem unknown_ready_uses_failure_effect :
    decideBurden true true true .undetermined = .failureEffect := rfl

/-- The failure consequence does not rewrite the factual finding. -/
def burdenReport (r c a : Bool) (f : Finding) : Finding × BurdenAnswer :=
  (f, decideBurden r c a f)

theorem burden_does_not_manufacture_negation (r c a : Bool) (f : Finding) :
    (burdenReport r c a f).1 = f := rfl

end JurisLean.ULM.UnifiedV2
