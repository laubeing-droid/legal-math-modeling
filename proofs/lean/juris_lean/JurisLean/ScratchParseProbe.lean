import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Common

namespace JurisLean.ULM

/- Probe A: exact EdgeKind shape -/
inductive EdgeKindA where
  | deterministic
  | partial
  | relation
  | stateTransition
deriving DecidableEq, Repr

/- Probe B: partial renamed -/
inductive EdgeKindB where
  | deterministic
  | partial2
  | relation
  | stateTransition
deriving DecidableEq, Repr

/- Probe C: only deterministic + partial -/
inductive EdgeKindC where
  | deterministic
  | partial
deriving DecidableEq, Repr

/- Probe D: only relation etc -/
inductive EdgeKindD where
  | relation
  | stateTransition
  | abstraction
deriving DecidableEq, Repr

end JurisLean.ULM
