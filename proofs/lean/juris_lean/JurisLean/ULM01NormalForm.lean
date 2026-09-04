import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Order
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Rat.Defs
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Lattice
import Mathlib.Order.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Common
import JurisLean.ArgumentSemanticsRegistry

/-!
# Unified Legal Model — executable normal-form vocabulary (forcibly retouched for fresh re-elaboration)


This module reuses the repository's existing argumentation-profile type and fixes
only the structural vocabulary needed by the sixteen-module package.  Digests and
serialized strings remain engineering projections; mathematical identity is the
structure itself.
-/

namespace JurisLean.ULM

/-- Reuse the existing repository profile registry; do not create a parallel enum. -/
abbrev SemanticProfile := JurisLean.SemanticsKind

inductive Layer where
  | input
  | normative
  | procedure
  | empirical
  | integration
deriving DecidableEq

inductive NodeKind where
  | fact
  | evidence
  | rule
  | position
  | argument
  | procedureState
  | legalStatus
  | consequence
  | calculation
  | empiricalArtifact
deriving DecidableEq

inductive EdgeKind where
  | deterministic
  | partialResult
  | relation
  | stateTransition
  | abstraction
  | probabilityKernel
  | ranker
  | exactCalculation
deriving DecidableEq

inductive ClaimKind where
  | typeSafety
  | soundness
  | failure
  | completeness
  | preserve
  | reflect
  | observe
  | trust
  | update
  | identity
  | branch
  | authority
  | dimension
  | termination
  | confluence
deriving DecidableEq

inductive PositionStage where
  | candidate
  | argumentSupported
  | extensionSupported
  | adjudicated
  | committed
deriving DecidableEq

structure ContextKey where
  caseScope : JurisLean.CaseScope
  runScope : JurisLean.RunScope
  scenario : String
  baseVersion : JurisLean.SchemaVersion
  subjectVersion : JurisLean.SemanticsVersion
deriving DecidableEq

/-- The run scope must belong to the same case as the enclosing context. -/
def ContextKey.WellFormed (k : ContextKey) : Prop :=
  k.runScope.caseScope = k.caseScope

structure RequestKey where
  context : ContextKey
  profile : SemanticProfile
  query : JurisLean.LegalId .claim
  mappingVersion : JurisLean.SchemaVersion
deriving DecidableEq

/-- A request is well formed exactly when its run scope belongs to its case. -/
def RequestKey.WellFormed (r : RequestKey) : Prop :=
  r.context.WellFormed

structure NormalForm where
  request : RequestKey
  facts : Finset (JurisLean.LegalId .fact)
  rules : Finset (JurisLean.LegalId .rule)
  activeDomains : Finset String
deriving DecidableEq

/-- Observation preservation is stated independently of the implementation. -/
def Preserves {α β γ : Type*}
    (obsIn : α → γ) (obsOut : β → γ) (f : α → β) : Prop :=
  ∀ x, obsOut (f x) = obsIn x

@[simp] theorem context_wf_iff (k : ContextKey) :
    k.WellFormed ↔ k.runScope.caseScope = k.caseScope := Iff.rfl

@[simp] theorem preserves_id {α γ : Type*} (obs : α → γ) :
    Preserves obs obs id := by
  intro x
  rfl

theorem preserves_comp {α β γ δ : Type*}
    (obsA : α → δ) (obsB : β → δ) (obsC : γ → δ)
    (f : α → β) (g : β → γ)
    (hf : Preserves obsA obsB f) (hg : Preserves obsB obsC g) :
    Preserves obsA obsC (g ∘ f) := by
  intro x
  change obsC (g (f x)) = obsA x
  rw [hg (f x), hf x]

end JurisLean.ULM
