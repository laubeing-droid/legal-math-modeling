import Mathlib

/-!
FullMath foundations: shared indexed vocabulary used across all full-plan areas.

Everything here is an independent mathematical definition; nothing refers to a
running solver, a stored status bit or a rendered report. Scope identity,
fact status, quantities and generic rational helpers live here so every later
module shares one business language (F01/C01).
-/

namespace JurisLean.FullMath

/-- Legal domain tag; three genuinely different procedural chains. -/
inductive Domain where
  | civil
  | criminal
  | administrative
  deriving DecidableEq, Repr

/-- Epistemic status of a factual item (F01/F03 layer separation). -/
inductive FactStatus where
  | statement
  | hypothesis
  | prediction
  | verified
  | disputed
  | unknown
  deriving DecidableEq, Repr

/-- Versioned interpretation scope: domain, issue, stage, source version. -/
structure Scope where
  domain : Domain
  issue : String
  stage : String
  version : String
  deriving DecidableEq

/-- A dimensioned rational quantity; currency/dimension strings are indices,
never identities. -/
structure Quantity where
  unit : String
  value : ℚ

/-- Generic rational helper: nonnegative reciprocal bound. -/
theorem rat_nonneg_of_both_nonneg {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b :=
  mul_nonneg ha hb

/-- Weighted sum bound used by statistical composition roots. -/
theorem weighted_sum_bound {ι : Type} (s : Finset ι) (w f g : ι → ℚ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hfg : ∀ i ∈ s, f i ≤ g i) :
    (∑ i ∈ s, w i * f i) ≤ ∑ i ∈ s, w i * g i := by
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_left (hfg i hi) (hw i hi)

end JurisLean.FullMath
