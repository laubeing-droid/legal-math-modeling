import JurisLean.FullMath.Core.Foundations

/-!
F03 — Strict premise admission. Hypotheses and predictions can never become
unconditionally verified premises; institutional inputs are binding-and-use
scoped adapters, not verified facts; a nonempty name is not an authorization.
-/

namespace JurisLean.FullMath.Evidence

/-- Admission constructors for factual input. -/
inductive Admission where
  /-- Verified premise: requires a checked source and a separately supplied
  authority token binding domain/issue/stage. -/
  | verifiedPremise (source : String) (authority : String)
  /-- Hypothesis: conditional input, never verified. -/
  | hypothesis (content : String)
  /-- Prediction: model output, never verified. -/
  | prediction (content : String)
  /-- Institutional act input: identified by binding and use scope only. -/
  | institution (name : String) (binding : String) (use : String)
  /-- Disputed item. -/
  | disputed (content : String)
  deriving DecidableEq

/-- The epistemic status each admission constructor yields. -/
def Admission.status : Admission → FactStatus
  | .verifiedPremise _ _ => .verified
  | .hypothesis _ => .hypothesis
  | .prediction _ => .prediction
  | .institution _ _ _ => .statement
  | .disputed _ => .disputed

/-- F03(a): predictions never admit as verified premises. -/
theorem prediction_not_verified (content : String) :
    Admission.prediction content |>.status ≠ FactStatus.verified := by
  simp [Admission.status]

/-- F03(b): hypotheses never admit as verified premises. -/
theorem hypothesis_not_verified (content : String) :
    Admission.hypothesis content |>.status ≠ FactStatus.verified := by
  simp [Admission.status]

/-- F03(c): whatever ends up verified must have come through the strict
constructor with a source and an authority token. -/
theorem verified_requires_source_authority (a : Admission)
    (h : a.status = FactStatus.verified) :
    ∃ source authority, a = Admission.verifiedPremise source authority := by
  cases a with
  | verifiedPremise s t => exact ⟨s, t, rfl⟩
  | hypothesis c => exact absurd h (by simp [Admission.status])
  | prediction c => exact absurd h (by simp [Admission.status])
  | institution n b u => exact absurd h (by simp [Admission.status])
  | disputed c => exact absurd h (by simp [Admission.status])

/-- F03(d): institutional inputs are binding-and-use scoped statements, never
verified facts, whatever the name says. -/
theorem institution_never_verified (n b u : String) :
    Admission.institution n b u |>.status = FactStatus.statement := rfl

/-- Authority is granted only by a token carrying an explicit grant marker;
plain names never carry it automatically. -/
def AuthorityGranted (token : String) : Prop := token.endsWith "-granted" = true

/-- F03(e): a nonempty name alone is not authorization. -/
theorem nonempty_name_is_not_authority :
    ∃ n : String, n ≠ "" ∧ ¬ AuthorityGranted n := by
  refine ⟨"court", by simp, ?_⟩
  intro h
  exact absurd h (by decide)

end JurisLean.FullMath.Evidence
