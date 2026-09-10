import Mathlib

/-!
ROOT02 — Fixed original input I0 and cross-language lossless encoding.

`ExactInput` is the typed carrier of the frozen I0 parameters (principal,
payment, recognition probability, threshold, four costs, legal grid). The
encoding into a canonical rational vector structure is lossless: decoding an
encoding recovers the input, and binding acceptance forces equality. A changed
parameter under the same version produces a different input — refused as this
selected input — while a legitimately different parameter set is simply a
different (new) task object, never forced to equal this one.
-/

namespace JurisLean.BusinessRoot

/-- Typed exact input of the frozen task; rationals only, no floats. -/
structure ExactInput where
  principal : ℚ
  payment : ℚ
  probability : ℚ
  threshold : ℚ
  costP : ℚ
  costD : ℚ
  settleP : ℚ
  settleD : ℚ
  options : List ℚ
  deriving DecidableEq, Repr

/-- Canonical positional encoding; hashes are locators, never equality proofs. -/
def encodeInput (i : ExactInput) : List ℚ × List ℚ :=
  ([i.principal, i.payment, i.probability, i.threshold,
    i.costP, i.costD, i.settleP, i.settleD], i.options)

def decodeInput : List ℚ × List ℚ → Option ExactInput
  | ([a, b, c, d, e, f, g, h], opts) =>
      some ⟨a, b, c, d, e, f, g, h, opts⟩
  | _ => none

/-- Lossless: decoding an encoding recovers the very input. -/
theorem codec_roundtrip (i : ExactInput) : decodeInput (encodeInput i) = some i := by
  cases i
  rfl

/-- Encoding is injective, hence binding to an encoding forces input equality. -/
theorem encode_injective (i j : ExactInput) (h : encodeInput i = encodeInput j) : i = j := by
  cases i
  cases j
  simp [encodeInput, Prod.mk.injEq, List.cons.injEq] at h
  simp [h]

/-- Binding predicate: accept only when the submitted input IS the selected one.
The producer's own output can never choose the expected side of this relation. -/
def CheckBinding (expected submitted : ExactInput) : Bool := decide (expected = submitted)

theorem binding_exact (i j : ExactInput) (h : CheckBinding i j = true) : i = j := by
  exact of_decide_eq_true h

/-- Same-version parameter change: a different parameter set is NOT this selected
input and is refused by the binding check. -/
theorem binding_refuses_changed (i : ExactInput) (δ : ℚ) (hne : δ ≠ 0) :
    CheckBinding i {i with principal := i.principal + δ} = false := by
  simp only [CheckBinding, decide_eq_false_iff_not, ne_eq]
  intro heq
  have hproj : i.principal = i.principal + δ :=
    congrArg ExactInput.principal heq
  exact hne (by linarith)

/-- A changed parameter set is a distinct task object — allowed to exist as a
new task; nothing above forbids its construction, only re-labeling it as this
previously selected input. -/
theorem changed_is_different (i : ExactInput) (δ : ℚ) (hne : δ ≠ 0) :
    {i with principal := i.principal + δ} ≠ i := by
  intro heq
  have hproj : i.principal + δ = i.principal :=
    congrArg ExactInput.principal heq
  exact hne (by linarith)

end JurisLean.BusinessRoot
