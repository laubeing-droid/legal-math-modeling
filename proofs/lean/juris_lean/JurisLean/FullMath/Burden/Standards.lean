import JurisLean.FullMath.Core.Foundations

/-!
B03 (formal part) and X02 — Proof standards as versioned rules.

Evidential outcomes are typed: fact-Unknown, evaluation-Pending,
standard-not-reached, historically-negated facts and procedural
consequences are distinct constructors. Promotion to `established` happens
only when the evidence weight meets the declared, version/issue/stage-bound
standard; numeric probabilities (75%, 95%…) are auxiliary inputs, never
automatic legal thresholds.
-/

namespace JurisLean.FullMath.Burden

/-- Typed evaluation outcome of a factual issue. -/
inductive FactOutcome where
  /-- The fact is unknown — no status may be invented. -/
  | unknown
  /-- Evaluation still pending. -/
  | pending
  /-- Evidence present but below the declared standard. -/
  | notReached
  /-- The fact was explicitly negated by the trier. -/
  | negated
  /-- Procedural consequence (exclusion, expiry) — not a factual status. -/
  | procedural
  /-- The fact is established under the declared standard. -/
  | established
  deriving DecidableEq

/-- A versioned proof standard: a numeric weight threshold plus the scope it
is declared for. -/
structure Standard where
  /-- Required evidential weight. -/
  threshold : ℚ
  /-- Scope binding: the standard is declared for this issue/stage/version. -/
  issue : String
  stage : String
  version : String

/-- Evidence weight (an auxiliary numeric input). -/
abbrev Weight := ℚ

/-- The gating function: promote to `established` only when the weight
meets the declared threshold; the numeric value alone never enters the
outcome type. -/
def gate (std : Standard) (w : Weight) : FactOutcome :=
  if std.threshold ≤ w then FactOutcome.established else FactOutcome.notReached

/-- B03(a): promotion to established happens exactly at the threshold. -/
theorem gate_established_iff (std : Standard) (w : Weight) :
    gate std w = FactOutcome.established ↔ std.threshold ≤ w := by
  rw [gate]
  by_cases h : std.threshold ≤ w
  · rw [if_pos h]
    exact fun _ => h
  · rw [if_neg h]
    exact fun hne => FactOutcome.noConfusion hne

/-- B03(b): below the threshold the outcome is notReached, a genuinely
different constructor from unknown and pending. -/
theorem gate_below_is_notReached (std : Standard) (w : Weight)
    (h : w < std.threshold) :
    gate std w = FactOutcome.notReached ∧
      gate std w ≠ FactOutcome.unknown ∧
      gate std w ≠ FactOutcome.pending := by
  refine ⟨by rw [gate, if_neg (by linarith)], ?_, ?_⟩
  · intro heq
    rw [gate, if_neg (by linarith : ¬ std.threshold ≤ w)] at heq
    exact FactOutcome.noConfusion heq
  · intro heq
    rw [gate, if_neg (by linarith : ¬ std.threshold ≤ w)] at heq
    exact FactOutcome.noConfusion heq

/-- X02(a): gating depends on the declared threshold only; the scope fields
(issue/stage/version) are carried by the record the decision must cite. -/
theorem gate_depends_only_on_threshold (std₁ std₂ : Standard) (w : Weight)
    (ht : std₁.threshold = std₂.threshold) : gate std₁ w = gate std₂ w := by
  rw [gate, gate, ht]

/-- X02(b): a bare probability alone cannot establish — for every weight
there is a declared standard under which the fact stays notReached. -/
theorem bare_probability_insufficient (w : Weight) :
    ∃ std : Standard, std.issue = "declared" ∧
      gate std w = FactOutcome.notReached := by
  refine ⟨⟨w + 1, "declared", "trial", "v1"⟩, rfl, ?_⟩
  rw [gate, if_neg (by linarith)]

end JurisLean.FullMath.Burden
