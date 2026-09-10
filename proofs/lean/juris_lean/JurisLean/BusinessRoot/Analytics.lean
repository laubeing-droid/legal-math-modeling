import Mathlib
import JurisLean.BusinessRoot.Semantics

/-!
ROOT04 — Nonnegative principal / overpayment expectations, threshold events
and the legal settlement grid.

Everything is computed with C (clipped nonnegative balance), never with the raw
residual: the conservation identity E[C] − E[U] = P − q·p is proven from the
per-scenario split identity, and the frozen numeric samples pin the failure
mode of the raw-residual shortcut (P(C ≥ 0) = 1 while P(R ≥ 0) = 3/5).
-/

namespace JurisLean.BusinessRoot

/-- Split identity: the clipped balance minus the overpayment residual is the
raw residual for every value. -/
theorem split_identity (r : ℚ) : clipC r - clipU r = r := by
  unfold clipC clipU
  by_cases h : r ≤ 0
  · by_cases h2 : r < 0
    · simp [h, h2]
    · have hreq : r = 0 := by linarith
      simp [hreq, h]
  · have h3 : ¬ (r ≤ 0) := by linarith
    have h4 : ¬ (r < 0) := by linarith
    rw [if_neg h3, if_neg h4]
    ring

/-- Weighted linearity under pointwise subtraction of the per-scenario quantity. -/
theorem weighted_sub (ws : List (ℚ × World)) (f g : World → ℚ) :
    weighted ws f - weighted ws g = weighted ws (fun w => f w - g w) := by
  induction ws with
  | nil => simp [weighted]
  | cons x rest ih =>
      have e1 : weighted (x :: rest) f = x.1 * f x.2 + weighted rest f := by
        simp [weighted]
      have e2 : weighted (x :: rest) g = x.1 * g x.2 + weighted rest g := by
        simp [weighted]
      have e3 : weighted (x :: rest) (fun w => f w - g w)
          = x.1 * (f x.2 - g x.2) + weighted rest (fun w => f w - g w) := by
        simp [weighted]
      rw [e1, e2, e3]
      have h1 : x.1 * f x.2 - x.1 * g x.2 = x.1 * (f x.2 - g x.2) := by ring
      have h2 : (x.1 * f x.2 + weighted rest f) - (x.1 * g x.2 + weighted rest g)
          = (x.1 * f x.2 - x.1 * g x.2) + (weighted rest f - weighted rest g) := by
        ring
      rw [h2, h1, ih]

/-- Weighted value only depends on the per-scenario quantities. -/
theorem weighted_congr (ws : List (ℚ × World)) (f g : World → ℚ)
    (h : ∀ p ∈ ws, f p.2 = g p.2) : weighted ws f = weighted ws g := by
  induction ws with
  | nil => rfl
  | cons x rest ih =>
      simp only [weighted, List.map_cons, List.sum_cons]
      rw [h x (by simp)]
      exact congrArg _ (ih fun p hp => h p (by simp [hp]))

/-- The two-branch probability weights of the frozen task. -/
def twoBranchWeights (p : ℚ) : List (ℚ × World) := [(p, [true]), (1 - p, [false])]

/-- The frozen two-branch weight list evaluates to an explicit pair sum. -/
theorem weighted_twoBranch (f : World → ℚ) (p : ℚ) :
    weighted (twoBranchWeights p) f = p * f [true] + (1 - p) * f [false] := by
  simp [weighted, twoBranchWeights]

/-- The frozen two-branch event mass evaluates to an explicit pair. -/
theorem eventMass_twoBranch (f : World → ℚ) (p t : ℚ) :
    eventMass (twoBranchWeights p) f t
      = (if t ≤ f [true] then p else 0) + (if t ≤ f [false] then 1 - p else 0) := by
  simp [eventMass, twoBranchWeights]

/-- Recognition test of a positional scenario under the single declared atom. -/
def isRecognized (w : World) : Bool :=
  match w with
  | [b] => b
  | _ => false

/-- Raw residual under one conditional payment. -/
def cres (P q : ℚ) (w : World) : ℚ := P - (if isRecognized w then q else 0)

/-- Clipped principal balance under one conditional payment. -/
def cbal (P q : ℚ) (w : World) : ℚ := clipC (cres P q w)

/-- Overpayment residual under one conditional payment. -/
def cover (P q : ℚ) (w : World) : ℚ := clipU (cres P q w)

/-- Recognition-branch residual values: the recognized branch pays, the
unrecognized branch pays nothing. -/
theorem cres_true_eq (P q : ℚ) : cres P q [true] = P - q := by
  simp [cres, isRecognized]

theorem cres_false_eq (P q : ℚ) : cres P q [false] = P := by
  simp [cres, isRecognized]

/-- Conservation for the nonnegative decomposition: E[C] − E[U] = P − q·p.
This uses C and U, never E[R] in place of E[C]. -/
theorem CU_expectation_conservation (P q p : ℚ) :
    weighted (twoBranchWeights p) (fun w => cbal P q w) -
      weighted (twoBranchWeights p) (fun w => cover P q w) = P - p * q := by
  have hT : cbal P q [true] - cover P q [true] = cres P q [true] :=
    split_identity (cres P q [true])
  have hF : cbal P q [false] - cover P q [false] = cres P q [false] :=
    split_identity (cres P q [false])
  rw [weighted_sub, weighted_twoBranch]
  simp only [cbal, cover, split_identity]
  rw [cres_true_eq, cres_false_eq]
  ring

/-- Frozen overpayment sample (P=100, q=300, p=2/5): the raw residual
expectation is −20. -/
theorem overpay_raw_expectation :
    weighted (twoBranchWeights (2 / 5)) (fun w => cres 100 300 w) = -20 := by
  rw [weighted_twoBranch]
  show (2 / 5) * cres 100 300 [true] + (1 - 2 / 5) * cres 100 300 [false] = -20
  rw [cres_true_eq, cres_false_eq]
  norm_num

/-- Frozen overpayment sample: the nonnegative principal expectation is 60,
not −20 — the raw expectation is not the principal expectation. -/
theorem overpay_principal_expectation :
    weighted (twoBranchWeights (2 / 5)) (fun w => cbal 100 300 w) = 60 := by
  rw [weighted_twoBranch]
  show (2 / 5) * clipC (cres 100 300 [true]) + (1 - 2 / 5) * clipC (cres 100 300 [false]) = 60
  rw [cres_true_eq, cres_false_eq]
  norm_num [clipC]

/-- Frozen overpayment sample: the overpayment expectation is 80. -/
theorem overpay_overpay_expectation :
    weighted (twoBranchWeights (2 / 5)) (fun w => cover 100 300 w) = 80 := by
  rw [weighted_twoBranch]
  show (2 / 5) * clipU (cres 100 300 [true]) + (1 - 2 / 5) * clipU (cres 100 300 [false]) = 80
  rw [cres_true_eq, cres_false_eq]
  norm_num [cover, clipU]

/-- At threshold 0 the clipped-balance event has probability 1 while the
raw-residual event has probability 3/5 — two different events. -/
theorem threshold_zero_distinction :
    eventMass (twoBranchWeights (2 / 5)) (fun w => cbal 100 300 w) 0 = 1 ∧
    eventMass (twoBranchWeights (2 / 5)) (fun w => cres 100 300 w) 0 = 3 / 5 := by
  constructor
  · rw [eventMass_twoBranch]
    show (if (0:ℚ) ≤ cbal 100 300 [true] then (2:ℚ) / 5 else (0:ℚ))
        + (if (0:ℚ) ≤ cbal 100 300 [false] then 1 - (2:ℚ) / 5 else (0:ℚ)) = 1
    rw [cres_true_eq, cres_false_eq]
    norm_num [cbal, clipC]
  · rw [eventMass_twoBranch]
    show (if (0:ℚ) ≤ cres 100 300 [true] then (2:ℚ) / 5 else (0:ℚ))
        + (if (0:ℚ) ≤ cres 100 300 [false] then (3:ℚ) / 5 else (0:ℚ)) = 3 / 5
    rw [cres_true_eq, cres_false_eq]
    norm_num

/-- Frozen main sample (P=1000, q=300, p=2/5): the principal expectation is
880. -/
theorem main_principal_expectation :
    weighted (twoBranchWeights (2 / 5)) (fun w => cbal 1000 300 w) = 880 := by
  rw [weighted_twoBranch]
  show (2 / 5) * clipC (cres 1000 300 [true]) + (1 - 2 / 5) * clipC (cres 1000 300 [false]) = 880
  rw [cres_true_eq, cres_false_eq]
  norm_num [clipC]

/-- Frozen main sample: the threshold-800 event probability is 3/5. -/
theorem main_threshold_event :
    eventMass (twoBranchWeights (2 / 5)) (fun w => cbal 1000 300 w) 800 = 3 / 5 := by
  rw [eventMass_twoBranch]
  show (if (800:ℚ) ≤ clipC (cres 1000 300 [true]) then 2 / 5 else 0)
      + (if (800:ℚ) ≤ clipC (cres 1000 300 [false]) then 1 - 2 / 5 else 0) = 3 / 5
  rw [cres_true_eq, cres_false_eq]
  norm_num [clipC]

/-- Frozen main sample interval: [790, 930]. -/
theorem main_interval : (880 : ℚ) - 100 + 10 = 790 ∧ 880 + 60 - 10 = 930 := by
  norm_num

/-- Frozen main sample: only 850 in the declared grid {600, 850, 1100} is
eligible within [790, 930]. -/
theorem main_eligible :
    ([600, 850, 1100] : List ℚ).filter (fun x => decide ((790 : ℚ) ≤ x ∧ x ≤ 930)) = [850] := by
  decide

/-- 860 lies inside the interval but outside the declared grid — an interval
midpoint is not automatically a legal candidate. -/
theorem interval_point_not_in_grid :
    ((790 : ℚ) ≤ 860 ∧ 860 ≤ 930) ∧ ¬ ∃ x ∈ ([600, 850, 1100] : List ℚ), x = 860 := by
  refine ⟨by norm_num, ?_⟩
  rintro ⟨x, hx, heq⟩
  subst heq
  rcases List.mem_cons.mp hx with h0 | hx
  · norm_num at h0
  · rcases List.mem_cons.mp hx with h1 | hx
    · norm_num at h1
    · rcases List.mem_cons.mp hx with h2 | hx
      · norm_num at h2
      · simp at hx

end JurisLean.BusinessRoot
