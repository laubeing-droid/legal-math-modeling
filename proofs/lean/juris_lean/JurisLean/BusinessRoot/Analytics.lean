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
  by_cases h : 0 ≤ r
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
    ring
  · have hr : r ≤ 0 := le_of_lt (lt_of_not_ge h)
    rw [max_eq_right hr, max_eq_left (neg_nonneg.mpr hr)]
    ring

/-- Weighted linearity under pointwise subtraction of the per-scenario quantity. -/
theorem weighted_sub (ws : List (ℚ × World)) (f g : World → ℚ) :
    weighted ws f - weighted ws g = weighted ws (fun w => f w - g w) := by
  induction ws with
  | nil => rfl
  | cons x rest ih =>
      simp only [weighted, List.map_cons, List.sum_cons]
      have h1 : x.1 * f x.2 - x.1 * g x.2 = x.1 * (f x.2 - g x.2) := by ring
      rw [h1, ih]

/-- Weighted value only depends on the per-scenario quantities. -/
theorem weighted_congr (ws : List (ℚ × World)) (f g : World → ℚ)
    (h : ∀ p ∈ ws, f p.2 = g p.2) : weighted ws f = weighted ws g := by
  induction ws with
  | nil => rfl
  | cons x rest ih =>
      simp only [weighted, List.map_cons, List.sum_cons]
      rw [h x (by simp)]
      exact congrArg _ (ih fun p hp => h p (by simp [hp]))

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

/-- The two-branch probability weights of the frozen task. -/
def twoBranchWeights (p : ℚ) : List (ℚ × World) := [(p, [true]), (1 - p, [false])]

/-- Conservation for the nonnegative decomposition: E[C] − E[U] = P − q·p.
This uses C and U, never E[R] in place of E[C]. -/
theorem CU_expectation_conservation (P q p : ℚ) :
    weighted (twoBranchWeights p) (fun w => cbal P q w) -
      weighted (twoBranchWeights p) (fun w => cover P q w) = P - p * q := by
  rw [weighted_sub, weighted_twoBranch]
  simp only [cbal, cover, split_identity, cres, isRecognized]
  ring

/-- Frozen overpayment sample (P=100, q=300, p=2/5): the raw residual
expectation is −20. -/
theorem overpay_raw_expectation :
    weighted (twoBranchWeights (2 / 5)) (fun w => cres 100 300 w) = -20 := by
  decide

/-- Frozen overpayment sample: the nonnegative principal expectation is 60,
not −20 — the raw expectation is not the principal expectation. -/
theorem overpay_principal_expectation :
    weighted (twoBranchWeights (2 / 5)) (fun w => cbal 100 300 w) = 60 := by
  decide

/-- Frozen overpayment sample: the overpayment expectation is 80. -/
theorem overpay_overpay_expectation :
    weighted (twoBranchWeights (2 / 5)) (fun w => cover 100 300 w) = 80 := by
  decide

/-- At threshold 0 the clipped-balance event has probability 1 while the
raw-residual event has probability 3/5 — two different events. -/
theorem threshold_zero_distinction :
    eventMass (twoBranchWeights (2 / 5)) (fun w => cbal 100 300 w) 0 = 1 ∧
    eventMass (twoBranchWeights (2 / 5)) (fun w => cres 100 300 w) 0 = 3 / 5 := by
  refine ⟨?_, ?_⟩ <;> decide

/-- Frozen main sample (P=1000, q=300, p=2/5): the principal expectation is
880. -/
theorem main_principal_expectation :
    weighted (twoBranchWeights (2 / 5)) (fun w => cbal 1000 300 w) = 880 := by
  decide

/-- Frozen main sample: the threshold-800 event probability is 3/5. -/
theorem main_threshold_event :
    eventMass (twoBranchWeights (2 / 5)) (fun w => cbal 1000 300 w) 800 = 3 / 5 := by
  decide

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
      · exact List.not_mem_nil _ hx

end JurisLean.BusinessRoot
