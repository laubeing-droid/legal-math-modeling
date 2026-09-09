import JurisLean.UnifiedV2.Quantified
import JurisLean.UnifiedV2.LegalInterfaces

namespace JurisLean.ULM.UnifiedV2

/-- An explicitly stipulated two-scenario debt example. The amount may be
negative (overpayment); this definition does not silently erase that issue.
This is not an implementation of all Chinese debt doctrine. -/
def branchAmount (due paid : ℚ) (paymentRecognized : Bool) : ℚ :=
  if paymentRecognized then due - paid else due

def branchSolutions (due paid : ℚ) : Set (Bool × ℚ) :=
  {w | w.2 = branchAmount due paid w.1}

def branchCandidates (due paid : ℚ) : List (Bool × ℚ) :=
  [(true, due-paid), (false, due)]

theorem branch_carrier_complete (due paid : ℚ) :
    {w | w ∈ branchCandidates due paid} = branchSolutions due paid := by
  ext w
  rcases w with ⟨b,y⟩
  cases b <;> simp [branchCandidates, branchSolutions, branchAmount, eq_comm]

def expectedBranchAmount (p due paid : ℚ) : ℚ :=
  p * branchAmount due paid true + (1-p)*branchAmount due paid false

theorem expected_amount_bridge (p due paid : ℚ) :
    expectedBranchAmount p due paid = due-p*paid := by
  simp [expectedBranchAmount,branchAmount]
  ring

def branchWin (p due paid threshold : ℚ) : ℚ :=
  p * (if threshold ≤ branchAmount due paid true then 1 else 0) +
  (1-p) * (if threshold ≤ branchAmount due paid false then 1 else 0)

theorem win_split_bridge (p due paid threshold : ℚ)
    (hLow : due-paid < threshold) (hHigh : threshold ≤ due) :
    branchWin p due paid threshold = 1-p := by
  simp [branchWin, branchAmount, not_le.mpr hLow, hHigh]

theorem win_probability_in_unit (p due paid threshold : ℚ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ branchWin p due paid threshold ∧ branchWin p due paid threshold ≤ 1 := by
  unfold branchWin
  split_ifs <;> constructor <;> linarith

def bargainingPoint (lo hi weight : ℚ) : ℚ :=
  lo + weight*(hi-lo)

theorem bargaining_point_ir (lo hi weight : ℚ)
    (h : lo ≤ hi) (hw0 : 0 ≤ weight) (hw1 : weight ≤ 1) :
    lo ≤ bargainingPoint lo hi weight ∧ bargainingPoint lo hi weight ≤ hi := by
  unfold bargainingPoint
  constructor <;> nlinarith

/-- Retained V2 algebraic conjunction. Its free lo/hi are NOT a proof of
end-to-end case data dependence. UnifiedV21.ConcreteRoot supersedes it for
that purpose; retaining this lemma preserves existing mathematical assets. -/
theorem concrete_complete_bridge (p due paid threshold lo hi weight : ℚ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hLow : due-paid < threshold) (hHigh : threshold ≤ due)
    (hRange : lo ≤ hi) (hw0 : 0 ≤ weight) (hw1 : weight ≤ 1) :
    {w | w ∈ branchCandidates due paid} = branchSolutions due paid ∧
    branchWin p due paid threshold = 1-p ∧
    (0 ≤ branchWin p due paid threshold ∧ branchWin p due paid threshold ≤ 1) ∧
    expectedBranchAmount p due paid = due-p*paid ∧
    (lo ≤ bargainingPoint lo hi weight ∧ bargainingPoint lo hi weight ≤ hi) := by
  exact ⟨branch_carrier_complete due paid,
    win_split_bridge p due paid threshold hLow hHigh,
    win_probability_in_unit p due paid threshold hp0 hp1,
    expected_amount_bridge p due paid,
    bargaining_point_ir lo hi weight hRange hw0 hw1⟩

end JurisLean.ULM.UnifiedV2
