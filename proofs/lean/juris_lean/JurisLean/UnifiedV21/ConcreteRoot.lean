import JurisLean.UnifiedV21.Representation
import JurisLean.UnifiedV21.Authority
import JurisLean.UnifiedV2.ConcreteBridge

namespace JurisLean.ULM.UnifiedV21

def normalizer (prior likeYes likeNo : ℚ) : ℚ :=
  prior*likeYes + (1-prior)*likeNo

def posterior (prior likeYes likeNo : ℚ) : ℚ :=
  prior*likeYes / normalizer prior likeYes likeNo

theorem posterior_unit (t a b : ℚ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hz : 0 < normalizer t a b) :
    0 ≤ posterior t a b ∧ posterior t a b ≤ 1 := by
  have hn : 0 ≤ t*a := mul_nonneg ht0 ha
  have hr : 0 ≤ (1-t)*b := mul_nonneg (sub_nonneg.mpr ht1) hb
  constructor
  · exact div_nonneg hn (le_of_lt hz)
  · apply (div_le_one hz).2
    dsimp [normalizer]
    linarith

structure CaseInput where
  context : ContextKey
  prior : ℚ
  likeYes : ℚ
  likeNo : ℚ
  due : ℚ
  paid : ℚ
  costP : ℚ
  costD : ℚ
  settlementCostP : ℚ
  settlementCostD : ℚ
  lawful : List ℚ

/-- This scenario concerns recognition, not an automatic fact-admission rule. -/
def recognitionProbability (d : CaseInput) := posterior d.prior d.likeYes d.likeNo

def expectedAward (d : CaseInput) : ℚ :=
  recognitionProbability d * (d.due-d.paid) + (1-recognitionProbability d)*d.due

def irLower (d : CaseInput) : ℚ := expectedAward d - d.costP + d.settlementCostP

def irUpper (d : CaseInput) : ℚ := expectedAward d + d.costD - d.settlementCostD

def lawfulIR (d : CaseInput) : Set ℚ :=
  {x | x ∈ d.lawful ∧ irLower d ≤ x ∧ x ≤ irUpper d}

def feasibleCandidates (d : CaseInput) : List ℚ :=
  d.lawful.filter fun x => decide (irLower d ≤ x ∧ x ≤ irUpper d)

def chooseFirst (lo hi : ℚ) : List ℚ → Option ℚ
  | [] => none
  | x::xs => if lo ≤ x ∧ x ≤ hi then some x else chooseFirst lo hi xs

def chooseSettlement (d : CaseInput) := chooseFirst (irLower d) (irUpper d) d.lawful

theorem expected_award_from_posterior (d : CaseInput) :
    expectedAward d = d.due - recognitionProbability d * d.paid := by
  dsimp [expectedAward]
  ring

theorem actual_candidate_representation_exact (d : CaseInput) :
    {x | x ∈ feasibleCandidates d} = lawfulIR d := by
  ext x
  simp [feasibleCandidates, lawfulIR]

theorem chooseFirst_member (lo hi z : ℚ) (xs : List ℚ)
    (h : chooseFirst lo hi xs = some z) : z ∈ xs ∧ lo ≤ z ∧ z ≤ hi := by
  revert h
  induction xs with
  | nil => simp [chooseFirst]
  | cons x xs ih =>
    intro h
    by_cases hx : lo ≤ x ∧ x ≤ hi
    · simp [chooseFirst, hx] at h
      subst z
      exact ⟨by simp, hx⟩
    · have ht : chooseFirst lo hi xs = some z := by simpa [chooseFirst, hx] using h
      rcases ih ht with ⟨hm, hl, hu⟩
      exact ⟨by simp [hm], hl, hu⟩

theorem chooseFirst_none (lo hi : ℚ) (xs : List ℚ) :
    chooseFirst lo hi xs = none ↔ ∀ x ∈ xs, ¬ (lo ≤ x ∧ x ≤ hi) := by
  induction xs with
  | nil => simp [chooseFirst]
  | cons x xs ih =>
    by_cases hx : lo ≤ x ∧ x ≤ hi
    · simp [chooseFirst, hx]
    · rw [chooseFirst, if_neg hx]
      exact ih

theorem selected_point_is_lawful_and_ir (d : CaseInput) (x : ℚ)
    (h : chooseSettlement d = some x) : x ∈ lawfulIR d :=
  chooseFirst_member (irLower d) (irUpper d) x d.lawful h

theorem no_choice_means_empty_declared_intersection (d : CaseInput)
    (h : chooseSettlement d = none) : lawfulIR d = ∅ := by
  have hn := (chooseFirst_none (irLower d) (irUpper d) d.lawful).mp h
  ext x
  simp only [lawfulIR, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro hx
  exact hn x hx.1 hx.2

/-- Actual data dependence: probability is updated from the SAME input;
amount and IR bounds are derived, not free lo/hi parameters; the selected
point belongs to the intersection of lawful candidates and mutual acceptance.
This is a concrete scoped seed, not the completed universal C07 theorem. -/
theorem concrete_root_contract (d : CaseInput)
    (ht0 : 0 ≤ d.prior) (ht1 : d.prior ≤ 1)
    (ha : 0 ≤ d.likeYes) (hb : 0 ≤ d.likeNo)
    (hz : 0 < normalizer d.prior d.likeYes d.likeNo) :
    (0 ≤ recognitionProbability d ∧ recognitionProbability d ≤ 1) ∧
    expectedAward d = d.due-recognitionProbability d*d.paid ∧
    {x | x ∈ feasibleCandidates d} = lawfulIR d ∧
    (∀ x, chooseSettlement d = some x → x ∈ lawfulIR d) := by
  exact ⟨posterior_unit d.prior d.likeYes d.likeNo ht0 ht1 ha hb hz,
    expected_award_from_posterior d, actual_candidate_representation_exact d,
    selected_point_is_lawful_and_ir d⟩

end JurisLean.ULM.UnifiedV21
