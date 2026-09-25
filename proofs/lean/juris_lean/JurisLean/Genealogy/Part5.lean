import JurisLean.Genealogy.Part4

/-!
Genealogy Part5 — L5 computation contracts lifted to theorem-level structural facts.
Numbers are exact Nat values here; no theorem asserts that a supplied legal rate/amount is correct.
-/

namespace JurisLean.Genealogy.Part5

namespace P096

structure InterestSegment where
  rate : Nat
  days : Nat
 deriving DecidableEq, Repr

def segmentInterest (principal : Nat) (s : InterestSegment) : Nat :=
  principal * s.rate * s.days

def segmentedInterest (principal : Nat) : List InterestSegment → Nat
  | [] => 0
  | s :: ss => segmentInterest principal s + segmentedInterest principal ss

/-- Two-segment whole equals the sum of the two explicit segment amounts. -/
theorem two_segment_refinement
    (principal : Nat) (s1 s2 : InterestSegment) :
    segmentedInterest principal [s1, s2] =
      segmentInterest principal s1 + segmentInterest principal s2 := by
  simp [segmentedInterest]
-- [定义展开] 置信：只展开两层递归并化简末尾 `+ 0`。

/-- Empty segmentation accrues zero in this structural calculator. -/
theorem empty_segments_zero (principal : Nat) :
    segmentedInterest principal [] = 0 := rfl
-- [rfl] 置信：空列表递归基例。

end P096

namespace P097

structure DebtItem where
  debtId : String
  amount : Nat
 deriving DecidableEq, Repr

structure AllocationStep where
  applied : Nat
  remainder : Nat
 deriving DecidableEq, Repr

def allocateOne (payment : Nat) (debt : DebtItem) : AllocationStep :=
  if h : payment ≤ debt.amount then
    { applied := payment, remainder := 0 }
  else
    { applied := debt.amount, remainder := payment - debt.amount }

/-- Underfunded single-debt step applies all payment and leaves zero remainder. -/
theorem allocate_one_underfunded
    (payment : Nat) (debt : DebtItem) (h : payment ≤ debt.amount) :
    allocateOne payment debt = { applied := payment, remainder := 0 } := by
  simp [allocateOne, h]
-- [定义展开] 置信：比较分支由 `h` 直接锁死。

/-- Overfunded single-debt step applies the debt and carries payment-debt as remainder. -/
theorem allocate_one_overfunded
    (payment : Nat) (debt : DebtItem) (h : ¬ payment ≤ debt.amount) :
    allocateOne payment debt =
      { applied := debt.amount, remainder := payment - debt.amount } := by
  simp [allocateOne, h]
-- [定义展开] 置信：否定比较分支由 `h` 直接锁死；不需减法守恒引理。

def allocateTwo
    (payment : Nat) (first second : DebtItem) : Nat × Nat × Nat :=
  let a1 := allocateOne payment first
  let a2 := allocateOne a1.remainder second
  (a1.applied, a2.applied, a2.remainder)

/-- Two-debt concrete conservation witness: 10 = 6 + 4 + 0. -/
theorem two_debt_conservation_witness :
    allocateTwo 10
      { debtId := "D1", amount := 6 }
      { debtId := "D2", amount := 8 }
      = (6, 4, 0) := by
  decide
-- [decide] 置信：两次 Nat ≤/减法均为闭式计算；未调用一般列表归纳引理。

end P097

namespace P098

def clamp (lo hi x : Nat) : Nat :=
  if x < lo then lo
  else if hi < x then hi
  else x

def inBand (lo hi x : Nat) : Bool :=
  decide (lo ≤ x ∧ x ≤ hi)

/-- Below-band values clamp to the lower bound. -/
theorem clamp_below_to_low (lo hi x : Nat) (h : x < lo) :
    clamp lo hi x = lo := by
  simp [clamp, h]
-- [定义展开] 置信：首个比较由 `h` 锁死。

/-- Below-band clamp output lies in a valid band. -/
theorem clamp_below_in_band
    (lo hi x : Nat) (hBand : lo ≤ hi) (hLow : x < lo) :
    inBand lo hi (clamp lo hi x) = true := by
  simp [clamp, inBand, hBand, hLow]
-- [定义展开] 置信：clamp 归约为 lo 后，仅剩 `lo≤lo ∧ lo≤hi`，由 simp+hBand 闭合。

/-- Above-band values clamp to the upper bound when the low branch is excluded. -/
theorem clamp_above_to_high
    (lo hi x : Nat) (hNotLow : ¬ x < lo) (hHigh : hi < x) :
    clamp lo hi x = hi := by
  simp [clamp, hNotLow, hHigh]
-- [定义展开] 置信：两个 if 条件均由参数锁死。

/-- Above-band clamp output lies in a valid band. -/
theorem clamp_above_in_band
    (lo hi x : Nat) (hBand : lo ≤ hi)
    (hNotLow : ¬ x < lo) (hHigh : hi < x) :
    inBand lo hi (clamp lo hi x) = true := by
  simp [clamp, inBand, hBand, hNotLow, hHigh]
-- [定义展开] 置信：clamp 归约为 hi 后，仅剩 `lo≤hi ∧ hi≤hi`。

/-- Inside-band points are fixed points. -/
theorem clamp_inside_fixed
    (lo hi x : Nat) (hLow : ¬ x < lo) (hHigh : ¬ hi < x) :
    clamp lo hi x = x := by
  simp [clamp, hLow, hHigh]
-- [定义展开] 置信：两个越界条件均被排除，直接返回 x。

/-- Inside-band clamping is idempotent. -/
theorem clamp_inside_idempotent
    (lo hi x : Nat) (hLow : ¬ x < lo) (hHigh : ¬ hi < x) :
    clamp lo hi (clamp lo hi x) = clamp lo hi x := by
  simp [clamp, hLow, hHigh]
-- [定义展开] 置信：内层与外层均由同一两个条件归约为 x。

end P098

namespace P099

def taxSlice (taxable lower upper rate : Nat) : Nat :=
  if taxable ≤ lower then 0
  else Nat.min (taxable - lower) (upper - lower) * rate

def topSlice (taxable lower rate : Nat) : Nat :=
  if taxable ≤ lower then 0 else (taxable - lower) * rate

def progressiveTax3
    (taxable cut1 cut2 rate1 rate2 rate3 : Nat) : Nat :=
  taxSlice taxable 0 cut1 rate1 +
  taxSlice taxable cut1 cut2 rate2 +
  topSlice taxable cut2 rate3

/-- Three-bracket concrete witness: only each bracket's slice is taxed. -/
theorem progressive_three_bracket_witness :
    progressiveTax3 250 100 200 1 2 3 = 450 := by
  decide
-- [decide] 置信：100*1 + 100*2 + 50*3 = 450，全部 Nat 闭式计算。

/-- Two effective brackets when taxable income does not reach the top bracket. -/
theorem progressive_two_effective_brackets_witness :
    progressiveTax3 150 100 200 1 2 3 = 200 := by
  decide
-- [decide] 置信：100*1 + 50*2 + 0 = 200。

end P099

namespace P100

inductive DamageFormulaId where
  | repair
  | lostProfit
  | spiritual
  | unknown
 deriving DecidableEq, Repr

def formulaFactor : DamageFormulaId → Option Nat
  | .repair => some 1
  | .lostProfit => some 2
  | .spiritual => some 3
  | .unknown => none

def computeDamageItem (formula : DamageFormulaId) (base : Nat) : Option Nat :=
  match formulaFactor formula with
  | none => none
  | some factor => some (factor * base)

/-- Unknown damage formula ids fail closed. -/
theorem unknown_damage_formula_none (base : Nat) :
    computeDamageItem .unknown base = none := rfl
-- [rfl] 置信：unknown 查表为 none，计算函数随即返回 none。

/-- Registered formula lookup computes deterministically. -/
theorem registered_damage_formula_witness :
    computeDamageItem .lostProfit 10 = some 20 := rfl
-- [rfl] 置信：factor=2 后 Nat 乘法字面量归约。

end P100

namespace P102

def delayInterest (principal dailyRate days : Nat) : Nat :=
  principal * dailyRate * days

/-- Delay interest is exactly principal × rate × nonnegative Nat days. -/
theorem delay_interest_formula (principal dailyRate days : Nat) :
    delayInterest principal dailyRate days = principal * dailyRate * days := rfl
-- [rfl] 置信：定理右侧即定义体；Nat 类型排除了负天数。

end P102

namespace P103

inductive ContractState where
  | draft
  | locked
  | executed
  | terminated
 deriving DecidableEq, Repr

def legalEdge : ContractState → ContractState → Bool
  | .draft, .locked => true
  | .locked, .executed => true
  | .locked, .terminated => true
  | .executed, .terminated => true
  | _, _ => false

def transitionContractState
    (current target : ContractState) (consentRecorded : Bool) : ContractState :=
  match consentRecorded with
  | false => current
  | true =>
      match legalEdge current target with
      | true => target
      | false => current

/-- No consent means no state movement. -/
theorem no_consent_no_transition (current target : ContractState) :
    transitionContractState current target false = current := rfl
-- [rfl] 置信：函数先匹配 consent=false 并直接返回 current。

/-- A listed edge with consent moves. -/
theorem consent_and_legal_edge_moves :
    transitionContractState .draft .locked true = .locked := rfl
-- [rfl] 置信：draft→locked 的 legalEdge 定义为 true。

/-- A non-edge remains unchanged even with consent. -/
theorem consent_cannot_create_nonedge :
    transitionContractState .draft .executed true = .draft := rfl
-- [rfl] 置信：draft→executed 落入 legalEdge wildcard=false。

end P103

namespace P114

inductive BridgeEvidence where
  | deduction
  | probabilityOne
 deriving DecidableEq, Repr

def bridgesToDeduction : BridgeEvidence → Bool
  | .deduction => true
  | .probabilityOne => false

/-- Deduction has the one-way bridge to probability-one status. -/
theorem deduction_bridges : bridgesToDeduction .deduction = true := rfl
-- [rfl] 置信：deduction 构造子直接映射 true。

/-- Probability one alone does not bridge back to deduction. -/
theorem probability_one_not_deduction :
    bridgesToDeduction .probabilityOne = false := rfl
-- [rfl] 置信：反向构造子直接映射 false，形成显式反例见证。

end P114

namespace P117

inductive SimilarityGrade where
  | candidateOnly
  | invalidOverreach
 deriving DecidableEq, Repr

structure SimilarityToolOutput where
  score : Nat
  assertedStructuralEquivalence : Bool
 deriving DecidableEq, Repr

def grade (o : SimilarityToolOutput) : SimilarityGrade :=
  match o.assertedStructuralEquivalence with
  | true => .invalidOverreach
  | false => .candidateOnly

/-- Claiming structural equivalence from similarity is invalid overreach. -/
theorem structural_equivalence_assertion_invalid (score : Nat) :
    grade { score := score, assertedStructuralEquivalence := true } = .invalidOverreach := rfl
-- [rfl] 置信：true 分支固定映射 invalidOverreach。

/-- Ordinary similarity output remains candidate-only. -/
theorem similarity_stays_candidate (score : Nat) :
    grade { score := score, assertedStructuralEquivalence := false } = .candidateOnly := rfl
-- [rfl] 置信：false 分支固定映射 candidateOnly。

end P117

end JurisLean.Genealogy.Part5
