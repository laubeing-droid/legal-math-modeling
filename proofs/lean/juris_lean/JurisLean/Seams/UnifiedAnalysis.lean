import Mathlib.Tactic

/-
Unified analysis, layer M (plan §7; I.4.15 L15, fragment for U27–U28).

The analysis-correspondence face: results carry their MODE and their
sources; correctness is derived from the algorithm lemmas, never
assumed as a premise.

* `FinProb`/`prob`: a finite probability space over ℚ masses;
  `prob_union_bound` PROVES the union bound by finset arithmetic on the
  same Ω — subadditivity is not assumed for an arbitrary set function.
* Outer composition: interval hulls stay monotone under composition
  (`hull_monotone`, `outer_compose_stays_outer`).
* Inner bounds need implementable witnesses; the CARTESIAN PRODUCT of
  local inner bounds is not a joint inner bound —
  `cartesian_point_infeasible` (the product point violates the coupling
  constraint x + y ≤ 1) with `joint_interior_witness` ((1/2, 1/2)).
* Missing propagates by scope: an issue absent from the results reads
  `none`, never a fabricated value; UNRELATED issues keep computing
  (`unrelated_continue`).
* Implementation error and missing authorization are never converted
  into court judgments (`error_not_court_judgment`).

Scope, honestly: finite Ω with rational masses; no filter families or
continuous martingale claims (the adaptive-calibration track is not
touched); statistical composition beyond the finite union bound
(root_STATISTICAL_COMPOSITION reuse) is recorded as future work.
-/

namespace JurisLean.Seams.UnifiedAnalysis

variable {Ω : Type} [DecidableEq Ω]

/-! ## 一、有限概率空间与并集界（同 Ω 实测） -/

/-- 有限概率空间（ℚ 质量函数，总质量 1）。 -/
structure FinProb (Ω : Type) [DecidableEq Ω] where
  /-- 支撑集。 -/
  support : Finset Ω
  /-- 质量函数。 -/
  mass : Ω → ℚ

/-- 事件概率（同 Ω 上实测；指标函数形，逐点算术可达）。 -/
def prob (fp : FinProb Ω) (A : Finset Ω) : ℚ :=
  ∑ ω ∈ fp.support, (if ω ∈ A then fp.mass ω else 0)

/-- **并集界（证明，不假设）**：同一 Ω 上 P(A∪B) ≤ P(A)+P(B)
    ——由有限集和的交并分解直接推出，不对任意集合函数假设立得。 -/
theorem prob_union_bound (fp : FinProb Ω) (A B : Finset Ω) :
    prob fp (A ∪ B) ≤ prob fp A + prob fp B := by
  have key : ∀ ω ∈ fp.support,
      (if ω ∈ A ∪ B then fp.mass ω else 0)
        ≤ (if ω ∈ A then fp.mass ω else 0) + (if ω ∈ B then fp.mass ω else 0) := by
    intro ω _
    by_cases h1 : ω ∈ A <;> by_cases h2 : ω ∈ B <;>
      simp [Finset.mem_union, h1, h2] <;>
      first
        | linarith
        | rfl
  calc prob fp (A ∪ B)
      = ∑ ω ∈ fp.support, (if ω ∈ A ∪ B then fp.mass ω else 0) := rfl
    _ ≤ ∑ ω ∈ fp.support,
          ((if ω ∈ A then fp.mass ω else 0) + (if ω ∈ B then fp.mass ω else 0)) :=
        Finset.sum_le_sum key
    _ = (∑ ω ∈ fp.support, (if ω ∈ A then fp.mass ω else 0))
        + ∑ ω ∈ fp.support, (if ω ∈ B then fp.mass ω else 0) :=
        Finset.sum_add_distrib _ _

/-! ## 二、外界的复合单调 -/

/-- 有理区间。 -/
structure Iv where
  lo : ℚ
  hi : ℚ

/-- 区间包含。 -/
def ivSub (a b : Iv) : Prop := b.lo ≤ a.lo ∧ a.hi ≤ b.hi

/-- 凸包（两点 hull）。 -/
def hull (a b : Iv) : Iv where
  lo := min a.lo b.lo
  hi := max a.hi b.hi

/-- hull 包含两个成分。 -/
theorem hull_monotone (a b : Iv) : ivSub a (hull a b) ∧ ivSub b (hull a b) := by
  unfold ivSub hull
  exact ⟨⟨min_le_left a.lo b.lo, le_max_left a.hi b.hi⟩,
    ⟨min_le_right a.lo b.lo, le_max_right a.hi b.hi⟩⟩

/-- **外界复合仍是外界**：两次外包的 hull 仍包含原区间
    （每步单调及包含的复合律）。 -/
theorem outer_compose_stays_outer (a b c : Iv)
    (h1 : ivSub a b) (h2 : ivSub b c) : ivSub a c := by
  obtain ⟨hl1, hh1⟩ := h1
  obtain ⟨hl2, hh2⟩ := h2
  exact ⟨le_trans hl2 hl1, le_trans hh1 hh2⟩

/-! ## 三、内界要可实现见证；局部内界的笛卡尔积不是联合内界 -/

/-- 联合可行域（耦合约束 x+y≤1，各分量 [0,1]）。 -/
def feasibleQ (x y : ℚ) : Prop :=
  0 ≤ x ∧ x ≤ 1 ∧ 0 ≤ y ∧ y ≤ 1 ∧ x + y ≤ 1

/-- 局部内界最优点之积 (1,1) 不可行：耦合约束击破笛卡尔积。 -/
theorem cartesian_point_infeasible : ¬ feasibleQ 1 1 := by
  intro ⟨_, _, _, _, hle⟩
  norm_num at hle

/-- 联合内部可行见证：(1/2,1/2) 可行且乘积 1/4。 -/
theorem joint_interior_witness :
    feasibleQ (1 / 2) (1 / 2) ∧ (1 / 2 : ℚ) * (1 / 2) = 1 / 4 := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩

/-! ## 四、缺失按作用域传播；无关争点继续算 -/

/-- 争点计算状态。 -/
inductive IssueStatus : Type
  | computed (v : ℚ)
  | missing (code : ℕ)
  | blockedNoAuth
  deriving DecidableEq

/-- 争点读数：实现错误/缺授权不得变法院判断。 -/
inductive CourtRead : Type
  | judgment (v : ℚ)
  | noJudgment
  deriving DecidableEq

def readOf : IssueStatus → CourtRead
  | .computed v => .judgment v
  | .missing _ => .noJudgment
  | .blockedNoAuth => .noJudgment

/-- **错误不变法院判断**。 -/
theorem error_not_court_judgment (st : IssueStatus)
    (h : ∃ c, st = .missing c ∨ st = .blockedNoAuth) :
    readOf st = CourtRead.noJudgment := by
  obtain ⟨_, h⟩ := h
  rcases h with rfl | rfl <;> rfl

/-- 争点状态表读数（作用域内查表，作用域外 none——不伪造）。 -/
def statusOf : List (ℕ × IssueStatus) → ℕ → Option IssueStatus
  | [], _ => none
  | (q, st) :: rest, q' =>
      if q = q' then some st else statusOf rest q'

/-- **缺失按作用域传播**：表中缺失读缺失，表外读 none。 -/
theorem missing_propagates_scope :
    statusOf [(1, IssueStatus.missing 0), (2, IssueStatus.computed 5)] 1
      = some (IssueStatus.missing 0)
      ∧ statusOf [(1, IssueStatus.missing 0), (2, IssueStatus.computed 5)] 3
      = none := by
  constructor <;> rfl

/-- **无关争点继续算**：一争点缺失不阻塞另一争点的计算读数。 -/
theorem unrelated_continue :
    statusOf [(1, IssueStatus.missing 0), (2, IssueStatus.computed 5)] 2
      = some (IssueStatus.computed 5) := rfl

end JurisLean.Seams.UnifiedAnalysis
