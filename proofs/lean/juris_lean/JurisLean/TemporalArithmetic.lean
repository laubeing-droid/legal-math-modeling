import JurisLean.LegalIds

/-!
中文说明：M5 P04 时态算术。日历天运算、区间交叠、边界包含性。
闰日/时区/粒度在数据层显式（见 TemporalApplicability），本模块只给
纯算术合同。
-/

namespace JurisLean

/-- 中文说明：日历天加法。 -/
def addDays (day : Int) (n : Nat) : Int :=
  day + n

/-- 中文说明：闭区间。 -/
structure DayInterval where
  fromDay : Int
  toDay : Int
deriving DecidableEq

/-- 中文说明：区间良态。 -/
def DayInterval.valid (i : DayInterval) : Prop :=
  i.fromDay ≤ i.toDay

/-- 中文说明：时点属于闭区间。 -/
def DayInterval.contains (i : DayInterval) (d : Int) : Prop :=
  i.fromDay ≤ d ∧ d ≤ i.toDay

/-- 中文说明：**日数计数**——补 `Seams/Temporal.lean` §未覆盖第 5 项自记的"`DayInterval` 无日数计数"，
    也是 `Nat`（论长）与 `DayInterval`（论区间）两格之间的具名换算。闭区间含的天数
    `(toDay - fromDay).toNat + 1`。诚实边界：不假设 `valid`；端点逆序时 `Int.toNat` 落到 `0`、
    计数退化为 `1`（见 `dayCount_ge_one`，故它是个全函数，不吞定义域）。 -/
def DayInterval.dayCount (i : DayInterval) : Nat := (i.toDay - i.fromDay).toNat + 1

/-- 中文证明：日数恒不小于 1（全函数有下界，逆序退化也仍是 1）。 -/
theorem DayInterval.dayCount_ge_one (i : DayInterval) : 1 ≤ i.dayCount := by
  unfold DayInterval.dayCount
  exact Nat.le_add_left 1 _

/-- 中文证明：单点闭区间 `[0,0]` 的日数是 1——具例核对定义不是空转。 -/
theorem DayInterval.dayCount_single_day : DayInterval.dayCount ⟨0, 0⟩ = 1 := rfl

/-- 中文说明：区间交集（可能为空）。 -/
def intervalIntersection (a b : DayInterval) : Option DayInterval :=
  if max a.fromDay b.fromDay ≤ min a.toDay b.toDay then
    some { fromDay := max a.fromDay b.fromDay, toDay := min a.toDay b.toDay }
  else
    none

/-- 中文证明：左端点包含于自身区间（闭区间边界）。 -/
theorem interval_contains_left_endpoint (i : DayInterval) (hv : i.valid) :
    i.contains i.fromDay := by
  dsimp [DayInterval.contains]
  exact ⟨le_rfl, hv⟩

/-- 中文证明：右端点包含于自身区间（闭区间边界）。 -/
theorem interval_contains_right_endpoint (i : DayInterval) (hv : i.valid) :
    i.contains i.toDay := by
  dsimp [DayInterval.contains]
  exact ⟨hv, le_rfl⟩

/-- 中文证明：区间外的时点不被包含。 -/
theorem interval_excludes_beyond_right (i : DayInterval) (d : Int)
    (h : i.toDay < d) : ¬ i.contains d := by
  intro hc
  exact lt_irrefl _ (lt_of_lt_of_le h hc.2)

/-- 中文证明：交集结果若存在则自身是良态区间。 -/
theorem intersection_some_is_valid (a b : DayInterval) (i : DayInterval)
    (hinter : intervalIntersection a b = some i) : i.valid := by
  dsimp [intervalIntersection] at hinter
  split at hinter
  · rename_i h
    injection hinter with hf
    rw [← hf]
    exact h
  · contradiction

/-- 中文证明：交集结果若存在则同时落在两个原区间内。 -/
theorem intersection_contained_in_both (a b i : DayInterval)
    (hinter : intervalIntersection a b = some i) (d : Int)
    (hd : i.contains d) : a.contains d ∧ b.contains d := by
  dsimp [intervalIntersection] at hinter
  split at hinter
  · rename_i _h
    injection hinter with hf
    rw [← hf] at hd
    dsimp [DayInterval.contains] at hd ⊢
    constructor
    · exact ⟨le_trans (le_max_left _ _) hd.1, le_trans hd.2 (min_le_left _ _)⟩
    · exact ⟨le_trans (le_max_right _ _) hd.1, le_trans hd.2 (min_le_right _ _)⟩
  · contradiction

/-- 中文证明：不交叠的区间交集为空（fail-closed 的算术基础）。 -/
theorem disjoint_intervals_no_intersection (a b : DayInterval)
    (hsep : a.toDay < b.fromDay) : intervalIntersection a b = none := by
  dsimp [intervalIntersection]
  split
  · rename_i h
    exact False.elim (not_le_of_gt hsep
      (le_trans (le_trans (le_max_right _ _) h) (min_le_left _ _)))
  · rfl

end JurisLean
