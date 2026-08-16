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
    injection hinter with hf ht
    rw [← hf, ← ht]
    exact h
  · contradiction

/-- 中文证明：交集结果若存在则同时落在两个原区间内。 -/
theorem intersection_contained_in_both (a b i : DayInterval)
    (hinter : intervalIntersection a b = some i) (d : Int)
    (hd : i.contains d) : a.contains d ∧ b.contains d := by
  dsimp [intervalIntersection] at hinter
  split at hinter
  · rename_i _h
    injection hinter with hf ht
    rw [← hf, ← ht] at hd
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
    exact not_le_of_gt hsep
      (le_trans (le_trans (le_max_right _ _) h) (min_le_left _ _))
  · rfl

end JurisLean
