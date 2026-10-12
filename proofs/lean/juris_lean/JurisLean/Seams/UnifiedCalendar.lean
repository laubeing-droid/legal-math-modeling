import Mathlib.Tactic
import JurisLean.TemporalArithmetic
import JurisLean.FullMath.Numeric.Quantities

-- 闭式见证里的 `decide` 要在内核里走完 addCalDays/subCalDays 的上百次结构迭代
-- 与 List 求和（仓内 BusinessRoot/SevenAxis.lean:17 同款处置）。
set_option maxRecDepth 100000

/-!
UC（统一历法 / UNIFIED CALENDAR）——B11（D095–D103 金额时间）批的共享历法构造包。

## §法律语义

组 11 九项合同（`ALL_134_MATH_CONTRACTS.md` D095–D103）的共同证明路线写着同一句：
"日历、期限与效力时间：对已选日历规则证明变换；表驱动节假日为外部参数"。
`MATHEMATICS_SPEC.md` §5（M10）钉死了历法基础的四件事："整数天序、闰年、月份长度和
指定营业日日历迭代。法律期间以正确事件锚定，不把月一律换 30 天"。本件把这四件事
做成可证的完整历法，供 B11 九项 demand 合同与 W2-B N01（同源回灌）直接消费：

1. **日期表示与有效性**：年月日三元组 `CalDate`，有效性谓词复用
   `FullMath/Numeric/Quantities.lean`（N01）已钉定的 `leap`/`monthLen`/`validDate`
   （格雷果里闰年规则、大小月表），加一条本件新增的年份下界（历元为公元 1 年）。
2. **序与等价**：`toEpochDay` 把日期映到与 Python `datetime.toordinal` 同约定的
   永恒格雷果里历元日（0001-01-01 = 1）。主定理 `epoch_le_iff_lex`（皇冠定理）：
   历元日序 ⟺ 年月日字典序——D096（适用时点）、D100（倒排可行性）、D103（同一参考日）
   的全部日期比较由此一条定理供给；推论 `toEpochDay_inj` 给出等价（同历元日的两个
   合法日期是同一个日期）。
3. **天数差**：`daysDiff` 全 ℤ 精确；`daysDiff_split` 是分段计息（D095"独立基数、
   期间"）的算术内核——期间在中点切开的两天数差相加等于整段天数差。
4. **日加法**：`succDate`/`predDate` 做完整月/年 rollover，`addCalDays n` 定义为
   后继的 n 次迭代。定理：保有效性、历元日严格对齐（`+n`）、结合/交换
   （`addCalDays_add`/`addCalDays_comm`——迭代代数，全域无条件成立）、
   倒排往返（`sub_add_cancel`，适用域=倒排不越过历元）。
5. **月/年加法与月末钳制**：合同未指定钳制规则，本件选银行业标准"末日钳制"
   （`clampDay y m d = min d (monthLen y m)`），选择在施工报告披露。定理：钳制不超过
   原日、不超过目标月末、幂等（`clampDay_idem`）；单月推进历元日至少 28 天
   （`addCalMonths_1_epoch_ge`——"不把月一律换 30 天"的可证形式），年末跨月严格
   前进；12 个月 = 1 年。月末锚定**不**保持是本规则的诚实后果（2 月末 + 1 年 =
   次年 2 月 28 日非月末），见证 `witness_addCalYears_1_feb29` 如实展示而非掩盖。
6. **营业日滚动**：`nextBiz hol fuel d`——表驱动节假日 `hol : ℤ → Bool` 是外部
   参数（合同原文），`fuel` 界搜索半径。定理：命中营业日且位移有界
   （`nextBiz_spec`，前提=窗口内存在营业日，显式不假装）、位移窗界无前提版
   （`nextBiz_displacement_bound`）、不动点（`nextBiz_fixpoint`）、**顺延幂等**
   （`roll_idempotent`——D099 deadline_effect：已顺延到营业日的期限再顺延一次不变）。
7. **期限规格与倒排**：`PeriodSpec`（anchor/length/holiday/rollFuel 四元组，
   D099 合同句"不同期限带 anchor、length、calendar、deadline_effect"的载体形状）；
   同锚点下更长期限 ⇒ 更晚期限（`base_strict_order`——60 日补正期未到，仅因
   30 日通知期到便认定终止的反例在此被封死）；`backSchedule` 倒排（D100）：
   可行 ⇔ 倒排结果存在（`backSchedule_none_iff` 冲突报告），可行时正向推回恰得
   原期限（`backSchedule_some_addBack`）。
8. **与既有时间算术的接口**：`TemporalArithmetic.lean` 只有 ℤ 日计数器与
   `DayInterval`（无年月日历法，已逐行核验——它的闰日/时区口径显式留给数据层）。
   本件桥：`addDays_bridge`（既有 `JurisLean.addDays` 与历法日加法对齐）、
   `toDayInterval`（日期区间 ↪ 既有 `DayInterval`）、`cal_intersection_sound`/
   `cal_disjoint`（复用 `intersection_contained_in_both`/
   `disjoint_intervals_no_intersection`，不重证）、`dayCount_bridge`
   （含首尾日计数接 `DayInterval.dayCount`）。`Seams/Temporal.lean` 的 as-of
   截断、期间平移等结论全部作用在 ℤ 日上，经 `toEpochDay` 即可搬运到日期层
   （皇冠定理保证序反射，故搬运不损信息）。
9. **存续区间**（D102）：`ray_trans`（点向传递）与 `interval_in_ray_iff`——
   闭期间整体落在终止日之后 ⟺ 其起点落在终止日之后；终止不清空期间内已发生
   义务的序结构。

## §数学对象

- `CalDate`：`y m d : ℕ` 三元组（结构体，DecidableEq）。
- `daysBeforeYear y = 365·(y−1) + ⌊(y−1)/4⌋ − ⌊(y−1)/100⌋ + ⌊(y−1)/400⌋ : ℤ`（格雷果里
  闰年修正的闭式；年份 ≥ 1 时与 ℕ 版本一致，公式在 ℤ 上做避免 ℕ 截断伤）。
- `toEpochDay a = daysBeforeYear a.y + dayOfYear a.y a.m a.d`（`dayOfYear` 复用 N01）。
- `succDate`/`predDate`：日 ± 1 带完整月末/年末 rollover；`addCalDays n = succDate^[n]`，
  `subCalDays n = predDate^[n]`。
- `clampDay y m d = min d (monthLen y m)`：末日钳制。
- `nextBiz hol fuel d`：带燃料的营业日顺延；`PeriodSpec`/`backSchedule` 如 §法律语义。

## §证与不证

**证**：`monthLen_ge_28`、`monthLen_pos`、`monthTotal_eq_yearLen`、`beforeMonth_succ`、
`beforeMonth_mono_span`、`beforeMonth_mono_le`、`beforeMonth_one`、`dayOfYear_pos`、
`dayOfYear_le_yearLen`、`leap_mod_iff`、`yearLen_bounds`、`daysBeforeYear_succ`、
`daysBeforeYear_step_ge`、`daysBeforeYear_add_ge`、`daysBeforeYear_mono`；
`epoch_le_iff_lex`（皇冠）、`toEpochDay_inj`、`daysDiff_split`、`daysDiff_nonneg_iff_lex`；
`succDate_valid`、`succDate_epoch`、`predDate_valid`、`predDate_epoch`、`pred_succ`、
`addCalDays_valid`、`addCalDays_epoch`、`addCalDays_add`、`addCalDays_comm`、
`subCalDays_epoch`、`sub_add_cancel`；`clampDay_le_self`、`clampDay_le_len`、
`clampDay_idem`、`addCalMonths_valid`、`addCalMonths_zero`、`addCalYears_valid`、
`addCalYears_zero`、`addCalMonths_12_eq_addCalYears_1`、`addCalMonths_1_epoch_ge`、
`addCalMonths_1_wrap_pos`、`addCalYears_epoch_pos`；`nextBiz_spec`、
`nextBiz_displacement_bound`、`nextBiz_fixpoint`、`roll_idempotent`；
`PeriodSpec.baseDeadline_epoch`、`PeriodSpec.baseDeadline_valid`、
`PeriodSpec.deadline_ge_base`、`PeriodSpec.base_strict_order`；`backSchedule_none_iff`、
`backSchedule_some_addBack`；`addDays_bridge`、`contains_bridge`、`dayCount_bridge`、
`dayCount_ge_one_cal`、`cal_intersection_sound`、`cal_disjoint`、`ray_trans`、
`interval_in_ray_iff`；§九 全部闭式数值见证（D095–D103 逐项标注）。

**不证**（不使用 `sorry`/`admit`/`axiom`，也不把下述任何一条说成已证）：
- 不证"任意 n 个月一次性推进历元日至少 28n 天"的跨年一般式：单月无跨（≥28）与
  年末跨月（严格正）已证，多月只给闭式见证，见 §未覆盖片段 1。
- 不证 `fromEpochDay`（历元日 → 日期的全域重建）：倒排经 `predDate` 迭代完成，
  其适用域显式为"不越过历元"，全域重建留给需要它的后续件。
- 不证时区、时刻（时分秒）、农历、节假日表内容本身：节假日表是外部参数
  （合同口径），本件只证"对已选日历规则的变换"。
- 不证金额/利率/舍入（ℚ 层）：那属 B11 demand 合同与 W2-B N01 数量账本；本件
  只供整数天数差与分段结构（"最少必要"边界）。
- 不声称 `TemporalArithmetic.lean` 原有任何定理被本件替代；全部复用不重证。

## §未覆盖片段

1. 多月推进的跨年下界一般式（见 §证与不证）；B11 合同如需，用单月定理迭代或
   逐合同闭式见证补。
2. `fromEpochDay` 全域逆；`toEpochDay` 在合法日期上单（`toEpochDay_inj`）但满射
   重建未构造。
3. 节假日表的良态（如"无连续 7 天节假日"）是使用方假设，不是本件定理；`nextBiz`
   的规格前提已把"窗口内存在营业日"显式化，不满足时只保证返回值在窗口内
   （`nextBiz_displacement_bound`），不保证命中营业日。
4. ISO 字符串日期仍无已证解析桥（与 `Seams/Temporal.lean` §未覆盖 1 同口径）。
5. `PeriodSpec.deadline` 的跨期限单调（顺延可能使相邻期限同日）不成立也
   不证：已证的严格序只在顺延前（`base_strict_order`），顺延后的合并是政策
   事实而非历法错误。

## §档位

定义为 [构造性定义]；全部定理在本件内给出完整证明，零 `sorry`、零 `admit`、
零新增 `axiom`，`decide` 只用于闭式字面量（历元锚点、闰年边界、分段天数等，
全部为无自由变量的地面命题），未使用 `native_decide`，未使用 `Float`，天数差
全 ℤ/ℕ 精确。按仓库边界约定，Lean 权威认定在 CI；本地复编仅为自检，称
provisional。
-/

namespace JurisLean.Seams.UnifiedCalendar

open JurisLean.FullMath.Numeric (leap monthLen validDate beforeMonth dayOfYear)

/-! ## §一 表示与有效性（复用 N01 的历法规则） -/

/-- 中文说明：日历日期——年月日 ℕ 三元组。结构体给出 DecidableEq；字段名 y/m/d。 -/
structure CalDate where
  y : ℕ
  m : ℕ
  d : ℕ
deriving DecidableEq, Repr

/-- 中文说明：日期有效性。月份/日期约束**复用** N01 已钉定的 `validDate`
    （`FullMath/Numeric/Quantities.lean`），本件只加年份下界：历元为公元 1 年，
    公元前不在构造域（诚实边界，见 §未覆盖片段 2）。 -/
def CalDate.Valid (a : CalDate) : Prop := 1 ≤ a.y ∧ validDate a.y a.m a.d

/-- 中文说明：有效性可判定（合取逐层 `infer_instance`；供闭式见证的 `decide`
    消费）。 -/
instance calDateValidDecidable (a : CalDate) : Decidable a.Valid := by
  simp only [CalDate.Valid, validDate]
  infer_instance

/-! ## §二 月份与年份基础 -/

/-- 中文说明：年长——闰年 366 天、平年 365 天（闰年判定复用 N01 的 `leap`）。 -/
def yearLen (y : ℕ) : ℕ := if leap y then 366 else 365

/-- 中文证明：年长夹在 365 与 366 之间（闰/平分岔的两行算术）。 -/
theorem yearLen_bounds (y : ℕ) : (365 : ℤ) ≤ (yearLen y : ℤ) ∧ (yearLen y : ℤ) ≤ 366 := by
  unfold yearLen
  split <;> omega

/-- 中文证明：合法月份的长度至少 28 天（二月下界；大小月表逐格核对，
    二月按闰年分岔）。这是"不把月一律换 30 天"的下界面。 -/
theorem monthLen_ge_28 (y m : ℕ) (h1 : 1 ≤ m) (h2 : m ≤ 12) : 28 ≤ monthLen y m := by
  have hfeb : 28 ≤ monthLen y 2 := by
    unfold monthLen
    by_cases hl : leap y = true
    · rw [if_pos hl]; norm_num
    · rw [if_neg hl]
  match m with
  | 1 => norm_num [monthLen]
  | 2 => exact hfeb
  | 3 => norm_num [monthLen]
  | 4 => norm_num [monthLen]
  | 5 => norm_num [monthLen]
  | 6 => norm_num [monthLen]
  | 7 => norm_num [monthLen]
  | 8 => norm_num [monthLen]
  | 9 => norm_num [monthLen]
  | 10 => norm_num [monthLen]
  | 11 => norm_num [monthLen]
  | 12 => norm_num [monthLen]
  | k + 13 => omega

/-- 中文证明：合法月份长度为正（`monthLen_ge_28` 的直接推论）。 -/
theorem monthLen_pos (y m : ℕ) (h1 : 1 ≤ m) (h2 : m ≤ 12) : 0 < monthLen y m := by
  have := monthLen_ge_28 y m h1 h2
  omega

/-- 中文证明：一月之前无累计天数（`List.range 0 = []`，定义级）。 -/
theorem beforeMonth_one (y : ℕ) : beforeMonth y 1 = 0 := rfl

/-- 中文证明：月末累计的 telescoping——`beforeMonth` 在月 +1 处恰好加上本月长度。
    这是全部月序单调性的引擎。 -/
theorem beforeMonth_succ (y m : ℕ) (h1 : 1 ≤ m) (h2 : m ≤ 11) :
    beforeMonth y (m + 1) = beforeMonth y m + monthLen y m := by
  obtain ⟨n, hn⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  subst hn
  show (((List.range (n + 1)).map (fun k => monthLen y (k + 1)) |>.sum) = ((List.range n).map (fun k => monthLen y (k + 1)) |>.sum) + monthLen y (n + 1))
  rw [List.range_succ, List.map_append, List.sum_append]
  rfl

/-- 中文证明：跨多月的累计单调（严格跨至少一个月）——从 m 起跨 s 个月（s ≥ 1），
    `beforeMonth` 至少吞掉本月长度。 -/
theorem beforeMonth_mono_span (y m : ℕ) (h1 : 1 ≤ m) :
    ∀ s : ℕ, 1 ≤ s → m + s ≤ 12 →
      beforeMonth y m + monthLen y m ≤ beforeMonth y (m + s) := by
  intro s
  induction s with
  | zero => intro hs; omega
  | succ k ih =>
    intro _ h2
    match k with
    | 0 =>
      have hstep := beforeMonth_succ y m h1 (by omega)
      show (beforeMonth y m + monthLen y m ≤ beforeMonth y (m + 1))
      omega
    | k' + 1 =>
      have ihk := ih (by omega) (by omega)
      have hstep := beforeMonth_succ y (m + (k' + 1)) (by omega) (by omega)
      have hnorm : m + (k' + 1) + 1 = m + (k' + 1 + 1) := by omega
      rw [hnorm] at hstep
      omega

/-- 中文证明：累计单调（非严格形）——月号不大则累计不大。 -/
theorem beforeMonth_mono_le (y m m' : ℕ) (h1 : 1 ≤ m) (h2 : m ≤ m') (h3 : m' ≤ 12) :
    beforeMonth y m ≤ beforeMonth y m' := by
  rcases Nat.eq_or_lt_of_le h2 with he | hlt
  · rw [he]
  · have h := beforeMonth_mono_span y m h1 (m' - m) (by omega) (by omega)
    have hadd : m + (m' - m) = m' := by omega
    rw [hadd] at h
    omega

/-- 中文证明：全年月长合计 = 年长（1–11 月累计 + 12 月 31 天；二月按闰年分岔后
    两张数值表闭式核对）。 -/
theorem monthTotal_eq_yearLen (y : ℕ) :
    beforeMonth y 12 + monthLen y 12 = yearLen y := by
  have hr : List.range 11 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] := by rfl
  have hml12 : monthLen y 12 = 31 := rfl
  by_cases hl : leap y = true
  · have hsum : ((List.range 11).map (fun k => monthLen y (k + 1)) |>.sum) = 335 := by
      rw [hr]
      simp [monthLen, hl]
    have hyl : yearLen y = 366 := if_pos hl
    show (((List.range 11).map (fun k => monthLen y (k + 1)) |>.sum) + monthLen y 12 = yearLen y)
    rw [hsum, hyl, hml12]
  · have hsum : ((List.range 11).map (fun k => monthLen y (k + 1)) |>.sum) = 334 := by
      rw [hr]
      simp [monthLen, hl]
    have hyl : yearLen y = 365 := if_neg hl
    show (((List.range 11).map (fun k => monthLen y (k + 1)) |>.sum) + monthLen y 12 = yearLen y)
    rw [hsum, hyl, hml12]

/-- 中文证明：年内日序至少为 1（日 ≥ 1）。 -/
theorem dayOfYear_pos (y m d : ℕ) (hd : 1 ≤ d) : 1 ≤ dayOfYear y m d := by
  show (1 ≤ beforeMonth y m + d)
  omega

/-- 中文证明：合法日期的年内日序不超过年长（月序单调吞掉本月，或 12 月直接
    收口到 `monthTotal_eq_yearLen`）。 -/
theorem dayOfYear_le_yearLen {y m d : ℕ} (hv : validDate y m d) :
    dayOfYear y m d ≤ yearLen y := by
  obtain ⟨hvm1, hvm2, hvd1, hvd2⟩ := hv
  have hmt := monthTotal_eq_yearLen y
  rcases Nat.lt_or_ge m 12 with hmlt | hm12
  · have hmono := beforeMonth_mono_span y m hvm1 1 (by omega) (by omega)
    have hmle := beforeMonth_mono_le y (m + 1) 12 (by omega) (by omega) (by omega)
    show (beforeMonth y m + d ≤ yearLen y)
    omega
  · have hm : m = 12 := by omega
    subst hm
    show (beforeMonth y 12 + d ≤ yearLen y)
    omega

/-! ## §三 历元日、序与等价 -/

/-- 中文说明：年起点之前的历元日数（永恒格雷果里闭式，ℤ 上避免 ℕ 截断；
    约定与 Python `datetime.toordinal` 一致：0001-01-01 的历元日为 1）。 -/
def daysBeforeYear (y : ℕ) : ℤ :=
  365 * ((y : ℤ) - 1) + (((y : ℤ) - 1) / 4) - (((y : ℤ) - 1) / 100)
    + (((y : ℤ) - 1) / 400)

/-- 中文说明：日期 → 历元日（年项 + N01 的年内日序 `dayOfYear`）。 -/
def toEpochDay (a : CalDate) : ℤ :=
  daysBeforeYear a.y + ((dayOfYear a.y a.m a.d : ℕ) : ℤ)

/-- 中文说明：天数差——从 a 到 b 的精确 ℤ 天数（含 b 不含 a 的差计数）。 -/
def daysDiff (a b : CalDate) : ℤ := toEpochDay b - toEpochDay a

/-- 中文证明：闰年判定的模算术形（供 `omega` 消费的等价改写；`4 ∣ y` 等经
    `Nat.dvd_iff_mod_eq_zero` 化为模等式）。 -/
theorem leap_mod_iff (y : ℕ) :
    leap y = true ↔ ((y % 4 = 0 ∧ y % 100 ≠ 0) ∨ y % 400 = 0) := by
  simp [leap, Nat.dvd_iff_mod_eq_zero]

/-- 中文证明：年起点递推——`daysBeforeYear (y+1) = daysBeforeYear y + yearLen y`
    （闰年修正三项分岔后纯线性算术；年份 ≥ 1 保证公式无 ℕ 截断伤）。 -/
theorem daysBeforeYear_succ (y : ℕ) (hy : 1 ≤ y) :
    daysBeforeYear (y + 1) = daysBeforeYear y + (yearLen y : ℤ) := by
  by_cases hl : leap y = true
  · have hmods : ((y % 4 = 0 ∧ y % 100 ≠ 0) ∨ y % 400 = 0) := (leap_mod_iff y).mp hl
    unfold daysBeforeYear yearLen
    rw [if_pos hl]
    push_cast
    rcases hmods with ⟨h4, h100⟩ | h400
    · omega
    · omega
  · have hmods : ¬((y % 4 = 0 ∧ y % 100 ≠ 0) ∨ y % 400 = 0) :=
      fun hc => hl ((leap_mod_iff y).mpr hc)
    push_neg at hmods
    unfold daysBeforeYear yearLen
    rw [if_neg hl]
    push_cast
    by_cases h4 : y % 4 = 0
    · have := hmods.1 h4
      omega
    · omega

/-- 中文证明：单步年增量 ≥ 365（闰年 366）。 -/
theorem daysBeforeYear_step_ge (y : ℕ) (hy : 1 ≤ y) :
    daysBeforeYear y + 365 ≤ daysBeforeYear (y + 1) := by
  have hsucc := daysBeforeYear_succ y hy
  have hb := yearLen_bounds y
  omega

/-- 中文证明：跨 n 年增量下界——首步整年长，其后每年至少 365 天。 -/
theorem daysBeforeYear_add_ge (y n : ℕ) (hy : 1 ≤ y) (hn : 1 ≤ n) :
    daysBeforeYear y + (yearLen y : ℤ) + 365 * ((n : ℤ) - 1) ≤ daysBeforeYear (y + n) := by
  obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  subst hk
  induction k with
  | zero =>
    rw [show (0 : ℕ) + 1 = 1 from by omega]
    have hsucc := daysBeforeYear_succ y hy
    omega
  | succ k ih =>
    have hsucc := daysBeforeYear_succ (y + (k + 1)) (by omega)
    have hb := (yearLen_bounds (y + (k + 1))).1
    rw [show y + (k + 1) + 1 = y + (k + 1 + 1) from by omega] at hsucc
    omega

/-- 中文证明：年起点单调（年大历元日不小）。 -/
theorem daysBeforeYear_mono (y₁ y₂ : ℕ) (hy₁ : 1 ≤ y₁) (h : y₁ ≤ y₂) :
    daysBeforeYear y₁ ≤ daysBeforeYear y₂ := by
  rcases h.eq_or_lt with he | hlt
  · rw [he]
  · have hadd := daysBeforeYear_add_ge y₁ (y₂ - y₁) hy₁ (by omega)
    have hsub : (((y₂ - y₁ : ℕ) : ℤ)) = ((y₂ : ℤ) - (y₁ : ℤ)) := by omega
    have heq : y₁ + (y₂ - y₁) = y₂ := by omega
    rw [heq] at hadd
    have hb := (yearLen_bounds y₁).1
    omega

/-- 中文说明：年月日字典序（"不早于"的lex形，显式 spelled-out 供合同直引）。 -/
def lexLE (a b : CalDate) : Prop :=
  a.y < b.y ∨ (a.y = b.y ∧ (a.m < b.m ∨ (a.m = b.m ∧ a.d ≤ b.d)))

/-- 中文证明：同年后，月小日序严格小（月末天数被本月长度盖住 + 下月累计严格
    超前——有效性前提在此必不可少：31 日只在 31 天月合法）。 -/
theorem dayOfYear_lt_of_ml (y : ℕ) {m₁ m₂ d₁ d₂ : ℕ}
    (hv1 : validDate y m₁ d₁) (hv2 : validDate y m₂ d₂) (h : m₁ < m₂) :
    dayOfYear y m₁ d₁ < dayOfYear y m₂ d₂ := by
  obtain ⟨hm1l, hm1m, hm1d, hm1u⟩ := hv1
  obtain ⟨hm2l, hm2m, hm2d, hm2u⟩ := hv2
  have hmono := beforeMonth_mono_span y m₁ hm1l (m₂ - m₁) (by omega) (by omega)
  have hbm : m₁ + (m₂ - m₁) = m₂ := by omega
  rw [hbm] at hmono
  show (beforeMonth y m₁ + d₁ < beforeMonth y m₂ + d₂)
  omega

/-- 中文证明：**皇冠定理**——历元日序 ⟺ 年月日字典序（合法日期上双向）。
    这是 D096 适用时点 / D100 倒排可行性 / D103 同一参考日的全部日期比较律；
    也是 `Seams/Temporal.lean` 的 ℤ 日结论向日期层无损搬运的反射律。 -/
theorem epoch_le_iff_lex (a b : CalDate) (ha : a.Valid) (hb : b.Valid) :
    toEpochDay a ≤ toEpochDay b ↔ lexLE a b := by
  obtain ⟨y1, m1, d1⟩ := a
  obtain ⟨y2, m2, d2⟩ := b
  simp only [CalDate.Valid, validDate] at ha hb
  obtain ⟨ay1, am1, am2, ad1, ad2⟩ := ha
  obtain ⟨by1, bm1, bm2, bd1, bd2⟩ := hb
  have hdoyA1 : (1 : ℤ) ≤ ((dayOfYear y1 m1 d1 : ℕ) : ℤ) :=
    Nat.cast_le.mpr (dayOfYear_pos y1 m1 d1 ad1)
  have hdoyB1 : (1 : ℤ) ≤ ((dayOfYear y2 m2 d2 : ℕ) : ℤ) :=
    Nat.cast_le.mpr (dayOfYear_pos y2 m2 d2 bd1)
  have hdoyAL : ((dayOfYear y1 m1 d1 : ℕ) : ℤ) ≤ ((yearLen y1 : ℕ) : ℤ) :=
    Nat.cast_le.mpr (dayOfYear_le_yearLen ⟨am1, am2, ad1, ad2⟩)
  have hdoyBL : ((dayOfYear y2 m2 d2 : ℕ) : ℤ) ≤ ((yearLen y2 : ℕ) : ℤ) :=
    Nat.cast_le.mpr (dayOfYear_le_yearLen ⟨bm1, bm2, bd1, bd2⟩)
  rcases lt_trichotomy y1 y2 with hy | hy | hy
  · have hmono := daysBeforeYear_mono (y1 + 1) y2 (by omega) (by omega)
    have hsucc := daysBeforeYear_succ y1 ay1
    constructor
    · intro _
      exact Or.inl hy
    · intro _
      show (daysBeforeYear y1 + ((dayOfYear y1 m1 d1 : ℕ) : ℤ) ≤ daysBeforeYear y2 + ((dayOfYear y2 m2 d2 : ℕ) : ℤ))
      omega
  · subst hy
    constructor
    · intro hle
      have hle' : (daysBeforeYear y1 + ((dayOfYear y1 m1 d1 : ℕ) : ℤ) ≤ daysBeforeYear y1 + ((dayOfYear y1 m2 d2 : ℕ) : ℤ)) := hle
      rw [add_le_add_iff_left, Nat.cast_le] at hle'
      rcases lt_trichotomy m1 m2 with hm | hm | hm
      · exact Or.inr ⟨rfl, Or.inl hm⟩
      · subst hm
        refine Or.inr ⟨rfl, Or.inr ⟨rfl, ?_⟩⟩
        show (d1 ≤ d2)
        have hc1 : beforeMonth y1 m1 + d1 ≤ beforeMonth y1 m1 + d2 := hle'
        omega
      · have hlt := dayOfYear_lt_of_ml y1 ⟨bm1, bm2, bd1, bd2⟩ ⟨am1, am2, ad1, ad2⟩ hm
        have hc1 : beforeMonth y1 m2 + d2 < beforeMonth y1 m1 + d1 := hlt
        have hc2 : beforeMonth y1 m1 + d1 ≤ beforeMonth y1 m2 + d2 := hle'
        omega
    · intro hlex
      rcases hlex with hy' | ⟨hy', hm'⟩
      · have hself : y1 < y1 := hy'
        omega
      · rcases hm' with hm' | ⟨he, hd'⟩
        · show (daysBeforeYear y1 + ((dayOfYear y1 m1 d1 : ℕ) : ℤ) ≤ daysBeforeYear y1 + ((dayOfYear y1 m2 d2 : ℕ) : ℤ))
          rw [add_le_add_iff_left, Nat.cast_le]
          exact (dayOfYear_lt_of_ml y1 ⟨am1, am2, ad1, ad2⟩ ⟨bm1, bm2, bd1, bd2⟩ hm').le
        · subst he
          show (daysBeforeYear y1 + ((dayOfYear y1 m1 d1 : ℕ) : ℤ) ≤ daysBeforeYear y1 + ((dayOfYear y1 m1 d2 : ℕ) : ℤ))
          rw [add_le_add_iff_left, Nat.cast_le]
          have hdy1 : dayOfYear y1 m1 d1 = beforeMonth y1 m1 + d1 := rfl
          have hdy2 : dayOfYear y1 m1 d2 = beforeMonth y1 m1 + d2 := rfl
          have hdd : d1 ≤ d2 := hd'
          omega
  · have hmono := daysBeforeYear_mono (y2 + 1) y1 (by omega) (by omega)
    have hsucc := daysBeforeYear_succ y2 by1
    constructor
    · intro hle
      have hle' : (daysBeforeYear y1 + ((dayOfYear y1 m1 d1 : ℕ) : ℤ) ≤ daysBeforeYear y2 + ((dayOfYear y2 m2 d2 : ℕ) : ℤ)) := hle
      omega
    · intro hlex
      rcases hlex with h' | ⟨he, _⟩
      · have hy12 : y1 < y2 := h'
        omega
      · have hye : y1 = y2 := he
        omega

/-- 中文证明：等价——同历元日的两个合法日期是同一日期（皇冠定理两向 + 字段
    反推）。D103"同一参考日"的等价判据。 -/
theorem toEpochDay_inj (a b : CalDate) (ha : a.Valid) (hb : b.Valid)
    (h : toEpochDay a = toEpochDay b) : a = b := by
  have h1 := (epoch_le_iff_lex a b ha hb).mp h.le
  have h2 := (epoch_le_iff_lex b a hb ha).mp h.ge
  obtain ⟨y1, m1, d1⟩ := a
  obtain ⟨y2, m2, d2⟩ := b
  simp only [CalDate.mk.injEq, lexLE] at h1 h2 ⊢
  rcases h1 with hy1 | hy1
  · rcases h2 with hy2 | hy2
    · omega
    · obtain ⟨he2, _⟩ := hy2
      omega
  · obtain ⟨he1, hm1⟩ := hy1
    rcases h2 with hy2 | hy2
    · omega
    · obtain ⟨he2, hm2⟩ := hy2
      rcases hm1 with hm1' | hm1'
      · rcases hm2 with hm2' | hm2'
        · omega
        · obtain ⟨he3, _⟩ := hm2'
          omega
      · obtain ⟨he3, hd3⟩ := hm1'
        rcases hm2 with hm2' | hm2'
        · omega
        · obtain ⟨he4, hd4⟩ := hm2'
          omega

/-- 中文证明：天数差非负 ⟺ 字典序（`daysDiff` 的适用判据）。 -/
theorem daysDiff_nonneg_iff_lex (a b : CalDate) (ha : a.Valid) (hb : b.Valid) :
    0 ≤ daysDiff a b ↔ lexLE a b := by
  rw [daysDiff, sub_nonneg]
  exact epoch_le_iff_lex a b ha hb

/-- 中文证明：**分段计息内核**——期间在中点切开，两天数差相加等于整段
    天数差（D095"独立基数、期间"组合规则的 ℤ 精确算术面）。 -/
theorem daysDiff_split (a m b : CalDate) :
    daysDiff a m + daysDiff m b = daysDiff a b := by
  unfold daysDiff
  ring

/-! ## §四 后继/前驱与日加法 -/

/-- 中文说明：后继日期——非月末则日 +1；月末则跳下月 1 日；年末跳下年 1 月
    1 日（完整 rollover，纯字段式便于 `split_ifs`）。 -/
def succDate (a : CalDate) : CalDate :=
  if a.d < monthLen a.y a.m then ⟨a.y, a.m, a.d + 1⟩
  else if a.m < 12 then ⟨a.y, a.m + 1, 1⟩
  else ⟨a.y + 1, 1, 1⟩

/-- 中文说明：前驱日期——非月初则日 −1；月初则退回上月末（取上月长度）；
    年初退回上年 12 月 31 日。 -/
def predDate (a : CalDate) : CalDate :=
  if 1 < a.d then ⟨a.y, a.m, a.d - 1⟩
  else if 1 < a.m then ⟨a.y, a.m - 1, monthLen a.y (a.m - 1)⟩
  else ⟨a.y - 1, 12, 31⟩

/-- 中文证明：后继保持有效性（跨月/跨年分支的月长下界由 `monthLen_ge_28` 供）。 -/
theorem succDate_valid (a : CalDate) (ha : a.Valid) : (succDate a).Valid := by
  obtain ⟨y, m, d⟩ := a
  have hva : (1 ≤ y ∧ validDate y m d) := ha
  obtain ⟨hy, hm1, hm2, hd1, hd2⟩ := hva
  show (CalDate.Valid (if d < monthLen y m then ⟨y, m, d + 1⟩ else if m < 12 then ⟨y, m + 1, 1⟩ else ⟨y + 1, 1, 1⟩))
  split_ifs with h1 h2
  · show (1 ≤ y ∧ (1 ≤ m ∧ m ≤ 12 ∧ 1 ≤ d + 1 ∧ d + 1 ≤ monthLen y m))
    omega
  · have h28 := monthLen_ge_28 y (m + 1) (by omega) (by omega)
    show (1 ≤ y ∧ (1 ≤ m + 1 ∧ m + 1 ≤ 12 ∧ 1 ≤ 1 ∧ 1 ≤ monthLen y (m + 1)))
    omega
  · have h31 : monthLen (y + 1) 1 = 31 := rfl
    show (1 ≤ y + 1 ∧ (1 ≤ 1 ∧ 1 ≤ 12 ∧ 1 ≤ 1 ∧ 1 ≤ monthLen (y + 1) 1))
    omega

/-- 中文证明：后继历元日恰 +1（三分支：日内 +1 由 `dayOfYear` 线性；月末跨月由
    `beforeMonth_succ` telescoping；年末跨年由 `monthTotal_eq_yearLen` +
    `daysBeforeYear_succ` 收口）。 -/
theorem succDate_epoch (a : CalDate) (ha : a.Valid) :
    toEpochDay (succDate a) = toEpochDay a + 1 := by
  obtain ⟨y, m, d⟩ := a
  have hva : (1 ≤ y ∧ validDate y m d) := ha
  obtain ⟨hy, hm1, hm2, hd1, hd2⟩ := hva
  show (toEpochDay (if d < monthLen y m then ⟨y, m, d + 1⟩ else if m < 12 then ⟨y, m + 1, 1⟩ else ⟨y + 1, 1, 1⟩) = toEpochDay ⟨y, m, d⟩ + 1)
  split_ifs with h1 h2
  · show (daysBeforeYear y + ((beforeMonth y m + (d + 1) : ℕ) : ℤ) = daysBeforeYear y + ((beforeMonth y m + d : ℕ) : ℤ) + 1)
    omega
  · have hstep := beforeMonth_succ y m (by omega) (by omega)
    show (daysBeforeYear y + ((beforeMonth y (m + 1) + 1 : ℕ) : ℤ) = daysBeforeYear y + ((beforeMonth y m + d : ℕ) : ℤ) + 1)
    omega
  · have hm12 : m = 12 := by omega
    subst hm12
    have hmt := monthTotal_eq_yearLen y
    have hdb := daysBeforeYear_succ y hy
    have hb1 : beforeMonth (y + 1) 1 = 0 := rfl
    have hdeq : monthLen y 12 = d := by omega
    show (daysBeforeYear (y + 1) + ((beforeMonth (y + 1) 1 + 1 : ℕ) : ℤ) = daysBeforeYear y + ((beforeMonth y 12 + d : ℕ) : ℤ) + 1)
    omega

/-- 中文证明：前驱保持有效性（前提：非历元起点 0001-01-01；年初分支需要年 ≥ 2，
    其余分支月长下界由 `monthLen_ge_28` 供）。 -/
theorem predDate_valid (a : CalDate) (ha : a.Valid) (hne : a ≠ ⟨1, 1, 1⟩) :
    (predDate a).Valid := by
  obtain ⟨y, m, d⟩ := a
  have hva : (1 ≤ y ∧ validDate y m d) := ha
  obtain ⟨hy, hm1, hm2, hd1, hd2⟩ := hva
  show (CalDate.Valid (if 1 < d then ⟨y, m, d - 1⟩ else if 1 < m then ⟨y, m - 1, monthLen y (m - 1)⟩ else ⟨y - 1, 12, 31⟩))
  split_ifs with h1 h2
  · show (1 ≤ y ∧ (1 ≤ m ∧ m ≤ 12 ∧ 1 ≤ d - 1 ∧ d - 1 ≤ monthLen y m))
    omega
  · have h28 := monthLen_ge_28 y (m - 1) (by omega) (by omega)
    show (1 ≤ y ∧ (1 ≤ m - 1 ∧ m - 1 ≤ 12 ∧ 1 ≤ monthLen y (m - 1) ∧ monthLen y (m - 1) ≤ monthLen y (m - 1)))
    omega
  · have hy2 : 2 ≤ y := by
      by_contra hcon
      simp only [not_le] at hcon
      exact hne (by
        show ((⟨y, m, d⟩ : CalDate) = ⟨1, 1, 1⟩)
        simp only [CalDate.mk.injEq]
        omega)
    show (1 ≤ y - 1 ∧ (1 ≤ 12 ∧ 12 ≤ 12 ∧ 1 ≤ 31 ∧ 31 ≤ monthLen (y - 1) 12))
    have h31 : monthLen (y - 1) 12 = 31 := rfl
    omega

/-- 中文证明：前驱历元日恰 −1（三分支对偶：日内 −1；月初退月由 telescoping；
    年初退年由年递推 + `beforeMonth 1 = 0` 收口）。 -/
theorem predDate_epoch (a : CalDate) (ha : a.Valid) :
    toEpochDay (predDate a) = toEpochDay a - 1 := by
  obtain ⟨y, m, d⟩ := a
  have hva : (1 ≤ y ∧ validDate y m d) := ha
  obtain ⟨hy, hm1, hm2, hd1, hd2⟩ := hva
  show (toEpochDay (if 1 < d then ⟨y, m, d - 1⟩ else if 1 < m then ⟨y, m - 1, monthLen y (m - 1)⟩ else ⟨y - 1, 12, 31⟩) = toEpochDay ⟨y, m, d⟩ - 1)
  split_ifs with h1 h2
  · show (daysBeforeYear y + ((beforeMonth y m + (d - 1) : ℕ) : ℤ) = daysBeforeYear y + ((beforeMonth y m + d : ℕ) : ℤ) - 1)
    omega
  · have hstep := beforeMonth_succ y (m - 1) (by omega) (by omega)
    rw [show (m - 1) + 1 = m from by omega] at hstep
    show (daysBeforeYear y + ((beforeMonth y (m - 1) + monthLen y (m - 1) : ℕ) : ℤ) = daysBeforeYear y + ((beforeMonth y m + d : ℕ) : ℤ) - 1)
    omega
  · have hm1e : m = 1 := by omega
    have hd1e : d = 1 := by omega
    subst hm1e
    subst hd1e
    rcases Nat.lt_or_ge y 2 with hy1 | hy2
    · have hye : y = 1 := by omega
      subst hye
      rfl
    · have hmt := monthTotal_eq_yearLen (y - 1)
      have hdb := daysBeforeYear_succ (y - 1) (by omega)
      rw [show (y - 1) + 1 = y from by omega] at hdb
      have hb0 : beforeMonth y 1 = 0 := rfl
      have hml : monthLen (y - 1) 12 = 31 := rfl
      show (daysBeforeYear (y - 1) + ((beforeMonth (y - 1) 12 + 31 : ℕ) : ℤ) = daysBeforeYear y + ((beforeMonth y 1 + 1 : ℕ) : ℤ) - 1)
      omega

/-- 中文证明：前驱∘后继 = 恒等（三分支：日内往返、月末→月初→月末、年末→年初
    →年末；月末分支的日恢复用"月末即月长"）。 -/
theorem pred_succ (a : CalDate) (ha : a.Valid) : predDate (succDate a) = a := by
  obtain ⟨y, m, d⟩ := a
  have hva : (1 ≤ y ∧ validDate y m d) := ha
  obtain ⟨hy, hm1, hm2, hd1, hd2⟩ := hva
  show (predDate (if d < monthLen y m then ⟨y, m, d + 1⟩ else if m < 12 then ⟨y, m + 1, 1⟩ else ⟨y + 1, 1, 1⟩) = ⟨y, m, d⟩)
  by_cases h1 : d < monthLen y m
  · rw [if_pos h1]
    show (predDate ⟨y, m, d + 1⟩ = ⟨y, m, d⟩)
    show (((if 1 < d + 1 then ⟨y, m, d + 1 - 1⟩ else if 1 < m then ⟨y, m - 1, monthLen y (m - 1)⟩ else ⟨y - 1, 12, 31⟩) : CalDate) = ⟨y, m, d⟩)
    rw [if_pos (by omega : 1 < d + 1)]
    rfl
  · rw [if_neg h1]
    by_cases h2 : m < 12
    · rw [if_pos h2]
      show (predDate ⟨y, m + 1, 1⟩ = ⟨y, m, d⟩)
      show (((if 1 < 1 then ⟨y, m + 1, 1 - 1⟩ else if 1 < m + 1 then ⟨y, m + 1 - 1, monthLen y (m + 1 - 1)⟩ else ⟨y - 1, 12, 31⟩) : CalDate) = ⟨y, m, d⟩)
      rw [if_neg (by omega : ¬ 1 < (1 : ℕ)), if_pos (by omega : 1 < m + 1)]
      rw [show m + 1 - 1 = m from by omega]
      have hdeq : monthLen y m = d := by omega
      rw [hdeq]
    · rw [if_neg h2]
      show (predDate ⟨y + 1, 1, 1⟩ = ⟨y, m, d⟩)
      show (((if 1 < 1 then ⟨y + 1, 1, 1 - 1⟩ else if 1 < 1 then ⟨y + 1, 1 - 1, monthLen y (1 - 1)⟩ else ⟨y + 1 - 1, 12, 31⟩) : CalDate) = ⟨y, m, d⟩)
      rw [if_neg (by omega : ¬ 1 < (1 : ℕ)), if_neg (by omega : ¬ 1 < (1 : ℕ))]
      have hm12 : m = 12 := by omega
      subst hm12
      have hml : monthLen y 12 = 31 := rfl
      rw [hml] at hd2
      have h31 : d = 31 := by omega
      rw [show y + 1 - 1 = y from by omega]
      rw [h31]

/-- 中文说明：日加法——后继的 n 次迭代（结构对齐 Lean 定义，无浮点无近似）。 -/
def addCalDays (n : ℕ) (a : CalDate) : CalDate := succDate^[n] a

/-- 中文说明：日减法——前驱的 n 次迭代（倒排 D100 的构造件）。 -/
def subCalDays (n : ℕ) (a : CalDate) : CalDate := predDate^[n] a

/-- 中文证明：迭代一步的改写（`Function.iterate_succ_apply` 直引，供归纳）。 -/
theorem addCalDays_succ_eq (n : ℕ) (a : CalDate) :
    addCalDays (n + 1) a = succDate (addCalDays n a) :=
  Function.iterate_succ_apply' succDate n a

/-- 中文证明：日加法保持有效性（归纳 + `succDate_valid`）。 -/
theorem addCalDays_valid (a : CalDate) (ha : a.Valid) (n : ℕ) :
    (addCalDays n a).Valid := by
  induction n with
  | zero => exact ha
  | succ k ih =>
    rw [addCalDays_succ_eq]
    exact succDate_valid _ ih

/-- 中文证明：日加法历元日严格对齐 `+n`（归纳 + `succDate_epoch`；这是
    YMD 日加法与既有 ℤ 日加法一致性的核心）。 -/
theorem addCalDays_epoch (a : CalDate) (ha : a.Valid) (n : ℕ) :
    toEpochDay (addCalDays n a) = toEpochDay a + n := by
  induction n with
  | zero =>
    show (toEpochDay a = toEpochDay a + ((0 : ℕ) : ℤ))
    omega
  | succ k ih =>
    have hv := addCalDays_valid a ha k
    rw [addCalDays_succ_eq, succDate_epoch _ hv, ih]
    omega

/-- 中文证明：**加法结合形**——`(n + k) 天 = n 天后 k 天`（纯迭代代数，
    全域无条件成立）。 -/
theorem addCalDays_add (n k : ℕ) (a : CalDate) :
    addCalDays (n + k) a = addCalDays n (addCalDays k a) :=
  Function.iterate_add_apply succDate n k a

/-- 中文证明：**加法交换**——日加法两个方向叠加可换（结合形 + `Nat.add_comm`）。
    适用域：全域（无需有效性前提）。 -/
theorem addCalDays_comm (n k : ℕ) (a : CalDate) :
    addCalDays n (addCalDays k a) = addCalDays k (addCalDays n a) := by
  rw [← addCalDays_add, ← addCalDays_add, Nat.add_comm]

/-- 中文证明：日减法的有效性 + 历元日对齐（归纳；适用域=倒排不越过历元：
    `n + 1 ≤ toEpochDay a` 保证每步前驱都不在历元起点上，前驱保持有效性
    的前提由此维持）。 -/
theorem subCalDays_epoch (a : CalDate) (ha : a.Valid) :
    ∀ n : ℕ, (n : ℤ) + 1 ≤ toEpochDay a →
      (subCalDays n a).Valid ∧ toEpochDay (subCalDays n a) = toEpochDay a - n := by
  intro n
  induction n with
  | zero =>
    intro _
    exact ⟨ha, by
      show (toEpochDay a = toEpochDay a - ((0 : ℕ) : ℤ))
      omega⟩
  | succ k ih =>
    intro h
    have ih' := ih (by omega)
    obtain ⟨hv, he⟩ := ih'
    have horig : toEpochDay (⟨1, 1, 1⟩ : CalDate) = 1 := rfl
    have hne : subCalDays k a ≠ ⟨1, 1, 1⟩ := by
      intro heq
      rw [heq, horig] at he
      omega
    rw [show subCalDays (k + 1) a = predDate (subCalDays k a) from
      Function.iterate_succ_apply' predDate k a]
    refine ⟨predDate_valid _ hv hne, ?_⟩
    rw [predDate_epoch _ hv, he]
    omega

/-- 中文证明：**倒排往返**——可行域内"先退 n 天再进 n 天"回到原日期
    （历元日相等 + 单射；D100 倒排计划可执行性的构造保证）。 -/
theorem sub_add_cancel (a : CalDate) (ha : a.Valid) (n : ℕ)
    (h : (n : ℤ) + 1 ≤ toEpochDay a) :
    addCalDays n (subCalDays n a) = a := by
  obtain ⟨hv, he⟩ := subCalDays_epoch a ha n h
  exact toEpochDay_inj _ _ (addCalDays_valid _ hv n) ha (by
    rw [addCalDays_epoch _ hv n, he]
    omega)

/-! ## §五 月/年加法与月末钳制 -/

/-- 中文说明：末日钳制——目标月放不下的日压到目标月末（银行业标准；合同
    未指定规则，此选择在施工报告披露）。 -/
def clampDay (y m d : ℕ) : ℕ := min d (monthLen y m)

/-- 中文说明：月加法（一次性，非逐月迭代——法律期间"n 个月后"按同日或月末
    一次取定，先迭代后取会得不同结果，见 `addCalMonths_12_eq_addCalYears_1` 与
    §法律语义 5）。 -/
def addCalMonths (n : ℕ) (a : CalDate) : CalDate :=
  ⟨a.y + ((a.m - 1) + n) / 12, ((a.m - 1) + n) % 12 + 1,
    clampDay (a.y + ((a.m - 1) + n) / 12) (((a.m - 1) + n) % 12 + 1) a.d⟩

/-- 中文说明：年加法（同月同日，末日钳制处理 2 月 29 → 平年 2 月 28）。 -/
def addCalYears (n : ℕ) (a : CalDate) : CalDate :=
  ⟨a.y + n, a.m, clampDay (a.y + n) a.m a.d⟩

/-- 中文证明：钳制不超过原日。 -/
theorem clampDay_le_self (y m d : ℕ) : clampDay y m d ≤ d := min_le_left _ _

/-- 中文证明：钳制不超过目标月末（钳后日期合法性的日上界来源）。 -/
theorem clampDay_le_len (y m d : ℕ) : clampDay y m d ≤ monthLen y m := min_le_right _ _

/-- 中文证明：**钳制幂等**——钳两次等于钳一次（`min` 的吸收律；D095 组合规则
    里"月末规则作用于已月末化的日"不再移动）。 -/
theorem clampDay_idem (y m d : ℕ) :
    clampDay y m (clampDay y m d) = clampDay y m d := by
  simp [clampDay, min_assoc, min_idem]

/-- 中文证明：月加法保持有效性（月号由 mod 12 落在 1–12；日号下界取
    `min` 两侧的 1 与 28，上界由钳制）。 -/
theorem addCalMonths_valid (a : CalDate) (ha : a.Valid) (n : ℕ) :
    (addCalMonths n a).Valid := by
  obtain ⟨y, m, d⟩ := a
  have hva : (1 ≤ y ∧ validDate y m d) := ha
  obtain ⟨hy, hm1, hm2, hd1, hd2⟩ := hva
  have hmod1 : 1 ≤ ((m - 1) + n) % 12 + 1 := by omega
  have hmod2 : ((m - 1) + n) % 12 + 1 ≤ 12 := by omega
  have h28 := monthLen_ge_28 (y + ((m - 1) + n) / 12)
    (((m - 1) + n) % 12 + 1) hmod1 hmod2
  have hmin : 1 ≤ min d
      (monthLen (y + ((m - 1) + n) / 12) (((m - 1) + n) % 12 + 1)) :=
    le_min_iff.mpr ⟨hd1, by omega⟩
  show (1 ≤ y + ((m - 1) + n) / 12 ∧ (1 ≤ ((m - 1) + n) % 12 + 1 ∧ ((m - 1) + n) % 12 + 1 ≤ 12 ∧ 1 ≤ min d (monthLen (y + ((m - 1) + n) / 12) (((m - 1) + n) % 12 + 1)) ∧ min d (monthLen (y + ((m - 1) + n) / 12) (((m - 1) + n) % 12 + 1)) ≤ monthLen (y + ((m - 1) + n) / 12) (((m - 1) + n) % 12 + 1)))
  omega

/-- 中文证明：零个月 = 恒等（合法日期的日 ≤ 月长，钳制不触发）。 -/
theorem addCalMonths_zero (a : CalDate) (ha : a.Valid) : addCalMonths 0 a = a := by
  obtain ⟨y, m, d⟩ := a
  have hva : (1 ≤ y ∧ validDate y m d) := ha
  obtain ⟨hy, hm1, hm2, hd1, hd2⟩ := hva
  have h1 : (m - 1) / 12 = 0 := by omega
  have h2 : (m - 1) % 12 = m - 1 := by omega
  have h3 : m - 1 + 1 = m := by omega
  show ((⟨y + (m - 1 + 0) / 12, (m - 1 + 0) % 12 + 1, min d (monthLen (y + (m - 1 + 0) / 12) ((m - 1 + 0) % 12 + 1))⟩ : CalDate) = ⟨y, m, d⟩)
  simp only [Nat.add_zero, h1, h2, h3, min_eq_left hd2]

/-- 中文证明：年加法保持有效性。 -/
theorem addCalYears_valid (a : CalDate) (ha : a.Valid) (n : ℕ) :
    (addCalYears n a).Valid := by
  obtain ⟨y, m, d⟩ := a
  have hva : (1 ≤ y ∧ validDate y m d) := ha
  obtain ⟨hy, hm1, hm2, hd1, hd2⟩ := hva
  have h28 := monthLen_ge_28 (y + n) m hm1 hm2
  have hmin : 1 ≤ min d (monthLen (y + n) m) := le_min_iff.mpr ⟨hd1, by omega⟩
  show (1 ≤ y + n ∧ (1 ≤ m ∧ m ≤ 12 ∧ 1 ≤ min d (monthLen (y + n) m) ∧ min d (monthLen (y + n) m) ≤ monthLen (y + n) m))
  omega

/-- 中文证明：零年 = 恒等。 -/
theorem addCalYears_zero (a : CalDate) (ha : a.Valid) : addCalYears 0 a = a := by
  obtain ⟨y, m, d⟩ := a
  have hva : (1 ≤ y ∧ validDate y m d) := ha
  obtain ⟨hy, hm1, hm2, hd1, hd2⟩ := hva
  show ((⟨y + 0, m, min d (monthLen (y + 0) m)⟩ : CalDate) = ⟨y, m, d⟩)
  simp only [Nat.add_zero, min_eq_left hd2]

/-- 中文证明：12 个月 = 1 年（一次性语义与年加法一致——跨年 carry 恰为 1）。 -/
theorem addCalMonths_12_eq_addCalYears_1 (a : CalDate) (ha : a.Valid) :
    addCalMonths 12 a = addCalYears 1 a := by
  obtain ⟨y, m, d⟩ := a
  have hva : (1 ≤ y ∧ validDate y m d) := ha
  obtain ⟨hy, hm1, hm2, hd1, hd2⟩ := hva
  have h1 : (m - 1 + 12) / 12 = 1 := by omega
  have h2 : (m - 1 + 12) % 12 = m - 1 := by omega
  have h3 : m - 1 + 1 = m := by omega
  show ((⟨y + (m - 1 + 12) / 12, (m - 1 + 12) % 12 + 1, min d (monthLen (y + (m - 1 + 12) / 12) ((m - 1 + 12) % 12 + 1))⟩ : CalDate) = ⟨y + 1, m, min d (monthLen (y + 1) m)⟩)
  simp only [h1, h2, h3]

/-- 中文证明：**单月推进至少 28 天**——"不把月一律换 30 天"的可证形式：
    无钳制时整月长度（≥ 28）入账；钳制时目标月末（≥ 28）加上跨过的整月，
    由源日 ≤ 源月长收口。 -/
theorem addCalMonths_1_epoch_ge (a : CalDate) (ha : a.Valid) (hm : a.m ≤ 11) :
    toEpochDay a + 28 ≤ toEpochDay (addCalMonths 1 a) := by
  obtain ⟨y, m, d⟩ := a
  have hva : (1 ≤ y ∧ validDate y m d) := ha
  obtain ⟨hy, hm1, hm2, hd1, hd2⟩ := hva
  have hmle : m ≤ 11 := hm
  have h28 := monthLen_ge_28 y m hm1 (by omega)
  have h28' := monthLen_ge_28 y (m + 1) (by omega) (by omega)
  have hstep := beforeMonth_succ y m hm1 hmle
  have e1 : (m - 1 + 1) / 12 = 0 := by omega
  have e2 : (m - 1 + 1) % 12 = m := by omega
  show (toEpochDay ⟨y, m, d⟩ + 28 ≤ toEpochDay (addCalMonths 1 ⟨y, m, d⟩))
  simp only [addCalMonths, clampDay, e1, e2, Nat.add_zero]
  rcases le_total d (monthLen y (m + 1)) with hcase | hcase
  · rw [min_eq_left hcase]
    show (daysBeforeYear y + ((beforeMonth y m + d : ℕ) : ℤ) + 28 ≤ daysBeforeYear y + ((beforeMonth y (m + 1) + d : ℕ) : ℤ))
    omega
  · rw [min_eq_right hcase]
    show (daysBeforeYear y + ((beforeMonth y m + d : ℕ) : ℤ) + 28 ≤ daysBeforeYear y + ((beforeMonth y (m + 1) + monthLen y (m + 1) : ℕ) : ℤ))
    omega

/-- 中文证明：年末跨月（12 月 + 1 月 → 次年 1 月）历元日严格前进
    （`yearLen = beforeMonth 12 + 31` 收口；31 天恒正）。 -/
theorem addCalMonths_1_wrap_pos (a : CalDate) (ha : a.Valid) (hm : a.m = 12) :
    toEpochDay a < toEpochDay (addCalMonths 1 a) := by
  obtain ⟨y, m, d⟩ := a
  have hva : (1 ≤ y ∧ validDate y m d) := ha
  obtain ⟨hy, hm1, hm2, hd1, hd2⟩ := hva
  have hmw : m = 12 := hm
  have hmt := monthTotal_eq_yearLen y
  have hdb := daysBeforeYear_succ y hy
  have hb1 : beforeMonth (y + 1) 1 = 0 := rfl
  have hml12 : monthLen y 12 = 31 := rfl
  have hml1 : monthLen (y + 1) 1 = 31 := rfl
  have e1 : (12 - 1 + 1) / 12 = 1 := by omega
  have e2 : (12 - 1 + 1) % 12 = 0 := by omega
  rw [hmw] at hd2 ⊢
  rw [hml12] at hd2 hmt
  show (toEpochDay ⟨y, 12, d⟩ < toEpochDay (addCalMonths 1 ⟨y, 12, d⟩))
  simp only [addCalMonths, clampDay, e1, e2, Nat.add_zero, Nat.zero_add]
  rw [hml1, min_eq_left hd2]
  show (daysBeforeYear y + ((beforeMonth y 12 + d : ℕ) : ℤ) < daysBeforeYear (y + 1) + ((beforeMonth (y + 1) 1 + d : ℕ) : ℤ))
  omega

/-- 中文证明：年加法（≥ 1 年）历元日严格前进——跨年增量 ≥ 首年整年长，
    新日序 ≥ 1、旧日序 ≤ 旧年长，闰/平分岔后收口为严格正。 -/
theorem addCalYears_epoch_pos (a : CalDate) (ha : a.Valid) (n : ℕ) (hn : 1 ≤ n) :
    toEpochDay a < toEpochDay (addCalYears n a) := by
  obtain ⟨y, m, d⟩ := a
  have hva : (1 ≤ y ∧ validDate y m d) := ha
  obtain ⟨hy, hm1, hm2, hd1, hd2⟩ := hva
  have hadd := daysBeforeYear_add_ge y n hy
  have hdoyLa : ((dayOfYear y m d : ℕ) : ℤ) ≤ ((yearLen y : ℕ) : ℤ) :=
    Nat.cast_le.mpr (dayOfYear_le_yearLen ⟨hm1, hm2, hd1, hd2⟩)
  have h28 := monthLen_ge_28 (y + n) m hm1 hm2
  have hmin : (1 : ℕ) ≤ min d (monthLen (y + n) m) := le_min_iff.mpr ⟨hd1, by omega⟩
  have hdoy1 : (1 : ℤ) ≤ ((dayOfYear (y + n) m (min d (monthLen (y + n) m)) : ℕ) : ℤ) :=
    Nat.cast_le.mpr (dayOfYear_pos _ _ _ hmin)
  show (daysBeforeYear y + ((dayOfYear y m d : ℕ) : ℤ) < daysBeforeYear (y + n) + ((dayOfYear (y + n) m (min d (monthLen (y + n) m)) : ℕ) : ℤ))
  have hdy : dayOfYear (y + n) m (min d (monthLen (y + n) m))
      = beforeMonth (y + n) m + min d (monthLen (y + n) m) := rfl
  have hdy2 : dayOfYear y m d = beforeMonth y m + d := rfl
  omega

/-! ## §六 营业日滚动（表驱动节假日＝外部参数） -/

/-- 中文说明：带燃料的营业日顺延——从 d 起逐日找 `hol` 为 false 的第一个日子，
    `fuel` 界搜索半径（表驱动节假日是**外部参数**，合同口径）。 -/
def nextBiz (hol : ℤ → Bool) : ℕ → ℤ → ℤ
  | 0, d => d
  | fuel + 1, d => if hol d = true then nextBiz hol fuel (d + 1) else d

/-- 中文证明：**顺延规格**——窗口内存在营业日（显式前提）⇒ 顺延结果命中营业日、
    不早于起点、不超出燃料窗。前提不满足时本定理不作任何承诺（fail-closed 的
    诚实形状：不把"表良态"偷换成本件定理）。 -/
theorem nextBiz_spec (hol : ℤ → Bool) :
    ∀ (fuel : ℕ) (d e : ℤ), (∃ k, k ≤ fuel ∧ hol (d + k) = false) →
      hol (nextBiz hol fuel d) = false ∧ d ≤ nextBiz hol fuel d
        ∧ nextBiz hol fuel d ≤ d + fuel := by
  intro fuel
  induction fuel with
  | zero =>
    intro d e ⟨k, hk, hkf⟩
    have hk0 : k = 0 := by omega
    subst hk0
    have hd0 : d + ((0 : ℕ) : ℤ) = d := by omega
    show (hol d = false ∧ d ≤ d ∧ d ≤ d + ((0 : ℕ) : ℤ))
    exact ⟨by rw [← hd0]; exact hkf, le_rfl, by omega⟩
  | succ f ih =>
    intro d e ⟨k, hk, hkf⟩
    by_cases hd : hol d = true
    · have hrec : nextBiz hol (f + 1) d = nextBiz hol f (d + 1) := by
        show ((if hol d = true then nextBiz hol f (d + 1) else d) = nextBiz hol f (d + 1))
        rw [if_pos hd]
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with h0 | h1
        · rw [h0] at hkf
          simp only [Nat.cast_zero, add_zero] at hkf
          rw [hkf] at hd
          exact absurd hd (by simp)
        · exact h1
      have hshift : d + 1 + ((k - 1 : ℕ) : ℤ) = d + ((k : ℕ) : ℤ) := by omega
      have hkf' : hol (d + 1 + ((k - 1 : ℕ) : ℤ)) = false := by
        rw [hshift]
        exact hkf
      obtain ⟨h1, h2, h3⟩ := ih (d + 1) e ⟨k - 1, by omega, hkf'⟩
      rw [hrec]
      exact ⟨h1, by omega, by omega⟩
    · have hfix : nextBiz hol (f + 1) d = d := by
        show ((if hol d = true then nextBiz hol f (d + 1) else d) = d)
        rw [if_neg hd]
      rw [hfix]
      exact ⟨by simp [hd], le_rfl, by omega⟩

/-- 中文证明：位移窗界——无论窗口内是否有营业日，顺延结果都不越过燃料窗
    （无前提版本，供规格前提不满足时的诚实报告用）。 -/
theorem nextBiz_displacement_bound (hol : ℤ → Bool) :
    ∀ (fuel : ℕ) (d : ℤ), d ≤ nextBiz hol fuel d ∧ nextBiz hol fuel d ≤ d + fuel := by
  intro fuel
  induction fuel with
  | zero =>
    intro d
    show (d ≤ d ∧ d ≤ d + ((0 : ℕ) : ℤ))
    exact ⟨le_rfl, by omega⟩
  | succ f ih =>
    intro d
    by_cases hd : hol d = true
    · have hrec : nextBiz hol (f + 1) d = nextBiz hol f (d + 1) := by
        show ((if hol d = true then nextBiz hol f (d + 1) else d) = nextBiz hol f (d + 1))
        rw [if_pos hd]
      obtain ⟨h1, h2⟩ := ih (d + 1)
      rw [hrec]
      exact ⟨by omega, by omega⟩
    · have hfix : nextBiz hol (f + 1) d = d := by
        show ((if hol d = true then nextBiz hol f (d + 1) else d) = d)
        rw [if_neg hd]
      rw [hfix]
      exact ⟨le_rfl, by omega⟩

/-- 中文证明：**顺延不动点**——已是营业日的日子顺延不动。 -/
theorem nextBiz_fixpoint (hol : ℤ → Bool) (fuel : ℕ) (d : ℤ) (h : hol d = false) :
    nextBiz hol fuel d = d := by
  cases fuel with
  | zero => rfl
  | succ f =>
    show ((if hol d = true then nextBiz hol f (d + 1) else d) = d)
    rw [if_neg (by simp [h])]

/-- 中文证明：**顺延幂等**——顺延到营业日后，再顺延任意次不变
    （D099 deadline_effect：非工作日顺延只做一次；第二次调用不移动日期）。 -/
theorem roll_idempotent (hol : ℤ → Bool) (f1 f2 : ℕ) (d : ℤ)
    (h : ∃ k, k ≤ f1 ∧ hol (d + k) = false) :
    nextBiz hol f2 (nextBiz hol f1 d) = nextBiz hol f1 d := by
  obtain ⟨h1, _, _⟩ := nextBiz_spec hol f1 d d h
  exact nextBiz_fixpoint hol f2 _ h1

/-! ## §七 期限规格（D099）与倒排（D100） -/

/-- 中文说明：期限规格——锚点日、长度（天）、节假日表（外部参数）、顺延燃料。
    D099 合同句"不同期限带 anchor、length、calendar、deadline_effect"的载体
    形状；证据状态不在本件（属 B11 合同本体）。 -/
structure PeriodSpec where
  anchor : CalDate
  length : ℕ
  holiday : ℤ → Bool
  rollFuel : ℕ

/-- 中文说明：顺延前基础期限（锚点 + length 天）。 -/
def PeriodSpec.baseDeadline (p : PeriodSpec) : CalDate := addCalDays p.length p.anchor

/-- 中文说明：期限（基础期限经营业日顺延后的 ℤ 历元日）。 -/
def PeriodSpec.deadline (p : PeriodSpec) : ℤ :=
  nextBiz p.holiday p.rollFuel (toEpochDay p.baseDeadline)

/-- 中文证明：基础期限历元日 = 锚点 + 长度（`addCalDays_epoch` 直引）。 -/
theorem PeriodSpec.baseDeadline_epoch (p : PeriodSpec) (ha : p.anchor.Valid) :
    toEpochDay p.baseDeadline = toEpochDay p.anchor + p.length :=
  addCalDays_epoch _ ha _

/-- 中文证明：基础期限保持有效性。 -/
theorem PeriodSpec.baseDeadline_valid (p : PeriodSpec) (ha : p.anchor.Valid) :
    p.baseDeadline.Valid := addCalDays_valid _ ha _

/-- 中文证明：期限命中营业日、不早于基础期限、位移有界（`nextBiz_spec` 直引；
    窗口前提由使用方供——表驱动节假日的良态是外部义务）。 -/
theorem PeriodSpec.deadline_ge_base (p : PeriodSpec)
    (h : ∃ k, k ≤ p.rollFuel ∧ p.holiday (toEpochDay p.baseDeadline + k) = false) :
    p.holiday p.deadline = false ∧ toEpochDay p.baseDeadline ≤ p.deadline
      ∧ p.deadline ≤ toEpochDay p.baseDeadline + p.rollFuel := by
  unfold PeriodSpec.deadline
  exact nextBiz_spec p.holiday p.rollFuel (toEpochDay p.baseDeadline)
    (toEpochDay p.baseDeadline) h

/-- 中文证明：**同锚点期限严格序**——同锚点下更长的期限给出更晚的基础期限
    （顺延前的严格区分；D099 反例"60 日补正期未到，仅因 30 日通知期到便认定
    终止"在此被封死：30 < 60 ⇒ 期限严格更早）。 -/
theorem PeriodSpec.base_strict_order (p q : PeriodSpec)
    (ha : p.anchor.Valid) (hb : q.anchor.Valid) (hanchor : p.anchor = q.anchor)
    (hlt : p.length < q.length) :
    toEpochDay p.baseDeadline < toEpochDay q.baseDeadline := by
  rw [PeriodSpec.baseDeadline_epoch p ha, PeriodSpec.baseDeadline_epoch q hb, hanchor]
  omega

/-- 中文说明：倒排——从期限日回退 lead 天；不可行（越过历元）时报冲突 `none`
    而不是输出计划（D100："不可行时报告冲突"）。 -/
def backSchedule (deadline : CalDate) (lead : ℕ) : Option CalDate :=
  if (lead : ℤ) + 1 ≤ toEpochDay deadline then some (subCalDays lead deadline) else none

/-- 中文证明：**冲突判据**——倒排为空 ⟺ 期限历元日容不下 lead + 1 天
    （fail-closed：冲突被显式报告，不静默夹到边界）。 -/
theorem backSchedule_none_iff (deadline : CalDate) (lead : ℕ) :
    backSchedule deadline lead = none ↔ toEpochDay deadline < (lead : ℤ) + 1 := by
  unfold backSchedule
  by_cases h : (lead : ℤ) + 1 ≤ toEpochDay deadline
  · rw [if_pos h]
    constructor
    · intro hnone
      exact absurd hnone (Option.some_ne_none _)
    · intro hcontra
      exact absurd hcontra (by omega)
  · rw [if_neg h]
    constructor
    · intro _
      omega
    · intro _
      rfl

/-- 中文证明：**倒排可执行**——可行的倒排结果有效，且从它正向加回 lead 天
    恰得原期限（`sub_add_cancel` 直引；D100 倒排计划与正向日程互为印证）。 -/
theorem backSchedule_some_addBack (deadline : CalDate) (lead : ℕ) (a : CalDate)
    (hd : deadline.Valid) (h : backSchedule deadline lead = some a) :
    a.Valid ∧ addCalDays lead a = deadline := by
  unfold backSchedule at h
  by_cases hc : (lead : ℤ) + 1 ≤ toEpochDay deadline
  · rw [if_pos hc] at h
    injection h with ha
    subst ha
    exact ⟨(subCalDays_epoch deadline hd lead hc).1,
      sub_add_cancel deadline hd lead hc⟩
  · rw [if_neg hc] at h
    exact absurd h (by simp)

/-! ## §八 与既有 TemporalArithmetic 的接口（复用不重证） -/

/-- 中文说明：日期闭区间 → 既有 `DayInterval`（`TemporalArithmetic.lean`）的
    嵌入。 -/
def toDayInterval (a b : CalDate) : DayInterval := ⟨toEpochDay a, toEpochDay b⟩

/-- 中文证明：**日加法桥**——既有 `JurisLean.addDays`（ℤ 日计数器）作用在历元日
    上等于本件历法日加法的历元日（两套日加法一致，D099 30/60/90/… 天通知期
    可任一侧计算）。 -/
theorem addDays_bridge (a : CalDate) (n : ℕ) (ha : a.Valid) :
    JurisLean.addDays (toEpochDay a) n = toEpochDay (addCalDays n a) :=
  (addCalDays_epoch a ha n).symm

/-- 中文证明：区间包含桥——历元日下的 `DayInterval.contains` 就是两个历元日
    不等式（定义级）。 -/
theorem contains_bridge (a b x : CalDate) :
    (toDayInterval a b).contains (toEpochDay x) ↔
      (toEpochDay a ≤ toEpochDay x ∧ toEpochDay x ≤ toEpochDay b) := Iff.rfl

/-- 中文证明：日数计数桥——含首尾日计数接既有 `DayInterval.dayCount`
    （D095 按日计息"含头含尾"的天数口径）。 -/
theorem dayCount_bridge (a b : CalDate) :
    DayInterval.dayCount (toDayInterval a b) = Int.toNat (daysDiff a b) + 1 := rfl

/-- 中文证明：日数计数 ≥ 1 的历法形（复用 `DayInterval.dayCount_ge_one`）：
    任何日期闭区间至少含一天。 -/
theorem dayCount_ge_one_cal (a b : CalDate) :
    1 ≤ DayInterval.dayCount (toDayInterval a b) :=
  DayInterval.dayCount_ge_one _

/-- 中文证明：**交集健全复用**——日期区间经嵌入后的交集结果落在两个原区间内
    （直引 `intersection_contained_in_both`，不重证）。 -/
theorem cal_intersection_sound (a b c e : CalDate) (i : DayInterval)
    (h : intervalIntersection (toDayInterval a b) (toDayInterval c e) = some i)
    (x : CalDate) (hx : i.contains (toEpochDay x)) :
    (toDayInterval a b).contains (toEpochDay x)
      ∧ (toDayInterval c e).contains (toEpochDay x) :=
  intersection_contained_in_both _ _ _ h _ hx

/-- 中文证明：**不交复用**——右端点在左起点之前的两个日期区间无交集
    （直引 `disjoint_intervals_no_intersection`）。 -/
theorem cal_disjoint (a b c e : CalDate) (h : toEpochDay b < toEpochDay c) :
    intervalIntersection (toDayInterval a b) (toDayInterval c e) = none :=
  disjoint_intervals_no_intersection _ _ h

/-- 中文证明：**射线传递律**（D102 点向）——终止日不晚于期间起点、期间内
    某日不早于起点 ⇒ 终止日不晚于该日（`Int.le_trans` 直引；历元日序即日期序）。 -/
theorem ray_trans (term a x : CalDate)
    (h1 : toEpochDay term ≤ toEpochDay a) (h2 : toEpochDay a ≤ toEpochDay x) :
    toEpochDay term ≤ toEpochDay x :=
  le_trans h1 h2

/-- 中文证明：**存续射线律**（D102）——闭期间 [a,b] 的每一天都在终止日之后
    ⟺ 期间起点在终止日之后（⟸ 取 x := 起点即得；⟹ 逐点传递）。终止不清空
    期间内已发生义务的序结构，也不让期间起点之前的日期混入。 -/
theorem interval_in_ray_iff (term a b : CalDate) (hab : toEpochDay a ≤ toEpochDay b) :
    toEpochDay term ≤ toEpochDay a ↔
      ∀ x : CalDate, toEpochDay a ≤ toEpochDay x ∧ toEpochDay x ≤ toEpochDay b →
        toEpochDay term ≤ toEpochDay x := by
  constructor
  · intro h x hx
    exact ray_trans term a x h hx.1
  · intro hall
    exact hall a ⟨le_rfl, hab⟩

/-! ## §九 闭式数值见证（D095–D103 逐项标注；全部地面命题） -/

/-- 中文证明：**D095 见证·闰年二月**——2024-02-29 合法、2023-02-29 不合法
    （利息期间跨闰二月与平二月的分岔是真实的，不是 30 天均摊）。 -/
theorem witness_valid_leap_feb :
    CalDate.Valid ⟨2024, 2, 29⟩ ∧ ¬ CalDate.Valid ⟨2023, 2, 29⟩ := by
  constructor
  · decide
  · decide

/-- 中文证明：**历元锚点**——0001-01-01 = 1（约定），1970-01-01 = 719163
    （Unix 纪元），2000-01-01 = 730120（与 Python `datetime.toordinal` 同值，
    Python 侧独立核验）。 -/
theorem witness_epoch_anchors :
    toEpochDay ⟨1, 1, 1⟩ = 1 ∧ toEpochDay ⟨1970, 1, 1⟩ = 719163
      ∧ toEpochDay ⟨2000, 1, 1⟩ = 730120 := by
  decide

/-- 中文证明：**闰年边界年**——2000 闰（400 ∣）、1900 不闰（100 ∣ 400 ∤）、
    2100 不闰、2024 闰（4 ∣ 100 ∤）。 -/
theorem witness_leap_years :
    leap 2000 = true ∧ leap 1900 = false ∧ leap 2100 = false ∧ leap 2024 = true := by
  decide

/-- 中文证明：**D095 见证·跨月利息分段**——期间 2024-01-15 → 2024-03-10 在
    2024-02-01 切开：17 + 38 = 55 天（闰二月入账；`daysDiff_split` 的闭式实例）。 -/
theorem witness_segmentation :
    daysDiff ⟨2024, 1, 15⟩ ⟨2024, 2, 1⟩ = 17
      ∧ daysDiff ⟨2024, 2, 1⟩ ⟨2024, 3, 10⟩ = 38
      ∧ daysDiff ⟨2024, 1, 15⟩ ⟨2024, 3, 10⟩ = 55 := by
  decide

/-- 中文证明：**D095 见证·二月天数差**——闰年 2024-02-01 → 2024-03-01 为 29 天、
    平年 2023 同期为 28 天；含头含尾计数（`DayInterval.dayCount`）对应 29 与 28。 -/
theorem witness_feb_days :
    daysDiff ⟨2024, 2, 1⟩ ⟨2024, 3, 1⟩ = 29 ∧ daysDiff ⟨2023, 2, 1⟩ ⟨2023, 3, 1⟩ = 28
      ∧ DayInterval.dayCount (toDayInterval ⟨2024, 2, 1⟩ ⟨2024, 2, 29⟩) = 29
      ∧ DayInterval.dayCount (toDayInterval ⟨2023, 2, 1⟩ ⟨2023, 2, 28⟩) = 28 := by
  decide

/-- 中文证明：**D095/D103 见证·同一参考日同一口径**——同一年 Q1 闭区间的
    含头含尾天数：2024 年 91 天、2023 年 90 天（同一参考日与同一区间定义给
    出精确差额，不因口径漂移）。 -/
theorem witness_q1_counts :
    DayInterval.dayCount (toDayInterval ⟨2024, 1, 1⟩ ⟨2024, 3, 31⟩) = 91
      ∧ DayInterval.dayCount (toDayInterval ⟨2023, 1, 1⟩ ⟨2023, 3, 31⟩) = 90 := by
  decide

/-- 中文证明：**日加法跨闰/跨年见证**——2024-02-28 + 1 = 2024-02-29（闰）、
    2023-02-28 + 1 = 2023-03-01（平）、2023-12-31 + 1 = 2024-01-01（年末）。 -/
theorem witness_add_days :
    addCalDays 1 ⟨2024, 2, 28⟩ = ⟨2024, 2, 29⟩
      ∧ addCalDays 1 ⟨2023, 2, 28⟩ = ⟨2023, 3, 1⟩
      ∧ addCalDays 1 ⟨2023, 12, 31⟩ = ⟨2024, 1, 1⟩ := by
  decide

/-- 中文证明：**D098 见证·月末钳制与 premium 分账时点**——2024-01-31 + 1 月 =
    2024-02-29、2023-01-31 + 1 月 = 2023-02-28（末日钳制在闰/平年的两种落点）；
    6 个月一次性推进 2024-03-15 → 2024-09-15（同日不钳）。 -/
theorem witness_clamp_months :
    addCalMonths 1 ⟨2024, 1, 31⟩ = ⟨2024, 2, 29⟩
      ∧ addCalMonths 1 ⟨2023, 1, 31⟩ = ⟨2023, 2, 28⟩
      ∧ addCalMonths 6 ⟨2024, 3, 15⟩ = ⟨2024, 9, 15⟩ := by
  decide

/-- 中文证明：**月末不保持的诚实见证**——2 月 29 + 12 个月 = 次年 2 月 28
    （末日钳制下月末锚定不保持：平年 2 月 28 日不是"2 月末对应日"的月末日；
    本条如实展示规则后果，不是缺陷修复对象）。 -/
theorem witness_addCalYears_1_feb29 :
    addCalYears 1 ⟨2024, 2, 29⟩ = ⟨2025, 2, 28⟩
      ∧ addCalMonths 11 ⟨2024, 2, 29⟩ = ⟨2025, 1, 29⟩ := by
  decide

/-- 中文说明：D099 见证用的合成节假日表（双休日模型：历元日 mod 7 ∈ {5,6} 为
    假日；**纯合成材料**，非任何司法辖区真实节假日表）。 -/
def syntheticWeekend (d : ℤ) : Bool := decide (d % 7 = 5 ∨ d % 7 = 6)

/-- 中文证明：**D099 见证·期限区分与顺延幂等**——锚点 2024-05-06（历元
    739012）下 30/60/90/120/180 天基础期限历元日严格递增（739042/739072/
    739102/739132/739192）；双休日表下顺延幂等成立（顺延两次 = 一次）。 -/
theorem witness_d099_periods :
    toEpochDay (addCalDays 30 ⟨2024, 5, 6⟩) = 739042
      ∧ toEpochDay (addCalDays 60 ⟨2024, 5, 6⟩) = 739072
      ∧ toEpochDay (addCalDays 90 ⟨2024, 5, 6⟩) = 739102
      ∧ toEpochDay (addCalDays 120 ⟨2024, 5, 6⟩) = 739132
      ∧ toEpochDay (addCalDays 180 ⟨2024, 5, 6⟩) = 739192
      ∧ nextBiz syntheticWeekend 7 (nextBiz syntheticWeekend 7 739011)
        = nextBiz syntheticWeekend 7 739011 := by
  decide

/-- 中文证明：**D100 见证·倒排可行与冲突报告**——2024-03-31 回退 30 天 =
    2024-03-01（可行）；0001-01-03 回退 10 天 = 冲突（none，因越过历元；
    倒排日期在过去/界外时输出冲突而非静默计划）。 -/
theorem witness_d100_back :
    backSchedule ⟨2024, 3, 31⟩ 30 = some ⟨2024, 3, 1⟩
      ∧ backSchedule ⟨1, 1, 3⟩ 10 = none := by
  decide

/-- 中文证明：**D096/D102 见证·适用时点与存续**——2024-02-29 < 2024-03-01
    （皇冠定理的闭式实例）且终止日 2024-06-30 之后整月期间 [2024-07-01,
    2024-07-31] 的起点与中点都在射线内。 -/
theorem witness_d096_d102 :
    toEpochDay ⟨2024, 2, 29⟩ < toEpochDay ⟨2024, 3, 1⟩
      ∧ toEpochDay ⟨2024, 6, 30⟩ ≤ toEpochDay ⟨2024, 7, 1⟩
      ∧ toEpochDay ⟨2024, 6, 30⟩ ≤ toEpochDay ⟨2024, 7, 15⟩ := by
  decide

end JurisLean.Seams.UnifiedCalendar
