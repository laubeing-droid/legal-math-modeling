import Mathlib.Tactic
import JurisLean.TemporalArithmetic
import JurisLean.TemporalApplicability
import JurisLean.TemporalKripke
import JurisLean.Genealogy.Part3

/-!
XT（横切时间针 / TIME cross-cut）——把仓内四条互不相通的时间载体缝成可证的性质。

## §法律语义

法律推理里的"时间"其实是四件不同的事，仓内过去各写各的：

1. **不得预览未来**（as-of 时点之前能看见什么）。既有 `TemporalApplicability.lean:79`
   `future_information_blocked` 只挡住"一条观察晚于 as-of"这一个动作，管不到"整条
   事件序列里 as-of 之后的部分不参与计算"。本件把后者做成真定理：先构造截断视图
   `trunc`，再证"在 as-of 之后追加或改写事件，视图一字不变"，从而任何从视图算出的
   值也不变（`trunc_view_congr`、`nonanticipation_computed_agrees`）。这才是程序法上
   "裁判时点锁死证据面"的数学形状。
2. **期间保义**（期间平移不改变其意义）。既有 `TemporalArithmetic.lean` 只有端点包含
   与交集良态，没有"平移"这一操作。本件加 `shiftInterval`，证良态性保持
   （`shiftInterval_valid`）、归属关系双向搬运（`shift_contains_iff`），并把交集算子与
   两个"包含"集合的交对齐成一条等值式（`intersection_agrees_with_contains_set`）。
3. **举证时限与迟到证据**（P-049）。仓内此前只有一个 11 对 10 的 `decide` 字面实例
   （`Genealogy/Part3.lean:93-96`），不是规律。本件在原载体
   `Genealogy.Part3.P049.FilingWindow` 上证出量化形式 `evidenceAdmissible_iff` 与
   一般排除方向 `late_without_good_cause_barred_general`，并回收那条字面实例
   （`p049_frozen_witness_recovered`）。
4. **追溯重排**（迟到材料进入已算好的流水线）。仓内**只有前向失效**：
   `FullMath/Burden/SourceTime.lean:89`、`FullMath/Evidence/Provenance.lean:90`、
   `FullMath/Evidence/Withdrawal.lean:144`、`TemporalApplicability.lean:86/93` 全部只
   产出一个"作废"标记，没有任何定理在迟到输入到达后**重算**已算结果。本件补上真正
   缺的算子 `insertLate` 与 `aggregate`，并把法律上真正的分岔证成两侧：可交换聚合下
   迟到无关（`aggregate_add_arrival_insensitive`，重跑是可靠的），非交换聚合下有具体
   反例（`late_insert_changes_noncommutative`），故 `reordering_requires_recomputation`
   成立——旧值不能留，必须重算；而 `invalidation_marker_computes_nothing` 说明"贴标记"
   这一反应形式在结构上改不了任何数值，所以仓内那批前向失效定理**覆盖不了**迟到输入。

## §数学对象

- `trunc asOf evs`：`List (Int × α)` 上"只保留 day ≤ asOf"的截断视图（本件自有算子，
  仓内此前没有任何视图/截断算子）。
- `shiftInterval n i`：把 `DayInterval` 两端同用 `addDays` 平移 `n` 天。
- `insertLate e evs := evs ++ [e]`：迟到材料按到达顺序排在既有序列之后。
- `aggregate op init evs := (evs.map Prod.fst).foldr op init`（写作右折叠）：到达顺序
  即结合顺序；`op` 决定是否可交换。
- `dayToTimePoint`：`Nat` 日计数器 → `LegalIds.lean:72` 的 `TimePoint (Int epochDay)`，
  本件唯一可证的载体转换。
- `ltl_always`（取自 `TemporalKripke.lean:39`）：本件只用它陈述"可达关系不贡献强度"
  （`ltl_always_transition_independent`），不借它的 LTL 名义。
- `IntertemporalLawSignature`：[代拟稿] 法源时间操作签名，见 §档位。

## §证与不证

**证**：`trunc_of_all_future`、`trunc_asOf_append_future_irrelevant`、
`legal_time_nonanticipation`（追加与改写两侧）、`nonanticipation_computed_agrees`、
`trunc_view_congr`、`trunc_sound`；`shiftInterval_valid`、`shift_contains_iff`、
`intersection_some_of_contains_both`、`intersection_agrees_with_contains_set`；
`evidenceAdmissible_iff`、`late_without_good_cause_barred_general`、
`p049_frozen_witness_recovered`；`aggregate_add_arrival_insensitive`、
`late_insert_changes_noncommutative`、`reordering_requires_recomputation`、
`invalidation_marker_computes_nothing`；`epochDay_dayToTimePoint`、
`dayToTimePoint_toNat_round`、`dayToTimePoint_inj`、`addDays_commutes_with_embedding`、
`no_unified_time_carrier_yet`；`ltl_always_of_pointwise`、
`ltl_always_implies_pointwise`、`ltl_always_transition_independent`；
`intertemporal_signature_preserves_effective_day`、
`IntertemporalLawSignature.withRetroFalse_preserves_wellFormed`。

**不证**（不使用 `sorry`/`admit`/`axiom`，也不把下述任何一条说成已证）：
- 不证 `trunc` 与既有 `observationAllowed`/`versionApplicableAt` 的等价：那是单点判定，
  与序列视图不同型。
- 不证集合层面的外延等式（把 `contains` 当 `Set Int` 证 `=`）；只证两侧包含并合成
  等值式，见 §未覆盖片段。
- 不证 `shiftInterval` 与 `intervalIntersection` 可交换（需要 `max`/`min` 与平移的
  分配引理，本件未点名引用，故不写）。
- 不证时际法本身；[代拟稿] 签名只给形状与一条签名卫生引理。
- 不声称仓内任何前向失效定理覆盖迟到输入；`reordering_requires_recomputation` 是
  本件自建 `aggregate` 上的定理，与那些定理无推理关系。
- 不借 `TemporalKripke.lean:55` 的 LTL 强度：该定理的步进情形写作 `intro j _; exact
  h_all j`，可达关系被丢弃，`n` 是世界计数而非时间轴。§F 三条定理正是把这一点钉明。

## §未覆盖片段

1. ISO 字符串日期**无已证比较桥**：`BusinessRoot/SevenAxis.lean:50-51,103-104` 与
   `BusinessRoot/ArtifactParser.lean:61-62` 用 `String` 承载 `dueDay/asOfDay`，仓内没有
   任何把字符串序与 `Int` epochDay 序对齐的函数或定理。本件不引入任何 `String` 日期算子。
2. 同名异义的 `EventHistory` 保持互不相干：`LegalModelV2.lean:158`
   （`JurisLean.EventHistory`，`events : List Event`，`Event.atDay : Int`）与
   `KernelV3.lean:224`（`JurisLean.KernelV3.EventHistory`，`eventTimes/factTime : Nat`）。
   本件不合并它们，也不在两者之间搬运结论。
3. 载体不止四个（`Nat` 日计数 / `Int` epoch 日 / `String` ISO / `Prop` 关系型），
   且除本件的 `dayToTimePoint` 之外，仓内原本**没有任何**载体间转换函数。
   `Int → Nat` 方向有信息损失，`no_unified_time_carrier_yet` 给出确切 witness。
4. `trunc` 的偏序单调性（as-of 后移则视图只增不减）未证：本件不为它引入 `⊆` 记法。
5. 期间算子缺失更多：`DayInterval` 无并、无补、无长度/日数计数，闰日、时区、粒度仍按
   `TemporalArithmetic.lean:4` 的口径留给数据层。
6. P-049 载体是 `Nat`，与 `TemporalApplicability` 的 `Int` 无桥；本件不跨载体套用时限结论。

## §档位

定义为 [构造性定义]；全部定理在本件内给出完整证明，零 `sorry`、零 `admit`、零新增
`axiom`，`decide` 只用于闭式字面量（`10 < 11`、`Int.toNat (-1) = 0`、
非交换聚合的 7 ≠ -7 等），未使用 `native_decide`，未使用 `Float`。
`IntertemporalLawSignature` 及其两条引理为 **[代拟稿]**：签名无可核验的中文时际法条文
支撑（唯一已核验的民诉法解释第 105 条涉证据评价、不涉时际法，故条文槽位记 **待核验**），
外部依据只引已核验书目：Karl Larenz, *Methodenlehre der Rechtswissenschaft*, 6. Aufl.,
Springer 1991, DOI `10.1007/978-3-662-08711-4`, ch. *Methoden richterlicher
Rechtsfortbildung*, pp. 366–436, DOI `10.1007/978-3-662-08711-4_11`。
按仓库边界约定，Lean 权威认定在 CI；本地编译仅为自检，称 provisional。
-/

namespace JurisLean.Seams.Temporal

section NonAnticipation

/-- 中文说明：裁判时点截断视图（A 组算子）。把带日期的事件序列截到 `asOf` 之前（含端点），
    即"只保留 day ≤ asOf"。仓内此前没有序列级视图算子；本件自带递归，不依赖
    `List.filter` 的引理库，方便后续整段可审计。 -/
def trunc {α : Type} (asOf : Int) : List (Int × α) → List (Int × α)
  | [] => []
  | x :: rest => if x.1 ≤ asOf then x :: trunc asOf rest else trunc asOf rest

/-- 中文证明：全在未来（day > asOf）的片段被截为空。这是"未来材料一个字都进不了视图"
    的算术内核。 -/
theorem trunc_of_all_future {α : Type} (asOf : Int) :
    ∀ (f : List (Int × α)), (∀ x ∈ f, asOf < x.1) → trunc asOf f = [] := by
  intro f
  induction f with
  | nil => intro _; rfl
  | cons y ys ih =>
    intro hf
    have hy : ¬ (y.1 ≤ asOf) :=
      not_le_of_gt (hf y (List.mem_cons_self : y ∈ y :: ys))
    have htail : ∀ x ∈ ys, asOf < x.1 := fun x hx => hf x (List.mem_cons_of_mem y hx)
    show (if y.1 ≤ asOf then y :: trunc asOf ys else trunc asOf ys) = []
    rw [if_neg hy, ih htail]

/-- 中文证明：在 as-of 之后追加事件不改变视图（A 组的引擎定理）。
    假设 `f` 里每个日期都严格晚于 `asOf`。 -/
theorem trunc_asOf_append_future_irrelevant {α : Type} (asOf : Int) (e f : List (Int × α))
    (hf : ∀ x ∈ f, asOf < x.1) : trunc asOf (e ++ f) = trunc asOf e := by
  induction e with
  | nil => rw [List.nil_append, trunc_of_all_future asOf f hf]; rfl
  | cons y ys ih =>
    show (if y.1 ≤ asOf then y :: trunc asOf (ys ++ f) else trunc asOf (ys ++ f)) =
           (if y.1 ≤ asOf then y :: trunc asOf ys else trunc asOf ys)
    by_cases hy : y.1 ≤ asOf
    · rw [if_pos hy, if_pos hy]
      exact congrArg (List.cons y) ih
    · rw [if_neg hy, if_neg hy]
      exact ih

/-- 中文证明：法律时间不预览未来（A 组主定理，比"追加"更强的"改写"形）。
    只要两段材料全部晚于 as-of，则把它们换掉也不改变裁判时点视图；于是取 `f₁ = []`
    就退化成 `trunc asOf (e ++ f₂) = trunc asOf e`。
    诚实对照：`TemporalApplicability.lean:79` `future_information_blocked` 只否定一次
    "观察晚于 as-of"（单点、Prop 级），不触及序列，也不涉及任何后序计算；本定理是
    序列级的等式，二者不同型，本件不声称本定理推出或包含那条定理。 -/
theorem legal_time_nonanticipation {α : Type} (asOf : Int) (e f₁ f₂ : List (Int × α))
    (h₁ : ∀ x ∈ f₁, asOf < x.1) (h₂ : ∀ x ∈ f₂, asOf < x.1) :
    trunc asOf (e ++ f₁) = trunc asOf (e ++ f₂) := by
  rw [trunc_asOf_append_future_irrelevant asOf e f₁ h₁,
    trunc_asOf_append_future_irrelevant asOf e f₂ h₂]

/-- 中文证明：视图相同则一切由视图算出的值相同（A 组推论一：事后诸葛不可能通过换视图
    改变结论）。`k` 是任意后接函数，本件不约束它，正因如此结论才与算法无关。 -/
theorem trunc_view_congr {α β : Type} (asOf : Int) (k : List (Int × α) → β)
    (e₁ e₂ : List (Int × α)) (h : trunc asOf e₁ = trunc asOf e₂) :
    k (trunc asOf e₁) = k (trunc asOf e₂) :=
  congrArg k h

/-- 中文证明：as-of 之后到达的材料不可能改变任何由视图计算出的值（A 组推论二，
    把 `trunc_asOf_append_future_irrelevant` 与 `trunc_view_congr` 串成法律上要的
    那一句："迟到材料不改判决函数值"）。 -/
theorem nonanticipation_computed_agrees {α β : Type} (asOf : Int)
    (k : List (Int × α) → β) (e f : List (Int × α))
    (hf : ∀ x ∈ f, asOf < x.1) :
    k (trunc asOf (e ++ f)) = k (trunc asOf e) := by
  rw [trunc_asOf_append_future_irrelevant asOf e f hf]

/-- 中文证明：视图健全——视图里的每个事件日期都不晚于 as-of（截断算子的另一侧：
    既不漏也不超）。与 `trunc_sound` 合起来说明 `trunc` 确为"过去视图"。 -/
theorem trunc_sound {α : Type} (asOf : Int) (e : List (Int × α)) :
    ∀ x ∈ trunc asOf e, x.1 ≤ asOf := by
  induction e with
  | nil => intro x hx; cases hx
  | cons y ys ih =>
    show ∀ z ∈ (if y.1 ≤ asOf then y :: trunc asOf ys else trunc asOf ys), z.1 ≤ asOf
    by_cases hy : y.1 ≤ asOf
    · intro z hz
      rw [if_pos hy] at hz
      obtain (heq | hmem) := List.mem_cons.mp hz
      · subst heq; exact hy
      · exact ih z hmem
    · intro z hz
      rw [if_neg hy] at hz
      exact ih z hz

end NonAnticipation

section PeriodPreservation

/-- 中文说明：期间平移（B 组算子）。把 `DayInterval` 的两端都用既有
    `JurisLean.addDays`（`TemporalArithmetic.lean:12`）平移 `n` 天。 -/
def shiftInterval (n : Nat) (i : DayInterval) : DayInterval :=
  { fromDay := addDays i.fromDay n, toDay := addDays i.toDay n }

/-- 中文证明：平移保良态（期间保义第一半：`valid` 不被平移破坏）。 -/
theorem shiftInterval_valid (n : Nat) (i : DayInterval) (hv : i.valid) :
    (shiftInterval n i).valid := by
  dsimp only [DayInterval.valid, shiftInterval, addDays] at hv ⊢
  omega

/-- 中文证明：平移双向搬运归属（期间保义第二半，等值式而非单侧蕴含）：
    `d` 属于原区间 ⟺ `d` 平移后属于平移后的区间。 -/
theorem shift_contains_iff (n : Nat) (i : DayInterval) (d : Int) :
    i.contains d ↔ (shiftInterval n i).contains (addDays d n) := by
  dsimp only [DayInterval.contains, shiftInterval, addDays]
  omega

/-- 中文证明：区间交集算子的**完备性**方向——若某日同时落在两个区间里，则
    `intervalIntersection` 必为 `some`，且结果也包含该日。这是既有
    `TemporalArithmetic.lean:66` `intersection_contained_in_both`（健全性方向）所没有的
    另一半；两端合起来才把"交集算子"与"包含集合之交"钉在一起。 -/
theorem intersection_some_of_contains_both (a b : DayInterval) (d : Int)
    (ha : a.contains d) (hb : b.contains d) :
    ∃ i : DayInterval, intervalIntersection a b = some i ∧ i.contains d := by
  dsimp only [DayInterval.contains] at ha hb
  refine ⟨{ fromDay := max a.fromDay b.fromDay, toDay := min a.toDay b.toDay }, ?_, ?_⟩
  · dsimp only [intervalIntersection]
    split
    · rfl
    · rename_i hneg
      have h1 : max a.fromDay b.fromDay ≤ d := max_le_iff.mpr ⟨ha.1, hb.1⟩
      have h2 : d ≤ min a.toDay b.toDay := le_min_iff.mpr ⟨ha.2, hb.2⟩
      exact absurd (le_trans h1 h2) hneg
  · dsimp only [DayInterval.contains]
    exact ⟨max_le_iff.mpr ⟨ha.1, hb.1⟩, le_min_iff.mpr ⟨ha.2, hb.2⟩⟩

/-- 中文证明：`intervalIntersection` 在 `some` 情形与两个 `contains` 集合的交完全一致
    （B 组第三件：等值式，健全性一侧复用既有 `intersection_contained_in_both`，
    完备性一侧用上一条）。注意本件用两个具名定理给出两侧包含，再合成等值式；
    `Set` 层面的外延等式（`Set` 化 `contains` 后证集合相等）不在本件覆盖内，见 §未覆盖片段。 -/
theorem intersection_agrees_with_contains_set (a b i : DayInterval)
    (hinter : intervalIntersection a b = some i) (d : Int) :
    i.contains d ↔ a.contains d ∧ b.contains d := by
  constructor
  · exact intersection_contained_in_both a b i hinter d
  · intro ⟨ha, hb⟩
    obtain ⟨j, hj, hjd⟩ := intersection_some_of_contains_both a b d ha hb
    have heq : i = j := Option.some.inj ((Eq.symm hinter).trans hj)
    rw [← heq] at hjd
    exact hjd

end PeriodPreservation

section LateEvidence

/-- 中文证明：P-049 举证时限的**量化刻画**（C 组主定理，冻结载体
    `JurisLean.Genealogy.Part3.P049.FilingWindow`，`Genealogy/Part3.lean:79-96`，本件不改它）。
    仓内此前只有 `Part3.lean:93-96` 那条 11 对 10 的 `decide` 字面实例与
    `Part3.lean:87-91` 的"有正当理由即准入"，**没有**对任意 `filed`、任意窗口成立的
    等值式；本件补上。载体经 `import JurisLean.Genealogy.Part3` 直连真身，未另立相似结构。 -/
theorem evidenceAdmissible_iff (filed : Nat)
    (w : Genealogy.Part3.P049.FilingWindow) :
    Genealogy.Part3.P049.evidenceAdmissible filed w = true ↔
      filed ≤ w.deadlineDay ∨ w.extendedForGoodCause = true := by
  by_cases hc : filed ≤ w.deadlineDay
  · show (if filed ≤ w.deadlineDay then true else w.extendedForGoodCause) = true ↔
           (filed ≤ w.deadlineDay ∨ w.extendedForGoodCause = true)
    rw [if_pos hc]
    exact ⟨fun _ => Or.inl hc, fun o => o.elim (fun _ => rfl) (fun _ => rfl)⟩
  · show (if filed ≤ w.deadlineDay then true else w.extendedForGoodCause) = true ↔
           (filed ≤ w.deadlineDay ∨ w.extendedForGoodCause = true)
    rw [if_neg hc]
    exact ⟨Or.inr, fun o => o.elim (fun h => absurd h hc) id⟩

/-- 中文证明：逾期且无正当理由的一般排除律（C 组第二件）。
    既有定理只对 `filed = 11, deadline = 10` 这一个具体数成立；本条把量词补全，
    因而原字面实例只是它的一个代入。 -/
theorem late_without_good_cause_barred_general (filed : Nat)
    (w : Genealogy.Part3.P049.FilingWindow) (hgt : w.deadlineDay < filed)
    (hno : w.extendedForGoodCause = false) :
    Genealogy.Part3.P049.evidenceAdmissible filed w = false := by
  show (if filed ≤ w.deadlineDay then true else w.extendedForGoodCause) = false
  rw [if_neg (not_le_of_gt hgt), hno]

/-- 中文证明：一般排除律回生出仓内那条冻结字面实例（C 组可审计对照：
    说明本件把 `Part3.lean:93-96` 的 `decide` 单点降级为一条规律的特例；
    复用定理，未修改 `Part3.lean` 任何一行）。 -/
theorem p049_frozen_witness_recovered :
    Genealogy.Part3.P049.evidenceAdmissible 11
      { deadlineDay := 10, extendedForGoodCause := false } = false :=
  late_without_good_cause_barred_general 11
    { deadlineDay := 10, extendedForGoodCause := false } (by decide) rfl

end LateEvidence

section RetrospectiveReordering

/-- 中文说明：迟到插入（D 组算子一）。迟到材料按到达顺序排在既有序列之后；
    仓内此前**不存在**任何把迟到输入送进已算流水线的算子（全仓 `retro*`/`Reorder`/
    `reprocess`/`溯`/`从旧兼从轻` 零声明，只有 `Genealogy/TSpectrum/Batch1.lean:433,678`
    两处把它列为"仍缺"的散文）。 -/
def insertLate {α : Type} (e : Int × α) (evs : List (Int × α)) : List (Int × α) :=
  evs ++ [e]

/-- 中文说明：聚合（D 组算子二）。按到达顺序对日标签做右折叠；`op` 决定该聚合是否
    可交换，法律后果的分岔正来自这一点。本件只在 `Int` 上取标签，不引入测度或拓扑。 -/
def aggregate {α : Type} (op : Int → Int → Int) (init : Int)
    (evs : List (Int × α)) : Int :=
  evs.foldr (fun x acc => op x.1 acc) init

/-- 中文证明：右折叠的技术引理——对"提取标签后相加"的折叠，先appendTo还是先cons
    结果相同。归纳只用线性算术，不点名任何 Mathlib 交换引理。 -/
theorem foldr_add_arrival_insensitive {α : Type} (f : α → Int) (l : List α) (x : α) :
    (l ++ [x]).foldr (fun a acc => f a + acc) 0 =
      (x :: l).foldr (fun a acc => f a + acc) 0 := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    show f y + (ys ++ [x]).foldr (fun a acc => f a + acc) 0 =
           f x + (f y + ys.foldr (fun a acc => f a + acc) 0)
    rw [ih]
    show f y + (f x + ys.foldr (fun a acc => f a + acc) 0) =
           f x + (f y + ys.foldr (fun a acc => f a + acc) 0)
    omega

/-- 中文证明：可交换聚合下迟到无关（D 组分岔第一侧）。取加法聚合器（`Int` 上可交换、
    可结合），则"迟到材料排在最后"与"它本来就在最前"给出同一个数——这就是
    "迟到之后整条流水线重跑一遍是可靠的"的数学内容。 -/
theorem aggregate_add_arrival_insensitive {α : Type} (evs : List (Int × α)) (e : Int × α) :
    aggregate (· + ·) 0 (insertLate e evs) = aggregate (· + ·) 0 (e :: evs) :=
  foldr_add_arrival_insensitive Prod.fst evs e

/-- 中文说明：D 组分岔第二侧用的非交换聚合器（减法既不可交换也不满足折叠同侧结合）。 -/
def noncommOp : Int → Int → Int := fun a b => a - b

/-- 中文证明：非交换聚合下迟到会改结果（D 组分岔第二侧，显式小 witness，闭式 `decide`）。
    迟到插入把 `10 - (3 - 0) = 7` 变成 `3 - (10 - 0) = -7`。这是"重排必须重算"的
    正面证据：存在这样的算子，不是猜想。 -/
theorem late_insert_changes_noncommutative :
    aggregate noncommOp 0 (insertLate (3, ()) [(10, ())]) ≠
      aggregate noncommOp 0 ((3, ()) :: [(10, ())]) := by
  decide

/-- 中文说明：前向失效的最小抽象（D 组对照物）。把"作废"建模成一个附加 `Bool` 标记，
    数值原样带过——这正是仓内 `SourceTime.lean:89`、`Provenance.lean:90`、
    `Withdrawal.lean:144`、`TemporalApplicability.lean:86/93` 共同的形状。 -/
def flagResponse (stale : Int) (invalid : Bool) : Int × Bool := (stale, invalid)

/-- 中文证明：贴标记不产生任何新数值（D 组结构性理由）。标记反应的第一投影恒等于旧值，
    所以 `late_insert_changes_noncommutative` 那种差异**不可能**由"只贴标记"的机制表达；
    仓内那批前向失效定理因此覆盖不了迟到输入。本件不声称它们中的任何一条与本定理有关。 -/
theorem invalidation_marker_computes_nothing (stale : Int) (invalid : Bool) :
    (flagResponse stale invalid).1 = stale := rfl

/-- 中文证明：重排要求重算（D 组结论）。存在已算序列与迟到材料，使迟到插入**必然**改变
    聚合值，故旧值不可保留、唯一正确反应是重算。
    诚实边界：本定理说的是本件自建的 `aggregate`/`insertLate`；它不推出、也不被
    `SourceTime.lean:89` `version_change_invalidates`、`Provenance.lean:90`
    `invalidated_of_retired_used`、`Withdrawal.lean:144` `deletion_invalidates_cache`
    任何一条推出——那三条只产出"作废"判定，仓内没有一条定理在迟到输入到达后重算结果
    （全仓零 `retro*`/`Reorder`/`reprocess` 声明，已核验）。 -/
theorem reordering_requires_recomputation :
    ∃ (evs : List (Int × Unit)) (e : Int × Unit),
      aggregate noncommOp 0 evs ≠ aggregate noncommOp 0 (insertLate e evs) := by
  refine ⟨[(10, ())], (3, ()), ?_⟩
  decide

end RetrospectiveReordering

section CarrierBridge

/-- 中文说明：唯一可证的时间载体转换（E 组）：`Nat` 日计数器 →
    `LegalIds.lean:72` 的 `TimePoint`（内部载体 `Int` epoch 日）。仓内原本
    **没有任何**载体间转换函数（`TimePoint.mk`、`toTimePoint`、`ofDay` 全仓零命中）。 -/
def dayToTimePoint (n : Nat) : TimePoint :=
  { epochDay := (n : Int) }

/-- 中文证明：往返之一（读回 epoch 日，定义级）。 -/
theorem epochDay_dayToTimePoint (n : Nat) : (dayToTimePoint n).epochDay = (n : Int) := rfl

/-- 中文证明：往返之二（`Int.toNat` 把嵌入读回原 `Nat`，非负方向无损）。 -/
theorem dayToTimePoint_toNat_round (n : Nat) :
    Int.toNat ((dayToTimePoint n).epochDay) = n := by
  dsimp only [dayToTimePoint]
  omega

/-- 中文证明：嵌入是单的（`Nat` 日在 `TimePoint` 载体里不坍缩）。 -/
theorem dayToTimePoint_inj (m n : Nat)
    (h : dayToTimePoint m = dayToTimePoint n) : m = n := by
  have hcast := congrArg TimePoint.epochDay h
  dsimp only [dayToTimePoint] at hcast
  omega

/-- 中文证明：嵌入与既有 `addDays`（`TemporalArithmetic.lean:12`）交换——平移后再嵌入
    等于嵌入后平移，因此 `Nat` 侧的"过 n 天"与 `Int` 侧的 `addDays` 不矛盾。 -/
theorem addDays_commutes_with_embedding (n k : Nat) :
    (dayToTimePoint (n + k)).epochDay = addDays ((dayToTimePoint n).epochDay) k := by
  dsimp only [dayToTimePoint, addDays]
  omega

/-- 中文说明：**限制条目**（本条只证"两侧载体不可等同"这一半；`String` ISO 日期无已证
    比较桥、两个同名 `EventHistory` 互不相干、以及"除此之外没有别的可用转换"这三句是
    仓库状态陈述，属 §未覆盖片段 的散文边界，本件不给定理也不假装给）。
    中文证明：唯一的 `Nat↔Int` 桥 `Int.toNat` 不反映 `Int` 的序——存在负日把信息吞掉：
    `Int.toNat (-1) = Int.toNat (-2) = 0` 而 `-1 > -2`。所以把 `Nat` 日计数器载体与
    `Int` epoch 日载体当成同一个载体是**不健全**的，二者只能靠显式转换函数衔接，
    而仓内此前一个都没有。 -/
theorem no_unified_time_carrier_yet :
    (∃ x : Int, Int.toNat x = 0 ∧ x < 0) ∧
      ¬ (∀ a b : Int, Int.toNat a ≤ Int.toNat b → a ≤ b) := by
  refine ⟨⟨(-1 : Int), by decide, by decide⟩, ?_⟩
  intro hall
  have hpre : Int.toNat (-1 : Int) ≤ Int.toNat (-2 : Int) := by decide
  exact absurd (hall (-1) (-2) hpre) (by decide : ¬ ((-1 : Int) ≤ (-2 : Int)))

/-- **`Int`（有向时点）↔ `DayInterval`（期间）桥**——13_ 卷 C5 指定"先收两套：`Int` 与
    `DayInterval` 保留为规范时间载体，四套无转换函数"。上面已把 `Nat↔Int(TimePoint)` 接上；
    本条补上 `Int`↔`DayInterval` 这一对：把一个时点看成退化单日闭区间 `[d,d]`。
    诚实边界：只交"时点→退化区间"这一方向的具名换算及其可逆/单射性，不声称 `String` 显示位、
    两个 `EventHistory` 也已被桥接（那三句仍是 §未覆盖片段的散文边界）。 -/
def instantToInterval (d : Int) : DayInterval := ⟨d, d⟩

/-- 期间→时点：取区间起始端点；与 `instantToInterval` 在退化区间上互逆。 -/
def intervalToInstant (i : DayInterval) : Int := i.fromDay

/-- 往返：时点先成退化区间再读回起点，等于原时点（定义级）。 -/
theorem intervalToInstant_instantToInterval (d : Int) :
    intervalToInstant (instantToInterval d) = d := rfl

/-- 桥非空洞：不同时点落到不同区间（`DayInterval` 有 DecidableEq，`decide` 直接判）。 -/
theorem instantToInterval_distinguishes :
    instantToInterval (0 : Int) ≠ instantToInterval (1 : Int) := by
  decide

/-- 桥是单的：把 `Int` 时点在 `DayInterval` 载体里不坍缩。 -/
theorem instantToInterval_inj (a b : Int)
    (h : instantToInterval a = instantToInterval b) : a = b := by
  simpa [instantToInterval] using congrArg DayInterval.fromDay h

end CarrierBridge

section TransitionSkeleton

/-- 中文证明：`TemporalKripke.lean:39` 的 `ltl_always` 只要逐点成立就已成立，
    与可达关系取什么值无关（F 组第一件，也是 `TemporalKripke.lean:55` 步进情形写成
    `intro j _; exact h_all j` 的真正原因）。这是对**当前文件假设**的陈述，
    不是"Kripke 层无用"的论断：加了序/非对称/传递假设后该算子可以变强，本件不否认这点。 -/
theorem ltl_always_of_pointwise {n : Nat} (K : TemporalKripke n) (φ : Fin n → Prop)
    (h : ∀ i, φ i) :
    ∀ (R : Fin n → Fin n → Prop), ltl_always { K with transitions := R } φ := by
  intro R i
  exact ⟨h i, fun _ _ => h _⟩

/-- 中文证明：反向的可分离性——`ltl_always` 的第一投影就是逐点成立；可达部分对这部分
    毫无贡献（F 组第二件）。 -/
theorem ltl_always_implies_pointwise {n : Nat} (K : TemporalKripke n) (φ : Fin n → Prop)
    (h : ltl_always K φ) : ∀ i, φ i := fun i => (h i).1

/-- 中文证明：任意两个可达关系下 `ltl_always` 同真同假（F 组主定理：转移独立性）。
    因此 XT 必须自建 (A) 组的不预览未来算子，而不能借
    `TemporalKripke.lean:55` 的名义当时间逻辑用——那里的 `n` 是世界计数（`Fin n`），
    不是时间轴，且文件内**没有**任何序、非对称或传递假设（已逐行核验）。 -/
theorem ltl_always_transition_independent {n : Nat} (K : TemporalKripke n)
    (φ : Fin n → Prop) (h : ∀ i, φ i)
    (R₁ R₂ : Fin n → Fin n → Prop) :
    ltl_always { K with transitions := R₁ } φ ↔ ltl_always { K with transitions := R₂ } φ :=
  ⟨fun _ => ltl_always_of_pointwise K φ h R₂, fun _ => ltl_always_of_pointwise K φ h R₁⟩

end TransitionSkeleton

section IntertemporalSignature

/-- 中文说明：**[代拟稿]** 法源时间操作签名（G 组）。仅为形状声明：公布日、生效日、
    是否溯及、是否"从旧兼从轻"的开关。法律语义上它对应"新法施行后旧法如何继续作用于
    既往事实"，即时际法的三类操作（不溯及、溯及既往、从轻例外）。
    依据只引已核验书目：Karl Larenz, *Methodenlehre der Rechtswissenschaft*,
    6. Aufl., Springer 1991, DOI `10.1007/978-3-662-08711-4`, ch. *Methoden richterlicher
    Rechtsfortbildung*, pp. 366–436, DOI `10.1007/978-3-662-08711-4_11`。
    **中文条文槽位：待核验**（唯一已核验的民诉法解释第 105 条涉证据评价，不涉时际法，
    故本签名不援引任何条号）。本件不声称本签名刻画了任何实定法，也不声称下面的引理
    是法律证明。 -/
structure IntertemporalLawSignature where
  promulgateDay : Int
  effectiveDay : Int
  retroactive : Bool
  lighterAlternative : Bool
deriving DecidableEq, Repr

/-- 中文说明：**[代拟稿]** 签名良态：公布日不晚于生效日（纯算术前提，不含条文内容）。 -/
def IntertemporalLawSignature.wellFormed (s : IntertemporalLawSignature) : Prop :=
  s.promulgateDay ≤ s.effectiveDay

/-- 中文说明：**[代拟稿]** 把溯及开关关掉的默认化操作（不溯及原则的签名形状）。 -/
def IntertemporalLawSignature.withRetroFalse
    (s : IntertemporalLawSignature) : IntertemporalLawSignature :=
  { s with retroactive := false, lighterAlternative := s.lighterAlternative }

/-- 中文证明：签名卫生引理（[代拟稿]）——默认化不改生效日。这是字段守恒的
    `rfl` 级事实，**不是**时际法定理，本件不把它当法律结论。 -/
theorem intertemporal_signature_preserves_effective_day (s : IntertemporalLawSignature) :
    (s.withRetroFalse).effectiveDay = s.effectiveDay := rfl

/-- 中文证明：签名卫生引理二（[代拟稿]）——默认化保持良态谓词（不引入新的日期矛盾）。
    同样是结构级事实，不承担法律证明。 -/
theorem IntertemporalLawSignature.withRetroFalse_preserves_wellFormed
    (s : IntertemporalLawSignature) (h : s.wellFormed) : s.withRetroFalse.wellFormed := h

end IntertemporalSignature

end JurisLean.Seams.Temporal
