import Mathlib.Tactic
import JurisLean.Seams.Temporal
import JurisLean.Seams.PrecedentFlow

/-!
# XT 族五针（附录 I.13 逐名承接，UnifiedNeedlesXT）

中文说明：承接 `docs/spec/20261007-统一法律数学模型_附录I_Lean施工明细.md` §I.13 XT 族
五针（#48-#52）。每针以**原验收名**命名，"拟"合同写成显式前提的定理；可复用锚
（`Seams/Temporal.lean:159` `legal_time_nonanticipation`、`:342`
`late_insert_changes_noncommutative`、`:399` `addDays_commutes_with_embedding`、
`Seams/PrecedentFlow.lean:867` `update_does_not_reach_before_effective_from`）以全限定名
引用或直接实例化，避免与同名本针遮蔽。降载体处均在语句与本文件内如实声明。

## 逐针人话语义（人话）

- 48 `legal_time_nonanticipation`：非预期性——裁判时点锁死证据面。任何实际 Eval 只要经
  `trunc asOf` 截断视图（lawView）取值（使用点前提 `hview` 显式化），截止日之后的材料
  无论整段换成 `f₁` 还是 `f₂`，Eval 读数一字不动（Temporal 同名锚定理的全限定实例化）。
- 49 `late_evidence_preserves_ontic_state`：迟到证据只进证据层（E），本体层（R）不动；
  有效追溯裁判另有独立的效果事件通道（`retroEffect`），两通道在构造子层面不混同。
- 50 `temporal_observations_preserved`：所有实际时间观察（端点序、日单位平移、期间归属
  与时长）在 `dayToTimePoint` 局部日历嵌入下保持；另附反例：保序不保时长
  （`f n = 2n` 把两日之差拉成四日）。
- 51 `past_applicability_without_retroactivity`：无追溯性——新版本记录对其生效起点之前
  的时点不可适用，且该时点可适用的旧记录未被取代名单命中（无相关改变）时，更新前后的
  源选择（可适用版本成员）完全保持。
- 52 `independent_events_commute`：读写槽分离（两事件各写各读自己的槽）时事件可交换；
  同槽附具体不交换反例，一般迟到插入的非交换锚（`late_insert_changes_noncommutative`）
  原样保留，不作一般交换声明。

## 载体差异（诚实降级声明）

- 第 48 针的 `hview`（Eval 经视图取值）是逐规则使用点要核的前提，本件只给使用点
  定义级成立的样例（`viewEval`），不声称对任何既有规则体自动成立，完整式开放。
- 第 49 针的双层载体 `DualLayerState` 与事件语言 `LawEvent` 为本件显式新建有限载体，
  与冻结内核（`LegalModelV2`/`KernelV3`）无定义关系；通道分离是构造级事实。
- 第 50 针的 `NatDayInterval` 为本件新建（`Nat` 日计数侧期间载体）；String ISO 日期仍无
  已证比较桥（沿 `Temporal.lean` §未覆盖片段口径），本件不引入。
- 第 51 针闭合成成员级（源选择）等值；表级列表相等（次序与多重性）未证，记开放。锚
  `update_does_not_reach_before_effective_from` 的存在句形式不直接给出新记录的判定，
  本针用其同一底层引理 `before_effective_interval_not_effective` 直接闭合该分量。
- 第 52 针的 `TwoSlotState`/`Slot` 为本件新建最小读写分离载体，不冒称一般事件账本
  可交换（D 组反例保留）。

## §档位

定义为 [构造性定义]；全部定理在本件内给出完整证明，零 `sorry`、零 `admit`、零新增
`axiom`，`decide` 只用于闭式字面量（4 ≠ 2、同槽 1 ≠ 2、构造子不混同由 `noConfusion`
给出），未使用 `native_decide`，未使用 `Float`。按仓库边界约定，Lean 权威认定在 CI；
本地未编译，状态 CI_NOT_RUN。
-/

namespace JurisLean.Seams.UnifiedNeedlesXT

open JurisLean.Seams.Temporal
open JurisLean.Seams.PrecedentFlow

/-! ## 第 48 针：legal_time_nonanticipation -/

section Needle48Nonanticipation

/-- **第 48 针（XT，I.13）**：legal_time_nonanticipation——非预期性（决策时只用截止前
    信息）。人话：只要实际 Eval 是经 `trunc asOf` 截断视图（lawView）取值的——这一
    "逐规则使用点"要核的前提在此显式写成 `hview`——那么截止日 `asOf` 之后的材料无论
    整段换成 `f₁` 还是 `f₂`，Eval 读数不变。证明是同名锚定理
    `JurisLean.Seams.Temporal.legal_time_nonanticipation`（`Temporal.lean:159`，追加与
    改写两侧）的全限定实例化：视图等式经 `congrArg` 抬到任意后接函数 `k`。
    诚实边界：`hview` 不在本件内对任何既有规则自动证出（仓内无消费 `trunc` 的实际
    规则体），完整式开放；使用点样例见 `viewEval_nonanticipation`。 -/
theorem legal_time_nonanticipation {α β : Type} (asOf : Int)
    (eval : List (Int × α) → β) (k : List (Int × α) → β)
    (hview : ∀ evs, eval evs = k (trunc asOf evs))
    (e f₁ f₂ : List (Int × α))
    (h₁ : ∀ x ∈ f₁, asOf < x.1) (h₂ : ∀ x ∈ f₂, asOf < x.1) :
    eval (e ++ f₁) = eval (e ++ f₂) := by
  rw [hview (e ++ f₁), hview (e ++ f₂)]
  exact congrArg k (JurisLean.Seams.Temporal.legal_time_nonanticipation asOf e f₁ f₂ h₁ h₂)

/-- 第 48 针的使用点样例：Eval 直接定义在截断视图上（lawView 形态），
    `hview` 对它是定义级成立。 -/
def viewEval {α : Type} (k : List (Int × α) → Int) (asOf : Int)
    (evs : List (Int × α)) : Int :=
  k (trunc asOf evs)

/-- 使用点 discharged 的形态展示：对 `viewEval` 这类"取值即读视图"的规则体，
    第 48 针的前提在定义层满足，结论由此闭合。 -/
theorem viewEval_nonanticipation {α : Type} (k : List (Int × α) → Int) (asOf : Int)
    (e f₁ f₂ : List (Int × α))
    (h₁ : ∀ x ∈ f₁, asOf < x.1) (h₂ : ∀ x ∈ f₂, asOf < x.1) :
    viewEval k asOf (e ++ f₁) = viewEval k asOf (e ++ f₂) :=
  JurisLean.Seams.UnifiedNeedlesXT.legal_time_nonanticipation asOf
    (viewEval k asOf) k (fun _ => rfl) e f₁ f₂ h₁ h₂

end Needle48Nonanticipation

/-! ## 第 49 针：late_evidence_preserves_ontic_state -/

section Needle49EvidenceOntic

/-- 第 49 针载体（本件新建）：双层状态——R 本体层与 E 证据层各一条时间戳事件账本
    （沿用 `Temporal.insertLate` 的到达序账本形态，不另造账本算子）。 -/
structure DualLayerState (α : Type) where
  ontic : List (Int × α)
  evidence : List (Int × α)

/-- 第 49 针载体（本件新建）：最小事件语言。迟到证据（`lateEvidence`）与有效追溯裁判
    的效果事件（`retroEffect`）是两个不同构造子——"不混同"由此在类型层读出。 -/
inductive LawEvent (α : Type) where
  | lateEvidence : Int × α → LawEvent α
  | retroEffect : Int × α → LawEvent α

/-- 事件应用：迟到证据只写 E 层（复用 `Temporal.insertLate`），追溯效果只写 R 层。 -/
def applyEvent {α : Type} : LawEvent α → DualLayerState α → DualLayerState α
  | LawEvent.lateEvidence e, s => { s with evidence := insertLate e s.evidence }
  | LawEvent.retroEffect e, s => { s with ontic := insertLate e s.ontic }

/-- **第 49 针（XT，I.13）**：late_evidence_preserves_ontic_state——迟到证据只进证据层，
    本体层不动。人话：纯 E（证据）更新保持 R（本体）一字不动；本原名在仓内未见，
    载体为本件新建双层状态，分离是构造级事实（`rfl`），不是事后检查。
    若确有有效追溯裁判，则另走 `retroEffect` 效果事件显式改写 R 层，不与证据更新混同。 -/
theorem late_evidence_preserves_ontic_state {α : Type} (e : Int × α) (s : DualLayerState α) :
    (applyEvent (LawEvent.lateEvidence e) s).ontic = s.ontic := rfl

/-- 第 49 针配套（通道分离另一半）：追溯效果事件不动 E 层。 -/
theorem retro_effect_goes_through_ontic_channel {α : Type} (e : Int × α)
    (s : DualLayerState α) :
    (applyEvent (LawEvent.retroEffect e) s).evidence = s.evidence := rfl

/-- 第 49 针配套（不混同的构造子层见证）：证据事件与效果事件是不同构造子，
    无法用等式互冒。 -/
theorem late_evidence_is_not_retro_effect {α : Type} (e e' : Int × α) :
    (LawEvent.lateEvidence e : LawEvent α) ≠ LawEvent.retroEffect e' := by
  intro h
  cases h

end Needle49EvidenceOntic

/-! ## 第 50 针：temporal_observations_preserved -/

section Needle50EmbeddingObservations

/-- 第 50 针载体（本件新建）：`Nat` 日计数侧的期间（与 `Temporal.lean` 的
    `Nat` 日计数器载体同族；`DayInterval` 是 `Int` epoch 日侧期间）。 -/
structure NatDayInterval where
  fromDay : Nat
  toDay : Nat

/-- `Nat` 日计数侧的期间归属观察。 -/
def NatDayInterval.contains (i : NatDayInterval) (d : Nat) : Prop :=
  i.fromDay ≤ d ∧ d ≤ i.toDay

/-- 期间嵌入：`NatDayInterval` → `DayInterval`（两端经 `dayToTimePoint` 同一嵌入）。 -/
def embedInterval (i : NatDayInterval) : DayInterval :=
  ⟨(i.fromDay : Int), (i.toDay : Int)⟩

/-- **第 50 针（XT，I.13）**：temporal_observations_preserved——所有实际时间观察在
    `dayToTimePoint` 局部日历嵌入下保持。三个观察族：
    (i) 端点序：`n ≤ m` 当且仅当嵌入后保持序（`omega`，Nat 嵌入 Int 单调且忠实）；
    (ii) 日单位：`Nat` 侧"过 k 天"与 `Int` 侧 `addDays` 交换——锚
    `addDays_commutes_with_embedding`（`Temporal.lean:399`）原样实例化；
    (iii) 期间：良态 `Nat` 期间（起点不晚于终点）的归属观察双向保持，且时长（两端
    `Int` 差）等于 `Nat` 侧时长嵌入。诚实边界：只覆盖这两侧载体，String ISO 日期
    无比较桥（沿 `Temporal.lean` §未覆盖片段），闰日/时区/粒度不在此层。 -/
theorem temporal_observations_preserved :
    (∀ n m : Nat, n ≤ m ↔ (dayToTimePoint n).epochDay ≤ (dayToTimePoint m).epochDay) ∧
    (∀ n k : Nat, (dayToTimePoint (n + k)).epochDay = addDays ((dayToTimePoint n).epochDay) k) ∧
    (∀ i : NatDayInterval, i.fromDay ≤ i.toDay →
      (∀ d : Nat, i.contains d ↔ (embedInterval i).contains ((dayToTimePoint d).epochDay)) ∧
        (embedInterval i).toDay - (embedInterval i).fromDay = ((i.toDay - i.fromDay : Nat) : Int)) := by
  refine ⟨?_, addDays_commutes_with_embedding, ?_⟩
  · intro n m
    dsimp only [dayToTimePoint]
    omega
  · intro i hi
    constructor
    · intro d
      dsimp only [NatDayInterval.contains, embedInterval, DayInterval.contains, dayToTimePoint]
      omega
    · dsimp only [embedInterval]
      omega

/-- 第 50 针配套反例（合同明示"保序不足以保时长"）：`f n = 2n` 保序，但把第 0 日到
    第 2 日的时长（应为 2）拉成 4。保序嵌入不等于时长保持，故 (iii) 的时长观察必须
    显式证、不能由 (i) 顺手推出。 -/
theorem order_preserving_need_not_preserve_duration :
    ∃ f : Nat → Int, (∀ a b : Nat, a ≤ b → f a ≤ f b) ∧ f 2 - f 0 ≠ 2 := by
  refine ⟨fun n => 2 * (n : Int), ?_, ?_⟩
  · intro a b hab
    show (2 : Int) * (a : Int) ≤ 2 * (b : Int)
    omega
  · show (2 : Int) * (2 : Int) - 2 * (0 : Int) ≠ 2
    decide

end Needle50EmbeddingObservations

/-! ## 第 51 针：past_applicability_without_retroactivity -/

section Needle51NoRetroactivity

/-- 第 51 针引理：取代动作只会让可适用性变弱——更新后记录仍可适用，则更新前就可适用
    （被降级为 `superseded` 的记录不可能可适用）。 -/
theorem applicableAtBool_of_supersede (d : PrecedentDecision) (v : SourceVersionRecord)
    (t : Int) (h : applicableAtBool (supersedeRecord d v) t = true) :
    applicableAtBool v t = true := by
  rw [applicableAtBool_true_iff] at h ⊢
  simp only [versionApplicableAt, supersedeRecord] at h ⊢
  by_cases hh : hitsSupersession d v = true
  · rw [if_pos hh] at h
    by_cases ha : v.status = VersionStatus.active
    · rw [if_pos ha] at h
      exact absurd h.2 (by simp)
    · rw [if_neg ha] at h
      exact h
  · rw [if_neg hh] at h
    exact h

/-- **第 51 针（XT，I.13）**：past_applicability_without_retroactivity——无追溯性。
    人话：新规则不改变其生效日之前的源选择。两个显式前提：
    (1) `hnoRetro` 无追溯——时点早于新记录生效起点（锚
    `update_does_not_reach_before_effective_from`（`PrecedentFlow.lean:867`）的同一底层
    事实，本针用其内核引理 `before_effective_interval_not_effective` 直接闭合该分量）；
    (2) `hnoRel` 无相关改变——该时点可适用的旧记录未被取代名单命中。二者成立时，
    更新前后的可适用版本表（源选择）成员级完全等值。
    诚实边界：闭合成成员级（源选择）等值，表级列表相等（次序与多重性）未证，开放。 -/
theorem past_applicability_without_retroactivity (E : VersionEnv) (ad : AuthorizedDecision)
    (hfire : updateFires ad.decision = true) (t : Int)
    (hnoRetro : t < ad.decision.newRecord.effectiveFrom)
    (hnoRel : ∀ v ∈ E.versions, versionApplicableAt v t →
      hitsSupersession ad.decision v ≠ true) :
    ∀ w, w ∈ applicableVersions (precedentUpdate ad E) t ↔ w ∈ applicableVersions E t := by
  have hnew : ¬ versionApplicableAt ad.decision.newRecord t :=
    not_applicable_of_not_effective _ _
      (before_effective_interval_not_effective _ _ hnoRetro)
  intro w
  rw [mem_applicableVersions (precedentUpdate ad E) t w, mem_applicableVersions E t w,
    update_versions_fires ad E hfire]
  constructor
  · intro hmem
    obtain ⟨hw, happ⟩ := hmem
    obtain (heq | hin) := List.mem_cons.mp hw
    · rw [heq] at happ
      exact absurd ((applicableAtBool_true_iff _ _).mp happ) hnew
    · obtain ⟨v, hv, hfw⟩ := List.mem_map.mp hin
      have happ' : applicableAtBool (supersedeRecord ad.decision v) t = true := by
        rw [hfw]; exact happ
      have hfv := applicableAtBool_of_supersede ad.decision v t happ'
      have hnhit := hnoRel v hv ((applicableAtBool_true_iff _ _).mp hfv)
      rw [supersedeRecord_keeps_unhit ad.decision v hnhit] at hfw
      subst hfw
      exact ⟨hv, hfv⟩
  · intro hmem
    obtain ⟨hw, happ⟩ := hmem
    have hnhit := hnoRel w hw ((applicableAtBool_true_iff _ _).mp happ)
    have hkeep : supersedeRecord ad.decision w = w :=
      supersedeRecord_keeps_unhit ad.decision w hnhit
    exact ⟨List.mem_cons_of_mem _ (List.mem_map.mpr ⟨w, hw, hkeep⟩), happ⟩

end Needle51NoRetroactivity

/-! ## 第 52 针：independent_events_commute -/

section Needle52IndependentEvents

/-- 第 52 针载体（本件新建）：两槽状态，读写分离的最小模型。 -/
structure TwoSlotState where
  x : Int
  y : Int
  deriving DecidableEq

/-- 第 52 针载体（本件新建）：槽位——每个事件只读写自己的槽。 -/
inductive Slot where
  | left
  | right

/-- 事件：对指定槽做局部更新（读该槽、写该槽，不碰另一槽）。 -/
def applyAt : Slot → (Int → Int) → TwoSlotState → TwoSlotState
  | Slot.left, f, s => { s with x := f s.x }
  | Slot.right, f, s => { s with y := f s.y }

/-- 读写分离的读侧见证一：左槽事件不读不写右槽。 -/
theorem applyAt_left_keeps_right (f : Int → Int) (s : TwoSlotState) :
    (applyAt Slot.left f s).y = s.y := rfl

/-- 读写分离的读侧见证二：右槽事件不读不写左槽。 -/
theorem applyAt_right_keeps_left (g : Int → Int) (s : TwoSlotState) :
    (applyAt Slot.right g s).x = s.x := rfl

/-- **第 52 针（XT，I.13）**：independent_events_commute——读写分离的独立事件可交换。
    人话：两个事件各写各的槽（`hsep`：槽位不同，即写集不相交且互不读对方槽，读侧
    见证见上两条 `rfl` 引理），则先做哪个结果都一样。
    诚实边界：这是一般命题的**分离条件侧**；一般不交换——同槽反例见
    `same_slot_need_not_commute`，仓内迟到插入非交换锚
    `JurisLean.Seams.Temporal.late_insert_changes_noncommutative`（`Temporal.lean:342`）
    原样保留，本件不作任何一般交换声明。 -/
theorem independent_events_commute (sl₁ sl₂ : Slot) (f g : Int → Int) (s : TwoSlotState)
    (hsep : sl₁ ≠ sl₂) :
    applyAt sl₂ g (applyAt sl₁ f s) = applyAt sl₁ f (applyAt sl₂ g s) := by
  cases sl₁ with
  | left =>
    cases sl₂ with
    | left => exact absurd rfl hsep
    | right => rfl
  | right =>
    cases sl₂ with
    | left => rfl
    | right => exact absurd rfl hsep

/-- 第 52 针配套反例：同槽两事件（加一与加倍）在 `x = 0` 上不交换（1 与 2 各是一侧），
    故 `hsep` 不可去。 -/
theorem same_slot_need_not_commute :
    applyAt Slot.left (fun v => v + 1) (applyAt Slot.left (fun v => 2 * v)
        { x := 0, y := 0 }) ≠
      applyAt Slot.left (fun v => 2 * v) (applyAt Slot.left (fun v => v + 1)
        { x := 0, y := 0 }) := by
  decide

end Needle52IndependentEvents

end JurisLean.Seams.UnifiedNeedlesXT
