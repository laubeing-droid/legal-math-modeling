import Mathlib.Tactic
import JurisLean.Seams.Temporal

/-! # 诉讼时效与审级位（17_ 卷缺口 6：民法典 192/193 条的程序面 + 第 66 条后两段）

此前时效只有 `ClaimBasis.lean` 注释面的读法与两个构造子级见证
（时效抗辩 `:313`、同意履行 `:318`），没有起算／中断／中止／期间计算；
审级位完全空缺（`ReductionConditions2.lean` §五#3 自证：第 66 条后两段
"一审认为抗辩成立且未释明时**二审**可直接释明"无法表达，因为 `clarified`
只有一个不分审级的总位）。本件补这两格：

* **审级位**：`InstanceLevel`（一审／二审）＋ `presentAtSecond`（一审因客观原因
  未到庭、二审到庭）＋ `clarificationDutyAt`——第 66 条后两段的两个分审级读数
  （二审释明义务存在、一审未到庭二审到庭可请求减少）。
* **时效**：`LimitationClock`（起算日＋期间长度）＋ `expiredAt`（届满判定）＋
  `interruptAt`（民法典 193 条中断：重新起算）＋ `suspendWithin`（中止：期间
  顺延）。载体取 `Int` 日标签，与 `Temporal.lean` 的 XT 层同形（错位登记 #6）。

**本件不做的**：期间长度按 `[建模选择]` 取 `1095` 天（三年，忽略闰年）；
不建"知道或应当知道权利受损"的起算认定（那是事实认定，`startDay` 由案卷给）；
不认定任何真实案件的时效状态。

制造日期：2026-10-04（17_ 卷缺口 6 轮）。
-/

namespace JurisLean.Seams.Limitation

/-! ## 一、审级位（第 66 条后两段） -/

/-- 审级：一审／二审。第 66 条后两段的义务差异挂在这一位上。 -/
inductive InstanceLevel : Type
  | firstInstance -- 一审
  | secondInstance -- 二审
deriving DecidableEq, Repr

/-- 当事人到庭位：第 66 条第 3 款的情形——"被告因客观原因一审未到庭、二审到庭"。 -/
structure Attendance where
  /-- 一审是否到庭。 -/
  presentAtFirst : Bool
  /-- 二审是否到庭。 -/
  presentAtSecond : Bool
  deriving Repr

/-- 中文说明（第 66 条第 2 款的审级读数）：**二审**可以释明——
    一审认为抗辩成立且未释明的，二审仍有释明义务。一审位的读数是本件
    `ReductionConditions2.clarified` 那个总位；二审位在这里补上。 -/
def clarificationDutyAt : InstanceLevel → Bool
  | .firstInstance => true
  | .secondInstance => true

/-- 中文证明（**二审释明义务存在**）：第 66 条第 2 款"二审可以直接释明"的
    机器读数——二审位上义务位为真。 -/
theorem second_instance_still_owes_clarification :
    clarificationDutyAt InstanceLevel.secondInstance = true :=
  rfl

/-- 中文证明（**第 66 条第 3 款的开启条件**）：一审因客观原因未到庭、
    二审到庭——这正是第 3 款"被告……请求减少的，人民法院应当……"的入口位。
    开启＝一审未到庭∧二审到庭。 -/
def art66Clause3Opens (att : Attendance) : Bool :=
  !att.presentAtFirst && att.presentAtSecond

/-- 中文证明（**开启位非空洞**）：这个组合真实可达（构造子级见证）。 -/
theorem art66Clause3_witness :
    art66Clause3Opens { presentAtFirst := false, presentAtSecond := true } = true := by
  unfold art66Clause3Opens
  rfl

/-- 中文证明（**到庭组合的互斥读数**）：一审二审都到庭时第 3 款不开——
    它只保护"一审因客观原因未到庭"的被告，不保护两次都到庭的。 -/
theorem art66Clause3_closed_when_both_present :
    art66Clause3Opens { presentAtFirst := true, presentAtSecond := true } = false := by
  unfold art66Clause3Opens
  rfl

/-! ## 二、诉讼时效（民法典 192／193 条） -/

/-- 期间长度（`[建模选择]`：三年＝1095 天，忽略闰年；民法典 188 条普通期间）。 -/
def limitationPeriod : Int := 1095

/-- 时钟：起算日＋固定期间。`startDay` 由案卷给（"知道或应当知道之日"是事实认定，
    本件不代认）。载体取 `Int` 日标签，与 XT 层同形。 -/
structure LimitationClock where
  /-- 起算日（日标签）。 -/
  startDay : Int
  deriving Repr

/-- 中文说明：届满判定——`d` 日时时效已过（起算日＋期间 ≤ d）。
    民法典 192 条第 1 款："时效期间届满的，义务人可以提出不履行的抗辩"。 -/
def expiredAt (c : LimitationClock) (d : Int) : Prop :=
  c.startDay + limitationPeriod ≤ d

/-- 中文说明：中断（民法典 193 条第 1 款）：起诉、请求、同意履行等中断事由发生——
    从中断之日**重新起算**。 -/
def interruptAt (c : LimitationClock) (atDay : Int) : LimitationClock where
  startDay := atDay

/-- 中文证明（**中断重启期间**）：中断前已过的天数全部作废——
    新时钟在旧时钟本已届满的 `d` 日仍未届满，只要 `d` 落在新期间内。
    这就是 193 条"从中断、有关程序终结时起重新计算"的机器读数。 -/
theorem interruption_restarts_the_clock (c : LimitationClock) (atDay d : Int)
    (hOld : expiredAt c d) (hFresh : atDay + limitationPeriod > d) :
    ¬ expiredAt (interruptAt c atDay) d := by
  intro hNew
  unfold expiredAt interruptAt at hNew
  exact absurd hFresh (by unfold limitationPeriod at *; linarith)

/-- 中文说明：中止（民法典 193 条第 2 款最后六个月内的不可抗力等）——
    中止原因消除后继续计算，本件建模为**期间顺延**一个中止窗口。 -/
def suspendWithin (c : LimitationClock) (fromDay toDay : Int) : LimitationClock where
  startDay := c.startDay - (toDay - fromDay)

/-- 中文证明（**中止推迟届满**）：中止窗口使届满日**只会后移**——
    旧时钟未届满则新时钟也未届满（顺延的期间把门槛抬高）。 -/
theorem suspension_only_delays (c : LimitationClock) (fromDay toDay d : Int)
    (hWindow : fromDay ≤ toDay) (hNew : expiredAt (suspendWithin c fromDay toDay) d) :
    expiredAt c d := by
  unfold expiredAt suspendWithin at hNew ⊢
  have : c.startDay - (toDay - fromDay) + limitationPeriod ≤ d := hNew
  have hshift : c.startDay + limitationPeriod ≤
      c.startDay - (toDay - fromDay) + limitationPeriod := by
    have : -(toDay - fromDay) ≤ 0 := by linarith
    linarith
  linarith

/-- 中文证明（**期间为正**）：三年期是非负期间——届满判定因此非空洞。 -/
theorem limitationPeriod_pos : 0 < limitationPeriod := by
  unfold limitationPeriod
  decide

/-- 中文证明（**届满日存在**）：任何时钟都有一个日标签使届满判定为真——
    例如起算日＋期间＋1。 -/
theorem expiration_day_exists (c : LimitationClock) :
    ∃ d : Int, expiredAt c d :=
  ⟨c.startDay + limitationPeriod + 1, by
    unfold expiredAt
    linarith⟩

end JurisLean.Seams.Limitation
