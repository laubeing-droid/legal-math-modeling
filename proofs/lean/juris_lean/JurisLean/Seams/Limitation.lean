import Mathlib.Tactic
import JurisLean.Seams.Temporal

/-! # 诉讼时效与审级位（17_ 卷缺口 6：民法典 192／194／195 条的程序面 + 第 66 条后两段）

此前时效只有 `ClaimBasis.lean` 注释面的读法与两个构造子级见证
（时效抗辩 `:313`、同意履行 `:318`），没有起算／中断／中止／期间计算；
审级位完全空缺（`ReductionConditions2.lean` §五#3 自证：第 66 条后两段
"一审认为抗辩成立且未释明时**二审**可直接释明"无法表达，因为 `clarified`
只有一个不分审级的总位）。本件补这两格：

* **审级位**：`InstanceLevel`（一审／二审）＋ `presentAtSecond`（一审因客观原因
  未到庭、二审到庭）＋ `clarificationDutyAt`。**读法须收窄**：义务位对两个审级
  都取真，因此它**不表达**第 66 条后两段的审级差异；这一条由
  `clarification_duty_is_level_blind` 证出（该位对审级判定恒真）。
  真正有内容的是第 3 款的**入口位** `art66Clause3Opens`（一审未到庭∧二审到庭）。
* **时效**：`LimitationClock`（起算日＋期间长度）＋ `expiredAt`（届满判定）＋
  `interruptAt`（民法典 195 条中断：重新起算）＋ `suspendWithin`（民法典 194 条
  中止：期间顺延）。载体取 `Int` 日标签，与 `Temporal.lean` 的 XT 层同形（错位登记 #6）。

**本件不做的**：期间长度按 `[建模选择]` 取 `1095` 天（三年，忽略闰年）；
不建"知道或应当知道权利受损"的起算认定（那是事实认定，`startDay` 由案卷给）；
不认定任何真实案件的时效状态。另有两处**已知与条文不同形**，在此登记而不是隐藏：
① 中止建模为"顺延整个中止窗口"，而第 194 条的读数是"自中止时效的原因消除之日起
**满六个月**届满"，两者不同形，本件不做六个月那支；
② 第 194 条要求障碍发生在"时效期间最后六个月内"，本件的 `suspendWithin` 不设
该时间窗检验，任何窗口都可顺延——比条文宽。

制造日期：2026-10-04（17_ 卷缺口 6 轮）。
-/

namespace JurisLean.Seams.Limitation

/-! ## 一、审级位（第 66 条后两段） -/

/-- 审级：一审／二审。这一位在 `art66Clause3Opens` 上产生差异（是否到过庭），
    在 `clarificationDutyAt` 上**不**产生差异——见 `clarification_duty_is_level_blind`。 -/
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

/-- 中文说明（第 66 条第 2 款的**弱化**读数）：把"有释明义务"做成一个位。
    本件把它定义为**两审级都取真**，所以它只说"义务存在"，不说"二审才有"或
    "两审不同"。一审位的具体读数是 `ReductionConditions2.clarified` 那个总位。 -/
def clarificationDutyAt : InstanceLevel → Bool
  | .firstInstance => true
  | .secondInstance => true

/-- 中文证明（**二审释明义务存在**）：第 66 条第 2 款"二审可以直接释明"的
    机器读数——二审位上义务位为真。**强度如实**：这条只是上一条定义在
    `secondInstance` 处的取值，它不含"仅二审"或"审级有别"的意思，
    那层意思由下面那条否证定理登记为**未表达**。 -/
theorem second_instance_still_owes_clarification :
    clarificationDutyAt InstanceLevel.secondInstance = true :=
  rfl

/-- 中文证明（**审级位对释明义务是盲的**）：`clarificationDutyAt` 对两个审级
    给出同一读数，因此第 66 条后两段里"**二审**可以直接释明并组织举证、质证、辩论"
    这一**审级差异**在本件未被表达。这是一条盲区登记，不是把该差异证否——
    它与 `ReductionConditions2.lean` §五#3 对旧件 `clarified` 总位的同一自证同形。 -/
theorem clarification_duty_is_level_blind (l : InstanceLevel) :
    clarificationDutyAt l = true := by
  cases l <;> rfl

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

/-! ## 二、诉讼时效（民法典 192／194／195 条） -/

/-- 期间长度（`[建模选择]`：三年＝1095 天，忽略闰年；民法典 188 条普通期间）。 -/
def limitationPeriod : Int := 1095

/-- 时钟：起算日＋固定期间。`startDay` 由案卷给（"知道或应当知道之日"是事实认定，
    本件不代认）。载体取 `Int` 日标签，与 XT 层同形。 -/
structure LimitationClock where
  /-- 起算日（日标签）。 -/
  startDay : Int
  deriving Repr

/-- 中文说明：届满判定——`d` 日时时效已过（起算日＋期间 ≤ d）。
    民法典第 192 条第 1 款逐字："诉讼时效期间届满的，义务人可以提出不履行义务的抗辩。"
    本件的 `expiredAt` 只判"届满"这一时点，不判抗辩是否被提出——后者是
    `ClaimBasis.lean` 的构造子面。 -/
def expiredAt (c : LimitationClock) (d : Int) : Prop :=
  c.startDay + limitationPeriod ≤ d

/-- 中文说明：中断（**民法典第 195 条**）：起诉、请求、同意履行等中断事由发生——
    从中断、有关程序终结时起**重新起算**。
    （纠错登记：本件此前把中断引作"193 条第 1 款"是**误引**。民法典第 193 条只有一句
    "人民法院不得主动适用诉讼时效的规定"，无第 1、2 款之分；同目录 `ClaimBasis.lean`
    对 193 条的用法才是正确读法。中断＝195 条，中止＝194 条。
    **档位**：192 条的引文已在仓内语料 `data/aaf_legal/yd_defense_limitation.csv:10-11`
    逐字对上；194／195 的条号归属在本环境**未能取到权威原文页**（两次外网抓取失败、
    仓内语料不含这两条），故记为 `[待一手核]`，不是 `[一手已核]`。条号错了要改的是引注，
    本件的数学体（顺延／重启）不受影响。 -/
def interruptAt (c : LimitationClock) (atDay : Int) : LimitationClock where
  startDay := atDay

/-- 中文证明（**中断重启期间**）：中断前已过的天数全部作废——
    新时钟在旧时钟本已届满的 `d` 日仍未届满，只要 `d` 落在新期间内。
    这就是第 195 条"从中断、有关程序终结时起，诉讼时效期间重新计算"的机器读数。 -/
theorem interruption_restarts_the_clock (c : LimitationClock) (atDay d : Int)
    (hOld : expiredAt c d) (hFresh : atDay + limitationPeriod > d) :
    ¬ expiredAt (interruptAt c atDay) d := by
  intro hNew
  unfold expiredAt interruptAt at hNew
  exact absurd hFresh (by unfold limitationPeriod at *; linarith)

/-- 中文说明：中止（**民法典第 194 条**）——该条要求在"诉讼时效期间的最后六个月内"
    发生不可抗力等障碍，且第 194 条末句的读数是"自中止时效的原因消除之日起**满六个月**
    诉讼时效期间届满"。本件不建那六个月，改为**期间顺延**一个中止窗口（起算日后移窗口
    长度）：这只保证"届满日后移"这一方向，比条文**宽**（不设最后六个月的时间窗检验），
    偏差已在头注登记，不靠措辞掩盖。 -/
def suspendWithin (c : LimitationClock) (fromDay toDay : Int) : LimitationClock where
  startDay := c.startDay + (toDay - fromDay)

/-- 中文证明（**中止推迟届满**）：中止窗口使届满日**只会后移**——
    旧时钟未届满则新时钟也未届满（顺延的期间把门槛抬高）。 -/
theorem suspension_only_delays (c : LimitationClock) (fromDay toDay d : Int)
    (hWindow : fromDay ≤ toDay) (hNew : expiredAt (suspendWithin c fromDay toDay) d) :
    expiredAt c d := by
  have h1 : (suspendWithin c fromDay toDay).startDay + limitationPeriod ≤ d := hNew
  unfold suspendWithin at h1
  unfold expiredAt
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
