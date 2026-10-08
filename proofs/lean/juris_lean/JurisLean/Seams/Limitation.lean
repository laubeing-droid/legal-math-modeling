import Mathlib.Tactic
import JurisLean.Seams.Temporal

/-! # 诉讼时效与审级位（17_ 卷缺口 6：民法典 192／194／195 条的程序面 + 法释〔2023〕13号第 66 条后两段）

此前时效只有 `ClaimBasis.lean` 注释面的读法与两个构造子级见证
（时效抗辩 `:313`、同意履行 `:318`），没有起算／中断／中止／期间计算；
审级位完全空缺（`ReductionConditions2.lean` §五#3 自证：法释〔2023〕13号第 66 条后两段
"一审认为抗辩成立且未释明时**二审**可直接释明"无法表达，因为 `clarified`
只有一个不分审级的总位）。本件补这两格：

* **审级位**：`InstanceLevel`（一审／二审）＋ `presentAtSecond`（一审因客观原因
  未到庭、二审到庭）＋ `clarificationDutyAt`。**读法须收窄**：义务位对两个审级
  都取真，因此它**不表达**法释〔2023〕13号第 66 条后两段的审级差异；这一条由
  `clarification_duty_is_level_blind` 证出（该位对审级判定恒真）。
  真正有内容的是第 3 款的**入口位** `fashi13_art66Clause3Opens`（一审未到庭∧二审到庭）。
* **时效**：`LimitationClock`（起算日＋期间长度）＋ `expiredAt`（届满判定）＋
  `interruptAt`（民法典 195 条中断：重新起算）＋ 194 条中止面（`sixMonths`／
  `naturalExpiry`／`obstacleInLastSixMonths`／`suspensionExpiryAfter`：
  最后六个月门槛＋消除日起满六个月届满）。载体取 `Int` 日标签，与 `Temporal.lean`
  的 XT 层同形（错位登记 #6）。

**本件不做的**：期间长度按 `[建模选择]` 取 `1095` 天（三年，忽略闰年），六个月
取 `180` 天（同口径忽略大小月）；不建"知道或应当知道权利受损"的起算认定
（那是事实认定，`startDay` 由案卷给）；不认定任何真实案件的时效状态。

**修订登记（2026-10-08，审查指定修正）**：本件此前把 194 条中止建成"期间顺延
一个中止窗口"（`suspendWithin`），且不设"最后六个月内"门槛，两处与条文不同形
并在头注登记为已知偏差。审查裁定该简化不能成立：194 条的读数是**门槛**（障碍
发生在时效期间最后六个月内）＋**届满**（自中止原因消除之日起满六个月届满）。
本轮已按条文原样重建（删除 `suspendWithin`，新增上述 194 条四个定义与
`suspension_never_shortens`／`suspension_strictly_delays_when_inside`／
`obstacle_before_window_not_qualified`／`suspension_only_delays`／
`suspension_remaining_month_counterexample` 五条定理，其中反例定理对应审查指定的
"剩余一个月＋次日消除"对照）。**范围**：这一支只表达普通诉讼时效的中止；
保证期间（692 条第 2 款）不适用中止／中断，除斥等其他期间按各自法源，
本件不把六个月规则外推给它们。

制造日期：2026-10-04（17_ 卷缺口 6 轮）。
-/

namespace JurisLean.Seams.Limitation

/-! ## 一、审级位（法释〔2023〕13号第 66 条后两段） -/

/-- 审级：一审／二审。这一位在 `fashi13_art66Clause3Opens` 上产生差异（是否到过庭），
    在 `clarificationDutyAt` 上**不**产生差异——见 `clarification_duty_is_level_blind`。 -/
inductive InstanceLevel : Type
  | firstInstance -- 一审
  | secondInstance -- 二审
deriving DecidableEq, Repr

/-- 当事人到庭位：法释〔2023〕13号第 66 条第 3 款的情形——"被告因客观原因一审未到庭、二审到庭"。 -/
structure Attendance where
  /-- 一审是否到庭。 -/
  presentAtFirst : Bool
  /-- 二审是否到庭。 -/
  presentAtSecond : Bool
  deriving Repr

/-- 中文说明（法释〔2023〕13号第 66 条第 2 款的**弱化**读数）：把"有释明义务"做成一个位。
    本件把它定义为**两审级都取真**，所以它只说"义务存在"，不说"二审才有"或
    "两审不同"。一审位的具体读数是 `ReductionConditions2.clarified` 那个总位。 -/
def clarificationDutyAt : InstanceLevel → Bool
  | .firstInstance => true
  | .secondInstance => true

/-- 中文证明（**二审释明义务存在**）：法释〔2023〕13号第 66 条第 2 款"二审可以直接释明"的
    机器读数——二审位上义务位为真。**强度如实**：这条只是上一条定义在
    `secondInstance` 处的取值，它不含"仅二审"或"审级有别"的意思，
    那层意思由下面那条否证定理登记为**未表达**。 -/
theorem second_instance_still_owes_clarification :
    clarificationDutyAt InstanceLevel.secondInstance = true :=
  rfl

/-- 中文证明（**审级位对释明义务是盲的**）：`clarificationDutyAt` 对两个审级
    给出同一读数，因此法释〔2023〕13号第 66 条后两段里"**二审**可以直接释明并组织举证、质证、辩论"
    这一**审级差异**在本件未被表达。这是一条盲区登记，不是把该差异证否——
    它与 `ReductionConditions2.lean` §五#3 对旧件 `clarified` 总位的同一自证同形。 -/
theorem clarification_duty_is_level_blind (l : InstanceLevel) :
    clarificationDutyAt l = true := by
  cases l <;> rfl

/-- 中文证明（**法释〔2023〕13号第 66 条第 3 款的开启条件**）：一审因客观原因未到庭、
    二审到庭——这正是第 3 款"被告……请求减少的，人民法院应当……"的入口位。
    开启＝一审未到庭∧二审到庭。 -/
def fashi13_art66Clause3Opens (att : Attendance) : Bool :=
  !att.presentAtFirst && att.presentAtSecond

/-- 中文证明（**开启位非空洞**）：这个组合真实可达（构造子级见证）。 -/
theorem fashi13_art66Clause3_witness :
    fashi13_art66Clause3Opens { presentAtFirst := false, presentAtSecond := true } = true := by
  unfold fashi13_art66Clause3Opens
  rfl

/-- 中文证明（**到庭组合的互斥读数**）：一审二审都到庭时第 3 款不开——
    它只保护"一审因客观原因未到庭"的被告，不保护两次都到庭的。 -/
theorem fashi13_art66Clause3_closed_when_both_present :
    fashi13_art66Clause3Opens { presentAtFirst := true, presentAtSecond := true } = false := by
  unfold fashi13_art66Clause3Opens
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
    逐字对上；194／195 的条号归属 **`[一手已核]`**（2026-10-05 核验）——法院系统官网
    五源逐字互证一致：ahczzy.ahcourt.gov.cn（article 7907772）、hbwqfy.nmgfy.gov.cn
    （article 8902912）、kbsqfy.nmgfy.gov.cn（article 9307377）、hgns.hljcourt.gov.cn
    （detail.php?id=4589）、qthqzh.hljcourt.gov.cn（detail.php?id=1372）。194＝"在诉讼
    时效期间的最后六个月内，因下列障碍，不能行使请求权的，诉讼时效中止……自中止时效的
    原因消除之日起满六个月，诉讼时效期间届满"；195＝"有下列情形之一的，诉讼时效中断，
    从中断、有关程序终结时起，诉讼时效期间重新计算……"。尾账：国家法律法规数据库
    详情页带防重复提交签名、本环境未取到，立法机关一手页复核留待后补。条号错了要改的
    是引注，本件的数学体（顺延／重启）不受影响。 -/
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

/-- 中文说明：六个月（`[建模选择]`：180 天，与三年＝1095 天同口径忽略闰年与
    大小月；民法典 194 条的"六个月"，门槛与届满各用一次）。 -/
def sixMonths : Int := 180

/-- 中文说明：自然届满日——起算日＋期间（无中止／中断时的届满日标签）。 -/
def naturalExpiry (c : LimitationClock) : Int := c.startDay + limitationPeriod

/-- 中文说明：194 条**门槛**——障碍发生日落在时效期间的最后六个月内
    （自然届满日前六个月（含）至届满日（不含））。门槛外的障碍不合格：
    194 条不适用，届满保持自然届满日（`obstacle_before_window_not_qualified`；
    Python 侧同合同 fail-closed 分支）。 -/
def obstacleInLastSixMonths (c : LimitationClock) (onsetDay : Int) : Prop :=
  naturalExpiry c - sixMonths ≤ onsetDay ∧ onsetDay < naturalExpiry c

/-- 中文说明：194 条**届满**——合格中止下，自中止原因消除之日起满六个月，
    诉讼时效期间届满（194 条末句的机器读数）。**不是**冻结剩余长度后继续：
    剩余长度根本不进这个式子。 -/
def suspensionExpiryAfter (removedDay : Int) : Int := removedDay + sixMonths

/-- 中文证明（**中止不缩短期限**）：合格中止（门槛内发生、消除不早于发生）下，
    194 条届满日不早于自然届满日——中止只会推迟，从不提前。 -/
theorem suspension_never_shortens (c : LimitationClock) (onsetDay removedDay : Int)
    (hGate : obstacleInLastSixMonths c onsetDay) (hWindow : onsetDay ≤ removedDay) :
    naturalExpiry c ≤ suspensionExpiryAfter removedDay := by
  obtain ⟨h1, _⟩ := hGate
  simp only [naturalExpiry, suspensionExpiryAfter, sixMonths] at h1 ⊢
  linarith

/-- 中文证明（**门槛必要**）：障碍发生在最后六个月开始之前的不合格——194 条
    不给它六个月规则，届满不因之改变。 -/
theorem obstacle_before_window_not_qualified (c : LimitationClock) (onsetDay : Int)
    (h : onsetDay < naturalExpiry c - sixMonths) :
    ¬ obstacleInLastSixMonths c onsetDay := by
  intro hgate
  obtain ⟨h1, _⟩ := hgate
  linarith

/-- 中文证明（**不能只续算剩余**）：只要障碍严格进入最后六个月（不是恰好踩在
    六个月边界那一天开始），194 条届满日就**严格晚于**自然届满日——
    "冻结剩余长度续算"（届满停在自然届满日附近）与条文不同形。 -/
theorem suspension_strictly_delays_when_inside (c : LimitationClock)
    (onsetDay removedDay : Int)
    (hInside : naturalExpiry c - sixMonths < onsetDay) (hWindow : onsetDay ≤ removedDay) :
    naturalExpiry c < suspensionExpiryAfter removedDay := by
  simp only [naturalExpiry, suspensionExpiryAfter, sixMonths] at hInside ⊢
  linarith

/-- 中文证明（**中止推迟届满判定**）：合格中止下，按 194 条届满日已过
    （d ≥ 消除日＋六个月）蕴含按自然期间也已届满——与旧件同名定理同一方向：
    中止只把届满门槛往后挪。 -/
theorem suspension_only_delays (c : LimitationClock) (onsetDay removedDay d : Int)
    (hGate : obstacleInLastSixMonths c onsetDay) (hWindow : onsetDay ≤ removedDay)
    (hSusp : suspensionExpiryAfter removedDay ≤ d) : expiredAt c d := by
  have h := suspension_never_shortens c onsetDay removedDay hGate hWindow
  simp only [naturalExpiry, suspensionExpiryAfter, limitationPeriod] at h
  simp only [suspensionExpiryAfter] at hSusp
  simp only [expiredAt, limitationPeriod]
  linarith

/-- 中文证明（**反例：剩余一个月≠只续一个月**）：起算日 0、三年期，自然届满日
    1095。原期间只剩一个月（30 天）时（第 1065 天）发生合格障碍，次日（第 1066 天）
    消除——194 条读数给届满日 **1246**（消除日＋180）；既不是自然届满日 1095
    （"冻结续算"到原届满），也不是"续算剩余一个月"的 1096。这是 2026-10-08
    审查指定的对照反例，机器读数如下。 -/
theorem suspension_remaining_month_counterexample :
    obstacleInLastSixMonths { startDay := 0 } 1065
      ∧ suspensionExpiryAfter 1066 = 1246
      ∧ suspensionExpiryAfter 1066 ≠ naturalExpiry { startDay := 0 } := by
  unfold obstacleInLastSixMonths suspensionExpiryAfter naturalExpiry
    limitationPeriod sixMonths
  decide

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
