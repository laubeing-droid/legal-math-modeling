import Mathlib.Tactic
import JurisLean.Seams.PayoffEquilibrium
import JurisLean.Seams.UnifiedFourteenFamilies
import JurisLean.Seams.UnifiedNeedlesGap05
import JurisLean.Seams.Temporal

/-!
# W1-13 收益编码链＋XT 逐规则使用点（UnifiedPayoffChain）

本件承接 Z1 审计（`docs/full-math/NEEDLE_STRENGTH_AUDIT.md` §一）钉出的两针差额：

- **针 28（I:782，S4 `legal_payoff_preserved`）**：旧交付
  `Seams/UnifiedNeedlesS4.lean:244` 的法律收益侧只是旧锚
  `PayoffEquilibrium.lean:224`（固定法律 status 同余）的保地位改名实例化；审计判
  **差额**——"未建立'实际后果现金流→成本→偏好积分→法律收益'的编码保持链；
  偏好积分结构整个缺失，收益与现金流两条保持互相独立"。
- **针 48（I:802，XT `legal_time_nonanticipation`）**：旧交付
  `Seams/UnifiedNeedlesXT.lean:71` 以 `hview` 外挂前提＋`:88` 一个定义级样例
  （`viewEval`）；审计判**差额**——"'逐规则使用点证明'未闭合……无任何实际规则体经
  lawView 取值的证明接入——'实际 Eval'未出现"。

## 施工合同（唯一权威：`docs/spec/20261007-统一法律数学模型_附录I_Lean施工明细.md` §I.13 原句）

- **针 28（I:782）**："`PayoffEquilibrium.lean:224`仅固定法律status同余；拟实际后果
  现金流、成本及偏好积分的编码保持"。
- **针 48（I:802）**："`Temporal.lean:159`只trunc前缀等式；拟实际Eval经lawView只消费
  截止前信息，逐规则使用点证明"。

## 一、针 28 数学内容（人话）

四层结构与层间编码映射：

1. **现金流层**：`CashEntry`（期次＋后果种类 `Consequence`＋金额 ℚ＋登记位 Bool）；
   `PayFlow`（条目表＋声明地位＋卷宗位）。登记位是现金流层的簿记位，下游不读。
2. **成本层**：`costAt`（逐后果种类的金额归集——有限离散成本向量）；`costTotal`
   （成本向量直和）。编码映射＝逐条目按种类累加。
3. **偏好积分层**：`prefIntegral`——有限离散偏好向量（锚
   `PayoffEquilibrium.consequenceValuation`，逐角色 6 分量）上的加权和
   `Σ_k w(role,k) · costAt(k)`。
4. **法律收益读数层**：`payoffOf`（锚的卷宗读数，只经声明地位）与本件的
   `legalReading`（读数层对一般现金流的读法＝偏好积分）。

逐层保持定理：

- **现金流→成本**：总额保持（`costTotal = cashTotal`）＋像保持
  （非零成本分量的种类必来自某条目——`costAt_ne_zero_witness`；反方向被净额归集
  合法吞掉毛额，见 `net_aggregation_swallows_gross` 边界见证）＋簿记位重写不变
  （`flipTags_preserves_costs`）。
- **成本→偏好积分**：同变（加一条现金流条目 ⇒ 积分恰好移动
  `w(role,kind)·amount`——`prefIntegral_cons`）＋同余（成本向量相等 ⇒ 积分相等）。
- **偏好积分→法律收益读数**：在地位向量（`statusFlow`，逐声明后果各一条单位条目）
  上积分恒等于锚读数（`statusIntegral_eq_payoff`，4 地位×2 角色全部 8 格推导，不是
  断言）；读数对卷宗位盲（消费锚 `payoff_determined_by_status`）。
- **端到端**：现金流簿记重写整链传播到读数（`cash_rewrite_propagates_to_reading`）；
  现金流改变⇒读数同变（`legal_reading_cons_covariance`）；单种类非零权重时反射
  （`legal_reading_single_kind_reflection`）。
- **反例**：地位投影丢现金流（同地位、读数不同——旧 status 同余的保持对链条其余
  层零约束，`old_status_congruence_and_independent_cash` 用锚定理＋本件反例把
  "互相独立"钉成构造性合取）；丢种类的成本编码断链（`dropped_kind_breaks_total`）。

## 二、针 48 数学内容（人话）

- **载体**：带日期材料事件账 `EvLedger = List (Int × Atom)`（Int＝epoch 日，沿
  `Temporal` 载体）；`lawView := trunc`（消费 `Temporal.lean:119` 的截断视图）；
  `occursBy`（材料是否经视图在卷）；`lawDocket`（把视图读数装回真实 `CaseDocket`
  的 14 族材料字段——共享量与程序记录沿用满料见证案）；`evalAt`/`ruleFiresAt`
  （真实规则体求值：`closureAt (hornOf ·)` 上的原子可导性——消费
  `UnifiedFourteenFamilies` 的 29 条规则网络与 `UnifiedNeedlesGap05` 的
  `rule_fires_of_materials`）。
- **逐规则使用点**（非 hview 外挂、非定义级样例）：对三条真实规则 R01（L01 借贷
  `ruleLoanEntitlement`）、R23（L11 行政 `ruleAdminDefects`）、R19（L06 继承中止
  `ruleStaySuccession`）：
  (i) 每个前提材料的案卷读数＝视图读数（`materialHolds_via_view` 在使用点逐前提
  discharge——`r01/r23/r19_use_point`）；
  (ii) 规则体求值对未来盲（`r01/r23/r19_eval_nonanticipating`：追加未来事件不改
  求值，证明走视图等式→案卷等式→闭包等式，不是前提）；
  (iii) 满料账上三条规则真的经视图开火（`r01/r23/r19_fires_witness`）。
- **越窗消费被拒**：未来-only 账上三条规则都不能开火（避开坏集模型见证，
  `conclusion_blocked_of_premise_missing`＋三条内核级阻断检查表）；且旧锚的 hview
  前提在这里是**定理**（`eval_is_view_valued`：实际求值恒等于取视图后的求值）。
- **时点动力学见证**：同一账本，合同材料 150 日才到达——截止 100 不开火、截止 160
  开火（`late_material_blocked_before_cut`）：改变读数的是时点，不是信息本身。

## 三、与旧锚的差异（Z1 差额逐条清算）

| 差额点（Z1 原文） | 旧交付 | 本件 |
|---|---|---|
| 针 28：偏好积分结构整个缺失 | 无此载体 | 有限离散偏好向量（锚估值表）＋加权积分＋同变/同余/反射 |
| 针 28：编码保持链未建立 | 现金流保持与收益保持两条独立合取 | 现金流→成本→积分→读数四层编码映射＋逐层保持＋端到端同变/反射＋整链传播定理 |
| 针 48：hview 外挂前提 | `hview : ∀ evs, eval evs = k (trunc asOf evs)` 是假设 | `eval_is_view_valued`：对真实规则网络求值是定理 |
| 针 48：无实际规则体接入 | `viewEval` 定义级样例 | R01/R23/R19 三条已绿规则体逐前提使用点＋求值未来盲＋开火/阻断 |

旧锚件（PayoffEquilibrium/UnifiedNeedlesS4/UnifiedNeedlesXT/Gap05）一律原样保留；
本件 import 消费之，不修改、不重述。

## 四、开放点（如实声明）

- 针 28 的估值权重＝锚的 [代拟稿] 声明表（无经验校准）；`legalReading` 对一般现金流
  的读法＝偏好积分是本件声明的模型选择，不冒称法定算法。像保持只有"非零成本⇒存在
  条目"方向；反方向被净额归集合法失败（毛额抵消，见边界见证定理）。
- 针 48 的逐前提使用点只对 R01/R23/R19 三条全材料前提规则逐字面展开；带推导原子
  前提的规则（R04/R09/R10/R20/R21/R29 等）由原子级一般式（`evalAt_append_future`）
  覆盖，不逐条展开。账本若带非材料原子事件，该事件对案卷读数惰性（任何材料字段都
  不读它）；本件不强制账本良构。asOf 是 Int epoch 日，日历换算属针 50 载体。
- 数值凡承自锚表处均为 [代拟稿]；无经验内容。

## 五、档位

零 `sorry`、零 `admit`、零自定义 `axiom`、零 `True` 逃避；语句位只写闭命题（无
`if`/`decide` 出现在定理语句）；`decide`/`rfl` 只用于闭式字面量与定义级归约；
金额一律 ℚ。按仓库边界约定，Lean 权威认定在 CI（CI_NOT_RUN，fail-closed）；
本机镜像试编译（仓外 scratch、真实依赖逐字复本＋预构建 Mathlib v4.30.0 oleans）
exit=0 见施工报告。
-/

namespace JurisLean.Seams.UnifiedPayoffChain

open JurisLean.Seams.PayoffEquilibrium
open JurisLean.Seams.UnifiedFourteenFamilies
open JurisLean.Seams.UnifiedNeedlesGap05
open JurisLean.Seams.SourceNorms

open Atom

/-! ## 一、针 28：收益编码链（四层载体） -/

section Needle28PayoffChain

/-- 现金流条目：期次＋后果种类（锚 `Consequence` 六分类）＋金额（ℚ，符号分向）＋
    登记位（现金流层簿记位，下游层一律不读）。 -/
structure CashEntry where
  period : Nat
  kind : Consequence
  amount : ℚ
  ledgerTag : Bool
deriving DecidableEq

/-- 实际后果现金流记录：条目表＋声明法律地位＋卷宗登记位（沿
    `UnifiedNeedlesS4.CashFlow` 的形状，种类挂到锚的后果分类上）。 -/
structure PayFlow where
  entries : List CashEntry
  declaredStatus : LegalStatus
  docket : Bool
deriving DecidableEq

/-- 有限离散后果种类全表（六分量，与锚估值表逐项对应）。 -/
def allCons : List Consequence :=
  [Consequence.costBurdenLoser, Consequence.costBurdenPartial, Consequence.costOwnOnDismiss,
    Consequence.noTitleNoCost, Consequence.enforcementAccess, Consequence.resJudicata]

/-- **层 2 编码映射**：成本层——逐后果种类归集金额（有限离散成本向量）。 -/
def costAt (es : List CashEntry) (k : Consequence) : ℚ :=
  es.foldr (fun e acc => if e.kind = k then e.amount + acc else acc) 0

/-- 成本向量直和（未加权总读数）。 -/
def costTotal (es : List CashEntry) : ℚ :=
  allCons.foldr (fun k acc => costAt es k + acc) 0

/-- 现金流层实际折算：逐条目求和（未加权）。 -/
def cashTotal (es : List CashEntry) : ℚ :=
  es.foldr (fun e acc => e.amount + acc) 0

/-- **层 3 编码映射**：偏好积分——有限离散偏好向量（锚 `consequenceValuation` 逐角色
    六分量）上的加权和 `Σ_k w(role,k) · costAt(k)`。 -/
def prefIntegral (role : Role) (es : List CashEntry) : ℚ :=
  allCons.foldr (fun k acc => consequenceValuation role k * costAt es k + acc) 0

/-- **层 4 读数层**：法律收益读数对一般现金流的读法＝偏好积分（本件声明的模型选择，
    见头注开放点）。 -/
def legalReading (role : Role) (fl : PayFlow) : ℚ := prefIntegral role fl.entries

/-- 地位向量：某声明地位所挂载的每一项后果各生成一条单位条目（层 4 锚读数的
    标准原像）。 -/
def statusFlow (st : LegalStatus) : PayFlow where
  entries := (declaredConsequences st).map
    (fun k => { period := 0, kind := k, amount := 1, ledgerTag := false })
  declaredStatus := st
  docket := false

/-! ### 层 1→2 保持：总额、像、簿记位 -/

theorem cashTotal_cons (e : CashEntry) (es : List CashEntry) :
    cashTotal (e :: es) = e.amount + cashTotal es := rfl

theorem costAt_cons (e : CashEntry) (es : List CashEntry) (k : Consequence) :
    costAt (e :: es) k = if e.kind = k then e.amount + costAt es k else costAt es k := rfl

/-- 加法分配（任意种类表上的列表引理，未加权版）。 -/
theorem foldr_add_distrib (ks : List Consequence) (x y : Consequence → ℚ) :
    ks.foldr (fun k acc => (x k + y k) + acc) 0
      = ks.foldr (fun k acc => x k + acc) 0 + ks.foldr (fun k acc => y k + acc) 0 := by
  induction ks with
  | nil => simp
  | cons k ks ih => simp only [List.foldr_cons]; rw [ih]; ring

/-- 加权分配（任意种类表上的列表引理）。 -/
theorem foldr_w_distrib (ks : List Consequence) (w : Consequence → ℚ) (x y : Consequence → ℚ) :
    ks.foldr (fun k acc => w k * (x k + y k) + acc) 0
      = ks.foldr (fun k acc => w k * x k + acc) 0
        + ks.foldr (fun k acc => w k * y k + acc) 0 := by
  induction ks with
  | nil => simp
  | cons k ks ih => simp only [List.foldr_cons]; rw [ih]; ring

/-- 未加权 δ-求和：六种类各恰一次，逐种类单点求和读出该点值。 -/
theorem allCons_delta (k : Consequence) (a : ℚ) :
    allCons.foldr (fun j acc => (if k = j then a else 0) + acc) 0 = a := by
  cases k <;> simp [allCons]

/-- 加权 δ-求和：同上（任意权向量）。 -/
theorem allCons_w_delta (w : Consequence → ℚ) (k : Consequence) (a : ℚ) :
    allCons.foldr (fun j acc => w j * (if k = j then a else 0) + acc) 0 = w k * a := by
  cases k <;> simp [allCons]

/-- 成本层逐头加法（未加权总额沿条目表线性和）。 -/
theorem costTotal_cons (e : CashEntry) (es : List CashEntry) :
    costTotal (e :: es) = costTotal es + e.amount := by
  have hcost : ∀ k : Consequence,
      costAt (e :: es) k = costAt es k + (if e.kind = k then e.amount else 0) := by
    intro k
    rw [costAt_cons e es k]
    by_cases hk : e.kind = k
    · rw [if_pos hk, if_pos hk]; ring
    · rw [if_neg hk, if_neg hk]; ring
  have hsplit := foldr_add_distrib allCons (fun k => costAt es k)
    (fun k => if e.kind = k then e.amount else 0)
  have hdelta := allCons_delta e.kind e.amount
  unfold costTotal
  simp only [hcost]
  rw [hsplit, hdelta]

/-- **层 1→2 总额保持**：成本归集编码保持现金总折算。 -/
theorem costTotal_eq_cashTotal (es : List CashEntry) : costTotal es = cashTotal es := by
  induction es with
  | nil => norm_num [costTotal, cashTotal, costAt, allCons]
  | cons e es ih => rw [costTotal_cons, cashTotal_cons, ih]; ring

/-- **层 1→2 像保持**：非零成本分量的种类必来自该种类的一条现金流条目。 -/
theorem costAt_ne_zero_witness (es : List CashEntry) (k : Consequence)
    (h : costAt es k ≠ 0) : ∃ e ∈ es, e.kind = k := by
  induction es with
  | nil => exact absurd rfl h
  | cons e es ih =>
      by_cases hk : e.kind = k
      · exact ⟨e, List.mem_cons_self, hk⟩
      · have h' : costAt es k ≠ 0 := by
          intro hz
          rw [costAt_cons, if_neg hk, hz] at h
          exact h rfl
        obtain ⟨e', hem, hkind⟩ := ih h'
        exact ⟨e', List.mem_cons_of_mem _ hem, hkind⟩

/-- 像保持的反方向边界见证：净额归集合法吞掉毛额——同种类 +5 与 -5 两条真实条目
    归集成 0。这不是编码缺陷，是归集的语义（成本层看净额不看毛额）；故像保持只声明
    单方向。 -/
theorem net_aggregation_swallows_gross :
    ∃ es : List CashEntry, es.length = 2 ∧ cashTotal es = 0 ∧
      ∀ k, costAt es k = 0 := by
  refine ⟨[{ period := 0, kind := .costBurdenLoser, amount := 5, ledgerTag := false },
      { period := 1, kind := .costBurdenLoser, amount := -5, ledgerTag := true }], rfl,
    by norm_num [cashTotal], ?_⟩
  intro k
  cases k <;> simp [costAt]

/-- 现金层簿记重写：翻转全部登记位（条目身份其余不动）。 -/
def flipTags : List CashEntry → List CashEntry
  | [] => []
  | e :: es => { e with ledgerTag := !e.ledgerTag } :: flipTags es

/-- 种类与金额相同、尾部成本相同的两条目在成本编码下不可分（登记位不进编码）。 -/
theorem costAt_cons_of (e e' : CashEntry) (es es' : List CashEntry) (k : Consequence)
    (hk : e'.kind = e.kind) (ha : e'.amount = e.amount) (ht : costAt es' k = costAt es k) :
    costAt (e' :: es') k = costAt (e :: es) k := by
  simp only [costAt_cons]
  rw [hk, ha, ht]

/-- **层 1 簿记重写→层 2 保持**：登记位翻转不动成本向量。 -/
theorem flipTags_preserves_costs (es : List CashEntry) (k : Consequence) :
    costAt (flipTags es) k = costAt es k := by
  induction es with
  | nil => rfl
  | cons e es ih =>
      exact costAt_cons_of e { e with ledgerTag := !e.ledgerTag } es (flipTags es) k
        rfl rfl ih

/-! ### 层 2→3 保持：同余、同变 -/

/-- **层 2→3 同余**：成本向量相等 ⇒ 偏好积分相等。 -/
theorem prefIntegral_congr (role : Role) (es es' : List CashEntry)
    (h : ∀ k : Consequence, costAt es k = costAt es' k) :
    prefIntegral role es = prefIntegral role es' := by
  unfold prefIntegral
  simp only [h]

/-- **层 2→3 同变**：追加一条现金流条目，积分恰好移动该种类权重×金额
    （现金流改变沿成本编码进入积分层）。 -/
theorem prefIntegral_cons (role : Role) (e : CashEntry) (es : List CashEntry) :
    prefIntegral role (e :: es) = prefIntegral role es
      + consequenceValuation role e.kind * e.amount := by
  have hcost : ∀ k : Consequence,
      costAt (e :: es) k = costAt es k + (if e.kind = k then e.amount else 0) := by
    intro k
    rw [costAt_cons e es k]
    by_cases hk : e.kind = k
    · rw [if_pos hk, if_pos hk]; ring
    · rw [if_neg hk, if_neg hk]; ring
  have hsplit := foldr_w_distrib allCons (consequenceValuation role)
    (fun k => costAt es k) (fun k => if e.kind = k then e.amount else 0)
  have hdelta := allCons_w_delta (consequenceValuation role) e.kind e.amount
  unfold prefIntegral
  simp only [hcost]
  rw [hsplit, hdelta]

/-! ### 层 3→4 保持：地位向量上的读数一致 -/

/-- **层 3→4 读数保持**：地位向量（逐声明后果各一条单位条目）的偏好积分恒等于
    锚的法律收益读数——4 地位 × 2 角色全部 8 格推导得出（不是断言的网格）。 -/
theorem statusIntegral_eq_payoff (role : Role) (st : LegalStatus) (d : Bool) :
    prefIntegral role (statusFlow st).entries = payoffOf role ⟨st, d⟩ := by
  cases role <;> cases st <;>
    simp [prefIntegral, costAt, statusFlow, allCons, declaredConsequences,
      consequenceValuation, payoffOf, statusOf, legal_payoff]

/-- 读数层对卷宗位盲（消费锚 `PayoffEquilibrium.payoff_determined_by_status`）。 -/
theorem reading_layer_docket_blind (role : Role) (st : LegalStatus) (d₁ d₂ : Bool) :
    payoffOf role ⟨st, d₁⟩ = payoffOf role ⟨st, d₂⟩ :=
  JurisLean.Seams.PayoffEquilibrium.payoff_determined_by_status role _ _ rfl

/-! ### 端到端：同变、反射、整链传播 -/

/-- **端到端同变**：现金流追加一条条目 ⇒ 法律收益读数恰好移动权重×金额。 -/
theorem legal_reading_cons_covariance (role : Role) (e : CashEntry) (fl : PayFlow) :
    legalReading role { fl with entries := e :: fl.entries }
      = legalReading role fl + consequenceValuation role e.kind * e.amount :=
  prefIntegral_cons role e fl.entries

/-- **端到端反射（单种类非零权重）**：同种类两条目、积分读数相等且该种类权重非零
    ⇒ 金额相等。权重为零的种类反射失败（见下方反例）。 -/
theorem legal_reading_single_kind_reflection (role : Role) (es : List CashEntry)
    (e e' : CashEntry) (hk : e.kind = e'.kind)
    (hw : consequenceValuation role e.kind ≠ 0)
    (h : legalReading role ⟨e :: es, LegalStatus.upheld, false⟩
      = legalReading role ⟨e' :: es, LegalStatus.upheld, false⟩) :
    e.amount = e'.amount := by
  rw [legal_reading_cons_covariance role e ⟨es, LegalStatus.upheld, false⟩,
    legal_reading_cons_covariance role e' ⟨es, LegalStatus.upheld, false⟩] at h
  have h2 : consequenceValuation role e.kind * e.amount
      = consequenceValuation role e.kind * e'.amount := by
    rw [hk] at h ⊢
    linarith [h]
  exact mul_left_cancel₀ hw h2

/-- **整链传播**：现金流层簿记重写 ⇒ 成本向量不动 ⇒ 积分不动 ⇒ 读数不动
    （旧交付的两条独立保持在此成为一条链的三段推导）。 -/
theorem cash_rewrite_propagates_to_reading (role : Role) (fl : PayFlow) :
    legalReading role { fl with entries := flipTags fl.entries } = legalReading role fl :=
  prefIntegral_congr role _ _ (fun k => flipTags_preserves_costs fl.entries k)

/-! ### 反例组 -/

/-- 加倍地位向量：同声明地位、每条单位条目金额翻倍。 -/
def doubledStatusFlow (st : LegalStatus) : PayFlow where
  entries := (statusFlow st).entries.map (fun e => { e with amount := 2 * e.amount })
  declaredStatus := st
  docket := (statusFlow st).docket

/-- **反例一（地位投影丢现金流）**：同声明地位、同卷宗位（旧 status 同余编码完全
    不可分）而法律读数不同——地位投影编码丢掉实际现金流信息，链条在它那里断。 -/
theorem status_projection_drops_cash :
    ∃ fl₁ fl₂ : PayFlow, fl₁.declaredStatus = fl₂.declaredStatus ∧ fl₁.docket = fl₂.docket ∧
      legalReading Role.claimant fl₁ ≠ legalReading Role.claimant fl₂ := by
  refine ⟨statusFlow LegalStatus.upheld, doubledStatusFlow LegalStatus.upheld, rfl, rfl, ?_⟩
  intro h
  have h7 : legalReading Role.claimant (statusFlow LegalStatus.upheld) = 7 := by
    simp [legalReading, prefIntegral, costAt, statusFlow, allCons,
      declaredConsequences, consequenceValuation] <;> norm_num
  have h14 : legalReading Role.claimant (doubledStatusFlow LegalStatus.upheld) = 14 := by
    simp [legalReading, prefIntegral, costAt, statusFlow, doubledStatusFlow, allCons,
      declaredConsequences, consequenceValuation] <;> norm_num
  rw [h7, h14] at h
  exact absurd h (by norm_num)

/-- **反例二（丢种类的成本编码断链）**：把某一类后果从成本编码里挖掉后，两个现金总
    额不同的流在该编码下不可分——层 1→2 的总额保持对它失效。 -/
def costAtDropped (es : List CashEntry) (k : Consequence) : ℚ :=
  if k = Consequence.resJudicata then 0 else costAt es k

theorem dropped_kind_breaks_total :
    ∃ es₁ es₂ : List CashEntry, (∀ k, costAtDropped es₁ k = costAtDropped es₂ k) ∧
      cashTotal es₁ ≠ cashTotal es₂ := by
  refine ⟨[{ period := 0, kind := .resJudicata, amount := 5, ledgerTag := false }], [],
    ?_, ?_⟩
  · intro k
    cases k <;> simp [costAtDropped, costAt]
  · norm_num [cashTotal]

/-- **旧锚地位同余与其对现金流的零约束（构造性合取）**：左支＝锚定理原样实例化
    （保地位改名不动收益——仍然成立）；右支＝同地位两流读数不同。二者合取正是
    Z1 所指"收益与现金流两条保持互相独立"的修复形态：左支不再被冒称为链条。 -/
theorem old_status_congruence_and_independent_cash :
    (∀ (f : Case → Case), (∀ c, statusOf (f c) = statusOf c) → ∀ (role : Role) (c : Case),
        payoffOf role (f c) = payoffOf role c) ∧
    (∃ fl₁ fl₂ : PayFlow, fl₁.declaredStatus = fl₂.declaredStatus ∧
      fl₁.docket = fl₂.docket ∧
      legalReading Role.claimant fl₁ ≠ legalReading Role.claimant fl₂) :=
  ⟨fun f h role c => JurisLean.Seams.PayoffEquilibrium.legal_payoff_preserved h role c,
    status_projection_drops_cash⟩

/-- **反射前提不可去（零权重反例）**：申请人侧 `noTitleNoCost` 权重为 0——同种类
    两条目金额 5 与 7 的积分读数相等而金额不等，反射在零权重种类上失效。 -/
theorem reflection_fails_at_zero_weight :
    ∃ (es : List CashEntry) (e e' : CashEntry), e.kind = e'.kind ∧
      consequenceValuation Role.claimant e.kind = 0 ∧
      legalReading Role.claimant ⟨e :: es, LegalStatus.upheld, false⟩
        = legalReading Role.claimant ⟨e' :: es, LegalStatus.upheld, false⟩ ∧
      e.amount ≠ e'.amount := by
  refine ⟨[], { period := 0, kind := .noTitleNoCost, amount := 5, ledgerTag := false },
    { period := 0, kind := .noTitleNoCost, amount := 7, ledgerTag := false }, rfl, rfl, ?_,
    by norm_num⟩
  simp [legalReading, prefIntegral, costAt, allCons, consequenceValuation]

/-! ### 见证读数 -/

/-- 见证现金流：胜诉方负担折价 10、执行可得 2、既判力 5 三笔（[代拟稿] 数值承锚表
    权重，金额为演示）。 -/
def witnessEntries : List CashEntry :=
  [{ period := 0, kind := .costBurdenLoser, amount := 10, ledgerTag := false },
    { period := 1, kind := .enforcementAccess, amount := 2, ledgerTag := true },
    { period := 2, kind := .resJudicata, amount := 5, ledgerTag := false }]

theorem witness_readouts :
    cashTotal witnessEntries = 17 ∧ costTotal witnessEntries = 17 ∧
      prefIntegral Role.claimant witnessEntries = 44 ∧
      prefIntegral Role.respondent witnessEntries = -44 := by
  simp [cashTotal, costTotal, prefIntegral, costAt, allCons, witnessEntries,
    consequenceValuation] <;> norm_num

/-- **针 28 旗舰（S4，I:782 编码保持链收口）**：四层结构＋层间编码映射＋逐层保持
    （现金流→成本总额/像/簿记位；成本→积分同余/同变；积分→读数在地位向量上恒等）＋
    端到端同变与单种类反射＋整链传播＋三组反例（地位投影丢现金流、丢种类断链、
    零权重反射失效）＋见证读数。 -/
theorem legal_payoff_preserved :
    (∀ es : List CashEntry, costTotal es = cashTotal es) ∧
    (∀ (es : List CashEntry) (k : Consequence), costAt es k ≠ 0 → ∃ e ∈ es, e.kind = k) ∧
    (∀ (role : Role) (es es' : List CashEntry), (∀ k, costAt es k = costAt es' k) →
        prefIntegral role es = prefIntegral role es') ∧
    (∀ (role : Role) (e : CashEntry) (es : List CashEntry),
        prefIntegral role (e :: es) = prefIntegral role es
          + consequenceValuation role e.kind * e.amount) ∧
    (∀ (role : Role) (st : LegalStatus) (d : Bool),
        prefIntegral role (statusFlow st).entries = payoffOf role ⟨st, d⟩) ∧
    (∀ (role : Role) (fl : PayFlow) (e : CashEntry),
        legalReading role { fl with entries := e :: fl.entries }
          = legalReading role fl + consequenceValuation role e.kind * e.amount) ∧
    (∀ (role : Role) (es : List CashEntry) (e e' : CashEntry), e.kind = e'.kind →
        consequenceValuation role e.kind ≠ 0 →
        legalReading role ⟨e :: es, LegalStatus.upheld, false⟩
          = legalReading role ⟨e' :: es, LegalStatus.upheld, false⟩ → e.amount = e'.amount) ∧
    (∀ (role : Role) (fl : PayFlow),
        legalReading role { fl with entries := flipTags fl.entries } = legalReading role fl) ∧
    (∃ (fl₁ fl₂ : PayFlow), fl₁.declaredStatus = fl₂.declaredStatus ∧
        fl₁.docket = fl₂.docket ∧
        legalReading Role.claimant fl₁ ≠ legalReading Role.claimant fl₂) ∧
    (∃ (es₁ es₂ : List CashEntry), (∀ k, costAtDropped es₁ k = costAtDropped es₂ k) ∧
        cashTotal es₁ ≠ cashTotal es₂) ∧
    (cashTotal witnessEntries = 17 ∧ prefIntegral Role.claimant witnessEntries = 44 ∧
      prefIntegral Role.respondent witnessEntries = -44) :=
  ⟨fun es => costTotal_eq_cashTotal es,
    fun es k => costAt_ne_zero_witness es k,
    fun role es es' => prefIntegral_congr role es es',
    fun role e es => prefIntegral_cons role e es,
    fun role st d => statusIntegral_eq_payoff role st d,
    fun role fl e => legal_reading_cons_covariance role e fl,
    fun role es e e' => legal_reading_single_kind_reflection role es e e',
    fun role fl => cash_rewrite_propagates_to_reading role fl,
    status_projection_drops_cash,
    dropped_kind_breaks_total,
    ⟨witness_readouts.1, witness_readouts.2.2.1, witness_readouts.2.2.2⟩⟩

end Needle28PayoffChain

/-! ## 二、针 48：XT 逐规则 lawView 使用点 -/

section Needle48LawView

/-- 带日期材料事件账：每条事件（日期，材料原子）声明该材料原子于该日在卷。
    Int＝epoch 日（沿 `Temporal` 载体）。非材料原子事件对案卷读数惰性（见头注）。 -/
abbrev EvLedger := List (Int × Atom)

/-- lawView＝`Temporal.trunc` 截断视图（消费 `Temporal.lean:119`）：只保留
    day ≤ asOf 的事件。 -/
def lawView (asOf : Int) (evs : EvLedger) : EvLedger :=
  JurisLean.Seams.Temporal.trunc asOf evs

/-- 材料原子经视图在卷读数：某材料原子是否在截断视图里被声明。 -/
def occursBy (asOf : Int) (evs : EvLedger) (a : Atom) : Bool :=
  decide (a ∈ (lawView asOf evs).map Prod.snd)

/-- 材料原子标记（消费 `UnifiedNeedlesGap05.allMaterialAtomList` 的 57 原子规范表）。 -/
def isMaterialAtom (a : Atom) : Bool := decide (a ∈ allMaterialAtomList)

/-- **lawDocket**：把 as-of 视图读数装回真实 `CaseDocket`——共享量与程序记录沿用
    满料见证案，14 族材料字段逐项改为经视图的在卷读数。规则网络（29 条）不变：
    `hornOf` 对任何案卷都取同一规则表，材料是个案、规则是制度。 -/
def lawDocket (evs : EvLedger) (asOf : Int) : CaseDocket :=
  { fullDocket with
    m01 := { fullDocket.m01 with
      contractSigned := occursBy asOf evs .matContractSigned
      bankSettlementMatched := occursBy asOf evs .matBankSettlementMatched
      reconciliationUnpaid := occursBy asOf evs .matReconciliationUnpaid
      guaranteeByGOpen := occursBy asOf evs .matGuaranteeByGOpen }
    m02 := { fullDocket.m02 with
      registryD := occursBy asOf evs .matRegistryD
      mortgageRegistered := occursBy asOf evs .matMortgageRegistered
      otherTitles := occursBy asOf evs .matOtherTitles
      realizationRecord := occursBy asOf evs .matRealizationRecord }
    m03 := { fullDocket.m03 with
      workInstruction := occursBy asOf evs .matWorkInstruction
      damageCorroboration := occursBy asOf evs .matDamageCorroboration
      notWorkInjury := occursBy asOf evs .matNotWorkInjury }
    m04 := { fullDocket.m04 with
      treatmentAtM := occursBy asOf evs .matTreatmentAtM
      recordsWithheld := occursBy asOf evs .matRecordsWithheld
      preExistingChecks := occursBy asOf evs .matPreExistingChecks }
    m05 := { fullDocket.m05 with
      samplingMatch := occursBy asOf evs .matSamplingMatch
      exceedance := occursBy asOf evs .matExceedance
      pondTesting := occursBy asOf evs .matPondTesting
      ecoCostDocs := occursBy asOf evs .matEcoCostDocs
      noExculpation := occursBy asOf evs .matNoExculpation
      inNewLawPeriod := occursBy asOf evs .matInNewLawPeriod }
    m06 := { fullDocket.m06 with
      marriageRegistered := occursBy asOf evs .matMarriageRegistered
      noSpousalJointBasis := occursBy asOf evs .matNoSpousalJointBasis
      cDeathRecord := occursBy asOf evs .matCDeathRecord
      heirIdentityOnFile := occursBy asOf evs .matHeirIdentityOnFile
      heirsNotYetJoined := occursBy asOf evs .matHeirsNotYetJoined }
    m07 := { fullDocket.m07 with
      wageBasisOnFile := occursBy asOf evs .matWageBasisOnFile
      overtimeUnsupported := occursBy asOf evs .matOvertimeUnsupported }
    m08 := { fullDocket.m08 with
      separateAccounts := occursBy asOf evs .matSeparateAccounts
      insolvencyShown := occursBy asOf evs .matInsolvencyShown
      acceptanceDecided := occursBy asOf evs .matAcceptanceDecided }
    m09 := { fullDocket.m09 with
      creationChain := occursBy asOf evs .matCreationChain
      licenseExpired := occursBy asOf evs .matLicenseExpired
      postTermUse := occursBy asOf evs .matPostTermUse
      noWillfulnessGravity := occursBy asOf evs .matNoWillfulnessGravity }
    m10 := { fullDocket.m10 with
      loanAcquisitionProven := occursBy asOf evs .matLoanAcquisitionProven
      intentOnlyConfession := occursBy asOf evs .matIntentOnlyConfession
      genuineBusinessShown := occursBy asOf evs .matGenuineBusinessShown
      criminalTrialDone := occursBy asOf evs .matCriminalTrialDone }
    m11 := { fullDocket.m11 with
      penaltyServedWithBasis := occursBy asOf evs .matPenaltyServedWithBasis
      factualDisputes := occursBy asOf evs .matFactualDisputes
      hearingMissed := occursBy asOf evs .matHearingMissed
      recordContradictions := occursBy asOf evs .matRecordContradictions }
    m12 := { fullDocket.m12 with
      detentionX := occursBy asOf evs .matDetentionX
      reviewFiledInTime := occursBy asOf evs .matReviewFiledInTime
      returnDamageRecords := occursBy asOf evs .matReturnDamageRecords
      remoteProfitUnsupported := occursBy asOf evs .matRemoteProfitUnsupported
      differentAct := occursBy asOf evs .matDifferentAct }
    m13 := { fullDocket.m13 with
      stayEventsKept := occursBy asOf evs .matStayEventsKept
      priorCarJudgment := occursBy asOf evs .matPriorCarJudgment
      namedErrorAlleged := occursBy asOf evs .matNamedErrorAlleged
      dependentClaimFiled := occursBy asOf evs .matDependentClaimFiled
      priorCaseUnconcluded := occursBy asOf evs .matPriorCaseUnconcluded }
    m14 := { fullDocket.m14 with
      maritimeContractWithClause := occursBy asOf evs .matMaritimeContractWithClause
      carrierCustody := occursBy asOf evs .matCarrierCustody
      cargoDamage := occursBy asOf evs .matCargoDamage
      exemptionMaterials := occursBy asOf evs .matExemptionMaterials
      nQualified := occursBy asOf evs .matNQualified } }

/-- **使用点核心引理**：材料原子在 lawDocket 的案卷读数＝其经视图的在卷读数
    （逐原子使用点：规则体读材料的位置恰好看的是截断视图）。 -/
theorem materialHolds_via_view (a : Atom) (evs : EvLedger) (asOf : Int)
    (hmat : isMaterialAtom a = true) :
    materialHolds a (lawDocket evs asOf) = occursBy asOf evs a := by
  cases a <;> first | rfl | exact absurd hmat (by decide)

/-- 非材料原子（推导/失败原子）在任何案卷的 `materialHolds` 读数恒假
    （它们不是输入材料——消费 `materialHolds` 求值桥的 catch-all 分支）。 -/
theorem materialHolds_of_not_material (a : Atom) (d : CaseDocket)
    (h : isMaterialAtom a = false) : materialHolds a d = false := by
  cases a <;> first | rfl | exact absurd h (by decide)

/-! ### 视图等式：未来无关性与取值即视图 -/

theorem lawView_append_future (asOf : Int) (evs fut : EvLedger)
    (hf : ∀ x ∈ fut, asOf < x.1) :
    lawView asOf (evs ++ fut) = lawView asOf evs :=
  JurisLean.Seams.Temporal.trunc_asOf_append_future_irrelevant asOf evs fut hf

theorem occursBy_append_future (asOf : Int) (evs fut : EvLedger)
    (hf : ∀ x ∈ fut, asOf < x.1) (a : Atom) :
    occursBy asOf (evs ++ fut) a = occursBy asOf evs a := by
  unfold occursBy
  rw [lawView_append_future asOf evs fut hf]

/-- **案卷级视图等式**：追加未来事件不改变 as-of 案卷（逐字段经 `occursBy` 传播；
    这是要证的等式，不是前提——与旧锚 hview 外挂的区别所在）。 -/
theorem lawDocket_append_future (asOf : Int) (evs fut : EvLedger)
    (hf : ∀ x ∈ fut, asOf < x.1) :
    lawDocket (evs ++ fut) asOf = lawDocket evs asOf := by
  simp only [lawDocket, occursBy_append_future asOf evs fut hf]

/-- 视图幂等（截断再截断不动）。 -/
theorem lawView_cons (asOf : Int) (y : Int × Atom) (ys : EvLedger) :
    lawView asOf (y :: ys)
      = if y.1 ≤ asOf then y :: lawView asOf ys else lawView asOf ys := rfl

theorem lawView_idem (asOf : Int) (evs : EvLedger) :
    lawView asOf (lawView asOf evs) = lawView asOf evs := by
  induction evs with
  | nil => rfl
  | cons y ys ih =>
      rw [lawView_cons asOf y ys]
      by_cases hy : y.1 ≤ asOf
      · rw [if_pos hy, lawView_cons asOf y (lawView asOf ys), if_pos hy, ih]
      · rw [if_neg hy, ih]

/-- **取值即视图（hview 是定理，不是前提）**：as-of 案卷恒等于先取视图再造案卷。 -/
theorem lawDocket_is_view (evs : EvLedger) (asOf : Int) :
    lawDocket evs asOf = lawDocket (lawView asOf evs) asOf := by
  have h : ∀ a : Atom, occursBy asOf evs a = occursBy asOf (lawView asOf evs) a := by
    intro a
    unfold occursBy
    rw [lawView_idem asOf evs]
  simp only [lawDocket, h]

/-- **实际 Eval**：原子在真实规则网络（`hornOf`：任一案卷都取同一 29 条规则表）
    的 as-of 案卷闭包中的可导性。 -/
def evalAt (a : Atom) (evs : EvLedger) (asOf : Int) : Bool :=
  decide (a ∈ closureAt (hornOf (lawDocket evs asOf)))

/-- 规则体求值：该规则的结论原子在 as-of 案卷的规则网络闭包中。 -/
def ruleFiresAt (r : LawRule) (evs : EvLedger) (asOf : Int) : Bool :=
  evalAt r.horn.conclusion evs asOf

/-- **旧锚 hview 前提在这里是定理**：实际求值恒等于取视图后的求值。 -/
theorem eval_is_view_valued (a : Atom) (evs : EvLedger) (asOf : Int) :
    evalAt a evs asOf = evalAt a (lawView asOf evs) asOf := by
  unfold evalAt
  rw [lawDocket_is_view evs asOf]

/-- **原子级未来盲（一般式）**：追加未来事件不改任何原子的可导性读数。 -/
theorem evalAt_append_future (a : Atom) (evs fut : EvLedger) (asOf : Int)
    (hf : ∀ x ∈ fut, asOf < x.1) :
    evalAt a (evs ++ fut) asOf = evalAt a evs asOf := by
  unfold evalAt
  rw [lawDocket_append_future asOf evs fut hf]

/-! ### 三条真实规则的逐规则使用点 -/

/-- R01（L01 借贷）前提全是材料原子（枚举核对）。 -/
theorem r01_premises_material : ∀ p ∈ ruleLoanEntitlement.horn.premises,
    isMaterialAtom p = true := by
  intro p hp
  have h3 : p = matContractSigned ∨ p = matBankSettlementMatched ∨
      p = matReconciliationUnpaid := by
    simpa [ruleLoanEntitlement, LawRule.horn] using hp
  rcases h3 with rfl | rfl | rfl <;> rfl

/-- R23（L11 行政）前提全是材料原子。 -/
theorem r23_premises_material : ∀ p ∈ ruleAdminDefects.horn.premises,
    isMaterialAtom p = true := by
  intro p hp
  have h3 : p = matPenaltyServedWithBasis ∨ p = matHearingMissed ∨
      p = matRecordContradictions := by
    simpa [ruleAdminDefects, LawRule.horn] using hp
  rcases h3 with rfl | rfl | rfl <;> rfl

/-- R19（L06 继承中止）前提全是材料原子。 -/
theorem r19_premises_material : ∀ p ∈ ruleStaySuccession.horn.premises,
    isMaterialAtom p = true := by
  intro p hp
  have h2 : p = matCDeathRecord ∨ p = matHeirsNotYetJoined := by
    simpa [ruleStaySuccession, LawRule.horn] using hp
  rcases h2 with rfl | rfl <;> rfl

/-- **使用点（i）**：R01 每个前提材料的案卷读数＝视图读数（逐前提 discharge，不是
    外挂前提）。 -/
theorem r01_use_point (evs : EvLedger) (asOf : Int) :
    ∀ p ∈ ruleLoanEntitlement.horn.premises,
      materialHolds p (lawDocket evs asOf) = occursBy asOf evs p :=
  fun p hp => materialHolds_via_view p evs asOf (r01_premises_material p hp)

theorem r23_use_point (evs : EvLedger) (asOf : Int) :
    ∀ p ∈ ruleAdminDefects.horn.premises,
      materialHolds p (lawDocket evs asOf) = occursBy asOf evs p :=
  fun p hp => materialHolds_via_view p evs asOf (r23_premises_material p hp)

theorem r19_use_point (evs : EvLedger) (asOf : Int) :
    ∀ p ∈ ruleStaySuccession.horn.premises,
      materialHolds p (lawDocket evs asOf) = occursBy asOf evs p :=
  fun p hp => materialHolds_via_view p evs asOf (r19_premises_material p hp)

/-- **开火使用点（通用形）**：规则前提全部经视图在卷 ⇒ 结论进真实规则网络闭包
    （消费 `UnifiedNeedlesGap05.rule_fires_of_materials`）。 -/
theorem fires_when_premises_occur (r : LawRule) (hr : r ∈ familyRuleList)
    (evs : EvLedger) (asOf : Int)
    (hmat : ∀ p ∈ r.horn.premises, isMaterialAtom p = true)
    (h : ∀ p ∈ r.horn.premises, occursBy asOf evs p = true) :
    r.horn.conclusion ∈ closureAt (hornOf (lawDocket evs asOf)) := by
  refine rule_fires_of_materials (lawDocket evs asOf) r hr (fun p hp => by
    rw [materialHolds_via_view p evs asOf (hmat p hp)]
    exact h p hp)

/-- **使用点（ii）**：三条规则体的求值对未来盲（经视图等式→案卷等式→闭包等式，
    逐规则实例）。 -/
theorem r01_eval_nonanticipating (evs fut : EvLedger) (asOf : Int)
    (hf : ∀ x ∈ fut, asOf < x.1) :
    ruleFiresAt ruleLoanEntitlement (evs ++ fut) asOf
      = ruleFiresAt ruleLoanEntitlement evs asOf := by
  unfold ruleFiresAt
  rw [evalAt_append_future ruleLoanEntitlement.horn.conclusion evs fut asOf hf]

theorem r23_eval_nonanticipating (evs fut : EvLedger) (asOf : Int)
    (hf : ∀ x ∈ fut, asOf < x.1) :
    ruleFiresAt ruleAdminDefects (evs ++ fut) asOf
      = ruleFiresAt ruleAdminDefects evs asOf := by
  unfold ruleFiresAt
  rw [evalAt_append_future ruleAdminDefects.horn.conclusion evs fut asOf hf]

theorem r19_eval_nonanticipating (evs fut : EvLedger) (asOf : Int)
    (hf : ∀ x ∈ fut, asOf < x.1) :
    ruleFiresAt ruleStaySuccession (evs ++ fut) asOf
      = ruleFiresAt ruleStaySuccession evs asOf := by
  unfold ruleFiresAt
  rw [evalAt_append_future ruleStaySuccession.horn.conclusion evs fut asOf hf]

/-! ### 越窗消费被拒（阻断侧） -/

/-- 全在未来（day > asOf）的账本上，任何原子的视图读数都为假。 -/
theorem occursBy_of_all_future (asOf : Int) (fut : EvLedger)
    (hf : ∀ x ∈ fut, asOf < x.1) (a : Atom) : occursBy asOf fut a = false := by
  unfold occursBy lawView
  rw [JurisLean.Seams.Temporal.trunc_of_all_future asOf fut hf]
  rfl

/-- **阻断通用引理（避开坏集模型见证）**：规则某前提材料经视图缺位 ⇒ 结论在该
    as-of 案卷的规则网络闭包中不可推导。坏集＝{结论, 缺位前提}；结论的非材料性与
    阻断表（29 条规则内核级全查）作为检查位传入。 -/
theorem conclusion_blocked_of_premise_missing (evs : EvLedger) (asOf : Int)
    (r : LawRule) (hr : r ∈ familyRuleList) (p : Atom)
    (hp : p ∈ r.horn.premises) (hmat : isMaterialAtom p = true)
    (hconmat : isMaterialAtom r.horn.conclusion = false)
    (hmiss : occursBy asOf evs p = false)
    (bad : Finset Atom) (hbadcon : r.horn.conclusion ∈ bad) (hbadp : p ∈ bad)
    (hbad : ∀ x ∈ bad, x = r.horn.conclusion ∨ x = p)
    (hchk : familyRuleList.all (fun r' => !decide (r'.horn.conclusion ∈ bad) ||
        !decide ((r'.horn.premises ∩ bad) = ∅)) = true) :
    r.horn.conclusion ∉ closureAt (hornOf (lawDocket evs asOf)) := by
  have hconclfalse : materialHolds r.horn.conclusion (lawDocket evs asOf) = false :=
    materialHolds_of_not_material r.horn.conclusion _ hconmat
  have hdisj : Disjoint (hornOf (lawDocket evs asOf)).initialFacts bad := by
    rw [Finset.disjoint_left]
    intro x hx hb
    have h1 : materialHolds x (lawDocket evs asOf) = true := (Finset.mem_filter.mp hx).2
    rcases hbad x hb with hc | hp
    · rw [hc, hconclfalse] at h1; exact Bool.noConfusion h1
    · rw [hp, materialHolds_via_view p evs asOf hmat, hmiss] at h1
      exact Bool.noConfusion h1
  have hblock' : ∀ r' ∈ familyRuleList, r'.horn.conclusion ∈ bad →
      r'.horn.premises ∩ bad ≠ ∅ := by
    intro r' hr' hcon
    have hchk' := List.all_eq_true.mp hchk r' hr'
    simp only [Bool.or_eq_true, not_decide_eq_true] at hchk'
    rcases hchk' with h9 | h9
    · exact absurd hcon h9
    · exact h9
  have hblock : ∀ rh ∈ (hornOf (lawDocket evs asOf)).rules, rh.conclusion ∈ bad →
      rh.premises ∩ bad ≠ ∅ := by
    intro rh hrh hcon
    obtain ⟨r', hr', rfl⟩ := Finset.mem_image.mp hrh
    exact hblock' r' (List.mem_toFinset.mp hr') hcon
  have hmodel := isModel_avoiding_gen (hornOf (lawDocket evs asOf)) bad hdisj hblock
  intro hmem
  obtain ⟨_, hnot⟩ := Finset.mem_sdiff.mp
    (closure_only_entailed (hornOf (lawDocket evs asOf)) hmem
      (Finset.univ \ bad) hmodel)
  exact hnot hbadcon

/-- R01 阻断检查表（内核级全查：只有 R01 以 loanEntitlement 为结论，其前提撞坏集）。 -/
theorem badR01_check :
    familyRuleList.all (fun r => !decide (r.horn.conclusion ∈
        ({ruleLoanEntitlement.horn.conclusion, matContractSigned} : Finset Atom)) ||
      !decide ((r.horn.premises ∩
        ({ruleLoanEntitlement.horn.conclusion, matContractSigned} : Finset Atom)) = ∅)) = true := by
  rfl

theorem badR23_check :
    familyRuleList.all (fun r => !decide (r.horn.conclusion ∈
        ({ruleAdminDefects.horn.conclusion, matPenaltyServedWithBasis} : Finset Atom)) ||
      !decide ((r.horn.premises ∩
        ({ruleAdminDefects.horn.conclusion, matPenaltyServedWithBasis} : Finset Atom)) = ∅)) = true := by
  rfl

theorem badR19_check :
    familyRuleList.all (fun r => !decide (r.horn.conclusion ∈
        ({ruleStaySuccession.horn.conclusion, matCDeathRecord} : Finset Atom)) ||
      !decide ((r.horn.premises ∩
        ({ruleStaySuccession.horn.conclusion, matCDeathRecord} : Finset Atom)) = ∅)) = true := by
  rfl

/-- **使用点（iv）阻断形 R01**：合同材料经视图缺位 ⇒ 借贷债权不可推导
    （对任意账本、任意 as-of）。 -/
theorem r01_blocked_when_contract_missing (evs : EvLedger) (asOf : Int)
    (hmiss : occursBy asOf evs matContractSigned = false) :
    ruleLoanEntitlement.horn.conclusion
      ∉ closureAt (hornOf (lawDocket evs asOf)) :=
  conclusion_blocked_of_premise_missing evs asOf ruleLoanEntitlement
    (by simp [familyRuleList]) matContractSigned
    (by simp [ruleLoanEntitlement, LawRule.horn]) rfl rfl hmiss
    {ruleLoanEntitlement.horn.conclusion, matContractSigned}
    (Finset.mem_insert_self _ _)
    (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    (fun x hb => by
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact Or.inl rfl
      · rw [Finset.mem_singleton.mp hb]; exact Or.inr rfl)
    badR01_check

theorem r23_blocked_when_penalty_missing (evs : EvLedger) (asOf : Int)
    (hmiss : occursBy asOf evs matPenaltyServedWithBasis = false) :
    ruleAdminDefects.horn.conclusion
      ∉ closureAt (hornOf (lawDocket evs asOf)) :=
  conclusion_blocked_of_premise_missing evs asOf ruleAdminDefects
    (by simp [familyRuleList]) matPenaltyServedWithBasis
    (by simp [ruleAdminDefects, LawRule.horn]) rfl rfl hmiss
    {ruleAdminDefects.horn.conclusion, matPenaltyServedWithBasis}
    (Finset.mem_insert_self _ _)
    (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    (fun x hb => by
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact Or.inl rfl
      · rw [Finset.mem_singleton.mp hb]; exact Or.inr rfl)
    badR23_check

theorem r19_blocked_when_death_missing (evs : EvLedger) (asOf : Int)
    (hmiss : occursBy asOf evs matCDeathRecord = false) :
    ruleStaySuccession.horn.conclusion
      ∉ closureAt (hornOf (lawDocket evs asOf)) :=
  conclusion_blocked_of_premise_missing evs asOf ruleStaySuccession
    (by simp [familyRuleList]) matCDeathRecord
    (by simp [ruleStaySuccession, LawRule.horn]) rfl rfl hmiss
    {ruleStaySuccession.horn.conclusion, matCDeathRecord}
    (Finset.mem_insert_self _ _)
    (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    (fun x hb => by
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact Or.inl rfl
      · rw [Finset.mem_singleton.mp hb]; exact Or.inr rfl)
    badR19_check

/-- **未来-only 账本上三条规则都不开火**（越窗信息消费被拒：能消费的只有视图，
    视图为空则前提缺位，规则链推不出）。 -/
theorem future_only_no_firing (fut : EvLedger) (asOf : Int)
    (hf : ∀ x ∈ fut, asOf < x.1) :
    ruleFiresAt ruleLoanEntitlement fut asOf = false ∧
      ruleFiresAt ruleAdminDefects fut asOf = false ∧
      ruleFiresAt ruleStaySuccession fut asOf = false := by
  have h1 : occursBy asOf fut matContractSigned = false :=
    occursBy_of_all_future asOf fut hf _
  have h2 : occursBy asOf fut matPenaltyServedWithBasis = false :=
    occursBy_of_all_future asOf fut hf _
  have h3 : occursBy asOf fut matCDeathRecord = false :=
    occursBy_of_all_future asOf fut hf _
  refine ⟨?_, ?_, ?_⟩ <;> unfold ruleFiresAt evalAt
  · rw [decide_eq_false (r01_blocked_when_contract_missing fut asOf h1)]
  · rw [decide_eq_false (r23_blocked_when_penalty_missing fut asOf h2)]
  · rw [decide_eq_false (r19_blocked_when_death_missing fut asOf h3)]

/-! ### 见证账本与时点动力学 -/

/-- 裁判时点（[代拟稿]：epoch 日演示值）。 -/
def tCut : Int := 100

/-- 见证账本：三条规则的全部前提材料都在截止前到账（R01 三份、R23 三份、
    R19 两份，日期 10–80 均 ≤ 100）。 -/
def witLedger : EvLedger :=
  [(10, matContractSigned), (20, matBankSettlementMatched), (30, matReconciliationUnpaid),
    (40, matPenaltyServedWithBasis), (50, matHearingMissed), (60, matRecordContradictions),
    (70, matCDeathRecord), (80, matHeirsNotYetJoined)]

theorem wit_reads :
    occursBy tCut witLedger matContractSigned = true ∧
      occursBy tCut witLedger matBankSettlementMatched = true ∧
      occursBy tCut witLedger matReconciliationUnpaid = true ∧
      occursBy tCut witLedger matPenaltyServedWithBasis = true ∧
      occursBy tCut witLedger matHearingMissed = true ∧
      occursBy tCut witLedger matRecordContradictions = true ∧
      occursBy tCut witLedger matCDeathRecord = true ∧
      occursBy tCut witLedger matHeirsNotYetJoined = true := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **使用点（iii）**：满料账上三条真实规则经视图开火。 -/
theorem r01_fires_witness : ruleFiresAt ruleLoanEntitlement witLedger tCut = true := by
  unfold ruleFiresAt evalAt
  rw [decide_eq_true (fires_when_premises_occur ruleLoanEntitlement
    (by simp [familyRuleList]) witLedger tCut r01_premises_material
    (by
      intro p hp
      have h3 : p = matContractSigned ∨ p = matBankSettlementMatched ∨
          p = matReconciliationUnpaid := by
        simpa [ruleLoanEntitlement, LawRule.horn] using hp
      rcases h3 with rfl | rfl | rfl
      · exact wit_reads.1
      · exact wit_reads.2.1
      · exact wit_reads.2.2.1))]

theorem r23_fires_witness : ruleFiresAt ruleAdminDefects witLedger tCut = true := by
  unfold ruleFiresAt evalAt
  rw [decide_eq_true (fires_when_premises_occur ruleAdminDefects
    (by simp [familyRuleList]) witLedger tCut r23_premises_material
    (by
      intro p hp
      have h3 : p = matPenaltyServedWithBasis ∨ p = matHearingMissed ∨
          p = matRecordContradictions := by
        simpa [ruleAdminDefects, LawRule.horn] using hp
      rcases h3 with rfl | rfl | rfl
      · exact wit_reads.2.2.2.1
      · exact wit_reads.2.2.2.2.1
      · exact wit_reads.2.2.2.2.2.1))]

theorem r19_fires_witness : ruleFiresAt ruleStaySuccession witLedger tCut = true := by
  unfold ruleFiresAt evalAt
  rw [decide_eq_true (fires_when_premises_occur ruleStaySuccession
    (by simp [familyRuleList]) witLedger tCut r19_premises_material
    (by
      intro p hp
      have h2 : p = matCDeathRecord ∨ p = matHeirsNotYetJoined := by
        simpa [ruleStaySuccession, LawRule.horn] using hp
      rcases h2 with rfl | rfl
      · exact wit_reads.2.2.2.2.2.2.1
      · exact wit_reads.2.2.2.2.2.2.2))]

/-- 迟到账本：合同材料 150 日才到（其余 R01 前提早到）。 -/
def lateLedger : EvLedger :=
  [(10, matBankSettlementMatched), (30, matReconciliationUnpaid), (150, matContractSigned)]

/-- **时点动力学见证**：同一账本，截止 100 时合同材料不在视图 ⇒ R01 不开火；
    截止移到 160（材料进视图）⇒ R01 开火。改变读数的是裁判时点，不是信息本身。 -/
theorem late_material_blocked_before_cut :
    evalAt ruleLoanEntitlement.horn.conclusion lateLedger 100 = false ∧
      evalAt ruleLoanEntitlement.horn.conclusion lateLedger 160 = true := by
  refine ⟨?_, ?_⟩
  · unfold evalAt
    rw [decide_eq_false (r01_blocked_when_contract_missing lateLedger 100 rfl)]
  · unfold evalAt
    rw [decide_eq_true (fires_when_premises_occur ruleLoanEntitlement
      (by simp [familyRuleList]) lateLedger 160 r01_premises_material
      (by
        intro p hp
        have h3 : p = matContractSigned ∨ p = matBankSettlementMatched ∨
            p = matReconciliationUnpaid := by
          simpa [ruleLoanEntitlement, LawRule.horn] using hp
        rcases h3 with rfl | rfl | rfl <;> rfl))]

/-- 具体未来事件（200 日再来一份合同材料）不改见证账上的规则读数。 -/
theorem witness_firing_future_blind :
    ruleFiresAt ruleLoanEntitlement (witLedger ++ [((200 : Int), matContractSigned)]) tCut
      = ruleFiresAt ruleLoanEntitlement witLedger tCut ∧
    ruleFiresAt ruleAdminDefects (witLedger ++ [((200 : Int), matContractSigned)]) tCut
      = ruleFiresAt ruleAdminDefects witLedger tCut ∧
    ruleFiresAt ruleStaySuccession (witLedger ++ [((200 : Int), matContractSigned)]) tCut
      = ruleFiresAt ruleStaySuccession witLedger tCut := by
  have hf : ∀ x ∈ [((200 : Int), matContractSigned)], tCut < x.1 := by
    intro x hx
    cases List.mem_cons.mp hx with
    | inl heq =>
        subst heq
        decide
    | inr hnil => exact absurd hnil (by simp)
  exact ⟨r01_eval_nonanticipating witLedger [((200 : Int), matContractSigned)] tCut hf,
    r23_eval_nonanticipating witLedger [((200 : Int), matContractSigned)] tCut hf,
    r19_eval_nonanticipating witLedger [((200 : Int), matContractSigned)] tCut hf⟩

/-- **针 48 旗舰（XT，I:802 逐规则使用点收口）**：(1) 旧锚 hview 前提成为定理；
    (2) 三条真实规则（R01 借贷/R23 行政/R19 继承中止）逐前提使用点（案卷读数＝视图
    读数）；(3) 三条规则体求值逐规则未来盲；(4) 满料账上三条规则经视图开火；
    (5) 未来-only 账上三条规则全部被拒；(6) 原子级一般未来盲；(7) 迟到材料时点
    动力学；(8) 具体未来事件不改见证读数。 -/
theorem legal_time_nonanticipation :
    (∀ (a : Atom) (evs : EvLedger) (asOf : Int),
        evalAt a evs asOf = evalAt a (lawView asOf evs) asOf) ∧
    (∀ (evs : EvLedger) (asOf : Int), ∀ p ∈ ruleLoanEntitlement.horn.premises,
        materialHolds p (lawDocket evs asOf) = occursBy asOf evs p) ∧
    (∀ (evs : EvLedger) (asOf : Int), ∀ p ∈ ruleAdminDefects.horn.premises,
        materialHolds p (lawDocket evs asOf) = occursBy asOf evs p) ∧
    (∀ (evs : EvLedger) (asOf : Int), ∀ p ∈ ruleStaySuccession.horn.premises,
        materialHolds p (lawDocket evs asOf) = occursBy asOf evs p) ∧
    (∀ (evs fut : EvLedger) (asOf : Int), (∀ x ∈ fut, asOf < x.1) →
        ruleFiresAt ruleLoanEntitlement (evs ++ fut) asOf
          = ruleFiresAt ruleLoanEntitlement evs asOf) ∧
    (∀ (evs fut : EvLedger) (asOf : Int), (∀ x ∈ fut, asOf < x.1) →
        ruleFiresAt ruleAdminDefects (evs ++ fut) asOf
          = ruleFiresAt ruleAdminDefects evs asOf) ∧
    (∀ (evs fut : EvLedger) (asOf : Int), (∀ x ∈ fut, asOf < x.1) →
        ruleFiresAt ruleStaySuccession (evs ++ fut) asOf
          = ruleFiresAt ruleStaySuccession evs asOf) ∧
    (ruleFiresAt ruleLoanEntitlement witLedger tCut = true ∧
      ruleFiresAt ruleAdminDefects witLedger tCut = true ∧
      ruleFiresAt ruleStaySuccession witLedger tCut = true) ∧
    (∀ (fut : EvLedger) (asOf : Int), (∀ x ∈ fut, asOf < x.1) →
        ruleFiresAt ruleLoanEntitlement fut asOf = false ∧
        ruleFiresAt ruleAdminDefects fut asOf = false ∧
        ruleFiresAt ruleStaySuccession fut asOf = false) ∧
    (∀ (a : Atom) (evs fut : EvLedger) (asOf : Int), (∀ x ∈ fut, asOf < x.1) →
        evalAt a (evs ++ fut) asOf = evalAt a evs asOf) ∧
    (evalAt ruleLoanEntitlement.horn.conclusion lateLedger 100 = false ∧
      evalAt ruleLoanEntitlement.horn.conclusion lateLedger 160 = true) ∧
    (ruleFiresAt ruleLoanEntitlement (witLedger ++ [(200, matContractSigned)]) tCut
        = ruleFiresAt ruleLoanEntitlement witLedger tCut ∧
      ruleFiresAt ruleAdminDefects (witLedger ++ [(200, matContractSigned)]) tCut
        = ruleFiresAt ruleAdminDefects witLedger tCut ∧
      ruleFiresAt ruleStaySuccession (witLedger ++ [(200, matContractSigned)]) tCut
        = ruleFiresAt ruleStaySuccession witLedger tCut) :=
  ⟨fun a evs asOf => eval_is_view_valued a evs asOf,
    fun evs asOf => r01_use_point evs asOf,
    fun evs asOf => r23_use_point evs asOf,
    fun evs asOf => r19_use_point evs asOf,
    fun evs fut asOf => r01_eval_nonanticipating evs fut asOf,
    fun evs fut asOf => r23_eval_nonanticipating evs fut asOf,
    fun evs fut asOf => r19_eval_nonanticipating evs fut asOf,
    ⟨r01_fires_witness, r23_fires_witness, r19_fires_witness⟩,
    fun fut asOf => future_only_no_firing fut asOf,
    fun a evs fut asOf => evalAt_append_future a evs fut asOf,
    late_material_blocked_before_cut,
    witness_firing_future_blind⟩

end Needle48LawView

end JurisLean.Seams.UnifiedPayoffChain
