import Mathlib.Tactic
import JurisLean.Seams.Probability
import JurisLean.FullMath.Numeric.Intervals

open JurisLean.Seams.Probability (Amount amountQ)
open JurisLean.FullMath.Numeric (Iv)

/-!
## W4 批5 / G3（12 卷 §W4 表行 5）—— L6 制裁层：迟延履行加倍利息的数额泛函
### （《民事诉讼法》第 264 条 ＋ 法释〔2014〕8号 第 1 条第 3 款）

**写者边界**：本件只新建这一份文件，不改动任何既有件，也**不**把本件加进根文件
`proofs/lean/juris_lean/JurisLean.lean`（该处 `import JurisLean.Seams.*` 到 `:180` 为止，
新模块要先拿到自己的 CI 单模块绿才入根，见 AGENTS.md「Lean Workflow」）。
本件是**未编译草稿**：状态 `CI_NOT_RUN`，本地不跑 Lean（AGENTS.md「Lean Execution Boundary」）。

### 一、施工令出处与实测缺口
出处只有一行：`docs/master-plan/12_一次性全量落地施工计划_20261002.md:68` 的 §W4 表**第 5 行**
「民诉法 264 ＋ 法释〔2014〕8号第1条第3款 ｜ L6 制裁层 ｜ 日万分之1.75 是确定算术式，可进数额泛函」。
同表已落地的两行是批1（法释〔2023〕13号 63—66 条 → `Seams/ReductionConditions2.lean`）与
批3（民诉法解释 90/91/92/93/108/109 条 → `Seams/BurdenStatutes.lean`）；
批2（民法典 577/580/584/585＋192/193）与批4（立法法 98—102）**不在本件范围**。
本件只交**表行 5**，并说明它在 Lean 里此前是空的。
实测（写入之前，`proofs/lean/juris_lean/JurisLean` 全树 `grep` 计文件数）：
`万分之` **0 命中**、`加倍` **0 命中**；`迟延履行` 只在
`Seams/PayoffEquilibrium.lean:22、:54、:135、:369-371` 出现，末处是
`withSanction` 把制裁抽象成一个自由参数 `k : ℚ`（该文件自述「迟延履行金/罚款的抽象化」），
**与该执行利率的数值毫无关系**。故本件是这批条文在 Lean 里的第一次落地。

### 二、法源与仓内一手记录（逐条给锚；取不到的一律标 [代拟稿]）
1. **法释〔2014〕8号 第 1 条第 3 款（算式）**——本件只引**本仓已记录**的那一句。
   `docs/master-plan/09_法律统一数学模型_20261001.md:316-318` 逐字记为：
   「加倍部分债务利息＝债务人尚未清偿的生效法律文书确定的除一般债务利息之外的金钱债务
   × **日万分之一点七五** × 迟延履行期间」，同处标注一手页
   `court.gov.cn/fabu/xiangqing/6628.html`。`11_继续完善施工方案_20261002.md:114` 与
   `12_…施工计划_20261002.md:68` 是同一读法的两处复述。
   **档位**：本件**没有**重新取回该页，引句是**转引本仓 09 卷**的记录；故凡本件的定理，
   其前提只依赖本件的 ℚ 算术，**不依赖**引句文本（引句若有出入，以公报页为准）。
2. **《民事诉讼法》（2023 修正）第 264 条（义务本体）**——**仓内无完整一手文本**。
   只有两处旁证：`Seams/PayoffEquilibrium.lean:22` 的注释「迟延履行金见《民事诉讼法》第264条」，
   以及 `data/external/supreme_court/extracted_rules.json:1859` 的一段 524 字 OCR 预览，
   引到「《民事诉讼法》第264条规定：'被执行人未按判决、裁定和其他法律文书指定的期间履行
   给付金钱义务的，应当加倍支付迟延」**就在此截断**（该件 `text_length` 恒为 524，是预览字段，
   不是全文；其 `source` 指向一本审判实务书的 OCR，属**法院系统二手读物**，不是人大一手文本）。
   同文件 `:1892` 另记一条脚注「①现为《民事诉讼法》2023年修正）第264条」，只坐实**条号迁移**，
   不坐实文字。⇒ **第264条的条文原句（含第2句关于"其他义务…支付迟延履行金"）在本仓取不到**，
   本件因此把该条写成 [代拟稿] 的 `def … : Prop`（`art264_obligationShape`），
   并**绝不**把它读成"第264条已被形式化证明"。
3. **2014-08-01 施行日分界**——仓内记录见
   `docs/history/evidence-archive/0924_二十轮对辩/五轮问_致GPT_20260924.md:8、:19`
   （R2 簇：「迟延加倍日万1.75、2014-08-01 分界」）。本件是**单段**泛函，
   **不**做跨施行日的分段累计，登记为未覆盖片段第 3 项。

### 三、口径：为什么是 ℚ，不是 ℝ，也不是浮点
既有数值口径有三处，本件全部**沿用**而不新造：
① `Seams/Probability.lean:428` 的 `abbrev Amount := ℤ`（最小货币单位）与 `:431` 的
`def amountQ (x : Amount) : ℚ`——注释原话「比例与门槛比较一律在此进行（`ℚ` 精确，绝无 `Float`）」；
② `Seams/Probability.lean:379` 的 `exactAmountQ : ExactAmountM5 → ℚ`；
③ `FullMath/Numeric/Intervals.lean:16-19` 的 `structure Iv`，其端点是 `lo hi : ℚ`。
万分之1.75 换成分数是 `1.75/10000 = 175/1000000 = 7/40000`，在 ℚ 上是**精确**的；
换成 `ℝ` 会把这条精确等式变成 `Rat.cast` 像的等式，等于另开一套口径（本仓已有 ℚ 口径三处），
故本件全程 `ℚ`，天数用 `ℕ`（条文的"期间"就是天数，不是实数）。

### 四、本件产出（全部具名）
- **率常量** `sanctionDailyRate` 与其精确性四件套：`…_eq_wanfen_yi_dian_qi_wu`（万分之1.75 原形）、
  `…_eq_seven_over_fourthousand`（**精确等于 7/40000**）、`…_times_40000_eq_7`（整数化）、
  `…_pos`、`…_lt_one`，再加一条纯整数交叉验算 `…_cross_multiplication`（`decide` 算出）。
- **泛函** `doubleInterest (principal : ℚ) (days : ℕ) : ℚ`，以及法院真正会用的性质：
  `…_zero_days`（零天为零）、`…_zero_principal`、`…_nonneg`、`…_monotone_days`（期间越长不减）、
  `…_strict_mono_days`（本金为正时**严格**随天数增）、`…_injective_days`（天数可由数额反推）、
  `…_monotone_principal`、`…_scale_principal`、`…_add_days`（**分段可加**，跨年度累计的算术根据）、
  `…_succ_days`（每多一天加"日利率×本金"）、`…_mul_days`（按天数**线性缩放**）、
  `…_cleared`（`40000 × 利息 = 7 × 本金 × 天数` 的整数化读法，法官手算式）。
- **算得出来的具体例**（`norm_num`/`decide` 逐条给出，读者可手验）：
  `…_case_1w_1d`（本金 1 万、1 天 → `7/4`＝1.75 元）、`…_case_10w_100d`（10 万、100 天 → 1750）、
  `…_case_100w_365d`（100 万、365 天 → 63875）、`…_case_10w_5714d`／`…_case_10w_5715d`
  （加倍利息何时**追上本金**：第 5714 天差一点、第 5715 天过头），
  配 `sanction_days_5714_5715_int_window`（`decide`）与 `doubleInterest_ge_principal`（一般判据）。
- **中途清偿的口径差**：`doubleInterest_sub_principal`、`doubleInterest_partial_payment_gap`
  （差额**正好**等于 `日利率 × 清偿额 × 后段天数`）、`sanction_single_basis_overstates`。
- **接缝**：`doubleInterestOfAmount`（把 `Amount := ℤ` 这一既有载体接进来）、
  `doubleInterest_Iv_bounds`（把 `Iv` 这一既有区间载体接进来，只引用其 `Iv.mem`，**不复述**其定理）。
- **边界**：`sanction_amount_is_rule_blind`（本件对"起算规则"**无感**）、
  `sanction_period_rule_gap_changes_amount`（规则之差直接变成钱之差）、
  两条挂账式 `sanctionDailyRate_matches_statuteObligation`、`sanctionPeriodDaysObligation`，
  以及证明它们**不是装饰**的 `sanctionDailyRate_matches_unique`、
  `sanction_period_days_obligation_failure_changes_amount`。
- 末尾 `未覆盖片段` 一节逐条承认本件没表达的法律内容。

### 五、本件**不**做什么（必须读）
- **不认定任何真实案件**的迟延履行期间、本金、数额；`principal`、`days` 始终是自由输入。
- **不声称第264条已被形式化**：条文原句仓内取不到，本件证的只是**本件自造读法**的算术部分。
- **不接一般债务利息**（第1条第3款明写"除一般债务利息之外"），不接 LPR 四倍上限，
  不接"利息与加倍部分债务利息之和不超过民间借贷利率保护上限"这一**裁判要旨级**读物
  （见 `data/external/supreme_court/extracted_rules.json:1859` 的标题句，它**不是**条文）。
- **不做舍入**：输出是 ℚ，未接 `Seams/Probability.lean` 的 `RoundingPolicy`/`denotateWithPolicy`
  （那一条的读数与政策关系本件**不复述**）。
- **不做跨 2014-08-01 的分段**，不做部分履行的清偿顺位（抵充顺序），不做非金钱义务的迟延履行金。
- **不碰公法制裁**：刑事罚金/没收、行政罚款按 `09 卷 §8.1` 判为越界，并列域未建。
- **不声称本件已编译、已入根、已过 CI**；状态 `CI_NOT_RUN`，零 `sorry`、零 `admit`、
  零 `native_decide`、零自定义 `axiom`，没有把结论写进前提，没有削弱任何复用的陈述。
-/

namespace JurisLean.Seams.SanctionInterest

section DailyRate

/-- 日万分之一点七五（法释〔2014〕8号第1条第3款的率；本仓记录见 09 卷 :316-318）。
    写成整数比而不是小数：`万分之1.75 = 1.75/10000 = 175/1000000`，全程 ℚ，绝无 `Float`。
    施工令把它读成"确定算术式"，本件就把"确定"做成可证的等式而不是措辞。 -/
def sanctionDailyRate : ℚ := (175 : ℚ) / 1000000

/-- 中文证明（"万分之一点七五"的字面形）：本件常量就是 `1.75 ÷ 10000`，
    即条文用词"日万分之一点七五"的算术原形。 -/
theorem sanctionDailyRate_eq_wanfen_yi_dian_qi_wu :
    sanctionDailyRate = (175 / 100 : ℚ) / 10000 := by
  unfold sanctionDailyRate
  norm_num

/-- 中文证明（**精确等于 7/40000**）：这是本件的主张——率是确定算术式，
    约分后唯一读数是 `7/40000`，没有第二种口径，也不需要极限或近似。 -/
theorem sanctionDailyRate_eq_seven_over_fourthousand :
    sanctionDailyRate = 7 / 40000 := by
  unfold sanctionDailyRate
  norm_num

/-- 中文证明（整数化读数）：率乘回分母得整数 7。法官手算用的就是这个形
    （"每 40000 元本金每天 7 元"）。 -/
theorem sanctionDailyRate_times_40000_eq_7 : sanctionDailyRate * 40000 = 7 := by
  unfold sanctionDailyRate
  norm_num

/-- 中文证明（率为正）：`0 < sanctionDailyRate`。这条是后面一切单调性的引擎。 -/
theorem sanctionDailyRate_pos : 0 < sanctionDailyRate := by
  unfold sanctionDailyRate
  norm_num

/-- 中文证明（率小于一）：一天的率不足一元钱的一倍，故泛函**不是**复利形。 -/
theorem sanctionDailyRate_lt_one : sanctionDailyRate < 1 := by
  unfold sanctionDailyRate
  norm_num

/-- 中文证明（**纯整数交叉验算**，`decide` 直接算）：`175 × 40000 = 7 × 1000000`。
    这条与 ℚ 无关，是"约分没有改变数值"的整数侧证据。
    口径说明：本件的 `decide` 只用在 ℕ/ℤ 的等式与大小上（本件共三处），
    ℚ 的除法与约分一律走 `norm_num`，因为 `Rat` 的规范化要走 `Nat.gcd`，
    交给 kernel 判定既慢又易假红。 -/
theorem sanctionDailyRate_cross_multiplication : (175 : ℤ) * 40000 = 7 * 1000000 := by
  decide

/-- 中文说明（**义务登记·非已证** [代拟稿]）：法定日利率与本件常量的**同一性**。
    设 `statutory` 为法释〔2014〕8号第1条第3款所指的那个日利率（一个本件在 Lean 里
    **取不到**的外部对象：本件没有通往 `court.gov.cn/fabu/xiangqing/6628.html` 的通道，
    仓内也只有 09 卷 :316-318 的转引记录）。要挂账的目标是 `sanctionDailyRate = statutory`。
    本件**不**把它写成定理——把它写成定理等于把"本件的定义"复读成"法条如此规定"，
    正是 `09 卷 §8.2` 批评的"签名不锁"。登记方式为**参数化**：将来取到一手文本时，
    兑现动作是把具体的 `statutory` 代入此式并闭合它。 -/
def sanctionDailyRate_matches_statuteObligation (statutory : ℚ) : Prop :=
  sanctionDailyRate = statutory

/-- 中文证明（这条挂账项**不是装饰**：它的解唯一）：
    `sanctionDailyRate_matches_statuteObligation q` 成立**当且仅当** `q = 7/40000`。
    也就是说，该义务式虽然未证，却已经把"猜一个率"这条路堵死：任何别的读数都不满足它。 -/
theorem sanctionDailyRate_matches_unique (q : ℚ) :
    sanctionDailyRate_matches_statuteObligation q ↔ q = 7 / 40000 := by
  constructor
  · intro h
    have h' : sanctionDailyRate = q := h
    exact h'.symm.trans sanctionDailyRate_eq_seven_over_fourthousand
  · intro h
    show sanctionDailyRate = q
    rw [h]
    exact sanctionDailyRate_eq_seven_over_fourthousand

end DailyRate

section Functional

/-- 加倍部分债务利息（法释〔2014〕8号第1条第3款的算式形）：
    `尚未清偿的金钱债务本金 × 日万分之1.75 × 迟延履行期间天数`。
    《民事诉讼法》（2023 修正）第264条提供的是"应当加倍支付"这一**义务**，
    算式本身来自司法解释；条文原句仓内取不到（见本件头注 §二·2），
    故本件只对此函数证算术性质，不声称它等于第264条的全部含义。 -/
def doubleInterest (principal : ℚ) (days : ℕ) : ℚ :=
  sanctionDailyRate * principal * days

/-- 中文证明（零天为零）：迟延履行期间为 0 天时加倍利息为 0。
    法律读法：**没有迟延就没有制裁**，本件的泛函自动满足这一点，不需要额外开关。 -/
theorem doubleInterest_zero_days (principal : ℚ) : doubleInterest principal 0 = 0 := by
  unfold doubleInterest
  rw [Nat.cast_zero]
  exact mul_zero _

/-- 中文证明（零本金为零）：尚未清偿的本金为 0（已全部清偿）时加倍利息为 0。 -/
theorem doubleInterest_zero_principal (days : ℕ) : doubleInterest 0 days = 0 := by
  unfold doubleInterest
  ring

/-- 中文证明（非负性）：本金非负时数额非负。这是 `art264_obligationShape` 的算术引擎。 -/
theorem doubleInterest_nonneg {principal : ℚ} (hp : 0 ≤ principal) (days : ℕ) :
    0 ≤ doubleInterest principal days := by
  have hd : (0 : ℚ) ≤ days := Nat.cast_le.mpr (Nat.zero_le days)
  unfold doubleInterest
  exact mul_nonneg (mul_nonneg (le_of_lt sanctionDailyRate_pos) hp) hd

/-- 中文证明（**天数单调不减**）：本金非负时，期间越长加倍利息不减少。
    《民诉法》第264条"迟延履行期间"越长越重的读法在此是可证的算术性质；
    但"从哪一天开始数"本件不决定（见 `sanction_amount_is_rule_blind`）。 -/
theorem doubleInterest_monotone_days (principal : ℚ) (hp : 0 ≤ principal) :
    Monotone (doubleInterest principal) := by
  intro d₁ d₂ h
  have hc : (d₁ : ℚ) ≤ (d₂ : ℚ) := Nat.cast_le.mpr h
  have hw : 0 ≤ sanctionDailyRate * principal :=
    mul_nonneg (le_of_lt sanctionDailyRate_pos) hp
  unfold doubleInterest
  exact mul_le_mul_of_nonneg_left hc hw

/-- 中文证明（**严格**单调）：本金为正时，天数严格增加则数额严格增加。 -/
theorem doubleInterest_strict_mono_days (principal : ℚ) (hp : 0 < principal) (d₁ d₂ : ℕ)
    (h : d₁ < d₂) : doubleInterest principal d₁ < doubleInterest principal d₂ := by
  have hcast : (d₁ : ℚ) < (d₂ : ℚ) := Nat.cast_lt.mpr h
  unfold doubleInterest
  exact mul_lt_mul_of_pos_left hcast (mul_pos sanctionDailyRate_pos hp)

/-- 中文证明（天数侧**单射**）：本金为正时，数额反推得出天数——即数额里**不夹带**
    任何天数之外的信息，也不丢失天数。这条与 `sanction_amount_is_rule_blind` 合起来
    构成本件的边界：泛函只看天数，看多少天由执行文书决定。 -/
theorem doubleInterest_injective_days (principal : ℚ) (hp : 0 < principal) :
    Function.Injective (doubleInterest principal) := by
  intro d₁ d₂ h
  have hc : sanctionDailyRate * principal ≠ 0 := ne_of_gt (mul_pos sanctionDailyRate_pos hp)
  unfold doubleInterest at h
  exact Nat.cast_inj.mp (mul_left_cancel₀ hc h)

/-- 中文证明（本金侧单调不减）：天数固定（自然数，故自动非负）时，本金越大数额越大。 -/
theorem doubleInterest_monotone_principal (days : ℕ) :
    Monotone (fun principal => doubleInterest principal days) := by
  intro p₁ p₂ h
  have hw : 0 ≤ (days : ℚ) := Nat.cast_le.mpr (Nat.zero_le days)
  have hscale : sanctionDailyRate * p₁ ≤ sanctionDailyRate * p₂ :=
    mul_le_mul_of_nonneg_left h (le_of_lt sanctionDailyRate_pos)
  unfold doubleInterest
  exact mul_le_mul_of_nonneg_right hscale hw

/-- 中文证明（本金侧**线性**）：本金同乘一个因子，数额同乘该因子。
    法律读法：加倍利息是**比例**制裁，不是定额制裁。 -/
theorem doubleInterest_scale_principal (c principal : ℚ) (days : ℕ) :
    doubleInterest (c * principal) days = c * doubleInterest principal days := by
  unfold doubleInterest
  ring

/-- 中文证明（**分段可加**）：两段迟延期间合并计息等于两段分别计息之和。
    这是"跨年度累计"与"多段迟延"的算术根据；本件的可加性只在**同一个率**下成立，
    跨 2014-08-01 施行日的分段（率会变）不在本件内，见未覆盖片段第 3 项。 -/
theorem doubleInterest_add_days (principal : ℚ) (d₁ d₂ : ℕ) :
    doubleInterest principal (d₁ + d₂) =
      doubleInterest principal d₁ + doubleInterest principal d₂ := by
  show sanctionDailyRate * principal * ((d₁ + d₂ : ℕ) : ℚ) =
    (sanctionDailyRate * principal * (d₁ : ℚ)) + (sanctionDailyRate * principal * (d₂ : ℚ))
  rw [Nat.cast_add]
  ring

/-- 中文证明（逐日累加式）：每多迟延一天，数额加"日利率 × 本金"。
    法官执行裁定里的逐日累计就是这个递推。 -/
theorem doubleInterest_succ_days (principal : ℚ) (days : ℕ) :
    doubleInterest principal (days + 1) =
      doubleInterest principal days + sanctionDailyRate * principal := by
  unfold doubleInterest
  rw [Nat.cast_add, Nat.cast_one]
  ring

/-- 中文证明（按天数**线性缩放**）：天数取 `a * b` 时数额等于 `a` 倍的天数 `b` 的数额。
    与 `doubleInterest_add_days` 合起来说明：泛函对"期间"是 ℚ-线性的。 -/
theorem doubleInterest_mul_days (principal : ℚ) (a b : ℕ) :
    doubleInterest principal (a * b) = (a : ℚ) * doubleInterest principal b := by
  unfold doubleInterest
  rw [Nat.cast_mul]
  ring

/-- 中文证明（**整数化手算式**）：`40000 × 加倍利息 = 7 × 本金 × 天数`。
    分母被消掉，剩下的全是整数乘法——"日万分之1.75 是确定算术式"这句话的可证形。 -/
theorem doubleInterest_cleared (principal : ℚ) (days : ℕ) :
    (40000 : ℚ) * doubleInterest principal days = 7 * principal * days := by
  unfold doubleInterest
  calc (40000 : ℚ) * (sanctionDailyRate * principal * (days : ℚ))
      = sanctionDailyRate * 40000 * principal * (days : ℚ) := by ring
    _ = 7 * principal * (days : ℚ) := by rw [sanctionDailyRate_times_40000_eq_7]

/-- 中文证明（清偿后的本金代入）：本金减少 `repaid` 时，数额同额减少"日利率 × 清偿额 × 天数"。 -/
theorem doubleInterest_sub_principal (principal repaid : ℚ) (days : ℕ) :
    doubleInterest (principal - repaid) days =
      doubleInterest principal days - sanctionDailyRate * repaid * (days : ℚ) := by
  show sanctionDailyRate * (principal - repaid) * (days : ℚ) =
    sanctionDailyRate * principal * (days : ℚ) - sanctionDailyRate * repaid * (days : ℚ)
  ring

/-- 中文证明（**中途清偿的口径差**）：前段 `d₁` 天按原本金计、后段 `d₂` 天按剩余本金计，
    与"全程按原本金计"之间的差额**正好**是 `日利率 × 清偿额 × 后段天数`。
    法律读法：两口径的差不是含糊的，可以精确到分；但**哪一口径合法**第264条与
    第1条第3款在本仓记录里都没有给出（第1条第3款只给算式），见未覆盖片段第 4 项。 -/
theorem doubleInterest_partial_payment_gap (principal repaid : ℚ) (d₁ d₂ : ℕ) :
    doubleInterest principal (d₁ + d₂)
      - (doubleInterest principal d₁ + doubleInterest (principal - repaid) d₂)
      = sanctionDailyRate * repaid * (d₂ : ℚ) := by
  have h1 : doubleInterest principal (d₁ + d₂) =
      doubleInterest principal d₁ + doubleInterest principal d₂ :=
    doubleInterest_add_days principal d₁ d₂
  have h2 : doubleInterest (principal - repaid) d₂ =
      doubleInterest principal d₂ - sanctionDailyRate * repaid * (d₂ : ℚ) :=
    doubleInterest_sub_principal principal repaid d₂
  rw [h1, h2]
  ring

/-- 中文证明（单一口径**高估**）：中途真有清偿、后段真有天数的话，
    按原本金一次性计的数额严格大于分段计的数额。这不是散文判断，是可等式化后 `linarith` 的结论。 -/
theorem sanction_single_basis_overstates (principal repaid : ℚ) (d₁ d₂ : ℕ)
    (hr : 0 < repaid) (hd : 0 < d₂) :
    doubleInterest principal d₁ + doubleInterest (principal - repaid) d₂
      < doubleInterest principal (d₁ + d₂) := by
  have key : doubleInterest principal (d₁ + d₂)
      - (doubleInterest principal d₁ + doubleInterest (principal - repaid) d₂)
      = sanctionDailyRate * repaid * (d₂ : ℚ) := doubleInterest_partial_payment_gap _ _ _ _
  have hpos : 0 < sanctionDailyRate * repaid * (d₂ : ℚ) :=
    mul_pos (mul_pos sanctionDailyRate_pos hr) (Nat.cast_lt.mpr hd)
  linarith

end Functional

section Concrete

/-- 中文证明（具体例一，可手验）：本金 1 万元、迟延 1 天 → `7/4` 元，即日万分之1.75 的字面读数
    （1 万元一天 1.75 元）。法释〔2014〕8号第1条第3款的算式在这里**算出来了**，不是存在声明。 -/
theorem doubleInterest_case_1w_1d : doubleInterest 10000 1 = (7 / 4 : ℚ) := by
  norm_num [doubleInterest, sanctionDailyRate]

/-- 中文证明（具体例二，可手验）：本金 10 万元、迟延 100 天 → **1750**。
    手验：10 万元一天 17.5 元（万分之1.75），100 天即 1750 元。 -/
theorem doubleInterest_case_10w_100d : doubleInterest 100000 100 = (1750 : ℚ) := by
  norm_num [doubleInterest, sanctionDailyRate]

/-- 中文证明（具体例三，可手验）：本金 100 万元、迟延 365 天 → **63875**。
    手验：100 万元一天 175 元；175 × 365 = 63875 元。 -/
theorem doubleInterest_case_100w_365d : doubleInterest 1000000 365 = (63875 : ℚ) := by
  norm_num [doubleInterest, sanctionDailyRate]

/-- 中文证明（"追上本金"的整数窗口，`decide` 算出）：`7 × 5714 < 40000 ≤ 7 × 5715`。
    这条是下面两个具体例的整数骨架：万分之1.75 的率要累计到与本金同量，需要 5715 天。 -/
theorem sanction_days_5714_5715_int_window : 7 * 5714 < 40000 ∧ 40000 ≤ 7 * 5715 := by
  decide

/-- 中文证明（一般判据）：只要"日利率 × 天数"不小于 1，加倍利息就不小于本金。
    陈述里没有除法，判据可直接由 `norm_num` 对具体天数闭合。 -/
theorem doubleInterest_ge_principal (principal : ℚ) (hp : 0 < principal) (days : ℕ)
    (hd : (1 : ℚ) ≤ sanctionDailyRate * days) : principal ≤ doubleInterest principal days := by
  calc principal = principal * 1 := (mul_one principal).symm
    _ ≤ principal * (sanctionDailyRate * (days : ℚ)) :=
      mul_le_mul_of_nonneg_left hd (le_of_lt hp)
    _ = sanctionDailyRate * principal * (days : ℚ) := by ring
    _ = doubleInterest principal days := rfl

/-- 中文证明（具体例四）：本金 10 万元、第 5714 天 → 99995，**不足**本金。 -/
theorem doubleInterest_case_10w_5714d : doubleInterest 100000 5714 = (99995 : ℚ) := by
  norm_num [doubleInterest, sanctionDailyRate]

/-- 中文证明（具体例五）：本金 10 万元、第 5715 天 → `200025/2`＝100012.5，**超过**本金。
    两条合起来把"加倍利息追平本金"的那一天钉成可判定的读数（约 15.65 年）。 -/
theorem doubleInterest_case_10w_5715d : doubleInterest 100000 5715 = (200025 / 2 : ℚ) := by
  norm_num [doubleInterest, sanctionDailyRate]

/-- 中文证明（阈值的具体判定）：第 5714 天仍不够，第 5715 天才够。全部由 `norm_num` 算出。 -/
theorem sanction_threshold_concrete :
    doubleInterest 100000 5714 < (100000 : ℚ) ∧ (100000 : ℚ) ≤ doubleInterest 100000 5715 := by
  refine ⟨?_, ?_⟩
  · rw [doubleInterest_case_10w_5714d]
    norm_num
  · rw [doubleInterest_case_10w_5715d]
    norm_num

end Concrete

section Bridges

/-- 中文说明（**接到已经在消费数额的那一层**）：`Seams/Probability.lean:428` 的
    `abbrev Amount := ℤ`（最小货币单位）是仓内既有的金额载体，`:431` 的 `amountQ` 是它进入
    ℚ 比例比较的**唯一**通道。本件的泛函吃 ℚ，故接缝就是把 `Amount` 经 `amountQ` 送进来。
    本件**不**在此复述 `amountQ`、`exactAmountQ` 或 `Iv` 的任何定理。 -/
def doubleInterestOfAmount (amount : Amount) (days : ℕ) : ℚ :=
  doubleInterest (amountQ amount) days

/-- 中文证明（接缝的定义式可回读）：接进来的读数与直接调用泛函相同。 -/
theorem doubleInterestOfAmount_apply (amount : Amount) (days : ℕ) :
    doubleInterestOfAmount amount days = doubleInterest (amountQ amount) days := rfl

/-- 中文证明（接缝上的具体例，`norm_num` 算出）：本金 10 万（最小货币单位）、100 天 → 1750。
    与 `doubleInterest_case_10w_100d` 同读数，说明接缝**没有**改变数值口径。 -/
theorem doubleInterestOfAmount_case_10w_100d : doubleInterestOfAmount 100000 100 = (1750 : ℚ) := by
  norm_num [doubleInterestOfAmount, amountQ, doubleInterest, sanctionDailyRate]

/-- 中文证明（负额的算术后果）：`Amount` 是 ℤ，可以取负。本金位取 `-100`、100 天时泛函给出
    `-7/4`，是**负数**。法律读法：第264条与第1条第3款只管"尚未清偿的金钱债务"，
    本件**不**为负数读法作任何法律辩护，只把它做成一条可判定的警告（见未覆盖片段第 6 项）。 -/
theorem doubleInterestOfAmount_negative_is_negative :
    doubleInterestOfAmount (-100 : Amount) 100 = (-7 / 4 : ℚ) := by
  norm_num [doubleInterestOfAmount, amountQ, doubleInterest, sanctionDailyRate]

/-- 中文证明（负额读数不为零）：故调用方必须先过滤符号，本件的泛函**不会**替它过滤。 -/
theorem doubleInterestOfAmount_negative_not_zero :
    doubleInterestOfAmount (-100 : Amount) 100 ≠ 0 := by
  rw [doubleInterestOfAmount_negative_is_negative]
  norm_num

/-- 中文证明（**区间载体续算**）：本金落在既有闭区间载体 `Iv`（端点 `lo hi : ℚ`，
    见 `FullMath/Numeric/Intervals.lean:16`）且左端非负时，加倍利息落在
    `[0, 日利率 × 区间右端 × 天数]` 的两侧界内。本件只借用 `Iv.mem` 这个载体，
    **不复述**该件的 `add_sound`/`mul_sound`。 -/
theorem doubleInterest_Iv_bounds (i : Iv) (hz : (0 : ℚ) ≤ i.lo) (days : ℕ) (principal : ℚ)
    (hp : Iv.mem principal i) :
    (0 : ℚ) ≤ doubleInterest principal days ∧
      doubleInterest principal days ≤ sanctionDailyRate * i.hi * (days : ℚ) := by
  obtain ⟨hlo, hhi⟩ := hp
  have hzn : (0 : ℚ) ≤ principal := le_trans hz hlo
  have hd : (0 : ℚ) ≤ (days : ℚ) := Nat.cast_le.mpr (Nat.zero_le days)
  constructor
  · exact doubleInterest_nonneg hzn days
  · have h1 : sanctionDailyRate * principal ≤ sanctionDailyRate * i.hi :=
      mul_le_mul_of_nonneg_left hhi (le_of_lt sanctionDailyRate_pos)
    unfold doubleInterest
    exact mul_le_mul_of_nonneg_right h1 hd

end Bridges

section Boundary

/-- 中文说明（**义务登记·非已证** [代拟稿]）：迟延履行期间天数的同一性。
    第264条（仓内只有 OCR 截断记录，见头注 §二·2）与法释〔2014〕8号第1条第3款
    （只给算式）**都没有**在本仓记录里给出"迟延履行期间"的起算与届满算法：
    它取决于生效法律文书确定的履行期间，以及执行通知所确定的期间。
    本件的泛函因此把天数当**自由输入** `days : ℕ`。要挂账的目标是
    `legalDays = inputDays`——把外部文书算出的那个天数与本件输入的那个天数对上。
    本件**不**证它（Lean 里没有通往执行文书的通道），也**不**假装它无关紧要：
    下一两条定理正是它的"无关紧要"读法的否证。 -/
def sanctionPeriodDaysObligation (legalDays inputDays : ℕ) : Prop := legalDays = inputDays

/-- 中文证明（**本件对起算规则无感**·边界一）：两条候选的"期间计算规则"
    （例如按生效文书确定的履行期间届满之次日起算，与按执行通知确定的期间履行期届满日起算）
    只要对同一份案卷给出**同一个天数**，本件就给出**同一个数额**。
    即：数额泛函**不携带**任何规则信息，它不能在规则之间做选择——这一条是定理，不是散文。 -/
theorem sanction_amount_is_rule_blind (rule₁ rule₂ : ℕ → ℕ) (principal : ℚ) (record : ℕ)
    (h : rule₁ record = rule₂ record) :
    doubleInterest principal (rule₁ record) = doubleInterest principal (rule₂ record) :=
  congrArg (fun d => doubleInterest principal d) h

/-- 中文证明（**规则之差直接变成钱之差**·边界二）：本金为正时，两条规则给的天数一大一小，
    数额就一大一小。与上一条合起来读：本件既能算，也**只**能算——
    选规则是法律判断，不在本件的算术里。 -/
theorem sanction_period_rule_gap_changes_amount (rule₁ rule₂ : ℕ → ℕ) (principal : ℚ)
    (record : ℕ) (hp : 0 < principal) (h : rule₁ record < rule₂ record) :
    doubleInterest principal (rule₁ record) < doubleInterest principal (rule₂ record) :=
  doubleInterest_strict_mono_days principal hp (rule₁ record) (rule₂ record) h

/-- 中文证明（天数挂账项**不是装饰**）：`sanctionPeriodDaysObligation` 不兑现时
    （`legalDays ≠ inputDays`），本金为正则数额必不同。
    即这条等式目标**不能糊过去**：它一旦错了，钱就错了。 -/
theorem sanction_period_days_obligation_failure_changes_amount (legalDays inputDays : ℕ)
    (principal : ℚ) (hp : 0 < principal)
    (h : ¬ sanctionPeriodDaysObligation legalDays inputDays) :
    doubleInterest principal legalDays ≠ doubleInterest principal inputDays := by
  intro hall
  rcases Nat.lt_or_ge legalDays inputDays with hlt | hge
  · exact ne_of_lt (doubleInterest_strict_mono_days principal hp legalDays inputDays hlt) hall
  · have hgt : inputDays < legalDays := Nat.lt_of_le_of_ne hge (fun he => h he.symm)
    exact ne_of_lt (doubleInterest_strict_mono_days principal hp inputDays legalDays hgt) hall.symm

/-- 中文说明（**义务登记·非已证** [代拟稿]）：第264条"应当加倍支付"在本件里的**读法形状**。
    本件**没有**条文原句（头注 §二·2 已把可核验的记录逐字交代到截断处），
    故不引用假想的条文文字，只把该义务读成一个**算术形状**：
    给定非负本金与天数，存在由第1条第3款算式确定的非负数额。
    下面的定理证的仅是**这个自造读法**的算术部分，**不是**"第264条已被形式化证明"。 -/
def art264_obligationShape (principal : ℚ) (days : ℕ) : Prop :=
  0 ≤ principal → 0 ≤ doubleInterest principal days

/-- 中文证明（形状里可证的那部分）：本金非负 ⇒ 数额非负。
    档位：[构造性定义]＋[算术已证]；条文文字面仍是 `sanctionDailyRate_matches_statuteObligation`
    那条挂账项，本条**不**替它背书。 -/
theorem art264_obligationShape_holds (principal : ℚ) (days : ℕ) :
    art264_obligationShape principal days := by
  intro hp
  exact doubleInterest_nonneg hp days

/-- 中文证明（第264条**没有**把数额定成定额）：同一份本金下存在两种天数读数给出两种数额，
    故"该给多少钱"完全押在天数上，而天数不在第264条的算术里。可判定形：取 100 天与 200 天。 -/
theorem art264_amount_is_not_a_fixed_sum :
    doubleInterest 100000 100 ≠ doubleInterest 100000 200 :=
  ne_of_lt (doubleInterest_strict_mono_days 100000 (by norm_num) 100 200 (by decide))

end Boundary

/-!
### 未覆盖片段（本件**没有**表达的法律内容，逐条给缺什么）

1. **《民事诉讼法》第264条第2句**（关于"履行其他义务"的**迟延履行金**）——本仓**无该句文本记录**
   （`data/external/supreme_court/extracted_rules.json:1859` 的预览在第 1 句中间就截断，
   全文字段不存在）。本件的泛函只吃金钱本金 `ℚ`，**没有**非金钱义务的载体；
   要补需要一个"行为义务→数额"的独立泛函，不得由 `doubleInterest` 顶替。
2. **迟延履行期间的起算与届满**——已具名挂账 `sanctionPeriodDaysObligation`，
   并已由 `sanction_amount_is_rule_blind`／`sanction_period_rule_gap_changes_amount` 说明
   本件为何**只能**把它当自由输入。缺的是执行文书（生效文书确定的履行期间＋执行通知确定的期间）
   的算法与一手文本，不是 Lean 技术。
3. **2014-08-01 施行日分界与分段累计**——仓内记录见
   `docs/history/evidence-archive/0924_二十轮对辩/五轮问_致GPT_20260924.md:8、:19`（R2 簇）。
   本件是**单段、单率**泛函：`doubleInterest_add_days` 只在同一个 `sanctionDailyRate` 下可加。
   跨越施行日的旧率/新率拼接（旧口径为日万分之一点七五**之前**的另一读法）未表达。
4. **部分履行时的清偿顺位（抵充顺序）**——`doubleInterest_partial_payment_gap` 只给出
   两口径的**精确差额**；"先抵哪一笔"是执行分配问题（仓内无条文记录），本件不判。
5. **一般债务利息**与加倍部分债务利息的**并存与合计上限**——第1条第3款明写"除一般债务利息之外"，
   本件因此只表达加倍部分。`extracted_rules.json:1859` 的标题句
   "利息与加倍部分债务利息之和不能超过民间借贷利率保护上限"是**审判实务读物的裁判要旨**，
   **不是条文**，本件不据以立定理；LPR 四倍上限亦未表达。
6. **舍入与最小货币单位**——本件输出 ℚ，未接 `Seams/Probability.lean` 的
   `RoundingPolicy`／`denotateWithPolicy`／`ExactAmountM5`（`exactAmountQ` 一侧的政策读数定理
   本件**不复述**）。`doubleInterestOfAmount` 接受任意 `Amount : ℤ`，含**负数**；
   `doubleInterestOfAmount_negative_is_negative` 只是警告，符号过滤在调用方。
7. **公法制裁**（刑事罚金与没收、行政罚款与没收违法所得、暂扣/吊销许可、限制从业、行政拘留）——
   按 `docs/master-plan/09_法律统一数学模型_20261001.md §8.1` 判为越界，
   "公法制裁并列域＋禁止跨域排序"未建；本件不与任何非民事数额共线比较。
8. **执行费用、罚款、拘留**等执行程序中的其他后果：本件未表达。
   `Seams/PayoffEquilibrium.lean:369-371` 的 `withSanction` 把制裁读成一个自由参数 `k : ℚ`，
   本件给出的是 `k` 的**一个候选数值来源**，但两者的相等**未证**（跨文件桥不在本件范围，
   且本件未 import 该件，避免为一句话引入整个博弈层）。
-/

end JurisLean.Seams.SanctionInterest
