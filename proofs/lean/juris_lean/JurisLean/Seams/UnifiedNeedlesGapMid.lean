import Mathlib
import JurisLean.Seams.UnifiedNeedlesS2

/-!
# W1-7/8/9 三针差额闭合件（UnifiedNeedlesGapMid）

承接 `docs/master-plan/20261010_统一法律数学模型_连续与语义全量施工方案.md` 的
W1-7/W1-8/W1-9 三行与 `docs/master-plan/20261010_接续方案评审_Codex_R1.md` 第 2 条
表中第 15、29–31、37 行；原合同 =
`docs/spec/20261007-统一法律数学模型_附录I_Lean施工明细.md:769`（针 15）、
`:783–785`（针 29–31）、`:791`（针 37）；
行为合同 = `docs/spec/20261007-统一法律数学模型_全量施工方案.md`
§8.2/§8.3（博弈/均衡）与 §6.5（舍入/清偿/超收另账）。

## 一、本件闭合的三个差额

- **针 15**（对照 `Seams/UnifiedNeedlesS2.lean:140–168` 的旧见证：四映射全为恒等、
  "缺映射反例"只拨 `full` 位）：本件给出两个**实质不同**的类比实例
  `analogyA`/`analogyB`——四个映射各分量都真实移动点（主体 张三→李四 / 李四→张三、
  事实 已履行↔书面、规范版本 旧→新、用途 补强↔区分），共用同一 FOLLOW 判断规则
  `followJudge`（保主体/事实/规范版本/证明用途四个具体规则谓词的合取）。
  `follow_judge_preserved` 证：四谓词逐维保持 ⇒ 判断函数在映射下保持
  （结构保持按维度逐项，非计数相同）；判断可分（同一规则分出支持/驳回）。
  `SubstantiveAnalogy` 是"实质不同"的显式判据：S2 旧见证 `fullIdMap` 四条全不成立，
  两个新实例全过且两实例彼此不同（`analogy_real_maps_substantive`）。

- **针 29–31**（对照 `Seams/UnifiedNeedlesS4.lean:25–34、61–65` 的两玩家特设载体）：
  **任意有限玩家**（玩家型 `I` 任意 Fintype，玩家数由 `I` 决定）、**混合策略**
  （每玩家一条 ℚ 概率向量，`RowSimplex`/`InSimplex` 承载 §8.2 的单纯形积）、
  **完整偏离枚举**（`IsNash` 对每个玩家 × 每条混合行偏差全称量化）、
  **同一"全部均衡"关系**（`IsNash`/`IsEpsNash` 只定义一次、对任意玩家数通用，
  不改成只有一个剖面）。`nash_iff_no_pure_dev_gain` 证"策略组合是纳什均衡 ↔
  无任一玩家任一纯偏离获益"（§8.2：纯偏离足够，任意混合偏离收益是其凸组合——
  凸组合/线性引理 `eu_dev_linear`）。实例：三玩家（`Fin 3`）剖面是均衡
  （`three_player_mixed_nash_instance`）；同一博弈另一剖面非均衡
  （`three_player_not_nash_counterexample`）。
  针 31：`eu_abs_sub_le`（混合期望保持——逐剖面逐玩家收益误差 ≤ η ⇒ 期望收益
  误差 ≤ η，总概率归一用 `Fintype.prod_sum`）＋
  `payoff_error_yields_two_eta_equilibrium_nplayer`（近似模型 ε-均衡折回真实模型
  (ε+2η)-均衡，全允许偏离统一 η）＋针 29 的 ε = 0 传递
  `external_equilibrium_reflects_legal_nplayer`。

- **针 37**（对照 `Seams/UnifiedNeedlesS5.lean:134–142` 的 Nat 截抵）：金额一律 ℚ；
  **债项身份**（`DebtItem`：ident 标识 + `DebtKind` 本金/利息/费用分型）；
  **法定抵充顺序**（`statOrder`：费用→利息→本金的确定性顺序，债项列按序供给）；
  逐项 min 递推（`stepAlloc`/`runPay`/`runRes`，§6.5 合同原形）；
  `StatRun` 归纳刻画 ⇒ **冲抵结果唯一**（`discharge_unique`：任何满足法定刻画的
  冲抵记录都等于标准运行）；对账闭合 `Σ冲抵 + 溢余 = p`（telescope，
  `runPay_sum_add_runRes`）；溢余非负（不压成负债务，`runRes_nonneg`）；
  **超收另账**（`overpay_separate_account`：溢余 > 0 ⇒ 总冲抵 = 总到期额，
  溢余 = p − 总到期额 全额记另账，不冲抵任何债项）；顺位的 T25 公开更正式
  （`Prioritized`：逐项不超抵 + 某项未足额则其后全零，即 a_j>0 ⇒ 前组足额；
  `prioritized_adjacent` 给直读形式）；债项身份保持（`dischargeItems_ident`）
  且无负余额（`dischargeItems_nonneg`）；支付流端到端（`flow_payment_closed`）＋
  具体见证读数（`statDebts_readout`）。

## 二、显式假设与开放点（fail-closed 声明）

1. 针 29–31 是**静态博弈片段**：每玩家一个信息集（单决策点），"每个信息集的偏离"
   在此退化为"每玩家混合行偏差"的全称枚举；§8.3 的多信息集/序贯均衡另案（W2）。
2. 法定抵充顺序按费用→利息→本金（民法典第 561 条顺序）编码为 `statOrder`；
   合同约定顺序由债项列的排列表达（调用方供序），本件不引入其他法定顺序变体。
3. 金额、概率全为 ℚ；无 Nat 截断、无浮点（仓规 LegalTech 约束 2）。
   概率向量为逐行 ℚ 定义（`Act → ℚ`），§8.2 的"单纯形积"以谓词承载，
   不使用 Mathlib pmf 载体。
4. 针 15 的"结构归纳"在四维载体逐项保持的层面闭合
   （`follow_judge_preserved` 对任意载体类型通用），不冒称对无限规范文本的归纳。
5. 判断规则 FOLLOW、收益表 `u3`、债项集 `statDebts` 数值均为 [代拟稿]，无经验校准。

## 三、档位

零 `sorry`／零自定义 `axiom`／零 `True` 逃避；`decide` 仅用于闭式字面量求值。
本机不编译 Lean：CI_NOT_RUN（fail-closed），Actions 模块轮为唯一 Lean 权威。
-/

namespace JurisLean.Seams.UnifiedNeedlesGapMid

open JurisLean.Seams.UnifiedNeedlesS2

/-! ## 第 15 针：analogy_preserves_judgment_under_full_conditions（真实不同映射与判断函数） -/

/-- 主体载体：两名自然人 + 一名法人。 -/
inductive GapSubject
  | zhang
  | li
  | corp
  deriving DecidableEq

/-- 事实载体：有书面约定 / 已实际履行 / 仅口头主张。 -/
inductive GapFact
  | written
  | performed
  | oralOnly
  deriving DecidableEq

/-- 规范版本载体：民法典施行前 / 施行后。 -/
inductive GapVersion
  | preCode
  | postCode
  deriving DecidableEq

/-- 证明用途载体：遵循先例（FOLLOW） / 区分本案 / 仅补强证据。 -/
inductive GapUse
  | follow
  | distinguish
  | reinforce
  deriving DecidableEq

/-- 判断载体：支持 / 驳回。 -/
inductive GapJudg
  | uphold
  | reject
  deriving DecidableEq

/-- 具体规则之一（主体维）：是否自然人。 -/
def isNaturalPerson : GapSubject → Bool
  | .zhang => true
  | .li => true
  | .corp => false

/-- 具体规则之一（事实维）：事实是否已获证据支撑。 -/
def evidencedFact : GapFact → Bool
  | .written => true
  | .performed => true
  | .oralOnly => false

/-- 具体规则之一（版本维）：系争规则在该版本下是否存在。 -/
def ruleInVersion : GapVersion → Bool
  | .preCode => true
  | .postCode => true

/-- 具体规则之一（用途维）：是否为遵循先例（FOLLOW）用途。 -/
def followUse : GapUse → Bool
  | .follow => true
  | .distinguish => false
  | .reinforce => false

/-- FOLLOW 判断规则（具体规则，非计数相同）：四谓词合取时支持，否则驳回。 -/
def followJudge (s : GapSubject) (f : GapFact) (v : GapVersion) (u : GapUse) : GapJudg :=
  if isNaturalPerson s && evidencedFact f && ruleInVersion v && followUse u then
    GapJudg.uphold
  else
    GapJudg.reject

/-- **结构保持的一般引理**：若类比映射在四个维度上分别保持对应的规则谓词，
    则以四谓词合取为判断规则的类比，其判断在映射下保持——逐维归纳，
    而非计数相同。 -/
theorem follow_judge_preserved {S F V U : Type} (m : AnalogyMap S F V U GapJudg)
    (ps : S → Bool) (pf : F → Bool) (pv : V → Bool) (pu : U → Bool)
    (hS : ∀ s, ps (m.onSubject s) = ps s) (hF : ∀ f, pf (m.onFacts f) = pf f)
    (hV : ∀ v, pv (m.onVersion v) = pv v) (hU : ∀ u, pu (m.onUse u) = pu u)
    (hj : m.judge
      = fun s f v u =>
        if ps s && pf f && pv v && pu u then GapJudg.uphold else GapJudg.reject) :
    ∀ s f v u,
      m.judge (m.onSubject s) (m.onFacts f) (m.onVersion v) (m.onUse u) = m.judge s f v u := by
  rw [hj]
  intro s f v u
  simp only [hS, hF, hV, hU]

/-- 实例 A：张三搬给李四（自然人→自然人）、已履行搬为书面（有据→有据）、
    旧版本搬为新版本（规则俱在）、补强搬为区分（非 FOLLOW→非 FOLLOW）。
    四映射都真实移动点；判断函数 = FOLLOW 规则；full = true。 -/
def analogyA : AnalogyMap GapSubject GapFact GapVersion GapUse GapJudg where
  onSubject := fun
    | .zhang => .li
    | s => s
  onFacts := fun
    | .performed => .written
    | f => f
  onVersion := fun
    | .preCode => .postCode
    | v => v
  onUse := fun
    | .reinforce => .distinguish
    | u => u
  judge := followJudge
  full := true

/-- 实例 B：与 A 实质不同——主体反向（李四→张三）、事实反向（书面→已履行）、
    版本同向（旧→新）、用途反向（区分→补强）。四映射也都真实移动点。 -/
def analogyB : AnalogyMap GapSubject GapFact GapVersion GapUse GapJudg where
  onSubject := fun
    | .li => .zhang
    | s => s
  onFacts := fun
    | .written => .performed
    | f => f
  onVersion := fun
    | .preCode => .postCode
    | v => v
  onUse := fun
    | .distinguish => .reinforce
    | u => u
  judge := followJudge
  full := true

/-- 实例 A 的四维规则逐项保持（主体/事实/版本/用途）。 -/
theorem analogyA_rules_preserved :
    (∀ s, isNaturalPerson (analogyA.onSubject s) = isNaturalPerson s) ∧
    (∀ f, evidencedFact (analogyA.onFacts f) = evidencedFact f) ∧
    (∀ v, ruleInVersion (analogyA.onVersion v) = ruleInVersion v) ∧
    (∀ u, followUse (analogyA.onUse u) = followUse u) :=
  ⟨fun s => by cases s <;> rfl, fun f => by cases f <;> rfl,
    fun v => by cases v <;> rfl, fun u => by cases u <;> rfl⟩

/-- 实例 B 的四维规则逐项保持。 -/
theorem analogyB_rules_preserved :
    (∀ s, isNaturalPerson (analogyB.onSubject s) = isNaturalPerson s) ∧
    (∀ f, evidencedFact (analogyB.onFacts f) = evidencedFact f) ∧
    (∀ v, ruleInVersion (analogyB.onVersion v) = ruleInVersion v) ∧
    (∀ u, followUse (analogyB.onUse u) = followUse u) :=
  ⟨fun s => by cases s <;> rfl, fun f => by cases f <;> rfl,
    fun v => by cases v <;> rfl, fun u => by cases u <;> rfl⟩

/-- 实例 A 在 S2 的 `analogyPreserves` 读法下成立（full 位 + 四维逐项保持）。 -/
theorem analogyA_preserves : analogyPreserves analogyA := by
  have hr := analogyA_rules_preserved
  exact ⟨rfl,
    follow_judge_preserved analogyA isNaturalPerson evidencedFact ruleInVersion followUse
      hr.1 hr.2.1 hr.2.2.1 hr.2.2.2 rfl⟩

/-- 实例 B 在 S2 的 `analogyPreserves` 读法下成立。 -/
theorem analogyB_preserves : analogyPreserves analogyB := by
  have hr := analogyB_rules_preserved
  exact ⟨rfl,
    follow_judge_preserved analogyB isNaturalPerson evidencedFact ruleInVersion followUse
      hr.1 hr.2.1 hr.2.2.1 hr.2.2.2 rfl⟩

/-- 判断可分：同一 FOLLOW 规则分得出支持与驳回两个判断。 -/
theorem followJudge_separates :
    followJudge GapSubject.zhang GapFact.written GapVersion.postCode GapUse.follow
      = GapJudg.uphold ∧
    followJudge GapSubject.corp GapFact.oralOnly GapVersion.postCode GapUse.distinguish
      = GapJudg.reject :=
  ⟨rfl, rfl⟩

/-- **"实质不同"显式判据**：四个映射每个都真实移动至少一个点
    （不是恒等映射，也不是只拨 full 位）。判据只看四映射，对任意判断载体通用。 -/
def SubstantiveAnalogy {S F V U J : Type} (m : AnalogyMap S F V U J) : Prop :=
  (∃ s, m.onSubject s ≠ s) ∧ (∃ f, m.onFacts f ≠ f) ∧
    (∃ v, m.onVersion v ≠ v) ∧ (∃ u, m.onUse u ≠ u)

/-- 两实例彼此实质不同（主体映射方向相反）。 -/
theorem analogyA_ne_analogyB : analogyA ≠ analogyB := by
  intro h
  exact GapSubject.noConfusion (congrFun (congrArg AnalogyMap.onSubject h) GapSubject.zhang)

/-- **第 15 针（S2，附录 I:769；BINDING 行 15）差额闭合**：真实不同映射与判断函数。
    (1)(2) 两个具体实例都过"实质不同"判据——四映射各分量真变，不是只拨 full 位；
    (3) 两实例彼此实质不同；(4) S2 旧见证 `fullIdMap`（恒等四映射 + 合取判断 +
    full 位）在判据下四条全不成立——旧见证的"缺映射反例只拨 full 位"被显式排除；
    (5)(6) 两实例在 S2 的 `analogyPreserves` 读法下都成立（结构保持按主体/事实/
    版本/用途及 FOLLOW 等具体规则逐维保持）；(7) 判断可分。 -/
theorem analogy_real_maps_substantive :
    SubstantiveAnalogy analogyA ∧
    SubstantiveAnalogy analogyB ∧
    analogyA ≠ analogyB ∧
    ¬ SubstantiveAnalogy fullIdMap ∧
    analogyPreserves analogyA ∧
    analogyPreserves analogyB ∧
    (followJudge GapSubject.zhang GapFact.written GapVersion.postCode GapUse.follow
        = GapJudg.uphold ∧
      followJudge GapSubject.corp GapFact.oralOnly GapVersion.postCode GapUse.distinguish
        = GapJudg.reject) := by
  refine ⟨⟨⟨GapSubject.zhang, by decide⟩, ⟨GapFact.performed, by decide⟩,
      ⟨GapVersion.preCode, by decide⟩, ⟨GapUse.reinforce, by decide⟩⟩,
    ⟨⟨GapSubject.li, by decide⟩, ⟨GapFact.written, by decide⟩,
      ⟨GapVersion.preCode, by decide⟩, ⟨GapUse.distinguish, by decide⟩⟩,
    analogyA_ne_analogyB, ?_, analogyA_preserves, analogyB_preserves, followJudge_separates⟩
  intro h
  obtain ⟨⟨s, hs⟩, -, -, -⟩ := h
  exact hs rfl

/-! ## 第 29–31 针：任意有限玩家的混合策略均衡（同一"全部均衡"关系） -/

section GameTheory

variable {I : Type} [Fintype I] [DecidableEq I] {Act : Type} [Fintype Act] [DecidableEq Act]

/-- 单行概率向量（一个玩家的混合策略）：非负且归一。 -/
def RowSimplex (p : Act → ℚ) : Prop := (∀ a, 0 ≤ p a) ∧ (∑ a, p a = 1)

/-- 混合策略剖面：每玩家一条概率向量（§8.2 单纯形积）。 -/
def InSimplex (σ : I → Act → ℚ) : Prop := ∀ i, RowSimplex (σ i)

/-- 概率点：全押在 `b` 上的点质量。 -/
def point (b : Act) : Act → ℚ := fun a => if a = b then 1 else 0

/-- 概率点剖面：每玩家全押其指定纯行动。 -/
def pureM (p : I → Act) : I → Act → ℚ := fun i a => if a = p i then 1 else 0

theorem point_rowSimplex (b : Act) : RowSimplex (point b) := by
  constructor
  · intro a
    simp only [point]
    split_ifs <;> norm_num
  · simp only [point, Fintype.sum_ite_eq']

theorem pureM_rowSimplex (p : I → Act) (i : I) : RowSimplex (pureM p i) :=
  point_rowSimplex (p i)

theorem pureM_inSimplex (p : I → Act) : InSimplex (pureM p) :=
  fun i => pureM_rowSimplex p i

/-- 单方偏差：玩家 `i` 把自己的行换成 `σ'`（完整偏离映射的单步：
    IsNash 对每个玩家、每条混合行偏差全称枚举）。 -/
def dev (σ : I → Act → ℚ) (i : I) (σ' : Act → ℚ) : I → Act → ℚ :=
  Function.update σ i σ'

/-- 期望收益：`eu u σ i = Σ_a ∏_j σ_j(a_j) · u_i(a)`（§8.2 混合延拓合同）。 -/
def eu (u : (I → Act) → I → ℚ) (σ : I → Act → ℚ) (i : I) : ℚ :=
  ∑ a, (∏ j, σ j (a j)) * u a i

/-- 点质量求值：纯剖面的混合延拓恰为该剖面的收益。 -/
theorem eu_pureM (u : (I → Act) → I → ℚ) (p : I → Act) (i : I) :
    eu u (pureM p) i = u p i := by
  have hprod : ∀ a : I → Act,
      (∏ j, (if a j = p j then (1 : ℚ) else 0)) = if (∀ j, a j = p j) then 1 else 0 := by
    intro a
    by_cases hall : ∀ j, a j = p j
    · rw [if_pos hall]
      exact Finset.prod_eq_one (fun j _ => by rw [if_pos (hall j)])
    · rw [if_neg hall]
      simp only [not_forall] at hall
      obtain ⟨j₀, hj₀⟩ := hall
      exact Finset.prod_eq_zero (Finset.mem_univ j₀) (by rw [if_neg hj₀])
  have hstep : ∀ a : I → Act, (∏ j, pureM p j (a j)) * u a i = if a = p then u p i else 0 := by
    intro a
    simp only [pureM]
    rw [hprod a]
    by_cases hall : ∀ j, a j = p j
    · rw [if_pos hall, if_pos (funext hall), funext hall]
      ring
    · simp only [not_forall] at hall
      obtain ⟨j₀, hj₀⟩ := hall
      rw [if_neg (fun hxe => hj₀ (hxe j₀)), if_neg (fun hxe => hj₀ (congrFun hxe j₀))]
      ring
  show (∑ a, (∏ j, pureM p j (a j)) * u a i) = u p i
  rw [Finset.sum_congr rfl (fun a _ => hstep a)]
  simp only [Fintype.sum_ite_eq']

/-- 单方偏差的更新读法。 -/
theorem update_pureM (p : I → Act) (i : I) (b : Act) :
    Function.update (pureM p) i (point b) = pureM (Function.update p i b) := by
  funext j a
  simp only [pureM]
  rw [Function.update_apply, Function.update_apply]
  by_cases hj : j = i
  · subst hj
    simp [point]
  · simp only [if_neg hj]

/-- 单行点质量的加权求和。 -/
theorem sum_point_weight (σ' : Act → ℚ) (b : Act) :
    ∑ a', σ' a' * (point a') b = σ' b := by
  have h : ∀ a', σ' a' * (point a') b = if b = a' then σ' a' else 0 := by
    intro a'
    simp only [point]
    split_ifs <;> ring
  calc ∑ a', σ' a' * (point a') b
      = ∑ a', if b = a' then σ' a' else 0 := Finset.sum_congr rfl (fun a' _ => h a')
    _ = σ' b := Fintype.sum_ite_eq b (fun a' => σ' a')

/-- **凸组合（线性）引理**：把玩家 i 的行换成任意概率向量 σ'，其期望收益是各
    纯偏离（点质量）期望的 σ'-加权平均——§8.2"纯偏离足够，混合偏离收益是
    其凸组合"的载体引理。 -/
theorem eu_dev_linear (u : (I → Act) → I → ℚ) (σ : I → Act → ℚ) (i : I) (σ' : Act → ℚ)
    (hσ' : RowSimplex σ') :
    eu u (dev σ i σ') i = ∑ a', σ' a' * eu u (dev σ i (point a')) i := by
  have hfac : ∀ (a : I → Act) (τ : Act → ℚ),
      (∏ j, Function.update σ i τ j (a j))
        = τ (a i) * ∏ j ∈ Finset.univ \ ({i} : Finset I), σ j (a j) := by
    intro a τ
    have hperj : ∀ j : I, Function.update σ i τ j (a j)
        = Function.update (fun k => σ k (a k)) i (τ (a i)) j := by
      intro j
      by_cases hji : j = i
      · subst hji
        rw [Function.update_apply, Function.update_apply, if_pos rfl, if_pos rfl]
      · rw [Function.update_apply, Function.update_apply, if_neg hji, if_neg hji]
    rw [Finset.prod_congr rfl (fun j _ => hperj j)]
    exact Finset.prod_update_of_mem (Finset.mem_univ i) (fun k => σ k (a k)) (τ (a i))
  have hpoint : ∀ a' : Act, eu u (dev σ i (point a')) i
      = ∑ a, ((point a') (a i) * ∏ j ∈ Finset.univ \ ({i} : Finset I), σ j (a j)) * u a i := by
    intro a'
    simp only [eu, dev, hfac]
  show (∑ a, (∏ j, Function.update σ i σ' j (a j)) * u a i)
      = ∑ a', σ' a' * eu u (dev σ i (point a')) i
  simp only [hfac, hpoint]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have hterm : ∀ a' : Act,
      σ' a' * (((point a') (a i) * ∏ j ∈ Finset.univ \ ({i} : Finset I), σ j (a j)) * u a i)
        = (σ' a' * (point a') (a i))
          * ((∏ j ∈ Finset.univ \ ({i} : Finset I), σ j (a j)) * u a i) := fun a' => by ring
  rw [Finset.sum_congr rfl (fun a' _ => hterm a'), ← Finset.sum_mul, sum_point_weight]
  ring

/-- **同一"全部均衡"关系（精确版）**：剖面 σ 是纳什均衡 ↔ 没有任何玩家能用任何
    混合偏差获益。偏差域 = 全体单行概率向量——每个玩家 × 每个混合偏差都被枚举
    （静态片段：每玩家单信息集，故信息集偏离退化为行偏差）。只此一个定义，
    对任意有限玩家数通用。 -/
def IsNash (u : (I → Act) → I → ℚ) (σ : I → Act → ℚ) : Prop :=
  ∀ (i : I) (σ' : Act → ℚ), RowSimplex σ' →
    eu u (Function.update σ i σ') i ≤ eu u σ i

/-- **同一"全部均衡"关系（带误差版）**。 -/
def IsEpsNash (u : (I → Act) → I → ℚ) (ε : ℚ) (σ : I → Act → ℚ) : Prop :=
  ∀ (i : I) (σ' : Act → ℚ), RowSimplex σ' →
    eu u (Function.update σ i σ') i ≤ eu u σ i + ε

/-- **第 30 针的同一全部均衡关系（附录 I:783–784）**：策略组合是纳什均衡 ↔
    无任一玩家任一纯偏离获益——§8.2 的多项式均衡描述（σ_i ≥ 0、Σσ_i = 1、
    u_i(σ) ≥ u_i(a'_i, σ₋ᵢ) 对每个纯偏离）与全偏差定义的等价。任意有限玩家。 -/
theorem nash_iff_no_pure_dev_gain (u : (I → Act) → I → ℚ) (σ : I → Act → ℚ) :
    IsNash u σ ↔ ∀ (i : I) (b : Act),
      eu u (Function.update σ i (point b)) i ≤ eu u σ i := by
  constructor
  · intro h i b
    exact h i (point b) (point_rowSimplex b)
  · intro h i σ' hσ'
    show eu u (dev σ i σ') i ≤ eu u σ i
    rw [eu_dev_linear u σ i σ' hσ']
    calc ∑ a', σ' a' * eu u (dev σ i (point a')) i
        ≤ ∑ a', σ' a' * eu u σ i :=
          Finset.sum_le_sum (fun a' _ =>
            mul_le_mul_of_nonneg_left (h i a') (hσ'.1 a'))
      _ = (∑ a', σ' a') * eu u σ i := (Finset.sum_mul _ _ _).symm
      _ = 1 * eu u σ i := by rw [hσ'.2]
      _ = eu u σ i := one_mul _

set_option maxHeartbeats 1000000 in
/-- 单剖面期望扰动界：逐剖面逐玩家收益误差 ≤ η 且 σ 在单纯形内时，
    期望收益误差 ≤ η（混合期望保持；总概率归一）。 -/
theorem eu_abs_sub_le (u v : (I → Act) → I → ℚ) (η : ℚ) (j : I) (σ : I → Act → ℚ)
    (hσ : InSimplex σ) (hpt : ∀ a k, |v a k - u a k| ≤ η) :
    |eu v σ j - eu u σ j| ≤ η := by
  have hw : ∀ a : I → Act, 0 ≤ ∏ k : I, σ k (a k) :=
    fun a => Finset.prod_nonneg (fun k _ => (hσ k).1 (a k))
  have htotal : ∑ a : I → Act, ∏ k : I, σ k (a k) = (1 : ℚ) :=
    (Fintype.prod_sum (R := ℚ) (fun (k : I) (a : Act) => σ k a)).symm.trans
      (Finset.prod_eq_one (fun k _ => (hσ k).2))
  have hsplit : eu v σ j - eu u σ j
      = ∑ a : I → Act, (∏ k : I, σ k (a k)) * (v a j - u a j) := by
    simp only [eu]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun a _ => by ring)
  calc |eu v σ j - eu u σ j|
      = |∑ a, (∏ k, σ k (a k)) * (v a j - u a j)| := by rw [hsplit]
    _ ≤ ∑ a, |(∏ k, σ k (a k)) * (v a j - u a j)| :=
        Finset.abs_sum_le_sum_abs (fun a => (∏ k, σ k (a k)) * (v a j - u a j)) Finset.univ
    _ = ∑ a, (∏ k, σ k (a k)) * |v a j - u a j| :=
        Finset.sum_congr rfl (fun a _ => by rw [abs_mul, abs_of_nonneg (hw a)])
    _ ≤ ∑ a, (∏ k, σ k (a k)) * η :=
        Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hpt a j) (hw a))
    _ = (∑ a : I → Act, ∏ k : I, σ k (a k)) * η := (Finset.sum_mul _ _ _).symm
    _ = η * 1 := by rw [htotal]; ring
    _ = η := mul_one _

/-- **第 31 针（任意有限玩家版）**：收益误差产出 (ε+2η)-均衡——全允许偏离统一 η、
    混合期望保持。近似模型 `v` 的 ε-均衡折回真实模型 `u` 的 (ε+2η)-均衡；
    同一 `IsEpsNash` 关系对任意有限玩家数成立。 -/
theorem payoff_error_yields_two_eta_equilibrium_nplayer
    (u v : (I → Act) → I → ℚ) (η ε : ℚ) (σ : I → Act → ℚ)
    (hσ : InSimplex σ) (hpt : ∀ a k, |v a k - u a k| ≤ η)
    (hrat : IsEpsNash v ε σ) : IsEpsNash u (ε + 2 * η) σ := by
  intro i σ' hσ'
  have hupd : InSimplex (Function.update σ i σ') := by
    intro k
    by_cases hk : k = i
    · subst hk
      simpa only [Function.update_self] using hσ'
    · rw [Function.update_apply, if_neg hk]
      exact hσ k
  have h1 : |eu v (Function.update σ i σ') i - eu u (Function.update σ i σ') i| ≤ η :=
    eu_abs_sub_le u v η i _ hupd hpt
  have h2 := hrat i σ' hσ'
  have h3 : |eu v σ i - eu u σ i| ≤ η := eu_abs_sub_le u v η i σ hσ hpt
  have h1' : eu u (Function.update σ i σ') i ≤ eu v (Function.update σ i σ') i + η := by
    linarith [(abs_le.mp h1).1]
  have h3' : eu v σ i ≤ eu u σ i + η := by
    linarith [(abs_le.mp h3).2]
  linarith

/-- **第 29 针（任意有限玩家版）**：外部估计的精确均衡折回法律收益——ε = 0 情形的
    ε+2η 传递。同一 `IsNash` 关系读入、同一 `IsEpsNash` 关系读出，任意有限玩家、
    混合策略、完整偏离枚举，不改成只有一个剖面。 -/
theorem external_equilibrium_reflects_legal_nplayer
    (u v : (I → Act) → I → ℚ) (η : ℚ) (σ : I → Act → ℚ)
    (hσ : InSimplex σ) (hpt : ∀ a k, |v a k - u a k| ≤ η)
    (hrat : IsNash v σ) : IsEpsNash u (2 * η) σ := by
  intro i σ' hσ'
  have h := payoff_error_yields_two_eta_equilibrium_nplayer u v η 0 σ hσ hpt
    (fun j τ hτ => by simpa only [add_zero] using hrat j τ hτ) i σ' hσ'
  simpa only [zero_add] using h

/-! ### 三玩家实例与非均衡反例 -/

/-- 三玩家二行动实例收益表：`u3 a i = if a i then 1 else 0`——每玩家的收益
    只由自己的行动决定（[代拟稿] 合规博弈：坚持则得 1，背离得 0）。 -/
def u3 (a : Fin 3 → Bool) (i : Fin 3) : ℚ := if a i then 1 else 0

/-- **≥3 玩家实例**：同一 `IsNash` 关系在 Fin 3 上实例化——全体全押"坚持"的
    剖面是纳什均衡（任意玩家任意混合偏差都不获益），且给出闭式读数。 -/
theorem three_player_mixed_nash_instance :
    IsNash u3 (pureM (fun _ : Fin 3 => true)) ∧
    (u3 (fun _ : Fin 3 => true) 0 = 1 ∧ u3 (fun _ : Fin 3 => false) 0 = 0) := by
  refine ⟨?_, rfl, rfl⟩
  rw [nash_iff_no_pure_dev_gain]
  intro i b
  rw [update_pureM]
  simp only [eu_pureM]
  have hdev : u3 (Function.update (fun _ : Fin 3 => true) i b) i = if b then (1 : ℚ) else 0 := by
    simp only [u3, Function.update_self]
  rw [hdev]
  cases b <;> simp [u3] <;> norm_num

/-- **非均衡反例**：同一 `IsNash` 关系在 Fin 3 上——全体全押"背离"的剖面不是
    均衡：玩家 0 单方纯偏离到"坚持"严格获益（1 > 0）。 -/
theorem three_player_not_nash_counterexample :
    ¬ IsNash u3 (pureM (fun _ : Fin 3 => false)) := by
  rw [nash_iff_no_pure_dev_gain]
  intro h
  have h1 : eu u3 (Function.update (pureM (fun _ : Fin 3 => false)) 0 (point true)) 0 = 1 := by
    rw [update_pureM, eu_pureM]
    simp [u3, Function.update_self]
  have h2 : eu u3 (pureM (fun _ : Fin 3 => false)) 0 = 0 := by
    rw [eu_pureM]
    rfl
  have hbad := h 0 true
  rw [h1, h2] at hbad
  exact absurd hbad (by decide)

end GameTheory

/-! ## 第 37 针：actual_payment_discharge_exact（真实支付、债项身份、法定抵充、超收另账） -/

/-- 债项分型：法定费用 / 利息 / 本金。 -/
inductive DebtKind
  | fee
  | interest
  | principal

/-- 法定抵充顺位：费用 → 利息 → 本金（民法典第 561 条顺序的确定性编码）。 -/
def statOrder : DebtKind → Nat
  | .fee => 0
  | .interest => 1
  | .principal => 2

/-- 债项身份：标识 + 分型 + 到期金额（金额 ℚ，非 Nat 截断）。 -/
structure DebtItem where
  ident : Nat
  kind : DebtKind
  amount : ℚ

/-- 单步法定抵充：本次冲抵 = min(到期额, 余款)。 -/
def stepAlloc (r : ℚ) (d : DebtItem) : ℚ := if d.amount ≤ r then d.amount else r

/-- 单步余款更新：余款' = 余款 − 本次冲抵。 -/
def stepRest (r : ℚ) (d : DebtItem) : ℚ := r - stepAlloc r d

theorem stepAlloc_eq_min (r : ℚ) (d : DebtItem) : stepAlloc r d = min d.amount r := by
  unfold stepAlloc
  split
  · exact (min_eq_left ‹d.amount ≤ r›).symm
  · exact (min_eq_right (le_of_not_ge ‹¬(d.amount ≤ r)›)).symm

theorem stepAlloc_le_amount (r : ℚ) (d : DebtItem) : stepAlloc r d ≤ d.amount := by
  rw [stepAlloc_eq_min]
  exact min_le_left _ _

theorem stepAlloc_le_r (r : ℚ) (d : DebtItem) : stepAlloc r d ≤ r := by
  rw [stepAlloc_eq_min]
  exact min_le_right _ _

theorem stepAlloc_eq_amount_of_le {r : ℚ} {d : DebtItem} (h : d.amount ≤ r) :
    stepAlloc r d = d.amount := by
  rw [stepAlloc_eq_min]
  exact min_eq_left h

theorem stepAlloc_eq_self_of_lt {r : ℚ} {d : DebtItem} (h : stepAlloc r d < d.amount) :
    stepAlloc r d = r := by
  rw [stepAlloc_eq_min] at h ⊢
  rcases le_total d.amount r with hle | hge
  · rw [min_eq_left hle] at h
    exact absurd h (lt_irrefl _)
  · exact min_eq_right hge

theorem stepAlloc_zero (d : DebtItem) (hd : 0 ≤ d.amount) : stepAlloc 0 d = 0 := by
  rw [stepAlloc_eq_min]
  exact min_eq_right hd

/-- 按序抵充：对债项列依给定顺序（法定顺序）逐项冲抵，输出各项冲抵额。 -/
def runPay : ℚ → List DebtItem → List ℚ
  | _, [] => []
  | r, d :: ds => stepAlloc r d :: runPay (r - stepAlloc r d) ds

/-- 抵充后的余款（溢余即另账金额）。 -/
def runRes : ℚ → List DebtItem → ℚ
  | r, [] => r
  | r, d :: ds => runRes (r - stepAlloc r d) ds

/-- 法定抵充运行记录的归纳刻画：余款 r 起步，逐项冲抵额 = stepAlloc r d，
    余款同步递减。任何满足该刻画的两份冲抵记录相等（结果唯一性的刻画侧）。 -/
inductive StatRun : ℚ → List DebtItem → List ℚ → Prop
  | nil {r : ℚ} : StatRun r [] []
  | cons {r : ℚ} {d : DebtItem} {ds : List DebtItem} {as : List ℚ}
      (h : StatRun (r - stepAlloc r d) ds as) :
      StatRun r (d :: ds) (stepAlloc r d :: as)

theorem statRun_exists (p : ℚ) : ∀ (ds : List DebtItem), StatRun p ds (runPay p ds) := by
  intro ds
  induction ds generalizing p with
  | nil => exact StatRun.nil
  | cons d ds ih => exact StatRun.cons (ih (p - stepAlloc p d))

theorem statRun_unique : ∀ (ds : List DebtItem) (a b : List ℚ) (r : ℚ),
    StatRun r ds a → StatRun r ds b → a = b := by
  intro ds
  induction ds with
  | nil =>
      intro a b r ha hb
      cases ha
      cases hb
      rfl
  | cons d ds ih =>
      intro a b r ha hb
      cases ha with
      | cons ha =>
          cases hb with
          | cons hb => rw [ih _ _ _ ha hb]

theorem statRun_length : ∀ (ds : List DebtItem) (a : List ℚ) (r : ℚ),
    StatRun r ds a → a.length = ds.length := by
  intro ds a r h
  induction h with
  | nil => rfl
  | @cons _ _ _ as _ ih => simp only [List.length_cons, ih]

/-- **冲抵结果唯一性**：任何满足法定刻画（逐项 min 递推）的冲抵记录都等于标准
    运行 `runPay` 的输出——给定支付与债项集，法定冲抵结果唯一。 -/
theorem discharge_unique (p : ℚ) (ds : List DebtItem) (a : List ℚ)
    (h : StatRun p ds a) : a = runPay p ds :=
  statRun_unique ds a (runPay p ds) p h (statRun_exists p ds)

/-- 对账闭合（望远镜）：Σ各项冲抵 + 溢余 = 支付额。 -/
theorem runPay_sum_add_runRes : ∀ (ds : List DebtItem) (r : ℚ),
    (runPay r ds).sum + runRes r ds = r := by
  intro ds
  induction ds with
  | nil => intro r; simp [runPay, runRes]
  | cons d ds ih =>
      intro r
      simp only [runPay, runRes, List.sum_cons]
      linarith [ih (r - stepAlloc r d)]

/-- 溢余非负：余款在逐项冲抵下永不变负（不压成负债务）。 -/
theorem runRes_nonneg : ∀ (ds : List DebtItem) (r : ℚ),
    0 ≤ r → (∀ d ∈ ds, 0 ≤ d.amount) → 0 ≤ runRes r ds := by
  intro ds
  induction ds with
  | nil => intro r hr _; simpa [runRes] using hr
  | cons d ds ih =>
      intro r hr hpos
      refine ih (r - stepAlloc r d) ?_ ?_
      · have hmin := stepAlloc_le_r r d
        linarith
      · intro d' hd'
        exact hpos d' (List.mem_cons_of_mem _ hd')

theorem runRes_zero : ∀ (ds : List DebtItem), (∀ d ∈ ds, 0 ≤ d.amount) → runRes 0 ds = 0 := by
  intro ds
  induction ds with
  | nil => intro _; rfl
  | cons d ds ih =>
      intro hpos
      have hd : 0 ≤ d.amount := hpos d List.mem_cons_self
      show runRes (0 - stepAlloc 0 d) ds = 0
      rw [stepAlloc_zero d hd, sub_zero]
      exact ih (fun d' hd' => hpos d' (List.mem_cons_of_mem _ hd'))

theorem runPay_zero_all : ∀ (ds : List DebtItem), (∀ d ∈ ds, 0 ≤ d.amount) →
    ∀ x ∈ runPay 0 ds, x = 0 := by
  intro ds
  induction ds with
  | nil => intro _ x hx; simp [runPay] at hx
  | cons d ds ih =>
      intro hpos x hx
      have hd : 0 ≤ d.amount := hpos d List.mem_cons_self
      simp only [runPay] at hx
      rcases List.mem_cons.1 hx with hx | hx
      · rw [hx, stepAlloc_zero d hd]
      · rw [stepAlloc_zero d hd, sub_zero] at hx
        exact ih (fun d' hd' => hpos d' (List.mem_cons_of_mem _ hd')) x hx

/-- 顺位的 T25 公开更正式：逐项冲抵不超过自身到期额；一旦某项未足额冲抵
    （冲抵额 < 到期额），其后所有项冲抵额为零——这正是"a_j > 0 ⇒ 对每个
    应先清偿组 i < j，a_i = d_i"的逆否读法（§6.5 公开更正 T25）。 -/
def Prioritized : List DebtItem → List ℚ → Prop
  | [], [] => True
  | [], _ :: _ => False
  | _ :: _, [] => False
  | d :: ds, a :: as =>
      a ≤ d.amount ∧ (a < d.amount → ∀ x ∈ as, x = 0) ∧ Prioritized ds as

/-- 标准运行的顺位刻画：法定抵充结果满足 T25 更正式。 -/
theorem runPay_prioritized : ∀ (ds : List DebtItem) (r : ℚ),
    (∀ d ∈ ds, 0 ≤ d.amount) → Prioritized ds (runPay r ds) := by
  intro ds
  induction ds with
  | nil => intro r _; trivial
  | cons d ds ih =>
      intro r hpos
      refine ⟨stepAlloc_le_amount r d, ?_,
        ih (r - stepAlloc r d) (fun d' hd' => hpos d' (List.mem_cons_of_mem _ hd'))⟩
      intro hlt
      rw [stepAlloc_eq_self_of_lt hlt, sub_self]
      exact runPay_zero_all ds (fun d' hd' => hpos d' (List.mem_cons_of_mem _ hd'))

/-- T25 顺位的相邻直读：后项得正 ⇒ 前项足额（相邻形式的两次应用得任意距离）。 -/
theorem prioritized_adjacent {d d' : DebtItem} {rest : List DebtItem}
    {x y : ℚ} {s : List ℚ}
    (hp : Prioritized (d :: d' :: rest) (x :: y :: s)) (hpos : 0 < y) :
    x = d.amount := by
  obtain ⟨hle, hlt, -⟩ := hp
  by_contra hne
  have hxlt : x < d.amount := lt_of_le_of_ne hle hne
  exact absurd (hlt hxlt y List.mem_cons_self) (ne_of_gt hpos)

/-- 溢余为正 ⇒ 每一项都被足额冲抵：总冲抵 = 总到期额。 -/
theorem runPay_sum_eq_due : ∀ (ds : List DebtItem) (r : ℚ),
    (∀ d ∈ ds, 0 ≤ d.amount) → 0 < runRes r ds →
    (runPay r ds).sum = (ds.map DebtItem.amount).sum := by
  intro ds
  induction ds with
  | nil => intro _ _ _; rfl
  | cons d ds ih =>
      intro r hpos hover
      have hd : 0 ≤ d.amount := hpos d List.mem_cons_self
      have hpos' : ∀ d' ∈ ds, 0 ≤ d'.amount :=
        fun d' hd' => hpos d' (List.mem_cons_of_mem _ hd')
      have hover' : 0 < runRes (r - stepAlloc r d) ds := hover
      have hmin : stepAlloc r d = d.amount := by
        rcases le_total d.amount r with h | h
        · exact stepAlloc_eq_amount_of_le h
        · exfalso
          have hminr : stepAlloc r d = r := by
            rw [stepAlloc_eq_min]
            exact min_eq_right h
          rw [hminr, sub_self] at hover'
          rw [runRes_zero ds hpos'] at hover'
          norm_num at hover'
      rw [hmin] at hover'
      show (stepAlloc r d :: runPay (r - stepAlloc r d) ds).sum
          = (d.amount :: (ds.map DebtItem.amount)).sum
      rw [hmin, List.sum_cons, List.sum_cons, ih (r - d.amount) hpos' hover']

/-- 冲抵后的债项列：身份（标识 + 分型）逐笔保持，金额减去冲抵额。 -/
def dischargeItems (ds : List DebtItem) (as : List ℚ) : List DebtItem :=
  (ds.zip as).map (fun q => ⟨q.1.ident, q.1.kind, q.1.amount - q.2⟩)

/-- 债项身份保持：冲抵前后标识逐笔对应不变。 -/
theorem dischargeItems_ident : ∀ (ds : List DebtItem) (as : List ℚ),
    as.length = ds.length →
    (dischargeItems ds as).map DebtItem.ident = ds.map DebtItem.ident := by
  intro ds
  induction ds with
  | nil =>
      intro as hlen
      cases as with
      | nil => rfl
      | cons a as => simp at hlen
  | cons d ds ih =>
      intro as hlen
      cases as with
      | nil => simp at hlen
      | cons a as =>
          have hlen' : as.length = ds.length := by simpa using hlen
          have hrec := ih as hlen'
          show (⟨d.ident, d.kind, d.amount - a⟩ :: dischargeItems ds as).map DebtItem.ident
              = d.ident :: ds.map DebtItem.ident
          rw [List.map_cons, hrec]

/-- 冲抵不产生负余额：冲抵后每笔债项的剩余金额非负。 -/
theorem dischargeItems_nonneg : ∀ (ds : List DebtItem) (r : ℚ),
    ∀ x ∈ dischargeItems ds (runPay r ds), 0 ≤ x.amount := by
  intro ds
  induction ds with
  | nil =>
      intro r x hx
      have hz : dischargeItems [] (runPay r []) = [] := rfl
      rw [hz] at hx
      cases hx
  | cons d ds ih =>
      intro r x hx
      rcases List.mem_cons.1 hx with hx | hx
      · subst hx
        have hmin := stepAlloc_le_amount r d
        show 0 ≤ d.amount - stepAlloc r d
        linarith
      · exact ih (r - stepAlloc r d) x hx

/-- 法定顺位债项列处于法定顺序（费用→利息→本金）。 -/
def StatutoryOrdered : List DebtItem → Prop
  | [] => True
  | [_] => True
  | d :: d' :: rest => statOrder d.kind ≤ statOrder d'.kind ∧ StatutoryOrdered (d' :: rest)

/-- 法定顺位债项集见证：费用 10（标识 1）→ 利息 100（标识 2）→ 本金 200（标识 3）。 -/
def statDebts : List DebtItem :=
  [⟨1, DebtKind.fee, 10⟩, ⟨2, DebtKind.interest, 100⟩, ⟨3, DebtKind.principal, 200⟩]

theorem statDebts_ordered : StatutoryOrdered statDebts := by
  show statOrder DebtKind.fee ≤ statOrder DebtKind.interest ∧
    (statOrder DebtKind.interest ≤ statOrder DebtKind.principal ∧ True)
  exact ⟨Nat.le_succ _, Nat.le_succ _, trivial⟩

theorem statDebts_amounts_nonneg : ∀ d ∈ statDebts, 0 ≤ d.amount := by
  intro d hd
  simp only [statDebts, List.mem_cons] at hd
  rcases hd with rfl | rfl | rfl | h4
  · norm_num
  · norm_num
  · norm_num
  · cases h4

/-- **第 37 针主定理（S5，附录 I:791；BINDING 行 37）差额闭合**：真实支付（ℚ）、
    债项身份、法定抵充的端到端唯一性——给定支付 p 与债项集 ds：
    (1) 冲抵结果唯一（任何满足法定刻画的记录都等于标准运行）；
    (2) 顺位满足 T25 更正式（逐项不超抵 + 未足额则后项全零）；
    (3) 对账闭合 Σ冲抵 + 溢余 = p（溢余不截断）；
    (4) 溢余非负（不产生负义务）；
    (5) 债项身份保持；(6) 冲抵后无负余额。 -/
theorem actual_payment_discharge_exact_q (p : ℚ) (ds : List DebtItem)
    (hp : 0 ≤ p) (hpos : ∀ d ∈ ds, 0 ≤ d.amount) :
    (∀ a : List ℚ, StatRun p ds a → a = runPay p ds) ∧
    Prioritized ds (runPay p ds) ∧
    ((runPay p ds).sum + runRes p ds = p) ∧
    (0 ≤ runRes p ds) ∧
    ((dischargeItems ds (runPay p ds)).map DebtItem.ident = ds.map DebtItem.ident) ∧
    (∀ x ∈ dischargeItems ds (runPay p ds), 0 ≤ x.amount) :=
  ⟨fun a ha => discharge_unique p ds a ha,
    runPay_prioritized ds p hpos,
    runPay_sum_add_runRes ds p,
    runRes_nonneg ds p hp hpos,
    dischargeItems_ident ds (runPay p ds) (statRun_length ds _ p (statRun_exists p ds)),
    dischargeItems_nonneg ds p⟩

/-- **超收另账定理**：支付超过全部债项总额时（溢余 > 0），每一项都被足额冲抵
    （总冲抵 = 总到期额），溢余 = p − 总到期额 全额记另账（返还/余额关系），
    不冲抵任何债项、不压成负债务。 -/
theorem overpay_separate_account (p : ℚ) (ds : List DebtItem)
    (hp : 0 ≤ p) (hpos : ∀ d ∈ ds, 0 ≤ d.amount)
    (hover : 0 < runRes p ds) :
    ((runPay p ds).sum = (ds.map DebtItem.amount).sum) ∧
    (runRes p ds = p - (ds.map DebtItem.amount).sum) ∧
    (0 < runRes p ds) := by
  refine ⟨runPay_sum_eq_due ds p hpos hover, ?_, hover⟩
  have htele := runPay_sum_add_runRes ds p
  rw [runPay_sum_eq_due ds p hpos hover] at htele
  linarith

/-- 支付流端到端：多笔支付逐笔按法定顺序抵充，笔笔对账闭合——总冲抵 + 总溢余
    = 总支付；每笔的溢余各自记另账，不跨笔混同（§6.5：同一付款只调用一次分配
    事件，超付款另立返还/余额关系）。 -/
theorem flow_payment_closed (ps : List ℚ) (ds : List DebtItem) :
    (ps.map (fun p => (runPay p ds).sum)).sum
      + (ps.map (fun p => runRes p ds)).sum = ps.sum := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
      have htele := runPay_sum_add_runRes ds p
      simp only [List.map_cons, List.sum_cons]
      linarith

/-- 具体见证读数（闭式）：支付 150 时逐项冲抵 (10, 100, 40)、溢余 0；
    支付 350 时逐项足额冲抵 (10, 100, 200)、溢余 40 全额另账。 -/
theorem statDebts_readout :
    runPay 150 statDebts = [10, 100, 40] ∧
    runRes 150 statDebts = 0 ∧
    runPay 350 statDebts = [10, 100, 200] ∧
    runRes 350 statDebts = 40 := by
  norm_num [statDebts, runPay, runRes, stepAlloc]

end JurisLean.Seams.UnifiedNeedlesGapMid
