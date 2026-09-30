import Mathlib
import JurisLean.Mandate.GameTree
import JurisLean.Mandate.PureNash

/-!
S4（L5 计算与保证层缝合件）——法律收益映射、2η 外部均衡反射、制裁回拉阈值。

## 一、法律语义（人话）

统一模型走到 L5 时需要问一句话："这个裁判结局对当事人值多少？"仓内此前**没有这句话的
载体**。全仓检索任何从 `EvalResult`/`Judgment`/`Outcome`/`LegalNormV2` 到收益的映射零命中，
`Sanction`、`Penalty` 的定义也不存在；已有的收益/效用定义全是博弈内部的
（`Mandate/MixedPennies.lean:45`、`Mandate/ZeroSumSion.lean:51`、
`FullMath/Action/Mechanisms.lean:26 def util`、`FullMath/Action/Settlement.lean:26,29,32`）。
所以本件第一件事是**把这条映射声明出来**，而不是假装它已存在：
`legal_payoff : Role → LegalStatus → ℚ`，由一张被货币化的法律后果清单
（`Consequence` × `consequenceValuation` × `declaredConsequences`）逐项相加得到。
四个声明结局（支持∥部分支持∥驳回∥不可强制实现）只沿用本仓既有的地位区分风格，
不导入 S1/S2 未由本件撰写的语义。

数值全部是 **[代拟稿]**：既无经验校准，也无法律根据；条文只用来指明"哪一类后果在结构上
挂在哪个结局上"（诉讼费负担见《诉讼费用交纳办法》第29条，迟延履行金见《民事诉讼法》第264条，
清偿致请求权消灭见《民法典》第557条第1款第1项）。**任何具体数字都不构成对胜诉率、
量刑幅度或可预测性的估计。**

法律内容四条：

1. **收益只认法律地位，不认载体标签**（`legal_payoff_preserved`）。同一地位换个案号、
   换套卷宗表述，折价不变；反过来，动了地位本身的改名（驳回 ↔ 不可强制实现）在被申请人
   一侧看不出来（`relabelStatus_preserves_respondent_payoff`），在申请人一侧却看得出来
   （`relabelStatus_visible_on_claimant_side`）——不变性来自声明表而非逻辑真空。
   这与 `GameTree.lean:124 value_ignores_payoff_renaming_when_dominated` 同形。
2. **外部算出来的均衡折回法律收益要付 2η**（`external_equilibrium_reflects_legal`，
   同一陈述在仓内 `PureNash.Game` 载体上是 `two_eta_transfer_Game`）：若外部收益函数与
   法律收益函数逐点相差 ≤ η，则外部的 ε-均衡至多是法律意义上的 (ε + 2η)-均衡。
   2η 由本件自己在 ℚ 上证出（`abs_two_close`，三角不等式两端的合成），并证明该上界在
   η > 0 时可达、不可压成 η（`two_eta_bound_is_tight`）。
3. **回拉条件有阈值，且只在最优反应集层成立**：制裁额 k ≥ 23 时"履行"回到被申请人对
   "起诉"的最优反应集（`sanction_pulls_back_lawful`），k < 23 时不在
   （`below_threshold_lawful_excluded`），二者合成锐利判据 `lawful_iff_sanction_threshold`。
   但把制裁提到 30 之后，本件的收益网格**没有任何纯策略均衡**
   （`no_pure_equilibrium_at_adequate_sanction`，计算得出）。故"制裁把均衡拉回合法"这句
   一般化的话在本模型里不成立，成立的是较弱的那句：制裁把**最优反应集**拉回合法。
4. **均衡不等于合法**（`equilibrium_and_lawfulness_are_different_notions`）：制裁不足
   （k = 10）时仓内既有的纯策略 Nash 判据（`Mandate/PureNash.lean:197 isNashPure`）在
   （起诉, 拒不履行）上为真，而法律上理想的（起诉, 履行）剖面不是均衡；该均衡剖面的声明
   结局是"支持请求"，义务却未履行（`equilibrium_status_upheld_yet_duty_unperformed`）。
   本件据此禁止把"法律"读成"纳什均衡"。

## 二、数学对象

- `LegalStatus`（4 结局）∥ `Role`（请求人/被申请人）∥ `Consequence`（6 项被货币化后果）。
- `legal_payoff role status = (declaredConsequences status).foldr (折价相加) 0`——映射是
  **声明表的和**，不是又一组常数；给付本金与迟延履行金分别记在行为侧与制裁变量上，避免重复计价。
- `Case`：卷宗载体 = ⟨法律地位, 一位与评价无关的案号标签⟩；`swapDocket` 是其上的非平凡置换。
- `WithinEta`（逐点绝对值接近）与 `IsApproxNash`（ℚ 上纯策略 ε-近似 Nash，本件自造，形状
  对齐外部 `KernelGame.IsNash` 但载体不同型）；`WithinEtaGame`/`IsApproxNashGame` 是同一
  两件事写在 `JurisLean.Mandate.PureNash.Game 2 2` 上。
- `ActC`（起诉/不起诉）∥ `ActR`（履行/拒不履行）∥ `outcomeOf` ∥ `litigateCost` ∥
  `principalTransferred` ∥ `withSanction`（只在"违法被认定"的结局上扣 k）∥ `legalPay k`；
  `legalRow`/`legalColLow`/`legalColHigh` 与 `idxC`/`idxR` 给出网格与指标约定。
- （E）`Strategy := Tree → Bool`（以**剩余局面**为自变量的事前策略）、`play`（按策略打到
  终局）、`bestStrategy`、`constStrategy`（一个比特管所有局面，即把所有节点并进一个信息集）。

## 三、证与不证

**证**：`legal_payoff_grid`（8 个读数）、`payoff_determined_by_status`、
`legal_payoff_preserved`（任何保地位的改名）与 `swapDocket` 具例及其对合/非平凡见证、
`relabelStatus_preserves_respondent_payoff` 与申请人侧的反面见证、`abs_two_close`、
`two_eta_bound_is_tight`、`dev_gain_two_eta`、`external_equilibrium_reflects_legal` 及法律
具象读数 `legal_payoff_two_eta_transfer*`、阈值充要式 `lawful_iff_sanction_threshold`、
声明侧与博弈侧同一张表 `legalPay_agrees_with_declaration`/`grids_realise_legalPay`/
`approxNash_agrees_with_isNashPure_at_k10`、`breach_profile_is_equilibrium_low`、
`lawful_profile_not_equilibrium_low`、`no_pure_equilibrium_at_adequate_sanction`、
`two_eta_transfer_Game` 与制裁档位的 40 读数、`play_le_value`（∀ 在 value 之外）、
`play_bestStrategy`（完美信息下一条策略同时达到每个局面的 value）、
`committed_bit_is_strictly_below_value`（事前一个比特只能得 3，strictly 掉在 9 之下）。

**不证**：不证任何均衡**存在**性。外部锚
`External/GameTheory/Theorems/NashExistenceMixed.lean:717 mixed_nash_exists`
（及 `:703 mixed_nash_exists_of_bounded`，载体 `KernelGame ι`、`Deviation`/`euAfterDeviation`
见 `Concepts/Deviation.lean:41,56`、`Core/KernelGame.lean:43,80`、`withUtility` 见
`Core/GameForm.lean:191`）是上游 elazarg 移植件的定理；该件页眉自陈 "Statements and proofs
are unchanged" 且"无本仓构建认定"，故只作**引证锚**，其存在性主张属于上游，不属于本件也不
属于本仓。本件的 `IsApproxNash` 在 ℚ 上、纯策略、逐剖面直接取值，与 `KernelGame`（over ℝ，
含期望算子与 `PMF`）不同型，本件不做桥接，也不得被读成桥接。
本件不认定任何真实案件的胜败，不校准任何金额，不声称法律收益函数是经验拟合。
（E）不是 Nash 也不是子博弈完美均衡定理，只把量词位置与信息条件钉在
`Mandate/GameTree.lean:51 value` 这一既有载体上（echo `GameTree.lean:9-10,17-21`、
`SequentialGames.lean:22-27`、`MatrixGame.lean:9-10,20-23`——后者的 shipped "均衡" 是冲突
过滤器，本件不 upgrade 它）。P-090 已挂 `Mandate/GameTree.lean` 与 `action_decision.py`
（AC-03）（`docs/master-plan/03_证明战役台账.md:299`、`docs/master-plan/02_复用总账.md:146`），
本件 (E) 只是该载体上的量词/信息条件重述，不另立证明号。

## 四、未覆盖片段

- `general_equilibrium_pull_back_UNPROVEN`（下方以 `def … : Prop` 显式声明，状态 UNPROVEN）：
  一般有限法律博弈上的**均衡层**回拉。本件已算出它在声明网格上为假（k = 30 满足回拉前提却
  无纯均衡），故该形必须另加前提；保留声明是为了让"这里没有证明"可检索，而不是主张它。
- 以下三条**未**声明为 `def`，因为在缺少载体的情况下写不出良构式子，硬写只会造出空洞真理：
  (i) 声明表数值的经验校准或法律正当性（本件无数据载体，禁"常数已校准"式读法）；
  (ii) η 的法律来源（裁判离散度/评估误差）——本件的 η 只是假设参数；
  (iii) 本件 ℚ 网格上的混合策略 Nash 存在性——需要单纯形与不动点载体，本件不建。

## 五、档位与文献锚

收益映射与全部数值：[代拟稿]（Owner 授权参照文献代拟；无经验依据）。
定理：本件内给出完整证明；编译认定待 CI，本地不称 PASS（`CI_NOT_RUN` 口径）。
锚：Nash 混合存在性＝上游 GameTheory 库（MIT，revision `107085bc4a0306672f2f35fce1abc1345d7975ed`，
见 `JurisLean/External/PROVENANCE.md`）；纯策略判据与 `Tree`/`value` 载体＝本仓
`Mandate/PureNash.lean`、`Mandate/GameTree.lean`；2η 逼近强度＝本件自证（全仓此前无任何
`η`-算术或 `2 * η` 引理，`η` 只在 `FullMath/Contracts.lean:149-153` 作约束变元）。
-/

namespace JurisLean.Seams.PayoffEquilibrium

/-! ## 一、声明的法律结局、角色与被货币化的法律后果 -/

/-- 声明的法律结局（4 值）。沿用本仓既有的地位区分风格，不导入 S1/S2 的语义；
    `unenforceable` 指"请求权存在但无执行名义，不能请求强制实现"。 -/
inductive LegalStatus
  | upheld
  | partiallyUpheld
  | dismissed
  | unenforceable
  deriving DecidableEq, Repr

/-- 收益指向的两个角色：请求人与被申请人。 -/
inductive Role
  | claimant
  | respondent
  deriving DecidableEq, Repr

/-- 被货币化的法律后果清单（声明表的可加项）。本件只声明这 6 项：给付本金**不在**此表内
    （它记在行为侧的实际移转 `principalTransferred`），迟延履行金也不在此表内（它记在制裁
    变量 `k`）；这两条区分是为了不重复计价。 -/
inductive Consequence
  | costBurdenLoser
  | costBurdenPartial
  | costOwnOnDismiss
  | noTitleNoCost
  | enforcementAccess
  | resJudicata
  deriving DecidableEq, Repr

/-- 单项后果对两个角色的折价。**[代拟稿]**：数字无经验与法律根据，只保证结构上可读、
    两侧净额相抵（零和式声明）。 -/
def consequenceValuation : Role → Consequence → ℚ
  | .claimant, .costBurdenLoser => 3
  | .claimant, .costBurdenPartial => 1
  | .claimant, .costOwnOnDismiss => -3
  | .claimant, .noTitleNoCost => 0
  | .claimant, .enforcementAccess => 2
  | .claimant, .resJudicata => 2
  | .respondent, .costBurdenLoser => -3
  | .respondent, .costBurdenPartial => -1
  | .respondent, .costOwnOnDismiss => 0
  | .respondent, .noTitleNoCost => 0
  | .respondent, .enforcementAccess => -2
  | .respondent, .resJudicata => -2

/-- 每个声明结局挂载哪些后果。清单是**声明**出来的，不是从法条推出来的。 -/
def declaredConsequences : LegalStatus → List Consequence
  | .upheld => [.costBurdenLoser, .enforcementAccess, .resJudicata]
  | .partiallyUpheld => [.costBurdenPartial, .enforcementAccess]
  | .dismissed => [.costOwnOnDismiss]
  | .unenforceable => [.noTitleNoCost]

/-- **(A) 本件补的那条缺失映射**：法律结局 → 角色收益，定义为该结局所挂载后果的折价之和。
    [代拟稿]：仓内此前没有任何结局→收益的函数（`Sanction`/`Penalty` 定义不存在），
    故本条是**声明**的估值，不是从经验数据或法律文书记载推出的估计。 -/
def legal_payoff (role : Role) (status : LegalStatus) : ℚ :=
  (declaredConsequences status).foldr (fun c acc => consequenceValuation role c + acc) 0

/-- 声明表的可核验读数：4 结局 × 2 角色 = 8 个数字，由声明后果逐项相加算出，
    不是事后贴上的标签。 -/
theorem legal_payoff_grid :
    legal_payoff Role.claimant LegalStatus.upheld = 7 ∧
      legal_payoff Role.respondent LegalStatus.upheld = -7 ∧
      legal_payoff Role.claimant LegalStatus.partiallyUpheld = 3 ∧
      legal_payoff Role.respondent LegalStatus.partiallyUpheld = -3 ∧
      legal_payoff Role.claimant LegalStatus.dismissed = -3 ∧
      legal_payoff Role.respondent LegalStatus.dismissed = 0 ∧
      legal_payoff Role.claimant LegalStatus.unenforceable = 0 ∧
      legal_payoff Role.respondent LegalStatus.unenforceable = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  <;> norm_num [legal_payoff, declaredConsequences, consequenceValuation]

/-! ## 二、(B) 载体改名不改变收益 -/

/-- 卷宗载体：法律地位 + 一位与法律评价无关的案号标签。之所以要有这个载体，
    是因为"改名不动收益"必须有可改的东西。 -/
structure Case where
  status : LegalStatus
  docket : Bool
  deriving DecidableEq, Repr

/-- 从卷宗读出声明的法律地位：评价侧只看这一条投影。 -/
def statusOf (c : Case) : LegalStatus := c.status

/-- 按卷宗计算收益 = 按该卷宗声明的地位计算收益。 -/
def payoffOf (role : Role) (c : Case) : ℚ := legal_payoff role (statusOf c)

/-- 案号改名：把标签取反。下面两条定理给出它是对合且非平凡。 -/
def swapDocket (c : Case) : Case := { c with docket := !c.docket }

/-- 逐字段形式的对合性（避免对变量做结构消去时的命名歧义）。 -/
theorem swapDocket_involutive_fields (s : LegalStatus) (d : Bool) :
    swapDocket (swapDocket ⟨s, d⟩) = (⟨s, d⟩ : Case) := by
  cases d <;> rfl

/-- 该改名确实是置换：做两次回到原状。 -/
theorem swapDocket_involutive (c : Case) : swapDocket (swapDocket c) = c := by
  cases c with
  | mk s d => exact swapDocket_involutive_fields s d

/-- 该改名确实非平凡：存在被它改变的卷宗（不是恒等改名的空洞不变性）。 -/
theorem swapDocket_is_not_identity : ∃ c : Case, swapDocket c ≠ c :=
  ⟨⟨LegalStatus.upheld, true⟩, by decide⟩

/-- **(B) 保持定理（一般形）**：收益只经法律地位依赖卷宗，故任何保持地位的载体改名都不改变
    收益。假设必要地写在签名里——动了地位的改名就没有这个结论
    （见 `relabelStatus_visible_on_claimant_side`）。 -/
theorem legal_payoff_preserved {f : Case → Case} (h : ∀ c, statusOf (f c) = statusOf c)
    (role : Role) (c : Case) : payoffOf role (f c) = payoffOf role c :=
  congrArg (legal_payoff role) (h c)

/-- **(B) 保持定理（具例）**：案号改名对两侧角色的收益都不可见。 -/
theorem legal_payoff_preserved_swapDocket (role : Role) (c : Case) :
    payoffOf role (swapDocket c) = payoffOf role c :=
  legal_payoff_preserved (fun _ => rfl) role c

/-- 读数式同余：地位相同则收益相同（"只认法律地位"的最短陈述）。 -/
theorem payoff_determined_by_status (role : Role) (c₁ c₂ : Case) (h : c₁.status = c₂.status) :
    payoffOf role c₁ = payoffOf role c₂ :=
  congrArg (legal_payoff role) h

/-- 地位层面的改名：驳回 ↔ 不可强制实现，其余不动。这是**动了法律地位本身**的改名，
    上面那条一般保持定理不适用；它是否可见完全由声明表决定。 -/
def relabelStatus : LegalStatus → LegalStatus
  | .dismissed => .unenforceable
  | .unenforceable => .dismissed
  | s => s

/-- **(B) 与 `GameTree.lean:124` 同形的可读性定理**：在被申请人一侧，这两个不同构造子的
    声明折价相等（都是 0），故把驳回改名成不可强制实现，被申请人看不出来。 -/
theorem relabelStatus_preserves_respondent_payoff (s : LegalStatus) :
    legal_payoff Role.respondent (relabelStatus s) = legal_payoff Role.respondent s := by
  cases s <;>
    norm_num [relabelStatus, legal_payoff, declaredConsequences, consequenceValuation]

/-- 同一改名在申请人一侧**是**看得出来的（驳回 −3，不可强制实现 0）。
    这条见证画出保持定理的边界：不变性来自声明表，不是逻辑真空。 -/
theorem relabelStatus_visible_on_claimant_side :
    ∃ s : LegalStatus, legal_payoff Role.claimant (relabelStatus s) ≠
      legal_payoff Role.claimant s :=
  ⟨LegalStatus.dismissed, by
    show legal_payoff Role.claimant LegalStatus.unenforceable ≠
      legal_payoff Role.claimant LegalStatus.dismissed
    norm_num [legal_payoff, declaredConsequences, consequenceValuation]⟩

/-! ## 三、(C) 2η：外部均衡折回法律收益 -/

/-- 逐点 η-接近（ℚ 上的绝对值形式，双侧）。这是本件对"外部模型算出的收益与法律收益差多少"
    的形式化说法；η 的来源本件不认定（见 §四）。 -/
def WithinEta {α β : Type} (u v : α → β → Role → ℚ) (η : ℚ) : Prop :=
  ∀ (a : α) (b : β) (r : Role), |u a b r - v a b r| ≤ η

/-- ε-近似 Nash（ℚ、纯策略、本件自造）。形状对齐外部 `KernelGame.IsNash`
    （`SolutionConcepts.lean:86`，那里是 `≥` 的偏差方向），但载体不同型：那里是 `eu`
    （over ℝ，含期望算子），这里是逐剖面直接取值。本件不桥接，也不 Claim 存在性。 -/
def IsApproxNash {α β : Type} (u : α → β → Role → ℚ) (ε : ℚ) (a : α) (b : β) : Prop :=
  (∀ a' : α, u a' b Role.claimant ≤ u a b Role.claimant + ε) ∧
    (∀ b' : β, u a b' Role.respondent ≤ u a b Role.respondent + ε)

/-- 把绝对值读数拆成两条单向界：只用 `ℚ` 的线性序与 `x ≤ |x|`。 -/
theorem withinEta_one_sided {η x y : ℚ} (h : |x - y| ≤ η) : x ≤ y + η ∧ y ≤ x + η := by
  have hxy : x - y ≤ η := le_trans (le_abs_self (x - y)) h
  have hyx : y - x ≤ η :=
    le_trans (le_abs_self (y - x)) (by rw [abs_sub_comm]; exact h)
  exact ⟨by linarith, by linarith⟩

/-- **(C) 的 2η 算术（本件自证）**：两次三角不等式合成，缺口恰是 `2 * η`。
    全仓此前没有任何 η-算术，故这条从零建在 ℚ 上，不动用 NNReal/ENNReal。 -/
theorem abs_two_close {a b c η : ℚ} (hab : |a - b| ≤ η) (hbc : |b - c| ≤ η) :
    |a - c| ≤ 2 * η :=
  calc |a - c|
    _ = |(a - b) + (b - c)| := congrArg abs (by ring : a - c = (a - b) + (b - c))
    _ ≤ |a - b| + |b - c| := abs_add_le _ _
    _ ≤ η + η := by linarith
    _ = 2 * η := by ring

/-- 上界可达，故 2η 不可压成 η：η > 0 时存在三点使两端差都恰为 η 而总缺口恰为 2η。 -/
theorem two_eta_bound_is_tight (η : ℚ) (hη : 0 < η) :
    ∃ a b c : ℚ, |a - b| = η ∧ |b - c| = η ∧ |a - c| = 2 * η :=
  ⟨2 * η, η, 0,
    by rw [show (2 : ℚ) * η - η = η by ring]; exact abs_of_pos hη,
    by rw [show (η : ℚ) - 0 = η by ring]; exact abs_of_pos hη,
    by rw [show (2 : ℚ) * η - 0 = 2 * η by ring]; exact abs_of_pos (by linarith)⟩

/-- 偏差值之差被 2η 夹住：同一角色在（当前剖面, 偏差剖面）上的收益差，换一个逐点 η-接近的
    收益函数来算，最多变动 2η。这就是"2η 是两端各 η 的和"的那条链。 -/
theorem dev_gain_two_eta {α β : Type} (u v : α → β → Role → ℚ) (η : ℚ)
    (hclo : WithinEta u v η) (a a' : α) (b : β) (r : Role) :
    |(v a' b r - v a b r) - (u a' b r - u a b r)| ≤ 2 * η := by
  have hkey : (v a' b r - v a b r) - (u a' b r - u a b r)
      = (v a' b r - u a' b r) + (u a b r - v a b r) := by ring
  have h1 : |v a' b r - u a' b r| ≤ η := by rw [abs_sub_comm]; exact hclo a' b r
  have h2 : |u a b r - v a b r| ≤ η := hclo a b r
  calc |(v a' b r - v a b r) - (u a' b r - u a b r)|
    _ = |(v a' b r - u a' b r) + (u a b r - v a b r)| := congrArg abs hkey
    _ ≤ |v a' b r - u a' b r| + |u a b r - v a b r| := abs_add_le _ _
    _ ≤ η + η := by linarith
    _ = 2 * η := by ring

/-- **(C) 外部均衡折回法律收益**：若剖面 `(a, b)` 在外部收益 `v` 下是 ε-均衡，而 `u`
    （法律收益）与 `v` 逐点相差 ≤ η，则同一剖面在 `u` 下是 (ε + 2η)-均衡。
    本件只证这条**传递**，不证任何一侧的均衡存在：存在性属于上游 `mixed_nash_exists`
    （`NashExistenceMixed.lean:717`），其主张是上游的，不是本缝的。 -/
theorem external_equilibrium_reflects_legal {α β : Type}
    (u v : α → β → Role → ℚ) (ε η : ℚ) (a : α) (b : β)
    (hclo : WithinEta u v η) (hv : IsApproxNash v ε a b) :
    IsApproxNash u (ε + 2 * η) a b := by
  obtain ⟨hvc, hvr⟩ := hv
  refine ⟨fun a' => ?_, fun b' => ?_⟩
  · obtain ⟨h1, _⟩ := withinEta_one_sided (hclo a' b Role.claimant)
    obtain ⟨_, h2⟩ := withinEta_one_sided (hclo a b Role.claimant)
    linarith [hvc a']
  · obtain ⟨h1, _⟩ := withinEta_one_sided (hclo a b' Role.respondent)
    obtain ⟨_, h2⟩ := withinEta_one_sided (hclo a b Role.respondent)
    linarith [hvr b']

/-! ## 四、行为、成本与制裁：法律博弈的收益网格 -/

/-- 请求人的行动：起诉 / 不起诉。 -/
inductive ActC
  | sue
  | forbear
  deriving DecidableEq, Repr

/-- 被请求人的行动：履行 / 拒不履行。 -/
inductive ActR
  | perform
  | refuse
  deriving DecidableEq, Repr

/-- 裁判结局声明：行动对 → 法律地位。已履行后被诉，请求权因清偿消灭而诉请驳回；
    拒不履行被诉则请求成立；未起诉则无执行名义。 -/
def outcomeOf : ActC → ActR → LegalStatus
  | .sue, .perform => .dismissed
  | .sue, .refuse => .upheld
  | .forbear, .perform => .unenforceable
  | .forbear, .refuse => .unenforceable

/-- 行为侧的诉讼费预交（[代拟稿]）：起诉 3，不起诉 0。 -/
def litigateCost : ActC → ℚ
  | .sue => 3
  | .forbear => 0

/-- 行为侧的实际本金移转（[代拟稿]）：只在履行时发生，数额 30。 -/
def principalTransferred : ActR → ℚ
  | .perform => 30
  | .refuse => 0

/-- 无制裁时"违法被认定"给被申请人的折价（阈值的读数就挂在这条上）。 -/
def sanctionedLoss : ℚ := legal_payoff Role.respondent LegalStatus.upheld

/-- 制裁调整：本件只把"违法被认定"（`upheld`）声明为可科处制裁的结局，在被申请人一侧扣去
    `k`（迟延履行金/罚款的抽象化）。写成模式匹配而不是 `if`，使每个格子的读数都能被
    kernel 直接算出。 -/
def withSanction : ℚ → Role → LegalStatus → ℚ
  | k, .respondent, .upheld => legal_payoff .respondent .upheld - k
  | _, role, status => legal_payoff role status

/-- 法律博弈的收益函数：声明折价（含制裁）+ 行为侧成本与实际移转。 -/
def legalPay (k : ℚ) : ActC → ActR → Role → ℚ
  | c, r, .claimant =>
      legal_payoff .claimant (outcomeOf c r) - litigateCost c + principalTransferred r
  | c, r, .respondent =>
      withSanction k .respondent (outcomeOf c r) - principalTransferred r

/-- 网格完整读数（k = 10，即制裁低于下面证出的阈值 23）。 -/
theorem legalPay_grid_k10 :
    legalPay 10 ActC.sue ActR.perform Role.claimant = 24 ∧
      legalPay 10 ActC.sue ActR.refuse Role.claimant = 4 ∧
      legalPay 10 ActC.forbear ActR.perform Role.claimant = 30 ∧
      legalPay 10 ActC.forbear ActR.refuse Role.claimant = 0 ∧
      legalPay 10 ActC.sue ActR.perform Role.respondent = -30 ∧
      legalPay 10 ActC.sue ActR.refuse Role.respondent = -17 ∧
      legalPay 10 ActC.forbear ActR.perform Role.respondent = -30 ∧
      legalPay 10 ActC.forbear ActR.refuse Role.respondent = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  <;> norm_num [legalPay, withSanction, outcomeOf, litigateCost, principalTransferred,
    legal_payoff, declaredConsequences, consequenceValuation]

/-- 声明侧与博弈侧是同一张表：每个格子的定义式就是"后果折价 − 诉讼成本 ± 实际移转"。 -/
theorem legalPay_agrees_with_declaration (k : ℚ) (c : ActC) (r : ActR) :
    legalPay k c r Role.claimant =
        legal_payoff Role.claimant (outcomeOf c r) - litigateCost c + principalTransferred r ∧
      legalPay k c r Role.respondent =
        withSanction k Role.respondent (outcomeOf c r) - principalTransferred r :=
  ⟨rfl, rfl⟩

/-- 无制裁折价的数值读数（= 声明表三项之和 −7）。
    ℚ 上的加法不走 kernel `decide`（`Rat.add` 的归一化用了良基递归的 `Nat.gcd`），
    故本件的数值读数一律用 `norm_num`，而只用比较而不带算术的地方才用 `decide`。 -/
theorem sanctionedLoss_eq : sanctionedLoss = (-7 : ℚ) := by
  norm_num [sanctionedLoss, legal_payoff, declaredConsequences, consequenceValuation]

/-- 拒不履行的收益 = 无制裁折价 − 制裁额：阈值的来源就在这条读数上。 -/
theorem legalPay_sue_refuse_respondent (k : ℚ) :
    legalPay k ActC.sue ActR.refuse Role.respondent = sanctionedLoss - k := by
  show withSanction k Role.respondent (outcomeOf ActC.sue ActR.refuse) -
      principalTransferred ActR.refuse = legal_payoff Role.respondent LegalStatus.upheld - k
  show (legal_payoff Role.respondent LegalStatus.upheld - k) - (0 : ℚ) =
      legal_payoff Role.respondent LegalStatus.upheld - k
  exact sub_zero _

/-- 履行的收益 = −实际给付本金，与 k 无关：履行了就不再处在被科处制裁的结局上。 -/
theorem legalPay_sue_perform_respondent (k : ℚ) :
    legalPay k ActC.sue ActR.perform Role.respondent = (-30 : ℚ) := by
  show legal_payoff Role.respondent (outcomeOf ActC.sue ActR.perform) -
      principalTransferred ActR.perform = (-30 : ℚ)
  show legal_payoff Role.respondent LegalStatus.dismissed - (30 : ℚ) = (-30 : ℚ)
  norm_num [legal_payoff, declaredConsequences, consequenceValuation]

/-- **(D) 回拉条件**：在"对方起诉"这一条件下，履行属于被申请人的最优反应集。 -/
def lawfulInBestResponse (k : ℚ) : Prop :=
  ∀ r : ActR, legalPay k ActC.sue r Role.respondent ≤
    legalPay k ActC.sue ActR.perform Role.respondent

/-- **回拉（充分性）**：k ≥ 23 时履行回到最优反应集。阈值 23 = 本金 30 − 折价 7。 -/
theorem sanction_pulls_back_lawful (k : ℚ) (hk : (23 : ℚ) ≤ k) : lawfulInBestResponse k := by
  intro r
  cases r with
  | perform => exact le_refl _
  | refuse =>
      rw [legalPay_sue_refuse_respondent, legalPay_sue_perform_respondent, sanctionedLoss_eq]
      linarith

/-- **回拉的失败面**：k < 23 时履行**不在**最优反应集内，拒不履行严格更优。
    这条不是修辞：它就是下一节均衡层反例的来源。 -/
theorem below_threshold_lawful_excluded (k : ℚ) (hk : k < (23 : ℚ)) :
    ∃ r : ActR, legalPay k ActC.sue ActR.perform Role.respondent <
      legalPay k ActC.sue r Role.respondent :=
  ⟨ActR.refuse, by
    rw [legalPay_sue_refuse_respondent, legalPay_sue_perform_respondent, sanctionedLoss_eq]
    linarith⟩

/-- 阈值锐利（充要条件）：回拉成立当且仅当 k ≥ 23。 -/
theorem lawful_iff_sanction_threshold (k : ℚ) : lawfulInBestResponse k ↔ (23 : ℚ) ≤ k := by
  constructor
  · intro h
    have href := h ActR.refuse
    rw [legalPay_sue_refuse_respondent, legalPay_sue_perform_respondent, sanctionedLoss_eq] at href
    linarith
  · exact sanction_pulls_back_lawful k

/-! ## 五、与本仓既有均衡判据（PureNash）的桥接 -/

open JurisLean.Mandate.PureNash

/-- 请求人行动的指标：0 = 起诉，1 = 不起诉。 -/
def idxC : ActC → Fin 2
  | .sue => 0
  | .forbear => 1

/-- 被请求人行动的指标：0 = 履行，1 = 拒不履行。 -/
def idxR : ActR → Fin 2
  | .perform => 0
  | .refuse => 1

/-- 行（请求人）收益网格。 -/
def legalRow : Fin 2 → Fin 2 → ℚ := fun i j =>
  if i = 0 then (if j = 0 then (24 : ℚ) else (4 : ℚ)) else (if j = 0 then (30 : ℚ) else (0 : ℚ))

/-- 列（被申请人）收益网格：制裁不足的一侧（k = 10）。 -/
def legalColLow : Fin 2 → Fin 2 → ℚ := fun i j =>
  if i = 0 then (if j = 0 then (-30 : ℚ) else (-17 : ℚ)) else
    (if j = 0 then (-30 : ℚ) else (0 : ℚ))

/-- 列收益网格：制裁充足的一侧（k = 30）。 -/
def legalColHigh : Fin 2 → Fin 2 → ℚ := fun i j =>
  if i = 0 then (if j = 0 then (-30 : ℚ) else (-37 : ℚ)) else
    (if j = 0 then (-30 : ℚ) else (0 : ℚ))

/-- 网格与声明侧 `legalPay 10` 一致：指标约定下的逐格核验（8 条等式）。 -/
theorem grids_realise_legalPay (c : ActC) (r : ActR) :
      legalRow (idxC c) (idxR r) = legalPay 10 c r Role.claimant ∧
      legalColLow (idxC c) (idxR r) = legalPay 10 c r Role.respondent := by
  cases c <;> cases r <;>
    norm_num [legalRow, legalColLow, idxC, idxR, legalPay, withSanction, outcomeOf, litigateCost,
      principalTransferred, legal_payoff, declaredConsequences, consequenceValuation]

/-- 制裁不足的博弈（k = 10 < 23）。 -/
def legalGameLow : Game 2 2 := (legalRow, legalColLow)

/-- 制裁充足的博弈（k = 30 ≥ 23）。 -/
def legalGameHigh : Game 2 2 := (legalRow, legalColHigh)

/-- 制裁不足时，仓内纯策略 Nash 判据落在（起诉, 拒不履行）上——由 `PureNash` 的可判定实例
    算出，不是注释主张。 -/
theorem breach_profile_is_equilibrium_low : isNashPure legalGameLow (0, 1) := by decide

/-- 同一博弈里法律上理想的（起诉, 履行）剖面不是均衡：请求人会被"不起诉"吸引过去
    （已履行后再起诉只剩成本）。 -/
theorem lawful_profile_not_equilibrium_low : ¬ isNashPure legalGameLow (0, 0) := by decide

/-- **(D) 均衡层的失败**：把制裁提到 k = 30 之后，本件网格没有任何纯策略均衡。
    故"制裁把均衡拉回合法"这句一般化的话是假的；成立的只有较弱的
    `sanction_pulls_back_lawful`（拉回最优反应集）。 -/
theorem no_pure_equilibrium_at_adequate_sanction :
    ¬ ∃ p : Fin 2 × Fin 2, isNashPure legalGameHigh p := by decide

/-- **(F) 局限定理**：仓内既有的均衡概念与本件声明的合法剖面不重合——同一个网格里
    一个是真的、一个不是。本件据此禁止把"法律"读成"纳什均衡"。 -/
theorem equilibrium_and_lawfulness_are_different_notions :
    isNashPure legalGameLow (0, 1) ∧ ¬ isNashPure legalGameLow (0, 0) :=
  ⟨breach_profile_is_equilibrium_low, lawful_profile_not_equilibrium_low⟩

/-- 不重合的另一半：均衡剖面的声明结局是"支持请求"，而被申请人的行动是拒不履行——
    裁判说"支持"与义务被履行是两件事。 -/
theorem equilibrium_status_upheld_yet_duty_unperformed :
      outcomeOf ActC.sue ActR.refuse = LegalStatus.upheld ∧ (idxR ActR.refuse : Fin 2) ≠ 0 :=
  ⟨rfl, by decide⟩

/-! ## 六、(C) 的法律侧具象读数，以及 2η 在仓内 Game 载体上的版本 -/

/-- 外部（估计侧）收益函数：与 `legalPay 10` 逐点相差 ≤ 1 的另一张表。
    [代拟稿]：它存在的目的只是让 η 有具体落点，不代表任何真实模型的输出。 -/
def extPay : ActC → ActR → Role → ℚ
  | .sue, .perform, .claimant => 24
  | .sue, .perform, .respondent => -31
  | .sue, .refuse, .claimant => 3
  | .sue, .refuse, .respondent => -16
  | .forbear, .perform, .claimant => 30
  | .forbear, .perform, .respondent => -30
  | .forbear, .refuse, .claimant => 1
  | .forbear, .refuse, .respondent => 0

/-- 两表逐点 1-接近（η = 1 的具例，8 格全核）。 -/
theorem withinEta_legal_external : WithinEta (legalPay 10) extPay (1 : ℚ) := by
  intro a b r
  cases a <;> cases b <;> cases r <;>
    norm_num [legalPay, extPay, withSanction, outcomeOf, litigateCost, principalTransferred,
      legal_payoff, declaredConsequences, consequenceValuation]

/-- 外部收益下（起诉, 拒不履行）是精确 Nash（ε = 0）。 -/
theorem extPay_nash : IsApproxNash extPay 0 ActC.sue ActR.refuse := by
  refine ⟨fun c => ?_, fun r => ?_⟩
  · cases c <;> norm_num [extPay]
  · cases r <;> norm_num [extPay]

/-- 折回法律收益：同一剖面在法律收益下是 (0 + 2·1)-均衡。 -/
theorem legal_payoff_two_eta_transfer :
    IsApproxNash (legalPay 10) (0 + 2 * (1 : ℚ)) ActC.sue ActR.refuse :=
  external_equilibrium_reflects_legal (u := legalPay 10) (v := extPay) (ε := 0) (η := 1)
    ActC.sue ActR.refuse withinEta_legal_external extPay_nash

/-- 上式的读数：缺口恰为 2。 -/
theorem legal_payoff_two_eta_transfer_reads_as_two :
    IsApproxNash (legalPay 10) (2 : ℚ) ActC.sue ActR.refuse := by
  have h := legal_payoff_two_eta_transfer
  rw [show (0 : ℚ) + 2 * 1 = (2 : ℚ) by norm_num] at h
  exact h

/-- 法律收益自己也在 (sue, refuse) 上达到精确 Nash（k = 10）：与仓内判据同一读数。 -/
theorem approxNash_legalPay_k10 : IsApproxNash (legalPay 10) 0 ActC.sue ActR.refuse := by
  refine ⟨fun c => ?_, fun r => ?_⟩
  · cases c <;>
      norm_num [legalPay, withSanction, outcomeOf, litigateCost, principalTransferred,
        legal_payoff, declaredConsequences, consequenceValuation]
  · cases r <;>
      norm_num [legalPay, withSanction, outcomeOf, litigateCost, principalTransferred,
        legal_payoff, declaredConsequences, consequenceValuation]

/-- 两套记法不冲突：自造的 `IsApproxNash` 与仓内 `isNashPure` 在 k = 10 网格上指向同一剖面。 -/
theorem approxNash_agrees_with_isNashPure_at_k10 :
    IsApproxNash (legalPay 10) 0 ActC.sue ActR.refuse ∧ isNashPure legalGameLow (0, 1) :=
  ⟨approxNash_legalPay_k10, breach_profile_is_equilibrium_low⟩

/-- `Game 2 2` 上的逐点 η-接近（写成两个投影面，避免额外取格函数的展开歧义）。 -/
def WithinEtaGame (u v : Game 2 2) (η : ℚ) : Prop :=
  (∀ i j : Fin 2, |u.1 i j - v.1 i j| ≤ η) ∧ (∀ i j : Fin 2, |u.2 i j - v.2 i j| ≤ η)

/-- `Game 2 2` 上的 ε-近似 Nash：把仓内 `isNashPure`（ε = 0）放宽一个容差。 -/
def IsApproxNashGame (u : Game 2 2) (ε : ℚ) (p : Fin 2 × Fin 2) : Prop :=
  (∀ i : Fin 2, u.1 i p.2 ≤ u.1 p.1 p.2 + ε) ∧ (∀ j : Fin 2, u.2 p.1 j ≤ u.2 p.1 p.2 + ε)

/-- **2η 反射写在仓内 `PureNash.Game` 载体上**：同一个证明形状，换的是载体。
    `isNashPure` 本身是 ε = 0 的概念，本条只把容差传过去，不涉及存在性。 -/
theorem two_eta_transfer_Game (u v : Game 2 2) (ε η : ℚ) (p : Fin 2 × Fin 2)
    (hclo : WithinEtaGame u v η) (hv : IsApproxNashGame v ε p) :
    IsApproxNashGame u (ε + 2 * η) p := by
  obtain ⟨hrow, hcol⟩ := hv
  refine ⟨fun i => ?_, fun j => ?_⟩
  · obtain ⟨h1, _⟩ := withinEta_one_sided (hclo.1 i p.2)
    obtain ⟨_, h2⟩ := withinEta_one_sided (hclo.1 p.1 p.2)
    linarith [hrow i]
  · obtain ⟨h1, _⟩ := withinEta_one_sided (hclo.2 p.1 j)
    obtain ⟨_, h2⟩ := withinEta_one_sided (hclo.2 p.1 p.2)
    linarith [hcol j]

/-- 把制裁从 10 提到 30 是一次逐点 20 的收益扰动（16 格全核：行面完全相同，
    列面只有一格差 20）。方向取"从 30 档位看 10 档位"，与下面的反射方向一致。 -/
theorem withinEtaGame_high_low : WithinEtaGame legalGameHigh legalGameLow (20 : ℚ) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · fin_cases i <;> fin_cases j <;>
      norm_num [legalGameLow, legalGameHigh, legalRow, legalColLow, legalColHigh]
  · fin_cases i <;> fin_cases j <;>
      norm_num [legalGameLow, legalGameHigh, legalRow, legalColLow, legalColHigh]

/-- k = 10 网格上 (0, 1) 的精确 Nash 读数（Game 载体形）。 -/
theorem isApproxNashGame_low_exact : IsApproxNashGame legalGameLow 0 (0, 1) := by
  refine ⟨fun i => ?_, fun j => ?_⟩
  · fin_cases i <;> norm_num [legalGameLow, legalRow, legalColLow]
  · fin_cases j <;> norm_num [legalGameLow, legalRow, legalColLow]

/-- 反射到 k = 30 档位：在 10 档位上算出的 0-均衡，折到 30 档位只剩 (0 + 2·20)-均衡。
    法律读法：容差不是免费的，换一档制裁就要付两倍档差的确定性损失。 -/
theorem high_grid_is_approx_at_adequate_sanction :
    IsApproxNashGame legalGameHigh (0 + 2 * (20 : ℚ)) (0, 1) :=
  two_eta_transfer_Game legalGameHigh legalGameLow 0 20 (0, 1)
    withinEtaGame_high_low isApproxNashGame_low_exact

/-! ## 七、(E) P-090：策略量词的位置与信息条件 -/

open JurisLean.Mandate

/-- 事前策略：一张以**剩余局面**为自变量的分支函数（`true` 取右支）。自变量是整个子树，
    正是"完美信息"的形式内容：每个节点知道自己是谁。
    写全名 `GameTree.Tree` 而不是裸 `Tree`：`import Mathlib` 已带进同名的 `_root_.Tree α`
    （`Mathlib/Data/Tree/Basic.lean:31`），裸名会撞车。 -/
abbrev Strategy : Type := GameTree.Tree → Bool

/-- 按策略把局面向下打到终局，读出终局收益。 -/
def play : GameTree.Tree → Strategy → ℕ
  | .leaf n, _ => n
  | .node l r, π => if π (.node l r) = true then play r π else play l π

/-- **量词在 value 之外**：任何策略在任何局面的实现收益都不超过该局面的 value。
    这就是 `GameTree.lean:51 value` 的逐节点 max 所隐藏的东西——它对所有策略取上界。 -/
theorem play_le_value : ∀ (t : GameTree.Tree) (π : Strategy), play t π ≤ GameTree.value t := by
  intro t
  induction t with
  | leaf n => intro π; exact Nat.le_of_eq rfl
  | node l r ihl ihr =>
      intro π
      by_cases hb : π (.node l r) = true
      · show (if π (.node l r) = true then play r π else play l π) ≤
          max (GameTree.value l) (GameTree.value r)
        rw [if_pos hb]
        exact Nat.le_trans (ihr π) (le_max_right _ _)
      · show (if π (.node l r) = true then play r π else play l π) ≤
          max (GameTree.value l) (GameTree.value r)
        rw [if_neg hb]
        exact Nat.le_trans (ihl π) (le_max_left _ _)

/-- 逐节点择优的那个比特（平手取右支，与 `SequentialGames.choose` 的约定一致）。 -/
def bestBit : GameTree.Tree → GameTree.Tree → Bool
  | l, r => if GameTree.value l ≤ GameTree.value r then true else false

/-- 完美信息策略：在每个局面比较两支的 value。 -/
def bestStrategy : Strategy
  | .node l r => bestBit l r
  | .leaf _ => false

/-- 择右支的读数。 -/
theorem bestStrategy_node_true (l r : GameTree.Tree) (h : GameTree.value l ≤ GameTree.value r) :
    bestStrategy (GameTree.Tree.node l r) = true := by
  show (if GameTree.value l ≤ GameTree.value r then true else false) = true
  exact if_pos h

/-- 不择右支的读数。 -/
theorem bestStrategy_node_false (l r : GameTree.Tree)
    (h : ¬ GameTree.value l ≤ GameTree.value r) :
    ¬ (bestStrategy (GameTree.Tree.node l r) = true) := by
  show ¬ ((if GameTree.value l ≤ GameTree.value r then true else false) = true)
  rw [if_neg h]
  exact Bool.false_ne_true

/-- **∃ 在 value 之内，且 witness 必须以局面为自变量**：一条事前交出的策略在所有局面上
    同时达到 value。它与 `GameTree.lean:103 value_attains` 相配，但把"策略"显式成函数。
    这不是 Nash 也不是子博弈完美均衡定理（echo `GameTree.lean:9-10,17-21`）。 -/
theorem play_bestStrategy :
    ∀ (t : GameTree.Tree), play t bestStrategy = GameTree.value t := by
  intro t
  induction t with
  | leaf n => exact rfl
  | node l r ihl ihr =>
      show (if bestStrategy (.node l r) = true then play r bestStrategy
        else play l bestStrategy) = max (GameTree.value l) (GameTree.value r)
      by_cases h : GameTree.value l ≤ GameTree.value r
      · rw [if_pos (bestStrategy_node_true l r h), max_eq_right h, ihr]
      · rw [if_neg (bestStrategy_node_false l r h), max_eq_left (Nat.le_of_not_le h), ihl]

/-- 受限策略：一个比特管所有局面，等价于把所有节点并成一个信息集。 -/
def constStrategy (b : Bool) : Strategy := fun _ => b

/-- 用于把信息条件算成数字的深度 2 局面。 -/
def eTree : GameTree.Tree :=
  GameTree.Tree.node (GameTree.Tree.node (GameTree.Tree.leaf 1) (GameTree.Tree.leaf 5))
    (GameTree.Tree.node (GameTree.Tree.leaf 9) (GameTree.Tree.leaf 3))

/-- 常数策略的两个读数：事前一个比特只能拿到 3 或 1。 -/
theorem constStrategy_reads :
    play eTree (constStrategy true) = 3 ∧ play eTree (constStrategy false) = 1 := by decide

/-- 该局面的后向归纳值。 -/
theorem eTree_value : GameTree.value eTree = 9 := by decide

/-- **(E) 信息-记忆条件被计算钉住**：把策略限制成事前一个比特，最好也只有 3，
    严格掉在 value 9 之下。差别不在收益数字，而在策略能否依赖自己所处的局面。
    这里没有任何 Nash 或子博弈完美断言：`GameTree` 没有第二_player_ 标签，也没有机会节点
    （echo `GameTree.lean:9-10,119-122`）。 -/
theorem committed_bit_is_strictly_below_value :
    max (play eTree (constStrategy true)) (play eTree (constStrategy false)) <
      GameTree.value eTree := by
  rw [constStrategy_reads.1, constStrategy_reads.2, eTree_value]
  decide

/-- 量词位置的合式陈述：∀（在所有策略上）在 value 之外，∃（达到 value 的策略）在 value
    之内，而该 witness 是局面依赖的。 -/
theorem strategy_quantifier_outside_value :
    (∀ π : Strategy, play eTree π ≤ GameTree.value eTree) ∧
      ∃ π : Strategy, play eTree π = GameTree.value eTree :=
  ⟨fun π => play_le_value _ π, ⟨bestStrategy, play_bestStrategy _⟩⟩

/-! ## 八、未覆盖片段（显式声明，状态 UNPROVEN，不作为定理引用） -/

/-- 未覆盖片段，状态 UNPROVEN：一般有限法律博弈上的**均衡层**回拉——"只要履行回到最优反应
    集，就存在一个以履行为被请求人行动的均衡剖面"。本件已算出它在声明网格上为假
    （`no_pure_equilibrium_at_adequate_sanction`：k = 30 满足回拉前提却无任何纯均衡），
    故该形必须另加前提。写成 `def … : Prop` 而不作定理，是为了让"这里没有证明"成为
    文件里可检索的事实，而不是主张它为真。 -/
def general_equilibrium_pull_back_UNPROVEN : Prop :=
  ∀ (k : ℚ), lawfulInBestResponse k → ∃ c : ActC,
    (∀ c' : ActC, legalPay k c' ActR.perform Role.claimant ≤
        legalPay k c ActR.perform Role.claimant) ∧
      (∀ r : ActR, legalPay k c r Role.respondent ≤ legalPay k c ActR.perform Role.respondent)

end JurisLean.Seams.PayoffEquilibrium
