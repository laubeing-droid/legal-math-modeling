import Mathlib.Tactic
import JurisLean.Seams.PayoffEquilibrium

/-!
S4 针位承接件（附录 I.13 第 27–31 针）—— 以原验收名命名的五条真定理。

出处：`docs/spec/20261007-统一法律数学模型_附录I_Lean施工明细.md` §I.13 的 S4 段
（第 27–31 针，拟合同以施工单给出的原文摘要为准，本件不复刻行号）；全部数学锚来自
`proofs/lean/juris_lean/JurisLean/Seams/PayoffEquilibrium.lean`（行号按本仓当前树）。
承接风格与通过件 `Seams/UnifiedNeedlesS0S1.lean` 一致：先在本件内构造具体载体，
把锚定理前提真实证出，再实例化锚。

## 一、法律语义（人话）

- 27 `legal_outcome_law_preserved`：程序树后果分布保持。无锚，自建小树结构＋归纳。
  "核推"（kernel push）只重写内部节点的内核侧记账标签，不动程序结构与叶子上的
  （实际后果, 法律结局）配对。同一定理内交出：后果分布保持（叶序列级＋逐后果计数级）、
  信息集保持、信息集对任意核标签重写不敏感（不泄漏）、信息集恒等于后果分布的法律投影，
  并附见证树的闭式读数。
- 28 `legal_payoff_preserved`：实际后果现金流编码保持。锚
  `PayoffEquilibrium.lean:224 legal_payoff_preserved`（保地位的载体改名不动收益）与
  `:234 payoff_determined_by_status`（读数式同余）。本件构造显式现金流记录
  （逐期条目 + 声明地位 + 登记位）与其到卷宗载体 `Case` 的编码；重写只动登记位，
  实际现金流逐条不动，法律收益经锚定理保持；附具体三笔现金流与 8 个网格读数。
- 29 `external_equilibrium_reflects_legal`：锚 `PayoffEquilibrium.lean:320`（两玩家
  ε+2η 传递）实例化到具体法律博弈载体（请求人 起诉/不起诉 × 被申请人 履行/拒不履行
  的 ℚ 收益表）。语句保留"两玩家有理纯策略"前提：剖面须在外部估计收益下 ε-有理。
- 30 `finite_legal_mixed_equilibrium_exists`：**降载体**——双玩家（各两纯策略）有限博弈，
  不做 Kakutani。构造 2×2 匹配硬币式表，显式解出满支撑混合均衡 p = q = 1/2；
  并证退化支撑不可能承载均衡（边界混合逐格排除 + 四个纯策略剖面逐一非均衡），
  这是支撑枚举在 2×2 上的完备侧读数。
- 31 `payoff_error_yields_two_eta_equilibrium`：锚 `PayoffEquilibrium.lean:285 abs_two_close`
  （三角界）、`:303 dev_gain_two_eta`（偏差值 2η 夹界）、`:320`（传递）全部实例化到
  同一具体载体，附三角界在具体数值上的紧读数。

## 二、数学对象

- 27：`ProgStep`（立案/庭审）∥ `ActualLegalOutcome`（actual : Nat, legal : LegalStatus）∥
  `ProgTree`（叶子 = 后果对；内部节点 = 程序步骤 + 内核标签 + 左右子树）∥ `kernelPush`
  （标签归一）∥ `retag f`（任意标签重写）∥ `leafOutcomes`（叶序列）∥ `infoSet`
  （法律侧投影）∥ `witnessTree`（见证树）。
- 28：`CashEntry`（period, amount : ℚ）∥ `CashFlow`（entries, declaredStatus, docket）∥
  `cashTotal`（逐条求和）∥ `encodeFlow`（→ `Case`）∥ `relabelFlow`（只翻登记位）∥
  `witnessFlow`（三笔具体现金流）。
- 29/31：`PC`（sue/forbear）∥ `PR`（perform/breach）∥ `uLaw`、`vEst` 两张 8 格 ℚ 收益表
  （逐点相差 ≤ 1/2，且恰在 (sue, perform) 剖面两角色各差 1/2）。
- 30：`uPenn`（匹配硬币式 8 格表）∥ `mixC`/`mixR`（混合策略）∥ `euC`/`euR`
  （双线性期望收益，闭式 = ±(2p-1)(2q-1)）∥ `IsProb` ∥ `IsMixedNash`
  （混合偏差下的 Nash 判据，偏差域 = 全体概率混合）。

## 三、本件证什么、不证什么

**证**：五针各一条定理，全部由本件构造或既有锚（`PayoffEquilibrium.lean`）合成；
每针前提（η-接近、ε-有理等）要么在本件内对具体载体真实证出，要么作为明示假设
保留在签名里，无一外填为空洞真。
**不证**（逐针边界）：
- 27 只覆盖有限二叉程序树；"分布"以叶子后果序列/逐后果计数承载，不是测度论载体；
  信息集 = 后果分布的法律投影，不含一般信息集代数或完美回忆条件。
- 28 的现金流数值与 `PayoffEquilibrium` 折价同为 [代拟稿]，无经验校准；
  编码保持只在"重写不动声明地位"的载体内成立（动了地位的改名不在保持范围内）。
- 29 只证传递，不证任何一侧的均衡存在性；"两玩家有理纯策略"前提不可删除。
- 30 只覆盖双玩家 2×2：一般有限博弈混合均衡存在性（Kakutani／上游
  `External/GameTheory/Theorems/NashExistenceMixed.lean:717`）不在本件；也不证
  全空间唯一性，只证"边界不可能 + 满支撑解存在"的枚举读数。
- 31 的 η、ε 仍是假设参数，η 的法律来源本件不认定。

## 四、档位

五针均为[已证，认定待 CI]。本件不含占位证明、不引入未证公理、不用 `native_decide`、
无 `: True :=` 逃避式；`decide` 仅作 `Decidable` 布尔求值出现在逐后果计数的谓词里，
`rfl` 仅用于本件内可定义展开的闭式计算。按仓库边界约定，Lean 权威认定在 CI；
本机不运行 Lean，当前状态 CI_NOT_RUN（fail-closed），本地静态自检仅为 provisional。
-/

namespace JurisLean.Seams.UnifiedNeedlesS4

open JurisLean.Seams.PayoffEquilibrium

/-! ## 第 27 针：legal_outcome_law_preserved（程序树后果分布保持） -/

/-- 程序步骤（声明侧）：立案 / 庭审。 -/
inductive ProgStep
  | fileCase
  | holdHearing
  deriving DecidableEq

/-- 叶子上的后果对：实际发生的给付（actual，货币单位）与声明法律结局（legal）。 -/
structure ActualLegalOutcome where
  actual : Nat
  legal : LegalStatus
  deriving DecidableEq

/-- 有限程序树：叶子挂后果对；内部节点 = 一个程序步骤 + 一位**内核侧**记账标签 +
  左右子树。内核标签不属于声明程序信息，`kernelPush`/`retag` 只动它。 -/
inductive ProgTree where
  | leaf : ActualLegalOutcome → ProgTree
  | step : ProgStep → Bool → ProgTree → ProgTree → ProgTree

/-- 核推：把所有内部节点的内核标签归一为 true；程序结构与叶子后果不动。 -/
def kernelPush : ProgTree → ProgTree
  | .leaf o => .leaf o
  | .step ps _ l r => .step ps true (kernelPush l) (kernelPush r)

/-- 任意核标签重写：`retag f` 把每个内部标签换成其 `f` 像；结构、叶子不动。 -/
def retag (f : Bool → Bool) : ProgTree → ProgTree
  | .leaf o => .leaf o
  | .step ps b l r => .step ps (f b) (retag f l) (retag f r)

/-- 后果分布（序列表示）：从左到右收集叶子上的（实际, 法律）后果对。 -/
def leafOutcomes : ProgTree → List ActualLegalOutcome
  | .leaf o => [o]
  | .step _ _ l r => leafOutcomes l ++ leafOutcomes r

/-- 信息集（声明侧读数）：只收集叶子的法律结局；内核标签不进信息集。 -/
def infoSet : ProgTree → List LegalStatus
  | .leaf o => [o.legal]
  | .step _ _ l r => infoSet l ++ infoSet r

/-- 核推保持后果分布（叶序列级）：对树结构归纳，核推不动叶子。 -/
theorem leafOutcomes_kernelPush (t : ProgTree) :
    leafOutcomes (kernelPush t) = leafOutcomes t := by
  induction t with
  | leaf o => rfl
  | step ps tag l r ihl ihr =>
      show leafOutcomes (kernelPush l) ++ leafOutcomes (kernelPush r)
        = leafOutcomes l ++ leafOutcomes r
      rw [ihl, ihr]

/-- 核推保持信息集。 -/
theorem infoSet_kernelPush (t : ProgTree) :
    infoSet (kernelPush t) = infoSet t := by
  induction t with
  | leaf o => rfl
  | step ps tag l r ihl ihr =>
      show infoSet (kernelPush l) ++ infoSet (kernelPush r) = infoSet l ++ infoSet r
      rw [ihl, ihr]

/-- 信息集对任意核标签重写不敏感：无论标签怎么改写，信息集读数相同（不泄漏）。 -/
theorem infoSet_retag_invariant (f g : Bool → Bool) (t : ProgTree) :
    infoSet (retag f t) = infoSet (retag g t) := by
  induction t with
  | leaf o => rfl
  | step ps tag l r ihl ihr =>
      show infoSet (retag f l) ++ infoSet (retag f r) = infoSet (retag g l) ++ infoSet (retag g r)
      rw [ihl, ihr]

/-- 信息集恒等于后果分布的法律投影。 -/
theorem infoSet_eq_legal_map (t : ProgTree) :
    infoSet t = (leafOutcomes t).map ActualLegalOutcome.legal := by
  induction t with
  | leaf o => rfl
  | step ps tag l r ihl ihr =>
      show infoSet l ++ infoSet r = (leafOutcomes l ++ leafOutcomes r).map ActualLegalOutcome.legal
      rw [ihl, ihr, List.map_append]

/-- 见证程序树：一次立案（标签故意留脏 false）下，庭审分支挂两个结局，旁路直接挂一个。 -/
def witnessTree : ProgTree :=
  .step ProgStep.fileCase false
    (.step ProgStep.holdHearing true
      (.leaf ⟨5, LegalStatus.upheld⟩)
      (.leaf ⟨0, LegalStatus.dismissed⟩))
    (.leaf ⟨0, LegalStatus.unenforceable⟩)

/-- 见证树的闭式读数：叶序列与信息集都能被 `rfl` 级归约读出（非真空检查）。 -/
theorem witnessTree_readout :
    leafOutcomes witnessTree =
      [⟨5, LegalStatus.upheld⟩, ⟨0, LegalStatus.dismissed⟩, ⟨0, LegalStatus.unenforceable⟩] ∧
    infoSet witnessTree = [LegalStatus.upheld, LegalStatus.dismissed, LegalStatus.unenforceable] :=
  ⟨rfl, rfl⟩

/-- **第 27 针（S4，附录 I.13 第 27 针）**：程序树后果分布保持。
    同一程序树在核推前后：(1) 叶序列上的（实际, 法律）后果分布相同；(2) 逐后果计数
    （经验分布读数）相同；(3) 信息集相同；(4) 信息集对**任意**核标签重写不敏感——
    信息集读不出任何内核侧记账信息（不泄漏）；(5) 信息集只是后果分布的法律投影；
    (6) 任何两棵后果分布相同的树信息集相同（信息集由分布决定，与核态无关）；
    (7) 见证树闭式读数（非真空）。
    边界：有限二叉程序树的显式归纳；分布以序列/计数承载，不是测度论载体；
    信息集 = 法律侧投影，不含一般信息集代数或完美回忆条件。 -/
theorem legal_outcome_law_preserved (t : ProgTree) :
    leafOutcomes (kernelPush t) = leafOutcomes t ∧
    (∀ o : ActualLegalOutcome,
      (leafOutcomes (kernelPush t)).countP (fun x => decide (x = o))
        = (leafOutcomes t).countP (fun x => decide (x = o))) ∧
    infoSet (kernelPush t) = infoSet t ∧
    (∀ f g : Bool → Bool, infoSet (retag f t) = infoSet (retag g t)) ∧
    infoSet t = (leafOutcomes t).map ActualLegalOutcome.legal ∧
    (∀ t₁ t₂ : ProgTree, leafOutcomes t₁ = leafOutcomes t₂ → infoSet t₁ = infoSet t₂) ∧
    (leafOutcomes witnessTree =
      [⟨5, LegalStatus.upheld⟩, ⟨0, LegalStatus.dismissed⟩, ⟨0, LegalStatus.unenforceable⟩] ∧
      infoSet witnessTree = [LegalStatus.upheld, LegalStatus.dismissed, LegalStatus.unenforceable]) :=
  ⟨leafOutcomes_kernelPush t,
    fun o => by rw [leafOutcomes_kernelPush t],
    infoSet_kernelPush t,
    fun f g => infoSet_retag_invariant f g t,
    infoSet_eq_legal_map t,
    fun t₁ t₂ h => by rw [infoSet_eq_legal_map, infoSet_eq_legal_map, h],
    witnessTree_readout⟩

/-! ## 第 28 针：legal_payoff_preserved（实际后果现金流编码保持） -/

/-- 现金流条目：期次与金额（金额为 ℚ，符号区分收付方向）。 -/
structure CashEntry where
  period : Nat
  amount : ℚ

/-- 实际后果现金流记录：逐期条目 + 声明法律结局 + 一位与法律评价无关的登记位。 -/
structure CashFlow where
  entries : List CashEntry
  declaredStatus : LegalStatus
  docket : Bool

/-- 现金流本体的实际折算：逐条求和（与编码无关侧）。 -/
def cashTotal (cf : CashFlow) : ℚ := cf.entries.foldr (fun e acc => e.amount + acc) 0

/-- 编码：现金流记录 → 卷宗载体 `Case`（声明地位 + 登记位）。 -/
def encodeFlow (cf : CashFlow) : Case := ⟨cf.declaredStatus, cf.docket⟩

/-- 载体重写：只翻登记位；条目与声明地位都不动。 -/
def relabelFlow (cf : CashFlow) : CashFlow := ⟨cf.entries, cf.declaredStatus, !cf.docket⟩

/-- 具体三笔现金流：期初给付 10、判后费用 -3、迟延补差 1；声明结局"支持"。 -/
def witnessFlow : CashFlow where
  entries := [⟨0, 10⟩, ⟨1, -3⟩, ⟨2, 1⟩]
  declaredStatus := LegalStatus.upheld
  docket := true

/-- 见证读数：实际折算 = 8；两侧法律收益 = 7 / -7（后者正是锚网格的第 1、2 格）。 -/
theorem witnessFlow_readout :
    cashTotal witnessFlow = 8 ∧
    payoffOf Role.claimant (encodeFlow witnessFlow) = 7 ∧
    payoffOf Role.respondent (encodeFlow witnessFlow) = -7 := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [cashTotal, witnessFlow, List.foldr_cons, List.foldr_nil]
  · exact legal_payoff_grid.1
  · exact legal_payoff_grid.2.1

/-- **第 28 针（S4，附录 I.13 第 28 针）**：实际后果现金流编码保持。
    显式现金流记录 `CashFlow` 经 `encodeFlow` 编码进卷宗载体 `Case`；只动登记位的
    载体重写 `relabelFlow`：(1) 实际现金流逐条不动（`cashTotal` 保持）；(2) 法律收益
    经锚 `PayoffEquilibrium.lean:224 legal_payoff_preserved`（保地位改名不动收益）保持
    ——此处 `f := swapDocket`，其"保地位"前提 `∀ c, statusOf (f c) = statusOf c` 由
    `rfl` 级投影读出真实成立；(3) 见证现金流与网格读数（8 / 7 / -7）。
    边界：数值为 [代拟稿]；编码保持只在"重写不动声明地位"的载体内成立。 -/
theorem legal_payoff_preserved (role : Role) (cf : CashFlow) :
    cashTotal (relabelFlow cf) = cashTotal cf ∧
    payoffOf role (encodeFlow (relabelFlow cf)) = payoffOf role (encodeFlow cf) ∧
    (cashTotal witnessFlow = 8 ∧
      payoffOf Role.claimant (encodeFlow witnessFlow) = 7 ∧
      payoffOf Role.respondent (encodeFlow witnessFlow) = -7) :=
  ⟨rfl,
    JurisLean.Seams.PayoffEquilibrium.legal_payoff_preserved
      (f := JurisLean.Seams.PayoffEquilibrium.swapDocket) (fun _ => rfl) role (encodeFlow cf),
    witnessFlow_readout.1, witnessFlow_readout.2.1, witnessFlow_readout.2.2⟩

/-! ## 第 29、31 针公共载体：具体法律博弈的两张收益表 -/

/-- 请求人（原告侧）纯策略：起诉 / 不起诉（容忍）。 -/
inductive PC
  | sue
  | forbear
  deriving DecidableEq

/-- 被申请人（被告侧）纯策略：履行 / 拒不履行。 -/
inductive PR
  | perform
  | breach
  deriving DecidableEq

/-- 法律收益表 `uLaw`（[代拟稿]：声明网格，无经验校准）。 -/
def uLaw : PC → PR → Role → ℚ
  | .sue, .perform, .claimant => 2
  | .sue, .perform, .respondent => -3 / 2
  | .sue, .breach, .claimant => 0
  | .sue, .breach, .respondent => -2
  | .forbear, .perform, .claimant => 1
  | .forbear, .perform, .respondent => 0
  | .forbear, .breach, .claimant => 1
  | .forbear, .breach, .respondent => 0

/-- 外部估计收益表 `vEst`：与 `uLaw` 逐点相差 ≤ 1/2，且恰在 (sue, perform) 剖面
    两角色各差 1/2，其余格完全相同。 -/
def vEst : PC → PR → Role → ℚ
  | .sue, .perform, .claimant => 5 / 2
  | .sue, .perform, .respondent => -1
  | .sue, .breach, .claimant => 0
  | .sue, .breach, .respondent => -2
  | .forbear, .perform, .claimant => 1
  | .forbear, .perform, .respondent => 0
  | .forbear, .breach, .claimant => 1
  | .forbear, .breach, .respondent => 0

/-- η-接近前提在具体载体上成立：两张表逐点相差 ≤ 1/2。 -/
theorem uLaw_vEst_within_half : WithinEta uLaw vEst (1 / 2 : ℚ) := by
  intro a b r
  cases a <;> cases b <;> cases r <;> norm_num [uLaw, vEst]

/-- 两玩家有理纯策略前提在具体载体上成立：(sue, perform) 是 `vEst` 下的
    精确（0-）均衡剖面——两玩家偏差收益都 ≤ 0。 -/
theorem vEst_sue_perform_is_rational : IsApproxNash vEst 0 PC.sue PR.perform := by
  refine ⟨fun a' => ?_, fun b' => ?_⟩
  · cases a' <;> norm_num [vEst]
  · cases b' <;> norm_num [vEst]

/-- 直接读数（不经锚）：同一剖面在 `uLaw` 下是 1-均衡，与 ε=0、η=1/2 时的
    ε+2η = 1 传递读数一致。 -/
theorem uLaw_sue_perform_one_equilibrium : IsApproxNash uLaw 1 PC.sue PR.perform := by
  refine ⟨fun a' => ?_, fun b' => ?_⟩
  · cases a' <;> norm_num [uLaw]
  · cases b' <;> norm_num [uLaw]

/-- **第 29 针（S4，附录 I.13 第 29 针）**：外部均衡折回法律收益。
    锚 `PayoffEquilibrium.lean:320 external_equilibrium_reflects_legal`（两玩家
    ε+2η 传递）实例化到具体法律博弈载体（`PC`×`PR` 两张 ℚ 表）：
    (1) 一般支——任意 ε、η 下，外部估计的 ε-有理剖面折回法律收益是 (ε+2η)-有理；
    (2) 常数支——η = 1/2、ε = 0 时，锚输出 `IsApproxNash uLaw (0 + 2 * (1/2)) sue perform`，
    其两个前提 `uLaw_vEst_within_half`、`vEst_sue_perform_is_rational` 都在本件内
    对具体表真实证出，不是外填假设；(3) 直接读数（不经锚）的 1-均衡。
    边界：只证传递，不证任何一侧均衡存在性；"两玩家有理纯策略"前提（`hrat`）
    保留在签名里，不可删除。 -/
theorem external_equilibrium_reflects_legal (a : PC) (b : PR) (ε η : ℚ)
    (hrat : IsApproxNash vEst ε a b)
    (hclo : WithinEta uLaw vEst η) :
    IsApproxNash uLaw (ε + 2 * η) a b ∧
    IsApproxNash uLaw (0 + 2 * (1 / 2 : ℚ)) PC.sue PR.perform ∧
    IsApproxNash uLaw 1 PC.sue PR.perform :=
  ⟨JurisLean.Seams.PayoffEquilibrium.external_equilibrium_reflects_legal
      uLaw vEst ε η a b hclo hrat,
    JurisLean.Seams.PayoffEquilibrium.external_equilibrium_reflects_legal
      uLaw vEst 0 (1 / 2 : ℚ) PC.sue PR.perform
      uLaw_vEst_within_half vEst_sue_perform_is_rational,
    uLaw_sue_perform_one_equilibrium⟩

/-! ## 第 30 针：finite_legal_mixed_equilibrium_exists（双玩家 2×2 显式混合均衡） -/

/-- 匹配硬币式表 `uPenn`（[代拟稿]）：(起诉, 履行) 与 (不起诉, 拒不履行) 同侧得 1，
    其余剖面反侧——纯策略层无均衡，混合层有唯一满支撑解。 -/
def uPenn : PC → PR → Role → ℚ
  | .sue, .perform, .claimant => 1
  | .sue, .perform, .respondent => -1
  | .sue, .breach, .claimant => -1
  | .sue, .breach, .respondent => 1
  | .forbear, .perform, .claimant => -1
  | .forbear, .perform, .respondent => 1
  | .forbear, .breach, .claimant => 1
  | .forbear, .breach, .respondent => -1

/-- 请求人混合策略：以概率 p 起诉、1-p 不起诉。 -/
def mixC (p : ℚ) : PC → ℚ
  | .sue => p
  | .forbear => 1 - p

/-- 被申请人混合策略：以概率 q 履行、1-q 拒不履行。 -/
def mixR (q : ℚ) : PR → ℚ
  | .perform => q
  | .breach => 1 - q

/-- 请求人期望收益：`uPenn`（claimant 侧）到混合策略的双线性延拓。 -/
def euC (p q : ℚ) : ℚ :=
  mixC p PC.sue * (mixR q PR.perform * uPenn PC.sue PR.perform Role.claimant
      + mixR q PR.breach * uPenn PC.sue PR.breach Role.claimant)
    + mixC p PC.forbear * (mixR q PR.perform * uPenn PC.forbear PR.perform Role.claimant
      + mixR q PR.breach * uPenn PC.forbear PR.breach Role.claimant)

/-- 被申请人期望收益：`uPenn`（respondent 侧）到混合策略的双线性延拓。 -/
def euR (p q : ℚ) : ℚ :=
  mixC p PC.sue * (mixR q PR.perform * uPenn PC.sue PR.perform Role.respondent
      + mixR q PR.breach * uPenn PC.sue PR.breach Role.respondent)
    + mixC p PC.forbear * (mixR q PR.perform * uPenn PC.forbear PR.perform Role.respondent
      + mixR q PR.breach * uPenn PC.forbear PR.breach Role.respondent)

/-- 概率混合的值域谓词。 -/
def IsProb (x : ℚ) : Prop := 0 ≤ x ∧ x ≤ 1

/-- 双玩家混合 Nash 判据：两玩家都可偏差到**任意**概率混合而不增收益。 -/
def IsMixedNash (p q : ℚ) : Prop :=
  (∀ p' : ℚ, IsProb p' → euC p' q ≤ euC p q) ∧
    (∀ q' : ℚ, IsProb q' → euR p q' ≤ euR p q)

/-- 闭式：请求人期望收益 = (2p-1)(2q-1)。 -/
theorem euC_eq (p q : ℚ) : euC p q = (2 * p - 1) * (2 * q - 1) := by
  simp only [euC, mixC, mixR, uPenn]
  ring

/-- 闭式：被申请人期望收益 = -(2p-1)(2q-1)。 -/
theorem euR_eq (p q : ℚ) : euR p q = -((2 * p - 1) * (2 * q - 1)) := by
  simp only [euR, mixC, mixR, uPenn]
  ring

theorem two_half_sub_one : (2 : ℚ) * (1 / 2 : ℚ) - 1 = 0 := by norm_num

/-- 满支撑混合均衡：(1/2, 1/2)。对方半混合时己方收益恒为 0（与己方混合无关），
    故任何概率偏差都无增益。 -/
theorem half_is_mixed_nash : IsMixedNash (1 / 2 : ℚ) (1 / 2 : ℚ) := by
  refine ⟨fun p' _ => ?_, fun q' _ => ?_⟩
  · rw [euC_eq, euC_eq, two_half_sub_one]
    simp
  · rw [euR_eq, euR_eq, two_half_sub_one]
    simp

/-- 期望收益的边界求值闭式（支撑枚举的排除侧工具）。 -/
theorem euC_eq_left_one (q : ℚ) : euC 1 q = 2 * q - 1 := by rw [euC_eq]; ring

theorem euC_eq_left_zero (q : ℚ) : euC 0 q = -(2 * q - 1) := by rw [euC_eq]; ring

theorem euC_eq_right_one (p : ℚ) : euC p 1 = 2 * p - 1 := by rw [euC_eq]; ring

theorem euC_eq_right_zero (p : ℚ) : euC p 0 = -(2 * p - 1) := by rw [euC_eq]; ring

theorem euR_eq_left_zero (q : ℚ) : euR 0 q = 2 * q - 1 := by rw [euR_eq]; ring

theorem euR_eq_right_zero (p : ℚ) : euR p 0 = 2 * p - 1 := by rw [euR_eq]; ring

theorem euR_eq_left_one (q : ℚ) : euR 1 q = -(2 * q - 1) := by rw [euR_eq]; ring

theorem euR_eq_right_one (p : ℚ) : euR p 1 = -(2 * p - 1) := by rw [euR_eq]; ring

/-- 支撑枚举的排除侧：混合均衡不可能落在边界上（任一方退化成纯策略）。
    四种退化各用两条最优反应不等式推出矛盾。 -/
theorem pennies_no_boundary_equilibrium {p q : ℚ} (hn : IsMixedNash p q)
    (hb : p = 0 ∨ p = 1 ∨ q = 0 ∨ q = 1) : False := by
  have h1 : IsProb (1 : ℚ) := ⟨by norm_num, by norm_num⟩
  have h0 : IsProb (0 : ℚ) := ⟨by norm_num, by norm_num⟩
  rcases hb with hp | hp | hq | hq
  · subst hp
    have e1 := hn.1 1 h1
    have e2 := hn.2 1 h1
    simp only [euC_eq_left_one, euC_eq_left_zero] at e1
    simp only [euR_eq_left_zero] at e2
    linarith
  · subst hp
    have e1 := hn.1 0 h0
    have e2 := hn.2 0 h0
    simp only [euC_eq_left_zero, euC_eq_left_one] at e1
    simp only [euR_eq_right_zero, euR_eq_left_one] at e2
    linarith
  · subst hq
    have e1 := hn.1 0 h0
    have e2 := hn.2 1 h1
    simp only [euC_eq_left_zero, euC_eq_right_zero] at e1
    simp only [euR_eq_right_one, euR_eq_right_zero] at e2
    linarith
  · subst hq
    have e1 := hn.1 1 h1
    have e2 := hn.2 0 h0
    simp only [euC_eq_left_one, euC_eq_right_one] at e1
    simp only [euR_eq_right_zero, euR_eq_right_one] at e2
    linarith

/-- 支撑枚举的纯端：四个纯策略剖面在 `uPenn` 下都不是 0-均衡（每格恰有一方可获利偏差）。 -/
theorem pennies_no_pure_profile_is_nash : ∀ (a : PC) (b : PR), ¬ IsApproxNash uPenn 0 a b := by
  intro a b
  cases a with
  | sue =>
      cases b with
      | perform => exact fun ⟨_, h2⟩ => absurd (h2 PR.breach) (by norm_num [uPenn])
      | breach => exact fun ⟨h1, _⟩ => absurd (h1 PC.forbear) (by norm_num [uPenn])
  | forbear =>
      cases b with
      | perform => exact fun ⟨h1, _⟩ => absurd (h1 PC.sue) (by norm_num [uPenn])
      | breach => exact fun ⟨_, h2⟩ => absurd (h2 PR.perform) (by norm_num [uPenn])

/-- **第 30 针（S4，附录 I.13 第 30 针，降载体）**：有限博弈混合均衡存在。
    **降载体声明（如实标注）**：只覆盖**双玩家**、各两个纯策略的有限博弈（2×2），
    不做 Kakutani，也不触上游 `NashExistenceMixed.lean:717` 的存在性主张。
    在匹配硬币式表 `uPenn` 上：(1) 显式解出混合均衡 p = q = 1/2（满支撑：两玩家
    的两个纯策略都以正概率使用）；(2) 该解通过 `IsMixedNash` 判据（偏差域 = 全体
    概率混合）验证；(3) 退化支撑被排除——任何边界混合（p 或 q ∈ {0,1}）都不是均衡；
    (4) 四个纯策略剖面逐一不是均衡。这四条合起来是 2×2 支撑枚举的完备侧读数：
    唯一候选是满支撑解，且它存在。 -/
theorem finite_legal_mixed_equilibrium_exists :
    ∃ p q : ℚ,
      IsProb p ∧
      IsProb q ∧
      IsMixedNash p q ∧
      p = 1 / 2 ∧
      q = 1 / 2 ∧
      (0 < p ∧ p < 1) ∧
      ¬ (p = 0 ∨ p = 1 ∨ q = 0 ∨ q = 1) ∧
      (∀ (a : PC) (b : PR), ¬ IsApproxNash uPenn 0 a b) :=
  ⟨1 / 2, 1 / 2,
    ⟨by norm_num, by norm_num⟩,
    ⟨by norm_num, by norm_num⟩,
    half_is_mixed_nash,
    rfl,
    rfl,
    ⟨by norm_num, by norm_num⟩,
    fun hcon => pennies_no_boundary_equilibrium half_is_mixed_nash hcon,
    pennies_no_pure_profile_is_nash⟩

/-! ## 第 31 针：payoff_error_yields_two_eta_equilibrium -/

/-- **第 31 针（S4，附录 I.13 第 31 针）**：收益误差产出 2η-均衡。
    锚 `PayoffEquilibrium.lean:285 abs_two_close`（三角界）、`:303 dev_gain_two_eta`
    （偏差值之差被 2η 夹住）、`:320 external_equilibrium_reflects_legal`（传递）
    全部实例化到同一具体载体：(1) 任意偏差 `a'` 与角色 `r` 上，外部估计与法律收益
    之间的**偏差值之差** ≤ 2η（`dev_gain_two_eta` 的直接实例化）；
    (2) 外部 ε-有理剖面折回法律收益是 (ε+2η)-均衡（传递实例化）；
    (3) 三角界在具体数值上的紧读数：|2-5/2| ≤ 1/2、|5/2-3| ≤ 1/2 ⇒ |2-3| ≤ 2·(1/2)，
    两端恰为 1（上界可达，与锚 `two_eta_bound_is_tight` 同形的具体见证）；
    (4) 直接读数的 1-均衡。
    边界：η、ε 是假设参数，η 的法律来源本件不认定。 -/
theorem payoff_error_yields_two_eta_equilibrium (a a' : PC) (b : PR) (r : Role) (ε η : ℚ)
    (hclo : WithinEta uLaw vEst η) (hrat : IsApproxNash vEst ε a b) :
    |(vEst a' b r - vEst a b r) - (uLaw a' b r - uLaw a b r)| ≤ 2 * η ∧
    IsApproxNash uLaw (ε + 2 * η) a b ∧
    (|(2 : ℚ) - 5 / 2| ≤ 1 / 2 ∧
      |(5 : ℚ) / 2 - 3| ≤ 1 / 2 ∧
      |(2 : ℚ) - 3| ≤ 2 * (1 / 2 : ℚ)) ∧
    IsApproxNash uLaw 1 PC.sue PR.perform :=
  ⟨JurisLean.Seams.PayoffEquilibrium.dev_gain_two_eta uLaw vEst η hclo a a' b r,
    JurisLean.Seams.PayoffEquilibrium.external_equilibrium_reflects_legal
      uLaw vEst ε η a b hclo hrat,
    ⟨by norm_num, by norm_num,
      JurisLean.Seams.PayoffEquilibrium.abs_two_close (a := 2) (b := 5 / 2) (c := 3) (η := 1 / 2)
        (by norm_num) (by norm_num)⟩,
    uLaw_sue_perform_one_equilibrium⟩

end JurisLean.Seams.UnifiedNeedlesS4
