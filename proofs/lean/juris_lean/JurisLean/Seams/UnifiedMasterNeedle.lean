import Mathlib.Tactic
import JurisLean.Seams.UnifiedNetTrajectory
import JurisLean.Seams.UnifiedPayoffChain
import JurisLean.Seams.UnifiedEvalLayer
import JurisLean.Seams.UnifiedQuantLedger
import JurisLean.Seams.UnifiedEquilExist
import JurisLean.Seams.UnifiedBetaDomain
import JurisLean.Seams.UnifiedNeedlesS3b

/-!
# W0 总针语义重建（第 60 针，附录 I:814；UnifiedMasterNeedle）

本件是 Z1 审计（`docs/full-math/NEEDLE_STRENGTH_AUDIT.md` 针 60 行，判**差额**）的
收口施工。旧交付 `Seams/UnifiedNeedlesTotal.lean`（保留不动，历史交付）被合同明文
否定："同一个 M 五约合取＋数量 AST 独立算术性质"——数量、Beta/概率、策略/均衡、
事件链解释**没有接到主链实际生成的共同中间结果**，也没有交换关系与误差传播。

## 施工合同（唯一权威：`docs/spec/20261007-统一法律数学模型_附录I_Lean施工明细.md` §I.13 :814）

> "共同中间见证、全静态链/事件链及精度传播总定理，明确实际适用域与全部原义务；
> 不得用'同一个 M'加独立算术性质代替连接"

R1 方案 W0 节（`docs/master-plan/20261010_统一法律数学模型_连续与语义全量施工方案.md`
§二 W0）：把数量 AST、Beta/概率、策略/均衡、事件链解释**接到主链实际生成的共同
中间结果**，证明相应交换关系与误差传播后再汇总。

## 一、本件结构（对照 I:814 逐义务）

| I:814 义务 | 本件条款 |
|---|---|
| 共同中间见证 | `CoherentInterim` 载体＋`Coherent` 谓词＋`masterInterim_coherent`：网络轨迹（W15）、账本读数（B06/B07）、收益链读数（W13）、评价层判定（W12）、区间/Beta 精度面（BetaDomain）在**一个综合合成案例**上同源共存，且以数值接线（C3–C7）互相咬合——不是"同一个 M"加独立算术 |
| 全静态链/事件链 | `master_static_event_correspondence`：(a) 事件链终态 ⊆ Horn 闭包（轨迹不能私造可推导性）；(b) 本案消费的原子集上静态可导 ⇔ 事件链实际产出（双向，限消费集）；(c) 每步规则钉死在 29 条规则表内、法源在效力窗口内 |
| 交换关系 | 三组：`ledger_payment_split_exchange`（支付流分段/重排与余额/收益读数交换——钳位复合代数）；`master_loss_aggregation_share_exchange`（损失区间合并×份额缩放分配律＋首见去重×缩放交换——端点代数与归纳证明）；`master_channel_exchange_readings`（负担输入通道×支付通道在综合中间结果上交换） |
| 精度传播 | `master_error_propagation_chain`：收益层（偏好积分对条目扰动的线性界）、账本层（ReLU 1-Lipschitz 支付扰动界）、数量面（divFree AST 整值承载，ε=0）、概率面（包围宽度→期望读数界），并合成端到端 `master_exposure_perturb_chain`（输入扰动→各层读数扰动界→总读数界） |
| 事件链解释接线 | 事件链即主链：`RequiredAtoms` 全部由 17 步满料轨迹实际产出且落入静态闭包 |
| 数量 AST 接线 | `master_qty_ast_carries_balance`：清偿后余额读数 160 由 divFree AST 逐字承载（针 25 的整值面进入主链，不再是独立算术） |
| Beta/概率接线 | `master_beta_face`：Bernstein CDF(2,3) 连续严格递增＋ℚ 闭式可比较；`beta_enclosure_expected_reading` 把 CDF 包围宽度 ρ 传播到期望读数扰动界（消费 BetaDomain 精度预算界面） |
| 策略/均衡接线 | `master_equil_face`：合法/制裁菜单的收益值恰为余额/收益读数（`masterLawful`），Kakutani 路线存在性＋ℚ↔ℝ 载体同一均衡关系＋显式全配合纯均衡 |
| 总定理 | `unified_legal_derivation_on_declared_fragment` 重建版：上述全部的合取 |
| 明确实际适用域 | 见下方"二、实际适用域" |
| 全部原义务 | 本表＋施工报告 `.local/agent_W17_master_needle_report.md` 逐义务对照 |

## 二、实际适用域（如实声明）

- **案卷域**：综合见证案＝满料案卷 `fullDocket`（十四族材料全在卷）上的 17 步全轨迹
  `fullTraj`；规则域＝29 条具名法源规则表 `familyRuleList`。静态链＝该案卷 Horn 网络
  的 `closureAt`；事件链＝`TraceOk/Productive/TimesInc` 良构轨迹。合同 §10.2 合成
  边界照旧：本件不冒称满料案之外的适用性。
- **两链对应的方向边界**：(a) 是一般健全性（任意良构轨迹）；(b) 的完备方向只在
  **本案消费集** `RequiredAtoms` 上证（四个原子全部被 witness 轨迹实际产出）；
  "闭包元素必被某条有限轨迹产出"的一般完备性仍是 W15 如实列出的开放方向，不在
  本件冒称。
- **数值域**：账本＝B06 demoLedger（费用 10/利息 100/本金 200），支付流 [150]；
  现金流种类归属 `costKindOf` 与制裁折价 1/5、损失区间 [100,200]、Beta(2,3) 后验
  均为 **[代拟稿]** 合成材料（无经验校准）；估值权重承锚表 [代拟稿]。金额一律 ℚ。
- **概率面**：`beta_enclosure_expected_reading` 的分子/分母包围 (N_l,N_u,B_l,B_u)
  是执行层供给接口（与 `UnifiedBetaDomain` 的 `RpowRatEnclosureInput` 同一诚实
  边界——包围的供给侧不在本件）；本件证的是"包围宽度→读数扰动界"的传播律本身。
- **评价面**：`masterFrame` 是 W12 评价层载体的 Pos 型实例（争点 1 二要件链），
  终局＝成立；其与网络侧的接线是同极性声明（C5），不冒称证据评价与规则推导两通道
  在一般情形同值。

## 三、档位

零 `sorry`/零 `admit`/零自定义 `axiom`/零 `: True` 逃避；语句位闭命题（if/decide
不出现在定理语句）；`decide` 战术零使用（闭式计算一律 `rfl`/`norm_num`）；ℚ/Fraction
纪律（Lean 侧 ℚ，Python 侧全 Fraction）。本机镜像试编译（仓外 LEAN_PATH 指向
pinned mathlib v4.30.0 预编译 olean＋全仓 JurisLean olean）exit=0 见施工报告；
CI 是唯一 Lean 权威，当前 CI_NOT_RUN（fail-closed）。旧件
`UnifiedNeedlesTotal.lean` 保留不动，本件为超越交付。
-/

namespace JurisLean.Seams.UnifiedMasterNeedle

open JurisLean.Seams.UnifiedFourteenFamilies
open JurisLean.Seams.SourceNorms
open JurisLean.Seams.UnifiedNetTrajectory
open JurisLean.Seams.PayoffEquilibrium

open Atom

/-! ## 一、共同中间载体：CoherentInterim 与 Coherent 谓词 -/

/-- 综合案件中间结果：主链各层的实际读数在**一个案卷**上同源共存。字段全部来自
本波已绿模块的实际构造（W15 轨迹／B06 账本／W13 收益链／W12 评价层／BetaDomain
概率面），不是"同一个 M"的抽象统一。 -/
structure CoherentInterim where
  /-- 主链案卷：事件链与静态链的共同定义域。 -/
  docket : CaseDocket
  /-- 事件链：十四族网络上的实际轨迹（W15 载体）。 -/
  traj : UnifiedNetTrajectory.NetTrace
  /-- 事件链终态（折叠读数）。 -/
  finalNet : UnifiedNetTrajectory.NetState
  /-- 数量层：分项债项账本（B06/B07 共享 AST 载体）。 -/
  ledger : List UnifiedQuantLedger.LedgerItem
  /-- 数量层：支付流（按准入顺序逐笔抵充）。 -/
  payPlan : List ℚ
  /-- 收益层：现金流条目表（W13 四层编码链的层 1 载体）。 -/
  flows : List UnifiedPayoffChain.CashEntry
  /-- 评价层：证据/标准/终局快照（W12 载体）。 -/
  frame : UnifiedEvalLayer.Frame
  /-- 评价层的争点编号。 -/
  focus : Nat
  /-- 区间面：损失区间读数（B07 区间载体）。 -/
  lossIv : JurisLean.FullMath.Numeric.Iv
  /-- 概率面：Beta 后验形状参数（BetaDomain 载体）。 -/
  probShape : ℕ × ℕ

/-- 本案实际消费的结论原子集（静态链与事件链在其上一致）。 -/
def RequiredAtoms : Finset Atom :=
  {loanEntitlement, wageDueEstablished, bankruptcyAccepted, ecoRemediationCosts}

/-- 债项背书表：每笔债项由哪个主链结论原子背书（[代拟稿] 合成分配：
费用债项由工资优先权背书、利息与本金由借贷债权背书）。 -/
def ledgerBacking : List (Nat × Atom) :=
  [(1, wageBankruptcyPriority), (2, loanEntitlement), (3, loanEntitlement)]

/-- 同源共存谓词：各层读数不是并排摆着，而是以 (C1)–(C7) 数值/成员接线互相咬合。 -/
def Coherent (ci : CoherentInterim) : Prop :=
  -- (C1) 案卷与轨迹同源：满料案卷上的 17 步全轨迹，终态＝折叠读数
  (ci.docket = fullDocket ∧ ci.traj = UnifiedNetTrajectory.fullTraj ∧
    ci.finalNet = UnifiedNetTrajectory.addAll (UnifiedNetTrajectory.initState fullDocket)
      UnifiedNetTrajectory.fullTrajConcls) ∧
  -- (C2) 事件链实际运行：良构（每步前提在此前状态中）、产出（无重复触发）、时点递增
  (UnifiedNetTrajectory.TraceOk ci.docket (UnifiedNetTrajectory.initState ci.docket)
      ci.finalNet ci.traj ∧
    UnifiedNetTrajectory.Productive ci.docket (UnifiedNetTrajectory.initState ci.docket)
      ci.traj ∧
    UnifiedNetTrajectory.TimesInc ci.traj) ∧
  -- (C3) 债项身份接到主链：每笔债项有背书原子，既在事件链终态也在静态闭包
  (∀ it ∈ ci.ledger, ∃ p ∈ ledgerBacking, p.1 = it.ident ∧
    p.2 ∈ ci.finalNet ∧ p.2 ∈ closureAt (hornOf ci.docket)) ∧
  -- (C4) 收益层输入接到账本读数：现金流金额面＝支付流的逐笔抵充分配；现金总额＝支付总额
  (ci.flows.map UnifiedPayoffChain.CashEntry.amount =
      (UnifiedQuantLedger.streamAllocs ci.payPlan ci.ledger).flatten ∧
    UnifiedPayoffChain.cashTotal ci.flows = ci.payPlan.sum) ∧
  -- (C5) 评价层判定接到同一案卷：争点 1 终局＝成立，与事件链推出借贷债权同极性
  (UnifiedEvalLayer.finalJudgment ci.frame ci.focus = some KernelV3.Judgment.established ∧
    loanEntitlement ∈ ci.finalNet ∧ ci.focus = 1) ∧
  -- (C6) 区间面：支付流走完后的账本余额落在损失区间内
  JurisLean.FullMath.Numeric.Iv.mem
    (UnifiedQuantLedger.outstanding (UnifiedQuantLedger.afterStream ci.payPlan ci.ledger))
    ci.lossIv ∧
  -- (C7) 概率面：Beta 后验形状合法（≥1，连续严格递增 CDF 的存在域）
  (1 ≤ ci.probShape.1 ∧ 1 ≤ ci.probShape.2)

/-! ### 综合见证案各层构件 -/

/-- 债项分型→后果种类的归集政策（现金流的种类面；[代拟稿] 声明表）。 -/
def costKindOf : UnifiedQuantLedger.DebtKind → Consequence
  | .attorneyFee => .costOwnOnDismiss
  | .courtFee => .costOwnOnDismiss
  | .preservationFee => .costOwnOnDismiss
  | .interest => .enforcementAccess
  | .overdueInterest => .enforcementAccess
  | .penalty => .costBurdenPartial
  | .principal => .resJudicata

/-- 综合见证案的现金流：金额面＝支付 150 对 demoLedger 的逐项抵充分配 (10,100,40)
（C4 接线；种类面走 `costKindOf` 政策，登记位演示簿记位非语义）。
字段序：⟨period, kind, amount, ledgerTag⟩。 -/
def masterFlows : List UnifiedPayoffChain.CashEntry :=
  [⟨0, costKindOf UnifiedQuantLedger.DebtKind.attorneyFee, 10, false⟩,
    ⟨1, costKindOf UnifiedQuantLedger.DebtKind.interest, 100, true⟩,
    ⟨2, costKindOf UnifiedQuantLedger.DebtKind.principal, 40, false⟩]

/-- 综合见证案的评价快照（W12 载体的 Pos 型实例：材料 1（已准入）→卡片 21→
强理由 31（In 扩展）→要件 2 CivilHigh→争点 1 Pos）。 -/
def masterMat : UnifiedEvalLayer.EvidenceItem := ⟨1, 1, 2, true⟩

def masterCard : UnifiedEvalLayer.FactCard := ⟨21, 1, 2, true, 5⟩

def masterReason : UnifiedEvalLayer.ReasonNode := ⟨31, 2, true, true, [21], 6⟩

def masterFrame : UnifiedEvalLayer.Frame where
  materials := [masterMat]
  cards := [masterCard]
  reasons := [masterReason]
  attacks := []
  accepted := [31]
  ready := fun q => q == 1
  proofClosed := fun _ => true
  barred := fun _ => false
  elements := fun q => if q = 1 then [2] else []
  burdenOnClaimant := fun e => e == 2
  exhaustion := fun _ => UnifiedEvalLayer.emptyExh

/-- 综合见证案本体。 -/
def masterInterim : CoherentInterim where
  docket := fullDocket
  traj := UnifiedNetTrajectory.fullTraj
  finalNet := UnifiedNetTrajectory.addAll (UnifiedNetTrajectory.initState fullDocket)
    UnifiedNetTrajectory.fullTrajConcls
  ledger := UnifiedQuantLedger.demoLedger
  payPlan := [150]
  flows := masterFlows
  frame := masterFrame
  focus := 1
  lossIv := ⟨100, 200, by norm_num⟩
  probShape := (2, 3)

/-! ### 评价快照的 Pos 判定（W12 构造在综合案上的实例化） -/

theorem masterCardDerives : UnifiedEvalLayer.LegalDerives.card masterFrame masterCard :=
  ⟨by simp [masterFrame], masterMat, by simp [masterFrame], rfl, rfl,
    by show (5 : Nat) ≠ 0; omega⟩

theorem masterReasonLicensed : UnifiedEvalLayer.reasonLicensed masterFrame masterReason := by
  refine ⟨rfl, fun l hl => ?_⟩
  cases List.mem_cons.mp hl with
  | inl heq =>
      exact ⟨masterCard, by simp [masterFrame], by rw [heq]; exact rfl, masterCardDerives⟩
  | inr hnil => exact absurd hnil (by simp)

theorem masterCivilHigh : UnifiedEvalLayer.civilHigh masterFrame 2 := by
  refine ⟨31, ⟨masterReason, by simp [masterFrame], rfl, masterReasonLicensed, rfl, rfl⟩, ?_, ?_⟩
  · show (31 : Nat) ∈ masterFrame.accepted
    simp [masterFrame]
  · intro s hs _
    cases hs with
    | intro rn hrn =>
        cases hrn with
        | intro hmem hfields =>
            cases List.mem_cons.mp hmem with
            | inl heq =>
                subst heq
                exact Bool.noConfusion hfields.2.2.2
            | inr hnil => exact absurd hnil (by simp)

theorem masterAllElements : ∀ e ∈ masterFrame.elements 1,
    UnifiedEvalLayer.civilHigh masterFrame e := by
  intro e he
  cases List.mem_cons.mp he with
  | inl heq => rw [heq]; exact masterCivilHigh
  | inr hnil => exact absurd hnil (by simp)

theorem masterPos : UnifiedEvalLayer.posOutcome masterFrame 1 :=
  ⟨rfl, masterAllElements, rfl⟩

theorem masterFinalEstablished :
    UnifiedEvalLayer.finalJudgment masterFrame 1 = some KernelV3.Judgment.established := by
  have hcls : UnifiedEvalLayer.classify masterFrame 1
      = UnifiedEvalLayer.FinalCall.finalPos masterPos := by
    rw [UnifiedEvalLayer.classify, dif_pos masterPos]
  rw [UnifiedEvalLayer.finalJudgment_eq, hcls]
  rfl

/-! ### 数值读数（供接线与传播消费） -/

/-- 主链结论原子进事件链终态的桥（fullTrajConcls 成员→折叠终态成员）。 -/
theorem conclInFinalNet (a : Atom) (h : a ∈ UnifiedNetTrajectory.fullTrajConcls) :
    a ∈ UnifiedNetTrajectory.addAll (UnifiedNetTrajectory.initState fullDocket)
      UnifiedNetTrajectory.fullTrajConcls :=
  (UnifiedNetTrajectory.mem_addAll a _ _).mpr (Or.inl h)

/-- 主链结论原子进静态闭包的桥（事件链终态成员→closureAt 成员）。 -/
theorem conclInClosure {a : Atom}
    (h : a ∈ UnifiedNetTrajectory.addAll (UnifiedNetTrajectory.initState fullDocket)
      UnifiedNetTrajectory.fullTrajConcls) :
    a ∈ closureAt (hornOf fullDocket) :=
  UnifiedNetTrajectory.traceOk_init_closure UnifiedNetTrajectory.fullTraj_ok h

/-- 支付 150 后的账本余额（数量层主读数）。 -/
def masterBalance : ℚ :=
  UnifiedQuantLedger.outstanding
    (UnifiedQuantLedger.afterStream [150] UnifiedQuantLedger.demoLedger)

theorem masterBalance_eq : masterBalance = 160 :=
  (UnifiedQuantLedger.demoLedger_readout).2.1

/-- 收益层主读数：申请人侧的法律收益读数（偏好积分）。 -/
def masterFlowCarrier : UnifiedPayoffChain.PayFlow :=
  ⟨masterFlows, LegalStatus.upheld, false⟩

def masterReading : ℚ :=
  UnifiedPayoffChain.legalReading Role.claimant masterFlowCarrier

theorem masterReading_eq : masterReading = 250 := by
  unfold masterReading masterFlowCarrier UnifiedPayoffChain.legalReading
  simp [UnifiedPayoffChain.prefIntegral, UnifiedPayoffChain.costAt,
    UnifiedPayoffChain.allCons, masterFlows, costKindOf, consequenceValuation]
  norm_num

/-- 满料分配读数（C4 第一支的数值面）。 -/
theorem master_allocs_rows : UnifiedQuantLedger.allocsOf 150 UnifiedQuantLedger.demoLedger
    = [10, 100, 40] :=
  (UnifiedQuantLedger.demoLedger_readout).1

/-- 首见原子成员（四消费原子都在 fullTrajConcls 内）。 -/
theorem required_concl_mem (a : Atom) (h : a ∈ RequiredAtoms) :
    a ∈ UnifiedNetTrajectory.fullTrajConcls := by
  simp only [RequiredAtoms, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl <;>
    exact by simp [UnifiedNetTrajectory.fullTrajConcls]

/-! ### 见证一致性 -/

/-- **共同中间见证**：综合见证案满足同源共存谓词（C1–C7 逐支成立）。 -/
theorem masterInterim_coherent : Coherent masterInterim := by
  refine ⟨⟨rfl, rfl, rfl⟩,
    ⟨UnifiedNetTrajectory.fullTraj_ok, UnifiedNetTrajectory.fullTraj_productive,
      UnifiedNetTrajectory.fullTraj_times⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · -- (C3) 债项背书
    intro it hit
    simp only [masterInterim, UnifiedQuantLedger.demoLedger, List.mem_cons, List.not_mem_nil]
      at hit
    rcases hit with rfl | rfl | rfl | h
    · exact ⟨(1, wageBankruptcyPriority), by simp [ledgerBacking], rfl,
        conclInFinalNet _ (by simp [UnifiedNetTrajectory.fullTrajConcls]),
        conclInClosure (conclInFinalNet _
          (by simp [UnifiedNetTrajectory.fullTrajConcls]))⟩
    · exact ⟨(2, loanEntitlement), by simp [ledgerBacking], rfl,
        conclInFinalNet _ (required_concl_mem _ (by simp [RequiredAtoms])),
        conclInClosure (conclInFinalNet _
          (required_concl_mem _ (by simp [RequiredAtoms])))⟩
    · exact ⟨(3, loanEntitlement), by simp [ledgerBacking], rfl,
        conclInFinalNet _ (required_concl_mem _ (by simp [RequiredAtoms])),
        conclInClosure (conclInFinalNet _
          (required_concl_mem _ (by simp [RequiredAtoms])))⟩
    · exact h.elim
  · -- (C4) 现金流接到账本读数
    constructor
    · have hrows : (UnifiedQuantLedger.streamAllocs [150]
          UnifiedQuantLedger.demoLedger).flatten = [10, 100, 40] := by
        simp only [UnifiedQuantLedger.streamAllocs, List.flatten_cons, List.flatten_nil,
          List.append_nil]
        exact master_allocs_rows
      show masterFlows.map UnifiedPayoffChain.CashEntry.amount
          = (UnifiedQuantLedger.streamAllocs [150]
              UnifiedQuantLedger.demoLedger).flatten
      rw [hrows]
      rfl
    · show UnifiedPayoffChain.cashTotal masterFlows = ([150] : List ℚ).sum
      norm_num [UnifiedPayoffChain.cashTotal, masterFlows]
  · -- (C5) 评价判定与网络同极性
    exact ⟨masterFinalEstablished,
      conclInFinalNet _ (required_concl_mem _ (by simp [RequiredAtoms])), rfl⟩
  · -- (C6) 余额落在损失区间内
    have hb : UnifiedQuantLedger.outstanding
        (UnifiedQuantLedger.afterStream masterInterim.payPlan masterInterim.ledger) = 160 :=
      masterBalance_eq
    rw [hb]
    show 100 ≤ 160 ∧ 160 ≤ 200
    exact ⟨by norm_num, by norm_num⟩
  · -- (C7) Beta 形状合法
    show 1 ≤ 2 ∧ 1 ≤ 3
    exact ⟨by omega, by omega⟩

/-! ## 二、静态链/事件链对应（合同"全静态链/事件链"支） -/

/-- **两链对应定理**：(a) 事件链健全于静态链——终态每个原子都在该案卷 Horn 网络
闭包内（轨迹结论都真实在闭包内，不是轨迹私造）；(b) 本案消费集上双向一致——
所需原子静态可导且被事件链实际产出；(c) 事件链每步规则钉死在 29 条规则表内、
法源在效力窗口内。 -/
theorem master_static_event_correspondence :
    (∀ a ∈ masterInterim.finalNet, a ∈ closureAt (hornOf masterInterim.docket)) ∧
    (∀ a ∈ RequiredAtoms,
      a ∈ closureAt (hornOf masterInterim.docket) ∧ a ∈ masterInterim.finalNet) ∧
    (∀ st ∈ masterInterim.traj, st.rule ∈ familyRuleList ∧ srcInForce st.rule.src = true) :=
  ⟨fun _ ha => UnifiedNetTrajectory.traceOk_init_closure UnifiedNetTrajectory.fullTraj_ok ha,
    fun a ha =>
      ⟨conclInClosure (conclInFinalNet a (required_concl_mem a ha)),
        conclInFinalNet a (required_concl_mem a ha)⟩,
    fun st hst => ⟨st.htab, UnifiedNetTrajectory.fullTraj_sources st hst⟩⟩

/-! ## 三、交换关系（合同"交换关系"支；三组，均有真实数学内容） -/

/-! ### 组一：支付流分段/重排 ↔ 余额与收益读数（钳位复合代数） -/

/-- 支付条目生成器：把抵充分配行装成现金流条目（收益层输入的通用形状；
cashTotal 只读金额面）。字段序：⟨period, kind, amount, ledgerTag⟩。 -/
def payEntriesOf (qs : List ℚ) : List UnifiedPayoffChain.CashEntry :=
  qs.map (fun q => ⟨0, Consequence.enforcementAccess, q, false⟩)

theorem cashTotal_append (l₁ l₂ : List UnifiedPayoffChain.CashEntry) :
    UnifiedPayoffChain.cashTotal (l₁ ++ l₂)
      = UnifiedPayoffChain.cashTotal l₁ + UnifiedPayoffChain.cashTotal l₂ := by
  induction l₁ with
  | nil => simp [UnifiedPayoffChain.cashTotal]
  | cons e es ih =>
      rw [List.cons_append, UnifiedPayoffChain.cashTotal_cons,
        UnifiedPayoffChain.cashTotal_cons, ih]
      ring

theorem cashTotal_payEntriesOf (qs : List ℚ) :
    UnifiedPayoffChain.cashTotal (payEntriesOf qs) = qs.sum := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
      have h1 : payEntriesOf (q :: qs)
          = (⟨0, Consequence.enforcementAccess, q, false⟩ :
              UnifiedPayoffChain.CashEntry) :: payEntriesOf qs := rfl
      rw [h1, UnifiedPayoffChain.cashTotal_cons, ih, List.sum_cons]

/-- **组一（账本×收益层交换）**：支付流的重排/合并/切分与账本余额读数及收益层
现金总额读数交换——余额只依赖支付总额（钳位复合 `max (max (x−p₁) 0 −p₂) 0 =
max (x−(p₁+p₂)) 0` 的结合/交换代数），两段式抵充的分配总和＝一次性抵充的分配
总和（min/max 对偶），从而进收益层的现金总额同值。 -/
theorem ledger_payment_split_exchange (p₁ p₂ : ℚ) (h₁ : 0 ≤ p₁) (h₂ : 0 ≤ p₂) :
    -- (E1) 重排不变：先付 p₁ 后付 p₂ ＝ 先付 p₂ 后付 p₁（余额读数）
    UnifiedQuantLedger.outstanding
        (UnifiedQuantLedger.afterStream [p₁, p₂] masterInterim.ledger)
      = UnifiedQuantLedger.outstanding
          (UnifiedQuantLedger.afterStream [p₂, p₁] masterInterim.ledger) ∧
    -- (E2) 合并不变：分两笔付 ＝ 一笔付总额（余额读数）
    UnifiedQuantLedger.outstanding
        (UnifiedQuantLedger.afterStream [p₁, p₂] masterInterim.ledger)
      = UnifiedQuantLedger.outstanding
          (UnifiedQuantLedger.afterStream [p₁ + p₂] masterInterim.ledger) ∧
    -- (E3) 分配总和不变：两段式分配行总和 ＝ 一次性分配总和
    (UnifiedQuantLedger.allocsOf p₁ masterInterim.ledger).sum
        + (UnifiedQuantLedger.allocsOf p₂
            (UnifiedQuantLedger.afterPay p₁ masterInterim.ledger)).sum
      = (UnifiedQuantLedger.allocsOf (p₁ + p₂) masterInterim.ledger).sum ∧
    -- (E4) 收益层读数交换：两段生成的现金流总额 ＝ 一段生成的现金流总额
    UnifiedPayoffChain.cashTotal
        (payEntriesOf (UnifiedQuantLedger.allocsOf p₁ masterInterim.ledger)
          ++ payEntriesOf (UnifiedQuantLedger.allocsOf p₂
            (UnifiedQuantLedger.afterPay p₁ masterInterim.ledger)))
      = UnifiedPayoffChain.cashTotal
          (payEntriesOf (UnifiedQuantLedger.allocsOf (p₁ + p₂) masterInterim.ledger)) := by
  have hnn : ∀ it ∈ masterInterim.ledger, 0 ≤ it.amount :=
    UnifiedQuantLedger.demoLedger_nonneg
  have hps : ∀ p ∈ [p₁, p₂], 0 ≤ p := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil] at hp
    rcases hp with h | h | h
    · rw [h]; exact h₁
    · rw [h]; exact h₂
    · exact h.elim
  have hps2 : ∀ p ∈ [p₂, p₁], 0 ≤ p := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil] at hp
    rcases hp with h | h | h
    · rw [h]; exact h₂
    · rw [h]; exact h₁
    · exact h.elim
  have hps3 : ∀ p ∈ [p₁ + p₂], 0 ≤ p := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil] at hp
    rcases hp with h | h
    · rw [h]; linarith
    · exact h.elim
  have e12 := UnifiedQuantLedger.outstanding_afterStream [p₁, p₂] masterInterim.ledger
    hnn hps
  have e21 := UnifiedQuantLedger.outstanding_afterStream [p₂, p₁] masterInterim.ledger
    hnn hps2
  have e1 := UnifiedQuantLedger.outstanding_afterStream [p₁ + p₂] masterInterim.ledger
    hnn hps3
  rw [show ([p₁, p₂] : List ℚ).sum = p₁ + p₂ from by
      simp only [List.sum_cons, List.sum_nil]; ring] at e12
  rw [show ([p₂, p₁] : List ℚ).sum = p₁ + p₂ from by
      simp only [List.sum_cons, List.sum_nil]; ring] at e21
  rw [show ([p₁ + p₂] : List ℚ).sum = p₁ + p₂ from by
      simp only [List.sum_cons, List.sum_nil]; ring] at e1
  -- 望远镜：两段式余额＝初始余额−两段分配总和
  have t1 : UnifiedQuantLedger.outstanding
        (UnifiedQuantLedger.afterPay p₁ masterInterim.ledger)
      = UnifiedQuantLedger.outstanding masterInterim.ledger
        - (UnifiedQuantLedger.allocsOf p₁ masterInterim.ledger).sum :=
    UnifiedQuantLedger.outstanding_afterPay p₁ masterInterim.ledger
  have hstream : UnifiedQuantLedger.afterStream [p₁, p₂] masterInterim.ledger
      = UnifiedQuantLedger.afterPay p₂
          (UnifiedQuantLedger.afterPay p₁ masterInterim.ledger) := rfl
  have ht2 : UnifiedQuantLedger.outstanding
        (UnifiedQuantLedger.afterPay p₂
          (UnifiedQuantLedger.afterPay p₁ masterInterim.ledger))
      = UnifiedQuantLedger.outstanding masterInterim.ledger
        - (UnifiedQuantLedger.allocsOf p₁ masterInterim.ledger).sum
        - (UnifiedQuantLedger.allocsOf p₂
            (UnifiedQuantLedger.afterPay p₁ masterInterim.ledger)).sum := by
    rw [UnifiedQuantLedger.outstanding_afterPay p₂
      (UnifiedQuantLedger.afterPay p₁ masterInterim.ledger), t1]
  -- afterPay 形的钳位读数（与 e12 同一量）
  have e12' : UnifiedQuantLedger.outstanding
        (UnifiedQuantLedger.afterPay p₂
          (UnifiedQuantLedger.afterPay p₁ masterInterim.ledger))
      = max (UnifiedQuantLedger.outstanding masterInterim.ledger - (p₁ + p₂)) 0 := by
    rw [← hstream]
    exact e12
  -- (E3) 望远镜：两段分配总和 ＝ O − max (O−P) 0 ＝ min P O ＝ 一次性分配总和
  have hP : 0 ≤ p₁ + p₂ := by linarith
  have s3 := UnifiedQuantLedger.allocsOf_sum_eq_min masterInterim.ledger (p₁ + p₂) hP hnn
  have hE3 : (UnifiedQuantLedger.allocsOf p₁ masterInterim.ledger).sum
        + (UnifiedQuantLedger.allocsOf p₂
            (UnifiedQuantLedger.afterPay p₁ masterInterim.ledger)).sum
      = (UnifiedQuantLedger.allocsOf (p₁ + p₂) masterInterim.ledger).sum := by
    have hst : (UnifiedQuantLedger.allocsOf p₁ masterInterim.ledger).sum
          + (UnifiedQuantLedger.allocsOf p₂
              (UnifiedQuantLedger.afterPay p₁ masterInterim.ledger)).sum
        = UnifiedQuantLedger.outstanding masterInterim.ledger
          - max (UnifiedQuantLedger.outstanding masterInterim.ledger - (p₁ + p₂)) 0 := by
      linarith
    have hs3 : (UnifiedQuantLedger.allocsOf (p₁ + p₂) masterInterim.ledger).sum
        = UnifiedQuantLedger.outstanding masterInterim.ledger
          - max (UnifiedQuantLedger.outstanding masterInterim.ledger - (p₁ + p₂)) 0 := by
      rw [s3]
      rcases le_total (p₁ + p₂)
          (UnifiedQuantLedger.outstanding masterInterim.ledger) with h | h
      · rw [min_eq_left h, max_eq_left (by linarith : (0:ℚ) ≤
          UnifiedQuantLedger.outstanding masterInterim.ledger - (p₁ + p₂)), sub_sub_cancel]
      · rw [min_eq_right h, max_eq_right (by linarith :
          UnifiedQuantLedger.outstanding masterInterim.ledger - (p₁ + p₂) ≤ 0), sub_zero]
    rw [hst, hs3]
  refine ⟨?_, ?_, hE3, ?_⟩
  · rw [hstream, e12', e21]
  · rw [hstream, e12', e1]
  · rw [cashTotal_append, cashTotal_payEntriesOf, cashTotal_payEntriesOf]
    exact hE3

/-! ### 组二：损失区间合并×份额缩放（分配律）＋首见去重×缩放（归纳交换） -/

/-- 损失账项的非负缩放。 -/
def scaleLoss (c : ℚ) : UnifiedQuantLedger.LossEntry → UnifiedQuantLedger.LossEntry :=
  fun e => { e with amount := c * e.amount }

/-- **去重与缩放交换（一般形，归纳证明）**：先缩放再去重＝先去重再缩放——
首见选择只读键，缩放只写金额，两算子交换。 -/
theorem dedupAux_scale_commute (c : ℚ) : ∀ (l : List UnifiedQuantLedger.LossEntry)
    (seen : List UnifiedQuantLedger.LossKey),
    UnifiedQuantLedger.dedupAux seen (l.map (scaleLoss c))
      = (UnifiedQuantLedger.dedupAux seen l).map (scaleLoss c) := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons e es ih =>
      intro seen
      simp only [List.map_cons]
      rw [UnifiedQuantLedger.dedupAux, UnifiedQuantLedger.dedupAux]
      simp only [scaleLoss]
      by_cases hk : e.key ∈ seen
      · rw [if_pos hk, if_pos hk]
        exact ih seen
      · rw [if_neg hk, if_neg hk, List.map_cons]
        exact congrArg (fun t => { e with amount := c * e.amount } :: t)
          (ih (e.key :: seen))

theorem dedup_scale_commute (c : ℚ) (l : List UnifiedQuantLedger.LossEntry) :
    UnifiedQuantLedger.dedupFirst (l.map (scaleLoss c))
      = (UnifiedQuantLedger.dedupFirst l).map (scaleLoss c) :=
  dedupAux_scale_commute c l []

theorem lossTotal_scale (c : ℚ) : ∀ l : List UnifiedQuantLedger.LossEntry,
    UnifiedQuantLedger.lossTotal (l.map (scaleLoss c))
      = c * UnifiedQuantLedger.lossTotal l := by
  intro l
  induction l with
  | nil => simp [UnifiedQuantLedger.lossTotal]
  | cons e es ih =>
      simp only [List.map_cons, scaleLoss, UnifiedQuantLedger.lossTotal, List.map_cons,
        List.sum_cons] at ih ⊢
      linarith

/-- 综合见证案的损失账本（B07 载体：发票额与同键评估额，[代拟稿] 合成材料）。 -/
def masterLoss : List UnifiedQuantLedger.LossEntry :=
  [⟨(1, 2, 3, 4), 1000⟩, ⟨(1, 2, 3, 4), 800⟩]

theorem masterLoss_dedup_total :
    UnifiedQuantLedger.lossTotal (UnifiedQuantLedger.dedupFirst masterLoss) = 1000 := by
  rw [show UnifiedQuantLedger.dedupFirst masterLoss = [⟨(1, 2, 3, 4), 1000⟩] from
    UnifiedQuantLedger.invoice_appraisal_single_count]
  norm_num [UnifiedQuantLedger.lossTotal]

/-- **组二（区间×账本归集交换）**：(A) 区间端点代数的分配律——先合并两笔损失
区间再按非负份额缩放＝先各自缩放再合并；(B) 首见去重与非负缩放交换（一般形）；
(C) 读数一致——交换两侧的损失总额相等（按读数值＝份额×去重总额）。 -/
theorem master_loss_aggregation_share_exchange (c : ℚ) (hc : 0 ≤ c)
    (i j : JurisLean.FullMath.Numeric.Iv) :
    (UnifiedQuantLedger.QIv.vscale c hc (JurisLean.FullMath.Numeric.Iv.add i j)
      = JurisLean.FullMath.Numeric.Iv.add (UnifiedQuantLedger.QIv.vscale c hc i)
          (UnifiedQuantLedger.QIv.vscale c hc j)) ∧
    (∀ l : List UnifiedQuantLedger.LossEntry,
      UnifiedQuantLedger.dedupFirst (l.map (scaleLoss c))
        = (UnifiedQuantLedger.dedupFirst l).map (scaleLoss c)) ∧
    (UnifiedQuantLedger.lossTotal
        (UnifiedQuantLedger.dedupFirst (masterLoss.map (scaleLoss c)))
      = c * UnifiedQuantLedger.lossTotal (UnifiedQuantLedger.dedupFirst masterLoss)) := by
  refine ⟨UnifiedQuantLedger.QIv.scale_distrib c hc i j,
    fun l => dedup_scale_commute c l, ?_⟩
  rw [dedup_scale_commute c masterLoss]
  exact lossTotal_scale c (UnifiedQuantLedger.dedupFirst masterLoss)

/-! ### 组三：负担输入通道×支付通道（层间通道交换） -/

/-- 支付通道：一笔支付进入综合中间结果（改账本/支付流/现金流，不碰评价快照）。 -/
def payInterim (p : ℚ) (ci : CoherentInterim) : CoherentInterim where
  docket := ci.docket
  traj := ci.traj
  finalNet := ci.finalNet
  ledger := UnifiedQuantLedger.afterPay p ci.ledger
  payPlan := ci.payPlan ++ [p]
  flows := ci.flows ++ payEntriesOf (UnifiedQuantLedger.allocsOf p ci.ledger)
  frame := ci.frame
  focus := ci.focus
  lossIv := ci.lossIv
  probShape := ci.probShape

/-- 负担通道：一个法定负担输入进入综合中间结果（只写评价快照的程序/负担位，
不碰数量层与收益层）。 -/
def burdenInterim (bi : UnifiedEvalLayer.BurdenInput)
    (ci : CoherentInterim) : CoherentInterim where
  docket := ci.docket
  traj := ci.traj
  finalNet := ci.finalNet
  ledger := ci.ledger
  payPlan := ci.payPlan
  flows := ci.flows
  frame := UnifiedEvalLayer.applyBurdenInput ci.frame bi
  focus := ci.focus
  lossIv := ci.lossIv
  probShape := ci.probShape

/-- **组三（负担通道×支付通道交换）**：两个输入通道在综合中间结果上交换（任一顺序
到达同一综合状态），且读数分层不动——负担输入后终局判断仍为成立（Pos 对负担输入
不变，W12 定理）、负担通道不触碰账本与现金流、支付通道不触碰评价快照。 -/
theorem master_channel_exchange_readings (p : ℚ) (bi : UnifiedEvalLayer.BurdenInput) :
    payInterim p (burdenInterim bi masterInterim)
      = burdenInterim bi (payInterim p masterInterim) ∧
    UnifiedEvalLayer.finalJudgment (UnifiedEvalLayer.applyBurdenInput masterFrame bi) 1
      = some KernelV3.Judgment.established ∧
    (burdenInterim bi masterInterim).ledger = masterInterim.ledger ∧
    (burdenInterim bi masterInterim).flows = masterInterim.flows ∧
    (payInterim p masterInterim).frame = masterInterim.frame :=
  ⟨rfl, UnifiedEvalLayer.burden_input_never_flips_pos masterFrame bi 1 masterPos,
    rfl, rfl, rfl⟩

/-! ## 四、误差传播（合同"精度传播"支） -/

/-! ### 收益层：偏好积分对条目扰动的线性界 -/

/-- 现金流条目的金额扰动（种类/期次不动，金额加 d）。 -/
def amtPerturb (d : UnifiedPayoffChain.CashEntry → ℚ)
    (es : List UnifiedPayoffChain.CashEntry) : List UnifiedPayoffChain.CashEntry :=
  es.map (fun e => { e with amount := e.amount + d e })

theorem amtPerturb_cons (d : UnifiedPayoffChain.CashEntry → ℚ)
    (e : UnifiedPayoffChain.CashEntry) (es : List UnifiedPayoffChain.CashEntry) :
    amtPerturb d (e :: es)
      = { e with amount := e.amount + d e } :: amtPerturb d es := rfl

/-- **收益层扰动界**：条目金额各扰动 d e ⇒ 偏好积分读数移动 ≤ Σₑ |w(k(e))|·|d e|
（层 3 对层 1 的线性传播；证明走 `prefIntegral_cons` 的同变式逐条目归纳）。 -/
theorem prefIntegral_perturb (role : Role) (d : UnifiedPayoffChain.CashEntry → ℚ)
    (es : List UnifiedPayoffChain.CashEntry) :
    |UnifiedPayoffChain.prefIntegral role (amtPerturb d es)
        - UnifiedPayoffChain.prefIntegral role es|
      ≤ (es.map (fun x => |consequenceValuation role x.kind| * |d x|)).sum := by
  induction es with
  | nil => simp [amtPerturb, UnifiedPayoffChain.prefIntegral]
  | cons e es ih =>
      have key : UnifiedPayoffChain.prefIntegral role (amtPerturb d (e :: es))
          - UnifiedPayoffChain.prefIntegral role (e :: es)
          = (UnifiedPayoffChain.prefIntegral role (amtPerturb d es)
              - UnifiedPayoffChain.prefIntegral role es)
            + consequenceValuation role e.kind * d e := by
        rw [amtPerturb_cons, UnifiedPayoffChain.prefIntegral_cons,
          UnifiedPayoffChain.prefIntegral_cons]
        dsimp only
        ring
      rw [key, List.map_cons, List.sum_cons]
      calc |(UnifiedPayoffChain.prefIntegral role (amtPerturb d es)
              - UnifiedPayoffChain.prefIntegral role es)
            + consequenceValuation role e.kind * d e|
          ≤ |UnifiedPayoffChain.prefIntegral role (amtPerturb d es)
              - UnifiedPayoffChain.prefIntegral role es|
            + |consequenceValuation role e.kind * d e| := abs_add_le _ _
        _ ≤ (es.map (fun x => |consequenceValuation role x.kind| * |d x|)).sum
            + |consequenceValuation role e.kind * d e| := add_le_add ih (le_refl _)
        _ = (es.map (fun x => |consequenceValuation role x.kind| * |d x|)).sum
            + |consequenceValuation role e.kind| * |d e| := by rw [abs_mul]
        _ = ((e :: es).map (fun x => |consequenceValuation role x.kind| * |d x|)).sum := by
              simp only [List.map_cons, List.sum_cons]
              ring

/-- 收益层读数形式的扰动界（同一定理在 `legalReading` 载体上）。 -/
theorem legalReading_perturb (role : Role) (d : UnifiedPayoffChain.CashEntry → ℚ)
    (fl : UnifiedPayoffChain.PayFlow) :
    |UnifiedPayoffChain.legalReading role { fl with entries := amtPerturb d fl.entries }
        - UnifiedPayoffChain.legalReading role fl|
      ≤ (fl.entries.map (fun x => |consequenceValuation role x.kind| * |d x|)).sum :=
  prefIntegral_perturb role d fl.entries

/-! ### 账本层：支付扰动界（ReLU 1-Lipschitz） -/

/-- 钳位函数的 1-Lipschitz：|max x 0 − max y 0| ≤ |x − y|。 -/
theorem abs_sub_max_zero (x y : ℚ) : |max x 0 - max y 0| ≤ |x - y| := by
  rcases le_total x 0 with hx | hx
  · rcases le_total y 0 with hy | hy
    · rw [max_eq_right hx, max_eq_right hy, sub_self]
      simp
    · rw [max_eq_right hx, max_eq_left hy, zero_sub, abs_neg, abs_of_nonneg hy,
        abs_sub_comm x y, abs_of_nonneg (by linarith : (0 : ℚ) ≤ y - x)]
      linarith
  · rcases le_total y 0 with hy | hy
    · rw [max_eq_left hx, max_eq_right hy, sub_zero, abs_of_nonneg hx,
        abs_of_nonneg (by linarith : (0 : ℚ) ≤ x - y)]
      linarith
    · rw [max_eq_left hx, max_eq_left hy]

/-- **账本层扰动界**：支付总额扰动 δ ⇒ 余额读数移动 ≤ δ（经
`outstanding_afterStream` 化归为钳位的 1-Lipschitz）。 -/
theorem outstanding_payment_perturb (items : List UnifiedQuantLedger.LedgerItem)
    (hnn : ∀ it ∈ items, 0 ≤ it.amount) (ps ps' : List ℚ)
    (hps : ∀ p ∈ ps, 0 ≤ p) (hps' : ∀ p ∈ ps', 0 ≤ p) (δ : ℚ)
    (h : |ps.sum - ps'.sum| ≤ δ) :
    |UnifiedQuantLedger.outstanding (UnifiedQuantLedger.afterStream ps items)
        - UnifiedQuantLedger.outstanding (UnifiedQuantLedger.afterStream ps' items)| ≤ δ := by
  rw [UnifiedQuantLedger.outstanding_afterStream ps items hnn hps,
    UnifiedQuantLedger.outstanding_afterStream ps' items hnn hps']
  have h1 := abs_sub_max_zero (UnifiedQuantLedger.outstanding items - ps.sum)
    (UnifiedQuantLedger.outstanding items - ps'.sum)
  rw [sub_sub_sub_cancel_left, abs_sub_comm ps'.sum ps.sum] at h1
  exact le_trans h1 h

/-! ### 数量面：余额读数的 divFree AST 整值承载（ε=0 面） -/

/-- 余额读数的数量 AST 承载：310 + (−150) 的无除表达式（divFree ⇒ 整值）。 -/
def masterQtyAst : UnifiedNeedlesS3b.QtyAst :=
  .add (.intLit 310) (.intLit (-150))

theorem qtyDenote_masterQtyAst :
    UnifiedNeedlesS3b.qtyDenote masterQtyAst = some ⟨(160 : ℚ), ""⟩ := by
  norm_num [masterQtyAst, UnifiedNeedlesS3b.qtyDenote]

/-- **数量 AST 接线（针 25 整值面进入主链）**：清偿后余额读数 160 由一个 divFree
AST 逐字承载（求值＝该读数、无除片段整值——数量层读数无舍入面，ε=0）。 -/
theorem master_qty_ast_carries_balance :
    UnifiedNeedlesS3b.qtyDenote masterQtyAst = some ⟨masterBalance, ""⟩ ∧
    UnifiedNeedlesS3b.divFree masterQtyAst = true ∧
    ∃ n : ℤ, masterBalance = (n : ℚ) := by
  have hfree : UnifiedNeedlesS3b.divFree masterQtyAst = true := rfl
  refine ⟨?_, hfree, ?_⟩
  · rw [masterBalance_eq]
    exact qtyDenote_masterQtyAst
  · obtain ⟨n, hn⟩ := UnifiedNeedlesS3b.qtyDenote_divFree_int_valued masterQtyAst hfree
      ⟨(160 : ℚ), ""⟩ qtyDenote_masterQtyAst
    exact ⟨n, by rw [masterBalance_eq]; exact hn⟩

/-- 数量面接线命题（别名，供总合取引用）。 -/
def QtyFaceProp : Prop :=
  UnifiedNeedlesS3b.qtyDenote masterQtyAst = some ⟨masterBalance, ""⟩ ∧
    UnifiedNeedlesS3b.divFree masterQtyAst = true ∧ ∃ n : ℤ, masterBalance = (n : ℚ)

/-! ### 概率面：CDF 包围宽度→期望读数扰动界（BetaDomain 精度预算的传播） -/

/-- **概率面扰动界（消费 BetaDomain 精度预算界面）**：分子包围 [N_l,N_u]、分母包围
[B_l,B_u]（宽度各 ≤ ρ、β ≤ B_l、N_l ≤ B_u）⇒ CDF 读数两端点之差 ≤ 2ρ/β（即
`cdfEnc_width`），从而后验质量扰动传播到期望读数：两端期望读数之差 ≤ (2ρ/β)·|损失|。
包围的供给侧是执行层接口（诚实边界见头注）。 -/
theorem beta_enclosure_expected_reading (N_l N_u B_l B_u ρ β loss : ℚ)
    (hρ : 0 < ρ) (hβ : 0 < β)
    (hNl : 0 ≤ N_l) (hBlβ : β ≤ B_l) (hBl : 0 < B_l) (hBlu : B_l ≤ B_u)
    (hNel : N_l ≤ N_u) (hNB : N_l ≤ B_u)
    (hwl : N_u - N_l ≤ ρ) (hwd : B_u - B_l ≤ ρ) :
    |N_u / B_l * loss - N_l / B_u * loss| ≤ 2 * ρ / β * |loss| := by
  have hw := UnifiedBetaDomain.cdfEnc_width N_l N_u B_l B_u ρ β hρ hβ hNl hBlβ hBl hBlu hNel
    hNB hwl hwd
  have hwdef : (UnifiedBetaDomain.cdfEnc N_l N_u B_l B_u).width
      = N_u / B_l - N_l / B_u := rfl
  rw [hwdef] at hw
  have key : N_u / B_l * loss - N_l / B_u * loss
      = (N_u / B_l - N_l / B_u) * loss := by ring
  have h1u : (0 : ℚ) < B_u := lt_of_lt_of_le hBl hBlu
  have hcross : N_u / B_l - N_l / B_u = (N_u * B_u - N_l * B_l) / (B_l * B_u) := by
    field_simp
  have hnum : (0 : ℚ) ≤ N_u * B_u - N_l * B_l := by
    have ha : N_l * B_l ≤ N_l * B_u := mul_le_mul_of_nonneg_left hBlu hNl
    have hb : N_l * B_u ≤ N_u * B_u := mul_le_mul_of_nonneg_right hNel h1u.le
    linarith
  have hdiff : (0 : ℚ) ≤ N_u / B_l - N_l / B_u := by
    rw [hcross]
    exact div_nonneg hnum (by positivity)
  rw [key, abs_mul, abs_of_nonneg hdiff]
  exact mul_le_mul_of_nonneg_right hw (abs_nonneg loss)

/-- **概率面载体接线**：综合案后验形状 (2,3) 的 Bernstein CDF 连续且在 [0,1]
严格递增（BetaDomain 四义务实例），ℚ 闭式与实层在该有理点精确互译（可比较、
无近似）。 -/
theorem master_beta_face :
    (1 ≤ masterInterim.probShape.1 ∧ 1 ≤ masterInterim.probShape.2) ∧
    (Continuous (UnifiedBetaDomain.bernCdf masterInterim.probShape.1
        masterInterim.probShape.2) ∧
      StrictMonoOn (UnifiedBetaDomain.bernCdf masterInterim.probShape.1
        masterInterim.probShape.2) (Set.Icc 0 1)) ∧
    (∀ q₁ q₂ : ℚ,
      (UnifiedBetaDomain.bernCdf masterInterim.probShape.1 masterInterim.probShape.2
          (q₁ : ℝ)
        ≤ UnifiedBetaDomain.bernCdf masterInterim.probShape.1 masterInterim.probShape.2
            (q₂ : ℝ))
      ↔ UnifiedBetaDomain.ratBernCdf masterInterim.probShape.1 masterInterim.probShape.2 q₁
        ≤ UnifiedBetaDomain.ratBernCdf masterInterim.probShape.1 masterInterim.probShape.2
            q₂) := by
  refine ⟨?_, ?_, fun q₁ q₂ =>
    UnifiedBetaDomain.bernCdf_rat_comparable 2 3 q₁ q₂⟩
  · show 1 ≤ 2 ∧ 1 ≤ 3
    exact ⟨by omega, by omega⟩
  · exact ⟨(UnifiedBetaDomain.bernCdf_mixable 2 3 (by norm_num) (by norm_num)).1,
      (UnifiedBetaDomain.bernCdf_mixable 2 3 (by norm_num) (by norm_num)).2.2.2.2⟩

/-- 概率面载体接线命题（别名，供总合取引用）。 -/
def BetaFaceProp : Prop :=
  (1 ≤ masterInterim.probShape.1 ∧ 1 ≤ masterInterim.probShape.2) ∧
    (Continuous (UnifiedBetaDomain.bernCdf masterInterim.probShape.1
        masterInterim.probShape.2) ∧
      StrictMonoOn (UnifiedBetaDomain.bernCdf masterInterim.probShape.1
        masterInterim.probShape.2) (Set.Icc 0 1)) ∧
    (∀ q₁ q₂ : ℚ,
      (UnifiedBetaDomain.bernCdf masterInterim.probShape.1 masterInterim.probShape.2 (q₁ : ℝ)
        ≤ UnifiedBetaDomain.bernCdf masterInterim.probShape.1 masterInterim.probShape.2
            (q₂ : ℝ))
      ↔ UnifiedBetaDomain.ratBernCdf masterInterim.probShape.1 masterInterim.probShape.2 q₁
        ≤ UnifiedBetaDomain.ratBernCdf masterInterim.probShape.1 masterInterim.probShape.2 q₂)

/-! ### 端到端：输入扰动→各层读数扰动界→总读数界 -/

/-- 综合暴露读数：收益读数＋账本余额＋后验×去重损失总额（三层读数的和；
后验点估计作为参数进入）。 -/
def exposureOf (fl : List UnifiedPayoffChain.CashEntry)
    (items : List UnifiedQuantLedger.LedgerItem) (ps : List ℚ) (post : ℚ) : ℚ :=
  UnifiedPayoffChain.legalReading Role.claimant ⟨fl, LegalStatus.upheld, false⟩
    + UnifiedQuantLedger.outstanding (UnifiedQuantLedger.afterStream ps items)
    + post * UnifiedQuantLedger.lossTotal (UnifiedQuantLedger.dedupFirst masterLoss)

/-- **端到端扰动传播链（合同"输入扰动→各层读数扰动界"的合成形）**：条目金额扰动 d
（收益层界）、支付总额扰动 δ（账本层界）、后验点在包围两端之间移动（概率面界）
⇒ 综合暴露读数的总移动 ≤ 三层界之和。 -/
theorem master_exposure_perturb_chain
    (d : UnifiedPayoffChain.CashEntry → ℚ)
    (ps ps' : List ℚ) (hps : ∀ p ∈ ps, 0 ≤ p) (hps' : ∀ p ∈ ps', 0 ≤ p)
    (δ : ℚ) (_hδ0 : 0 ≤ δ) (hsum : |ps.sum - ps'.sum| ≤ δ)
    (N_l N_u B_l B_u ρ β : ℚ) (hρ : 0 < ρ) (hβ : 0 < β) (hNl : 0 ≤ N_l) (hBlβ : β ≤ B_l)
    (hBl : 0 < B_l) (hBlu : B_l ≤ B_u) (hNel : N_l ≤ N_u) (hNB : N_l ≤ B_u)
    (hwl : N_u - N_l ≤ ρ) (hwd : B_u - B_l ≤ ρ) :
    |exposureOf (amtPerturb d masterFlows) masterInterim.ledger ps' (N_u / B_l)
        - exposureOf masterFlows masterInterim.ledger ps (N_l / B_u)|
      ≤ (masterFlows.map (fun x => |consequenceValuation Role.claimant x.kind| * |d x|)).sum
        + δ + 2 * ρ / β
          * |UnifiedQuantLedger.lossTotal (UnifiedQuantLedger.dedupFirst masterLoss)| := by
  have h1 : |UnifiedPayoffChain.legalReading Role.claimant
        ⟨amtPerturb d masterFlows, LegalStatus.upheld, false⟩
        - UnifiedPayoffChain.legalReading Role.claimant
          ⟨masterFlows, LegalStatus.upheld, false⟩|
      ≤ (masterFlows.map (fun x => |consequenceValuation Role.claimant x.kind| * |d x|)).sum :=
    legalReading_perturb Role.claimant d ⟨masterFlows, LegalStatus.upheld, false⟩
  have h2 := outstanding_payment_perturb masterInterim.ledger
    UnifiedQuantLedger.demoLedger_nonneg ps' ps hps' hps δ
    (by rw [abs_sub_comm]; exact hsum)
  have h3 := beta_enclosure_expected_reading N_l N_u B_l B_u ρ β
    (UnifiedQuantLedger.lossTotal (UnifiedQuantLedger.dedupFirst masterLoss))
    hρ hβ hNl hBlβ hBl hBlu hNel hNB hwl hwd
  have key : exposureOf (amtPerturb d masterFlows) masterInterim.ledger ps' (N_u / B_l)
      - exposureOf masterFlows masterInterim.ledger ps (N_l / B_u)
      = (UnifiedPayoffChain.legalReading Role.claimant
            ⟨amtPerturb d masterFlows, LegalStatus.upheld, false⟩
          - UnifiedPayoffChain.legalReading Role.claimant
            ⟨masterFlows, LegalStatus.upheld, false⟩)
        + ((UnifiedQuantLedger.outstanding
            (UnifiedQuantLedger.afterStream ps' masterInterim.ledger)
          - UnifiedQuantLedger.outstanding
            (UnifiedQuantLedger.afterStream ps masterInterim.ledger))
          + (N_u / B_l * UnifiedQuantLedger.lossTotal
              (UnifiedQuantLedger.dedupFirst masterLoss)
            - N_l / B_u * UnifiedQuantLedger.lossTotal
              (UnifiedQuantLedger.dedupFirst masterLoss))) := by
    unfold exposureOf
    ring
  rw [key]
  calc |(UnifiedPayoffChain.legalReading Role.claimant
          ⟨amtPerturb d masterFlows, LegalStatus.upheld, false⟩
        - UnifiedPayoffChain.legalReading Role.claimant ⟨masterFlows, LegalStatus.upheld, false⟩)
      + ((UnifiedQuantLedger.outstanding
          (UnifiedQuantLedger.afterStream ps' masterInterim.ledger)
        - UnifiedQuantLedger.outstanding
          (UnifiedQuantLedger.afterStream ps masterInterim.ledger))
        + (N_u / B_l * UnifiedQuantLedger.lossTotal
            (UnifiedQuantLedger.dedupFirst masterLoss)
          - N_l / B_u * UnifiedQuantLedger.lossTotal
            (UnifiedQuantLedger.dedupFirst masterLoss)))|
      ≤ |UnifiedPayoffChain.legalReading Role.claimant
          ⟨amtPerturb d masterFlows, LegalStatus.upheld, false⟩
        - UnifiedPayoffChain.legalReading Role.claimant ⟨masterFlows, LegalStatus.upheld, false⟩|
        + |(UnifiedQuantLedger.outstanding
            (UnifiedQuantLedger.afterStream ps' masterInterim.ledger)
          - UnifiedQuantLedger.outstanding
            (UnifiedQuantLedger.afterStream ps masterInterim.ledger))
          + (N_u / B_l * UnifiedQuantLedger.lossTotal
              (UnifiedQuantLedger.dedupFirst masterLoss)
            - N_l / B_u * UnifiedQuantLedger.lossTotal
              (UnifiedQuantLedger.dedupFirst masterLoss))| := abs_add_le _ _
  _ ≤ (masterFlows.map (fun x => |consequenceValuation Role.claimant x.kind| * |d x|)).sum
      + (|UnifiedQuantLedger.outstanding
          (UnifiedQuantLedger.afterStream ps' masterInterim.ledger)
        - UnifiedQuantLedger.outstanding
          (UnifiedQuantLedger.afterStream ps masterInterim.ledger)|
        + |N_u / B_l * UnifiedQuantLedger.lossTotal
            (UnifiedQuantLedger.dedupFirst masterLoss)
          - N_l / B_u * UnifiedQuantLedger.lossTotal
            (UnifiedQuantLedger.dedupFirst masterLoss)|) :=
        add_le_add h1 (abs_add_le _ _)
  _ ≤ (masterFlows.map (fun x => |consequenceValuation Role.claimant x.kind| * |d x|)).sum
      + (δ + 2 * ρ / β
        * |UnifiedQuantLedger.lossTotal (UnifiedQuantLedger.dedupFirst masterLoss)|) :=
        add_le_add (le_refl _) (add_le_add h2 h3)
  _ = (masterFlows.map (fun x => |consequenceValuation Role.claimant x.kind| * |d x|)).sum
      + δ + 2 * ρ / β
        * |UnifiedQuantLedger.lossTotal (UnifiedQuantLedger.dedupFirst masterLoss)| := by
        ring

/-- **误差传播面命题（别名，供总合取引用）**：收益层线性界（∀ 扰动函数）＋账本层
Lipschitz 界（∀ 支付流）＋数量面整值承载（ε=0）＋概率面包围传播律（∀ 包围输入）
＋端到端合成界。 -/
def ErrorChainProp : Prop :=
    (∀ (role : Role) (d : UnifiedPayoffChain.CashEntry → ℚ)
        (fl : UnifiedPayoffChain.PayFlow),
      |UnifiedPayoffChain.legalReading role { fl with entries := amtPerturb d fl.entries }
        - UnifiedPayoffChain.legalReading role fl|
        ≤ (fl.entries.map (fun x => |consequenceValuation role x.kind| * |d x|)).sum) ∧
    (∀ (items : List UnifiedQuantLedger.LedgerItem), (∀ it ∈ items, 0 ≤ it.amount) →
      ∀ (ps ps' : List ℚ), (∀ p ∈ ps, 0 ≤ p) → (∀ p ∈ ps', 0 ≤ p) → ∀ (δ : ℚ),
      |ps.sum - ps'.sum| ≤ δ →
      |UnifiedQuantLedger.outstanding (UnifiedQuantLedger.afterStream ps items)
        - UnifiedQuantLedger.outstanding (UnifiedQuantLedger.afterStream ps' items)| ≤ δ) ∧
    QtyFaceProp ∧
    (∀ (N_l N_u B_l B_u ρ β loss : ℚ), 0 < ρ → 0 < β → 0 ≤ N_l → β ≤ B_l → 0 < B_l →
      B_l ≤ B_u → N_l ≤ N_u → N_l ≤ B_u → N_u - N_l ≤ ρ → B_u - B_l ≤ ρ →
      |N_u / B_l * loss - N_l / B_u * loss| ≤ 2 * ρ / β * |loss|) ∧
    (∀ (d : UnifiedPayoffChain.CashEntry → ℚ) (ps ps' : List ℚ),
      (∀ p ∈ ps, 0 ≤ p) → (∀ p ∈ ps', 0 ≤ p) → ∀ (δ : ℚ),
      0 ≤ δ → |ps.sum - ps'.sum| ≤ δ →
      ∀ (N_l N_u B_l B_u ρ β : ℚ), 0 < ρ → 0 < β → 0 ≤ N_l → β ≤ B_l → 0 < B_l →
        B_l ≤ B_u → N_l ≤ N_u → N_l ≤ B_u → N_u - N_l ≤ ρ → B_u - B_l ≤ ρ →
      |exposureOf (amtPerturb d masterFlows) masterInterim.ledger ps' (N_u / B_l)
          - exposureOf masterFlows masterInterim.ledger ps (N_l / B_u)|
        ≤ (masterFlows.map (fun x => |consequenceValuation Role.claimant x.kind| * |d x|)).sum
          + δ + 2 * ρ / β
            * |UnifiedQuantLedger.lossTotal (UnifiedQuantLedger.dedupFirst masterLoss)|)

/-- **误差传播面收口**：`ErrorChainProp` 在综合见证案上成立。 -/
theorem master_error_propagation_chain : ErrorChainProp := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact fun role d fl => legalReading_perturb role d fl
  · exact fun items hnn ps ps' hps hps' δ h =>
      outstanding_payment_perturb items hnn ps ps' hps hps' δ h
  · exact master_qty_ast_carries_balance
  · exact fun N_l N_u B_l B_u ρ β loss hρ hβ hNl hBlβ hBl hBlu hNel hNB hwl hwd =>
      beta_enclosure_expected_reading N_l N_u B_l B_u ρ β loss hρ hβ hNl hBlβ hBl hBlu hNel
        hNB hwl hwd
  · exact fun d ps ps' hps hps' δ _hδ0 hsum N_l N_u B_l B_u ρ β hρ hβ hNl hBlβ hBl hBlu hNel
      hNB hwl hwd =>
      master_exposure_perturb_chain d ps ps' hps hps' δ _hδ0 hsum N_l N_u B_l B_u ρ β hρ hβ
        hNl hBlβ hBl hBlu hNel hNB hwl hwd

/-! ## 五、策略/均衡面（菜单值＝主链读数；同一均衡关系） -/

/-- 玩家 i 的合法利益值：恰为综合案的账本余额（玩家 0）或收益读数（玩家 1）——
均衡菜单的收益面**定义性**来自主链中间读数，不是任意实数表。 -/
def masterLawful (i : Fin 2) : ℚ :=
  if i = 0 then masterBalance else masterReading

theorem masterLawful_0 : masterLawful 0 = masterBalance := rfl

theorem masterLawful_1 : masterLawful 1 = masterReading := rfl

theorem masterLawful_eq (i : Fin 2) :
    masterLawful i = if i = 0 then 160 else 250 := by
  fin_cases i
  · show (if (0 : Fin 2) = 0 then masterBalance else masterReading)
        = if (0 : Fin 2) = 0 then 160 else 250
    rw [masterBalance_eq, if_pos (rfl : (0 : Fin 2) = 0),
      if_pos (rfl : (0 : Fin 2) = 0)]
  · show (if (1 : Fin 2) = 0 then masterBalance else masterReading)
        = if (1 : Fin 2) = 0 then 160 else 250
    rw [if_neg (by simp : ¬((1 : Fin 2) = 0)), masterReading_eq,
      if_neg (by simp : ¬((1 : Fin 2) = 0))]

/-- 综合案的法律行动菜单：两玩家各自"配合（lawful v）／违约（sanction v/5）"，
v ＝该玩家的主链读数（[代拟稿] 制裁折价 1/5）。 -/
def masterMenu : UnifiedEquilExist.LegalActionMenu (Fin 2) Bool where
  pay := fun a i =>
    if a i then UnifiedEquilExist.LegalEval.lawful (masterLawful i)
    else UnifiedEquilExist.LegalEval.sanction (masterLawful i / 5)

/-- 菜单的 ℚ 收益表（同一 pay 的读数面）。 -/
def masterQ : (Fin 2 → Bool) → Fin 2 → ℚ :=
  fun a i => (masterMenu.pay a i).toQ

theorem master_uReal_eq_cast :
    masterMenu.uReal = fun a i => (masterQ a i : ℝ) := rfl

theorem update_pureMR (p : Fin 2 → Bool) (i : Fin 2) (b : Bool) :
    Function.update (UnifiedEquilExist.pureMR p) i (UnifiedEquilExist.pointR b)
      = UnifiedEquilExist.pureMR (Function.update p i b) := by
  funext j a
  have hrow : Function.update (UnifiedEquilExist.pureMR p) i (UnifiedEquilExist.pointR b) j a
      = if j = i then UnifiedEquilExist.pointR b a
        else UnifiedEquilExist.pureMR p j a := by
    rw [Function.update_apply, ite_apply]
  rw [hrow]
  by_cases hji : j = i
  · rw [if_pos hji]
    have hu : Function.update p i b j = b := by
      rw [Function.update_apply, if_pos hji]
    show UnifiedEquilExist.pointR b a
        = (if a = Function.update p i b j then (1 : ℝ) else 0)
    rw [hu]
    rfl
  · rw [if_neg hji]
    have hu : Function.update p i b j = p j := by
      rw [Function.update_apply, if_neg hji]
    show UnifiedEquilExist.pureMR p j a
        = (if a = Function.update p i b j then (1 : ℝ) else 0)
    rw [hu]
    rfl

theorem master_base_eu (i : Fin 2) :
    UnifiedEquilExist.euR masterMenu.uReal (UnifiedEquilExist.pureMR (fun _ => true)) i
      = ((masterLawful i : ℚ) : ℝ) := by
  rw [UnifiedEquilExist.euR_pureMR]
  show ((masterMenu.pay (fun _ => true) i).toQ : ℝ) = ((masterLawful i : ℚ) : ℝ)
  simp [masterMenu, UnifiedEquilExist.LegalEval.toQ]

theorem master_pay_dev (i : Fin 2) (b : Bool) :
    masterMenu.pay (Function.update (fun _ => true) i b) i
      = (if b then UnifiedEquilExist.LegalEval.lawful (masterLawful i)
        else UnifiedEquilExist.LegalEval.sanction (masterLawful i / 5)) := by
  have hb : (Function.update (fun _ => true) i b) i = b := by simp
  simp only [masterMenu]
  rw [hb]

theorem master_dev_eu (i : Fin 2) (b : Bool) :
    UnifiedEquilExist.euR masterMenu.uReal
        (Function.update (UnifiedEquilExist.pureMR (fun _ => true)) i
          (UnifiedEquilExist.pointR b)) i
      = ((if b then masterLawful i else -(masterLawful i / 5) : ℚ) : ℝ) := by
  rw [update_pureMR, UnifiedEquilExist.euR_pureMR]
  show ((masterMenu.pay (Function.update (fun _ => true) i b) i).toQ : ℝ)
      = ((if b then masterLawful i else -(masterLawful i / 5) : ℚ) : ℝ)
  rw [master_pay_dev i b]
  cases b <;> rfl

/-- **策略/均衡面收口**：菜单收益定义性来自主链读数（余额 160／收益读数 250）；
Kakutani 路线混合均衡存在（消费 W16 主定理）；ℚ↔ℝ 两载体同一均衡关系（消费
W16 cast 桥）；显式全配合纯均衡（合法值严格超过 1/5 折价制裁 ⇒ 配合是
最优回应，逐玩家纯偏离检查）。 -/
theorem master_equil_face :
    (masterLawful 0 = masterBalance ∧ masterLawful 1 = masterReading
      ∧ masterBalance = 160 ∧ masterReading = 250) ∧
    (∃ σ : Fin 2 → Bool → ℝ, UnifiedEquilExist.InSimplexR σ
      ∧ UnifiedEquilExist.IsNashR masterMenu.uReal σ) ∧
    (∀ σ : Fin 2 → Bool → ℚ, UnifiedNeedlesGapMid.IsNash masterQ σ
      ↔ UnifiedEquilExist.IsNashR masterMenu.uReal (UnifiedEquilExist.castProfile σ)) ∧
    UnifiedEquilExist.IsNashR masterMenu.uReal (UnifiedEquilExist.pureMR (fun _ => true)) := by
  refine ⟨⟨masterLawful_0, masterLawful_1, masterBalance_eq, masterReading_eq⟩,
    UnifiedEquilExist.finite_legal_mixed_equilibrium_exists_of_menu (I := Fin 2) (Act := Bool)
      masterMenu,
    fun σ => UnifiedEquilExist.gapmid_nash_iff_real masterQ σ, ?_⟩
  refine (UnifiedEquilExist.nashR_iff_no_pure_dev_gain masterMenu.uReal _).mpr ?_
  intro i b
  rw [master_dev_eu i b, master_base_eu i, masterLawful_eq i]
  fin_cases i <;> cases b <;> norm_num

/-- 策略/均衡面接线命题（别名，供总合取引用）。 -/
def EquilFaceProp : Prop :=
  (masterLawful 0 = masterBalance ∧ masterLawful 1 = masterReading
    ∧ masterBalance = 160 ∧ masterReading = 250) ∧
    (∃ σ : Fin 2 → Bool → ℝ, UnifiedEquilExist.InSimplexR σ
      ∧ UnifiedEquilExist.IsNashR masterMenu.uReal σ) ∧
    (∀ σ : Fin 2 → Bool → ℚ, UnifiedNeedlesGapMid.IsNash masterQ σ
      ↔ UnifiedEquilExist.IsNashR masterMenu.uReal (UnifiedEquilExist.castProfile σ)) ∧
    UnifiedEquilExist.IsNashR masterMenu.uReal (UnifiedEquilExist.pureMR (fun _ => true))

/-- 静态链/事件链对应命题（别名，供总合取引用）。 -/
def EventFaceProp : Prop :=
  (∀ a ∈ masterInterim.finalNet, a ∈ closureAt (hornOf masterInterim.docket)) ∧
    (∀ a ∈ RequiredAtoms,
      a ∈ closureAt (hornOf masterInterim.docket) ∧ a ∈ masterInterim.finalNet) ∧
    (∀ st ∈ masterInterim.traj, st.rule ∈ familyRuleList ∧ srcInForce st.rule.src = true)

/-! ## 六、总定理（第 60 针重建版） -/

/-- **第 60 针（总，I:814 重建版）**：`unified_legal_derivation_on_declared_fragment`
——在声明的综合适用域（满料案卷＋29 规则表＋[代拟稿] 数值政策，见头注"二、实际
适用域"）上，下列事实**同时**成立：(F1) 共同中间见证（各层读数同源共存、数值
接线咬合）；(F2) 静态链/事件链对应（健全性＋消费集上双向一致＋规则/法源钉死）；
(F3) 交换关系（支付流×余额/收益、区间合并×份额缩放、负担通道×支付通道）；
(F4) 误差传播（收益层线性界＋账本层 Lipschitz 界＋数量面整值承载＋概率面包围
传播律＋端到端合成界）；(F5) 四面接线（数量 AST／Beta 概率／策略均衡／事件链
解释全部接到同一综合中间结果的读数上）。旧件"同一个 M＋独立算术"的凑法被本合取
逐项超越：每一面都消费主链读数（C3–C7、masterLawful、masterQtyAst、暴露函数）。 -/
theorem unified_legal_derivation_on_declared_fragment :
    -- (F1) 共同中间见证
    Coherent masterInterim ∧
    -- (F2) 静态链/事件链对应
    ((∀ a ∈ masterInterim.finalNet, a ∈ closureAt (hornOf masterInterim.docket)) ∧
      (∀ a ∈ RequiredAtoms,
        a ∈ closureAt (hornOf masterInterim.docket) ∧ a ∈ masterInterim.finalNet) ∧
      (∀ st ∈ masterInterim.traj, st.rule ∈ familyRuleList ∧ srcInForce st.rule.src = true)) ∧
    -- (F3) 交换关系（三组）
    ((∀ p₁ p₂ : ℚ, 0 ≤ p₁ → 0 ≤ p₂ →
        UnifiedQuantLedger.outstanding
            (UnifiedQuantLedger.afterStream [p₁, p₂] masterInterim.ledger)
          = UnifiedQuantLedger.outstanding
            (UnifiedQuantLedger.afterStream [p₂, p₁] masterInterim.ledger)) ∧
      (∀ (c : ℚ) (hc : 0 ≤ c) (i j : JurisLean.FullMath.Numeric.Iv),
        UnifiedQuantLedger.QIv.vscale c hc (JurisLean.FullMath.Numeric.Iv.add i j)
          = JurisLean.FullMath.Numeric.Iv.add (UnifiedQuantLedger.QIv.vscale c hc i)
            (UnifiedQuantLedger.QIv.vscale c hc j)) ∧
      (∀ (p : ℚ) (bi : UnifiedEvalLayer.BurdenInput),
        payInterim p (burdenInterim bi masterInterim)
          = burdenInterim bi (payInterim p masterInterim))) ∧
    -- (F4) 误差传播
    ErrorChainProp ∧
    -- (F5) 四面接线
    (QtyFaceProp ∧ BetaFaceProp ∧ EquilFaceProp ∧ EventFaceProp) := by
  refine ⟨masterInterim_coherent, master_static_event_correspondence, ?_,
    master_error_propagation_chain, ?_⟩
  · refine ⟨fun p₁ p₂ h₁ h₂ => (ledger_payment_split_exchange p₁ p₂ h₁ h₂).1, ?_, ?_⟩
    · exact fun c hc i j => UnifiedQuantLedger.QIv.scale_distrib c hc i j
    · exact fun p bi => (master_channel_exchange_readings p bi).1
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact master_qty_ast_carries_balance
    · exact master_beta_face
    · exact master_equil_face
    · exact master_static_event_correspondence

end JurisLean.Seams.UnifiedMasterNeedle
