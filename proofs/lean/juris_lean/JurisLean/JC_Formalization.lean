-- JC_Formalization.lean
-- JC 法律推理统一数学模型形式化证明系统
-- v5.0: 红队审计后重建，禁止证明幻觉
--
-- 所有 axiom 标记为 ASSUMED_NOT_PROVED，不计入 G1 完成率。
-- GraphSimilarityAxioms 已删除（存在反例 CE-001/CE-002）。
-- theorem_metadata 使用诚实状态标签。

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Basic

-- ==============================================
-- 1.1 证明状态枚举（v5.0 诚实标签）
-- ==============================================
inductive ProofStatus : Type
  | PROVED_BY_ARTIFACT    -- 有可运行 checker，输出 PASS
  | EMPIRICAL_PROXY       -- 有经验数据，但是代理/相关
  | AXIOM_ONLY            -- 用 axiom 声明，未从独立公理推出
  | PLAN_ONLY             -- 方案已定义，代码/证明未写
  | REFUTED               -- 有反例，永久禁集
  | MISSING_ARTIFACT      -- 验收命令引用的文件不存在
  | INVALID_CLAIM         -- 数学上错误的任务定义
  | PENDING_TOOLCHAIN     -- 待工具链（Lean/Z3/TLA+）
  deriving DecidableEq

-- ==============================================
-- 1.2 证据类型枚举
-- ==============================================
inductive EvidenceType : Type
  | FINITE_EXHAUST
  | SYMBOLIC
  | SMT
  | TOY_SYNTHETIC
  | DATA_PROXY
  | COUNTEREXAMPLE
  | ASSUMED_NOT_PROVED
  deriving DecidableEq

-- ==============================================
-- 1.3 核心定理集合
-- ==============================================
inductive CoreTheorem : Type
  | T1_GaloisConnection
  | T2_HornCorrectness
  | T3_EvidenceCredibility
  | T4_KripkeProgram
  | T5_TemporalKripke
  | T6_PolicyExpressiveness
  | T7_GradualVerification
  | T8_TriRailComplexity
  | T9_HornDungBridge
  | T10_CountsAs
  | T11_RoughSetDiscretion
  | T12_HierarchicalBayes
  | T13_Incommensurability
  | T14_DeonticProcedure
  | T15_CBLNonInterference
  | T16_CategoryRosetta
  | T17_BanachContraction
  | T18_DPPrivilege
  | T19_AbstractInterpretation
  | T20_MDLRuleComplexity
  deriving DecidableEq

-- ==============================================
-- 1.4 定理元数据结构
-- ==============================================
structure TheoremMetadata : Type where
  status : ProofStatus
  evidence : EvidenceType
  domain_bound : String
  sorry_count : Nat
  axiom_count : Nat
  deriving DecidableEq

-- ==============================================
-- 1.5 约束违反类型
-- ==============================================
inductive ConstraintViolation : Type
  | MONOTONICITY_OVERREACH
  | TOY_AS_UNIVERSAL
  | PROXY_AS_REAL
  | PENDING_AS_PROVED
  | CORRELATION_AS_CAUSAL
  | CROSS_JURISDICTION_CLAIM
  | AXIOM_AS_PROOF
  deriving DecidableEq

-- ==============================================
-- 2.1 定理元数据映射（v5.0 诚实状态）
-- ==============================================

-- NOTE: axiom 标记为 ASSUMED_NOT_PROVED，不计入证明完成率。
-- 66,066 是 AAF 图数，不是 Horn 闭包图数。
-- T20 claim_mapping level 不显著 (ρ=0.1168, p=0.4459)。

def theorem_metadata : CoreTheorem → TheoremMetadata
  -- PROVED_BY_ARTIFACT（有可运行 checker）
  | .T3_EvidenceCredibility => ⟨.PROVED_BY_ARTIFACT, .SYMBOLIC, "证据评分S(e)=r×i×a", 0, 0⟩
  | .T9_HornDungBridge => ⟨.PROVED_BY_ARTIFACT, .FINITE_EXHAUST, "AAF 66066图穷举", 0, 0⟩
  -- EMPIRICAL_PROXY（有经验数据但不是定理）
  | .T2_HornCorrectness => ⟨.EMPIRICAL_PROXY, .FINITE_EXHAUST, "3969 acyclic KB + 50K采样", 0, 0⟩
  | .T20_MDLRuleComplexity => ⟨.EMPIRICAL_PROXY, .DATA_PROXY, "claim_mapping level不显著", 0, 0⟩
  -- AXIOM_ONLY（Z3 把结论当公理）
  | .T4_KripkeProgram => ⟨.AXIOM_ONLY, .ASSUMED_NOT_PROVED, "Z3 consistency check only", 0, 1⟩
  -- PLAN_ONLY（框架存在）
  | .T12_HierarchicalBayes => ⟨.PLAN_ONLY, .DATA_PROXY, "框架存在，无数据", 0, 0⟩
  -- PROVED_BY_ARTIFACT（新证明）
  | .T1_GaloisConnection => ⟨.PROVED_BY_ARTIFACT, .SYMBOLIC, "有限join-半格上的残余映射Galois连接", 0, 0⟩
  | .T17_BanachContraction => ⟨.PROVED_BY_ARTIFACT, .SYMBOLIC, "Banach收缩定价函数", 0, 0⟩
  | .T16_CategoryRosetta => ⟨.PROVED_BY_ARTIFACT, .FINITE_EXHAUST, "44条样本CN_ONLY占30/44", 0, 0⟩
  -- PENDING_TOOLCHAIN
  | .T5_TemporalKripke => ⟨.PENDING_TOOLCHAIN, .TOY_SYNTHETIC, "有限时间线", 3, 0⟩
  | .T15_CBLNonInterference => ⟨.PENDING_TOOLCHAIN, .TOY_SYNTHETIC, "60条CBL规则", 0, 0⟩
  -- 已反驳（永久禁集）
  | .T18_DPPrivilege => ⟨.REFUTED, .COUNTEREXAMPLE, "无限隐私比反例", 0, 0⟩
  -- 已砍（产品不需要）
  | .T6_PolicyExpressiveness => ⟨.INVALID_CLAIM, .TOY_SYNTHETIC, "已砍：CTRS不是产品功能", 0, 0⟩
  | .T11_RoughSetDiscretion => ⟨.INVALID_CLAIM, .TOY_SYNTHETIC, "已砍：粗糙集不是产品功能", 0, 0⟩
  | .T14_DeonticProcedure => ⟨.INVALID_CLAIM, .TOY_SYNTHETIC, "已砍：道义逻辑不是产品功能", 0, 0⟩
  -- 未验证
  | .T7_GradualVerification => ⟨.MISSING_ARTIFACT, .TOY_SYNTHETIC, "无边界", 0, 0⟩
  | .T8_TriRailComplexity => ⟨.INVALID_CLAIM, .TOY_SYNTHETIC, "已砍：TriRail不是产品功能", 0, 0⟩
  | .T10_CountsAs => ⟨.INVALID_CLAIM, .TOY_SYNTHETIC, "已砍：counts-as不是产品功能", 0, 0⟩
  | .T13_Incommensurability => ⟨.INVALID_CLAIM, .TOY_SYNTHETIC, "已砍：不可通约不是产品功能", 0, 0⟩
  | .T19_AbstractInterpretation => ⟨.INVALID_CLAIM, .TOY_SYNTHETIC, "已砍：抽象解释不是产品功能", 0, 0⟩

-- ==============================================
-- 2.2 已证明定理集合（仅 PROVED_BY_ARTIFACT）
-- ==============================================
def proved_theorems : Finset CoreTheorem :=
  {CoreTheorem.T1_GaloisConnection, CoreTheorem.T3_EvidenceCredibility,
   CoreTheorem.T9_HornDungBridge, CoreTheorem.T16_CategoryRosetta,
   CoreTheorem.T17_BanachContraction}

theorem proved_theorems_card : proved_theorems.card = 5 := by decide

-- ==============================================
-- 2.3 经验代理定理集合
-- ==============================================
def empirical_proxy_theorems : Finset CoreTheorem :=
  {CoreTheorem.T2_HornCorrectness, CoreTheorem.T20_MDLRuleComplexity}

theorem empirical_proxy_card : empirical_proxy_theorems.card = 2 := by decide

-- ==============================================
-- 2.4 已反驳定理集合
-- ==============================================
def refuted_theorems : Finset CoreTheorem :=
  {CoreTheorem.T18_DPPrivilege}

theorem refuted_theorems_card : refuted_theorems.card = 1 := by decide

-- ==============================================
-- 2.5 待证明定理集合
-- ==============================================
def pending_theorems : Finset CoreTheorem :=
  {CoreTheorem.T5_TemporalKripke, CoreTheorem.T15_CBLNonInterference}

theorem pending_theorems_card : pending_theorems.card = 2 := by decide

-- ==============================================
-- 3.1 推进算子（边界保持）
-- ==============================================
def advance (T : CoreTheorem) (e : EvidenceType) : TheoremMetadata :=
  let m := theorem_metadata T
  if m.status = .PENDING_TOOLCHAIN ∧
     e ∈ [.FINITE_EXHAUST, .SYMBOLIC, .SMT] then
    { m with status := .PROVED_BY_ARTIFACT, evidence := e }
  else
    m

theorem advance_preserves_domain_bound :
    ∀ T e, (advance T e).domain_bound = (theorem_metadata T).domain_bound := by
  intro T e
  simp [advance]
  split <;> rfl

theorem advance_cannot_revive_refuted :
    ∀ T e, (theorem_metadata T).status = .REFUTED →
    (advance T e).status = .REFUTED := by
  intro T e h
  simp [advance, h]

-- ==============================================
-- 3.2 axiom 不计入证明完成率
-- ==============================================
def has_core_axiom (T : CoreTheorem) : Bool :=
  (theorem_metadata T).axiom_count > 0

-- NOTE: axiom exclusion is enforced by policy, not Lean proof.
-- G1 verification: grep -R "sorry\|axiom\|admit" proofs/lean
-- Any file with core axioms is excluded from G1 completion count.
