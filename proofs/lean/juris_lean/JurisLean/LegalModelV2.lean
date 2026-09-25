import JurisLean.LegalIds

/-!
中文说明：M1 canonical semantics v2 类型宇宙。v1 的 11 个 canonical types
作为兼容层保留在 v2 推理类型集合中；v2 不在原类上塞自由字典，而是显式
扩充身份、来源准入、推理和编译四层类型。Python 与 Lean 的名称、字段语义
和枚举由机器可读 manifest 对齐；Python 可序列化合同不取得 Lean 定义
authority。
-/

namespace JurisLean

/-- 中文说明：v1 兼容的 11 个 canonical types。 -/
def v1CanonicalTypeNames : List String :=
  ["LegalFact", "LegalRule", "LegalNorm", "LegalClaim", "Argument",
   "Attack", "Priority", "Violation", "Reparation", "DecisionStatus",
   "ProofTrace"]

/-- 中文说明：v2 基础身份类型。 -/
def identityV2TypeNames : List String :=
  ["LegalId", "ContentDigest", "SchemaVersion", "SemanticsVersion",
   "CommitId", "TreeId", "BuildId", "CaseScope", "RunScope",
   "SourceLocator", "TimePoint", "TimeInterval", "ExactAmount",
   "ExactRate", "RoundingPolicy"]

/-- 中文说明：v2 来源与准入类型。 -/
def sourceV2TypeNames : List String :=
  ["SourceSnapshotRef", "SourceVersionEdge", "SourcePath", "EvidenceRef",
   "InterpretationRef", "FactCandidate", "FactAdmissionAttestation",
   "ProposalEnvelope", "HumanResearchReceipt", "Jurisdiction"]

/-- 中文说明：v2 规则与推理类型（含 v1 全部 11 类与新增类型）。 -/
def reasoningV2TypeNames : List String :=
  v1CanonicalTypeNames ++
  ["Permission", "Exception", "Relation", "LegalPower", "Event"]

/-- 中文说明：v2 编译与后端类型。 -/
def compilationV2TypeNames : List String :=
  ["LegalSpec", "LegalIVL", "ProofObligation", "BackendKind",
   "BackendProblem", "BackendWitness", "TranslationWitness",
   "CheckerReceipt", "SolverReceipt", "ProofReceipt",
   "RuntimeRefinementReceipt"]

/-- 中文说明：完整 v2 类型宇宙注册表。 -/
def canonicalV2TypeNames : List String :=
  identityV2TypeNames ++ sourceV2TypeNames ++ reasoningV2TypeNames ++
    compilationV2TypeNames

/-- 中文说明：v2 推理层的最小事实记录。 -/
structure LegalFactV2 where
  id : LegalId .fact
  predicate : String
  sourceRef : Option (LegalId .snapshot)
  admitted : Bool
deriving DecidableEq

/-- 中文说明：v2 规则记录；version 必须显式。 -/
structure LegalRuleV2 where
  id : LegalId .rule
  version : SchemaVersion
  premises : List (LegalId .fact)
  conclusion : LegalId .fact
deriving DecidableEq

/-- 中文说明：v2 规范记录；modality 用字符串句柄，语义在 DDL 层解释。 -/
structure LegalNormV2 where
  id : LegalId .norm
  modality : String
  ruleRef : LegalId .rule
deriving DecidableEq

/-- 中文说明：v2 argument 记录；support 必须来自已准入事实。 -/
structure ArgumentRecord where
  id : LegalId .argument
  ruleRef : LegalId .rule
  support : List (LegalId .fact)
  conclusion : LegalId .fact
deriving DecidableEq

/-- 中文说明：v2 attack 记录；每个攻击必须携带输入 witness。 -/
structure AttackRecord where
  id : LegalId .attack
  attacker : LegalId .argument
  target : LegalId .argument
  kind : String
  inputWitness : String
deriving DecidableEq

/-- 中文说明：来源快照引用；内容与 locator 改变使旧绑定失效。 -/
structure SourceSnapshotRef where
  id : LegalId .snapshot
  locator : SourceLocator
  digest : ContentDigest
  version : SchemaVersion
deriving DecidableEq

/-- 中文说明：翻译见证记录的一跳。 -/
structure TranslationStep where
  sourceDigest : ContentDigest
  targetDigest : ContentDigest
  lostFields : List String
  defaultedFields : List String
  obligationDischarged : Bool
deriving DecidableEq

/-- 中文说明：证书信封 v2 的身份头；内容绑定字段在 checker 层重算。 -/
structure CertificateEnvelopeId where
  certificate : LegalId .certificate
  producerCommit : CommitId
  tree : TreeId
  build : BuildId
  semantics : SemanticsVersion
deriving DecidableEq

/-!
TY-01..TY-04：对象定义 v3 新增四类型的最小结构（对象定义冻结版 2026-09-25）。
名称进注册表；Power/Obligation/Occurred 三模态互不推出；H 为事件时间结构
并进入 ApplicableNorm 签名；Jurisdiction 为法域轴。选择/求值语义是 EV 池
目标，此处不实现。
-/

/-- 中文说明：TY-01 法律关系共同约束的类别：同一损失/竞合互斥/共同消减。 -/
inductive SharedConstraintKind where
  | sameLoss | competingExclusive | jointReduction
deriving DecidableEq, Repr

/-- 中文说明：TY-01 共同约束；约束跨关系成立，成员关系显式列出。 -/
structure SharedConstraint where
  kind : SharedConstraintKind
  memberRelations : List String
deriving DecidableEq, Repr

/-- 中文说明：TY-01 法律关系；关系整体含共同约束（对象定义 v3 第一条）。 -/
structure Relation where
  relationId : String
  parties : List String
  kind : String
  sharedConstraints : List SharedConstraint
deriving DecidableEq, Repr

/-- 中文说明：TY-02 权能记录；Power/Obligation/Occurred 三模态独立承载，
互不推出（对象定义 v3 第五条）。 -/
structure LegalPower where
  powerId : String
  powerGranted : Bool
  obligationImposed : Bool
  occurred : Bool
deriving DecidableEq, Repr

/-- 中文说明：TY-03 事件；事件历史 H 的成员。 -/
structure Event where
  eventId : String
  atDay : Int
  eventType : String
deriving DecidableEq, Repr

/-- 中文说明：TY-03 事件历史时间结构 H；按构造序承载事件。 -/
structure EventHistory where
  events : List Event
deriving DecidableEq, Repr

/-- 中文说明：TY-04 法域轴 J：内地/港/美/其他（其他须携带显式代码）。 -/
inductive Jurisdiction where
  | mainland | hongKong | unitedStates | other (code : String)
deriving DecidableEq, Repr

/-- 中文说明：规范选择签名 A(J,V,q,H,t) 的载体（对象定义 v3 第六条）；
H 与 t 都是必填，t 不单独决定版本。选择语义是 EV-04 目标。 -/
structure ApplicableNormQuery where
  jurisdiction : Jurisdiction
  normEnv : String
  question : String
  history : EventHistory
  timePoint : TimePoint
deriving DecidableEq, Repr

/-- 中文证明：v2 注册表完整覆盖四个分层。 -/
theorem v2_registry_covers_four_layers :
    canonicalV2TypeNames =
      identityV2TypeNames ++ sourceV2TypeNames ++ reasoningV2TypeNames ++
        compilationV2TypeNames := rfl

/-- 中文证明：v1 的 11 个 canonical types 全部保留在 v2 推理层中。 -/
theorem v1_types_preserved_in_v2 :
    ∀ name ∈ v1CanonicalTypeNames, name ∈ reasoningV2TypeNames := by
  decide

/-- 中文证明：v1 兼容层名称全部出现在 v2 宇宙中（兼容不丢失）。 -/
theorem v1_compatible_names_in_universe :
    ∀ name ∈ v1CanonicalTypeNames, name ∈ canonicalV2TypeNames := by
  decide

/-- 中文证明：DecisionStatus 属于 v2 宇宙。 -/
theorem decision_status_in_v2_universe :
    "DecisionStatus" ∈ canonicalV2TypeNames := by
  decide

/-- 中文证明：注册表规模由当前源静态决定，不由报告复制。
TY-01..04 增 Relation/LegalPower/Event/Jurisdiction 后为 52。 -/
theorem v2_registry_size : canonicalV2TypeNames.length = 52 := by
  decide

/-- 中文证明：注册表无重复名称（canonical 宇宙不重复定义类型）。 -/
theorem v2_registry_nodup : canonicalV2TypeNames.Nodup := by
  decide

/-- 中文证明：TY-01..04 四个新类型都在 v2 注册表中。 -/
theorem v3_kernel_types_in_v2_universe :
    "Relation" ∈ canonicalV2TypeNames ∧ "LegalPower" ∈ canonicalV2TypeNames ∧
      "Event" ∈ canonicalV2TypeNames ∧ "Jurisdiction" ∈ canonicalV2TypeNames := by
  decide

/-- 中文证明：Power 不蕴含 Occurred——存在权能成立而事件未发生的记录
（对象定义 v3 第五条：三模态互不推出，仅为类型层见证，不涉规范内容）。 -/
theorem legalPower_power_not_implies_occurred :
    ∃ p : LegalPower, p.powerGranted = true ∧ p.occurred = false := by
  refine ⟨{ powerId := "synthetic", powerGranted := true,
            obligationImposed := false, occurred := false }, rfl, rfl⟩

/-- 中文证明：Obligation 不蕴含 Occurred。 -/
theorem legalPower_obligation_not_implies_occurred :
    ∃ p : LegalPower, p.obligationImposed = true ∧ p.occurred = false := by
  refine ⟨{ powerId := "synthetic", powerGranted := false,
            obligationImposed := true, occurred := false }, rfl, rfl⟩

/-- 中文证明：Power 不蕴含 Obligation。 -/
theorem legalPower_power_not_implies_obligation :
    ∃ p : LegalPower, p.powerGranted = true ∧ p.obligationImposed = false := by
  refine ⟨{ powerId := "synthetic", powerGranted := true,
            obligationImposed := false, occurred := false }, rfl, rfl⟩

/-- 中文证明：共同约束参与关系同一性——只换约束集得到不同的关系记录。 -/
theorem relation_shared_constraints_participate (rid : String)
    (ps : List String) (k : String) (c1 c2 : List SharedConstraint)
    (hne : c1 ≠ c2) :
    Relation.mk rid ps k c1 ≠ Relation.mk rid ps k c2 := by
  intro heq
  exact hne (congrArg Relation.sharedConstraints heq)

/-- 中文证明：H 参与规范选择签名的同一性——其余参数相同、仅 H 不同的
两个选择语境不同（H 真正进入签名，而非装饰字段）。 -/
theorem applicable_norm_history_participates (j : Jurisdiction) (V q : String)
    (h1 h2 : EventHistory) (t : TimePoint) (hne : h1 ≠ h2) :
    ApplicableNormQuery.mk j V q h1 t ≠ ApplicableNormQuery.mk j V q h2 t := by
  intro heq
  exact hne (congrArg ApplicableNormQuery.history heq)

/-- 中文证明：法域轴的主干路由两两可区分（fail-closed 路由的前提）。 -/
theorem jurisdiction_mainland_distinct_from_united_states :
    Jurisdiction.mainland ≠ Jurisdiction.unitedStates := by
  decide

end JurisLean
