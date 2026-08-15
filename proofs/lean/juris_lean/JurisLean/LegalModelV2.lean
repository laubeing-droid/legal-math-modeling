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
   "ProposalEnvelope", "HumanResearchReceipt"]

/-- 中文说明：v2 规则与推理类型（含 v1 全部 11 类与新增类型）。 -/
def reasoningV2TypeNames : List String :=
  v1CanonicalTypeNames ++ ["Permission", "Exception"]

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

/-- 中文证明：注册表规模由当前源静态决定，不由报告复制。 -/
theorem v2_registry_size : canonicalV2TypeNames.length = 48 := by
  decide

/-- 中文证明：注册表无重复名称（canonical 宇宙不重复定义类型）。 -/
theorem v2_registry_nodup : canonicalV2TypeNames.Nodup := by
  decide

end JurisLean
