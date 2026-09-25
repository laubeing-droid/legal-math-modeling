import JurisLean.Genealogy.General

/-!
Round 9 — six inexpressibility boundary theorems (BND-01..04 new;
BND-05/06 point to existing assets: ReceiptAuthority.consensus_does_not_escalate
and TaintNoninterference.repetition_does_not_clean / majority_cannot_clean).
These are positive records of type-level inexpressibility inside the
Genealogy side; they do not re-implement the ULM trunk nor claim bridge
equivalences.
-/

namespace JurisLean.Genealogy.Boundary

/-! ============================================================
    BND-01
    失败不映射为正常载荷
    ============================================================ -/

inductive FailureKind where
  | unsupported
  | invalidInput
  | solverIncomplete
  | internalFailure
deriving DecidableEq

structure FailureCore where
  kind : FailureKind
  reason : String
  requestId : String
deriving DecidableEq


/-! ============================================================
    BND-02
    PartialValue 必带至少一个未关闭义务
    ============================================================ -/

structure PartialValue (α : Type) where
  value : α
  firstOpenObligation : String
  remainingOpenObligations : List String

def PartialValue.openObligations
    {α : Type}
    (p : PartialValue α) : List String :=
  p.firstOpenObligation :: p.remainingOpenObligations

def PartialValue.map
    {α β : Type}
    (f : α → β)
    (p : PartialValue α) : PartialValue β :=
  {
    value := f p.value
    firstOpenObligation := p.firstOpenObligation
    remainingOpenObligations := p.remainingOpenObligations
  }

/-- [BND-02] 任意 PartialValue 的未关闭义务列表非空（类型构造层保证）。 -/
theorem partialValue_openObligations_nonempty
    {α : Type}
    (p : PartialValue α) :
    p.openObligations ≠ [] := by
  cases p
  simp [PartialValue.openObligations]


/-!
计算结果三分：complete / partial / failure。
failure 与 payload 是不同构造子。
-/
inductive KernelResult (α : Type) where
  | complete (value : α)
  | partialResult (value : PartialValue α)
  | failure (failure : FailureCore)

/-- 只映射正常值；failure 分支完全不碰 FailureCore。 -/
def mapKernelResult
    {α β : Type}
    (f : α → β) :
    KernelResult α → KernelResult β
  | .complete value =>
      .complete (f value)
  | .partialResult value =>
      .partialResult (value.map f)
  | .failure failure =>
      .failure failure

/-- [BND-01] FailureCore 经载荷映射后原样保持为 failure。 -/
theorem failure_map_identity
    {α β : Type}
    (f : α → β)
    (failure : FailureCore) :
    mapKernelResult f (.failure failure)
      = (.failure failure : KernelResult β) := by
  rfl


/-! ============================================================
    BND-03
    “扩张族为空”必须先携带空性证明
    ============================================================ -/

/-- 某一选定语义下的扩张族。 -/
structure ExtensionFamily where
  members : List (List String)

/-- 声称“无扩张”的证书：空性证明是必填字段而非 Bool。 -/
structure NoExtensionsCertificate where
  family : ExtensionFamily
  emptyProof : family.members = []

/-- 声称“已有扩张”的证书：必须附与真实 family 相等的证据。 -/
structure ExactExtensionsCertificate where
  family : ExtensionFamily
  reported : List (List String)
  exactProof : reported = family.members

/-- 未完成求解：至少携带一个未关闭义务。 -/
structure IncompleteEvaluation where
  discovered : List (List String)
  firstOpenObligation : String
  remainingOpenObligations : List String

inductive EvaluationResult where
  | noExtensions
      (certificate : NoExtensionsCertificate)
  | extensionsFound
      (certificate : ExactExtensionsCertificate)
  | unfinished
      (state : IncompleteEvaluation)

/-- [BND-03] 进入 noExtensions 构造子的证书已拥有空性证明。 -/
theorem noExtensions_family_empty
    (certificate : NoExtensionsCertificate) :
    certificate.family.members = [] :=
  certificate.emptyProof


/-! ============================================================
    BND-04
    求解不完备不得改写成不利裁判
    ============================================================ -/

inductive AuthorityFinding where
  | satisfied
  | unmet
deriving DecidableEq

/-- 裁判权源形成的实体认定。 -/
structure AdjudicativeAuthority where
  authorityId : String
  requestId : String
  finding : AuthorityFinding

/-- 不利裁判权源证书：必须额外交出 finding = unmet 的依赖证明。 -/
structure AdverseAuthority where
  authority : AdjudicativeAuthority
  findingUnmet :
    authority.finding = AuthorityFinding.unmet

/-- 裁判输出四构造子：adverse 参数类型是 AdverseAuthority 而非普通权源。 -/
inductive AdjudicationOutput where
  | solverIncomplete
      (firstOpenObligation : String)
  | pendingLegalJudgment
  | favorable
      (authority : AdjudicativeAuthority)
  | adverse
      (authority : AdverseAuthority)

/-- 实体处置中间类型：故意不含 solverIncomplete。 -/
inductive SubstantiveDisposition where
  | favorable
      (authority : AdjudicativeAuthority)
  | adverse
      (authority : AdverseAuthority)

def substantiveToOutput :
    SubstantiveDisposition → AdjudicationOutput
  | .favorable authority =>
      .favorable authority
  | .adverse authority =>
      .adverse authority

/-- 裁判函数：unfinished 无条件输出 solverIncomplete。 -/
def adjudicate
    (evaluation : EvaluationResult)
    (disposition : Option SubstantiveDisposition) :
    AdjudicationOutput :=
  match evaluation with
  | .unfinished incomplete =>
      .solverIncomplete incomplete.firstOpenObligation
  | .noExtensions _ =>
      match disposition with
      | none =>
          .pendingLegalJudgment
      | some substantive =>
          substantiveToOutput substantive
  | .extensionsFound _ =>
      match disposition with
      | none =>
          .pendingLegalJudgment
      | some substantive =>
          substantiveToOutput substantive

/-- [BND-04-A] 未完成求解时不论传入何种实体处置，只能返回 solverIncomplete。 -/
theorem incomplete_adjudication_is_solverIncomplete
    (state : IncompleteEvaluation)
    (disposition : Option SubstantiveDisposition) :
    adjudicate (.unfinished state) disposition
      =
    .solverIncomplete state.firstOpenObligation := by
  rfl

/-- [BND-04-B] adverse 构造参数必然已携带 finding = unmet 的依赖证明。 -/
theorem adverseAuthority_requires_unmet
    (authority : AdverseAuthority) :
    authority.authority.finding
      = AuthorityFinding.unmet :=
  authority.findingUnmet


/-! ============================================================
    六类边界状态表

    1. Failure map identity                 —— 本文件 BND-01
    2. PartialValue nonempty obligations   —— 本文件 BND-02
    3. noExtensions carries emptiness      —— 本文件 BND-03
    4. incomplete cannot become adverse    —— 本文件 BND-04
    5. aggregation cannot raise guarantee  —— 既有资产指针：
         ReceiptAuthority.consensus_does_not_escalate
         （同级任意多次共识不产生层级提升）
    6. taint resubmission cannot clean     —— 既有资产指针：
         TaintNoninterference.repetition_does_not_clean
         TaintNoninterference.majority_cannot_clean
    ============================================================ -/

end JurisLean.Genealogy.Boundary
