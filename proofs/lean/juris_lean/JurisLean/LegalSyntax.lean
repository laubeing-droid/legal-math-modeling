import Mathlib.Data.Finset.Basic

/-!
中文说明：本文件定义四个竖切共享的 canonical Lean 类型。
这些类型只覆盖 contract breach、license、permission、priority 闭环所需
的最小语义，不声明全法律宇宙的本体论。
-/

namespace JurisLean

/-- 中文说明：事实、规则、当事人等外部标识统一用稳定字符串承载。 -/
abbrev FactId := String
abbrev RuleId := String
abbrev Party := String
abbrev ClaimId := String
abbrev EvidenceId := String
abbrev NormId := String
abbrev ArgumentId := String
abbrev AttackId := String
abbrev CertificateId := String

/-- 中文说明：Playbook 要求闭合的四个法律竖切。 -/
inductive SliceKind where
  | contractBreach
  | license
  | permission
  | priority
deriving DecidableEq, Repr

/-- 中文说明：最小 DDL 层需要区分的规范模态。 -/
inductive Modality where
  | obligation
  | permission
  | prohibition
  | constitutive
deriving DecidableEq, Repr

/-- 中文说明：证据来源的可信边界；candidate 不能直接证明法律结论。 -/
inductive EvidenceKind where
  | sourceSpan
  | formalBackend
  | humanReview
  | candidate
deriving DecidableEq, Repr

/-- 中文说明：JC runtime 与 spec 共享的判定状态枚举。 -/
inductive DecisionStatus where
  | proved
  | refuted
  | undecided
  | tainted
deriving DecidableEq, Repr

/-- 中文说明：披露/复核标签；它只能限制披露或触发复核，不能提升结论。 -/
inductive TrustLabel where
  | disclosePublic
  | disclosePrivate
  | needsReview
  | tainted
deriving DecidableEq, Repr

/-- 中文说明：攻击类型显式区分普通反驳、例外抗辩和优先级击败。 -/
inductive AttackKind where
  | rebuttal
  | exception
  | priorityDefeat
  | selfAttack
deriving DecidableEq, Repr

/-- 中文说明：事实包含竖切归属和 verified gate，不把候选事实默认为真。 -/
structure LegalFact where
  id : FactId
  predicate : String
  slice : SliceKind
  verified : Bool
deriving DecidableEq, Repr

/-- 中文说明：Claim 是进入论证层的规范化结论。 -/
structure Claim where
  id : ClaimId
  conclusion : FactId
  slice : SliceKind
deriving DecidableEq, Repr

/-- 中文说明：Evidence 保留来源类型、复核状态和披露标签。 -/
structure Evidence where
  id : EvidenceId
  kind : EvidenceKind
  verified : Bool
  trust : TrustLabel
deriving DecidableEq, Repr

/-- 中文说明：Norm 是 DDL 最小核中的规范节点。 -/
structure Norm where
  id : NormId
  modality : Modality
  actor : Party
  action : String
  active : Bool
  slice : SliceKind
deriving DecidableEq, Repr

/-- 中文说明：Obligation 用结构包裹 Norm，避免把 permission 静默当作 obligation。 -/
structure Obligation where
  norm : Norm
  modalityProof : norm.modality = Modality.obligation

/-- 中文说明：Permission 明确表示许可规范，不直接携带违约后果。 -/
structure Permission where
  norm : Norm
  modalityProof : norm.modality = Modality.permission

/-- 中文说明：Prohibition 表示禁止规范，和 permission 分离建模。 -/
structure Prohibition where
  norm : Norm
  modalityProof : norm.modality = Modality.prohibition

/-- 中文说明：Defense 表示抗辩或例外事实对目标结论的击败。 -/
structure Defense where
  id : String
  trigger : FactId
  defeats : FactId
  evidence : Evidence
deriving DecidableEq, Repr

/-- 中文说明：Exception 是 Defense 的竖切内别名结构，用于 DDL 语义显式化。 -/
structure Exception where
  defense : Defense
deriving DecidableEq, Repr

/-- 中文说明：Priority 表示一个论证或规则相对另一个目标的优先级。 -/
structure Priority where
  id : String
  higher : ArgumentId
  lower : ArgumentId
  evidence : Evidence
  active : Bool
deriving DecidableEq, Repr

/-- 中文说明：Argument 必须带有支持事实和 supported 标记。 -/
structure Argument where
  id : ArgumentId
  claim : Claim
  support : Finset FactId
  rule : RuleId
  supported : Bool
deriving DecidableEq

/-- 中文说明：Attack 是有向击败关系，kind 保留法律语义。 -/
structure Attack where
  id : AttackId
  source : ArgumentId
  target : ArgumentId
  kind : AttackKind
deriving DecidableEq, Repr

/-- 中文说明：Violation 把未被击败的规范违反映射到后果事实。 -/
structure Violation where
  normId : NormId
  trigger : FactId
  consequence : FactId
deriving DecidableEq, Repr

/-- 中文说明：Reparation 记录违反后的最小补救后果。 -/
structure Reparation where
  normId : NormId
  remedy : String
deriving DecidableEq, Repr

/-- 中文说明：ProofTrace 保留规则、论证和攻击的最小可审计轨迹。 -/
structure ProofTrace where
  facts : Finset FactId
  rules : Finset RuleId
  arguments : Finset ArgumentId
  attacks : Finset AttackId
deriving DecidableEq

/-- 中文说明：Certificate 是 checker 的输入边界，缺字段或未核验证据必须 fail-closed。 -/
structure Certificate where
  id : CertificateId
  slice : SliceKind
  status : DecisionStatus
  evidence : Evidence
  trace : ProofTrace
  wellFormed : Bool
  requiredFactsPresent : Bool
  proofObligationsPresent : Bool
deriving DecidableEq

/-- 中文说明：FactId 的序列化键就是输入标识，保证键稳定。 -/
def FactId.serializationKey (id : FactId) : String := id

/-- 中文说明：RuleId 的序列化键就是输入标识，保证键稳定。 -/
def RuleId.serializationKey (id : RuleId) : String := id

/-- 中文说明：DecisionStatus 对应 JC runtime 的四个字符串状态。 -/
def DecisionStatus.runtimeKey : DecisionStatus -> String
  | DecisionStatus.proved => "PROVED"
  | DecisionStatus.refuted => "REFUTED"
  | DecisionStatus.undecided => "UNDECIDED"
  | DecisionStatus.tainted => "TAINTED"

/-- 中文说明：信任标签不会改变判定状态；它只约束披露/复核流程。 -/
def TrustLabel.applyToStatus (_label : TrustLabel) (status : DecisionStatus) : DecisionStatus :=
  status

/-- 中文说明：candidate 不是可审计证据。 -/
def Evidence.isAuditable (e : Evidence) : Bool :=
  e.verified && e.kind != EvidenceKind.candidate

/-- 中文证明：事实标识序列化键稳定。 -/
theorem fact_serialization_key_stable (id : FactId) :
    FactId.serializationKey id = id := rfl

/-- 中文证明：规则标识序列化键稳定。 -/
theorem rule_serialization_key_stable (id : RuleId) :
    RuleId.serializationKey id = id := rfl

/-- 中文证明：DecisionStatus runtime 字符串和 Lean 枚举一一对应。 -/
theorem decisionStatus_runtimeKey_injective :
    Function.Injective DecisionStatus.runtimeKey := by
  intro a b h
  cases a <;> cases b <;> simp [DecisionStatus.runtimeKey] at h ⊢

/-- 中文证明：TrustLabel 不能把法律结论提升成其他状态。 -/
theorem trust_label_cannot_promote_status
    (label : TrustLabel) (status : DecisionStatus) :
    TrustLabel.applyToStatus label status = status := rfl

/-- 中文证明：candidate evidence 永远不是可审计证据。 -/
theorem candidate_evidence_not_auditable
    (id : EvidenceId) (verified : Bool) (trust : TrustLabel) :
    Evidence.isAuditable {
      id := id,
      kind := EvidenceKind.candidate,
      verified := verified,
      trust := trust
    } = false := by
  cases verified <;> simp [Evidence.isAuditable]

end JurisLean
