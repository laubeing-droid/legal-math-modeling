import JurisLean.LegalSyntax

/-!
中文说明：本文件给出四个竖切所需的 DDL minimal core。
它只定义 obligation、permission、prohibition、violation、defense/exception、
remedial consequence 和 priority ordering 的最小接口。
-/

namespace JurisLean

/-- 中文说明：判断一个规范是否为 obligation。 -/
def isObligation (n : Norm) : Prop :=
  n.modality = Modality.obligation

/-- 中文说明：判断一个规范是否为 permission。 -/
def isPermission (n : Norm) : Prop :=
  n.modality = Modality.permission

/-- 中文说明：判断一个规范是否为 prohibition。 -/
def isProhibition (n : Norm) : Prop :=
  n.modality = Modality.prohibition

/-- 中文说明：判断一个规范是否为 constitutive status rule。 -/
def isConstitutive (n : Norm) : Prop :=
  n.modality = Modality.constitutive

/-- 中文说明：directViolation 只允许 obligation/prohibition 产生直接违反。 -/
def directViolation (n : Norm) (f : LegalFact) : Prop :=
  n.active = true ∧
  f.verified = true ∧
  f.slice = n.slice ∧
  (n.modality = Modality.obligation ∨ n.modality = Modality.prohibition)

/-- 中文说明：Defense 生效需要触发事实和证据均通过 verified gate。 -/
def defenseApplies (d : Defense) (f : LegalFact) : Prop :=
  f.id = d.trigger ∧ f.verified = true ∧ d.evidence.verified = true

/-- 中文说明：Exception 生效复用 Defense 的最小条件。 -/
def exceptionApplies (e : Exception) (f : LegalFact) : Prop :=
  defenseApplies e.defense f

/-- 中文说明：补救后果只和同一个规范 id 下的 violation 绑定。 -/
def remedialConsequence (v : Violation) (r : Reparation) : Prop :=
  v.normId = r.normId

/-- 中文说明：priority ordering 的最小接口要求优先级已激活且证据已核验。 -/
def priorityOrdering (p : Priority) : Prop :=
  p.active = true ∧ p.evidence.verified = true

/-- 中文说明：四个竖切使用同一个规范构造器，避免重复但保留 slice 标签。 -/
def sliceNorm (slice : SliceKind) (modality : Modality) (active : Bool := true) : Norm :=
  {
    id := "norm",
    modality := modality,
    actor := "party",
    action := "act",
    active := active,
    slice := slice
  }

/-- 中文说明：四个竖切使用同一个 verified fact 构造器。 -/
def sliceFact (slice : SliceKind) (verified : Bool := true) : LegalFact :=
  {
    id := "fact",
    predicate := "predicate",
    slice := slice,
    verified := verified
  }

/-- 中文证明：直接违反必然要求规范处于 active 状态。 -/
theorem violation_implies_norm_active {n : Norm} {f : LegalFact}
    (h : directViolation n f) : n.active = true :=
  h.1

/-- 中文证明：permission 不产生直接违反。 -/
theorem permission_no_direct_violation {n : Norm} {f : LegalFact}
    (hmod : n.modality = Modality.permission) :
    ¬ directViolation n f := by
  intro h
  rcases h with ⟨_, _, _, hmode⟩
  rcases hmode with hob | hproh
  · rw [hmod] at hob
    contradiction
  · rw [hmod] at hproh
    contradiction

/-- 中文证明：constitutive status rule 不产生直接违反。 -/
theorem constitutive_no_direct_violation {n : Norm} {f : LegalFact}
    (hmod : n.modality = Modality.constitutive) :
    ¬ directViolation n f := by
  intro h
  rcases h with ⟨_, _, _, hmode⟩
  rcases hmode with hob | hproh
  · rw [hmod] at hob
    contradiction
  · rw [hmod] at hproh
    contradiction

/-- 中文证明：permission 不能自动推出 obligation。 -/
theorem permission_does_not_imply_obligation {n : Norm}
    (hperm : isPermission n) : ¬ isObligation n := by
  intro hobl
  change n.modality = Modality.permission at hperm
  change n.modality = Modality.obligation at hobl
  rw [hperm] at hobl
  contradiction

/-- 中文证明：contract breach slice 的 obligation 可产生直接违反前提。 -/
theorem contract_breach_direct_violation_shape :
    directViolation
      (sliceNorm SliceKind.contractBreach Modality.obligation)
      (sliceFact SliceKind.contractBreach) := by
  unfold directViolation sliceNorm sliceFact
  simp

/-- 中文证明：license slice 的 permission 不会被混同为 obligation 违反。 -/
theorem license_permission_not_direct_violation :
    ¬ directViolation
      (sliceNorm SliceKind.license Modality.permission)
      (sliceFact SliceKind.license) := by
  exact permission_no_direct_violation rfl

/-- 中文证明：permission slice 保持 permission/prohibition 冲突由 AAF 处理。 -/
theorem permission_slice_permission_not_obligation :
    ¬ isObligation (sliceNorm SliceKind.permission Modality.permission) := by
  exact permission_does_not_imply_obligation rfl

/-- 中文证明：priority slice 的 ordering 需要已核验证据。 -/
theorem priority_ordering_requires_verified_evidence
    {p : Priority} (h : priorityOrdering p) : p.evidence.verified = true :=
  h.2

/-- 中文证明：补救后果不会跨 norm id 自动漂移。 -/
theorem remedial_consequence_same_norm
    {v : Violation} {r : Reparation} (h : remedialConsequence v r) :
    v.normId = r.normId :=
  h

end JurisLean
