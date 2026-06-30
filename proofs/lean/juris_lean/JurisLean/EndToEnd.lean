import JurisLean.SafetyTheorems

/-!
中文说明：本文件把 contract breach、license、permission、priority 四个竖切
连接到 canonical types、DDL minimal core、Horn->AAF contract 与 certificate
checker fail-closed theorem。
-/

namespace JurisLean

/-- 中文说明：空 trace 仅用于检查 certificate gate，不代表真实 proof trace。 -/
def emptyTrace : ProofTrace :=
  {
    facts := ∅,
    rules := ∅,
    arguments := ∅,
    attacks := ∅
  }

/-- 中文说明：已核验的 formal backend 证据。 -/
def verifiedBackendEvidence : Evidence :=
  {
    id := "evidence::backend",
    kind := EvidenceKind.formalBackend,
    verified := true,
    trust := TrustLabel.disclosePublic
  }

/-- 中文说明：未核验候选证据，用于证明 candidate 不得入 verified gate。 -/
def candidateEvidence : Evidence :=
  {
    id := "evidence::candidate",
    kind := EvidenceKind.candidate,
    verified := false,
    trust := TrustLabel.needsReview
  }

/-- 中文说明：构造一个四个 slice 共用的 ready certificate。 -/
def readyCertificate (slice : SliceKind) : Certificate :=
  {
    id := "certificate::ready",
    slice := slice,
    status := DecisionStatus.proved,
    evidence := verifiedBackendEvidence,
    trace := emptyTrace,
    wellFormed := true,
    requiredFactsPresent := true,
    proofObligationsPresent := true
  }

/-- 中文说明：构造缺少必需事实的 certificate。 -/
def missingFactsCertificate (slice : SliceKind) : Certificate :=
  {
    id := "certificate::missing-facts",
    slice := slice,
    status := DecisionStatus.proved,
    evidence := verifiedBackendEvidence,
    trace := emptyTrace,
    wellFormed := true,
    requiredFactsPresent := false,
    proofObligationsPresent := true
  }

/-- 中文说明：构造缺少 proof obligations 的 certificate。 -/
def missingObligationsCertificate (slice : SliceKind) : Certificate :=
  {
    id := "certificate::missing-obligations",
    slice := slice,
    status := DecisionStatus.proved,
    evidence := verifiedBackendEvidence,
    trace := emptyTrace,
    wellFormed := true,
    requiredFactsPresent := true,
    proofObligationsPresent := false
  }

/-- 中文说明：构造 malformed certificate。 -/
def malformedCertificate (slice : SliceKind) : Certificate :=
  {
    id := "certificate::malformed",
    slice := slice,
    status := DecisionStatus.proved,
    evidence := verifiedBackendEvidence,
    trace := emptyTrace,
    wellFormed := false,
    requiredFactsPresent := true,
    proofObligationsPresent := true
  }

/-- 中文说明：构造 candidate evidence certificate。 -/
def candidateCertificate (slice : SliceKind) : Certificate :=
  {
    id := "certificate::candidate",
    slice := slice,
    status := DecisionStatus.proved,
    evidence := candidateEvidence,
    trace := emptyTrace,
    wellFormed := true,
    requiredFactsPresent := true,
    proofObligationsPresent := true
  }

/-- 中文证明：contract breach ready path 可被 checker 接受。 -/
theorem contract_breach_ready_certificate_accepted :
    checkCertificate (readyCertificate SliceKind.contractBreach) =
      CheckVerdict.accept := rfl

/-- 中文证明：contract breach 缺少 defense/obligation payload 时 fail-closed。 -/
theorem contract_breach_missing_defense_fail_closed :
    checkCertificate
      (missingObligationsCertificate SliceKind.contractBreach) ≠
      CheckVerdict.accept := by
  exact missing_obligations_rejected
    (missingObligationsCertificate SliceKind.contractBreach) rfl rfl

/-- 中文证明：license ready path 可被 checker 接受。 -/
theorem license_ready_certificate_accepted :
    checkCertificate (readyCertificate SliceKind.license) =
      CheckVerdict.accept := rfl

/-- 中文证明：license outside-scope 缺事实时不能误判 permitted。 -/
theorem license_outside_scope_fail_closed :
    checkCertificate (missingFactsCertificate SliceKind.license) ≠
      CheckVerdict.accept := by
  exact license_outside_scope_not_permitted
    (missingFactsCertificate SliceKind.license) rfl rfl rfl

/-- 中文证明：permission ready path 可被 checker 接受。 -/
theorem permission_ready_certificate_accepted :
    checkCertificate (readyCertificate SliceKind.permission) =
      CheckVerdict.accept := rfl

/-- 中文证明：permission/prohibition conflict 未闭合 obligations 时不能压成 PROVED。 -/
theorem permission_conflict_fail_closed :
    checkCertificate (missingObligationsCertificate SliceKind.permission) ≠
      CheckVerdict.accept := by
  exact permission_conflict_not_forced_proved
    (missingObligationsCertificate SliceKind.permission) rfl rfl rfl

/-- 中文证明：priority ready path 可被 checker 接受。 -/
theorem priority_ready_certificate_accepted :
    checkCertificate (readyCertificate SliceKind.priority) =
      CheckVerdict.accept := rfl

/-- 中文证明：priority cycle 的 malformed certificate 必须 reject。 -/
theorem priority_cycle_fail_closed :
    checkCertificate (malformedCertificate SliceKind.priority) =
      CheckVerdict.reject := by
  let ev := verifiedBackendEvidence
  let left : Priority :=
    {
      id := "priority::left",
      higher := "arg::a",
      lower := "arg::b",
      evidence := ev,
      active := true
    }
  let right : Priority :=
    {
      id := "priority::right",
      higher := "arg::b",
      lower := "arg::a",
      evidence := ev,
      active := true
    }
  have hCycle : priorityCycle left right := by
    unfold priorityCycle left right
    simp
  exact priority_cycle_certificate_fail_closed
    left right (malformedCertificate SliceKind.priority) hCycle rfl

/-- 中文证明：candidate certificate 不能进入任何 slice 的 verified fact gate。 -/
theorem candidate_certificate_fail_closed (slice : SliceKind) :
    checkCertificate (candidateCertificate slice) ≠ CheckVerdict.accept := by
  exact candidate_cannot_enter_verified_fact_gate
    (candidateCertificate slice) rfl rfl

/-- 中文证明：End-to-end accepted certificate 必须保留 required payload。 -/
theorem end_to_end_acceptance_requires_payload
    (slice : SliceKind)
    (h : checkCertificate (readyCertificate slice) = CheckVerdict.accept) :
    (readyCertificate slice).requiredFactsPresent = true ∧
      (readyCertificate slice).proofObligationsPresent = true :=
  accepted_certificate_has_required_payload (readyCertificate slice) h

end JurisLean
