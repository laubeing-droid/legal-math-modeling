import JurisLean.LegalSyntax

/-!
中文说明：本文件定义 specification-side certificate checker 的 fail-closed
边界。checker 只接受 well-formed、verified、非 candidate、且 obligations
齐备的 PROVED certificate。
-/

namespace JurisLean

/-- 中文说明：checker 的三值输出；reject 和 undecided 都不是 proved 接受。 -/
inductive CheckVerdict where
  | accept
  | reject
  | undecided
deriving DecidableEq, Repr

/-- 中文说明：证书是否携带足以支撑 decisive verdict 的强证据。 -/
def Certificate.hasStrongEvidence (c : Certificate) : Bool :=
  c.evidence.verified && c.evidence.kind != EvidenceKind.candidate

/-- 中文说明：fail-closed checker；任何缺失、污染或候选证据都不得 accepted。 -/
def checkCertificate (c : Certificate) : CheckVerdict :=
  match c.wellFormed, c.status, c.evidence.kind,
      c.evidence.verified, c.requiredFactsPresent, c.proofObligationsPresent with
  | false, _, _, _, _, _ => CheckVerdict.reject
  | true, DecisionStatus.tainted, _, _, _, _ => CheckVerdict.reject
  | true, DecisionStatus.proved, EvidenceKind.candidate, _, _, _ => CheckVerdict.reject
  | true, DecisionStatus.proved, _, true, true, true => CheckVerdict.accept
  | true, DecisionStatus.proved, _, _, _, _ => CheckVerdict.reject
  | true, _, _, _, _, _ => CheckVerdict.undecided

/-- 中文证明：malformed certificate 必须 reject。 -/
theorem malformed_certificate_rejected (c : Certificate)
    (h : c.wellFormed = false) :
    checkCertificate c = CheckVerdict.reject := by
  rcases c with ⟨id, slice, status, evidence, trace, wellFormed,
    requiredFactsPresent, proofObligationsPresent⟩
  rcases evidence with ⟨evidenceId, kind, verified, trust⟩
  cases wellFormed <;> cases status <;> cases kind <;> cases verified <;>
    cases requiredFactsPresent <;> cases proofObligationsPresent <;>
    simp [checkCertificate] at h ⊢

/-- 中文证明：TAINTED 状态不能被 checker 接受为 proved。 -/
theorem tainted_certificate_rejected (c : Certificate)
    (h : c.status = DecisionStatus.tainted) :
    checkCertificate c = CheckVerdict.reject := by
  rcases c with ⟨id, slice, status, evidence, trace, wellFormed,
    requiredFactsPresent, proofObligationsPresent⟩
  rcases evidence with ⟨evidenceId, kind, verified, trust⟩
  cases wellFormed <;> cases status <;> cases kind <;> cases verified <;>
    cases requiredFactsPresent <;> cases proofObligationsPresent <;>
    simp [checkCertificate] at h ⊢

/-- 中文证明：candidate evidence 不能支撑 accepted PROVED。 -/
theorem candidate_evidence_not_accepted (c : Certificate)
    (hstatus : c.status = DecisionStatus.proved)
    (hkind : c.evidence.kind = EvidenceKind.candidate) :
    checkCertificate c ≠ CheckVerdict.accept := by
  rcases c with ⟨id, slice, status, evidence, trace, wellFormed,
    requiredFactsPresent, proofObligationsPresent⟩
  rcases evidence with ⟨evidenceId, kind, verified, trust⟩
  cases wellFormed <;> cases status <;> cases kind <;> cases verified <;>
    cases requiredFactsPresent <;> cases proofObligationsPresent <;>
    simp [checkCertificate] at hstatus hkind ⊢

/-- 中文证明：缺少必需事实时，PROVED certificate 必须 fail-closed。 -/
theorem missing_required_facts_rejected (c : Certificate)
    (hstatus : c.status = DecisionStatus.proved)
    (hmissing : c.requiredFactsPresent = false) :
    checkCertificate c ≠ CheckVerdict.accept := by
  rcases c with ⟨id, slice, status, evidence, trace, wellFormed,
    requiredFactsPresent, proofObligationsPresent⟩
  rcases evidence with ⟨evidenceId, kind, verified, trust⟩
  cases wellFormed <;> cases status <;> cases kind <;> cases verified <;>
    cases requiredFactsPresent <;> cases proofObligationsPresent <;>
    simp [checkCertificate] at hstatus hmissing ⊢

/-- 中文证明：缺少 proof obligations 时，PROVED certificate 必须 fail-closed。 -/
theorem missing_obligations_rejected (c : Certificate)
    (hstatus : c.status = DecisionStatus.proved)
    (hmissing : c.proofObligationsPresent = false) :
    checkCertificate c ≠ CheckVerdict.accept := by
  rcases c with ⟨id, slice, status, evidence, trace, wellFormed,
    requiredFactsPresent, proofObligationsPresent⟩
  rcases evidence with ⟨evidenceId, kind, verified, trust⟩
  cases wellFormed <;> cases status <;> cases kind <;> cases verified <;>
    cases requiredFactsPresent <;> cases proofObligationsPresent <;>
    simp [checkCertificate] at hstatus hmissing ⊢

/-- 中文证明：checker 接受意味着所有 proof obligations 存在。 -/
theorem checker_acceptance_requires_obligations (c : Certificate)
    (h : checkCertificate c = CheckVerdict.accept) :
    c.proofObligationsPresent = true := by
  rcases c with ⟨id, slice, status, evidence, trace, wellFormed,
    requiredFactsPresent, proofObligationsPresent⟩
  rcases evidence with ⟨evidenceId, kind, verified, trust⟩
  cases wellFormed <;> cases status <;> cases kind <;> cases verified <;>
    cases requiredFactsPresent <;> cases proofObligationsPresent <;>
    simp [checkCertificate] at h ⊢

/-- 中文证明：checker 接受意味着必需事实存在。 -/
theorem checker_acceptance_requires_required_facts (c : Certificate)
    (h : checkCertificate c = CheckVerdict.accept) :
    c.requiredFactsPresent = true := by
  rcases c with ⟨id, slice, status, evidence, trace, wellFormed,
    requiredFactsPresent, proofObligationsPresent⟩
  rcases evidence with ⟨evidenceId, kind, verified, trust⟩
  cases wellFormed <;> cases status <;> cases kind <;> cases verified <;>
    cases requiredFactsPresent <;> cases proofObligationsPresent <;>
    simp [checkCertificate] at h ⊢

/-- 中文证明：checker 接受意味着证据不是 candidate。 -/
theorem checker_acceptance_requires_non_candidate (c : Certificate)
    (h : checkCertificate c = CheckVerdict.accept) :
    c.evidence.kind ≠ EvidenceKind.candidate := by
  rcases c with ⟨id, slice, status, evidence, trace, wellFormed,
    requiredFactsPresent, proofObligationsPresent⟩
  rcases evidence with ⟨evidenceId, kind, verified, trust⟩
  cases wellFormed <;> cases status <;> cases kind <;> cases verified <;>
    cases requiredFactsPresent <;> cases proofObligationsPresent <;>
    simp [checkCertificate] at h ⊢

end JurisLean
