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

/-- All source snapshots must be present and content-bound. -/
def CertificateEnvelopeV2.sourceSnapshotsBound (c : CertificateEnvelopeV2) : Bool :=
  match c.sourceSnapshots with
  | [] => false
  | bindings => bindings.all (fun binding => binding.matches)

/-- Required facts are recomputed from the envelope contents. -/
def CertificateEnvelopeV2.requiredFactsCovered (c : CertificateEnvelopeV2) : Bool :=
  decide (c.expectedFacts ⊆ c.usedFacts)

/-- Required obligations are recomputed from the envelope contents. -/
def CertificateEnvelopeV2.obligationsCovered (c : CertificateEnvelopeV2) : Bool :=
  decide (c.expectedObligations ⊆ c.dischargedObligations)

/-- Accepted arguments must have been constructed by the translation. -/
def CertificateEnvelopeV2.acceptedArgumentsBound (c : CertificateEnvelopeV2) : Bool :=
  decide (c.acceptedArguments ⊆ c.constructedArguments)

/-- The release boundary currently recognizes one task-bounded semantics contract. -/
def CertificateEnvelopeV2.knownSemantics (c : CertificateEnvelopeV2) : Bool :=
  c.semanticsId == "grounded" && c.semanticsVersion == "1"

/-- The release boundary recognizes only the v2 checker contract. -/
def CertificateEnvelopeV2.knownChecker (c : CertificateEnvelopeV2) : Bool :=
  c.checkerVersion == "certificate-checker-v2"

/-- Every acceptance prerequisite is recomputed from content rather than trusted flags. -/
def CertificateEnvelopeV2.contentReady (c : CertificateEnvelopeV2) : Bool :=
  c.trace.nonempty &&
    (c.requiredFactsCovered &&
      (c.obligationsCovered &&
        (c.acceptedArgumentsBound &&
          (c.sourceSnapshotsBound &&
            (c.rulePackDigest.matches &&
              (c.traceDigest.matches &&
                (c.knownSemantics &&
                  (c.knownChecker &&
                    (c.evidence.isAuditable && c.producerCommit != "")))))))))

/--
Authoritative v2 checker. A content failure rejects; a well-bound but non-decisive
status remains undecided. `accept` means that a decisive certificate is structurally valid,
not that an external hash implementation or runtime is proved correct by Lean.
-/
def checkCertificateV2 (c : CertificateEnvelopeV2) : CheckVerdict :=
  match c.contentReady, c.status with
  | false, _ => CheckVerdict.reject
  | true, DecisionStatus.proved => CheckVerdict.accept
  | true, DecisionStatus.refuted => CheckVerdict.accept
  | true, DecisionStatus.undecided => CheckVerdict.undecided
  | true, DecisionStatus.tainted => CheckVerdict.reject

/-- Legacy v1 input remains parseable but can never obtain a v2 decisive verdict. -/
def checkLegacyCertificateAsV2 (_certificate : Certificate) : CheckVerdict :=
  CheckVerdict.reject

/-- Acceptance implies that all content-derived prerequisites evaluated to true. -/
theorem checkerV2_acceptance_requires_content
    (c : CertificateEnvelopeV2)
    (h : checkCertificateV2 c = CheckVerdict.accept) :
    c.contentReady = true := by
  cases hready : c.contentReady with
  | false => simp [checkCertificateV2, hready] at h
  | true => rfl

/-- Acceptance implies a non-empty proof trace. -/
theorem checkerV2_acceptance_requires_nonempty_trace
    (c : CertificateEnvelopeV2)
    (h : checkCertificateV2 c = CheckVerdict.accept) :
    c.trace.nonempty = true := by
  have hready := checkerV2_acceptance_requires_content c h
  simp [CertificateEnvelopeV2.contentReady] at hready
  exact hready.1

/-- Acceptance implies recomputed coverage of every expected fact. -/
theorem checkerV2_acceptance_requires_fact_coverage
    (c : CertificateEnvelopeV2)
    (h : checkCertificateV2 c = CheckVerdict.accept) :
    c.requiredFactsCovered = true := by
  have hready := checkerV2_acceptance_requires_content c h
  simp [CertificateEnvelopeV2.contentReady] at hready
  exact hready.2.1

/-- Acceptance implies recomputed coverage of every expected obligation. -/
theorem checkerV2_acceptance_requires_obligation_coverage
    (c : CertificateEnvelopeV2)
    (h : checkCertificateV2 c = CheckVerdict.accept) :
    c.obligationsCovered = true := by
  have hready := checkerV2_acceptance_requires_content c h
  simp [CertificateEnvelopeV2.contentReady] at hready
  exact hready.2.2.1

/-- A legacy v1 certificate cannot be promoted into v2 acceptance. -/
theorem legacy_certificate_never_v2_accepted (c : Certificate) :
    checkLegacyCertificateAsV2 c ≠ CheckVerdict.accept := by
  simp [checkLegacyCertificateAsV2]

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
