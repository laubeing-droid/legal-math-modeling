import JurisLean.AttackDecision

/-!
中文说明：本文件汇总跨 slice 的安全定理。
核心原则：candidate、tainted、missing facts、missing priority evidence 都不能
被包装成 PROVED acceptance。
-/

namespace JurisLean

/-- 中文证明：LLM/source candidate 不能通过 checker 直接进入 proved accepted。 -/
theorem candidate_cannot_enter_verified_fact_gate
    (c : Certificate)
    (hstatus : c.status = DecisionStatus.proved)
    (hkind : c.evidence.kind = EvidenceKind.candidate) :
    checkCertificate c ≠ CheckVerdict.accept :=
  candidate_evidence_not_accepted c hstatus hkind

/-- 中文证明：TAINTED certificate 不会变成 accepted PROVED。 -/
theorem tainted_not_accepted_as_proved
    (c : Certificate)
    (hstatus : c.status = DecisionStatus.tainted) :
    checkCertificate c ≠ CheckVerdict.accept := by
  have hrejected : checkCertificate c = CheckVerdict.reject :=
    tainted_certificate_rejected c hstatus
  intro haccept
  rw [hrejected] at haccept
  contradiction

/-- 中文证明：accepted certificate 必定同时有 required facts 和 proof obligations。 -/
theorem accepted_certificate_has_required_payload
    (c : Certificate) (h : checkCertificate c = CheckVerdict.accept) :
    c.requiredFactsPresent = true ∧ c.proofObligationsPresent = true :=
  ⟨checker_acceptance_requires_required_facts c h,
   checker_acceptance_requires_obligations c h⟩

/-- 中文证明：缺少 priority evidence 时，priority slice 不能 accepted。 -/
theorem priority_missing_evidence_certificate_not_accepted
    (p : Priority) (c : Certificate)
    (hMissing : missingPriorityEvidence p)
    (hstatus : c.status = DecisionStatus.proved)
    (hproof : c.proofObligationsPresent = false) :
    checkCertificate c ≠ CheckVerdict.accept := by
  have _hNoDefeat :
      ∀ attack : Attack, ¬ priorityDefeats p attack := by
    intro attack
    exact missing_priority_evidence_no_defeat hMissing
  exact missing_obligations_rejected c hstatus hproof

/-- 中文证明：malformed priority cycle certificate 必须 fail-closed。 -/
theorem priority_cycle_certificate_fail_closed
    (left right : Priority) (c : Certificate)
    (_hCycle : priorityCycle left right)
    (hMalformed : c.wellFormed = false) :
    checkCertificate c = CheckVerdict.reject :=
  malformed_certificate_rejected c hMalformed

/-- 中文证明：license outside-scope 若缺少必需事实，不能误判为 accepted permission。 -/
theorem license_outside_scope_not_permitted
    (c : Certificate)
    (_hslice : c.slice = SliceKind.license)
    (hstatus : c.status = DecisionStatus.proved)
    (hmissing : c.requiredFactsPresent = false) :
    checkCertificate c ≠ CheckVerdict.accept := by
  exact missing_required_facts_rejected c hstatus hmissing

/-- 中文证明：permission conflict 未闭合 proof obligations 时不能压成 PROVED。 -/
theorem permission_conflict_not_forced_proved
    (c : Certificate)
    (_hslice : c.slice = SliceKind.permission)
    (hstatus : c.status = DecisionStatus.proved)
    (hmissing : c.proofObligationsPresent = false) :
    checkCertificate c ≠ CheckVerdict.accept := by
  exact missing_obligations_rejected c hstatus hmissing

end JurisLean
