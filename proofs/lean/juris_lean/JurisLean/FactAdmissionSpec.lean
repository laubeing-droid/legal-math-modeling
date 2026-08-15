import JurisLean.LegalIds

/-!
中文说明：M3 P09 三门准入合同。source gate、interpretation gate、fact
gate 三门独立，各自状态为 PASS / FAIL / BLOCKED / DISPUTED。hash/content
binding 不蕴含 source authority；rule/checker/solver PASS 不蕴含 fact
reliability；candidate、user-assumed、disputed、revoked、expired
attestation 不能进入 decisive premise set。
-/

namespace JurisLean

/-- 中文说明：三门类别。 -/
inductive GateKind where
  | source
  | interpretation
  | fact
deriving DecidableEq, Repr

/-- 中文说明：每门独立状态。 -/
inductive GateState where
  | pass
  | fail
  | blocked
  | disputed
deriving DecidableEq, Repr

/-- 中文说明：三门状态记录。 -/
structure TripleGateStatus where
  sourceGate : GateState
  interpretationGate : GateState
  factGate : GateState
deriving DecidableEq

/-- 中文说明：attestation 状态；只有 admitted 可进入决定性前提。 -/
inductive AttestationStatus where
  | admitted
  | candidate
  | userAssumed
  | disputed
  | revoked
  | expired
deriving DecidableEq, Repr

/-- 中文说明：事实准入 attestation：绑定事实、来源、解释、case/run scope
与签发者权威。 -/
structure FactAdmissionAttestation where
  fact : LegalId .fact
  snapshot : LegalId .snapshot
  interpretationRef : String
  caseScope : CaseScope
  runScope : RunScope
  signer : String
  status : AttestationStatus
deriving DecidableEq

/-- 中文说明：decisive 前提集合要求全部 attestation 均为 admitted。 -/
def decisivePremiseSet (atts : List FactAdmissionAttestation) : Prop :=
  ∀ a ∈ atts, a.status = .admitted

/-- 中文说明：attestation 与请求上下文的精确绑定。 -/
def attestationBinds (a : FactAdmissionAttestation)
    (fact : LegalId .fact) (caseScope : CaseScope) (runScope : RunScope) : Prop :=
  a.fact = fact ∧ a.caseScope = caseScope ∧ a.runScope = runScope

/-- 中文证明：source PASS 不蕴含 interpretation PASS（三门独立，反例存在）。 -/
theorem source_pass_not_interpretation_pass :
    ∃ t : TripleGateStatus, t.sourceGate = .pass ∧ t.interpretationGate = .fail :=
  ⟨{ sourceGate := .pass, interpretationGate := .fail, factGate := .blocked }, by decide⟩

/-- 中文证明：interpretation PASS 不蕴含 fact PASS。 -/
theorem interpretation_pass_not_fact_pass :
    ∃ t : TripleGateStatus, t.interpretationGate = .pass ∧ t.factGate = .fail :=
  ⟨{ sourceGate := .pass, interpretationGate := .pass, factGate := .fail }, by decide⟩

/-- 中文证明：三门全 PASS 才允许准入判定；任何一门非 PASS 都阻塞。 -/
theorem admission_requires_all_gates_pass {t : TripleGateStatus}
    (h : t.sourceGate ≠ .pass ∨ t.interpretationGate ≠ .pass ∨ t.factGate ≠ .pass) :
    ¬ (t.sourceGate = .pass ∧ t.interpretationGate = .pass ∧ t.factGate = .pass) := by
  intro hall
  rcases h with h1 | h2 | h3
  · exact h1 hall.1
  · exact h2 hall.2.1
  · exact h3 hall.2.2

/-- 中文证明：candidate attestation 不能进入 decisive premise set。 -/
theorem candidate_not_decisive {a : FactAdmissionAttestation}
    (hcand : a.status = .candidate) :
    ¬ decisivePremiseSet [a] := by
  intro hdec
  have hadm := hdec a (by simp)
  rw [hcand] at hadm
  cases hadm

/-- 中文证明：user-assumed attestation 不能进入 decisive premise set。 -/
theorem user_assumed_not_decisive {a : FactAdmissionAttestation}
    (hassumed : a.status = .userAssumed) :
    ¬ decisivePremiseSet [a] := by
  intro hdec
  have hadm := hdec a (by simp)
  rw [hassumed] at hadm
  cases hadm

/-- 中文证明：revoked attestation 不能进入 decisive premise set。 -/
theorem revoked_not_decisive {a : FactAdmissionAttestation}
    (hrev : a.status = .revoked) :
    ¬ decisivePremiseSet [a] := by
  intro hdec
  have hadm := hdec a (by simp)
  rw [hrev] at hadm
  cases hadm

/-- 中文证明：expired attestation 不能进入 decisive premise set。 -/
theorem expired_not_decisive {a : FactAdmissionAttestation}
    (hexp : a.status = .expired) :
    ¬ decisivePremiseSet [a] := by
  intro hdec
  have hadm := hdec a (by simp)
  rw [hexp] at hadm
  cases hadm

/-- 中文证明：跨 case scope 的重放不保留绑定（准入不重放）。 -/
theorem cross_scope_replay_not_bound {a : FactAdmissionAttestation}
    {fact : LegalId .fact} {cs1 cs2 : CaseScope} {rs : RunScope}
    (hbind : attestationBinds a fact cs1 rs) (hdiff : cs1 ≠ cs2) :
    ¬ attestationBinds a fact cs2 rs := by
  intro hreplay
  exact hdiff (hbind.2.1.symm.trans hreplay.2.1)

/-- 中文证明：跨 run scope 的重放同样不保留绑定。 -/
theorem cross_run_replay_not_bound {a : FactAdmissionAttestation}
    {fact : LegalId .fact} {cs : CaseScope} {rs1 rs2 : RunScope}
    (hbind : attestationBinds a fact cs rs1) (hdiff : rs1 ≠ rs2) :
    ¬ attestationBinds a fact cs rs2 := by
  intro hreplay
  exact hdiff (hbind.2.2.symm.trans hreplay.2.2)

/-- 中文说明：撤销只改变目标 attestation 的状态。 -/
def revokeAttestation (target : LegalId .fact)
    (a : FactAdmissionAttestation) : FactAdmissionAttestation :=
  if a.fact = target then { a with status := .revoked } else a

/-- 中文证明：撤销后目标 attestation 状态变为 revoked。 -/
theorem revocation_sets_revoked {target : LegalId .fact}
    {a : FactAdmissionAttestation} (hmatch : a.fact = target) :
    (revokeAttestation target a).status = .revoked := by
  dsimp [revokeAttestation]
  split
  · rfl
  · contradiction

/-- 中文证明：撤销后目标 attestation 不再是 admitted。 -/
theorem revocation_removes_admission {target : LegalId .fact}
    {a : FactAdmissionAttestation} (hmatch : a.fact = target) :
    (revokeAttestation target a).status ≠ .admitted := by
  have hrevoked := revocation_sets_revoked hmatch
  intro hadm
  rw [hrevoked] at hadm
  cases hadm

/-- 中文证明：撤销单调地不影响其他 attestation（frame property）。 -/
theorem revocation_frame {target : LegalId .fact}
    {a b : FactAdmissionAttestation} (hother : b.fact ≠ target) :
    revokeAttestation target b = b := by
  dsimp [revokeAttestation]
  split
  · contradiction
  · rfl

end JurisLean
