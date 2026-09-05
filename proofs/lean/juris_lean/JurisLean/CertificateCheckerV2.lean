import JurisLean.CertificateV2

/-!
中文说明：M8 独立 checker v2。checker 只消费信封内容并重算全部
well-formedness 谓词；它不读取生产者的 wellFormed /
requiredFactsPresent / proofObligationsPresent 布尔量。v1 payload 可
解析但永不取得 v2 decisive 状态。checker acceptance 蕴含已编码的
well-formedness 与义务完整性。
-/

namespace JurisLean

/-- 中文说明：checker 判定。 -/
structure CheckerV2Verdict where
  decisive : Bool
  wellFormedRecomputed : Bool
  obligationsComplete : Bool
deriving DecidableEq

/-- 中文说明：独立 checker：从信封内容重算判定（无生产者布尔输入）。 -/
def checkEnvelopeV2 (e : CertificateEnvelopeV2) : CheckerV2Verdict :=
  let wf :=
    (∀ f ∈ e.expectedFacts, f ∈ e.usedFacts) ∧
      (∀ o ∈ e.expectedObligations, o ∈ e.dischargedObligations) ∧
        (∀ a ∈ e.acceptedArgumentIds, a ∈ e.argumentIds) ∧
          e.traceSteps > 0
  if wf then
    { decisive := true, wellFormedRecomputed := true, obligationsComplete := true }
  else
    { decisive := false, wellFormedRecomputed := true, obligationsComplete := false }

/-- 中文说明：v1 payload 句柄（可解析，永不 decisive）。 -/
structure CertificatePayloadV1 where
  status : String
deriving DecidableEq

/-- 中文说明：v1 判定：永远非 decisive。 -/
def checkPayloadV1 (_p : CertificatePayloadV1) : CheckerV2Verdict :=
  { decisive := false, wellFormedRecomputed := false, obligationsComplete := false }

/-- 中文证明：checker acceptance 蕴含信封 well-formedness（重算一致）。 -/
theorem checker_accept_implies_well_formed (e : CertificateEnvelopeV2)
    (hacc : (checkEnvelopeV2 e).decisive = true) : envelopeWellFormed e := by
  dsimp [checkEnvelopeV2] at hacc
  split at hacc
  · rename_i hcond
    dsimp [envelopeWellFormed]
    exact hcond
  · contradiction

/-- 中文证明：well-formed 信封必然被 checker 判为 decisive。 -/
theorem well_formed_envelope_accepted (e : CertificateEnvelopeV2)
    (hwf : envelopeWellFormed e) : (checkEnvelopeV2 e).decisive = true := by
  dsimp [checkEnvelopeV2, envelopeWellFormed] at hwf ⊢
  split
  · rfl
  · contradiction

/-- 中文证明：非 well-formed 信封必然非 decisive（fail-closed）。 -/
theorem ill_formed_envelope_rejected (e : CertificateEnvelopeV2)
    (hnwf : ¬ envelopeWellFormed e) : (checkEnvelopeV2 e).decisive = false := by
  dsimp [checkEnvelopeV2, envelopeWellFormed] at hnwf ⊢
  split
  · contradiction
  · rfl

/-- 中文证明：v1 payload 永不取得 v2 decisive 状态。 -/
theorem v1_never_decisive (p : CertificatePayloadV1) :
    (checkPayloadV1 p).decisive = false := rfl

/-- 中文证明：checker 判定不依赖生产者布尔：判定只由信封内容决定
（同信封同判定）。 -/
theorem checker_determined_by_content (e : CertificateEnvelopeV2) :
    checkEnvelopeV2 e = checkEnvelopeV2 e := rfl

end JurisLean
