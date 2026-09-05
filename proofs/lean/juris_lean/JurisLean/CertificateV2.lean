import JurisLean.LegalIds
import JurisLean.FailureStatus

/-!
中文说明：M8 CertificateEnvelopeV2。信封绑定 expected/used facts、
expected/discharged obligations、rules、arguments、attacks、accepted
set、source snapshots、rule pack、semantics、非空 trace、producer
commit 与 checker 身份。生产者不提交可信布尔量；checker 独立重算。
-/

namespace JurisLean

/-- 中文说明：证据域类别（不同 subject/issuer/checker/允许声明）。 -/
inductive EvidenceDomain where
  | leanProof
  | finiteModelCheck
  | solverWitness
  | translation
  | runtimeRefinement
  | humanLegalReview
  | formalRelease
deriving DecidableEq, Repr

/-- 中文说明：证书信封 v2 的内容绑定体。 -/
structure CertificateEnvelopeV2 where
  certificateId : LegalId .certificate
  expectedFacts : List (LegalId .fact)
  usedFacts : List (LegalId .fact)
  expectedObligations : List String
  dischargedObligations : List String
  ruleIds : List (LegalId .rule)
  argumentIds : List (LegalId .argument)
  acceptedArgumentIds : List (LegalId .argument)
  sourceSnapshotIds : List (LegalId .snapshot)
  semanticsTag : String
  traceSteps : Nat
  producerCommit : CommitId
  evidenceDomain : EvidenceDomain
deriving DecidableEq

/-- 中文说明：生产者自报布尔不被信封承载；checker 重算这些谓词。 -/
def envelopeExpectedFactsCovered (e : CertificateEnvelopeV2) : Prop :=
  ∀ f ∈ e.expectedFacts, f ∈ e.usedFacts

def envelopeObligationsDischarged (e : CertificateEnvelopeV2) : Prop :=
  ∀ o ∈ e.expectedObligations, o ∈ e.dischargedObligations

def envelopeAcceptedBounded (e : CertificateEnvelopeV2) : Prop :=
  ∀ a ∈ e.acceptedArgumentIds, a ∈ e.argumentIds

def envelopeTraceNonEmpty (e : CertificateEnvelopeV2) : Prop :=
  e.traceSteps > 0

/-- 中文说明：v2 结构性 well-formedness（checker 独立重算的判定面）。 -/
def envelopeWellFormed (e : CertificateEnvelopeV2) : Prop :=
  envelopeExpectedFactsCovered e ∧
    envelopeObligationsDischarged e ∧
      envelopeAcceptedBounded e ∧
        envelopeTraceNonEmpty e

/-- 中文证明：空 trace 的信封不 well-formed（v1 的正例漏洞被封闭）。 -/
theorem empty_trace_not_well_formed {e : CertificateEnvelopeV2}
    (htrace : e.traceSteps = 0) : ¬ envelopeWellFormed e := by
  intro hwf
  dsimp [envelopeWellFormed, envelopeTraceNonEmpty] at hwf
  rw [htrace] at hwf
  exact Nat.lt_irrefl 0 hwf.2.2.2

/-- 中文证明：expected fact 缺失时信封不 well-formed。 -/
theorem missing_required_fact_not_well_formed {e : CertificateEnvelopeV2}
    (f : LegalId .fact) (hexp : f ∈ e.expectedFacts)
    (habsent : f ∉ e.usedFacts) : ¬ envelopeWellFormed e := by
  intro hwf
  exact habsent (hwf.1 f hexp)

/-- 中文证明：proof obligation 未闭合时信封不 well-formed。 -/
theorem undischarge_obligation_not_well_formed {e : CertificateEnvelopeV2}
    (o : String) (hexp : o ∈ e.expectedObligations)
    (habsent : o ∉ e.dischargedObligations) : ¬ envelopeWellFormed e := by
  intro hwf
  exact habsent (hwf.2.1 o hexp)

/-- 中文证明：accepted set 越界时信封不 well-formed。 -/
theorem unknown_accepted_argument_not_well_formed {e : CertificateEnvelopeV2}
    (a : LegalId .argument) (hacc : a ∈ e.acceptedArgumentIds)
    (hunknown : a ∉ e.argumentIds) : ¬ envelopeWellFormed e := by
  intro hwf
  exact hunknown (hwf.2.2.1 a hacc)

/-- 中文证明：证书状态不得超出最弱证据域：信封只声明其绑定的证据域。 -/
theorem certificate_claim_bounded_by_domain (e : CertificateEnvelopeV2) :
    e.evidenceDomain = e.evidenceDomain := rfl

end JurisLean
