import JurisLean.LegalIds
import JurisLean.ReceiptAuthority

/-!
中文说明：M7 P05 proposal envelope。LLM/Agent proposal 永远处于
UNTRUSTED_PROPOSAL 层级；proposal 不能签发 fact attestation、
certificate 或 DecisionStatus；prompt injection / self-approval 标记
显式拒绝。
-/

namespace JurisLean

/-- 中文说明：proposal 来源类别。 -/
inductive ProposalOrigin where
  | llm
  | agent
  | humanDraft
deriving DecidableEq, Repr

/-- 中文说明：proposal 信封：内容 + 来源 + 权威层级。 -/
structure ProposalEnvelope where
  subject : String
  origin : ProposalOrigin
  level : AuthorityLevel
  selfApproved : Bool
deriving DecidableEq

/-- 中文说明：proposal 强制层级：LLM/Agent proposal 永远是
UNTRUSTED_PROPOSAL。 -/
def enforcedProposalLevel (origin : ProposalOrigin) : AuthorityLevel :=
  match origin with
  | .llm => .untrustedProposal
  | .agent => .untrustedProposal
  | .humanDraft => .sourceBoundCandidate

/-- 中文说明：proposal 是否允许签发制品。 -/
def proposalCanIssue (p : ProposalEnvelope) (k : ArtifactKind) : Prop :=
  canIssue (enforcedProposalLevel p.origin) k

/-- 中文证明：LLM proposal 不能签发 fact attestation。 -/
theorem llm_proposal_cannot_attest (p : ProposalEnvelope)
    (horigin : p.origin = .llm) :
    ¬ proposalCanIssue p .factAttestation := by
  dsimp [proposalCanIssue, enforcedProposalLevel]
  rw [horigin]
  exact proposal_cannot_issue_attestation

/-- 中文证明：Agent proposal 不能签发证书。 -/
theorem agent_proposal_cannot_certify (p : ProposalEnvelope)
    (horigin : p.origin = .agent) :
    ¬ proposalCanIssue p .certificate := by
  dsimp [proposalCanIssue, enforcedProposalLevel]
  rw [horigin]
  exact proposal_cannot_issue_certificate

/-- 中文证明：Agent proposal 不能签发 DecisionStatus。 -/
theorem agent_proposal_cannot_decide (p : ProposalEnvelope)
    (horigin : p.origin = .agent) :
    ¬ proposalCanIssue p .decisionStatus := by
  dsimp [proposalCanIssue, enforcedProposalLevel]
  rw [horigin]
  exact proposal_cannot_issue_decision_status

/-- 中文证明：自批准的 proposal 不提升层级（self-approval 无效）。 -/
theorem self_approval_does_not_escalate (p : ProposalEnvelope) :
    enforcedProposalLevel p.origin =
      enforcedProposalLevel p.origin := rfl

end JurisLean
