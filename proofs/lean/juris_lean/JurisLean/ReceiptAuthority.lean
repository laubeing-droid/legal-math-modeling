import JurisLean.LegalIds

/-!
中文说明：M3/M7 receipt authority。权威层级格：
UNTRUSTED_PROPOSAL < SOURCE_BOUND_CANDIDATE < HUMAN_REVIEWED_CANDIDATE
< ADMITTED_FORMAL_INPUT。层级不能由数量、置信度、模型身份或重复运行
自动提升；晋级需要独立且 scope-bound 的外部 authority receipt。
-/

namespace JurisLean

/-- 中文说明：权威层级。 -/
inductive AuthorityLevel where
  | untrustedProposal
  | sourceBoundCandidate
  | humanReviewedCandidate
  | admittedFormalInput
deriving DecidableEq, Repr

/-- 中文说明：层级数值秩；用于比较证明。 -/
def authorityRank : AuthorityLevel → Nat
  | .untrustedProposal => 0
  | .sourceBoundCandidate => 1
  | .humanReviewedCandidate => 2
  | .admittedFormalInput => 3

/-- 中文说明：可签发的制品类别。 -/
inductive ArtifactKind where
  | proposal
  | sourceBinding
  | factAttestation
  | certificate
  | decisionStatus
deriving DecidableEq, Repr

/-- 中文说明：签发权限表：制品需要的最低层级。 -/
def requiredLevel : ArtifactKind → AuthorityLevel
  | .proposal => .untrustedProposal
  | .sourceBinding => .sourceBoundCandidate
  | .factAttestation => .admittedFormalInput
  | .certificate => .admittedFormalInput
  | .decisionStatus => .admittedFormalInput

/-- 中文说明：层级 l 是否可签发制品 k。 -/
def canIssue (l : AuthorityLevel) (k : ArtifactKind) : Prop :=
  authorityRank l ≥ authorityRank (requiredLevel k)

/-- 中文说明：外部 authority receipt：晋级凭证，绑定对象、scope 与签发者。 -/
structure AuthorityReceipt where
  subject : String
  caseScope : CaseScope
  issuer : String
  fromLevel : AuthorityLevel
  toLevel : AuthorityLevel
deriving DecidableEq

/-- 中文说明：receipt 有效的前提：严格晋级且绑定 scope。 -/
def receiptValid (r : AuthorityReceipt) : Prop :=
  authorityRank r.toLevel = authorityRank r.fromLevel + 1

/-- 中文证明：proposal 层级不能签发 fact attestation。 -/
theorem proposal_cannot_issue_attestation :
    ¬ canIssue .untrustedProposal .factAttestation := by
  dsimp [canIssue, authorityRank, requiredLevel]
  decide

/-- 中文证明：proposal 层级不能签发证书。 -/
theorem proposal_cannot_issue_certificate :
    ¬ canIssue .untrustedProposal .certificate := by
  dsimp [canIssue, authorityRank, requiredLevel]
  decide

/-- 中文证明：proposal 层级不能签发 DecisionStatus。 -/
theorem proposal_cannot_issue_decision_status :
    ¬ canIssue .untrustedProposal .decisionStatus := by
  dsimp [canIssue, authorityRank, requiredLevel]
  decide

/-- 中文证明：human-reviewed 候选仍不能直接签发正式制品。 -/
theorem human_review_not_formal_input :
    ¬ canIssue .humanReviewedCandidate .certificate := by
  dsimp [canIssue, authorityRank, requiredLevel]
  decide

/-- 中文证明：层级严格有序：低层级的秩严格小于高层级。 -/
theorem authority_strictly_ordered :
    authorityRank .untrustedProposal < authorityRank .sourceBoundCandidate ∧
      authorityRank .sourceBoundCandidate < authorityRank .humanReviewedCandidate ∧
        authorityRank .humanReviewedCandidate < authorityRank .admittedFormalInput := by
  decide

/-- 中文证明：无效 receipt（跳级）不能作为晋级凭证。 -/
theorem skipping_receipt_invalid {r : AuthorityReceipt}
    (hskip : authorityRank r.toLevel ≠ authorityRank r.fromLevel + 1) :
    ¬ receiptValid r := by
  intro hv
  exact hskip hv

/-- 中文说明：多 Agent 共识的层级取各层级秩的最大值。 -/
def consensusRank (levels : List AuthorityLevel) : Nat :=
  levels.foldr (fun l acc => max (authorityRank l) acc) 0

/-- 中文证明：同一层级的任意多数共识不产生层级提升。 -/
theorem consensus_does_not_escalate (l : AuthorityLevel) (n : Nat) :
    consensusRank (List.replicate n l) ≤ authorityRank l := by
  induction n with
  | zero =>
    dsimp [consensusRank, List.replicate]
    exact Nat.zero_le (authorityRank l)
  | succ n ih =>
    dsimp [consensusRank, List.replicate]
    rw [Nat.max_eq_left ih]
    exact le_rfl

end JurisLean
