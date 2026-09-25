import JurisLean.Genealogy.Part5

/-!
Genealogy Part6 — L6 / cross-cutting delivery, suppression, lifecycle,
idempotence, and human-gate disciplines. No theorem asserts substantive legal correctness.
-/

namespace JurisLean.Genealogy.Part6

namespace P105

inductive ProceduralDisposition where
  | file
  | answer
  | crossExamine
  | dismiss
  | suspend
  | terminate
 deriving DecidableEq, Repr

def legalEdge : ProceduralDisposition → ProceduralDisposition → Bool
  | .file, .answer => true
  | .answer, .crossExamine => true
  | .crossExamine, .dismiss => true
  | .crossExamine, .suspend => true
  | .suspend, .terminate => true
  | _, _ => false

def sequenceValid : List ProceduralDisposition → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => legalEdge a b && sequenceValid (b :: rest)

/-- A listed procedural path is valid. -/
theorem disposition_valid_path :
    sequenceValid [.file, .answer, .crossExamine, .suspend, .terminate] = true := by
  decide
-- [decide] 置信：四条相邻边均在有限边表中。

/-- A direct file→terminate jump is invalid. -/
theorem disposition_invalid_jump :
    sequenceValid [.file, .terminate] = false := rfl
-- [rfl] 置信：file→terminate 直接落入 legalEdge wildcard=false。

end P105

namespace P106

structure LitigationSubject where
  causeOfAction : String
  partyA : String
  partyB : String
 deriving DecidableEq, Repr

def sameText (a b : String) : Bool := decide (a = b)

def samePartiesUnordered (a b : LitigationSubject) : Bool :=
  (sameText a.partyA b.partyA && sameText a.partyB b.partyB) ||
  (sameText a.partyA b.partyB && sameText a.partyB b.partyA)

def sameSubject (a b : LitigationSubject) : Bool :=
  sameText a.causeOfAction b.causeOfAction && samePartiesUnordered a b

/-- Same cause plus the same two parties is order-insensitive. -/
theorem swapped_parties_same_subject :
    sameSubject
      { causeOfAction := "COA", partyA := "A", partyB := "B" }
      { causeOfAction := "COA", partyA := "B", partyB := "A" } = true := by
  decide
-- [decide] 置信：字符串字面量相等性与 Bool 组合闭式计算。

/-- Different causes are not the same subject even with identical parties. -/
theorem different_cause_not_same_subject :
    sameSubject
      { causeOfAction := "X", partyA := "A", partyB := "B" }
      { causeOfAction := "Y", partyA := "A", partyB := "B" } = false := by
  decide
-- [decide] 置信：首个 cause equality 为 false，使合取为 false。

end P106

namespace P107

inductive AssetVerdict where
  | deliveryAssetOk
  | rejectedMasquerade
 deriving DecidableEq, Repr

structure ScriptAsset where
  assetId : String
  containsLegalFactAssertions : Bool
 deriving DecidableEq, Repr

def receiptVerdict (a : ScriptAsset) : AssetVerdict :=
  match a.containsLegalFactAssertions with
  | true => .rejectedMasquerade
  | false => .deliveryAssetOk

/-- Script assets containing legal-fact assertions are rejected. -/
theorem legal_fact_script_rejected (id : String) :
    receiptVerdict { assetId := id, containsLegalFactAssertions := true }
      = .rejectedMasquerade := rfl
-- [rfl] 置信：true 分支固定返回 rejectedMasquerade。

end P107

namespace P121

structure Proposal where
  proposalId : String
  source : String
  admitted : Bool
 deriving DecidableEq, Repr

inductive ProposalGrade where
  | candidateOnly
  | admittedCandidate
 deriving DecidableEq, Repr

def grade (p : Proposal) : ProposalGrade :=
  match p.admitted with
  | false => .candidateOnly
  | true => .admittedCandidate

def admitProposal (gatePassed : Bool) (p : Proposal) : Proposal :=
  match gatePassed with
  | false => p
  | true => { p with admitted := true }

/-- A failed gate leaves the proposal untouched. -/
theorem failed_gate_keeps_candidate (p : Proposal) :
    admitProposal false p = p := rfl
-- [rfl] 置信：gate=false 分支直接返回原 p。

/-- A passed gate sets admitted=true. -/
theorem passed_gate_sets_admitted (p : Proposal) :
    (admitProposal true p).admitted = true := rfl
-- [rfl] 置信：record update 对 admitted 字段直接写 true。

end P121

namespace P122

structure VersionDiscipline where
  sourceVersion : String
  modelVersion : String
  dataVersion : String
 deriving DecidableEq, Repr

def bound (v : VersionDiscipline) : String :=
  v.sourceVersion ++ "|" ++ v.modelVersion ++ "|" ++ v.dataVersion

/-- The source/model/data triplet is bound by one deterministic concatenation. -/
theorem version_triplet_binding_identity (v : VersionDiscipline) :
    bound v = v.sourceVersion ++ "|" ++ v.modelVersion ++ "|" ++ v.dataVersion := rfl
-- [rfl] 置信：定理右侧即字符串拼接定义体。

end P122

namespace P124

structure DisclosureRecord where
  corpusVersion : String
  disclosed : Bool
 deriving DecidableEq, Repr

def compliant (r : DisclosureRecord) : Bool := r.disclosed

/-- Disclosure is the compliance gate. -/
theorem disclosed_is_compliant (version : String) :
    compliant { corpusVersion := version, disclosed := true } = true := rfl
-- [rfl] 置信：compliant 仅投影 disclosed 字段。

/-- Nondisclosure is noncompliant. -/
theorem undisclosed_is_noncompliant (version : String) :
    compliant { corpusVersion := version, disclosed := false } = false := rfl
-- [rfl] 置信：同上，字段为 false。

end P124

namespace P125

inductive HallucinationPattern where
  | fabricatedDocket
  | fabricatedStatute
  | fabricatedFact
 deriving DecidableEq, Repr

def blockHallucination : List HallucinationPattern → Bool
  | [] => false
  | _ :: _ => true

/-- Any detected hallucination pattern blocks output. -/
theorem detected_pattern_blocks (p : HallucinationPattern) (ps : List HallucinationPattern) :
    blockHallucination (p :: ps) = true := rfl
-- [rfl] 置信：非空列表固定返回 true。

end P125

namespace P126

structure ConceptUse where
  conceptId : String
  homeJurisdiction : String
  adapted : Bool
 deriving DecidableEq, Repr

def smugglingBlocked (u : ConceptUse) (analysisJurisdiction : String) : Bool :=
  if h : u.homeJurisdiction = analysisJurisdiction then false
  else match u.adapted with | true => false | false => true

/-- Cross-jurisdiction use without adaptation is blocked. -/
theorem foreign_unadapted_blocked
    (u : ConceptUse) (analysisJurisdiction : String)
    (h : u.homeJurisdiction ≠ analysisJurisdiction) :
    smugglingBlocked { u with adapted := false } analysisJurisdiction = true := by
  simp [smugglingBlocked, h]
-- [定义展开] 置信：跨辖区条件由 `h` 锁死，adapted=false 再归约为 true。

/-- Same-jurisdiction use is not blocked by this cross-jurisdiction gate. -/
theorem home_jurisdiction_not_blocked (u : ConceptUse) :
    smugglingBlocked u u.homeJurisdiction = false := by
  simp [smugglingBlocked]
-- [定义展开] 置信：jurisdiction 与自身相等，首分支固定 false。

end P126

namespace P127

/-- Prefix-only verbatim checker; substring search is intentionally not claimed here. -/
def isPrefixChars : List Char → List Char → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
      if h : a = b then isPrefixChars as bs else false

def verbatimPrefix (cited snapshot : String) : Bool :=
  isPrefixChars cited.toList snapshot.toList

/-- Concrete verbatim-prefix hit. -/
theorem verbatim_prefix_hit_witness :
    verbatimPrefix "Article 1" "Article 1 text" = true := by
  decide
-- [decide] 置信：String.toList 后仅做有限 Char 相等递归。

/-- Concrete verbatim-prefix miss. -/
theorem verbatim_prefix_miss_witness :
    verbatimPrefix "Article 2" "Article 1 text" = false := by
  decide
-- [decide] 置信：首个不同 Char 位置有限闭式判定。

end P127

namespace P128

structure DueProcessPresence where
  notice : Bool
  opportunityToBeHeard : Bool
  reasonsRecorded : Bool
 deriving DecidableEq, Repr

def satisfied (p : DueProcessPresence) : Bool :=
  p.notice && p.opportunityToBeHeard && p.reasonsRecorded

/-- All three mapped due-process elements are required. -/
theorem all_due_process_elements_present :
    satisfied { notice := true, opportunityToBeHeard := true, reasonsRecorded := true } = true := rfl
-- [rfl] 置信：三 Bool 字面量合取归约。

/-- A missing mapped element fails the gate. -/
theorem missing_reason_record_fails :
    satisfied { notice := true, opportunityToBeHeard := true, reasonsRecorded := false } = false := rfl
-- [rfl] 置信：末项 false 使合取为 false。

end P128

namespace P129

structure AnonymizationBoundary where
  anonymized : Bool
  reidentificationTested : Bool
 deriving DecidableEq, Repr

def withinBoundary (b : AnonymizationBoundary) : Bool :=
  b.anonymized && b.reidentificationTested

/-- Both anonymization and re-identification testing are required. -/
theorem anonymization_boundary_two_conditions :
    withinBoundary { anonymized := true, reidentificationTested := true } = true := rfl
-- [rfl] 置信：true && true 直接归约。

end P129

namespace P130

inductive LifecycleState where
  | intake
  | active
  | suspended
  | closed
  | archived
 deriving DecidableEq, Repr

def lifecycleEdge : LifecycleState → LifecycleState → Bool
  | .intake, .active => true
  | .active, .suspended => true
  | .suspended, .active => true
  | .active, .closed => true
  | .closed, .archived => true
  | _, _ => false

/-- A listed lifecycle edge is valid. -/
theorem lifecycle_listed_edge_valid :
    lifecycleEdge .closed .archived = true := rfl
-- [rfl] 置信：显式边表直接命中。

/-- An unlisted lifecycle edge is invalid. -/
theorem lifecycle_unlisted_edge_invalid :
    lifecycleEdge .intake .archived = false := rfl
-- [rfl] 置信：未列边进入 wildcard=false。

end P130

namespace P131

def hasCommand (commandId : String) : List (String × String) → Bool
  | [] => false
  | (existingId, _) :: rest =>
      if h : existingId = commandId then true else hasCommand commandId rest

def effectLogApply
    (log : List (String × String)) (commandId effect : String) : List (String × String) :=
  match hasCommand commandId log with
  | true => log
  | false => (commandId, effect) :: log

/-- Applying the same command twice to an empty log has the same result as once. -/
theorem replay_empty_log_idempotent (commandId effect : String) :
    effectLogApply (effectLogApply [] commandId effect) commandId effect =
      effectLogApply [] commandId effect := by
  simp [effectLogApply, hasCommand]
-- [定义展开] 置信：首次写入头部 `(commandId,effect)`；第二次 head id 与自身相等而不再写入。

/-- Concrete existing-command witness: a replay does not replace the old effect. -/
theorem existing_command_replay_witness :
    effectLogApply [("cmd", "first")] "cmd" "second" = [("cmd", "first")] := by
  decide
-- [decide] 置信：head command id 字面量相等，直接返回原日志。

end P131

namespace P132

inductive HumanGate where
  | lawyerApproval
  | signature
  | finalReview
 deriving DecidableEq, Repr

inductive GatedAction where
  | fileDocument
  | issueOpinion
  | submitOutput
 deriving DecidableEq, Repr

def requiredGate : GatedAction → HumanGate
  | .fileDocument => .signature
  | .issueOpinion => .lawyerApproval
  | .submitOutput => .finalReview

def actionRequiresGate (action : GatedAction) (gate : HumanGate) : Bool :=
  decide (requiredGate action = gate)

/-- Every listed action requires exactly its tabled human gate. -/
theorem listed_action_requires_its_gate (action : GatedAction) :
    actionRequiresGate action (requiredGate action) = true := by
  cases action <;> decide
-- [cases+decide] 置信：三个动作逐一化为同构造子相等。

end P132

end JurisLean.Genealogy.Part6
