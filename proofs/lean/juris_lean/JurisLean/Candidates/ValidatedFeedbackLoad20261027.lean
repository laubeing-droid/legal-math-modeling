import JurisLean.Candidates.ProtectedFeedback20261027
import JurisLean.Candidates.Final20261021.Authorization

/-!
Actual finite model-store transitions for original E14/E15 and consumer edge15.
This is executable mathematical repository code: the loaded slot is written,
then read by this implementation. It is not a claim that a production service,
database, JC or Harness has been deployed.

External catalogues attest the declared prevalidation plan/sampling procedure
and authorize the exact evaluation package. Catalogue membership does not prove
that these attestations are true; population statements retain the iid, source
and fixed-target premises of ProtectedFeedback. No Boolean creates those facts.
-/

namespace JurisLean.Candidates.ValidatedFeedbackLoad20261027

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.LearningConsumer20261027
open JurisLean.Candidates.EventFeedbackConsumer20261027
open JurisLean.Candidates.ProtectedFeedback20261027

structure SamplingReceipt (m : Nat) where
  plan : ValidationPlan
  parent : TrainingCandidate m
  blocks : List (DomainBlock m)
  declaredAt : Instant
  acquiredAt : Instant
  evidence : SourceRef
  deriving DecidableEq, Repr

structure LoadPermit (m : Nat) where
  evaluation : Evaluation m
  grant : Authorization.Grant
  deriving DecidableEq, Repr

inductive LoadStatus where
  | parentMismatch | snapshotMismatch | contextMismatch | invalidEvaluation
  | protectedScopeFailed | samplingUnresolved | authorityUnresolved | loaded
  deriving DecidableEq, Repr

structure LoadLog (m : Nat) where
  evaluation : Evaluation m
  status : LoadStatus
  samplingEvidence : SourceRef
  authorityEvidence : SourceRef
  readback : Option (TrainingCandidate m)
  deriving DecidableEq, Repr

structure Service (m : Nat) where
  gamma : Gamma
  principal : PartyId
  lossVersion : Nat
  loaded : TrainingCandidate m
  journal : Store m
  history : List (LoadLog m)
  deriving DecidableEq, Repr

def readLoaded {m : Nat} (s : Service m) : TrainingCandidate m := s.loaded

def predictLoaded {m : Nat} (s : Service m) (query : Fin m) : ℚ :=
  (readLoaded s).fitted.table.getD query.val 0

structure LoadOutcome (m : Nat) where
  status : LoadStatus
  post : Service m
  readback : Option (TrainingCandidate m)
  deriving DecidableEq, Repr

def samplingMatches {m : Nat} (catalog : List (SamplingReceipt m))
    (evaluation : Evaluation m) (receipt : SamplingReceipt m) : Bool :=
  decide (receipt ∈ catalog ∧ receipt.plan = evaluation.plan ∧
    receipt.parent = evaluation.parent ∧ receipt.blocks = evaluation.blocks ∧
    receipt.declaredAt.ticks < receipt.acquiredAt.ticks)

def loadAllowed {m : Nat} (catalog : List (LoadPermit m)) (s : Service m)
    (evaluation : Evaluation m) (permit : LoadPermit m) : Bool :=
  decide (permit ∈ catalog ∧ permit.evaluation = evaluation) &&
  Authorization.checkGrant s.gamma s.principal 2
    evaluation.candidate.fitted.protocol.fit.modelVersion (.party s.principal) none none permit.grant

def refuse {m : Nat} (s : Service m) (evaluation : Evaluation m)
    (receipt : SamplingReceipt m) (permit : LoadPermit m) (status : LoadStatus) : LoadOutcome m :=
  ⟨status, { s with history := s.history ++
    [⟨evaluation, status, receipt.evidence, permit.grant.evidence, none⟩] }, none⟩

-- The readback is produced from the state just written, not supplied by a caller.
def writeAndRead {m : Nat} (s : Service m) (evaluation : Evaluation m)
    (receipt : SamplingReceipt m) (permit : LoadPermit m) : LoadOutcome m :=
  let written := { s with loaded := evaluation.candidate }
  let actual := readLoaded written
  ⟨.loaded, { written with history := s.history ++
    [⟨evaluation, .loaded, receipt.evidence, permit.grant.evidence, some actual⟩] }, some actual⟩

def activate {m : Nat} (s : Service m) (evaluation : Evaluation m)
    (samplingCatalog : List (SamplingReceipt m)) (receipt : SamplingReceipt m)
    (authorityCatalog : List (LoadPermit m)) (permit : LoadPermit m) : LoadOutcome m :=
  if evaluation.parent ≠ readLoaded s then refuse s evaluation receipt permit .parentMismatch
  else if evaluation.candidate.snapshot ≠ s.journal then refuse s evaluation receipt permit .snapshotMismatch
  else if evaluation.plan.scope.ruleVersion ≠ s.gamma.normVersion ∨
      evaluation.plan.scope.mechanismVersion ≠ s.gamma.mechanismVersion ∨
      evaluation.candidate.fitted.protocol.lossVersion ≠ s.lossVersion then
    refuse s evaluation receipt permit .contextMismatch
  else if evaluate evaluation.plan evaluation.parent evaluation.candidate binaryLoss
      evaluation.blocks ≠ .known evaluation then refuse s evaluation receipt permit .invalidEvaluation
  else if evaluation.passesBounds = false then refuse s evaluation receipt permit .protectedScopeFailed
  else if samplingMatches samplingCatalog evaluation receipt = false then
    refuse s evaluation receipt permit .samplingUnresolved
  else if loadAllowed authorityCatalog s evaluation permit = false then
    refuse s evaluation receipt permit .authorityUnresolved
  else writeAndRead s evaluation receipt permit

theorem activation_keeps_rules_mechanism_and_training {m : Nat}
    (s : Service m) (evaluation : Evaluation m)
    (samplingCatalog : List (SamplingReceipt m)) (receipt : SamplingReceipt m)
    (authorityCatalog : List (LoadPermit m)) (permit : LoadPermit m) :
    (activate s evaluation samplingCatalog receipt authorityCatalog permit).post.gamma = s.gamma ∧
    (activate s evaluation samplingCatalog receipt authorityCatalog permit).post.principal = s.principal ∧
    (activate s evaluation samplingCatalog receipt authorityCatalog permit).post.lossVersion = s.lossVersion ∧
    (activate s evaluation samplingCatalog receipt authorityCatalog permit).post.journal = s.journal := by
  unfold activate
  split_ifs <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem every_activation_attempt_retains_history {m : Nat}
    (s : Service m) (evaluation : Evaluation m)
    (samplingCatalog : List (SamplingReceipt m)) (receipt : SamplingReceipt m)
    (authorityCatalog : List (LoadPermit m)) (permit : LoadPermit m) :
    ∃ entry, (activate s evaluation samplingCatalog receipt authorityCatalog permit).post.history =
      s.history ++ [entry] := by
  unfold activate
  split_ifs <;> exact ⟨_, rfl⟩

theorem refusal_keeps_actual_prediction {m : Nat}
    (s : Service m) (evaluation : Evaluation m)
    (samplingCatalog : List (SamplingReceipt m)) (receipt : SamplingReceipt m)
    (authorityCatalog : List (LoadPermit m)) (permit : LoadPermit m)
    (refused : (activate s evaluation samplingCatalog receipt authorityCatalog permit).status ≠ .loaded) :
    readLoaded (activate s evaluation samplingCatalog receipt authorityCatalog permit).post = readLoaded s ∧
    (activate s evaluation samplingCatalog receipt authorityCatalog permit).readback = none ∧
    ∀ query, predictLoaded (activate s evaluation samplingCatalog receipt authorityCatalog permit).post query =
      predictLoaded s query := by
  unfold activate at refused ⊢
  split_ifs at refused ⊢ <;> simp_all [refuse, writeAndRead, readLoaded, predictLoaded]

theorem loaded_package_is_actual_written_readback {m : Nat}
    (s : Service m) (evaluation : Evaluation m)
    (samplingCatalog : List (SamplingReceipt m)) (receipt : SamplingReceipt m)
    (authorityCatalog : List (LoadPermit m)) (permit : LoadPermit m)
    (loaded : (activate s evaluation samplingCatalog receipt authorityCatalog permit).status = .loaded) :
    evaluation.parent = readLoaded s ∧ evaluation.candidate.snapshot = s.journal ∧
    evaluate evaluation.plan evaluation.parent evaluation.candidate binaryLoss evaluation.blocks = .known evaluation ∧
    evaluation.passesBounds = true ∧ samplingMatches samplingCatalog evaluation receipt = true ∧
    loadAllowed authorityCatalog s evaluation permit = true ∧
    readLoaded (activate s evaluation samplingCatalog receipt authorityCatalog permit).post = evaluation.candidate ∧
    (activate s evaluation samplingCatalog receipt authorityCatalog permit).readback =
      some (readLoaded (activate s evaluation samplingCatalog receipt authorityCatalog permit).post) := by
  unfold activate at loaded ⊢
  split_ifs at loaded ⊢ <;> simp_all [refuse, writeAndRead, readLoaded]

theorem replaced_candidate_does_not_reuse_old_permit {m : Nat}
    (catalog : List (LoadPermit m)) (s : Service m) (evaluation : Evaluation m) (permit : LoadPermit m)
    (changed : permit.evaluation ≠ evaluation) :
    loadAllowed catalog s evaluation permit = false := by
  simp [loadAllowed, changed]

theorem actual_loaded_risk_follows_computed_domain_bounds {m : Nat}
    (s : Service m) (evaluation : Evaluation m)
    (samplingCatalog : List (SamplingReceipt m)) (receipt : SamplingReceipt m)
    (authorityCatalog : List (LoadPermit m)) (permit : LoadPermit m)
    (loaded : (activate s evaluation samplingCatalog receipt authorityCatalog permit).status = .loaded)
    (risk : Nat → List ℚ → ℝ)
    (confidence : ∀ block ∈ evaluation.blocks, ∀ model ∈ evaluation.plan.models,
      |(blockRisk binaryLoss block model : ℝ) - risk block.domain model| ≤
        JurisLean.Candidates.LearningFiniteClass20261027.finiteRadius block.rows.length
          evaluation.plan.models.toFinset.card (block.delta : ℝ)) :
    ∀ block ∈ evaluation.blocks,
      risk block.domain (readLoaded (activate s evaluation samplingCatalog receipt authorityCatalog permit).post).fitted.table ≤
      risk block.domain (readLoaded s).fitted.table + (block.tolerance : ℝ) := by
  obtain ⟨parent, _, computed, passed, _, _, actual, _⟩ :=
    loaded_package_is_actual_written_readback s evaluation samplingCatalog receipt authorityCatalog permit loaded
  have bounds := bounds_gate_on_joint_event_preserves_each_risk evaluation.plan
    evaluation.parent evaluation.candidate binaryLoss evaluation.blocks evaluation computed passed risk confidence
  simpa only [actual, parent] using bounds

theorem changed_validation_snapshot_does_not_reuse_sampling_receipt {m : Nat}
    (catalog : List (SamplingReceipt m)) (evaluation : Evaluation m) (receipt : SamplingReceipt m)
    (changed : receipt.blocks ≠ evaluation.blocks) :
    samplingMatches catalog evaluation receipt = false := by
  simp [samplingMatches, changed]

structure Prepared (m : Nat) where
  post : Service m
  observation : Receipt m
  parent : TrainingCandidate m
  candidate : Result (TrainingCandidate m)
  models : List (List ℚ)
  deriving DecidableEq, Repr

-- Current loaded weights enter the actual search class. The actual updated
-- journal, not a parallel training input, feeds the existing finite fitter.
def prepareNext {m : Nat} (s : Service m) (now : Instant)
    (correctionPermits : List (CorrectionPermit m)) (change : Change m)
    (protocol : LearningProtocol) (proposals : List (List ℚ)) : Prepared m :=
  let family := (readLoaded s).fitted.table :: proposals
  let updated := processAndFit now correctionPermits s.journal change protocol binaryLoss family
  let fitted := if protocol.lossVersion = s.lossVersion then updated.candidate
    else .unknown .targetMismatch
  ⟨{ s with journal := updated.observation.post }, updated.observation, readLoaded s, fitted, family⟩

theorem next_candidate_consumes_current_loaded_and_actual_post {m : Nat}
    (s : Service m) (now : Instant) (correctionPermits : List (CorrectionPermit m))
    (change : Change m) (protocol : LearningProtocol) (proposals : List (List ℚ))
    (lossSame : protocol.lossVersion = s.lossVersion) :
    (prepareNext s now correctionPermits change protocol proposals).parent = readLoaded s ∧
    (prepareNext s now correctionPermits change protocol proposals).models =
      (readLoaded s).fitted.table :: proposals ∧
    (prepareNext s now correctionPermits change protocol proposals).candidate =
      (processAndFit now correctionPermits s.journal change protocol binaryLoss
        ((readLoaded s).fitted.table :: proposals)).candidate ∧
    (prepareNext s now correctionPermits change protocol proposals).post.journal =
      (applyChange now correctionPermits s.journal change).post ∧
    readLoaded (prepareNext s now correctionPermits change protocol proposals).post = readLoaded s := by
  simp [prepareNext, lossSame, processAndFit, readLoaded]

theorem newly_loaded_model_is_next_actual_parent {m : Nat}
    (s : Service m) (evaluation : Evaluation m)
    (samplingCatalog : List (SamplingReceipt m)) (receipt : SamplingReceipt m)
    (authorityCatalog : List (LoadPermit m)) (permit : LoadPermit m)
    (loaded : (activate s evaluation samplingCatalog receipt authorityCatalog permit).status = .loaded)
    (now : Instant) (correctionPermits : List (CorrectionPermit m)) (change : Change m)
    (protocol : LearningProtocol) (proposals : List (List ℚ)) :
    (prepareNext (activate s evaluation samplingCatalog receipt authorityCatalog permit).post
      now correctionPermits change protocol proposals).parent = evaluation.candidate ∧
    (prepareNext (activate s evaluation samplingCatalog receipt authorityCatalog permit).post
      now correctionPermits change protocol proposals).models = evaluation.candidate.fitted.table :: proposals := by
  have exactLoaded := (loaded_package_is_actual_written_readback
    s evaluation samplingCatalog receipt authorityCatalog permit loaded).2.2.2.2.2.2.1
  exact ⟨exactLoaded, congrArg (fun p : TrainingCandidate m => p.fitted.table :: proposals) exactLoaded⟩

end JurisLean.Candidates.ValidatedFeedbackLoad20261027
