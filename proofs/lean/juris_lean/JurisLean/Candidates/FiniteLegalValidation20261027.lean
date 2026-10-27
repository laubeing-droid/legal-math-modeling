import JurisLean.Candidates.TemporalInterpretation20261027
import JurisLean.Candidates.EvidenceWorlds20261027
import JurisLean.Candidates.ProcedureClosure20261027

/-!
Original 08.7/08.8: finite legal validation consumes all extracted source
atoms, the actual selected norm version and an independent procedure policy.
The round trace is executable derivation evidence. A missing requested proof
does not remove a source fact or turn non-derivability into factual falsity.
-/

namespace JurisLean.Candidates.FiniteLegalValidation20261027

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.Final20261021.Compiler
open JurisLean.Candidates.Final20261021.Temporal
open JurisLean.Candidates.Final20261021.EvidenceProcedure


def enabledRules (rules : List (Rule Nat)) (known : List Nat) : List (Rule Nat) :=
  rules.filter fun r => r.premises.all (fun a => decide (a ∈ known))

theorem fired_conclusions_are_enabled_rules (rules : List (Rule Nat)) (known : List Nat) :
    rules.flatMap (fun r => if r.premises.all (fun a => decide (a ∈ known))
      then [r.conclusion] else []) = (enabledRules rules known).map Rule.conclusion := by
  induction rules with
  | nil => rfl
  | cons rule rest ih =>
      cases allowed : rule.premises.all (fun a => decide (a ∈ known)) <;>
        simp only [List.flatMap_cons, enabledRules, List.filter_cons, allowed,
          Bool.false_eq_true, if_false, if_true, List.map_cons,
          List.nil_append, List.cons_append, ih]

theorem advance_is_recorded_round (rules : List (Rule Nat)) (known : List Nat) :
    advance rules known = known ++ (enabledRules rules known).map Rule.conclusion := by
  rw [advance, fired_conclusions_are_enabled_rules]

def traceRounds (rules : List (Rule Nat)) : Nat → List Nat → List (List (Rule Nat))
  | 0, _ => []
  | fuel + 1, known => enabledRules rules known :: traceRounds rules fuel (advance rules known)

def replayTrace : List Nat → List (List (Rule Nat)) → List Nat
  | known, [] => known
  | known, fired :: rest => replayTrace (known ++ fired.map Rule.conclusion) rest

def ValidTrace (rules : List (Rule Nat)) : List Nat → List (List (Rule Nat)) → Prop
  | _, [] => True
  | known, fired :: rest =>
      (∀ r ∈ fired, r ∈ rules ∧ ∀ a ∈ r.premises, a ∈ known) ∧
        ValidTrace rules (known ++ fired.map Rule.conclusion) rest

theorem generated_trace_has_actual_rule_premises (rules : List (Rule Nat))
    (fuel : Nat) (facts : List Nat) : ValidTrace rules facts (traceRounds rules fuel facts) := by
  induction fuel generalizing facts with
  | zero => trivial
  | succ fuel ih =>
      refine ⟨?_, ?_⟩
      · intro r member
        have parts := List.mem_filter.mp member
        exact ⟨parts.1, by simpa only [List.all_eq_true, decide_eq_true_eq] using parts.2⟩
      · rw [← advance_is_recorded_round]
        exact ih (advance rules facts)

theorem replay_generated_trace_is_exact_closure (rules : List (Rule Nat))
    (fuel : Nat) (facts : List Nat) :
    replayTrace facts (traceRounds rules fuel facts) = proposed_rule_input rules fuel facts := by
  induction fuel generalizing facts with
  | zero => rfl
  | succ fuel ih =>
      simp only [traceRounds, replayTrace, proposed_rule_input]
      rw [← advance_is_recorded_round]
      exact ih (advance rules facts)

theorem trace_has_exact_number_of_rounds (rules : List (Rule Nat))
    (fuel : Nat) (facts : List Nat) : (traceRounds rules fuel facts).length = fuel := by
  induction fuel generalizing facts with
  | zero => rfl
  | succ fuel ih => simp [traceRounds, ih]

theorem enabled_count_bounded_by_rule_count (rules : List (Rule Nat)) (facts : List Nat) :
    (enabledRules rules facts).length ≤ rules.length := by
  induction rules with
  | nil => simp [enabledRules]
  | cons rule rest ih =>
      cases allowed : rule.premises.all (fun a => decide (a ∈ facts)) <;>
        simp [enabledRules, allowed] at ih ⊢ <;> omega

theorem closure_list_size_bound (rules : List (Rule Nat)) (fuel : Nat) (facts : List Nat) :
    (proposed_rule_input rules fuel facts).length ≤ facts.length + fuel * rules.length := by
  induction fuel generalizing facts with
  | zero => simp [proposed_rule_input]
  | succ fuel ih =>
      have tailBound := ih (advance rules facts)
      have added := enabled_count_bounded_by_rule_count rules facts
      rw [advance_is_recorded_round] at tailBound
      simp only [List.length_append, List.length_map] at tailBound
      simp only [proposed_rule_input, Nat.succ_mul, advance_is_recorded_round]
      omega

theorem carrier_round_bound (rules : List (Rule Nat)) (facts : List Nat) :
    (finiteCarrier rules facts).card ≤ facts.length + rules.length := by
  simpa only [finiteCarrier, List.length_append, List.length_map] using
    List.toFinset_card_le (facts ++ rules.map Rule.conclusion)

theorem total_trace_rule_count_bound (rules : List (Rule Nat)) (fuel : Nat) (facts : List Nat) :
    ((traceRounds rules fuel facts).map List.length).sum ≤ fuel * rules.length := by
  induction fuel generalizing facts with
  | zero => simp [traceRounds]
  | succ fuel ih =>
      have tailBound := ih (advance rules facts)
      have firstBound := enabled_count_bounded_by_rule_count rules facts
      simp only [traceRounds, List.map_cons, List.sum_cons, Nat.succ_mul]
      omega

structure HornReport where
  source : SourceCompilation20261027.ExtractedView
  selectedVersion : Nat
  active : List (Rule Nat)
  fuel : Nat
  trace : List (List (Rule Nat))
  closure : List Nat

def sourceFacts (view : SourceCompilation20261027.ExtractedView) : List Nat := view.decoded.atoms.map SourceCompilation20261027.Quoted.value

def fullHorn (view : SourceCompilation20261027.ExtractedView) (selected : Nat) (rules : List CompilerProvenance20261027.RuleUse)
    (ruleGate : Gamma → CompilerProvenance20261027.RuleUse → Bool) : HornReport :=
  let active := CompilerProvenance20261027.activeRules view.material.gamma rules (TemporalInterpretation20261027.selectedGate selected ruleGate)
  let facts := sourceFacts view
  let fuel := (finiteCarrier active facts).card
  let trace := traceRounds active fuel facts
  ⟨view, selected, active, fuel, trace, replayTrace facts trace⟩

theorem full_horn_consumes_every_source_fact (view : SourceCompilation20261027.ExtractedView) (selected : Nat)
    (rules : List CompilerProvenance20261027.RuleUse) (ruleGate : Gamma → CompilerProvenance20261027.RuleUse → Bool) (a : Nat) :
    a ∈ (fullHorn view selected rules ruleGate).closure ↔
      Derives (· ∈ sourceFacts view)
        (· ∈ CompilerProvenance20261027.activeRules view.material.gamma rules (TemporalInterpretation20261027.selectedGate selected ruleGate)) a := by
  simp only [fullHorn, replay_generated_trace_is_exact_closure]
  exact u03_2_computed_at_carrier_iff _ _ _

theorem full_horn_trace_is_checked (view : SourceCompilation20261027.ExtractedView) (selected : Nat)
    (rules : List CompilerProvenance20261027.RuleUse) (ruleGate : Gamma → CompilerProvenance20261027.RuleUse → Bool) :
    ValidTrace (fullHorn view selected rules ruleGate).active (sourceFacts view)
      (fullHorn view selected rules ruleGate).trace :=
  generated_trace_has_actual_rule_premises _ _ _

open JurisLean.Candidates.SourceCompilation20261027
open JurisLean.Candidates.CompilerProvenance20261027
open JurisLean.Candidates.TemporalInterpretation20261027
open JurisLean.Candidates.EvidenceWorlds20261027
open JurisLean.Candidates.ProcedureClosure20261027

-- Observation payloads cannot supply their own trusted receipt registries.
structure RawProcess where
  declaredRequired : List Nat
  domain : List Nat
  records : List Opportunity
  closureAuthority : Option SourceRef
  blocked : Bool

structure ProcessPolicy where
  gamma : Gamma
  version : Nat
  required : List Nat
  validExecutions : List SourceRef
  validWaivers : List SourceRef
  validClosures : List SourceRef

structure Supplement where
  material : MaterialSnapshot
  branch : Nat
  queryAtom : Nat
  policyVersion : Nat
  evidence : List (Quoted EvidenceItem)
  process : RawProcess
  receiptCitations : List Citation

def processReferences (p : RawProcess) : List SourceRef :=
  p.records.flatMap (fun o => o.executedReceipt.toList ++ o.waivedBy.toList) ++
    p.closureAuthority.toList

def supplementChecks (s : Supplement) : Bool :=
  s.evidence.all (fun e => citationPresent s.material e.citation &&
    decide (e.value.source = e.citation.source)) &&
  s.receiptCitations.all (citationPresent s.material) &&
  (processReferences s.process).all (fun ref =>
    s.receiptCitations.any (fun c => decide (c.source = ref)))

def processInput (raw : RawProcess) (policy : ProcessPolicy) : ProcessInput :=
  ⟨raw.declaredRequired, raw.domain, raw.records, policy.validExecutions,
    policy.validWaivers, raw.closureAuthority, policy.validClosures, raw.blocked⟩

structure BoundData where
  source : ExtractedView
  supplement : Supplement
  policy : ProcessPolicy

def supplementalRows (view : ExtractedView) (rows : List Supplement) : List Supplement :=
  rows.filter fun s => decide (s.material = view.material ∧ s.branch = view.branch)

def policyRows (view : ExtractedView) (version : Nat) (policies : List ProcessPolicy) :
    List ProcessPolicy :=
  policies.filter fun p => decide (p.gamma = view.material.gamma ∧ p.version = version)

def bindAdditional (view : ExtractedView) (rows : List Supplement)
    (policies : List ProcessPolicy) : Result BoundData :=
  match supplementalRows view rows with
  | [s] =>
      if supplementChecks s then
        match policyRows view s.policyVersion policies with
        | [p] => .known ⟨view, s, p⟩
        | [] => .unknown .authorityUnresolved
        | _ => .conflict s.policyVersion 2
      else .rejected .observationBindingMismatch
  | [] => .unknown .missingEvidence
  | _ => .conflict view.branch 2

theorem bound_data_keeps_exact_source_and_independent_policy (view : ExtractedView)
    (rows : List Supplement) (policies : List ProcessPolicy) (out : BoundData)
    (accepted : bindAdditional view rows policies = .known out) :
    out.source = view ∧ out.supplement ∈ rows ∧ out.policy ∈ policies ∧
      out.supplement.material = view.material ∧ out.supplement.branch = view.branch ∧
      supplementChecks out.supplement = true ∧ out.policy.gamma = view.material.gamma ∧
      out.policy.version = out.supplement.policyVersion := by
  unfold bindAdditional at accepted
  cases chosen : supplementalRows view rows with
  | nil => simp [chosen] at accepted
  | cons s tail =>
      cases tail with
      | cons second rest => simp [chosen] at accepted
      | nil =>
          simp only [chosen] at accepted
          split at accepted
          next valid =>
            cases selected : policyRows view s.policyVersion policies with
            | nil => simp [selected] at accepted
            | cons p rest =>
                cases rest with
                | cons other remaining => simp [selected] at accepted
                | nil =>
                    simp only [selected, Result.known.injEq] at accepted
                    cases accepted
                    have sm : s ∈ supplementalRows view rows := by simp [chosen]
                    have pm : p ∈ policyRows view s.policyVersion policies := by simp [selected]
                    have sr := List.mem_filter.mp sm
                    have pr := List.mem_filter.mp pm
                    have sh := of_decide_eq_true sr.2
                    have ph := of_decide_eq_true pr.2
                    exact ⟨rfl, sr.1, pr.1, sh.1, sh.2, valid, ph.1, ph.2⟩
          next invalid => cases accepted

def selectedHorn (view : ExtractedView) (selection : Result Nat)
    (rules : List RuleUse) (ruleGate : Gamma → RuleUse → Bool) : Result HornReport :=
  match selection with
  | .known v =>
      if v = view.material.gamma.normVersion then .known (fullHorn view v rules ruleGate)
      else .rejected .versionConflict
  | .unknown e => .unknown e
  | .rejected e => .rejected e
  | .conflict l r => .conflict l r

theorem selected_horn_cannot_rewrite_original_context (view : ExtractedView)
    (selection : Result Nat) (rules : List RuleUse) (ruleGate : Gamma → RuleUse → Bool)
    (out : HornReport) (accepted : selectedHorn view selection rules ruleGate = .known out) :
    selection = .known out.selectedVersion ∧ out.selectedVersion = view.material.gamma.normVersion ∧
      out = fullHorn view out.selectedVersion rules ruleGate := by
  cases selection with
  | unknown e => cases accepted
  | rejected e => cases accepted
  | conflict l r => cases accepted
  | known v =>
      simp only [selectedHorn] at accepted
      split at accepted
      next sameVersion =>
        cases accepted
        exact ⟨rfl, sameVersion, rfl⟩
      next mismatch => cases accepted

def modelCheck {W : Type} (truth : W → Nat → Bool) (w : W)
    (facts : List Nat) (rules : List (Rule Nat)) : Bool :=
  facts.all (truth w) && rules.all (fun r =>
    decide ((∀ a ∈ r.premises, truth w a = true) → truth w r.conclusion = true))

theorem model_check_exact {W : Type} (truth : W → Nat → Bool) (w : W)
    (facts : List Nat) (rules : List (Rule Nat)) :
    modelCheck truth w facts rules = true ↔
      Models (· ∈ facts) (· ∈ rules) (fun a => truth w a = true) := by
  simp only [modelCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Models]

def hornWorlds {W : Type} (out : HornReport) (modelWorlds : List W)
    (truth : W → Nat → Bool) : List W :=
  modelWorlds.filter fun w => modelCheck truth w (sourceFacts out.source) out.active

theorem horn_world_membership {W : Type} (out : HornReport) (modelWorlds : List W)
    (truth : W → Nat → Bool) (w : W) :
    w ∈ hornWorlds out modelWorlds truth ↔ w ∈ modelWorlds ∧
      Models (· ∈ sourceFacts out.source) (· ∈ out.active) (fun a => truth w a = true) := by
  simp only [hornWorlds, List.mem_filter, model_check_exact]

def joinedWorldView {W : Type} (bound : BoundData) (horn : Result HornReport)
    (modelWorlds : List W) (truth : W → Nat → Bool) : Result (EvidenceView W) :=
  match horn with
  | .known out => .known (viewEvidence (hornWorlds out modelWorlds truth) truth
      bound.supplement.queryAtom (bound.supplement.evidence.map Quoted.value))
  | .unknown e => .unknown e
  | .rejected e => .rejected e
  | .conflict l r => .conflict l r

inductive FailureWitness where
  | omittedOpportunity (id : Nat)
  | unfinishedOpportunity (id : Nat)
  | requiredMismatch
  | missingClosureAuthority
  | duplicateOpportunity
  | missingPremise (ruleReference atom : Nat)
  | queryNotDerived (atom : Nat)
  | pendingEvidence (source : SourceRef) (query : Nat)
  | incompatibleWorlds
  | unresolved (reason : Error)
  | conflicting (left right : Nat)
  deriving DecidableEq, Repr

def procedureWitnesses (bound : BoundData) : List FailureWitness :=
  let p := processInput bound.supplement.process bound.policy
  (missingOpportunities bound.policy.required p).map FailureWitness.omittedOpportunity ++
  (unfinishedOpportunities p).map FailureWitness.unfinishedOpportunity ++
  (if p.required = bound.policy.required then [] else [.requiredMismatch]) ++
  (if p.closureAuthority.any (fun r => decide (r ∈ p.validClosureAuthorities))
    then [] else [.missingClosureAuthority]) ++
  (if (p.records.map Opportunity.id).Nodup then [] else [.duplicateOpportunity])

def hornWitnesses (query : Nat) (rules : List RuleUse) (ruleGate : Gamma → RuleUse → Bool) :
    Result HornReport → List FailureWitness
  | .known out =>
      (if query ∈ out.closure then [] else [.queryNotDerived query]) ++
      ((rules.filter fun r => decide (r.normVersion = out.source.material.gamma.normVersion) &&
        selectedGate out.selectedVersion ruleGate out.source.material.gamma r).flatMap fun r =>
          (r.rule.premises.filter fun a => decide (a ∉ out.closure)).map
            (FailureWitness.missingPremise r.reference))
  | .unknown e => [.unresolved e]
  | .rejected e => [.unresolved e]
  | .conflict l r => [.conflicting l r]

def worldWitnesses {W : Type} : Result (EvidenceView W) → List FailureWitness
  | .known out => if out.possibleWorlds.isEmpty then [.incompatibleWorlds] else []
  | .unknown e => [.unresolved e]
  | .rejected e => [.unresolved e]
  | .conflict l r => [.conflicting l r]

-- Pending evidence about another atom can still change this query's worlds.
def admissionWitnesses (bound : BoundData) : List FailureWitness :=
  ((bound.supplement.evidence.map Quoted.value).filter fun e => decide (e.admissibility = .unknown)).map
    (fun e => .pendingEvidence e.source e.query)

structure ValidationReport (W : Type) where
  bound : BoundData
  versionCandidates : List Nat
  pendingVersions : List Nat
  selected : Result Nat
  horn : Result HornReport
  evidenceJudgment : Judgment
  procedure : Result Procedure
  worldView : Result (EvidenceView W)
  failures : List FailureWitness

-- A completed inspection retains unresolved subresults. It is not a legal PASS.
-- The procedure consumes independent policy records, never the Horn conclusion.
def inspectBound {W : Type} (bound : BoundData) (history : List VersionRecord)
    (versions : List Nat) (app : App) (rules : List RuleUse)
    (ruleGate : Gamma → RuleUse → Bool) (modelWorlds : List W)
    (truth : W → Nat → Bool) : ValidationReport W :=
  let g := bound.source.material.gamma
  let selected := selectVersion g history versions app
  let horn := selectedHorn bound.source selected rules ruleGate
  let worldView := joinedWorldView bound horn modelWorlds truth
  ⟨bound, candidates g (visibleSet g history) versions app,
    TemporalInterpretation20261027.pending g (visibleSet g history) versions app,
    selected, horn, judgment bound.supplement.queryAtom (bound.supplement.evidence.map Quoted.value),
    checkProcess bound.policy.required (processInput bound.supplement.process bound.policy), worldView,
    procedureWitnesses bound ++ hornWitnesses bound.supplement.queryAtom rules ruleGate horn ++
      worldWitnesses worldView ++ admissionWitnesses bound⟩

def validate {W : Type} (s : MaterialSnapshot) (branch : Nat) (catalog : List InterpretationRow)
    (supplements : List Supplement) (policies : List ProcessPolicy) (history : List VersionRecord)
    (versions : List Nat) (app : App) (rules : List RuleUse) (ruleGate : Gamma → RuleUse → Bool)
    (modelWorlds : List W) (truth : W → Nat → Bool) : Result (ValidationReport W) :=
  match extractView s branch catalog with
  | .known view =>
      match bindAdditional view supplements policies with
      | .known bound => .known (inspectBound bound history versions app rules ruleGate modelWorlds truth)
      | .unknown e => .unknown e
      | .rejected e => .rejected e
      | .conflict l r => .conflict l r
  | .unknown e => .unknown e
  | .rejected e => .rejected e
  | .conflict l r => .conflict l r

theorem validator_consumes_actual_bound_source {W : Type} (s : MaterialSnapshot) (branch : Nat)
    (catalog : List InterpretationRow) (supplements : List Supplement) (policies : List ProcessPolicy)
    (history : List VersionRecord) (versions : List Nat) (app : App) (rules : List RuleUse)
    (ruleGate : Gamma → RuleUse → Bool) (modelWorlds : List W) (truth : W → Nat → Bool)
    (out : ValidationReport W)
    (accepted : validate s branch catalog supplements policies history versions app rules ruleGate
      modelWorlds truth = .known out) :
    extractView s branch catalog = .known out.bound.source ∧
      bindAdditional out.bound.source supplements policies = .known out.bound ∧
      out = inspectBound out.bound history versions app rules ruleGate modelWorlds truth := by
  cases extracted : extractView s branch catalog with
  | unknown e => simp [validate, extracted] at accepted
  | rejected e => simp [validate, extracted] at accepted
  | conflict l r => simp [validate, extracted] at accepted
  | known view =>
      cases bound : bindAdditional view supplements policies with
      | unknown e => simp [validate, extracted, bound] at accepted
      | rejected e => simp [validate, extracted, bound] at accepted
      | conflict l r => simp [validate, extracted, bound] at accepted
      | known b =>
          have sameSource := (bound_data_keeps_exact_source_and_independent_policy
            view supplements policies b bound).1
          simp only [validate, extracted, bound, Result.known.injEq] at accepted
          cases accepted
          exact ⟨by simpa only [inspectBound, sameSource] using extracted,
            by simpa only [inspectBound, sameSource] using bound, rfl⟩

theorem inspected_closed_process_exhausts_independent_requirements {W : Type}
    (bound : BoundData) (history : List VersionRecord) (versions : List Nat) (app : App)
    (rules : List RuleUse) (ruleGate : Gamma → RuleUse → Bool) (modelWorlds : List W)
    (truth : W → Nat → Bool)
    (closed : (inspectBound bound history versions app rules ruleGate modelWorlds truth).procedure =
      .known .closedLawfully) :
    ∀ o ∈ bound.policy.required, terminal (processInput bound.supplement.process bound.policy) o = true :=
  checked_closure_exhausts_independent_requirements _ _ closed

theorem inspected_horn_is_applicable_and_complete {W : Type}
    (bound : BoundData) (history : List VersionRecord) (versions : List Nat) (app : App)
    (rules : List RuleUse) (ruleGate : Gamma → RuleUse → Bool) (modelWorlds : List W)
    (truth : W → Nat → Bool) (horn : HornReport)
    (accepted : (inspectBound bound history versions app rules ruleGate modelWorlds truth).horn = .known horn) :
    horn.selectedVersion = bound.source.material.gamma.normVersion ∧
      app bound.source.material.gamma (visibleSet bound.source.material.gamma history) horn.selectedVersion = .yes ∧
      ∀ a, a ∈ horn.closure ↔ Derives (· ∈ sourceFacts bound.source)
        (· ∈ activeRules bound.source.material.gamma rules (selectedGate horn.selectedVersion ruleGate)) a := by
  have flow := selected_horn_cannot_rewrite_original_context bound.source
    (selectVersion bound.source.material.gamma history versions app) rules ruleGate horn accepted
  have applicable := successful_version_is_applicable _ _ _ _ _ flow.1
  refine ⟨flow.2.1, applicable.2, ?_⟩
  intro a
  have computed := full_horn_consumes_every_source_fact bound.source horn.selectedVersion rules ruleGate a
  have sameClosure : horn.closure = (fullHorn bound.source horn.selectedVersion rules ruleGate).closure :=
    congrArg HornReport.closure flow.2.2
  rw [sameClosure]
  exact computed

theorem inspected_query_truth_requires_primitive_model {W : Type}
    (bound : BoundData) (history : List VersionRecord) (versions : List Nat) (app : App)
    (rules : List RuleUse) (ruleGate : Gamma → RuleUse → Bool) (modelWorlds : List W)
    (valuation : W → Nat → Bool) (horn : HornReport) (truth : Nat → Prop) (query : Nat)
    (accepted : (inspectBound bound history versions app rules ruleGate modelWorlds valuation).horn = .known horn)
    (model : Models (· ∈ sourceFacts bound.source)
      (· ∈ activeRules bound.source.material.gamma rules (selectedGate horn.selectedVersion ruleGate)) truth)
    (derived : query ∈ horn.closure) : truth query := by
  have computed := (inspected_horn_is_applicable_and_complete bound history versions app rules ruleGate
    modelWorlds valuation horn accepted).2.2 query
  exact u03_1_relative_soundness model (computed.mp derived)

theorem full_horn_worlds_keep_actual_truth_conditionally {W : Type}
    (view : ExtractedView) (selected : Nat) (rules : List RuleUse)
    (ruleGate : Gamma → RuleUse → Bool) (modelWorlds : List W) (truth : W → Nat → Bool)
    (actual : W) (covered : actual ∈ modelWorlds)
    (model : Models (· ∈ sourceFacts view)
      (· ∈ activeRules view.material.gamma rules (selectedGate selected ruleGate))
      (fun a => truth actual a = true)) (items : List EvidenceItem)
    (faithful : ∀ e ∈ items, usable e.query e = true → truth actual e.query = e.supports) :
    actual ∈ constrained (hornWorlds (fullHorn view selected rules ruleGate) modelWorlds truth)
      truth items := by
  apply faithful_evidence_retains_actual_world _ truth items actual _ faithful
  exact (horn_world_membership _ _ _ _).mpr ⟨covered, model⟩

structure BranchCase where
  key : Nat
  material : MaterialSnapshot
  parseBranch : Nat

-- Interpretation and applicable norm may vary across explicit legal branches.
-- Every other question/snapshot coordinate stays fixed; no Gamma is rewritten.
def sameQuestionScope (a b : MaterialSnapshot) : Bool :=
  decide (a.gamma.caseId = b.gamma.caseId ∧ a.gamma.caseRevision = b.gamma.caseRevision ∧
    a.gamma.evidenceVersion = b.gamma.evidenceVersion ∧ a.gamma.jurisdiction = b.gamma.jurisdiction ∧
    a.gamma.question = b.gamma.question ∧ a.gamma.lawDate = b.gamma.lawDate ∧
    a.gamma.knowledgeCutoff = b.gamma.knowledgeCutoff ∧ a.gamma.recordCutoff = b.gamma.recordCutoff ∧
    a.gamma.schemaVersion = b.gamma.schemaVersion ∧ a.gamma.observationFamily = b.gamma.observationFamily ∧
    a.gamma.mechanismVersion = b.gamma.mechanismVersion ∧ a.parseVersion = b.parseVersion ∧
    a.unitVersion = b.unitVersion ∧ a.fragments = b.fragments)

def branchWorlds {W : Type} (key : Nat) (allowedPairs : List (Nat × W)) : List W :=
  (allowedPairs.filter fun p => decide (p.1 = key)).map Prod.snd

theorem branch_worlds_do_not_invent_cartesian_pairs {W : Type} (key : Nat)
    (allowedPairs : List (Nat × W)) (w : W) :
    w ∈ branchWorlds key allowedPairs ↔ (key, w) ∈ allowedPairs := by
  constructor
  · intro member
    obtain ⟨⟨k, world⟩, selected, value⟩ := List.mem_map.mp member
    have checked := List.mem_filter.mp selected
    have same : k = key := of_decide_eq_true checked.2
    subst k
    change world = w at value
    subst world
    exact checked.1
  · intro member
    exact List.mem_map.mpr ⟨(key, w), List.mem_filter.mpr ⟨member, by simp⟩, rfl⟩

def inspectBranch {W : Type} (anchor : MaterialSnapshot) (entry : BranchCase)
    (catalog : List InterpretationRow) (supplements : List Supplement) (policies : List ProcessPolicy)
    (history : List VersionRecord) (versions : List Nat) (app : App) (rules : List RuleUse)
    (ruleGate : Gamma → RuleUse → Bool) (allowedPairs : List (Nat × W)) (truth : W → Nat → Bool) :
    Result (ValidationReport W) :=
  if sameQuestionScope anchor entry.material then
    validate entry.material entry.parseBranch catalog supplements policies history versions app rules ruleGate
      (branchWorlds entry.key allowedPairs) truth
  else .rejected .scopeMismatch

def validateFamily {W : Type} (anchor : MaterialSnapshot) (entries : List BranchCase)
    (catalog : List InterpretationRow) (supplements : List Supplement) (policies : List ProcessPolicy)
    (history : List VersionRecord) (versions : List Nat) (app : App) (rules : List RuleUse)
    (ruleGate : Gamma → RuleUse → Bool) (allowedPairs : List (Nat × W)) (truth : W → Nat → Bool) :
    Result (List (Nat × Result (ValidationReport W))) :=
  if entries.isEmpty then .unknown .missingEvidence
  else if (entries.map BranchCase.key).Nodup then
    .known (entries.map fun entry => (entry.key, inspectBranch anchor entry catalog supplements policies
      history versions app rules ruleGate allowedPairs truth))
  else .rejected .observationBindingMismatch

theorem family_retains_each_branch_including_failures {W : Type} (anchor : MaterialSnapshot)
    (entries : List BranchCase) (catalog : List InterpretationRow) (supplements : List Supplement)
    (policies : List ProcessPolicy) (history : List VersionRecord) (versions : List Nat) (app : App)
    (rules : List RuleUse) (ruleGate : Gamma → RuleUse → Bool) (allowedPairs : List (Nat × W))
    (truth : W → Nat → Bool) (out : List (Nat × Result (ValidationReport W)))
    (accepted : validateFamily anchor entries catalog supplements policies history versions app rules ruleGate
      allowedPairs truth = .known out) (entry : BranchCase) (member : entry ∈ entries) :
    (entry.key, inspectBranch anchor entry catalog supplements policies history versions app rules ruleGate
      allowedPairs truth) ∈ out := by
  unfold validateFamily at accepted
  split at accepted
  next empty => cases accepted
  next nonempty =>
    split at accepted
    next unique =>
      cases accepted
      exact List.mem_map.mpr ⟨entry, member, rfl⟩
    next duplicate => cases accepted

theorem pending_admission_is_reported_for_every_atom (bound : BoundData) (item : EvidenceItem)
    (member : item ∈ bound.supplement.evidence.map Quoted.value)
    (unresolved : item.admissibility = .unknown) :
    FailureWitness.pendingEvidence item.source item.query ∈ admissionWitnesses bound := by
  exact List.mem_map.mpr ⟨item, List.mem_filter.mpr ⟨member, by simp [unresolved]⟩, rfl⟩

theorem omitted_opportunity_has_actual_failure_witness (bound : BoundData) (o : Nat)
    (required : o ∈ bound.policy.required) (missing : o ∉ bound.supplement.process.domain) :
    FailureWitness.omittedOpportunity o ∈ procedureWitnesses bound := by
  have member := (missing_witness_is_an_actual_uncovered_requirement bound.policy.required
    (processInput bound.supplement.process bound.policy) o).mpr ⟨required, missing⟩
  simp only [procedureWitnesses, List.mem_append]
  exact Or.inl (List.mem_map.mpr ⟨o, member, rfl⟩)

end JurisLean.Candidates.FiniteLegalValidation20261027

end JurisLean.Candidates.FiniteLegalValidation20261027
