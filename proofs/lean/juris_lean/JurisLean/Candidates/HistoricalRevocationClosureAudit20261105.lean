import JurisLean.Candidates.FinalizeReadClosureAudit20261105
import JurisLean.Candidates.TemporalInterpretationAudit20261027

namespace JurisLean.Candidates.HistoricalRevocationClosureAudit20261105

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.Final20261021.Temporal
open JurisLean.Candidates.TemporalInterpretation20261027
open JurisLean.Candidates.AuthorizationClosureAudit20261104

/- Frozen 10.3 L117: a two-version, three-event finite replay instance.
   Event ids 0/1/2 mean enable v0 / replace by v1 / revoke v1 here only.
   The applicability input is explicit; this is not a rule about actual legal retroactivity. -/
inductive Retroactivity where
  | prospective
  | fromReplacement
  deriving DecidableEq, Repr

def gammaAt (law cut : Int) : Gamma :=
  { TemporalInterpretation20261027.Audit.gamma with
    normVersion := 1
    lawDate := ⟨law⟩
    knowledgeCutoff := ⟨cut⟩
    recordCutoff := ⟨cut⟩ }

def enable : VersionRecord :=
  TemporalInterpretation20261027.Audit.record 0 0 0 none 0 0

def replacement : VersionRecord :=
  TemporalInterpretation20261027.Audit.record 1 1 1 none 1 1

def revocation : VersionRecord :=
  TemporalInterpretation20261027.Audit.record 2 1 2 none 2 2

def events : List VersionRecord := [enable, replacement, revocation]

def legalStart (rule : Retroactivity) (e : VersionRecord) : Int :=
  if e.id.value = 2 ∧ rule = .fromReplacement then 1 else e.factFrom.ordinal

def replayStep (rule : Retroactivity) (g : Gamma) (records : Finset VersionRecord)
    (active : Option Nat) (e : VersionRecord) : Option Nat :=
  if e ∈ records ∧ e.jurisdiction = g.jurisdiction ∧ e.question = g.question ∧
      legalStart rule e ≤ g.lawDate.ordinal then
    match e.id.value with
    | 0 => some 0
    | 1 => some 1
    | 2 => if active = some 1 then none else active
    | _ => active
  else active

def replayApp (template : List VersionRecord) (rule : Retroactivity) : App :=
  fun g records version =>
    match template.foldl (replayStep rule g records) none with
    | none => .no
    | some active => if active = version then .yes else .no

def readNorm (rule : Retroactivity) (g : Gamma) (history : List VersionRecord) : Result Nat :=
  selectVersion g history [0, 1] (replayApp events rule)

/- L117: the actual existing selector consumes the finite replay App.
   The old prefix and both version records remain unchanged when revocation is appended. -/
theorem append_replay_enable_replace_revoke :
    (0 : Int) < 1 ∧ (1 : Int) < 2 ∧
    readNorm .prospective { gammaAt 0 0 with normVersion := 0 } [enable] = .known 0 ∧
    readNorm .prospective (gammaAt 1 1) [enable, replacement] = .known 1 ∧
    readNorm .prospective (gammaAt 2 2) events = .unknown .missingEvidence ∧
    events.take 2 = [enable, replacement] := by
  decide +kernel

/- L117: countermodel only. Reading the mutable current status changes a query
   whose Gamma and stored historical records have not changed. This changes App,
   so it is not a counterexample to the fixed-App stability theorem. -/
def badCurrentStatusApp (currentActive : Bool) : App :=
  fun _ _ version => if currentActive && decide (version = 1) then .yes else .no

theorem overwritten_status_pollutes_fixed_historical_query :
    selectVersion (gammaAt 1 1) [enable, replacement] [0, 1]
      (badCurrentStatusApp true) = .known 1 ∧
    selectVersion (gammaAt 1 1) [enable, replacement] [0, 1]
      (badCurrentStatusApp false) = .unknown .missingEvidence := by
  decide +kernel

/- L119: instantiate the existing stability theorem. App and immutable record
   contents are fixed, and the appended record is outside both historical cuts. -/
theorem fixed_cut_replay_uses_invisible_append_stability :
    readNorm .prospective (gammaAt 1 1) [enable, replacement] = .known 1 ∧
    readNorm .prospective (gammaAt 1 1) ([enable, replacement] ++ [revocation]) = .known 1 := by
  have stable := selection_stable_after_invisible_append (gammaAt 1 1)
    [enable, replacement] [revocation] [0, 1] (replayApp events .prospective)
    (by decide +kernel)
  constructor
  · decide +kernel
  · exact stable.trans (by decide +kernel)

/- L117/L119: the same past legal date, evaluated with past or present knowledge,
   can differ only under the explicitly supplied retroactivity rule here. -/
theorem past_knowledge_and_current_material_are_distinct :
    readNorm .fromReplacement (gammaAt 1 1) events = .known 1 ∧
    readNorm .fromReplacement (gammaAt 1 2) events = .unknown .missingEvidence ∧
    readNorm .prospective (gammaAt 1 2) events = .known 1 := by
  decide +kernel

def lateOldRecord : VersionRecord :=
  TemporalInterpretation20261027.Audit.record 7 1 0 none 2 2

/- L119: an old legal start cannot disguise its later recording and knowledge. -/
theorem late_old_event_is_not_past_knowledge :
    visible (gammaAt 1 1) lateOldRecord = false ∧
    selectVersion (gammaAt 1 1) [lateOldRecord] [1] intervalApp = .unknown .missingEvidence ∧
    selectVersion (gammaAt 1 2) [lateOldRecord] [1] intervalApp = .known 1 := by
  decide +kernel

/- L119/L121: neither retroactivity branch is silently selected. These are the
   two declared finite rules, not a claim that they exhaust all real legal rules. -/
def unknownRetroactivityResults (g : Gamma) (history : List VersionRecord) : List (Result Nat) :=
  [readNorm .prospective g history, readNorm .fromReplacement g history]

theorem unknown_retroactivity_preserves_different_past_outcomes :
    unknownRetroactivityResults (gammaAt 1 2) events = [.known 1, .unknown .missingEvidence] ∧
    readNorm .prospective (gammaAt 1 2) events ∈ unknownRetroactivityResults (gammaAt 1 2) events ∧
    readNorm .fromReplacement (gammaAt 1 2) events ∈ unknownRetroactivityResults (gammaAt 1 2) events := by
  decide +kernel

/- L119: three independent finite effects, using the actual authorization check
   and selector. Question 3 is the primary norm read; question 4 is a separate
   precedent-reference read. Replacing that reference creates no authorization. -/
def currentQuery : Query := { baseQuery with gamma := gammaAt 2 2 }
def liveGrant : Authorization.Grant := grantFor currentQuery
def expiredGrant : Authorization.Grant := { liveGrant with untilDate := ⟨2⟩ }

def referenceGamma : Gamma := { gammaAt 2 2 with question := 4 }
def reference0 : VersionRecord := { enable with question := 4 }
def reference1 : VersionRecord :=
  { replacement with
    question := 4
    factFrom := ⟨2⟩
    recordedAt := ⟨2⟩
    knownAt := ⟨2⟩ }
def referenceEvents : List VersionRecord := [reference0, reference1]

def readReference (history : List VersionRecord) : Result Nat :=
  selectVersion referenceGamma history [0, 1] (replayApp referenceEvents .prospective)

def expiryEffect : Bool × Result Nat × Result Nat :=
  (check currentQuery expiredGrant,
    readNorm .prospective (gammaAt 2 2) [enable, replacement], readReference [reference0])
def revocationEffect : Bool × Result Nat × Result Nat :=
  (check currentQuery liveGrant,
    readNorm .prospective (gammaAt 2 2) events, readReference [reference0])
def precedentEffect : Bool × Result Nat × Result Nat :=
  (check currentQuery liveGrant,
    readNorm .prospective (gammaAt 2 2) [enable, replacement], readReference referenceEvents)

theorem expiry_revocation_and_precedent_replacement_have_distinct_effects :
    expiryEffect = (false, .known 1, .known 0) ∧
    revocationEffect = (true, .unknown .missingEvidence, .known 0) ∧
    precedentEffect = (true, .known 1, .known 1) ∧
    expiryEffect ≠ revocationEffect ∧ expiryEffect ≠ precedentEffect ∧
    revocationEffect ≠ precedentEffect := by
  decide +kernel

/- L121: five necessary dimensions for reusing this bound authorization receipt.
   This projection is not a sufficient condition for reusing a complete evaluation:
   check_full_bindings requires full Gamma and the other bindings as well.
   For successful timed compilation, the existing read contract identifies the
   selected version with Gamma.normVersion. -/
def cacheKey (q : Query) : ObjectId × Nat × Nat × Instant × LawDate :=
  (q.object, q.gamma.question, q.gamma.normVersion, q.gamma.knowledgeCutoff, q.gamma.lawDate)

theorem same_bound_receipt_requires_five_cache_dimensions (q r : Query)
    (a : Authorization.Grant) (oldValid : check q a = true) (newValid : check r a = true) :
    cacheKey q = cacheKey r := by
  have oldBindings := check_full_bindings q a oldValid
  have newBindings := check_full_bindings r a newValid
  have sameGamma : q.gamma = r.gamma :=
    oldBindings.2.2.2.1.symm.trans newBindings.2.2.2.1
  have sameObject : q.object = r.object :=
    oldBindings.2.2.2.2.1.symm.trans newBindings.2.2.2.2.1
  unfold cacheKey
  rw [sameGamma, sameObject]

def changedQuestion : Query :=
  { baseQuery with gamma := { baseQuery.gamma with question := baseQuery.gamma.question + 1 } }
def changedNorm : Query :=
  { baseQuery with gamma := { baseQuery.gamma with normVersion := baseQuery.gamma.normVersion + 1 } }
def changedKnowledge : Query :=
  { baseQuery with
    gamma := { baseQuery.gamma with knowledgeCutoff := ⟨baseQuery.gamma.knowledgeCutoff.ticks + 1⟩ } }
def changedLaw : Query :=
  { baseQuery with gamma := { baseQuery.gamma with lawDate := ⟨baseQuery.gamma.lawDate.ordinal + 1⟩ }}

/- L121: removing any one of the five dimensions can identify a valid old receipt
   with an invalid current request. The changed law date is still inside the date
   window, isolating the context binding from the separate expiry counterexample. -/
theorem five_cache_dimension_erasure_witnesses :
    check baseQuery baseGrant = true ∧
    check wrongObject baseGrant = false ∧ check changedQuestion baseGrant = false ∧
    check changedNorm baseGrant = false ∧ check changedKnowledge baseGrant = false ∧
    check changedLaw baseGrant = false ∧
    (baseQuery.gamma.question, baseQuery.gamma.normVersion, baseQuery.gamma.knowledgeCutoff,
      baseQuery.gamma.lawDate) =
      (wrongObject.gamma.question, wrongObject.gamma.normVersion, wrongObject.gamma.knowledgeCutoff,
        wrongObject.gamma.lawDate) ∧
    (baseQuery.object, baseQuery.gamma.normVersion, baseQuery.gamma.knowledgeCutoff,
      baseQuery.gamma.lawDate) =
      (changedQuestion.object, changedQuestion.gamma.normVersion, changedQuestion.gamma.knowledgeCutoff,
        changedQuestion.gamma.lawDate) ∧
    (baseQuery.object, baseQuery.gamma.question, baseQuery.gamma.knowledgeCutoff,
      baseQuery.gamma.lawDate) =
      (changedNorm.object, changedNorm.gamma.question, changedNorm.gamma.knowledgeCutoff,
        changedNorm.gamma.lawDate) ∧
    (baseQuery.object, baseQuery.gamma.question, baseQuery.gamma.normVersion,
      baseQuery.gamma.lawDate) =
      (changedKnowledge.object, changedKnowledge.gamma.question, changedKnowledge.gamma.normVersion,
        changedKnowledge.gamma.lawDate) ∧
    (baseQuery.object, baseQuery.gamma.question, baseQuery.gamma.normVersion,
      baseQuery.gamma.knowledgeCutoff) =
      (changedLaw.object, changedLaw.gamma.question, changedLaw.gamma.normVersion,
        changedLaw.gamma.knowledgeCutoff) ∧
    baseGrant.fromDate.ordinal ≤ changedLaw.gamma.lawDate.ordinal ∧
    changedLaw.gamma.lawDate.ordinal < baseGrant.untilDate.ordinal := by
  decide +kernel

/- L121: retaining a historical environment is different from using it as the
   fresh value at a later current Gamma. No claim that all past results change. -/
theorem historical_environment_is_not_current_cache :
    readNorm .prospective (gammaAt 1 1) events = .known 1 ∧
    readNorm .prospective (gammaAt 2 2) events = .unknown .missingEvidence ∧
    (gammaAt 1 1).lawDate ≠ (gammaAt 2 2).lawDate ∧
    (gammaAt 1 1).knowledgeCutoff ≠ (gammaAt 2 2).knowledgeCutoff := by
  decide +kernel

#check append_replay_enable_replace_revoke
#print axioms append_replay_enable_replace_revoke
#check overwritten_status_pollutes_fixed_historical_query
#print axioms overwritten_status_pollutes_fixed_historical_query
#check fixed_cut_replay_uses_invisible_append_stability
#print axioms fixed_cut_replay_uses_invisible_append_stability
#check past_knowledge_and_current_material_are_distinct
#print axioms past_knowledge_and_current_material_are_distinct
#check late_old_event_is_not_past_knowledge
#print axioms late_old_event_is_not_past_knowledge
#check unknown_retroactivity_preserves_different_past_outcomes
#print axioms unknown_retroactivity_preserves_different_past_outcomes
#check expiry_revocation_and_precedent_replacement_have_distinct_effects
#print axioms expiry_revocation_and_precedent_replacement_have_distinct_effects
#check same_bound_receipt_requires_five_cache_dimensions
#print axioms same_bound_receipt_requires_five_cache_dimensions
#check five_cache_dimension_erasure_witnesses
#print axioms five_cache_dimension_erasure_witnesses
#check historical_environment_is_not_current_cache
#print axioms historical_environment_is_not_current_cache
#check selection_stable_after_invisible_append
#print axioms selection_stable_after_invisible_append
#check check_full_bindings
#print axioms check_full_bindings
#check timed_compiler_consumes_selected_version
#print axioms timed_compiler_consumes_selected_version

end JurisLean.Candidates.HistoricalRevocationClosureAudit20261105