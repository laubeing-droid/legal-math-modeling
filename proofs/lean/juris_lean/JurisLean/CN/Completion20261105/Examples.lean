import JurisLean.CN.Completion20261105.Program

/-!
C3/C5 acceptance examples: actual Command calls and state endpoints, using
synthetic documents. These are representative parameter instances, not a
coverage matrix or assertions that the synthetic documents exist in reality.
Each case below checks its named legal property, not an instance counter.
-/
namespace JurisLean.CN.Completion20261105.Examples
open JurisLean.KernelV3
open JurisLean.CN.Revision20261101
open InstitutionRules

def request (act : Act) : Request := {toyRequest with act := act}
def grant (act : Act) (role : Role) : Grant := {toyGrant with act := act, role := role}
def grants : List Grant :=
  [grant .addTemplate .court, grant .admitEvidence .court, grant .decide .court,
   grant .constitute .party, grant .otherBind .administrator, grant .perform .party,
   grant .learnModel .party, grant .choose .party]
def confirmation : Rule := {toyRule with effect := .confirmatory, formed := none}
def policy : ProofPolicy := ⟨toyNorm, toyScope, support⟩
def call (act : Act) : Law.Call := ⟨request act, policy, .human, toyWorld⟩
def faithAtom : Atom := ⟨toyScope,⟨90⟩⟩
def priceAtom : Atom := ⟨toyScope,⟨91⟩⟩
def publicityAtom : Atom := ⟨toyScope,⟨92⟩⟩
def arrestAtom : Atom := ⟨toyScope,⟨96⟩⟩
def terminationAtom : Atom := ⟨toyScope,⟨97⟩⟩
def exclusion19Atom : Atom := ⟨toyScope,⟨98⟩⟩
def template : ProofTemplate :=
  ⟨toyNorm, toyScope, .civil, .claimant, [(toyAtom, .support toyAtom),(faithAtom,.support faithAtom),
      (priceAtom,.support priceAtom),(publicityAtom,.support publicityAtom),
      (arrestAtom,.support arrestAtom),(terminationAtom,.support terminationAtom),
      (exclusion19Atom,.support exclusion19Atom)], ⟨12⟩, ⟨50⟩⟩

def configured (law : Rule) (kind : InstitutionKind) : Situation :=
  let st := {initial with N := ⟨1, [law], grants⟩}
  {Situation.initial with
    core := initialCase.putState st rfl
    uses := [⟨toyNorm, toyScope, kind⟩]}

def advance {α : Type} (s : Situation) (c : Command α) : Situation :=
  (executeCommand s c).after
def registered (law : Rule) (kind : InstitutionKind) : Situation :=
  advance (configured law kind) (.addTemplate (request .addTemplate)
    {template with clauses := template.clauses.filter (fun clause => containsAtom clause.1 law.guard)})
def recordedCase (law : Rule) (kind : InstitutionKind) : Situation :=
  advance (registered law kind) (.record ⟨9⟩ toyRaw)
def readyCase (law : Rule) (kind : InstitutionKind) : Situation :=
  advance (recordedCase law kind) (.admitEvidence (request .admitEvidence) .human ⟨9⟩ toyRaw toyReceipt)
def normal : Situation := readyCase confirmation .evidence
def formedCase : Situation := advance (readyCase toyRule .lifecycle) (.legal (call .constitute))

/- No court decision or binding is smuggled into nonjudicial formation. -/
theorem actual_nonjudicial_formation :
    formedCase.core.state.L = [toyRelation] ∧
    formedCase.core.state.decisions = [] ∧ formedCase.core.state.bindings.isEmpty = true := by decide

def formationHistory : History (registered toyRule .lifecycle) formedCase :=
  History.snoc (History.snoc (History.snoc (History.nil _)
    (.record ⟨9⟩ toyRaw))
    (.admitEvidence (request .admitEvidence) .human ⟨9⟩ toyRaw toyReceipt)) (.legal (call .constitute))

theorem formation_history_has_three_ordered_calls : formationHistory.length = 3 := rfl

def revokeStart : Situation :=
  {formedCase with
    life := assign formedCase.life toyScope.object (some revocableLife)
    actRelations := assign formedCase.actRelations toyScope.object [toyRelation.id]}
def revokeGuard : RevokeGuard := ⟨⟨12⟩, ⟨51⟩, true, 0, 10, 0⟩
def revokedCase : Reply CivilActLife := executeCommand revokeStart
  (.institution (.revoke (call .constitute) (.atom toyAtom) toyScope.object revokeGuard))

/- 1: effective + revocable before; actual successful revocation removes
   tracked effects, keeps establishment and does not change natural F. -/
theorem lifecycle_actual :
    (revokeStart.life toyScope.object).map CivilActLife.effective = some true ∧
    (revokeStart.life toyScope.object).map CivilActLife.revocationPower = some true ∧
    (revokedCase.after.life toyScope.object).map CivilActLife.established = some true ∧
    (revokedCase.after.life toyScope.object).map CivilActLife.invalid = some true ∧
    revokedCase.after.core.state.L = [] ∧
    revokedCase.after.core.state.F = revokeStart.core.state.F := by decide

theorem lifecycle_failure_preserves_effect :
    (executeCommand revokeStart (.institution (.revoke (call .constitute) (.atom toyAtom)
      toyScope.object {revokeGuard with atTime := 100}))).after.core.state.L =
      revokeStart.core.state.L := by decide

/- Permission to undo an existing effect does not first create a replacement
   relation. This case deliberately has formed = none in the selected rule. -/
def undoOnlyStart : Situation :=
  let s := readyCase {toyRule with formed := none} .lifecycle
  let st := {s.core.state with L := [toyRelation]}
  {s.withCore (s.core.putState st rfl) with
    life := assign s.life toyScope.object (some revocableLife)
    actRelations := assign s.actRelations toyScope.object [toyRelation.id]}

theorem revoke_without_fictitious_formed :
    (executeCommand undoOnlyStart (.institution (.revoke (call .constitute) (.atom toyAtom)
      toyScope.object revokeGuard))).answer = .success (revokeLife revocableLife) ∧
    (executeCommand undoOnlyStart (.institution (.revoke (call .constitute) (.atom toyAtom)
      toyScope.object revokeGuard))).after.core.state.L = [] := by decide

def agency : Agency := ⟨⟨12⟩, ⟨22⟩, ⟨23⟩, toyScope, true, []⟩
def agencyStart : Situation :=
  let s := readyCase toyRule .agency
  {s with agencies := assign s.agencies toyScope.object (some agency)}
def child : Grant := {grant .constitute .party with actor := ⟨22⟩, start := 0, stop := 5}
def delegated : Reply Agency := executeCommand agencyStart
  (.institution (.delegate (call .constitute) (.atom toyAtom) toyScope.object child))

/- 2: derived authority is actually in N.grants, principal capacity survives. -/
theorem agency_actual :
    delegated.after.core.state.N.grants.contains child = true ∧
    (delegated.after.agencies toyScope.object).map Agency.principalCapacity = some true := by decide

theorem agency_over_scope_rejected :
    (executeCommand agencyStart (.institution (.delegate (call .constitute) (.atom toyAtom)
      toyScope.object {child with stop := 100}))).after.core.state.N.grants = agencyStart.core.state.N.grants := by decide

def apparentRelation : LegalRelation := {toyRelation with holder := ⟨22⟩}

def apparentStart : Situation :=
  let s := readyCase {toyRule with formed := none} .agency
  let st := {s.core.state with L := [apparentRelation]
    constraints := [.sameLoss apparentRelation apparentRelation]}
  s.withCore (s.core.putState st rfl)

def apparentResult : Reply Judgment := executeCommand apparentStart
  (.institution (.apparent (call .constitute) (.atom toyAtom) ⟨22⟩ ⟨12⟩
    ⟨true,true,.established,true⟩))

theorem apparent_actual_attribution :
    apparentResult.answer = .success .established ∧
    (apparentResult.after.core.state.L.head?).map LegalRelation.holder = some ⟨12⟩ ∧
    apparentResult.after.core.state.constraints = [.sameLoss toyRelation toyRelation] ∧
    apparentResult.after.core.state.F = apparentStart.core.state.F := by decide

theorem apparent_unchecked_faith_is_not_attribution :
    (executeCommand apparentStart (.institution (.apparent (call .constitute) (.atom toyAtom)
      ⟨22⟩ ⟨12⟩ ⟨true,true,.undetermined,true⟩))).answer = .unknown .inputUnchecked ∧
    (executeCommand apparentStart (.institution (.apparent (call .constitute) (.atom toyAtom)
      ⟨22⟩ ⟨12⟩ ⟨true,true,.undetermined,true⟩))).after.core.state.L = [apparentRelation] := by decide

/- 3: exclusive is a branch; ordinary jurisdiction requires no agreement. -/
theorem jurisdiction_actual :
    (executeCommand normal (.institution (.jurisdiction true
      ⟨true,false,false,false,false,false,false,true⟩))).answer = .success (some .ordinary) ∧
    (executeCommand normal (.institution (.jurisdiction true
      ⟨true,true,false,false,false,false,true,true⟩))).answer = .success none := by decide

/- 4: the same actual approved proof method sees pending/admitted/excluded
   differently; exclusion leaves raw material and cannot change F. -/
def withdrawnCase : Situation := advance normal (.withdraw (request .admitEvidence) ⟨9⟩ ⟨52⟩)
theorem evidence_actual :
    (executeCommand (recordedCase confirmation .evidence)
      (.burdenEvidence (call .decide) (.atom toyAtom))).answer = .unknown .inputUnchecked ∧
    (executeCommand normal (.burdenEvidence (call .decide) (.atom toyAtom))).answer = .success .established ∧
    (executeCommand withdrawnCase (.burdenEvidence (call .decide) (.atom toyAtom))).answer =
      .unknown .inputUnchecked ∧
    rawOf (withdrawnCase.core.state.E ⟨9⟩) = some toyRaw ∧
    withdrawnCase.core.state.F = normal.core.state.F := by decide

def admitOne (s : Situation) (id : Ref .material) (atom : Atom) (value : Bool) : Situation :=
  let raw : Raw id := ⟨atom,value,⟨id.value⟩,0⟩
  let receipt : Receipt raw := ⟨⟨id.value⟩,⟨12⟩,toyNorm,true,true,true,by decide⟩
  advance (advance s (.record id raw)) (.admitEvidence (request .admitEvidence) .human id raw receipt)
def ownerRelation : LegalRelation := {toyRelation with holder := aO}
def acquisitionLaw : Rule := {confirmation with
  guard := .both (.atom faithAtom) (.both (.atom priceAtom) (.atom publicityAtom))
  materials := [⟨9⟩,⟨90⟩,⟨91⟩,⟨92⟩,⟨93⟩]}
def acquisitionStart : Situation :=
  let s := admitOne (admitOne (admitOne (readyCase acquisitionLaw .acquisition)
    ⟨90⟩ faithAtom true) ⟨91⟩ priceAtom true) ⟨92⟩ publicityAtom true
  let st := {s.core.state with
    L := [ownerRelation]
    F := [⟨⟨60⟩,aD,toyAtom,0⟩, ⟨⟨61⟩,aT,toyAtom,0⟩]}
  s.withCore (s.core.putState st rfl)
def parties : AcquisitionParties := ⟨aO,aD,aT,by decide,by decide,by decide⟩
def disputedFaith : Situation := admitOne acquisitionStart ⟨93⟩ faithAtom false
def badFaithStart : Situation := advance disputedFaith (.withdraw (request .admitEvidence) ⟨90⟩ ⟨94⟩)
def repairedFaith : Situation := advance disputedFaith (.withdraw (request .admitEvidence) ⟨93⟩ ⟨95⟩)

/- 5: three actors and three distinct predicates, each evaluated from actual
   admitted material. Contradiction/withdrawal changes assessment, never F. -/
theorem acquisition_actual :
    (executeCommand acquisitionStart (.acquisitionEvidence (call .decide) parties .ordinary311
      faithAtom priceAtom publicityAtom)).answer = .success .established ∧
    (executeCommand badFaithStart (.acquisitionEvidence (call .decide) parties .ordinary311
      faithAtom priceAtom publicityAtom)).answer = .success .notEstablished ∧
    (executeCommand acquisitionStart (.acquisitionEvidence (call .decide) parties .lost312
      faithAtom priceAtom publicityAtom)).answer = .unknown .systemNotJudge := by decide

theorem actual_nonmonotone_withdrawal :
    (executeCommand disputedFaith (.acquisitionEvidence (call .decide) parties .ordinary311
      faithAtom priceAtom publicityAtom)).answer = .unknown .systemNotJudge ∧
    (executeCommand repairedFaith (.acquisitionEvidence (call .decide) parties .ordinary311
      faithAtom priceAtom publicityAtom)).answer = .success .established ∧
    repairedFaith.core.state.F = acquisitionStart.core.state.F := by decide

def offenseStart (actor : Ref .actor) : Situation :=
  let s := readyCase confirmation .offense
  let st := {s.core.state with F := [⟨ev1,actor,toyAtom,0⟩]}
  {s.withCore (s.core.putState st rfl) with
    participations := jiaParts ++ yiParts
    offenseSlots := [⟨toyNorm,toyScope,actor,ev1,q1,toyScope.question⟩]}
/- 6: actual actor/event projection blocks copying the other's excess. The
   general differing-charge theorem uses two norm-element queries, not scores. -/
theorem offense_actual :
    (executeCommand (offenseStart aYi) (.offenseEvidence (call .decide) aYi ev1 q1
      toyAtom toyAtom)).answer = .success toyScope.question ∧
    (executeCommand (offenseStart aYi) (.offenseEvidence (call .decide) aYi ev2 q1
      toyAtom toyAtom)).answer = .unknown .inputUnchecked := by decide

def bankruptcyLaw : Rule := {confirmation with effect := .proceduralBinding}
def bankruptcyStart : Situation :=
  {readyCase bankruptcyLaw .bankruptcy with
    executions := [procD,procO]
    interest := fun id => if id = ⟨21⟩ then some ⟨⟨7⟩,⟨3⟩⟩ else none}
def accepted : Situation := advance bankruptcyStart
  (.institution (.bankruptcy (call .decide) (.atom toyAtom) ⟨0,some 0⟩ aD))
def interestClaim : InterestClaim := ⟨⟨21⟩,aD,0,true⟩
def interestResult : Reply Nat := executeCommand accepted
  (.institution (.interest (call .decide) (.atom toyAtom) interestClaim 20))
/- 7: one debtor, actual stored acceptance date, article46 class and preinterest. -/
theorem bankruptcy_actual :
    accepted.stayed = [procD.id] ∧ accepted.bankruptcyCases aD = some 0 ∧
    accepted.bankruptcyCases aO = none ∧ interestResult.answer = .success 0 ∧
    (interestResult.after.interest ⟨21⟩).map (fun x => x.preAccrued.value) = some 7 ∧
    (executeCommand accepted (.institution (.interest (call .decide) (.atom toyAtom)
      {interestClaim with in46 := false} 20))).answer = .unknown .systemNotJudge := by decide

/- 8: art17(2) arrest + termination and no art19 exclusion. Art18 is
   the property route; it is not silently identified with art19. -/
def compensationLaw : Rule := {confirmation with
  guard := .both (.atom arrestAtom) (.both (.atom terminationAtom) (.neg (.atom exclusion19Atom)))
  materials := [⟨96⟩,⟨97⟩,⟨98⟩]}
def compensationStart : Situation :=
  admitOne (admitOne (admitOne (readyCase compensationLaw (.compensation .criminal))
    ⟨96⟩ arrestAtom true) ⟨97⟩ terminationAtom true) ⟨98⟩ exclusion19Atom false
def compensated : Reply Judgment := executeCommand compensationStart
  (.institution (.compensation (call .decide) compensationLaw.guard .criminal ⟨62⟩))
theorem compensation_actual :
    compensated.after.tracks.stateCompensation = [(.criminal,⟨62⟩)] ∧
    compensated.after.tracks.civil = [] ∧ compensated.after.tracks.criminal = [] ∧
    compensated.after.tracks.administrative = [] := by decide

def noTermination : Situation := advance compensationStart (.withdraw (request .admitEvidence) ⟨97⟩ ⟨99⟩)
theorem compensation_missing_prerequisite_not_automatic :
    (executeCommand noTermination (.institution (.compensation (call .decide)
      compensationLaw.guard .criminal ⟨62⟩))).answer = .unknown .inputUnchecked := by decide

/- 9: automatic elimination is absent; the actual conflict result is retained. -/
theorem rights_actual :
    (executeCommand normal (.institution .rightsConflict)).answer =
      .conflict .competentReview ∧
    (executeCommand normal (.institution .rightsConflict)).after.core.state.L = normal.core.state.L := by decide

def interpreted : Situation := advance (readyCase confirmation .interpretation)
  (.institution (.interpret (call .decide) (.atom toyAtom) toyScope.object (.known (.atom toyAtom))))
/- 10: actual stored interpretation is read by a following query; global N
   stays exactly the same, another object has no invented meaning. -/
theorem interpretation_actual :
    (executeCommand interpreted (.contractQuery (call .decide) toyScope.object)).answer = .success .established ∧
    interpreted.core.state.N.version = 1 ∧ interpreted.meanings ⟨999⟩ = none := by decide

def decisionSource : DecisionSource :=
  ⟨⟨70⟩,⟨70⟩,request .decide,.established,true,[.resJudicata],⟨[⟨12⟩],toyScope,0,10⟩⟩
def sourcedDecisionCase : Situation := advance (admitOne normal ⟨70⟩ toyAtom true)
  (.admitDecisionSource (request .admitEvidence) decisionSource)
def decisionCase : Situation := advance sourcedDecisionCase (.decide (call .decide) ⟨70⟩)
theorem no_source_no_model_judgment :
    (executeCommand normal (.decide (call .decide) ⟨70⟩)).answer = .unknown .inputUnchecked := by decide

def decisionRecord : DecisionRecord := ⟨⟨70⟩,request .decide,.established,true⟩
def decisionBinding : DecideBinding :=
  ⟨decisionRecord,.resJudicata,⟨[⟨12⟩],toyScope,0,10⟩,rfl,rfl⟩
def bound : Situation := advance decisionCase (.bindDecided decisionBinding .human)
/- 11: actual DecideBind, indexed person/subject/time, consumed from storage. -/
theorem resJudicata_actual :
    (executeCommand bound (.storedResJudicata ⟨70⟩ ⟨12⟩ toyScope 5)).answer = .success true ∧
    (executeCommand bound (.storedResJudicata ⟨70⟩ ⟨99⟩ toyScope 5)).answer = .success false ∧
    (executeCommand bound (.storedResJudicata ⟨70⟩ ⟨12⟩ toyScope 11)).answer = .success false ∧
    (executeCommand bound (.storedResJudicata ⟨70⟩ ⟨12⟩ {toyScope with question := ⟨999⟩} 5)).answer =
      .success false := by decide

/- 12: a native output becomes a candidate, never a decision or binding. -/
theorem proposal_actual :
    (executeCommand normal (.institution (.propose fitOut))).after.core.state.candidates.length = 1 ∧
    (executeCommand normal (.institution (.propose fitOut))).after.core.state.decisions = [] ∧
    (executeCommand normal (.institution (.propose fitOut))).after.core.state.bindings.isEmpty = true := by decide

theorem unauthorized_actual :
    (executeCommand (configured toyRule .lifecycle)
      (.legal {call .constitute with request := {request .constitute with actor := ⟨999⟩}})).answer =
      .rejected .unauthorized := by decide

def refused : Situation :=
  normal.withCore (normal.core.putState {normal.core.state with refusals := [toyScope]} rfl)
theorem refused_actual :
    (executeCommand refused (.legal {call .decide with mode := .automated})).answer = .blockedHuman ∧
    (executeCommand refused (.decide {call .decide with mode := .automated} ⟨90⟩)).answer = .blockedHuman := by decide

#print axioms actual_nonjudicial_formation
#print axioms formation_history_has_three_ordered_calls
#print axioms lifecycle_actual
#print axioms lifecycle_failure_preserves_effect
#print axioms agency_actual
#print axioms agency_over_scope_rejected
#print axioms jurisdiction_actual
#print axioms evidence_actual
#print axioms acquisition_actual
#print axioms actual_nonmonotone_withdrawal
#print axioms offense_actual
#print axioms bankruptcy_actual
#print axioms compensation_actual
#print axioms compensation_missing_prerequisite_not_automatic
#print axioms rights_actual
#print axioms interpretation_actual
#print axioms no_source_no_model_judgment
#print axioms resJudicata_actual
#print axioms proposal_actual
#print axioms unauthorized_actual
#print axioms refused_actual
end JurisLean.CN.Completion20261105.Examples
