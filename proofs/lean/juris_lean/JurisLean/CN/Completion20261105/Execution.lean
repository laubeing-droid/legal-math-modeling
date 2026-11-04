import JurisLean.CN.Completion20261105.EvidenceInstitutions
import JurisLean.CN.Completion20261105.FinancialMerge

/-!
One executable command graph: observations, admitted evidence, legal steps,
institutional instances, the nine operators and the eight native consumers.
Only the constructors below are public graph edges; bare update formulas are
not independent admission/decision entrypoints.
-/
namespace JurisLean.CN.Completion20261105
open JurisLean.KernelV3
open JurisLean.CN.Revision20261101
open InstitutionRules


def callEngine (s : Situation) (c : EngineContext) :
    (call : EngineCall) → NativeReply call.NativeType
  | .fit _ _ protocol loss models data => consumeFit s c protocol loss models data
  | .prob _ prior likelihood event => consumeProb s c prior likelihood event
  | .causal _ _ model permit => consumeCausal s c model permit
  | .bargain _ score permitted options offers => consumeBargain s c score permitted options offers
  | .cash before payment => consumeCash s c before payment
  | .exact unit left right => consumeExact s c unit left right
  | .behavior threshold actor action => consumeBehavior s c threshold actor action
  | .rsi _ before request samples permits proposal =>
      consumeRSI s c before request samples permits proposal

structure BoundEngineReply where
  legal : Reply EngineOutput
  native : Option (Sigma EngineCall.NativeType)

def engineMaterialAllowed (s : Situation) (c : EngineContext) (input : EngineMaterial) : Bool :=
  input.scope == c.scope && input.target == c.target &&
  input.version == s.core.state.N.version &&
  (match s.core.state.E input.id with
   | .accepted raw receipt => raw.source == input.source && raw.atom.scope == input.scope &&
       receipt.norm.version == input.version
   | _ => false)

def runBoundEngine (s : Situation) (c : EngineContext) (i : Ref .material) : BoundEngineReply :=
  match s.engineInputs.filter (fun input => input.id == i) with
  | [input] =>
    if engineMaterialAllowed s c input then
      let actual := callEngine s c input.input
      let reported := {actual.legal.after with
        engineResults := ⟨input,actual.native⟩ :: actual.legal.after.engineResults}
      ⟨⟨reported,actual.legal.answer⟩, some ⟨input.input, actual.native⟩⟩
    else ⟨quiet s (.unknown .inputUnchecked), none⟩
  | [] => ⟨quiet s (.unknown .inputUnchecked), none⟩
  | _ :: _ :: _ => ⟨quiet s (.conflict .competentReview), none⟩

def registerEngineMaterial (s : Situation) (r : Request) (input : EngineMaterial) : Reply Unit :=
  if !freshRequest s r || r.act != .learnModel || input.scope != r.scope ||
      input.version != r.version then quiet s (.rejected .unauthorized)
  else if s.engineInputs.any (fun old => old.id == input.id) then
    quiet s (.conflict .competentReview)
  else match rawOf (s.core.state.E input.id) with
    | none => quiet s (.unknown .inputUnchecked)
    | some raw =>
      if raw.source == input.source && raw.atom.scope == input.scope then
        ⟨{s with engineInputs := input :: s.engineInputs}, .success ()⟩
      else quiet s (.rejected .unsupported)

def learnedTable : (report : EngineReport) → Option (List Rat)
  | ⟨⟨_,_,_,_,_,.fit _ _ _ _ _ _⟩,.known fitted⟩ => some fitted.table
  | ⟨⟨_,_,_,_,_,.rsi _ _ _ _ _ _⟩,actual⟩ =>
    if actual.status == .evaluated &&
        (actual.receipt.bind (fun record => record.load)).any (fun load => load.status == .loaded) then
      some actual.post.service.loaded.fitted.table
    else none
  | _ => none

def learnReport (s : Situation) (r : Request) (id : Ref .material) : Reply Unit :=
  if !freshRequest s r || r.act != .learnModel then quiet s (.rejected .unauthorized)
  else match s.engineResults.find? (fun report => report.material.id == id) with
    | none => quiet s (.unknown .inputUnchecked)
    | some report =>
      if engineMaterialAllowed s ⟨r.scope,report.material.target⟩ report.material then
        match learnedTable report with
        | none => quiet s (.unknown .systemNotJudge)
        | some theta =>
          let st := {s.core.state with A := {s.core.state.A with theta := theta}}
          ⟨s.withCore (s.core.putState st rfl),.success ()⟩
      else quiet s (.unknown .inputUnchecked)

/- C4: a subsequent authorized Learn consumes the retained actual native
   table. It cannot write N/F/L, and an excluded input cannot be reused here. -/
theorem learnReport_frame (s : Situation) (r : Request) (i : Ref .material) :
    (learnReport s r i).after.core.state.N = s.core.state.N ∧
    (learnReport s r i).after.core.state.F = s.core.state.F ∧
    (learnReport s r i).after.core.state.L = s.core.state.L := by
  unfold learnReport
  split
  · exact ⟨rfl,rfl,rfl⟩
  · split
    · exact ⟨rfl,rfl,rfl⟩
    · split
      · split <;> exact ⟨rfl,rfl,rfl⟩
      · exact ⟨rfl,rfl,rfl⟩

/- C4: the public graph fetches the native input from the admitted keyed
   material; it cannot attach provenance to an unrelated supplied calculation.
   A raw/source decoder is an external input contract, not legal fact truth. -/
theorem bound_engine_calls_stored_input (s : Situation) (c : EngineContext)
    (i : Ref .material) (input : EngineMaterial)
    (h : s.engineInputs.filter (fun record => record.id == i) = [input])
    (ha : engineMaterialAllowed s c input = true) :
    (runBoundEngine s c i).legal.answer = (callEngine s c input.input).legal.answer ∧
    (runBoundEngine s c i).native = some ⟨input.input, (callEngine s c input.input).native⟩ ∧
    (runBoundEngine s c i).legal.after.engineResults.head? =
      some ⟨input,(callEngine s c input.input).native⟩ := by
  simp [runBoundEngine, h, ha]

theorem unadmitted_engine_material_blocks (s : Situation) (c : EngineContext)
    (input : EngineMaterial) (h : isAdmitted (s.core.state.E input.id) = false) :
    engineMaterialAllowed s c input = false := by
  cases he : s.core.state.E input.id <;> simp_all [isAdmitted, engineMaterialAllowed]

inductive InstitutionCall : Type → Type
  | revoke (c : Law.Call) (grounds : Formula) (obj : Ref .object) (g : RevokeGuard) :
      InstitutionCall CivilActLife
  | delegate (c : Law.Call) (grounds : Formula) (obj : Ref .object) (g : Grant) :
      InstitutionCall Agency
  | apparent (c : Law.Call) (grounds : Formula) (agent principal : Ref .actor)
      (g : ApparentGuard) : InstitutionCall Judgment
  | jurisdiction (known : Bool) (input : JurisdictionInput) :
      InstitutionCall (Option JurisdictionBranch)
  | burden (p : ProofPolicy) (ids : List (Ref .material)) (a : Atom) : InstitutionCall Judgment
  | acquisition (route : AcqRoute) (goodFaith price publicity : Judgment) : InstitutionCall Judgment
  | offense (ps : List Participation) (known : Bool) (ability elements : Judgment)
      (who : Ref .actor) (event : Ref .event) (commonScope charge : Ref .query) :
      InstitutionCall (Ref .query)
  | bankruptcy (c : Law.Call) (grounds : Formula) (dates : CaseDates) (debtor : Ref .actor) :
      InstitutionCall (List (Ref .event))
  | interest (c : Law.Call) (grounds : Formula)
      (claim : InterestClaim) (time : Nat) : InstitutionCall Nat
  | compensation (c : Law.Call) (grounds : Formula) (kind : CompensationKind)
      (relation : Ref .relation) : InstitutionCall Judgment
  | rightsConflict : InstitutionCall Unit
  | interpret (c : Law.Call) (grounds : Formula) (obj : Ref .object) (meaning : Check Formula) :
      InstitutionCall Formula
  | resJudicata (index : Option BindingIndex) (who : Ref .actor) (scope : Scope) (time : Nat) :
      InstitutionCall Bool
  | propose (output : EngineOutput) : InstitutionCall Candidate

def callInstitution (s : Situation) {α : Type} : InstitutionCall α → Reply α
  | .revoke c ground obj guard => Law.revoke s c ground obj guard
  | .delegate c ground obj grant => Law.delegateCall s c ground obj grant
  | .apparent c ground agent principal guard => Law.apparentCall s c ground agent principal guard
  | .jurisdiction known input => Law.jurisdictionQuery s known input
  | .burden policy ids a => Law.burdenQuery s policy ids a
  | .acquisition route faith price pub => Law.acquisitionQuery s route faith price pub
  | .offense ps known ability elements who event scope charge =>
      Law.offenseQuery s ps known ability elements who event scope charge
  | .bankruptcy c ground dates debtor => Law.acceptBankruptcy s c ground dates debtor
  | .interest c ground claim time =>
      Law.grounded s c (Law.continueWith (Law.gateFor s c ground .bankruptcy)
        (fun z => Law.interestFromCase z claim time))
  | .compensation c ground kind rel =>
      Law.grounded s c (Law.continueWith (Law.gateFor s c ground (.compensation kind))
        (fun z => ⟨{z with tracks := {z.tracks with
            stateCompensation := (kind,rel) :: z.tracks.stateCompensation}}, .success .established⟩))
  | .rightsConflict => Law.rightsConflict s
  | .interpret c ground obj meaning => Law.interpret s c ground obj meaning
  | .resJudicata index who scope time => Law.resJudicataQuery s index who scope time
  | .propose output => Law.proposeEngine s output

def recordMaterial (s : Situation) (i : Ref .material) (raw : Raw i) : Reply (Ref .material) :=
  match rawOf (s.core.state.E i) with
  | none => ⟨s.withCore (s.core.setCell i (.pending raw)), .success i⟩
  | some current =>
    if current == raw then quiet s (.success i)
    else quiet s (.conflict .competentReview)

def admission (s : Situation) (r : Request) (m : Mode) (i : Ref .material)
    (raw : Raw i) (receipt : Receipt raw) : Reply (Ref .material) :=
  if automationAllowed s.core.state r.scope m = false then quiet s .blockedHuman
  else if freshRequest s r = false || r.act != .admitEvidence ||
      r.scope != raw.atom.scope || r.rule != receipt.norm.id ||
      r.version != receipt.norm.version then quiet s (.rejected .unauthorized)
  else
    match s.core.state.E i with
    | .pending current =>
      if current == raw then
        ⟨EffectIR.adjust (EffectIR.admission i raw receipt) s, .success i⟩
      else quiet s (.conflict .competentReview)
    | _ => quiet s (.rejected .prerequisites)

def withdrawal (s : Situation) (r : Request) (i : Ref .material)
    (reason : Ref .document) : Reply (Ref .material) :=
  if freshRequest s r = false || r.act != .admitEvidence then quiet s (.rejected .unauthorized)
  else
    match rawOf (s.core.state.E i) with
    | none => quiet s (.rejected .prerequisites)
    | some raw =>
      if r.scope == raw.atom.scope then
        ⟨s.withCore (s.core.setCell i (.excluded raw reason)), .success i⟩
      else quiet s (.rejected .unauthorized)

def occurrence (s : Situation) (o : Occurrence) : Reply (Ref .event) :=
  match s.core.state.F.find? (fun old => old.id == o.id) with
  | none =>
    ⟨EffectIR.adjust [.fact o] s, .success o.id⟩
  | some old =>
    if old == o then quiet s (.success o.id) else quiet s (.conflict .competentReview)

def selectClaim (s : Situation) (r : Request) (mode : Mode) (rel : LegalRelation) :
    Reply (Ref .relation) :=
  if automationAllowed s.core.state r.scope mode = false then quiet s .blockedHuman
  else if freshRequest s r && r.act == .choose && r.scope == rel.scope &&
      s.core.state.L.contains rel then
    ⟨{s with choices := (fun scope => if scope = r.scope then some rel.id else s.choices scope)},
      .success rel.id⟩
  else quiet s (.rejected .unauthorized)

def legalPositions (s : Situation) (scope : Scope) : List HohfeldPosition :=
  (s.core.state.L.filter (fun rel => rel.scope == scope)).flatMap hohfeld

/- An execution descriptor is the checked projection of a source document:
   debtor denotes the estate to which this property execution is related.
   Observation is not a command to an external enforcement system. A newly
   discovered related execution passes the same bankruptcy shared gate. -/
def observeExecution (s : Situation) (r : Request) (material : Ref .material)
    (proc : ExecProc) : Reply (Ref .event) :=
  if !freshRequest s r || r.act != .admitEvidence then quiet s (.rejected .unauthorized)
  else match s.core.state.E material with
    | .accepted raw receipt =>
      if raw.atom.scope != r.scope || receipt.norm.version != r.version then quiet s (.unknown .inputUnchecked)
      else if s.executions.any (fun old => old.id == proc.id && old != proc) then
        quiet s (.conflict .competentReview)
      else
        let executions := if s.executions.contains proc then s.executions else s.executions ++ [proc]
        let stayed := if (s.bankruptcyCases proc.debtor).isSome then
            if s.stayed.contains proc.id then s.stayed else s.stayed ++ [proc.id]
          else s.stayed
        ⟨{s with executions := executions,stayed := stayed},.success proc.id⟩
    | _ => quiet s (.unknown .inputUnchecked)

inductive Command : Type → Type 1
  | observeExecution (r : Request) (material : Ref .material) (p : ExecProc) : Command (Ref .event)
  | admitDecisionSource (r : Request) (d : DecisionSource) : Command Unit
  | learnReport (r : Request) (material : Ref .material) : Command Unit
  | check (predicate : Situation → Bool) : Command Unit
  | positions (scope : Scope) : Command (List HohfeldPosition)
  | operator (params : OperatorParams) {α : Type} (op : OpRequest α) : Command α
  | institution {α : Type} (call : InstitutionCall α) : Command α
  | engine (context : EngineContext) (material : Ref .material) : Command EngineOutput
  | registerEngine (r : Request) (input : EngineMaterial) : Command Unit
  | legal (call : Law.Call) : Command Unit
  | burdenEvidence (c : Law.Call) (body : Formula) : Command Judgment
  | acquisitionEvidence (c : Law.Call) (parties : AcquisitionParties) (route : AcqRoute)
      (faith price publicity : Atom) : Command Judgment
  | offenseEvidence (c : Law.Call) (person : Ref .actor)
      (event : Ref .event) (commonScope : Ref .query) (ability elements : Atom) : Command (Ref .query)
  | storedResJudicata (doc : Ref .document) (person : Ref .actor) (scope : Scope) (time : Nat) : Command Bool
  | contractQuery (c : Law.Call) (obj : Ref .object) : Command Judgment
  | assignment (a : MeaningAssignment) (r : Request) : Command Formula
  | perform (call : Law.Call) (relation : Ref .relation) (p : Native.PaymentPayload) : Command Unit
  | addTemplate (r : Request) (t : ProofTemplate) : Command (Ref .document)
  | decide (c : Law.Call) (document : Ref .document) : Command DecisionRecord
  | bindDecided (b : DecideBinding) (mode : Mode) : Command Unit
  | bindOther (b : OtherBinding) (mode : Mode) : Command Unit
  | learn (r : Request) (theta : List Rat) (i : Ref .material) (raw : Raw i) : Command Unit
  | record (i : Ref .material) (raw : Raw i) : Command (Ref .material)
  | admitEvidence (r : Request) (mode : Mode) (i : Ref .material)
      (raw : Raw i) (receipt : Receipt raw) : Command (Ref .material)
  | withdraw (r : Request) (i : Ref .material) (why : Ref .document) : Command (Ref .material)
  | occur (event : Occurrence) : Command (Ref .event)
  | choose (r : Request) (mode : Mode) (relation : LegalRelation) : Command (Ref .relation)

def executeCommand (s : Situation) {α : Type} : Command α → Reply α
  | .observeExecution r i p => observeExecution s r i p
  | .admitDecisionSource r d => admitDecisionSource s r d
  | .learnReport r i => learnReport s r i
  | .check predicate => if predicate s then quiet s (.success ()) else quiet s (.rejected .prerequisites)
  | .positions scope => quiet s (.success (legalPositions s scope))
  | .operator params op => runOperator params s op
  | .institution call => callInstitution s call
  | .engine context material => (runBoundEngine s context material).legal
  | .registerEngine r input => registerEngineMaterial s r input
  | .legal call => legalDispatch s call.request call.policy call.mode call.world
  | .perform call relation p => performCall s call relation p
  | .assignment a r => assignmentQuery s a r
  | .burdenEvidence c body => burdenEvidence s c body
  | .acquisitionEvidence c ps route faith price pub => acquisitionEvidence s c ps route faith price pub
  | .offenseEvidence c person event commonScope ability elements =>
      offenseEvidence s c person event commonScope ability elements
  | .storedResJudicata doc person scope time => storedResJudicata s doc person scope time
  | .contractQuery c obj => contractQuery s c obj
  | .addTemplate r t => registerTemplate s r t
  | .decide c document => recordDecision s c document
  | .bindDecided b mode => bindDecided s b mode
  | .bindOther b mode => bindOtherSource s b mode
  | .learn r theta i raw => learnMaterial s r theta i raw
  | .record i raw => recordMaterial s i raw
  | .admitEvidence r mode i raw receipt => admission s r mode i raw receipt
  | .withdraw r i why => withdrawal s r i why
  | .occur o => occurrence s o
  | .choose r mode relation => selectClaim s r mode relation

/- There is one history type for all command families. Each endpoint is the
   actual interpreter result, and all typed input payloads are retained. -/
inductive History : Situation → Situation → Type 1
  | nil (s : Situation) : History s s
  | snoc {a b : Situation} (h : History a b) {α : Type} (c : Command α) :
      History a (executeCommand b c).after

def History.length {a b : Situation} : History a b → Nat
  | .nil _ => 0
  | .snoc h _ => h.length + 1

theorem history_keeps_ordered_step {a b : Situation} (h : History a b)
    {α : Type} (c : Command α) : (h.snoc c).length = h.length + 1 := rfl

/- The replay path cannot revive a withdrawn/pending label. The exact old
   cell, including exclusion and its reason, remains the current cell. -/
theorem recorded_replay_keeps_exclusion (s : Situation) (i : Ref .material)
    (raw : Raw i) (why : Ref .document) (h : s.core.state.E i = .excluded raw why) :
    (recordMaterial s i raw).after = s := by
  simp [recordMaterial, h, rawOf, quiet]

theorem admission_missing_authority (s : Situation) (r : Request) (mode : Mode)
    (i : Ref .material) (raw : Raw i) (receipt : Receipt raw)
    (h : freshRequest s r = false) : (admission s r mode i raw receipt).after = s := by
  by_cases hm : automationAllowed s.core.state r.scope mode = false <;>
    simp [admission, hm, h, quiet]

theorem choice_not_model_score (s : Situation) (r : Request) (mode : Mode)
    (rel : LegalRelation) :
    (selectClaim s r mode rel).after.core.state.L = s.core.state.L ∧
    (selectClaim s r mode rel).after.core.state.F = s.core.state.F := by
  unfold selectClaim
  split
  · exact ⟨rfl, rfl⟩
  · split <;> exact ⟨rfl, rfl⟩

#print axioms history_keeps_ordered_step
#print axioms recorded_replay_keeps_exclusion
#print axioms admission_missing_authority
#print axioms choice_not_model_score
#print axioms bound_engine_calls_stored_input
#print axioms unadmitted_engine_material_blocks
#print axioms learnReport_frame
end JurisLean.CN.Completion20261105

