import JurisLean.CN.Completion20261105.EngineConsumers

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

inductive EngineCall
  | fit (m n : Nat) (protocol : Native.Fit.LearningProtocol)
      (loss : ℚ → Bool → ℚ) (models : List (List ℚ)) (data : Fin n → Fin m × Bool)
  | prob (n : Nat) (prior : Native.Prob.FiniteLaw (Fin n))
      (likelihood : Fin n → ℚ) (event : Fin n → Ref .event)
  | causal (n k : Nat) (model : CausalInput n k) (permit : Option CausalPermit)
  | bargain (n : Nat) (score : Fin n → ℚ) (permitted : Fin n → Bool)
      (options : List (Fin n)) (offers : Fin n → List (Ref .actor × Quantity .money))
  | cash (before : Native.Cash.State) (payment : Native.PaymentPayload)
  | exact (unit : UnitKind) (left right : Native.Decision.TypedValue)
  | behavior (threshold : ℚ) (actor : Ref .actor) (action : Fin 3 → Ref .query)
  | rsi (m : Nat) (before : Native.RSI.RoundState m) (request : Native.RSI.RoundRequest m)
      (samples : List (Native.RSI.SamplingReceipt m)) (permits : List (Native.RSI.LoadPermit m))
      (proposal : Ref .model)

def EngineCall.NativeType : EngineCall → Type
  | .fit _ _ _ _ _ _ => Native.Result Native.Fit.FittedTable
  | .prob n _ _ _ => Native.Result (Native.Prob.FiniteLaw (Fin n))
  | .causal _ _ _ _ => Native.Result ℚ
  | .bargain n _ _ _ _ => Native.Result (Fin n)
  | .cash _ _ => Native.Result Native.Cash.State
  | .exact _ _ _ => Native.Result Native.Decision.TypedValue
  | .behavior _ _ _ => Native.Result (Fin 3)
  | .rsi m _ _ _ _ _ => Native.RSI.RoundOutcome m

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
  | interest (c : Law.Call) (grounds : Formula) (accepted : Check Bool) (atTime : Nat)
      (claim : InterestClaim) (time : Nat) : InstitutionCall Nat
  | compensation (c : Law.Call) (grounds : Formula) (kind : CompensationKind)
      (relation : Ref .relation) (custody : Bool) (conditions1719 : Judgment) :
      InstitutionCall Judgment
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
  | .interest c ground accepted atTime claim time =>
      Law.atomic s (Law.continueWith (Law.gate s c ground)
        (fun z => Law.interestLocal z accepted atTime claim time))
  | .compensation c ground kind rel custody conditions =>
      Law.atomic s (Law.continueWith (Law.gate s c ground)
        (fun z => Law.stateCompensationLocal z kind rel custody conditions))
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
        ⟨s.withCore (s.core.setCell i (.accepted raw receipt)), .success i⟩
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
    let st := {s.core.state with F := s.core.state.F ++ [o]}
    ⟨{s with core := {s.core with state := st}}, .success o.id⟩
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

inductive Command : Type → Type 1
  | operator (params : OperatorParams) {α : Type} (op : OpRequest α) : Command α
  | institution {α : Type} (call : InstitutionCall α) : Command α
  | engine (context : EngineContext) (call : EngineCall) : Command EngineOutput
  | legal (call : Law.Call) : Command Unit
  | record (i : Ref .material) (raw : Raw i) : Command (Ref .material)
  | admitEvidence (r : Request) (mode : Mode) (i : Ref .material)
      (raw : Raw i) (receipt : Receipt raw) : Command (Ref .material)
  | withdraw (r : Request) (i : Ref .material) (why : Ref .document) : Command (Ref .material)
  | occur (event : Occurrence) : Command (Ref .event)
  | choose (r : Request) (mode : Mode) (relation : LegalRelation) : Command (Ref .relation)

def executeCommand (s : Situation) {α : Type} : Command α → Reply α
  | .operator params op => runOperator params s op
  | .institution call => callInstitution s call
  | .engine context call => (callEngine s context call).legal
  | .legal call => legalDispatch s call.request call.policy call.mode call.world
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
end JurisLean.CN.Completion20261105

