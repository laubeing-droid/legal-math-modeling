import JurisLean.CN.Completion20261105.Examples

/-!
C5: a callable runtime, not a separately recomputed ideal function.
Wire input selects an exact typed command from a source/receipt catalog. This
finite reference protocol intentionally does not invent external receipt trust,
deserialize functions as authorities, install DeepInfer or modify the workbench.
All operation/institution/native-input payloads are retained in the catalog and
the resulting History. The IO entry calls this same dispatcher once.
-/
namespace JurisLean.CN.Completion20261105.Runtime
open JurisLean.KernelV3
open JurisLean.CN.Revision20261101

inductive Tag
  | operator | institution | engine | legal | assignment | perform | template
  | decide | bindDecision | bindOther | learn | record | admit | withdraw | occur | choose
  deriving DecidableEq, Repr

def commandTag {α : Type} : Command α → Tag
  | .operator _ _ | .check _ => .operator
  | .positions _ => .institution
  | .institution _ | .burdenEvidence _ _ | .acquisitionEvidence _ _ _ _ _ _ |
      .offenseEvidence _ _ _ _ _ _ | .storedResJudicata _ _ _ _ | .contractQuery _ _ => .institution
  | .engine _ _ | .registerEngine _ _ => .engine
  | .legal _ => .legal
  | .assignment _ _ => .assignment
  | .perform _ _ _ => .perform
  | .addTemplate _ _ => .template
  | .decide _ _ => .decide
  | .bindDecided _ _ => .bindDecision
  | .bindOther _ _ => .bindOther
  | .learn _ _ _ _ | .learnReport _ _ => .learn
  | .record _ _ => .record
  | .admitEvidence _ _ _ _ _ | .admitDecisionSource _ _ | .observeExecution _ _ _ => .admit
  | .withdraw _ _ _ => .withdraw
  | .occur _ => .occur
  | .choose _ _ _ => .choose

def parseTag : String → Option Tag
  | "operator" => some .operator | "institution" => some .institution
  | "engine" => some .engine | "legal" => some .legal
  | "assignment" => some .assignment | "perform" => some .perform
  | "template" => some .template | "decide" => some .decide
  | "bindDecision" => some .bindDecision | "bindOther" => some .bindOther
  | "learn" => some .learn | "record" => some .record
  | "admit" => some .admit | "withdraw" => some .withdraw
  | "occur" => some .occur | "choose" => some .choose
  | _ => none

structure Wire where
  tag : Tag
  key : Nat
  deriving DecidableEq, Repr

def decode (line : String) : Option Wire :=
  match line.splitOn ":" with
  | [tag,key] => do
    let t ← parseTag tag
    let k ← key.toNat?
    pure ⟨t,k⟩
  | _ => none

structure PackedCommand where
  resultType : Type
  command : Command resultType

abbrev Catalog := Nat → Option PackedCommand

inductive Status
  | success | rejected (reason : Refusal) | unknown (reason : UnknownKind)
  | conflict (route : ReviewRoute) | blockedHuman
  deriving DecidableEq, Repr

def statusOf {α : Type} : Answer α → Status
  | .success _ => .success
  | .rejected r => .rejected r
  | .unknown k => .unknown k
  | .conflict r => .conflict r
  | .blockedHuman => .blockedHuman

structure PackedReply where
  resultType : Type
  reply : Reply resultType

/- A closed, typed wire value keeps actual result data in Type. The generic
   command/history language lives in Type 1 and cannot itself be an IO result.
   This is an executed projection, not a second computation of the answer. -/
inductive Value
  | unit | boolean (value : Bool) | natural (value : Nat)
  | reference (kind : JurisLean.CN.Revision20261101.IdKind) (id : Nat)
  | judgment (value : Judgment) | formula (value : Formula)
  | events (ids : List (Ref .event)) | times (values : List Nat)
  | quantity (u : UnitKind) (value : Quantity u) | clock (value : Clock)
  | life (value : CivilActLife) | agency (value : Agency)
  | jurisdiction (value : Option JurisdictionBranch)
  | decision (value : DecisionRecord) | candidate (value : Candidate)
  | engine (value : EngineOutput) | positions (value : List HohfeldPosition)

def operatorValue {α : Type} : OpRequest α → α → Value
  | .anchor _,v => .events v | .measure u _,v => .quantity u v
  | .exclude _ _,v => .times v | .adjust _ _ _,v => .clock v
  | .expire _,v => .boolean v | .witness _,v => .reference .document v.value
  | .count _,v => .natural v | .project _,v => .events v | .commute _ _ _ _,v => .boolean v

def institutionValue {α : Type} : InstitutionCall α → α → Value
  | .revoke _ _ _ _,v => .life v | .delegate _ _ _ _,v => .agency v
  | .apparent _ _ _ _ _,v => .judgment v | .jurisdiction _ _,v => .jurisdiction v
  | .bankruptcy _ _ _ _,v => .events v | .interest _ _ _ _,v => .natural v
  | .compensation _ _ _ _,v => .judgment v | .rightsConflict,_ => .unit
  | .interpret _ _ _ _,v => .formula v
  | .propose _,v => .candidate v

def commandValue {α : Type} : Command α → α → Value
  | .observeExecution _ _ _,v => .reference .event v.value
  | .admitDecisionSource _ _,_ => .unit
  | .learnReport _ _,_ => .unit
  | .check _,_ => .unit | .positions _,v => .positions v
  | .operator _ op,v => operatorValue op v
  | .institution call,v => institutionValue call v
  | .engine _ _,v => .engine v | .registerEngine _ _,_ => .unit
  | .legal _,_ => .unit | .burdenEvidence _ _,v => .judgment v
  | .acquisitionEvidence _ _ _ _ _ _,v => .judgment v
  | .offenseEvidence _ _ _ _ _ _,v => .reference .query v.value
  | .storedResJudicata _ _ _ _,v => .boolean v | .contractQuery _ _,v => .judgment v
  | .assignment _ _,v => .formula v | .perform _ _ _,_ => .unit
  | .addTemplate _ _,v => .reference .document v.value | .decide _ _,v => .decision v
  | .bindDecided _ _,_ => .unit | .bindOther _ _,_ => .unit | .learn _ _ _ _,_ => .unit
  | .record _ _,v => .reference .material v.value
  | .admitEvidence _ _ _ _ _,v => .reference .material v.value
  | .withdraw _ _ _,v => .reference .material v.value | .occur _,v => .reference .event v.value
  | .choose _ _ _,v => .reference .relation v.value

def returnedValue {α : Type} (c : Command α) : Answer α → Option Value
  | .success v => some (commandValue c v)
  | _ => none

structure Result (before : Situation) where
  after : Situation
  status : Status
  returned : Option PackedReply
  value : Option Value
  history : History before after

def reject (s : Situation) (status : Status) : Result s :=
  ⟨s,status,none,none,.nil s⟩

def invoke (s : Situation) (p : PackedCommand) : Result s :=
  let actual := executeCommand s p.command
  ⟨actual.after,statusOf actual.answer,some ⟨p.resultType,actual⟩,returnedValue p.command actual.answer,
    (History.nil s).snoc p.command⟩

def runLine (catalog : Catalog) (s : Situation) (line : String) : Result s :=
  match decode line with
  | none => reject s (.rejected .unsupported)
  | some wire =>
    match catalog wire.key with
    | none => reject s (.unknown .inputUnchecked)
    | some p =>
      if commandTag p.command == wire.tag then invoke s p
      else reject s (.rejected .unsupported)

/- The actual parsed request is dispatched to the exact stored command. It
   is neither passed to an unchecked parallel runtime nor evaluated twice. -/
theorem decoded_call_refines (catalog : Catalog) (s : Situation) (line : String)
    (wire : Wire) (p : PackedCommand) (hd : decode line = some wire)
    (hc : catalog wire.key = some p) (ht : commandTag p.command = wire.tag) :
    (runLine catalog s line).after = (executeCommand s p.command).after ∧
    (runLine catalog s line).status = statusOf (executeCommand s p.command).answer ∧
    (runLine catalog s line).history.length = 1 := by
  have hr : runLine catalog s line = invoke s p := by simp [runLine,hd,hc,ht]
  rw [hr]
  exact ⟨rfl,rfl,rfl⟩

theorem malformed_keeps_state (catalog : Catalog) (s : Situation) (line : String)
    (h : decode line = none) : (runLine catalog s line).after = s := by
  simp [runLine,h,reject]

/- All unknown causes and conflict/refusal branches are mapped injectively;
   in particular input absence is not rewritten into legislative absence. -/
theorem unknown_kind_preserved {α : Type} (k : UnknownKind) :
    statusOf (Answer.unknown k : Answer α) = .unknown k := rfl

theorem unknown_labels_distinct :
    Status.unknown .systemNotJudge ≠ .unknown .inputUnchecked ∧
    Status.unknown .lawNotWritten ≠ .unknown .inputUnchecked := by decide

structure Observation where
  after : Situation
  status : Status
  value : Option Value
  steps : Nat

def observe {s : Situation} (actual : Result s) : Observation :=
  ⟨actual.after,actual.status,actual.value,actual.history.length⟩

theorem decoded_value_is_actual (s : Situation) (p : PackedCommand) :
    (observe (invoke s p)).value = returnedValue p.command (executeCommand s p.command).answer := rfl

def serveLine (catalog : Catalog) (s : Situation) (line : String) : IO Observation := do
  let actual := observe (runLine catalog s line)
  IO.println s!"REFERENCE|{repr actual.status}|F={actual.after.core.state.F.length}|L={actual.after.core.state.L.length}|steps={actual.steps}"
  pure actual

def stdioOnce (catalog : Catalog) (s : Situation) : IO Observation := do
  let input ← IO.getStdin
  let line ← input.getLine
  serveLine catalog s line.trimAscii.toString

/- Reuses the same executable serveLine as stdioOnce; synthetic tests below
   exercise success, rejected, unknown, conflict, and S4 actual branches. -/
def testCatalog : Catalog := fun key =>
  match key with
  | 0 => some ⟨_,.legal (Examples.call .decide)⟩
  | 1 => some ⟨_,.legal {Examples.call .decide with mode := .automated}⟩
  | 2 => some ⟨_,.operator ⟨[],[],[]⟩ (.count toyScope)⟩
  | 3 => some ⟨_,.institution .rightsConflict⟩
  | 4 => some ⟨_,.legal {Examples.call .decide with request :=
      {Examples.request .decide with actor := ⟨999⟩}}⟩
  | _ => none

def checkIO : IO Unit := do
  let success ← serveLine testCatalog Examples.normal "legal:0"
  unless success.status == .success do throw (IO.userError "actual legal call failed")
  let missing ← serveLine testCatalog Examples.normal "legal:999"
  unless missing.status == .unknown .inputUnchecked do throw (IO.userError "missing key branch changed")
  let refused ← serveLine testCatalog Examples.refused "legal:1"
  unless refused.status == .blockedHuman do throw (IO.userError "S4 not blocking")
  let conflict ← serveLine testCatalog Examples.normal "institution:3"
  unless conflict.status == .conflict .competentReview do throw (IO.userError "conflict selected a norm")
  let denied ← serveLine testCatalog Examples.normal "legal:4"
  unless denied.status == .rejected .unauthorized do throw (IO.userError "authority bypass")
  let malformed ← serveLine testCatalog Examples.normal "legal:0:extra"
  unless malformed.status == .rejected .unsupported do throw (IO.userError "decoder accepted extra fields")

#eval checkIO
#print axioms decoded_call_refines
#print axioms malformed_keeps_state
#print axioms unknown_kind_preserved
#print axioms unknown_labels_distinct
#print axioms decoded_value_is_actual
end JurisLean.CN.Completion20261105.Runtime
