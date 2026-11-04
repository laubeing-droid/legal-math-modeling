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
  | .operator _ _ => .operator
  | .positions _ => .institution
  | .institution _ | .burdenEvidence _ _ | .acquisitionEvidence _ _ _ _ _ _ |
      .offenseEvidence _ _ _ _ _ _ _ | .storedResJudicata _ _ _ _ | .contractQuery _ _ => .institution
  | .engine _ _ | .registerEngine _ _ => .engine
  | .legal _ => .legal
  | .assignment _ _ => .assignment
  | .perform _ _ _ _ => .perform
  | .addTemplate _ _ => .template
  | .decide _ _ => .decide
  | .bindDecided _ _ => .bindDecision
  | .bindOther _ _ => .bindOther
  | .learn _ _ _ _ => .learn
  | .record _ _ => .record
  | .admitEvidence _ _ _ _ _ => .admit
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

structure Result (before : Situation) where
  after : Situation
  status : Status
  returned : Option PackedReply
  history : History before after

def reject (s : Situation) (status : Status) : Result s :=
  ⟨s,status,none,.nil s⟩

def invoke (s : Situation) (p : PackedCommand) : Result s :=
  let actual := executeCommand s p.command
  ⟨actual.after,statusOf actual.answer,some ⟨p.resultType,actual⟩,
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
  simp [runLine, hd, hc, ht, invoke, History.length]

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

def serveLine (catalog : Catalog) (s : Situation) (line : String) : IO (Result s) := do
  let actual := runLine catalog s line
  IO.println s!"REFERENCE|{repr actual.status}|F={actual.after.core.state.F.length}|L={actual.after.core.state.L.length}|steps={actual.history.length}"
  pure actual

def stdioOnce (catalog : Catalog) (s : Situation) : IO (Result s) := do
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
end JurisLean.CN.Completion20261105.Runtime
