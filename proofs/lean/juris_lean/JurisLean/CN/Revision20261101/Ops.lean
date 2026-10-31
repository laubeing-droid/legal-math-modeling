import JurisLean.CN.Ops

/-! A dated extension, not a replacement of CN.Walls or CN.Ops.
    The rule language below is a finite represented fragment, not all Chinese law. -/
namespace JurisLean.CN.Revision20261101

open JurisLean.KernelV3
abbrev Op := JurisLean.CN.Ops.Op
abbrev DI := JurisLean.CN.Ops.DI
abbrev UEng := JurisLean.CN.Ops.UEng

inductive IdKind
  | actor | object | matter | event | material | rule | document | query | relation | model
  deriving DecidableEq, Repr

structure Ref (kind : IdKind) where
  value : Nat
  deriving DecidableEq, Repr

structure Scope where
  matter : Ref .matter
  object : Ref .object
  question : Ref .query
  deriving DecidableEq, Repr

inductive UnknownKind
  | systemNotJudge | inputUnchecked | lawNotWritten
  deriving DecidableEq, Repr

inductive Check (α : Type)
  | known (value : α)
  | unknown (reason : UnknownKind)
  deriving DecidableEq, Repr

inductive UnitKind
  | money | day | count | information | scalar
  deriving DecidableEq, Repr

structure Quantity (unit : UnitKind) where
  value : Rat
  deriving DecidableEq, Repr

structure NormRef where
  id : Ref .rule
  version : Nat
  source : JurisLean.CN.Walls.SourceKind
  lawSource : JurisLean.CN.Walls.inN source ≠ .no

inductive ReasoningSource
  | policy | minutes | scholarship | advocacy
  deriving DecidableEq, Repr

structure Atom where
  scope : Scope
  predicate : Ref .query
  deriving DecidableEq, Repr

inductive Formula
  | atom (a : Atom)
  | both (a b : Formula)
  | either (a b : Formula)
  | neg (a : Formula)
  deriving DecidableEq, Repr

def andJ : Judgment → Judgment → Judgment
  | .notEstablished, _ => .notEstablished
  | _, .notEstablished => .notEstablished
  | .established, .established => .established
  | _, _ => .undetermined

def orJ : Judgment → Judgment → Judgment
  | .established, _ => .established
  | _, .established => .established
  | .notEstablished, .notEstablished => .notEstablished
  | _, _ => .undetermined

def notJ : Judgment → Judgment
  | .established => .notEstablished
  | .notEstablished => .established
  | .undetermined => .undetermined

def evalFormula (v : Atom → Judgment) : Formula → Judgment
  | .atom a => v a
  | .both a b => andJ (evalFormula v a) (evalFormula v b)
  | .either a b => orJ (evalFormula v a) (evalFormula v b)
  | .neg a => notJ (evalFormula v a)

inductive Role
  | court | procurator | party | registrar | administrator | lawyer
  deriving DecidableEq, Repr

inductive Act
  | decide | constitute | perform | choose | addTemplate | admitEvidence | otherBind
  deriving DecidableEq, Repr

structure Request where
  actor : Ref .actor
  scope : Scope
  rule : Ref .rule
  version : Nat
  time : Nat
  act : Act
  deriving DecidableEq, Repr

structure Grant where
  actor : Ref .actor
  role : Role
  scope : Scope
  rule : Ref .rule
  version : Nat
  start : Nat
  stop : Nat
  act : Act
  document : Ref .document
  deriving DecidableEq, Repr

def roleAllows (r : Role) : Act → Bool
  | .addTemplate | .decide => r == .court || r == .procurator
  | .choose => r == .party
  | _ => true

def grantMatches (g : Grant) (r : Request) : Bool :=
  g.actor == r.actor && g.scope == r.scope && g.rule == r.rule &&
  g.version == r.version && g.act == r.act &&
  decide (g.start ≤ r.time ∧ r.time ≤ g.stop) && roleAllows g.role r.act

structure LegalRelation where
  id : Ref .relation
  holder : Ref .actor
  counterparty : Ref .actor
  scope : Scope
  objectKind : JurisLean.CN.Walls.ObjKind
  right : JurisLean.CN.Walls.RightKind
  deriving DecidableEq, Repr

structure Rule where
  source : NormRef
  scope : Scope
  guard : Formula
  materials : List (Ref .material)
  effect : EffectType
  formed : Option LegalRelation

structure Param where
  version : Nat
  rules : List Rule
  grants : List Grant

def authorized (p : Param) (r : Request) : Bool :=
  p.grants.any (fun g => grantMatches g r)

def ruleMatches (r : Request) (eff : EffectType) (v : Atom → Judgment)
    (law : Rule) : Bool :=
  law.source.id == r.rule && law.source.version == r.version &&
  law.scope == r.scope && law.effect == eff &&
  evalFormula v law.guard == .established

def applicable (p : Param) (r : Request) (eff : EffectType)
    (v : Atom → Judgment) : Bool :=
  p.version == r.version && p.rules.any (ruleMatches r eff v)

theorem no_grants_no_authority (v : Nat) (rs : List Rule) (r : Request) :
    authorized ⟨v, rs, []⟩ r = false := rfl

theorem lawyer_cannot_add_template : roleAllows .lawyer .addTemplate = false := rfl

theorem court_name_alone_insufficient (r : Request) :
    authorized ⟨r.version, [], []⟩ r = false := rfl

theorem false_conjunct_decisive (j : Judgment) :
    andJ .notEstablished j = .notEstablished := rfl

theorem unknown_not_false :
    andJ .undetermined .established = .undetermined := rfl

/- Nine signatures retain their distinct result types. They are a typed interface;
   complete law-bound interpreters are not claimed by these declarations. -/
structure AnchorRequest where
  scope : Scope
  source : Ref .document
  version : Nat

structure Clock where
  scope : Scope
  anchor : Ref .event
  calendarVersion : Nat
  elapsed : Quantity .day
  threshold : Quantity .day

structure WitnessRequest where
  material : Ref .material
  scope : Scope
  rule : Ref .rule

structure ViewRequest where
  viewer : Ref .actor
  scope : Scope
  purpose : Ref .query
  cutoff : Nat

structure ExchangeRequest where
  first : Ref .event
  second : Ref .event
  observation : ViewRequest

inductive Primitive : Type → Type
  | anchor (r : AnchorRequest) : Primitive (Check (List (Ref .event)))
  | measure (u : UnitKind) (scope : Scope) : Primitive (Check (Quantity u))
  | exclude (a b : Set Nat) : Primitive (Set Nat)
  | adjust (c : Clock) (rule : Ref .rule) : Primitive (Check Clock)
  | expire (c : Clock) : Primitive (Check Bool)
  | witness (r : WitnessRequest) : Primitive (Check (Ref .document))
  | count (scope : Scope) : Primitive (Check Nat)
  | project (r : ViewRequest) : Primitive (List (Ref .event))
  | commute (r : ExchangeRequest) : Primitive (Check Bool)

def Primitive.kind {α : Type} : Primitive α → Op
  | .anchor _ => .anchor
  | .measure _ _ => .measure
  | .exclude _ _ => .exclude
  | .adjust _ _ => .adjust
  | .expire _ => .expire
  | .witness _ => .witness
  | .count _ => .count
  | .project _ => .project
  | .commute _ => .commute

/- Concrete, unit-preserving clock query; its result is not a legal effect. -/
def expireClock (c : Clock) : Bool := decide (c.threshold.value ≤ c.elapsed.value)

def excludeTimes (a b : Set Nat) : Set Nat := a \ b

inductive ConflictKind
  | law105 | admin105 | sameMaker106 | localDepartment106 | constitutionalReview
  deriving DecidableEq, Repr

inductive ReviewRoute
  | npcStanding | stateCouncil | maker | stateCouncilThenNPC | competentReview
  deriving DecidableEq, Repr

def reviewRoute : ConflictKind → ReviewRoute
  | .law105 => .npcStanding
  | .admin105 => .stateCouncil
  | .sameMaker106 => .maker
  | .localDepartment106 => .stateCouncilThenNPC
  | .constitutionalReview => .competentReview

inductive Resolve
  | selected (rule : Ref .rule)
  | adjudicate (route : ReviewRoute)
  | unknown (kind : UnknownKind)
  deriving DecidableEq, Repr

def unresolvedConflict (c : ConflictKind) : Resolve := .adjudicate (reviewRoute c)

theorem unresolved_ne_selected (c : ConflictKind) (r : Ref .rule) :
    unresolvedConflict c ≠ .selected r := by
  intro h
  cases c <;> cases h

theorem article105_routes_differ : reviewRoute .law105 ≠ reviewRoute .admin105 := by decide

/- No scalar legal score is a field of this result. Numerical engine payloads
   stay separate. This is an API restriction, not an impossibility theorem. -/
structure Disposition where
  source : NormRef
  request : Request
  document : Ref .document

inductive Evaluation
  | pending (why : UnknownKind)
  | conflict (route : ReviewRoute)
  | final (answer : EvalResult Disposition)

structure EngineOutput where
  engine : UEng
  scope : Scope
  sourceHistory : List (Ref .event)
  theoremRef : String
  payload : String

structure Candidate where
  scope : Scope
  parentModel : Ref .model
  basis : List EngineOutput
  proposed : Formula

/- A law may license examination of a named statistic; this does not prove causation. -/
structure CausalPermit where
  source : NormRef
  scope : Scope
  statistic : Ref .query

def bridgeCandidate (permit : Option CausalPermit) (output : EngineOutput) : Check EngineOutput :=
  match permit with
  | none => .unknown .inputUnchecked
  | some p => if p.scope == output.scope then .known output else .unknown .inputUnchecked

theorem no_causal_permit_no_bridge (out : EngineOutput) :
    bridgeCandidate none out = .unknown .inputUnchecked := rfl

end JurisLean.CN.Revision20261101
