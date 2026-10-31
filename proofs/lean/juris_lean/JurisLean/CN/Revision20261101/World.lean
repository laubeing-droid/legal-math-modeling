import JurisLean.CN.Revision20261101.Rights

namespace JurisLean.CN.Revision20261101

open JurisLean.KernelV3

structure Raw (id : Ref .material) where
  atom : Atom
  asserted : Bool
  source : Ref .document
  observedAt : Nat
  deriving DecidableEq, Repr

/- These are checked input receipts, not a claim that a document proves its
   own authenticity. The external verifier and its refinement remain separate. -/
structure Receipt {id : Ref .material} (raw : Raw id) where
  document : Ref .document
  issuer : Ref .actor
  norm : NormRef
  sourceGate : Bool
  factGate : Bool
  ruleGate : Bool
  passed : sourceGate = true ∧ factGate = true ∧ ruleGate = true

inductive EvidenceCell (id : Ref .material)
  | absent
  | pending (raw : Raw id)
  | accepted (raw : Raw id) (receipt : Receipt raw)
  | excluded (raw : Raw id) (reason : Ref .document)

abbrev Evidence := (id : Ref .material) → EvidenceCell id

def rawOf {i : Ref .material} : EvidenceCell i → Option (Raw i)
  | .absent => none
  | .pending r | .accepted r _ | .excluded r _ => some r

def isAdmitted {i : Ref .material} : EvidenceCell i → Bool
  | .accepted _ _ => true
  | _ => false

def isExcluded {i : Ref .material} : EvidenceCell i → Bool
  | .excluded _ _ => true
  | _ => false

def Evidence.raws (e : Evidence) : Set (Ref .material) := fun i => (rawOf (e i)).isSome
def Evidence.admitted (e : Evidence) : Set (Ref .material) := fun i => isAdmitted (e i)
def Evidence.excluded (e : Evidence) : Set (Ref .material) := fun i => isExcluded (e i)

def setEvidence (e : Evidence) (i : Ref .material) (c : EvidenceCell i) : Evidence :=
  fun j => if h : j = i then h.symm ▸ c else e j

structure AdmittedItem where
  id : Ref .material
  raw : Raw id
  receipt : Receipt raw

def admittedAt (e : Evidence) (i : Ref .material) : Option AdmittedItem :=
  match e i with
  | .accepted raw receipt => some ⟨i, raw, receipt⟩
  | _ => none

def admittedView (e : Evidence) (ids : List (Ref .material)) : List AdmittedItem :=
  ids.filterMap (admittedAt e)

def support (es : List AdmittedItem) (a : Atom) : Judgment :=
  let pos := es.any fun x => x.raw.atom == a && x.raw.asserted
  let neg := es.any fun x => x.raw.atom == a && !x.raw.asserted
  match pos, neg with
  | true, false => .established
  | false, true => .notEstablished
  | _, _ => .undetermined

/- This interface separates weight/standard/burden policy from admissibility. -/
def burden (policy : List AdmittedItem → EvalResult Disposition)
    (e : Evidence) (ids : List (Ref .material)) : EvalResult Disposition :=
  policy (admittedView e ids)

theorem buckets_disjoint {i : Ref .material} (c : EvidenceCell i) :
    ¬ (isAdmitted c = true ∧ isExcluded c = true) := by
  cases c <;> decide

theorem admitted_implies_raw {i : Ref .material} (c : EvidenceCell i)
    (h : isAdmitted c = true) : (rawOf c).isSome = true := by
  cases c <;> simp_all [isAdmitted, rawOf]

theorem absent_not_admitted {i : Ref .material} :
    isAdmitted (EvidenceCell.absent : EvidenceCell i) = false := rfl

theorem excluded_keeps_raw {i : Ref .material} (r : Raw i) (reason : Ref .document) :
    rawOf (.excluded r reason) = some r := rfl

inductive SharedConstraint
  | exclusive (a b : LegalRelation)
  | sameLoss (a b : LegalRelation)
  | equalReduction (a b : LegalRelation)

structure PossibleWorld where
  fact : Atom → Bool
  active : LegalRelation → Bool
  lossIdentity : LegalRelation → Ref .event
  reduction : LegalRelation → Quantity .money

def satisfies (w : PossibleWorld) : SharedConstraint → Prop
  | .exclusive a b => ¬ (w.active a = true ∧ w.active b = true)
  | .sameLoss a b => w.lossIdentity a = w.lossIdentity b
  | .equalReduction a b => w.reduction a = w.reduction b

inductive DecideKind
  | resJudicata | constitutive | executable | evidential | procedural
  deriving DecidableEq, Repr

inductive OtherSource
  | persuasive (document : Ref .document)
  | referential (document : Ref .document) (norm : NormRef)
  | credit (document : Ref .document) (norm : NormRef)
  | publicValidity (document : Ref .document) (norm : NormRef)

structure DecisionRecord where
  document : Ref .document
  request : Request
  judgment : Judgment
  valid : Bool
  deriving DecidableEq, Repr

structure DecideBinding where
  decision : DecisionRecord
  kind : DecideKind
  index : BindingIndex
  effective : decision.valid = true
  scoped : index.subject = decision.request.scope

structure OtherBinding where
  source : OtherSource
  index : BindingIndex
  request : Request
  scoped : index.subject = request.scope

inductive Binding
  | decide (b : DecideBinding)
  | other (b : OtherBinding)

structure Occurrence where
  id : Ref .event
  actor : Ref .actor
  atom : Atom
  occurredAt : Nat
  deriving DecidableEq, Repr

structure AIState where
  model : Ref .model
  version : Nat
  theta : List Rat

structure Performance where
  event : Ref .event
  relation : Ref .relation
  amount : Quantity .money
  request : Request

/- Coherence is partly intrinsic: evidence is keyed, receipts depend on the
   exact raw item, all endpoints are typed, and K is derived from shared facts
   and constraints. No actual-world truth is assumed for admitted testimony. -/
structure Sit where
  F : List Occurrence
  E : Evidence
  N : Param
  L : List LegalRelation
  constraints : List SharedConstraint
  candidates : List Candidate
  A : AIState
  bindings : List Binding
  decisions : List DecisionRecord
  ledger : List Performance
  clocks : List Clock
  proceedings : List (Scope × Ref .event)
  interpretations : List (Ref .object × Formula)
  refusals : List Scope

def compatible (s : Sit) : Set PossibleWorld := fun w =>
  (∀ i raw receipt, s.E i = .accepted raw receipt → w.fact raw.atom = raw.asserted) ∧
  (∀ c, c ∈ s.constraints → satisfies w c)

def relationView (s : Sit) : RelationalState LegalRelation :=
  { relations := {r | r ∈ s.L}
    sameLoss := fun a b => SharedConstraint.sameLoss a b ∈ s.constraints
    exclusive := fun a b => SharedConstraint.exclusive a b ∈ s.constraints
    commonReduction := fun a b => SharedConstraint.equalReduction a b ∈ s.constraints }

def kernel (s : Sit) : KernelState (RelationalState LegalRelation) PossibleWorld :=
  ⟨relationView s, compatible s⟩

def propose (s : Sit) (c : Candidate) : Sit :=
  { s with candidates := c :: s.candidates, A := {s.A with version := s.A.version + 1} }

def learn (s : Sit) (theta : List Rat) (i : Ref .material) (raw : Raw i) : Sit :=
  { s with A := {s.A with theta := theta}, E := setEvidence s.E i (.pending raw) }

def admitEvidence (s : Sit) (i : Ref .material) (raw : Raw i) (receipt : Receipt raw) : Sit :=
  { s with E := setEvidence s.E i (.accepted raw receipt) }

def withdraw (s : Sit) (i : Ref .material) (raw : Raw i) (why : Ref .document) : Sit :=
  { s with E := setEvidence s.E i (.excluded raw why) }

def bindDecision (s : Sit) (b : DecideBinding) : Sit :=
  { s with bindings := .decide b :: s.bindings }

def bindOther (s : Sit) (b : OtherBinding) : Sit :=
  { s with bindings := .other b :: s.bindings }

def effectEvent (s : Sit) (law : Rule) (j : Judgment) : JudgmentEvent (List LegalRelation) :=
  match law.effect with
  | .confirmatory => .confirmatory j
  | .constitutive => .constitutive j (match law.formed with | some r => r :: s.L | none => s.L)
  | .performance => .performance j
  | .proceduralBinding => .proceduralBinding j

def effectAction : EffectType → Act
  | .constitutive => .constitute
  | .performance => .perform
  | _ => .decide

def applyEffect (s : Sit) (e : JudgmentEvent (List LegalRelation)) : Sit :=
  let b : KernelState (List LegalRelation) PossibleWorld := ⟨s.L, compatible s⟩
  {s with L := (transfer b e).R_t}

inductive Mode
  | human | automated
  deriving DecidableEq, Repr

def automationAllowed (s : Sit) (scope : Scope) : Mode → Bool
  | .human => true
  | .automated => !(s.refusals.contains scope)

structure RuleTicket (s : Sit) where
  law : Rule
  member : law ∈ s.N.rules
  /- A conservative unique-rule fragment: unresolved alternatives cannot be chosen. -/
  unique : ∀ other ∈ s.N.rules,
    other.scope = law.scope → other.source.version = law.source.version → other = law

inductive StepStatus
  | applied | unauthorized | blockedHuman | awaiting (reason : UnknownKind)
  deriving DecidableEq, Repr

structure Execution where
  after : Sit
  status : StepStatus

def legalStep (s : Sit) (req : Request) (ticket : RuleTicket s) (mode : Mode) : Execution :=
  if automationAllowed s req.scope mode = false then ⟨s, .blockedHuman⟩
  else if authorized s.N req = false then ⟨s, .unauthorized⟩
  else if req.act != effectAction ticket.law.effect then ⟨s, .unauthorized⟩
  else if (s.N.version == req.version && ruleMatches req ticket.law.effect
      (support (admittedView s.E ticket.law.materials)) ticket.law) = false then
    ⟨s, .awaiting .inputUnchecked⟩
  else if ticket.law.effect == .constitutive && ticket.law.formed.isNone then
    ⟨s, .awaiting .inputUnchecked⟩
  else ⟨applyEffect s (effectEvent s ticket.law .established), .applied⟩

theorem no_authority_no_creation (s : Sit) (r : Request) (t : RuleTicket s) (m : Mode)
    (h : authorized s.N r = false) : (legalStep s r t m).after.L = s.L := by
  simp [legalStep, h]

theorem confirmatory_preserves_relations (s : Sit) (j : Judgment) :
    (applyEffect s (.confirmatory j)).L = s.L := by
  exact congrArg (fun b : KernelState (List LegalRelation) PossibleWorld => b.R_t)
    (transfer_confirmatory_identity ⟨s.L, compatible s⟩ j)

theorem refused_automated_step (s : Sit) (r : Request) (t : RuleTicket s)
    (h : s.refusals.contains r.scope = true) :
    (legalStep s r t .automated).status = .blockedHuman := by
  simp [legalStep, automationAllowed, h]

theorem propose_frame (s : Sit) (c : Candidate) :
    (propose s c).F = s.F ∧ (propose s c).N = s.N ∧
    (propose s c).L = s.L ∧ (propose s c).bindings = s.bindings := ⟨rfl, rfl, rfl, rfl⟩

theorem learn_frame (s : Sit) (theta : List Rat) (i : Ref .material) (raw : Raw i) :
    (learn s theta i raw).F = s.F ∧ (learn s theta i raw).N = s.N ∧
    (learn s theta i raw).L = s.L ∧ (learn s theta i raw).bindings = s.bindings :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem admission_frame (s : Sit) (i : Ref .material) (raw : Raw i) (rc : Receipt raw) :
    (admitEvidence s i raw rc).F = s.F ∧ (admitEvidence s i raw rc).L = s.L := ⟨rfl, rfl⟩

theorem withdrawal_preserves_reality (s : Sit) (i : Ref .material) (raw : Raw i)
    (why : Ref .document) : (withdraw s i raw why).F = s.F := rfl

/- Only these indexed constructors are accepted graph edges. Helper updates
   above are formulas, not independent unchecked admission entrypoints. -/
inductive Event (s : Sit)
  | propose (c : Candidate) (parent : c.parentModel = s.A.model)
  | learn (theta : List Rat) (i : Ref .material) (raw : Raw i)
      (fresh : s.E i = .absent)
  | record (i : Ref .material) (raw : Raw i) (fresh : s.E i = .absent)
  | admitEvidence (i : Ref .material) (raw : Raw i) (rc : Receipt raw)
      (present : s.E i = .pending raw)
  | withdraw (i : Ref .material) (raw : Raw i) (reason : Ref .document)
      (present : rawOf (s.E i) = some raw)
  | occur (o : Occurrence)
  | legal (req : Request) (ticket : RuleTicket s) (mode : Mode)
  | decide (d : DecisionRecord) (auth : authorized s.N d.request = true)
      (kind : d.request.act = .decide) (mode : Mode)
      (humanGate : automationAllowed s d.request.scope mode = true)
  | bindDecision (b : DecideBinding) (present : b.decision ∈ s.decisions) (mode : Mode)
      (humanGate : automationAllowed s b.index.subject mode = true)
  | bindOther (b : OtherBinding) (auth : authorized s.N b.request = true)
      (kind : b.request.act = .otherBind) (mode : Mode)
      (humanGate : automationAllowed s b.index.subject mode = true)

def step (s : Sit) : Event s → Sit
  | .propose c _ => propose s c
  | .learn theta i raw _ => learn s theta i raw
  | .record i raw _ => {s with E := setEvidence s.E i (.pending raw)}
  | .admitEvidence i raw rc _ => admitEvidence s i raw rc
  | .withdraw i raw why _ => withdraw s i raw why
  | .occur o => {s with F := o :: s.F}
  | .legal req ticket mode => (legalStep s req ticket mode).after
  | .decide d _ _ _ _ => {s with decisions := d :: s.decisions}
  | .bindDecision b _ _ _ => bindDecision s b
  | .bindOther b _ _ _ _ => bindOther s b

/- Complete endpoints and event payloads are retained; no quotient is taken. -/
inductive Hist : Sit → Sit → Type
  | nil (s : Sit) : Hist s s
  | snoc {start last : Sit} (h : Hist start last) (e : Event last) :
      Hist start (step last e)

def Hist.length {a b : Sit} : Hist a b → Nat
  | .nil _ => 0
  | .snoc h _ => h.length + 1

theorem append_keeps_history_length {a b : Sit} (h : Hist a b) (e : Event b) :
    (Hist.snoc h e).length = h.length + 1 := rfl

/- A nonjudicial formation has a genuine history and no decision. This is a
   synthetic registration rule, not an assertion about a real registry. -/
def toyScope : Scope := ⟨⟨1⟩, ⟨2⟩, ⟨3⟩⟩
def toyAtom : Atom := ⟨toyScope, ⟨4⟩⟩
def toyNorm : NormRef := ⟨⟨5⟩, 1, .statute, by decide⟩
def toyRelation : LegalRelation := ⟨⟨6⟩, ⟨7⟩, ⟨8⟩, toyScope, .status, .form⟩
def toyRaw : Raw ⟨9⟩ := ⟨toyAtom, true, ⟨10⟩, 0⟩
def toyReceipt : Receipt toyRaw := ⟨⟨11⟩, ⟨12⟩, toyNorm, true, true, true, by decide⟩
def toyRule : Rule := ⟨toyNorm, toyScope, .atom toyAtom, [⟨9⟩], .constitutive, some toyRelation⟩
def toyRequest : Request := ⟨⟨12⟩, toyScope, ⟨5⟩, 1, 0, .constitute⟩
def toyGrant : Grant := ⟨⟨12⟩, .registrar, toyScope, ⟨5⟩, 1, 0, 10, .constitute, ⟨13⟩⟩

def initial : Sit :=
  { F := [], E := fun _ => .absent, N := ⟨1, [toyRule], [toyGrant]⟩,
    L := [], constraints := [], candidates := [], A := ⟨⟨14⟩, 0, []⟩,
    bindings := [], decisions := [], ledger := [], clocks := [], proceedings := [],
    interpretations := [], refusals := [] }

def recorded : Sit := {initial with E := setEvidence initial.E ⟨9⟩ (.pending toyRaw)}
def prepared : Sit := admitEvidence recorded ⟨9⟩ toyRaw toyReceipt

def toyTicket : RuleTicket prepared :=
  { law := toyRule
    member := by simp [prepared, admitEvidence, recorded, initial]
    unique := by
      intro other h _ _
      simpa [prepared, admitEvidence, recorded, initial] using h }

def recordEvent : Event initial := .record ⟨9⟩ toyRaw rfl
def admitEvent : Event recorded := .admitEvidence ⟨9⟩ toyRaw toyReceipt (by
  simp [recorded, setEvidence])
def formEvent : Event prepared := .legal toyRequest toyTicket .human
def formed : Sit := step prepared formEvent

def nonjudicialHistory : Hist initial formed :=
  .snoc (.snoc (.snoc (.nil initial) recordEvent) admitEvent) formEvent

theorem nonjudicial_formation_exists :
    formed.L = [toyRelation] ∧ formed.decisions = [] ∧ nonjudicialHistory.length = 3 := by
  decide

theorem no_receipt_no_guard_support :
    support (admittedView recorded.E [⟨9⟩]) toyAtom = .undetermined := by decide

theorem admitted_guard_has_support :
    support (admittedView prepared.E [⟨9⟩]) toyAtom = .established := by decide

def withdrawn : Sit := withdraw prepared ⟨9⟩ toyRaw ⟨15⟩

theorem withdrawal_removes_support :
    support (admittedView withdrawn.E [⟨9⟩]) toyAtom = .undetermined := by decide

theorem withdrawal_keeps_excluded_and_raw :
    isExcluded (withdrawn.E ⟨9⟩) = true ∧ rawOf (withdrawn.E ⟨9⟩) = some toyRaw := by decide

def toyCandidate : Candidate := ⟨toyScope, ⟨14⟩, [], .atom toyAtom⟩

theorem proposal_is_not_learning :
    (propose initial toyCandidate).A.theta ≠ (learn initial [1] ⟨9⟩ toyRaw).A.theta := by decide

/- Audit the actual transitive dependencies of representative new theorems. -/
#print axioms buckets_disjoint
#print axioms admitted_implies_raw
#print axioms no_authority_no_creation
#print axioms confirmatory_preserves_relations
#print axioms refused_automated_step
#print axioms nonjudicial_formation_exists
#print axioms withdrawal_removes_support

end JurisLean.CN.Revision20261101
