import JurisLean.CN.Completion20261105.Exchange

/-!
Actual nine-operator interpreter. Parameters are source links and permission/
clock policies, not arbitrary state transformers. All operators consume the
same Situation as the institutional commands. Arithmetic results are material,
not a legal Judgment. Unsupported input, not missing law, is inputUnchecked.
-/
namespace JurisLean.CN.Completion20261105
open JurisLean.KernelV3
open JurisLean.CN.Revision20261101

structure AnchorLink where
  source : Ref .document
  event : Ref .event
  scope : Scope
  version : Nat

inductive ChangeKind
  | advance | extend | restart | cap | suspend | resume
  deriving DecidableEq, Repr

structure ClockPolicy where
  scope : Scope
  norm : NormRef
  allowed : List ChangeKind
  action : Act

structure ViewPermit where
  grant : Grant
  purpose : Ref .query

structure OperatorParams where
  anchors : List AnchorLink
  clocks : List ClockPolicy
  views : List ViewPermit

structure Change where
  kind : ChangeKind
  amount : Quantity .day
  anchor : Ref .event

def registeredNorm (s : Situation) (n : NormRef) : Bool :=
  n.version == s.core.state.N.version &&
  s.core.state.N.rules.any (fun r => r.source.id == n.id && r.source.version == n.version)

def freshRequest (s : Situation) (r : Request) : Bool :=
  authorized s.core.state.N r && r.version == s.core.state.N.version

def admittedSource (s : Situation) (source : Ref .document) (scope : Scope) : Bool :=
  s.core.keys.any (fun i =>
    match s.core.state.E i with
    | .accepted raw _ => raw.source == source && raw.atom.scope == scope
    | _ => false)

def anchorQuery (p : OperatorParams) (s : Situation) (r : AnchorRequest) :
    Reply (List (Ref .event)) :=
  if r.version != s.core.state.N.version || !admittedSource s r.source r.scope then
    quiet s (.unknown .inputUnchecked)
  else
    let links := p.anchors.filter (fun l =>
      l.source == r.source && l.scope == r.scope && l.version == r.version &&
      s.core.state.F.any (fun e => e.id == l.event && e.atom.scope == l.scope))
    match links with
    | [] => quiet s (.unknown .inputUnchecked)
    | _ => quiet s (.success ((links.map (fun l => l.event)).eraseDups))

def clockAt (s : Situation) (scope : Scope) : Option Clock :=
  match s.core.state.clocks.filter (fun c => c.scope == scope) with
  | [clock] => some clock
  | _ => none

def exactDatum (u : UnitKind) (out : EngineOutput) : Option (Quantity u) :=
  match out.engine, out.payload with
  | .exact, ⟨v, quantity⟩ => if h : v = u then some (h ▸ quantity) else none
  | _, _ => none

def measureQuery (s : Situation) (u : UnitKind) (scope : Scope) : Reply (Quantity u) :=
  match u with
  | .money =>
    let xs := s.core.state.ledger.filter (fun p => p.request.scope == scope)
    quiet s (.success ⟨xs.foldl (fun total p => total + p.amount.value) 0⟩)
  | .day =>
    match clockAt s scope with
    | none => quiet s (.unknown .inputUnchecked)
    | some c => quiet s (.success c.elapsed)
  | .count =>
    let ids := ((s.core.state.F.filter (fun e => e.atom.scope == scope)).map (fun e => e.id)).eraseDups
    quiet s (.success ⟨ids.length⟩)
  | unit =>
    let outs := (s.core.state.candidates.flatMap (fun c => c.basis)).filter
      (fun o => o.scope == scope)
    match (outs.filterMap (exactDatum unit)).head? with
    | none => quiet s (.unknown .inputUnchecked)
    | some q => quiet s (.success q)

def excludeQuery (s : Situation) (times removed : List Nat) : Reply (List Nat) :=
  quiet s (.success ((times.filter (fun t => !removed.contains t)).eraseDups))

def changedClock (c : Clock) (d : Change) : Clock :=
  match d.kind with
  | .advance => {c with elapsed := ⟨c.elapsed.value + d.amount.value⟩}
  | .extend => {c with threshold := ⟨c.threshold.value + d.amount.value⟩}
  | .restart => {c with anchor := d.anchor, elapsed := ⟨0⟩}
  | .cap => {c with threshold := ⟨min c.threshold.value d.amount.value⟩}
  | .suspend | .resume => c

/- C2: exact arithmetic schema, separately from its concrete IO instance. -/
theorem advance_clock_exact (c : Clock) (q : Quantity .day) (anchor : Ref .event) :
    (changedClock c ⟨.advance,q,anchor⟩).elapsed.value = c.elapsed.value + q.value ∧
    (changedClock c ⟨.advance,q,anchor⟩).threshold = c.threshold := ⟨rfl,rfl⟩

def adjustQuery (p : OperatorParams) (s : Situation) (r : Request) (mode : Mode)
    (d : Change) : Reply Clock :=
  if automationAllowed s.core.state r.scope mode = false then quiet s .blockedHuman
  else if freshRequest s r = false then quiet s (.rejected .unauthorized)
  else if p.clocks.any (fun policy =>
      policy.scope == r.scope && policy.norm.id == r.rule &&
      registeredNorm s policy.norm && policy.allowed.contains d.kind && policy.action == r.act) = false then
    quiet s (.unknown .inputUnchecked)
  else if d.amount.value < 0 then quiet s (.rejected .prerequisites)
  else
    match clockAt s r.scope with
    | none => quiet s (.unknown .inputUnchecked)
    | some clock =>
      if d.kind == .advance && s.paused.contains r.scope then
        quiet s (.rejected .prerequisites)
      else if d.kind == .restart &&
          !(s.core.state.F.any (fun e => e.id == d.anchor && e.atom.scope == r.scope)) then
        quiet s (.unknown .inputUnchecked)
      else
        let next := changedClock clock d
        let clocks := s.core.state.clocks.map (fun c => if c.scope == r.scope then next else c)
        let st := {s.core.state with clocks := clocks}
        let paused := match d.kind with
          | .suspend => r.scope :: s.paused
          | .resume => s.paused.filter (fun scope => scope != r.scope)
          | _ => s.paused
        ⟨{s with core := {s.core with state := st}, paused := paused}, .success next⟩

def expireQuery (s : Situation) (scope : Scope) : Reply Bool :=
  match clockAt s scope with
  | none => quiet s (.unknown .inputUnchecked)
  | some c => quiet s (.success (expireClock c))

def witnessQuery (s : Situation) (r : WitnessRequest) : Reply (Ref .document) :=
  match s.core.state.E r.material with
  | .accepted raw rc =>
    if raw.atom.scope == r.scope && rc.norm.id == r.rule &&
        rc.norm.version == s.core.state.N.version then quiet s (.success rc.document)
    else quiet s (.unknown .inputUnchecked)
  | _ => quiet s (.unknown .inputUnchecked)

def countQuery (s : Situation) (scope : Scope) : Reply Nat :=
  quiet s (.success (((s.core.state.F.filter (fun e => e.atom.scope == scope)).map
    (fun e => e.id)).eraseDups.length))

def viewAllowed (p : OperatorParams) (s : Situation) (r : ViewRequest) : Bool :=
  p.views.any (fun permission =>
    permission.purpose == r.purpose && s.core.state.N.grants.contains permission.grant &&
    grantMatches permission.grant
      ⟨r.viewer, r.scope, permission.grant.rule, s.core.state.N.version, r.cutoff, .otherBind⟩)

def projectQuery (p : OperatorParams) (s : Situation) (r : ViewRequest) :
    Reply (List (Ref .event)) :=
  if viewAllowed p s r then
    quiet s (.success ((s.core.state.F.filter (fun e =>
      e.atom.scope == r.scope && decide (e.occurredAt ≤ r.cutoff))).map (fun e => e.id)))
  else quiet s (.rejected .unauthorized)

def assignmentAllowed (s : Situation) (a : MeaningAssignment) (r : Request) : Bool :=
  freshRequest s r && r.act == .decide && institutionAllowed s r .interpretation &&
    r.scope.object == a.target && (a.expression.eval s.meanings).isSome

def assignmentQuery (s : Situation) (a : MeaningAssignment) (r : Request) : Reply Formula :=
  if automationAllowed s.core.state r.scope .automated = false then quiet s .blockedHuman
  else if assignmentAllowed s a r then assignLocal s a else quiet s (.rejected .unauthorized)

/- C2/A02: the public assignment is gated, so the store algebra alone is
   insufficient. This lemma states the exact gate-stability condition that
   the subsequent actual-call composition needs. The expression condition is
   an input evaluation equality, not the desired commutation conclusion. -/
theorem assignment_gate_stable (s : Situation) (a b : MeaningAssignment) (r : Request)
    (hb : b.expression.eval (assignLocal s a).after.meanings = b.expression.eval s.meanings) :
    assignmentAllowed (assignLocal s a).after b r = assignmentAllowed s b r := by
  have hn : (assignLocal s a).after.core.state.N = s.core.state.N := by
    unfold assignLocal
    split <;> rfl
  have hu : (assignLocal s a).after.uses = s.uses := by
    unfold assignLocal
    split <;> rfl
  simp only [assignmentAllowed, freshRequest, institutionAllowed, hn, hu, hb]

theorem actual_assignments_commute (s : Situation) (a b : MeaningAssignment)
    (ra rb : Request) (h : Independent a b)
    (ga : assignmentAllowed s a ra = true) (gb : assignmentAllowed s b rb = true)
    (ma : automationAllowed s.core.state ra.scope .automated = true)
    (mb : automationAllowed s.core.state rb.scope .automated = true)
    (fa fb : Formula) (ha : a.expression.eval s.meanings = some fa)
    (hb : b.expression.eval s.meanings = some fb) :
    (assignmentQuery (assignmentQuery s a ra).after b rb).after.meanings =
      (assignmentQuery (assignmentQuery s b rb).after a ra).after.meanings := by
  have va := assignLocal_view s a fa ha
  have vb := assignLocal_view s b fb hb
  have ea : a.expression.eval (assignLocal s b).after.meanings = a.expression.eval s.meanings := by
    rw [vb, expression_after_unread_write a.expression b s.meanings h.2.2]
  have eb : b.expression.eval (assignLocal s a).after.meanings = b.expression.eval s.meanings := by
    rw [va, expression_after_unread_write b.expression a s.meanings h.2.1]
  have gba := assignment_gate_stable s a b rb eb
  have gab := assignment_gate_stable s b a ra ea
  have preserve (z : MeaningAssignment) :
      (assignLocal s z).after.core.state.refusals = s.core.state.refusals := by
    unfold assignLocal
    split <;> rfl
  have pma : automationAllowed (assignLocal s b).after.core.state ra.scope .automated = true := by
    simpa only [automationAllowed, preserve] using ma
  have pmb : automationAllowed (assignLocal s a).after.core.state rb.scope .automated = true := by
    simpa only [automationAllowed, preserve] using mb
  simpa [assignmentQuery, ma, mb, ga, gb, gba, gab, pma, pmb] using
    assignment_two_defined s a b fa fb h ha hb

def commuteQuery (s : Situation) (a b : MeaningAssignment) (ra rb : Request) : Reply Bool :=
  if assignmentAllowed s a ra && assignmentAllowed s b rb then
    if Independent a b then quiet s (.success true)
    else
      let ab := (assignLocal (assignLocal s a).after b).after.meanings
      let ba := (assignLocal (assignLocal s b).after a).after.meanings
      if ab a.target != ba a.target || ab b.target != ba b.target then
        quiet s (.success false)
      else quiet s (.unknown .systemNotJudge)
  else quiet s (.rejected .unauthorized)

inductive OpRequest : Type → Type
  | anchor (r : AnchorRequest) : OpRequest (List (Ref .event))
  | measure (u : UnitKind) (scope : Scope) : OpRequest (Quantity u)
  | exclude (times removed : List Nat) : OpRequest (List Nat)
  | adjust (r : Request) (mode : Mode) (change : Change) : OpRequest Clock
  | expire (scope : Scope) : OpRequest Bool
  | witness (r : WitnessRequest) : OpRequest (Ref .document)
  | count (scope : Scope) : OpRequest Nat
  | project (r : ViewRequest) : OpRequest (List (Ref .event))
  | commute (a b : MeaningAssignment) (ra rb : Request) : OpRequest Bool

def runOperator (p : OperatorParams) (s : Situation) {α : Type} : OpRequest α → Reply α
  | .anchor r => anchorQuery p s r
  | .measure u scope => measureQuery s u scope
  | .exclude ts removed => excludeQuery s ts removed
  | .adjust r mode d => adjustQuery p s r mode d
  | .expire scope => expireQuery s scope
  | .witness r => witnessQuery s r
  | .count scope => countQuery s scope
  | .project r => projectQuery p s r
  | .commute a b ra rb => commuteQuery s a b ra rb

/- Obligations: every known-true commute is linked to actual state updates;
   read/write and shared authorization gate stability were proved in Exchange. -/
theorem commute_true_sound (s : Situation) (a b : MeaningAssignment) (ra rb : Request)
    (h : (commuteQuery s a b ra rb).answer = .success true) :
    (assignLocal (assignLocal s a).after b).after.meanings =
      (assignLocal (assignLocal s b).after a).after.meanings := by
  unfold commuteQuery at h
  split at h
  · rename_i hg
    split at h
    · rename_i hi
      have both : assignmentAllowed s a ra = true ∧ assignmentAllowed s b rb = true := by
        simpa only [Bool.and_eq_true] using hg
      have ag : (a.expression.eval s.meanings).isSome = true := by
        have hg := both.1
        simp only [assignmentAllowed, Bool.and_eq_true] at hg
        exact hg.2
      have bg : (b.expression.eval s.meanings).isSome = true := by
        have hg := both.2
        simp only [assignmentAllowed, Bool.and_eq_true] at hg
        exact hg.2
      have defined := And.intro ag bg
      cases ha : a.expression.eval s.meanings with
      | none => simp [ha] at defined
      | some fa =>
        cases hb : b.expression.eval s.meanings with
        | none => simp [hb] at defined
        | some fb => exact assignment_two_defined s a b fa fb hi ha hb
    · dsimp only at h
      split at h <;> cases h
  · cases h

theorem adjustment_no_authority (p : OperatorParams) (s : Situation) (r : Request)
    (m : Mode) (d : Change) (h : freshRequest s r = false) :
    (adjustQuery p s r m d).after = s := by
  by_cases hm : automationAllowed s.core.state r.scope m = false <;>
    simp [adjustQuery, hm, h, quiet]

theorem expiry_not_extinction (s : Situation) (scope : Scope) :
    (expireQuery s scope).after.core.state.L = s.core.state.L := by
  unfold expireQuery
  split <;> rfl

theorem project_denied (p : OperatorParams) (s : Situation) (r : ViewRequest)
    (h : viewAllowed p s r = false) :
    (projectQuery p s r).answer = .rejected .unauthorized := by
  simp [projectQuery, h, quiet]

theorem witness_pending (s : Situation) (r : WitnessRequest) (raw : Raw r.material)
    (h : s.core.state.E r.material = .pending raw) :
    (witnessQuery s r).answer = .unknown .inputUnchecked := by
  simp [witnessQuery, h, quiet]

#print axioms advance_clock_exact
#print axioms commute_true_sound
#print axioms assignment_gate_stable
#print axioms actual_assignments_commute
#print axioms adjustment_no_authority
#print axioms expiry_not_extinction
#print axioms project_denied
#print axioms witness_pending
end JurisLean.CN.Completion20261105

