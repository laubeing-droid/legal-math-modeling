import JurisLean.CN.Completion20261105.Ready

/-!
V4 section 6: actual institutional calls over the shared Situation.
Rules and receipts are read through legalDispatch, not caller-made Ready tickets.
Local update lemmas below close the missing state/projection part of P11/P12.
Legal grounds are Formula parameters; the actual rule in N must have that guard.
-/
namespace JurisLean.CN.Completion20261105
open JurisLean.KernelV3
open JurisLean.CN.Revision20261101
namespace Law
open InstitutionRules

structure Call where
  request : Request
  policy : ProofPolicy
  mode : Mode
  world : PossibleWorld

def gate (s : Situation) (c : Call) (grounds : Formula) : Reply Unit :=
  if automationAllowed s.core.state c.request.scope c.mode = false then quiet s .blockedHuman
  else match selectedRules s.core c.request with
  | [law] =>
    if law.guard == grounds then legalDispatch s c.request c.policy c.mode c.world
    else quiet s (.rejected .unsupported)
  | _ => legalDispatch s c.request c.policy c.mode c.world

def continueWith {α : Type} (permission : Reply Unit)
    (next : Situation → Reply α) : Reply α :=
  match permission.answer with
  | .success _ => next permission.after
  | .rejected k => ⟨permission.after, .rejected k⟩
  | .unknown k => ⟨permission.after, .unknown k⟩
  | .conflict k => ⟨permission.after, .conflict k⟩
  | .blockedHuman => ⟨permission.after, .blockedHuman⟩

/- The permission check and its institutional continuation form one commit.
   A failed continuation must not retain a staged constitutive effect. -/
def atomic {α : Type} (before : Situation) (staged : Reply α) : Reply α :=
  match staged.answer with
  | .success _ => staged
  | other => quiet before other

theorem atomic_failure_preserves {α : Type} (s : Situation) (r : Reply α)
    (h : ∀ v, r.answer ≠ .success v) : (atomic s r).after = s := by
  cases ha : r.answer <;> simp [atomic, ha, quiet]
  exact (h _ ha).elim

/- Obligations: preserve specified legal unknown/conflict branches; a missing
   implementation is not hidden behind these propagation theorems. -/
theorem unknown_propagates {α : Type} (s : Situation) (k : UnknownKind)
    (next : Situation → Reply α) :
    (continueWith ⟨s, .unknown k⟩ next).answer = .unknown k := rfl

theorem conflict_propagates {α : Type} (s : Situation) (k : ReviewRoute)
    (next : Situation → Reply α) :
    (continueWith ⟨s, .conflict k⟩ next).answer = .conflict k := rfl

def revokeLocal (s : Situation) (obj : Ref .object) (g : RevokeGuard) : Reply CivilActLife :=
  match s.life obj with
  | none => quiet s (.unknown .inputUnchecked)
  | some life =>
    if life.revocationPower && revokeGuardOK g then
      let next := revokeLife life
      let remaining := s.core.state.L.filter (fun r => !(s.actRelations obj).contains r.id)
      let st := applyEffect s.core.state (.constitutive .established remaining)
      ⟨{s with
        life := assign s.life obj (some next)
        core := {s.core with state := st}}, .success next⟩
    else quiet s (.rejected .prerequisites)

def revoke (s : Situation) (c : Call) (grounds : Formula)
    (obj : Ref .object) (g : RevokeGuard) : Reply CivilActLife :=
  atomic s (if c.request.actor == g.holder && c.request.scope.object == obj then
    continueWith (gate s c grounds) (fun z => revokeLocal z obj g)
  else quiet s (.rejected .unauthorized))

/- The lifecycle is read from the actual common object. Scope/frame are
   conclusions of the update, rather than unused c1/c2 parameters. -/
theorem revoke_effective_and_power (s : Situation) (obj : Ref .object)
    (life : CivilActLife) (g : RevokeGuard) (hl : s.life obj = some life)
    (hp : life.revocationPower = true) (hg : revokeGuardOK g = true) :
    ∃ updated, (revokeLocal s obj g).after.life obj = some updated ∧
      updated.effective = false ∧ updated.revocationPower = false ∧
      updated.established = life.established := by
  refine ⟨revokeLife life, ?_, rfl, rfl, rfl⟩
  simp [revokeLocal, hl, hp, hg, assign]

theorem revoke_other_object (s : Situation) (a b : Ref .object) (g : RevokeGuard)
    (h : b ≠ a) : (revokeLocal s a g).after.life b = s.life b := by
  unfold revokeLocal
  split
  · rfl
  · split
    · simp [assign, h]
    · rfl

theorem revoke_natural_facts (s : Situation) (obj : Ref .object) (g : RevokeGuard) :
    (revokeLocal s obj g).after.core.state.F = s.core.state.F := by
  unfold revokeLocal
  split
  · rfl
  · split <;> rfl

theorem revocation_removes_tracked_relations (s : Situation) (obj : Ref .object)
    (life : CivilActLife) (g : RevokeGuard) (hl : s.life obj = some life)
    (hp : life.revocationPower = true) (hg : revokeGuardOK g = true)
    (r : LegalRelation) (hr : r.id ∈ s.actRelations obj) :
    r ∉ (revokeLocal s obj g).after.core.state.L := by
  intro hm
  have hf : r ∈ s.core.state.L.filter (fun q => !(s.actRelations obj).contains q.id) := by
    simpa [revokeLocal, hl, hp, hg, applyEffect, transfer] using hm
  have hn := (List.mem_filter.mp hf).2
  simpa [hr] using hn

def childGrantWithin (parent child : Grant) (agent : Ref .actor) : Bool :=
  child.actor == agent && child.scope == parent.scope &&
  child.rule == parent.rule && child.version == parent.version &&
  child.act == parent.act &&
  decide (parent.start ≤ child.start ∧ child.stop ≤ parent.stop)

def delegateLocal (s : Situation) (obj : Ref .object)
    (request : Request) (child : Grant) : Reply Agency :=
  match s.agencies obj with
  | none => quiet s (.unknown .inputUnchecked)
  | some a =>
    if request.actor != a.principal || request.scope != a.scope then
      quiet s (.rejected .unauthorized)
    else
      match s.core.state.N.grants.find? (fun parent =>
          grantMatches parent request && childGrantWithin parent child a.agent) with
      | none => quiet s (.rejected .unauthorized)
      | some _ =>
        let next := delegate a child
        let st := {s.core.state with
          N := {s.core.state.N with grants := child :: s.core.state.N.grants}}
        ⟨{s with
          agencies := assign s.agencies obj (some next)
          core := {s.core with state := st}}, .success next⟩

def delegateCall (s : Situation) (c : Call) (grounds : Formula)
    (obj : Ref .object) (child : Grant) : Reply Agency :=
  atomic s (continueWith (gate s c grounds) (fun z => delegateLocal z obj c.request child))

/- Norm text/version are unchanged; the derived authority registry changes.
   Delegation never removes the principal's capacity. -/
theorem delegation_norms_unchanged (s : Situation) (obj : Ref .object)
    (r : Request) (g : Grant) :
    (delegateLocal s obj r g).after.core.state.N.rules = s.core.state.N.rules ∧
    (delegateLocal s obj r g).after.core.state.N.version = s.core.state.N.version := by
  unfold delegateLocal
  split
  · exact ⟨rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl⟩
    · split <;> exact ⟨rfl, rfl⟩

theorem delegation_actual_capacity (s : Situation) (obj : Ref .object)
    (r : Request) (child : Grant) (a result : Agency)
    (ha : s.agencies obj = some a)
    (hs : (delegateLocal s obj r child).answer = .success result) :
    (delegateLocal s obj r child).after.agencies obj = some result ∧
      result.principalCapacity = a.principalCapacity := by
  unfold delegateLocal at hs ⊢
  rw [ha] at hs ⊢
  dsimp only at hs ⊢
  split at hs
  · cases hs
  · rename_i guard
    split at hs
    · cases hs
    · rename_i parent found
      dsimp only at hs
      cases hs
      simp [guard, found, assign, delegate]

def attributeRelation (agent principal : Ref .actor) (scope : Scope)
    (r : LegalRelation) : LegalRelation :=
  if r.scope == scope then
    {r with
      holder := (if r.holder == agent then principal else r.holder)
      counterparty := (if r.counterparty == agent then principal else r.counterparty)}
  else r

def apparentLocal (s : Situation) (scope : Scope) (agent principal : Ref .actor)
    (g : ApparentGuard) : Reply Judgment :=
  match apparentAttribution g with
  | .undetermined => quiet s (.unknown .inputUnchecked)
  | .notEstablished => quiet s (.rejected .prerequisites)
  | .established =>
    let st := {s.core.state with L := s.core.state.L.map (attributeRelation agent principal scope)}
    ⟨{s with core := {s.core with state := st}}, .success .established⟩

def apparentCall (s : Situation) (c : Call) (grounds : Formula)
    (agent principal : Ref .actor) (g : ApparentGuard) : Reply Judgment :=
  atomic s (continueWith (gate s c grounds)
    (fun z => apparentLocal z c.request.scope agent principal g))

theorem apparent_preserves_F (s : Situation) (scope : Scope)
    (agent principal : Ref .actor) (g : ApparentGuard) :
    (apparentLocal s scope agent principal g).after.core.state.F = s.core.state.F := by
  unfold apparentLocal
  split <;> rfl

theorem attribution_other_scope (r : LegalRelation) (a p : Ref .actor)
    (scope : Scope) (h : r.scope ≠ scope) :
    attributeRelation a p scope r = r := by simp [attributeRelation, h]

def jurisdictionQuery (s : Situation) (known : Bool) (j : JurisdictionInput) :
    Reply (Option JurisdictionBranch) :=
  match jurisdictionCheck known j with
  | .known branch => quiet s (.success branch)
  | .unknown k => quiet s (.unknown k)

def burdenQuery (s : Situation) (p : ProofPolicy) (ids : List (Ref .material))
    (a : Atom) : Reply Judgment :=
  quiet s (.success (p.evaluate (admittedView s.core.state.E ids) a))

def acquisitionQuery (s : Situation) (route : AcqRoute)
    (goodFaith price publicity : Judgment) : Reply Judgment :=
  match acqJudge route goodFaith price publicity with
  | .undetermined => quiet s (.unknown .inputUnchecked)
  | .notEstablished => quiet s (.rejected .prerequisites)
  | .established => quiet s (.success .established)

/- Common-crime scope and the charge/elements query are separate. Each
   participant's charge is retained; shared event identity cannot overwrite it. -/
def offenseQuery (s : Situation) (ps : List Participation) (known : Bool)
    (ability elements : Judgment) (person : Ref .actor) (event : Ref .event)
    (commonScope charge : Ref .query) : Reply (Ref .query) :=
  if !known then quiet s (.unknown .inputUnchecked)
  else match andJ (liableFor ps ability person event commonScope) elements with
    | .undetermined => quiet s (.unknown .inputUnchecked)
    | .notEstablished => quiet s (.rejected .prerequisites)
    | .established => quiet s (.success charge)

theorem same_event_different_charges (s : Situation) :
    (offenseQuery s jiaParts true .established .established aJia ev1 q1 ⟨100⟩).answer =
      .success ⟨100⟩ ∧
    (offenseQuery s yiParts true .established .established aYi ev1 q1 ⟨101⟩).answer =
      .success ⟨101⟩ := by constructor <;> rfl

theorem excess_not_copied (s : Situation) (charge : Ref .query) :
    (offenseQuery s yiParts true .established .established aYi ev2 q1 charge).answer =
      .rejected .prerequisites := rfl

def acceptBankruptcyLocal (s : Situation) (d : CaseDates) (debtor : Ref .actor) :
    Reply (List (Ref .event)) :=
  match stayNeedsAcceptance d with
  | .unknown k => quiet s (.unknown k)
  | .known false => quiet s (.rejected .prerequisites)
  | .known true =>
    let ids := (staySelected debtor s.executions).map (fun e => e.id)
    ⟨{s with stayed := ids ++ s.stayed}, .success ids⟩

def acceptBankruptcy (s : Situation) (c : Call) (grounds : Formula)
    (d : CaseDates) (debtor : Ref .actor) : Reply (List (Ref .event)) :=
  atomic s (continueWith (gate s c grounds) (fun z => acceptBankruptcyLocal z d debtor))

def interestLocal (s : Situation) (accepted : Check Bool) (atTime : Nat)
    (claim : InterestClaim) (t : Nat) : Reply Nat :=
  match cutDay accepted atTime claim t with
  | .unknown k => quiet s (.unknown k)
  | .known cutoff =>
    let old := s.interest claim.id
    let next := old.map (fun x => onAcceptance x.preAccrued)
    ⟨{s with
      cutoffs := (fun id => if id = claim.id then some cutoff else s.cutoffs id)
      interest := (fun id => if id = claim.id then next else s.interest id)}, .success cutoff⟩

/- Equality at acceptance was the failed old proof step. min-cut is proved on
   both branches, and unrelated debtors are not inserted into the stay list. -/
theorem cut_at_acceptance (atTime : Nat) (claim : InterestClaim) (h : claim.in46 = true) :
    cutDay (.known true) atTime claim atTime = .known atTime := by simp [cutDay, h]

theorem cut_after_acceptance (atTime t : Nat) (claim : InterestClaim)
    (hc : claim.in46 = true) (ht : atTime ≤ t) :
    cutDay (.known true) atTime claim t = .known atTime := by
  by_cases h : t ≤ atTime
  · have he : t = atTime := Nat.le_antisymm h ht
    subst t
    simp [cutDay, hc]
  · simp [cutDay, hc, h]

theorem filing_no_stay (s : Situation) (day : Nat) (debtor : Ref .actor) :
    (acceptBankruptcyLocal s ⟨day, none⟩ debtor).after.stayed = s.stayed := rfl

theorem other_interest_unchanged (s : Situation) (a : Check Bool) (day t : Nat)
    (claim : InterestClaim) (other : Ref .relation) (h : other ≠ claim.id) :
    (interestLocal s a day claim t).after.interest other = s.interest other := by
  unfold interestLocal
  split
  · rfl
  · simp [h]

def stateCompensationLocal (s : Situation) (kind : CompensationKind)
    (relation : Ref .relation) (custody : Bool) (ground1719 : Judgment) : Reply Judgment :=
  match compFromCustody custody false ground1719 with
  | .undetermined => quiet s (.unknown .inputUnchecked)
  | .notEstablished => quiet s (.rejected .prerequisites)
  | .established =>
    ⟨{s with tracks := {s.tracks with
      stateCompensation := (kind, relation) :: s.tracks.stateCompensation}}, .success .established⟩

theorem compensation_other_tracks (s : Situation) (kind : CompensationKind)
    (relation : Ref .relation) (custody : Bool) (g : Judgment) :
    (stateCompensationLocal s kind relation custody g).after.tracks.civil = s.tracks.civil ∧
    (stateCompensationLocal s kind relation custody g).after.tracks.criminal = s.tracks.criminal ∧
    (stateCompensationLocal s kind relation custody g).after.tracks.administrative =
      s.tracks.administrative := by
  unfold stateCompensationLocal
  split <;> exact ⟨rfl, rfl, rfl⟩

inductive NormLevel
  | constitution | law | administrative | local | rule
  deriving DecidableEq, Repr

def normRank : NormLevel → Nat
  | .constitution => 4 | .law => 3 | .administrative => 2 | .local => 1 | .rule => 0

theorem constitution_top (n : NormLevel) : normRank n ≤ normRank .constitution := by
  cases n <;> decide

def rightsConflict (s : Situation) : Reply Unit :=
  quiet s (.conflict (reviewRoute .constitutionalReview))

theorem rights_conflict_preserves_L (s : Situation) :
    (rightsConflict s).after.core.state.L = s.core.state.L := rfl

def interpretLocal (s : Situation) (obj : Ref .object) (f : Formula) : Reply Formula :=
  let st := {s.core.state with interpretations :=
    (obj, f) :: s.core.state.interpretations.filter (fun e => e.1 != obj)}
  ⟨{s with
    core := {s.core with state := st}
    meanings := assign s.meanings obj (some f)}, .success f⟩

def interpret (s : Situation) (c : Call) (grounds : Formula)
    (obj : Ref .object) (f : Check Formula) : Reply Formula :=
  atomic s (match f with
  | .unknown k => quiet s (.unknown k)
  | .known meaning =>
    if c.request.scope.object == obj then
      continueWith (gate s c grounds) (fun z => interpretLocal z obj meaning)
    else quiet s (.rejected .unauthorized))

theorem interpretation_other_contract (s : Situation) (a b : Ref .object) (f : Formula)
    (h : b ≠ a) : (interpretLocal s a f).after.meanings b = s.meanings b := by
  simp [interpretLocal, assign, h]

theorem interpretation_preserves_N (s : Situation) (a : Ref .object) (f : Formula) :
    (interpretLocal s a f).after.core.state.N = s.core.state.N := rfl

def resJudicataQuery (s : Situation) (idx : Option BindingIndex)
    (person : Ref .actor) (scope : Scope) (time : Nat) : Reply Bool :=
  match resJudicataGate idx person scope time with
  | .known value => quiet s (.success value)
  | .unknown k => quiet s (.unknown k)

def proposeEngine (s : Situation) (out : EngineOutput) : Reply Candidate :=
  let candidate := candidateFromEngine s.core.state.A.model out
  let st := propose s.core.state candidate
  ⟨{s with core := {s.core with state := st}}, .success candidate⟩

theorem engine_proposal_only (s : Situation) (out : EngineOutput) :
    (proposeEngine s out).after.core.state.L = s.core.state.L ∧
    (proposeEngine s out).after.core.state.N = s.core.state.N ∧
    (proposeEngine s out).after.core.state.bindings = s.core.state.bindings := by
  exact ⟨rfl, rfl, rfl⟩

#print axioms unknown_propagates
#print axioms atomic_failure_preserves
#print axioms conflict_propagates
#print axioms revoke_effective_and_power
#print axioms revoke_other_object
#print axioms revoke_natural_facts
#print axioms revocation_removes_tracked_relations
#print axioms delegation_norms_unchanged
#print axioms delegation_actual_capacity
#print axioms apparent_preserves_F
#print axioms attribution_other_scope
#print axioms same_event_different_charges
#print axioms excess_not_copied
#print axioms cut_at_acceptance
#print axioms cut_after_acceptance
#print axioms filing_no_stay
#print axioms other_interest_unchanged
#print axioms compensation_other_tracks
#print axioms constitution_top
#print axioms rights_conflict_preserves_L
#print axioms interpretation_other_contract
#print axioms interpretation_preserves_N
#print axioms engine_proposal_only

end Law
end JurisLean.CN.Completion20261105

