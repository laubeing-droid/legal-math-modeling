import JurisLean.CN.Revision20261101.Ops

namespace JurisLean.CN.Revision20261101

open JurisLean.KernelV3 JurisLean.Hohfeld

structure HohfeldPosition where
  holder : Ref .actor
  counterparty : Ref .actor
  scope : Scope
  concept : Concept
  deriving DecidableEq, Repr

/- Typical bundles, not an exhaustive classification of every defense. The
   privilege concerns refusal; power concerns the procedural act of raising it. -/
def rightConcepts : JurisLean.CN.Walls.RightKind → List Concept
  | .domin => [.claimRight, .privilege]
  | .req => [.claimRight]
  | .form => [.power]
  | .defend => [.privilege, .power]

def hohfeld (r : LegalRelation) : List HohfeldPosition :=
  (rightConcepts r.right).map fun c => ⟨r.holder, r.counterparty, r.scope, c⟩

def counterpart (p : HohfeldPosition) : HohfeldPosition :=
  ⟨p.counterparty, p.holder, p.scope, correlative p.concept⟩

theorem request_maps_to_claim : rightConcepts .req = [.claimRight] := rfl
theorem formation_maps_to_power : rightConcepts .form = [.power] := rfl
theorem defense_not_noRight : rightConcepts .defend ≠ [.noRight] := by decide
theorem domination_contains_privilege : Concept.privilege ∈ rightConcepts .domin := by decide
theorem counterpart_preserves_scope (p : HohfeldPosition) :
    (counterpart p).scope = p.scope := rfl

theorem counterpart_twice (p : HohfeldPosition) : counterpart (counterpart p) = p := by
  cases p with
  | mk h c s k => cases k <;> rfl

/- Establishment, effectiveness, and an unexercised revocation power are not
   mutually exclusive stages. Invalidity and effectiveness cannot coexist here. -/
structure CivilActLife where
  established : Bool
  effective : Bool
  invalid : Bool
  revocationPower : Bool
  effective_established : effective = true → established = true
  effective_not_invalid : effective = true → invalid = false

def revocableLife : CivilActLife := ⟨true, true, false, true, fun _ => rfl, fun _ => rfl⟩

theorem revocable_and_effective :
    revocableLife.effective = true ∧ revocableLife.revocationPower = true := by decide

def revokeLife (c : CivilActLife) : CivilActLife :=
  ⟨c.established, false, true, false, by decide, by decide⟩

theorem revocation_keeps_establishment (c : CivilActLife) :
    (revokeLife c).established = c.established := rfl

structure Agency where
  principal : Ref .actor
  agent : Ref .actor
  counterparty : Ref .actor
  scope : Scope
  principalCapacity : Bool
  derivedGrants : List Grant

def delegate (a : Agency) (g : Grant) : Agency :=
  { a with derivedGrants := g :: a.derivedGrants }

theorem delegation_keeps_principal_capacity (a : Agency) (g : Grant) :
    (delegate a g).principalCapacity = a.principalCapacity := rfl

structure AcquisitionParties where
  originalOwner : Ref .actor
  unauthorizedDisposer : Ref .actor
  transferee : Ref .actor
  owner_ne_disposer : originalOwner ≠ unauthorizedDisposer
  owner_ne_transferee : originalOwner ≠ transferee
  disposer_ne_transferee : unauthorizedDisposer ≠ transferee

/- Special-property rules are selected before this ordinary acquisition guard. -/
def ordinaryAcquisition (goodFaith price publicity : Judgment) : Judgment :=
  andJ goodFaith (andJ price publicity)

theorem proven_bad_faith_fails (p d : Judgment) :
    ordinaryAcquisition .notEstablished p d = .notEstablished := rfl

theorem unchecked_good_faith_stays_unknown :
    ordinaryAcquisition .undetermined .established .established = .undetermined := rfl

inductive JurisdictionBranch
  | ordinary | agreement | exclusive | appearance | arbitration
  deriving DecidableEq, Repr

structure JurisdictionInput where
  levelOK : Bool
  exclusiveApplies : Bool
  exclusiveOK : Bool
  arbitrationBlocksMerits : Bool
  agreementApplies : Bool
  agreementOK : Bool
  appearanceApplies : Bool
  ordinaryOK : Bool
  deriving DecidableEq, Repr

def jurisdiction (j : JurisdictionInput) : Option JurisdictionBranch :=
  if !j.levelOK then none
  else if j.exclusiveApplies then
    if j.exclusiveOK then some .exclusive else none
  else if j.arbitrationBlocksMerits then some .arbitration
  else if j.agreementApplies then
    if j.agreementOK then some .agreement else none
  else if j.appearanceApplies then some .appearance
  else if j.ordinaryOK then some .ordinary else none

theorem ordinary_needs_no_agreement :
    jurisdiction ⟨true, false, false, false, false, false, false, true⟩ =
      some .ordinary := by decide

theorem appearance_cannot_override_exclusive :
    jurisdiction ⟨true, true, false, false, false, false, true, true⟩ = none := by decide

inductive CompensationKind
  | administrative | criminal | civilAdministrativeJudicial
  deriving DecidableEq, Repr

structure LiabilityTracks where
  civil : List (Ref .relation)
  criminal : List (Ref .relation)
  administrative : List (Ref .relation)
  stateCompensation : List (CompensationKind × Ref .relation)

structure BindingIndex where
  persons : List (Ref .actor)
  subject : Scope
  fromTime : Nat
  toTime : Nat
  deriving DecidableEq, Repr

def withinBinding (i : BindingIndex) (p : Ref .actor) (s : Scope) (t : Nat) : Bool :=
  i.persons.contains p && i.subject == s && decide (i.fromTime ≤ t ∧ t ≤ i.toTime)

/- Expiry creates availability, never a fictional exercise or extinction. -/
structure LimitationState where
  claim : LegalRelation
  defenseAvailable : Bool
  defenseRaised : Bool

def limitationExpires (s : LimitationState) : LimitationState :=
  { s with defenseAvailable := true }

theorem limitation_preserves_claim (s : LimitationState) :
    (limitationExpires s).claim = s.claim := rfl

theorem limitation_does_not_raise (s : LimitationState) :
    (limitationExpires s).defenseRaised = s.defenseRaised := rfl

end JurisLean.CN.Revision20261101
