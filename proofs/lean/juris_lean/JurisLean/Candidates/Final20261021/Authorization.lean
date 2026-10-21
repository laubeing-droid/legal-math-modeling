import JurisLean.Candidates.Final20261021.EvidenceProcedure

namespace JurisLean.Candidates.Final20261021.Authorization

structure Grant where
  evidence : SourceRef
  subject : PartyId
  caseId : CaseId
  action : Nat
  contentVersion : Nat
  authorityRuleVersion : Nat
  fromDate : LawDate
  untilDate : LawDate
  deriving DecidableEq, Repr

def checkGrant (g : Gamma) (subject : PartyId) (action version : Nat) (a : Grant) : Bool :=
  decide (a.subject = subject ∧ a.caseId = g.caseId ∧ a.action = action ∧
    a.contentVersion = version ∧ a.authorityRuleVersion = g.normVersion ∧
    a.fromDate.ordinal ≤ g.lawDate.ordinal ∧ g.lawDate.ordinal < a.untilDate.ordinal)

def authorized (catalog : List Grant) (g : Gamma) (subject : PartyId) (action version : Nat) : Bool :=
  catalog.any (checkGrant g subject action version)

structure Configured (B : Type) where
  gamma : Gamma
  history : List Temporal.VersionRecord
  env : Result Nat
  business : B
  deriving DecidableEq, Repr

def fresh {B : Type} (s : Configured B) : Prop :=
  s.env = Temporal.proposed_applicability s.gamma s.history

-- Pure preparation; the returned value is jointly published by an atomic
-- transaction. There is no observable H-new/env-old intermediate state.
def append_and_refresh {B : Type} (s : Configured B) (g : Gamma)
    (event : Temporal.VersionRecord) : Configured B :=
  let h := s.history ++ [event]
  ⟨g, h, Temporal.proposed_applicability g h, s.business⟩

def next_eval {B : Type} (s : Configured B) : Result Nat := s.env

theorem u10_1_enable_append_select_refresh_consume {B : Type}
    (s : Configured B) (g : Gamma) (event : Temporal.VersionRecord) :
    fresh (append_and_refresh s g event) ∧
    next_eval (append_and_refresh s g event) =
      Temporal.proposed_applicability g (s.history ++ [event]) ∧
    (append_and_refresh s g event).business = s.business := ⟨rfl, rfl, rfl⟩

-- Rooted delegation uses the same positive Horn semantics; an unsupported
-- cycle is not an external root, nor is every cycle prohibited.
def rootedPermissions (roots : List Nat) (delegations : List (Compiler.Rule Nat)) (fuel : Nat) :=
  Compiler.proposed_rule_input delegations fuel roots

end JurisLean.Candidates.Final20261021.Authorization
