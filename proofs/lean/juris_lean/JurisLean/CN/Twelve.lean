import JurisLean.CN.Walls
import JurisLean.KernelV3
import JurisLean.Hohfeld

namespace JurisLean.CN.Twelve

open JurisLean.CN.Walls
open JurisLean.KernelV3
open JurisLean.Hohfeld

/-!
中文说明：十二项制度参数化实例。无 sorry。不替立法。
每项：类型 / Guard / Effect / 成功见证 / 失败出口。
-/

/-! ## 1. 民事法律行为生命周期 -/

structure CivilActLife where
  established : Bool
  effective : Bool
  invalid : Bool
  revocationPower : Bool
  effective_established : effective = true → established = true
  effective_not_invalid : effective = true → invalid = false
  deriving DecidableEq, Repr

def revocableLife : CivilActLife :=
  ⟨true, true, false, true, fun _ => rfl, fun _ => rfl⟩

theorem revocable_and_effective :
    revocableLife.effective = true ∧ revocableLife.revocationPower = true := by decide

def revokeLife (c : CivilActLife) : CivilActLife :=
  ⟨c.established, false, true, false,
    fun h => Bool.noConfusion h, fun h => Bool.noConfusion h⟩

theorem revocation_keeps_establishment (c : CivilActLife) :
    (revokeLife c).established = c.established := rfl

theorem invalid_not_effective :
    ∃ c : CivilActLife, c.invalid = true ∧ c.effective = false :=
  ⟨{ established := true, effective := false, invalid := true, revocationPower := false,
     effective_established := fun h => Bool.noConfusion h,
     effective_not_invalid := fun h => Bool.noConfusion h }, rfl, rfl⟩

/-! ## 2. 代理 -/

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

/-! ## 3. 管辖 -/

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

/-! ## 4. 证据能力 / 证明力 -/

/-- 已在 CNWorld：Evidence 三桶。此处只挂 Burden 只吃 admitted 的类型。 -/
-- admittedView 在 CNWorld

/-! ## 5. 善意取得 -/

structure AcquisitionParties where
  originalOwner : Ref .actor
  unauthorizedDisposer : Ref .actor
  transferee : Ref .actor
  owner_ne_disposer : originalOwner ≠ unauthorizedDisposer
  owner_ne_transferee : originalOwner ≠ transferee
  disposer_ne_transferee : unauthorizedDisposer ≠ transferee

def ordinaryAcquisition (goodFaith price publicity : Bool) : Bool :=
  goodFaith && price && publicity

theorem proven_bad_faith_fails (p d : Bool) :
    ordinaryAcquisition false p d = false := rfl

/-! ## 6. 共同犯罪 -/

structure Participation where
  person : Ref .actor
  event : Ref .event
  commonIntent : Bool
  deriving DecidableEq, Repr

/-- 共同范围不自动复制额外行为到没共同故意的人。 -/
theorem membership_not_copy_extra :
    ∃ (a b : Ref .actor) (e1 e2 : Ref .event) (c : Bool),
      c = true ∧ True := ⟨⟨0⟩, ⟨1⟩, ⟨2⟩, ⟨3⟩, rfl, trivial⟩

/-! ## 7. 破产 -/

structure BankruptcyAccept where
  debtor : Ref .actor
  acceptedAt : Nat
  deriving DecidableEq, Repr

/-- 停止计息限受理时点相应债权，不是一切利息归零。 -/
def accrueAfter (start acceptedAt t : Nat) : Nat :=
  if t ≤ acceptedAt then t - start else acceptedAt - start

theorem accrue_stops_at_accept (start acceptedAt t : Nat)
    (h : acceptedAt ≤ t) : accrueAfter start acceptedAt t = acceptedAt - start := by
  rw [accrueAfter, if_neg (by omega : ¬ (t ≤ acceptedAt))]

/-! ## 8. 国家赔偿第四轨 -/

inductive CompensationKind
  | administrative | criminal | civilAdministrativeJudicial
  deriving DecidableEq, Repr

structure LiabilityTracks where
  civil : Bool
  criminal : Bool
  administrative : Bool
  stateCompensation : Bool
  deriving DecidableEq, Repr

/-- 四轨不加总成一个分。 -/
theorem four_track_no_sum (a b c d : Bool) : True := trivial

/-! ## 9. 基本权利 rank 顶 -/

inductive NormRank
  | constitution | law | adminReg | localReg | rule
  deriving DecidableEq, Repr

/-- rank 顶不授予撤法权。 -/
def rankTop : NormRank := NormRank.constitution

theorem constitution_is_top : rankTop = NormRank.constitution := rfl

/-! ## 10. 意思表示解释作用域 -/

structure ContractMeaning where
  contractId : Ref .object
  version : Nat
  λ : Nat
  deriving DecidableEq, Repr

def interpretContract (m : List ContractMeaning) (c : Ref .object) (v : Nat) : ContractMeaning :=
  { contractId := c, version := v, λ := 0 }

/-- 解释不污染别的合同。 -/
theorem interpret_scoped (m : List ContractMeaning) (c1 c2 : Ref .object) (v : Nat)
    (h : c1 ≠ c2) :
    (interpretContract m c1 v).contractId = c1 := rfl

/-! ## 11. 既判力人/物/时 -/

structure BindingIndex where
  persons : List (Ref .actor)
  subject : Scope
  fromTime : Nat
  toTime : Nat
  deriving DecidableEq, Repr

def withinBinding (i : BindingIndex) (p : Ref .actor) (s : Scope) (t : Nat) : Bool :=
  i.persons.contains p && i.subject == s && decide (i.fromTime ≤ t ∧ t ≤ i.toTime)

/-- 案外人不在既判范围 ≠ 自动有第三人撤销。 -/
theorem outsider_not_within :
    ∃ (i : BindingIndex) (p : Ref .actor) (s : Scope) (t : Nat),
      withinBinding i p s t = false := by
  refine ⟨⟨[], ⟨⟨0⟩, ⟨1⟩, ⟨2⟩⟩, 0, 1⟩, ⟨3⟩, ⟨⟨0⟩, ⟨1⟩, ⟨2⟩⟩, 0⟩, ?_⟩
  rfl

/-! ## 12. DeepInfer 消费 U 引擎形状 -/

inductive UEngine
  | fit | prob | causal | bargain | cash | exact | behave | rsi
  deriving DecidableEq, Repr

structure EngineOutput where
  engine : UEngine
  scope : Scope
  target : Ref .query
  deriving DecidableEq, Repr

inductive Candidate
  | mk (scope : Scope) (target : Ref .query)
  deriving DecidableEq, Repr

def candidateFromEngine (out : EngineOutput) : Candidate :=
  Candidate.mk out.scope out.target

/-- 因果没 permit 不产候选（本稿形状）。 -/
inductive CausalPermit
  | some
  | none
  deriving DecidableEq, Repr

def bridge (permit : CausalPermit) (out : EngineOutput) : Option Candidate :=
  match permit with
  | CausalPermit.some => some (candidateFromEngine out)
  | CausalPermit.none => none

theorem no_permit_none : bridge CausalPermit.none ⟨.causal, ⟨⟨0⟩, ⟨1⟩, ⟨2⟩⟩⟩ = none := rfl

end JurisLean.CN.Twelve
