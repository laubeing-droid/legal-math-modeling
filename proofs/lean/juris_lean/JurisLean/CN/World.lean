import JurisLean.CN.Walls
import JurisLean.KernelV3
import JurisLean.Hohfeld

namespace JurisLean.CN.World

open JurisLean.CN.Walls
open JurisLean.KernelV3
open JurisLean.Hohfeld

/-!
中文说明：修正版点。无 sorry。除关债外。
-/

structure Sit where
  fF : Bool
  eRaw : Nat
  eAdm : Nat
  eExcl : Nat
  nVer : Nat
  lCreated : Bool
  lConfirmed : Bool
  clk : Nat
  procOn : Bool
  aiVer : Nat
  pLedger : Nat
  deriving DecidableEq, Repr

def initSit : Sit :=
  { fF := (true : Bool), eRaw := (1 : Nat), eAdm := (0 : Nat), eExcl := (0 : Nat),
    nVer := (1 : Nat), lCreated := (true : Bool), lConfirmed := (false : Bool),
    clk := (1 : Nat), procOn := (true : Bool), aiVer := (0 : Nat), pLedger := (1 : Nat) }

/-- 无裁判正常对象。 -/
theorem no_trial_normal :
    ∃ s : Sit,
      s.procOn = true ∧ s.lCreated = true ∧ s.aiVer = 0 ∧ s.fF = true := by
  have s : Sit :=
    { fF := (true : Bool), eRaw := (1 : Nat), eAdm := (1 : Nat), eExcl := (0 : Nat),
      nVer := (1 : Nat), lCreated := (true : Bool), lConfirmed := (false : Bool),
      clk := (1 : Nat), procOn := (true : Bool), aiVer := (0 : Nat), pLedger := (1 : Nat) }
  exact ⟨s, rfl, rfl, rfl, rfl⟩

/-- 提议：aiVer+1，L/N/F 不变。 -/
def propose (s : Sit) : Sit := { s with aiVer := s.aiVer + 1 }

theorem propose_frame_L (s : Sit) : (propose s).lCreated = s.lCreated := by
  cases s; rfl

theorem propose_frame_F (s : Sit) : (propose s).fF = s.fF := by
  cases s; rfl

theorem propose_frame_N (s : Sit) : (propose s).nVer = s.nVer := by
  cases s; rfl

/-- 学习：aiVer+1 且 eRaw+1。不改 N/F/L。 -/
def learn (s : Sit) : Sit := { s with aiVer := s.aiVer + 1, eRaw := s.eRaw + 1 }

theorem learn_frame_N (s : Sit) : (learn s).nVer = s.nVer := by cases s; rfl
theorem learn_frame_F (s : Sit) : (learn s).fF = s.fF := by cases s; rfl
theorem learn_frame_L (s : Sit) : (learn s).lCreated = s.lCreated := by cases s; rfl

/-- Record：eRaw+1，F 不变。 -/
def record (s : Sit) : Sit := { s with eRaw := s.eRaw + 1 }

theorem record_frame_F (s : Sit) : (record s).fF = s.fF := by cases s; rfl

/-- 准入。 -/
def admit (s : Sit) : Sit := { s with eAdm := s.eAdm + 1 }

/-- 排除。 -/
def exclude (s : Sit) : Sit := { s with eExcl := s.eExcl + 1 }

/-- 合法形成步。 -/
inductive Eff
  | confirmatory
  | constitutive
  | performance
  | proceduralBinding
  deriving DecidableEq, Repr

def legalStep (s : Sit) (hasDoc : Bool) (e : Eff) : Sit :=
  match hasDoc, e with
  | true, Eff.constitutive => { s with lCreated := true, procOn := true }
  | true, Eff.confirmatory => { s with lConfirmed := true, procOn := true }
  | true, Eff.performance => { s with procOn := true, pLedger := s.pLedger + 1 }
  | true, Eff.proceduralBinding => { s with procOn := true }
  | false, _ => s

theorem confirm_no_create (s : Sit) :
    (legalStep s true Eff.confirmatory).lCreated = s.lCreated := by
  cases s; rfl

theorem nodoc_no_create (s : Sit) :
    (legalStep s false Eff.constitutive).lCreated = s.lCreated := by
  cases s; rfl

theorem legalStep_frame_F (s : Sit) (hasDoc : Bool) (e : Eff) :
    (legalStep s hasDoc e).fF = s.fF := by
  cases s
  cases hasDoc <;> cases e <;> rfl

/-- AI 分数不是 established。 -/
inductive CnOut
  | est
  | notEst
  | undet
  | score (n : Nat)
  deriving DecidableEq, Repr

theorem score_ne_est (n : Nat) :
    CnOut.score n ≠ CnOut.est := by
  intro h
  cases h

/-- 法无明文。 -/
def evalNoNorm : CnOut := CnOut.undet

theorem noNorm_undetermined : evalNoNorm = CnOut.undet := rfl
theorem noNorm_not_established : evalNoNorm ≠ CnOut.est := by
  intro h
  cases h

/-- 生命周期：可撤销仍有效。 -/
structure ContractLife where
  established : Bool
  effective : Bool
  invalid : Bool
  voidablePower : Bool
  deriving DecidableEq, Repr

theorem voidable_still_effective :
    ∃ c : ContractLife,
      c.effective = true ∧ c.voidablePower = true ∧ c.invalid = false := by
  have c : ContractLife :=
    { established := (true : Bool), effective := (true : Bool),
      invalid := (false : Bool), voidablePower := (true : Bool) }
  exact ⟨c, rfl, rfl, rfl⟩

/-- 公定力不是事实真。 -/
theorem gongding_still :
    ∃ a : AdminAct,
      a.publicValidity = true ∧ a.factTrue = false ∧ a.substantiallyLegal = false := by
  have a : AdminAct :=
    { publicValidity := (true : Bool), substantiallyLegal := (false : Bool),
      factTrue := (false : Bool) }
  exact ⟨a, rfl, rfl, rfl⟩

/-- 刑事无罪民事可赔。 -/
structure SameFact where
  criminalGuilty : Bool
  civilLiable : Bool

theorem criminal_not_cover_civil :
    ∃ s : SameFact, s.criminalGuilty = false ∧ s.civilLiable = true := by
  have s : SameFact :=
    { criminalGuilty := (false : Bool), civilLiable := (true : Bool) }
  exact ⟨s, rfl, rfl⟩

end JurisLean.CN.World
