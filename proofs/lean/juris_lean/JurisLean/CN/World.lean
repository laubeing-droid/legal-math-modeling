import JurisLean.CN.Walls
import JurisLean.KernelV3
import JurisLean.Hohfeld

namespace JurisLean.CN.World

open JurisLean.CN.Walls
open JurisLean.KernelV3
open JurisLean.Hohfeld

/-!
中文说明：修正版点。审计 F01–F14 接了。
无 sorry。除关债外。用 decide 不用 rfl 证否定。
四墙定理在 Walls 里，不重证。
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
  { fF := true, eRaw := 0, eAdm := 0, eExcl := 0,
    nVer := 0, lCreated := false, lConfirmed := false,
    clk := 0, procOn := false, aiVer := 0, pLedger := 0 }

/-- 无裁判正常对象：程序开、关系形成、AI 关、事实在。 -/
theorem no_trial_normal :
    ∃ s : Sit,
      s.procOn = true ∧ s.lCreated = true ∧ s.aiVer = 0 ∧ s.fF = true := by
  refine ⟨{ fF := true, eRaw := 1, eAdm := 1, eExcl := 0,
     nVer := 1, lCreated := true, lConfirmed := false,
     clk := 1, procOn := true, aiVer := 0, pLedger := 1 }, rfl, rfl, rfl, rfl⟩

/-- 提议：aiVer+1，L/N/F 不变。 -/
def propose (s : Sit) : Sit := { s with aiVer := s.aiVer + 1 }

theorem propose_frame_L (s : Sit) : (propose s).lCreated = s.lCreated := by
  cases s; rfl

theorem propose_frame_F (s : Sit) : (propose s).fF = s.fF := by
  cases s; rfl

theorem propose_frame_N (s : Sit) : (propose s).nVer = s.nVer := by
  cases s; rfl

/-- 学习：aiVer+1 且 eRaw+1。与 propose 不同。不改 N/F/L。 -/
def learn (s : Sit) : Sit := { s with aiVer := s.aiVer + 1, eRaw := s.eRaw + 1 }

theorem learn_frame_N (s : Sit) : (learn s).nVer = s.nVer := by cases s; rfl
theorem learn_frame_F (s : Sit) : (learn s).fF = s.fF := by cases s; rfl
theorem learn_frame_L (s : Sit) : (learn s).lCreated = s.lCreated := by cases s; rfl

/-- Record：eRaw+1，F 不变。 -/
def record (s : Sit) : Sit := { s with eRaw := s.eRaw + 1 }

theorem record_frame_F (s : Sit) : (record s).fF = s.fF := by cases s; rfl

/-- 准入：eAdm+1。无回执不调。 -/
def admit (s : Sit) : Sit := { s with eAdm := s.eAdm + 1 }

/-- 排除：eExcl+1，不进 eAdm。 -/
def exclude (s : Sit) : Sit := { s with eExcl := s.eExcl + 1 }

/-- 合法形成步：hasDoc + EffectType。确认不创关系。无权不创。 -/
def legalStep (s : Sit) (hasDoc : Bool) (e : EffectType) : Sit :=
  match hasDoc, e with
  | true, EffectType.constitutive => { s with lCreated := true, procOn := true }
  | true, EffectType.confirmatory => { s with lConfirmed := true, procOn := true }
  | true, EffectType.performance => { s with procOn := true, pLedger := s.pLedger + 1 }
  | true, EffectType.proceduralBinding => { s with procOn := true }
  | false, _ => s

theorem confirm_no_create (s : Sit) :
    (legalStep s true EffectType.confirmatory).lCreated = s.lCreated := by
  cases s; rfl

theorem nodoc_no_create (s : Sit) :
    (legalStep s false EffectType.constitutive).lCreated = s.lCreated := by
  cases s; rfl

theorem legalStep_frame_F (s : Sit) (hasDoc : Bool) (e : EffectType) :
    (legalStep s hasDoc e).fF = s.fF := by
  cases s
  cases hasDoc <;> cases e <;> rfl

/-- AI 分数不是 established。 -/
inductive CnOut
  | established
  | notEstablished
  | undetermined
  | aiScore (n : Nat)
  deriving DecidableEq, Repr

theorem ai_ne_established (n : Nat) :
    CnOut.ai n ≠ CnOut.established := by
  intro h
  cases h

/-- 法无明文 → undetermined，不是 established，也不是程序驳回。 -/
def evalNoNorm : CnOut := CnOut.undetermined

theorem noNorm_undetermined : evalNoNorm = CnOut.undetermined := rfl
theorem noNorm_not_established : evalNoNorm ≠ CnOut.established := by
  intro h
  cases h

/-- 生命周期：可撤销仍有效，不是互斥枚举。 -/
structure ContractLife where
  established : Bool
  effective : Bool
  invalid : Bool
  voidablePower : Bool
  deriving DecidableEq, Repr

theorem voidable_still_effective :
    ∃ c : ContractLife,
      c.effective = true ∧ c.voidablePower = true ∧ c.invalid = false := by
  refine ⟨{ established := true, effective := true, invalid := false, voidablePower := true },
    rfl, rfl, rfl⟩

/-- 公定力不是事实真。 -/
theorem gongding_still :
    ∃ a : AdminAct,
      a.publicValidity = true ∧ a.factTrue = false ∧ a.substantiallyLegal = false := by
  refine ⟨{ publicValidity := true, substantiallyLegal := false, factTrue := false },
    rfl, rfl, rfl⟩

/-- 刑事无罪民事可赔。 -/
structure SameFact where
  criminalGuilty : Bool
  civilLiable : Bool

theorem criminal_not_cover_civil :
    ∃ s : SameFact, s.criminalGuilty = false ∧ s.civilLiable = true := by
  refine ⟨{ criminalGuilty := false, civilLiable := true }, rfl, rfl⟩

end JurisLean.CN.World
