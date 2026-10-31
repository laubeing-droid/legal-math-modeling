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

def initSit : Sit := Sit.mk true 0 0 0 0 false false 0 false 0 0

/-- 无裁判正常对象。 -/
theorem no_trial_normal :
    ∃ s : Sit,
      s.procOn = true ∧ s.lCreated = true ∧ s.aiVer = 0 ∧ s.fF = true :=
  ⟨Sit.mk true 1 1 0 1 true false 1 true 0 1, rfl, rfl, rfl, rfl⟩

/-- 提议：aiVer+1，L/N/F 不变。 -/
def propose (s : Sit) : Sit := Sit.mk (fF s) (eRaw s) (eAdm s) (eExcl s) (nVer s) (lCreated s) (lConfirmed s) (clk s) (procOn s) (aiVer s + 1) (pLedger s)

theorem propose_frame_L (s : Sit) : (propose s).lCreated = lCreated s := by
  cases s; rfl

theorem propose_frame_F (s : Sit) : (propose s).fF = fF s := by
  cases s; rfl

theorem propose_frame_N (s : Sit) : (propose s).nVer = nVer s := by
  cases s; rfl

/-- 学习：aiVer+1 且 eRaw+1。不改 N/F/L。 -/
def learn (s : Sit) : Sit := Sit.mk (fF s) (eRaw s + 1) (eAdm s) (eExcl s) (nVer s) (lCreated s) (lConfirmed s) (clk s) (procOn s) (aiVer s + 1) (pLedger s)

theorem learn_frame_N (s : Sit) : (learn s).nVer = nVer s := by cases s; rfl
theorem learn_frame_F (s : Sit) : (learn s).fF = fF s := by cases s; rfl
theorem learn_frame_L (s : Sit) : (learn s).lCreated = lCreated s := by cases s; rfl

/-- Record：eRaw+1，F 不变。 -/
def record (s : Sit) : Sit := Sit.mk (fF s) (eRaw s + 1) (eAdm s) (eExcl s) (nVer s) (lCreated s) (lConfirmed s) (clk s) (procOn s) (aiVer s) (pLedger s)

theorem record_frame_F (s : Sit) : (record s).fF = fF s := by cases s; rfl

/-- 准入。 -/
def admit (s : Sit) : Sit := Sit.mk (fF s) (eRaw s) (eAdm s + 1) (eExcl s) (nVer s) (lCreated s) (lConfirmed s) (clk s) (procOn s) (aiVer s) (pLedger s)

/-- 排除。 -/
def exclude (s : Sit) : Sit := Sit.mk (fF s) (eRaw s) (eAdm s) (eExcl s + 1) (nVer s) (lCreated s) (lConfirmed s) (clk s) (procOn s) (aiVer s) (pLedger s)

/-- 合法形成步。 -/
inductive Eff
  | confirmatory
  | constitutive
  | performance
  | proceduralBinding
  deriving DecidableEq, Repr

def legalStep (s : Sit) (hasDoc : Bool) (e : Eff) : Sit :=
  match hasDoc, e with
  | true, Eff.constitutive => Sit.mk (fF s) (eRaw s) (eAdm s) (eExcl s) (nVer s) true (lConfirmed s) (clk s) true (aiVer s) (pLedger s)
  | true, Eff.confirmatory => Sit.mk (fF s) (eRaw s) (eAdm s) (eExcl s) (nVer s) (lCreated s) true (clk s) true (aiVer s) (pLedger s)
  | true, Eff.performance => Sit.mk (fF s) (eRaw s) (eAdm s) (eExcl s) (nVer s) (lCreated s) (lConfirmed s) (clk s) true (aiVer s) (pLedger s + 1)
  | true, Eff.proceduralBinding => Sit.mk (fF s) (eRaw s) (eAdm s) (eExcl s) (nVer s) (lCreated s) (lConfirmed s) (clk s) true (aiVer s) (pLedger s)
  | false, _ => s

theorem confirm_no_create (s : Sit) :
    (legalStep s true Eff.confirmatory).lCreated = lCreated s := by
  cases s; rfl

theorem nodoc_no_create (s : Sit) :
    (legalStep s false Eff.constitutive).lCreated = lCreated s := by
  cases s; rfl

theorem legalStep_frame_F (s : Sit) (hasDoc : Bool) (e : Eff) :
    (legalStep s hasDoc e).fF = fF s := by
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
      c.effective = true ∧ c.voidablePower = true ∧ c.invalid = false :=
  ⟨ContractLife.mk true true false true, rfl, rfl, rfl⟩

/-- 公定力不是事实真。 -/
theorem gongding_still :
    ∃ a : AdminAct,
      a.publicValidity = true ∧ a.factTrue = false ∧ a.substantiallyLegal = false :=
  ⟨AdminAct.mk true false false, rfl, rfl, rfl⟩

/-- 刑事无罪民事可赔。 -/
structure SameFact where
  criminalGuilty : Bool
  civilLiable : Bool

theorem criminal_not_cover_civil :
    ∃ s : SameFact, s.criminalGuilty = false ∧ s.civilLiable = true :=
  ⟨SameFact.mk false true, rfl, rfl⟩

end JurisLean.CN.World
