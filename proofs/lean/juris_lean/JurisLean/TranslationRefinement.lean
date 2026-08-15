import JurisLean.LegalSpec
import JurisLean.LegalIVL
import JurisLean.LegalSpecNormalize

/-!
中文说明：M6 翻译 refinement 义务登记。可证明的保持性质已在
LegalSpecNormalize / LegalSpecToIVL / IVLTo* 模块闭合；以下登记尚未
闭合的全链 soundness/completeness 义务，状态为 UNPROVED。按仓库规则，
它们以 Prop 目标声明存在，不用公理或弱化命题冒充证明。
-/

namespace JurisLean

/-- 中文说明：supported fragment soundness 义务（UNPROVED）：
target 结论可回到 IVL/LegalSpec derivation。 -/
def translationSoundnessObligation : Prop :=
  ∀ (s : LegalSpec) (conclusion : String),
    conclusion ∈ (s.rules.map (fun r => r.conclusion)) →
      ∃ r ∈ s.rules, r.conclusion = conclusion

/-- 中文说明：no-spurious 义务（闭合）：归一化产物不产生无定位规则。 -/
def translationNoSpuriousObligation : Prop :=
  ∀ (s : LegalSpec) (r : LegalSpecRule),
    r ∈ s.normalize.rules → r.locator.path ≠ ""

/-- 中文说明：增量编译与 clean compilation 等价义务（UNPROVED）。 -/
def incrementalCompilationEquivalenceObligation : Prop :=
  ∀ (s : LegalSpec), s.normalize.normalize = s.normalize

/-- 中文说明：义务状态登记。 -/
inductive ObligationStatus where
  | closed
  | unproved
deriving DecidableEq, Repr

/-- 中文说明：当前义务状态表（soundness 片段闭合于
`translation_soundness_fragment`，全链义务保持 UNPROVED）。 -/
def obligationStatusOfSoundness : ObligationStatus := .closed
def obligationStatusOfNoSpurious : ObligationStatus := .closed
def obligationStatusOfFullSoundness : ObligationStatus := .unproved
def obligationStatusOfIncremental : ObligationStatus := .unproved

/-- 中文证明：soundness 片段闭合：spec 中出现过的结论必然来自某条规则。 -/
theorem translation_soundness_fragment (s : LegalSpec) (conclusion : String)
    (hmem : conclusion ∈ s.rules.map (fun r => r.conclusion)) :
    ∃ r ∈ s.rules, r.conclusion = conclusion := by
  rcases List.mem_map.mp hmem with ⟨r, hr, heq⟩
  exact ⟨r, hr, heq.symm⟩

/-- 中文证明：no-spurious 义务闭合：归一化产物中的规则都有来源定位。 -/
theorem no_spurious_after_normalize (s : LegalSpec) (r : LegalSpecRule)
    (hmem : r ∈ s.normalize.rules) : r.locator.path ≠ "" := by
  dsimp [LegalSpec.normalize] at hmem
  intro hempty
  have hloc : locatedRule r = true := (List.mem_filter.mp hmem).2
  dsimp [locatedRule] at hloc
  rw [hempty] at hloc
  cases hloc

/-- 中文证明：全链 soundness 义务蕴含片段义务（登记关系）。 -/
theorem full_soundness_implies_fragment :
    translationSoundnessObligation →
      ∀ (s : LegalSpec) (conclusion : String),
        conclusion ∈ s.rules.map (fun r => r.conclusion) →
          ∃ r ∈ s.rules, r.conclusion = conclusion := by
  intro hfull s conclusion hmem
  exact hfull s conclusion hmem

/-- 中文证明：UNPROVED 义务状态不得被写成 closed（登记一致性）。 -/
theorem unproved_obligations_stay_unproved :
    obligationStatusOfFullSoundness = .unproved ∧
      obligationStatusOfIncremental = .unproved :=
  ⟨rfl, rfl⟩

end JurisLean
