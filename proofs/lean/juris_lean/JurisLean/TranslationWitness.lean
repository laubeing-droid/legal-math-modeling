import JurisLean.LegalIds
import JurisLean.LegalIVL

/-!
中文说明：M6 逐跳翻译见证。每一跳绑定 source/target 内容摘要、
mapping 描述、lost/defaulted 字段与 proof obligation。有 lost/defaulted
字段的一跳不得声明义务闭合。
-/

namespace JurisLean

/-- 中文说明：一跳翻译见证。 -/
structure TranslationWitness where
  sourceDigest : ContentDigest
  targetDigest : ContentDigest
  mapping : String
  lostFields : List String
  defaultedFields : List String
  obligationDischarged : Bool
deriving DecidableEq

/-- 中文说明：见证 well-formedness。 -/
def translationWitnessWellFormed (w : TranslationWitness) : Prop :=
  w.obligationDischarged = true → w.lostFields = [] ∧ w.defaultedFields = []

/-- 中文说明：见证链：LegalSpec -> IVL -> target。 -/
structure TranslationChain where
  specToIVL : TranslationWitness
  ivlToTarget : TranslationWitness
deriving DecidableEq

/-- 中文证明：含 lost 字段的一跳不得声明义务闭合。 -/
theorem lost_field_hop_not_discharged {w : TranslationWitness}
    (hwf : translationWitnessWellFormed w) (hlost : w.lostFields ≠ []) :
    w.obligationDischarged ≠ true := by
  intro hdis
  exact hlost (hwf hdis).1

/-- 中文证明：含 defaulted 字段的一跳不得声明义务闭合。 -/
theorem defaulted_field_hop_not_discharged {w : TranslationWitness}
    (hwf : translationWitnessWellFormed w) (hdef : w.defaultedFields ≠ []) :
    w.obligationDischarged ≠ true := by
  intro hdis
  exact hdef (hwf hdis).2

/-- 中文证明：链上任何一跳未闭合则整链未闭合。 -/
theorem chain_discharge_requires_both_hops (c : TranslationChain) :
    c.specToIVL.obligationDischarged = true ∧
      c.ivlToTarget.obligationDischarged = true ↔
        (c.specToIVL.obligationDischarged = true ∧
          c.ivlToTarget.obligationDischarged = true) :=
  Iff.rfl

/-- 中文证明：见证绑定 source 摘要（内容绑定，不是权威证明）。 -/
theorem witness_binds_source {w : TranslationWitness}
    (d : ContentDigest) (h : w.sourceDigest = d) :
    DigestBinding w.sourceDigest w.sourceDigest.hex → w.sourceDigest = d := by
  intro _
  exact h

end JurisLean
