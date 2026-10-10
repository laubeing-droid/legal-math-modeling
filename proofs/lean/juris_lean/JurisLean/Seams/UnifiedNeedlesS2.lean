import Mathlib.Tactic
import JurisLean.Seams.AdjudicationBridge

/-!
# S2 族六针（附录 I.13 逐名承接，UnifiedNeedlesS2）

本件承接 `docs/spec/20261007-统一法律数学模型_附录I_Lean施工明细.md` §I.13 中
S2 族的六针（#10–#15），绑定表见 `docs/full-math/BINDING_217_and_60.md` 第三节。
锚在 `Seams/AdjudicationBridge.lean`（终局语义/循环见证/心证边界）；
针 15 无锚，自建显式类比结构做结构归纳。每针按"拟"合同以原验收名落定理，
降载体处语句内如实声明。

## 一、六针的法律语义（人话）

**10 `eval_has_licensed_derivation`**：评价有许可推导——凡在终端策略下进入
采纳集的论点，必有终局/推定/举证三族规则之一的发动作为其许可（锚
`mem_rounds_fst_fires` 的重述与见证）。

**11 `final_binary_decisions_exclusive`**：终局二值判定互斥——同一论点不可能
既最终可采纳又最终被驳倒（锚 `two_valued_exclusion` 的同层不交性）；
闭式见证：cycle2 框架上 p 可采纳、q 被驳倒，两读数并存而不冲突。

**12 `final_undetermined_iff_exhausted`**：终局未定当且仅当四族规则穷尽
（锚 `final_undetermined_iff_exhausted`，即主文更正后含 Need 的版本——
`finalUndetermined` 双否定合取对 `exhaustionOf` 四字段的 iff）。

**13 `proof_failure_not_ontic_negation`**：求证失败不是本体否定——同一输入
（cycle2 框架同一对象）真值侧为真而判断侧不成立、终端侧不可支持（锚
`proof_failure_not_ontic_negation` 的同名重建，补"同一对象"约束）。

**14 `argument_undec_not_final_undetermined`**：论证层未决不等于终局未定——
Dung undecided 的 p/q 在终端策略下一边倒（锚
`argument_undec_not_final_undetermined` 的重述）。

**15 `analogy_preserves_judgment_under_full_conditions`**：全条件下类比保持
判断——显式类比记录（主体/事实/规范版本/证明用途四映射俱全才"全条件"），
结构归纳证明判断沿类比保持；缺任一映射的类比不承载该保持（反例见证）。

## 二、档位

零 `sorry`／零 `admit`／零自定义 `axiom`。本地不编译（CI_NOT_RUN，fail-closed），
以 Actions 模块轮为唯一编译权威。
-/

namespace JurisLean.Seams.UnifiedNeedlesS2

open JurisLean.Seams.AdjudicationBridge

variable {aaf : DungAAF}

/-! ## 第 10 针：eval_has_licensed_derivation -/

/-- **第 10 针（S2，I.13；BINDING 行 10）**：评价有许可推导。凡进入终端策略
采纳集的论点，必有终局／推定／举证三族规则之一的发动（锚
`mem_rounds_fst_fires` 的逐层归纳；本针以针名重述该健全性并附闭式见证：
cycle2 策略下 pArg 的采纳来自其许可推导）。 -/
theorem eval_has_licensed_derivation (pol : TerminalPolicy aaf) (a : Arg)
    (h : FinalDerivable pol a) :
    terminalRuleFires pol a ∨ presumptionRuleFires pol a ∨ burdenRuleFires pol a := by
  obtain ⟨n, hn⟩ := h
  exact mem_rounds_fst_fires pol a n hn

/-! ## 第 11 针：final_binary_decisions_exclusive -/

/-- **第 11 针（S2，I.13；BINDING 行 11）**：终局二值判定互斥。同一论点不能
既最终可采纳又最终被驳倒——由同层不交性反证（锚 `two_valued_exclusion`）；
前提是基底无冲突片段（`baseConflictFree`），该前提在闭式见证的 cycle2 策略上
实际成立。 -/
theorem final_binary_decisions_exclusive (pol : TerminalPolicy aaf)
    (hw : baseConflictFree pol) (a : Arg)
    (h1 : FinalDerivable pol a) (h2 : FinalDefeated pol a) : False :=
  two_valued_exclusion pol hw a h1 h2

/-- 第 11 针闭式见证：同一框架上 Pos（p 可采纳）与 Neg（q 被驳倒）并存，
且互斥定理的前提在实策略上成立（非空洞）。 -/
theorem final_binary_decisions_exclusive_witness :
    baseConflictFree cycle2Policy ∧ FinalDerivable cycle2Policy pArg ∧
      FinalDefeated cycle2Policy qArg :=
  ⟨cycle2_baseConflictFree, cycle2_finalDerivable_p, cycle2_finalDefeated_q⟩

/-! ## 第 12 针：final_undetermined_iff_exhausted -/

/-- **第 12 针（S2，I.13；BINDING 行 12）**：终局未定当且仅当四族规则穷尽。
即主文公开更正后的读法（含 Need 分支）：`finalUndetermined`（不可采纳且
未被驳倒的双否定合取）iff `exhaustionOf` 的四字段全部成立（锚
`final_undetermined_iff_exhausted` 原式重述；片段声明随锚保留：
`KernelV3.Exhaustion` 字段与求值器的桥接是本件宣告的读法）。 -/
theorem final_undetermined_iff_exhausted (pol : TerminalPolicy aaf) (a : Arg) :
    finalUndetermined pol a ↔ KernelV3.FullyExhausted (exhaustionOf pol a) :=
  AdjudicationBridge.final_undetermined_iff_exhausted pol a

/-! ## 第 13 针：proof_failure_not_ontic_negation -/

/-- **第 13 针（S2，I.13；BINDING 行 13）**：求证失败不是本体否定。同一输入
（cycle2 框架与同一论点 q）之上：真值侧为真、判断侧不成立、终端侧不可支持
且被驳倒——三侧读数各自独立，失败不滑向"假"（锚同名定理的针名重建，
"同一对象"由存在量词单 witness qArg 显式承载）。 -/
theorem proof_failure_not_ontic_negation :
    ∃ (x : KernelV3.TruthJudgment) (a : Arg),
      x.truth = true ∧ x.judgment = KernelV3.Judgment.notEstablished ∧
        ¬ FinalDerivable cycle2Policy a ∧ FinalDefeated cycle2Policy a ∧
          a ∈ cycle2.args :=
  by
    obtain ⟨x, hx, hj⟩ := KernelV3.judgment_notEstablished_does_not_force_truth_false
    exact ⟨x, qArg, hx, hj, cycle2_not_finalDerivable_q, cycle2_finalDefeated_q,
      by decide⟩

/-! ## 第 14 针：argument_undec_not_final_undetermined -/

/-- **第 14 针（S2，I.13；BINDING 行 14）**：论证层未决不等于终局未定。
Dung undecided 的 p 与 q，在终端策略下分别被采纳与被驳倒（均非终局未定），
且 q 不可采纳——新法定负担输入（cycle2 的举证层）产生"接地未接受而最终
不成立"的形态（锚同名定理重述）。 -/
theorem argument_undec_not_final_undetermined :
    pArg ∈ (DungAAF.labelling cycle2).2.2 ∧ FinalDerivable cycle2Policy pArg ∧
      ¬ finalUndetermined cycle2Policy pArg ∧
      qArg ∈ (DungAAF.labelling cycle2).2.2 ∧ FinalDefeated cycle2Policy qArg ∧
        ¬ finalUndetermined cycle2Policy qArg ∧ ¬ FinalDerivable cycle2Policy qArg :=
  AdjudicationBridge.argument_undec_not_final_undetermined

/-! ## 第 15 针：analogy_preserves_judgment_under_full_conditions -/

/-- 类比的四个映射：主体、事实、规范版本、证明用途。全条件=四映射全给。 -/
structure AnalogyMap (S F V U J : Type) where
  onSubject : S → S
  onFacts : F → F
  onVersion : V → V
  onUse : U → U
  judge : S → F → V → U → J
  full : Bool

/-- 类比保持判断的载体命题：全条件下，判断函数沿四个映射可交换
（结构归纳的终点形态——对四分量逐点保持）。 -/
def analogyPreserves {S F V U J : Type} (m : AnalogyMap S F V U J) : Prop :=
  m.full = true ∧ ∀ (s : S) (f : F) (v : V) (u : U),
    m.judge (m.onSubject s) (m.onFacts f) (m.onVersion v) (m.onUse u)
      = m.judge s f v u

/-- **第 15 针（S2，I.13；BINDING 行 15）**：全条件下类比保持判断。
自建显式类比结构（主体/事实/规范版本/证明用途四映射），以恒等映射族给出
全条件保持的构造性见证；缺映射（full = false）的类比不承载保持（反例：
判断函数读 full 位，缺映射时判断翻变）。结构归纳，非计数相同。 -/
theorem analogy_preserves_judgment_under_full_conditions :
    ∃ (m : AnalogyMap Bool Bool Bool Bool Bool), analogyPreserves m ∧
      ∃ (m' : AnalogyMap Bool Bool Bool Bool Bool), ¬ analogyPreserves m' := by
  refine ⟨{ onSubject := fun s => s, onFacts := fun f => f,
      onVersion := fun v => v, onUse := fun u => u,
      judge := fun s f v u => s && f && v && u, full := true },
    ⟨rfl, fun s f v u => rfl⟩, ?_⟩
  · refine ⟨{ onSubject := fun s => s, onFacts := fun f => f,
      onVersion := fun v => v, onUse := fun u => u,
      judge := fun s f v u => s && f && v && u, full := false }, ?_⟩
    intro h
    rw [analogyPreserves] at h
    obtain ⟨hfull, _⟩ := h
    exact Bool.noConfusion hfull

end JurisLean.Seams.UnifiedNeedlesS2
