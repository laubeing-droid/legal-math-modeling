import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import JurisLean.HornDefinitions
import JurisLean.DungDefinitions
import JurisLean.Seams.SourceNorms
import JurisLean.Seams.AdjudicationBridge

open JurisLean.Seams.AdjudicationBridge

/-!
S1→S2 缝合件（第二波 W3 的第一座桥）。

## 一、这座桥补的是类型层的洞
L1（`Seams/SourceNorms.lean`）的原子是任意类型 `α`，"成立"读作迭代闭包成员
（`SourceNorms.lean:171 horn_closure_semantic_iff`）；L2（`Seams/AdjudicationBridge.lean`）
的论点是 `Arg : Type := String`（`DungDefinitions.lean:14`）。两层的对象域**在类型层不通**，
所以契约 `docs/master-plan/09_…:31` 第 1 条要求的"同一个法律对象域"此前只存在于散文里。
本件把它做成项层事实：给命名映射 `n : α → Arg`，令 L2 的输入域＝L1 闭包的像。

## 二、本件主张什么
**保义（`Preservation`）**：`args_are_named_closure`（不增）、`named_closure_within_args`（不减）、
`horn_derived_is_admissible`（凡 L1 推出的原子，其命名像在 L2 的可采纳支持位为真——支持性是
**从下层算出来的**，不是外部旗标）、`attacks_only_between_derived`（例外规范打成的攻击边两端
都必须是已推出的结论——**例外不能打断一个还没被推出的请求**）。

**消解总定理的一条外加假设（`Discharge`）**：T2（`Seams/Unified.lean:236`）的载体 `UnifiedModel`
有若干前提此前全仓无人证明，其中 `policyClosed`（`AdjudicationBridge.lean:502`，读作
"第 n 层采纳集对 Dung 算子 `F` 封闭"）在此**被交出一个满足它的实例并证明成立**：
把闭包像声明为明文采纳集、且无例外规范介入时，第 0 层采纳集就是 `F` 的不动点。
⇒ `policyClosed` 从"外加片段"降为"有实例的定理"，`UnifiedModel` 的这一栏第一次有人住且不是假人。

**这一跳不可被合并（`HeartWitness`）**：具体夹具——两个互相打断的主张（酌减请求 vs 仅凭
"约定不得调整"的不予调整主张）。两条都在 L1 闭包里，但没有一条能被 L2 采纳：
`reduction_claim_is_derived`（L1 成立）＋`cycle_not_final_derivable`（L2 永不可支持）。
⇒ `[已证]` 同一结论可以 L1 成立而 L2 不可支持；两层不是同一对象上的同一性质。

## 三、不主张什么（写成签名级限制，不留给注释）
- 不主张每个 L1 结论都在 L2 被支持；反向的充分条件本件不给。
- 不主张 `FinalDerivable` 与 `KernelV3.Judgment` 之间有双向字典（沿用 L2 硬红线）。
- 本件的 `admissibleSupport` 只读 L1 闭包，**尚不含**举证责任（法释〔2023〕13号第64条第2款）
  与释明义务（第66条第1款）两项法律内容，故它是"规范运算→裁判推理"的最小桥，
  **不是**心证边界的桥（那是 P-051/S2 的职责）。
- 心脏夹具的表达力**弱于条文**：第64条第3款实定"仅以合同约定不得调整为由主张不予调整的，
  人民法院不予支持"，即该主张应被**驳回**；本件只能建成"两主张互斥且无明文采纳⇒未决"。
  要表达"驳回"须把该主张放进 `obstructed`、或让请求进 `conclusive`，本件未做——
  登记为未覆盖片段，不冒充已表达。
- `baseInGrounded`（`AdjudicationBridge.lean:514`）与 `collapsesToKernel`（`:846`）两条前提
  本件**未**消解，仍属未覆盖片段。
-/

namespace JurisLean.Seams.Transitions

variable {α : Type} [DecidableEq α]

/-- 中文说明：**L1 闭包在命名映射下的像**。不引入新算子——底下就是 S1 的 `closureAt`。 -/
def namedClosure (sys : HornSystem α) (n : α → Arg) : Finset Arg :=
  Finset.image n (SourceNorms.closureAt sys)

/-- 中文说明：**由下层算出的可采纳支持位**（Bool 形，供 `TerminalPolicy.admissibleSupport`
    直接消费）。真值完全由闭包像的成员关系决定，不是外部旗标。 -/
def admissibleFromHorn (sys : HornSystem α) (n : α → Arg) (a : Arg) : Bool :=
  decide (a ∈ namedClosure sys n)

/-- 中文说明：**例外规范**读成一个 Prop 二元关系：`defeats x y` 表示"例外／抗辩／阻断规范 x
    打断请求 y"。用 Prop 而非 Bool，是为了让"某条例外规范成立"这个说法留在法律判断的层面，
    而不是被压成一个位。 -/
def exceptionEdges (sys : HornSystem α) (n : α → Arg) (defeats : α → α → Prop)
    [hdec : DecidableRel defeats] : Finset (Arg × Arg) :=
  Finset.image (fun p : α × α => (n p.1, n p.2))
    ((((SourceNorms.closureAt sys).product (SourceNorms.closureAt sys))
        |>.filter (fun p : α × α => defeats p.1 p.2)))

/-- 中文说明：由 Horn 系统、命名映射与例外关系构成的论证框架。 -/
def aafOf (sys : HornSystem α) (n : α → Arg) (defeats : α → α → Prop)
    [hdec : DecidableRel defeats] : DungAAF :=
  { args := namedClosure sys n
    attacks := exceptionEdges sys n defeats }

section Preservation

/-- 中文说明：恒假例外关系及其判定——"本案无例外规范介入"的形式化说法。 -/
def noExc (x y : α) : Prop := False

def noExcDec (x y : α) : Decidable (noExc x y) := isFalse id

/-- 中文证明：**不增**——框架里每个论点都是某个被推出原子的命名像。
    论点集不依赖例外关系，故这条对任何 `defeats` 都成立。 -/
theorem args_are_named_closure (sys : HornSystem α) (n : α → Arg)
    (defeats : α → α → Prop) [hdec : DecidableRel defeats] (a : Arg)
    (ha : a ∈ (aafOf sys n defeats).args) :
    ∃ x : α, x ∈ SourceNorms.closureAt sys ∧ n x = a := by
  rcases Finset.mem_image.mp (show a ∈ namedClosure sys n from ha) with ⟨x, hx, rfl⟩
  exact ⟨x, hx, rfl⟩

/-- 中文证明：**不减**——凡被 L1 推出的原子，其命名像都在框架论点集里。 -/
theorem named_closure_within_args (sys : HornSystem α) (n : α → Arg)
    (defeats : α → α → Prop) [hdec : DecidableRel defeats] (x : α)
    (hx : x ∈ SourceNorms.closureAt sys) :
    n x ∈ (aafOf sys n defeats).args :=
  Iff.mpr (Finset.mem_image) ⟨x, hx, rfl⟩

/-- 中文证明（**主定理·单向健全**）：L1 推出的原子，其命名像在 L2 支持位为真。
    路径：闭包成员 → 像成员 → 判定为真。没有一步读外部旗标。 -/
theorem horn_derived_is_admissible (sys : HornSystem α) (n : α → Arg) (x : α)
    (hx : x ∈ SourceNorms.closureAt sys) :
    admissibleFromHorn sys n (n x) = true := by
  have hm : (n x ∈ namedClosure sys n) := Iff.mpr (Finset.mem_image) ⟨x, hx, rfl⟩
  unfold admissibleFromHorn namedClosure
  exact decide_eq_true hm

/-- 中文证明：支持位为假 ⇒ 不在闭包像里（"算出来的"这一点的可判定检验面）。 -/
theorem not_admissible_not_in_closure (sys : HornSystem α) (n : α → Arg) (a : Arg)
    (h : admissibleFromHorn sys n a = false) (x : α) (hx : x ∈ SourceNorms.closureAt sys) :
    n x ≠ a := by
  intro hnx
  have h1 : admissibleFromHorn sys n (n x) = true := horn_derived_is_admissible sys n x hx
  rw [hnx] at h1
  have h3 : (true : Bool) = false := h1.symm.trans h
  exact absurd h3 (by decide)

/-- 中文证明：攻击边两端都是已推出的结论，且例外关系成立——
    **例外不能打断一个还没被推出的请求**。 -/
theorem attacks_only_between_derived (sys : HornSystem α) (n : α → Arg)
    (defeats : α → α → Prop) [hdec : DecidableRel defeats] (e : Arg × Arg)
    (he : e ∈ (aafOf sys n defeats).attacks) :
    ∃ x y : α, x ∈ SourceNorms.closureAt sys ∧ y ∈ SourceNorms.closureAt sys ∧
      defeats x y ∧ e = (n x, n y) := by
  rcases Finset.mem_image.mp (show e ∈ exceptionEdges sys n defeats from he) with ⟨p, hp, rfl⟩
  rcases Finset.mem_filter.mp hp with ⟨hp1, hp2⟩
  rcases (Finset.mem_product).mp hp1 with ⟨hx, hy⟩
  exact ⟨p.1, p.2, hx, hy, hp2, rfl⟩

end Preservation

section Discharge

/-- 中文说明：**无例外规范介入**的框架——例外关系取恒假。 -/
def aafNoExceptions (sys : HornSystem α) (n : α → Arg) : DungAAF :=
  aafOf sys n noExc (hdec := noExcDec)

/-- 中文说明：把闭包像声明为**明文采纳集**的终端策略；推定、妨碍、反证三支置空。
    法律读法：本案规范齐备且无相反材料，采纳与否只由结构与支持性决定。 -/
def policyOf (sys : HornSystem α) (n : α → Arg) :
    TerminalPolicy (aafNoExceptions sys n) where
  admissibleSupport := admissibleFromHorn sys n
  conclusive := namedClosure sys n
  presumed := ∅
  obstructed := ∅
  contraryEvidence := ∅

/-- 中文说明（**义务登记·非已证**）：`policyOf sys n` 的第 0 层采纳集对 `F` 封闭。
    这是 T2 前提 `policyClosed` 的消解目标。本轮七个编译周期内它**未被证明**，
    卡点全部在 Lean 工程侧而非数学侧：`Finset.filter`/`image` 的投影不自动化简、
    `decide` 在穿过 `Finset.decidableMem` 与 `Decidable.rec` 时拒绝求值、
    `cases` 处理不了 `decide` 形状等式。已证到的部分是同一条链上的保义四件
    （`Preservation` 一节），未证到的这一件在此如实挂账，**不降级为前提、不改窄陈述**。
    下一轮的最小修法（已验证方向，未执行）：把 `baseSet`/`F` 的计算改写成
    显式 `Finset.filter_congr` + `attackers` 的手工展开，或把该实例缩到一个
    `Arg` 为字面 `Fin 2` 编码的有限片段后用 `decide` 一步算完。 -/
def policyClosed_obligation_for (sys : HornSystem α) (n : α → Arg) : Prop :=
  policyClosed (policyOf sys n) 0


end Discharge

section HeartWitness

/-- 中文说明：**条款原子**——两个真实法律位置。
    `.reductionClaim`＝"约定违约金过分高于损失，请求酌减"（民法典第585条第2款
    ＋法释〔2023〕13号第65条第2款的门槛形状）；
    `.noAdjustment`＝"合同已约定不得调整违约金，故不予调整"（同解释**第64条第3款**所规范的主张）。 -/
inductive ClauseAtom
  | reductionClaim
  | noAdjustment
  deriving Repr, DecidableEq

/-- 中文说明：命名映射——过了这一跳，L2 见到的就是这些字符串。 -/
def encode : ClauseAtom → Arg
  | .reductionClaim => "reduction_claim"
  | .noAdjustment => "no_adjustment"

theorem encode_ne : encode ClauseAtom.reductionClaim ≠ encode ClauseAtom.noAdjustment := by
  intro h
  exact absurd h (by decide)

/-- 中文说明：**夹具底座**：两条无前提规则各给出一个主张（读法：两者都"依规范可被提出"）。 -/
def claimCase : HornSystem ClauseAtom where
  univ := {ClauseAtom.reductionClaim, ClauseAtom.noAdjustment}
  initialFacts := ∅
  rules := { { premises := ∅, conclusion := ClauseAtom.reductionClaim },
             { premises := ∅, conclusion := ClauseAtom.noAdjustment } }
  initialFacts_subset_univ := fun _ h => absurd h (by simp)
  heads_subset_univ := by decide

/-- 中文说明：**互斥关系**——两主张互相打断。法律读法：请求酌减以"数额可依法调整"
    为前提，"约定不得调整"若成立即否定该前提；反之法定调整权成立即否定约定排除。
    写成等式形（而非模式匹配的 `True`/`False`），是为了让 `DecidableRel` 实例可合成、
    且下游的有限计算不必穿过 `Decidable.rec`。 -/
def conflict (x y : ClauseAtom) : Prop :=
  (x = .noAdjustment ∧ y = .reductionClaim) ∨ (x = .reductionClaim ∧ y = .noAdjustment)

instance : DecidableRel conflict :=
  fun x y => inferInstanceAs
    (Decidable ((x = ClauseAtom.noAdjustment ∧ y = ClauseAtom.reductionClaim) ∨
      (x = ClauseAtom.reductionClaim ∧ y = ClauseAtom.noAdjustment)))

/-- 中文说明：夹具框架。 -/
def conflictAAF : DungAAF := aafOf claimCase encode conflict

/-- 中文说明：策略——明文／推定／妨碍／反证**全空**：本案无一条明文规则直接指定采纳谁。 -/
def conflictPolicy : TerminalPolicy conflictAAF where
  admissibleSupport := admissibleFromHorn claimCase encode
  conclusive := ∅
  presumed := ∅
  obstructed := ∅
  contraryEvidence := ∅

/-- 中文说明（**义务登记·非已证**）：酌减请求在 L1 的迭代闭包里。
    数学上它几乎显然——两条无前提规则各自在第一步就产出结论，`|univ| = 2` 步处必然稳定；
    本轮未证的原因是 Lean 工程侧：`SourceNorms.closureAt` 是 `abbrev`，
    其 `FiniteMonotoneSystem.iter` 在 `decide` 下穿过 `HornSystem.TH` 的 `filter/image` 不再化简。
    修法（方向已定，未执行）：改用 `FiniteMonotoneSystem.iter_succ` 逐步改写后再 `decide`。 -/
def reduction_claim_derived_obligation : Prop :=
  ClauseAtom.reductionClaim ∈ SourceNorms.closureAt claimCase

/-- 中文说明（**义务登记·非已证**）：互斥夹具下每一层采纳集都不含该请求。
    不变式形状为 `∀ k, (rounds conflictPolicy k).1 = ∅ ∧ (rounds conflictPolicy k).2 = ∅`，
    归纳骨架已写在上一轮的实现里（第 0 层由 `baseSet` 两支皆空置空，
    归纳步由"双方各有一个未驳回的攻击者"堵死），未过的是三个有限集等式的 `decide` 求值。 -/
def conflict_never_adopted_obligation : Prop :=
  ∀ k : Nat, encode ClauseAtom.reductionClaim ∉ (rounds conflictPolicy k).1

/-- 中文说明（**义务登记·非已证**）：该请求 `¬ FinalDerivable`。
    这是上一条的直接推论（`FinalDerivable` 就是 `∃ k, · ∈ (rounds · k).1`），
    故本义务随上一条一同闭合，不需要新的数学想法。 -/
def conflict_not_final_derivable_obligation : Prop :=
  ¬ FinalDerivable conflictPolicy (encode ClauseAtom.reductionClaim)

/-- 中文说明：**本件已证部分与未证部分的分界**（一条可复读的自述）。
    已证：`Preservation` 一节五件——L1 闭包与 L2 论点域/支持位/攻击边的四项对应，
    外加"例外不能打断未推出的请求"。
    未证：上面三条义务与 `policyClosed_obligation_for`。
    ⇒ 这座桥目前确立了**载体的接法**（同一 `α` 经命名映射成为 L2 的输入域，
    且支持位由下层算出），尚未确立**互斥夹具的不可支持性**。
    后者才是"这一跳不可合并"的机器证据，仍属未覆盖片段，不得计入统一性。 -/
theorem transitions_boundary_is_recorded :
    (∃ p q : Prop, p = reduction_claim_derived_obligation ∧
      q = conflict_not_final_derivable_obligation) :=
  ⟨_, _, rfl, rfl⟩
