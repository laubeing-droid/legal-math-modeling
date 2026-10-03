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
`reduction_claim_derived_obligation`（L1 成立）＋`conflict_never_adopted_obligation`
与 `conflict_not_final_derivable_obligation`（L2 每层都不采纳，因而不是 `FinalDerivable`）。
⇒ `[已证]` 同一结论可以 L1 成立而 L2 不可支持；两层不是同一对象上的同一性质。

## 三、不主张什么（写成签名级限制，不留给注释）
- 不主张每个 L1 结论都在 L2 被支持；反向的充分条件本件不给。
- 不主张 `FinalDerivable` 与 `KernelV3.Judgment` 之间有双向字典（沿用 L2 硬红线）。
- 本件的 `admissibleSupport` 只读 L1 闭包，**尚不含**举证责任（法释〔2023〕13号第64条第2款）
  与释明义务（第66条第1款）两项法律内容，故它是"规范运算→裁判推理"的最小桥，
  **不是**心证边界的桥（那是 P-051/S2 的职责）。
- 心脏夹具的表达力**弱于条文**：第64条第3款实定"仅以合同约定不得调整为由主张不予调整的，
  人民法院不予支持"，即该主张应被**驳回**；本件的互斥夹具一节只建成"两主张互斥且无明文采纳
  ⇒未决"，§五另给该款的驳回编码。**先前此处写作"须把该主张放进 `obstructed`、或让请求进
  `conclusive`"是错的**（那两支只作用于 `baseSet`，产不出 `FinalDefeated`），已在 §五 更正。
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

/-- 中文说明：`noExc` 的可判定性**实例**，值就是上面的 `noExcDec`。
    本轮实测的卡点：`Finset.mem_filter` 要合成 `DecidablePred (fun p => noExc p.1 p.2)`，
    只具名传 `(hdec := noExcDec)` 到 `exceptionEdges` 不够——`mem_filter` 那一侧仍搜索失败。 -/
instance noExcDecidableRel {β : Type} : DecidableRel (noExc (α := β)) := noExcDec

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

/-- 中文证明（**技术引理·闭包成员的唯一生产方式**）：`sys` 里任何**无前提规则**的结论都在
    L1 的 |univ| 步闭包里。
    路径是仓内已证的典范模型 `SourceNorms.closure_is_model`（闭包自身是模型）在该规则处的
    闭合条件：前提空 ⇒ 前提含于闭包 ⇒ 结论进闭包。
    工程说明：这条引理**故意绕开** `FiniteMonotoneSystem.iter` 的逐层计算——
    `SourceNorms.closureAt` 是 `abbrev`，`decide` 穿过 `HornSystem.TH` 的 `filter/image`
    不再化简（前九轮编译的实测卡点），而固定点一侧的等式把同一件事变成一次成员推理。 -/
theorem noPremiseRule_in_closure (sys : HornSystem α) (r : HornRule α)
    (hr : r ∈ sys.rules) (hprem : r.premises = (∅ : Finset α)) :
    r.conclusion ∈ SourceNorms.closureAt sys := by
  refine ((SourceNorms.closure_is_model sys).2 r hr) ?_
  rw [hprem]
  exact Finset.empty_subset _

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

/-- 中文证明（技术引理）：恒假例外关系打不出任何攻击边——`filter` 的谓词是 `noExc`，
    而 `noExc x y` 就展开成 `False`，故筛出的对集为空，其像亦空。 -/
theorem exceptionEdges_noExc_eq_empty (sys : HornSystem α) (n : α → Arg) :
    exceptionEdges sys n noExc (hdec := noExcDec) = ∅ := by
  refine (Finset.eq_empty_iff_forall_notMem
    (s := exceptionEdges sys n noExc (hdec := noExcDec))).mpr ?_
  intro e he
  rcases Finset.mem_image.mp
    (show e ∈ exceptionEdges sys n noExc (hdec := noExcDec) from he) with ⟨p, hp, rfl⟩
  rcases Finset.mem_filter.mp hp with ⟨_, hno⟩
  exact hno

/-- 中文证明（技术引理）：无例外规范介入时，框架的攻击边集为空。 -/
theorem aafNoExceptions_attacks_eq_empty (sys : HornSystem α) (n : α → Arg) :
    (aafNoExceptions sys n).attacks = ∅ :=
  exceptionEdges_noExc_eq_empty sys n

/-- 中文证明（技术引理）：攻击边为空 ⇒ 每个论点的攻击者集为空。
    `attackers aaf a` 就是把 `aaf.args` 按"攻击 `a`"来筛，边集空则该筛必空。 -/
theorem attackers_eq_empty_of_attacks_empty (aaf : DungAAF) (a : Arg)
    (h : aaf.attacks = ∅) : DungAAF.attackers aaf a = ∅ := by
  refine (Finset.eq_empty_iff_forall_notMem (s := DungAAF.attackers aaf a)).mpr ?_
  intro b hb
  have hb' : (b, a) ∈ aaf.attacks := (Finset.mem_filter.mp hb).2
  rw [h] at hb'
  exact notMemEmptyFinset _ hb'

/-- 中文证明（技术引理，`policyClosed` 的**技术核**）：攻击边为空 ⇒ `F aaf` 把论点集映回自身。
    `F aaf S` 只筛掉"存在一个不被 `S` 打回的攻击者"的论点；攻击者集恒空时该条件**真空成立**，
    于是 `F aaf aaf.args = aaf.args`，即论点集是 `F` 的不动点。
    工程说明：这里用 `Finset.ext` 手工展开两次成员刻画，不用 `decide`——
    本 pin 的 `decide` 穿不过 `Finset.filter` 的 `Decidable.rec`。 -/
theorem F_args_eq_args_of_attacks_empty (aaf : DungAAF) (h : aaf.attacks = ∅) :
    DungAAF.F aaf aaf.args = aaf.args := by
  refine Finset.ext ?_
  intro a
  refine ⟨fun ha => (Finset.mem_filter.mp ha).1, fun ha => Finset.mem_filter.mpr ⟨ha, ?_⟩⟩
  intro b hb
  rw [attackers_eq_empty_of_attacks_empty aaf a h] at hb
  exact absurd hb (notMemEmptyFinset b)

/-- 中文证明（技术引理）：把闭包像声明为明文采纳集时，第 0 层采纳集**恰是**框架论点集。
    `baseSet` 的谓词是"不被妨碍 ∧（明文 ∨（推定 ∧ 无反证攻击））"；本策略里妨碍集空、
    明文集＝论点集，故谓词对每个论点都真。 -/
theorem baseSet_policyOf_eq_args (sys : HornSystem α) (n : α → Arg) :
    baseSet (policyOf sys n) = (aafNoExceptions sys n).args := by
  refine Finset.ext ?_
  intro a
  refine ⟨fun ha => (Finset.mem_filter.mp ha).1,
    fun ha => Finset.mem_filter.mpr ⟨ha, ⟨fun h => notMemEmptyFinset a h, Or.inl ha⟩⟩⟩

/-- 中文证明（**义务闭合·第 4 条**）：`policyOf sys n` 的第 0 层采纳集对 Dung 算子 `F` 封闭。
    原为 `def policyClosed_obligation_for : Prop` 挂账项，陈述一字未改，改为 `theorem`。
    链条：`policyClosed` 展开 → `rounds_zero_fst`（第 0 层＝`baseSet`）→
    `baseSet_policyOf_eq_args`（该层＝论点集）→ `F_args_eq_args_of_attacks_empty`
    （无例外规范 ⇒ 攻击边空 ⇒ 论点集是 `F` 的不动点）。
    ⇒ T2（`Seams/Unified.lean:236`）载体 `UnifiedModel` 的 `policyClosed` 一栏
    第一次有**被证明成立**的实例，不再只是外加片段。 -/
theorem policyClosed_obligation_for (sys : HornSystem α) (n : α → Arg) :
    policyClosed (policyOf sys n) 0 := by
  show DungAAF.F (aafNoExceptions sys n) (rounds (policyOf sys n) 0).1 =
      (rounds (policyOf sys n) 0).1
  rw [rounds_zero_fst, baseSet_policyOf_eq_args]
  exact F_args_eq_args_of_attacks_empty (aafNoExceptions sys n)
    (aafNoExceptions_attacks_eq_empty sys n)

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

/-- 中文说明（**见证项**）：`claimCase` 的两条无前提规则写成可命名的项，
    使"某条规则在 `rules` 里"这一有限成员判定可以在下游被单独引用。 -/
def rcRule : HornRule ClauseAtom :=
  { premises := ∅, conclusion := ClauseAtom.reductionClaim }

/-- 中文说明（**见证项**）：`claimCase` 的第二条无前提规则（"约定不得调整"主张）。 -/
def naRule : HornRule ClauseAtom :=
  { premises := ∅, conclusion := ClauseAtom.noAdjustment }

/-- 中文证明：两条规则确在 `claimCase.rules` 里（有限集字面量的成员判定，不涉及 `closureAt`
    的迭代计算，故 `decide` 在此可用——与文件头登记的卡点是不同的判定对象）。 -/
theorem rcRule_mem_rules : rcRule ∈ claimCase.rules := by decide

/-- 中文证明：第二条规则的成员判定。 -/
theorem naRule_mem_rules : naRule ∈ claimCase.rules := by decide

/-- 中文证明（**义务闭合·第 1 条**）：酌减请求在 L1 的迭代闭包里。
    原为 `def reduction_claim_derived_obligation : Prop` 挂账项，陈述一字未改，改为 `theorem`。
    证法走 `noPremiseRule_in_closure`（典范模型一侧），**不**穿过 `FiniteMonotoneSystem.iter`
    的逐层计算——这正是前九轮 `decide` 卡住的位置。
    法律读法：民法典第585条第2款＋法释〔2023〕13号第65条第2款的门槛形状，
    在夹具里就是一条无前提规则直接给出的主张。 -/
theorem reduction_claim_derived_obligation :
    ClauseAtom.reductionClaim ∈ SourceNorms.closureAt claimCase :=
  noPremiseRule_in_closure claimCase rcRule rcRule_mem_rules rfl

/-- 中文证明（技术引理）：另一主张同样在闭包里——互斥夹具要两条都在，才有环。 -/
theorem no_adjustment_derived :
    ClauseAtom.noAdjustment ∈ SourceNorms.closureAt claimCase :=
  noPremiseRule_in_closure claimCase naRule naRule_mem_rules rfl

/-- 中文证明（技术引理）：两条主张的命名像都在 L2 的论点集里（过了命名映射这一跳）。 -/
theorem reduction_in_args : encode ClauseAtom.reductionClaim ∈ conflictAAF.args :=
  Finset.mem_image.mpr ⟨ClauseAtom.reductionClaim, reduction_claim_derived_obligation, rfl⟩

/-- 中文证明（技术引理）：同上，另一条。 -/
theorem no_adjustment_in_args : encode ClauseAtom.noAdjustment ∈ conflictAAF.args :=
  Finset.mem_image.mpr ⟨ClauseAtom.noAdjustment, no_adjustment_derived, rfl⟩

/-- 中文证明（技术引理）：**论点集只有这两个元素**——L1 闭包走不出论域
    （仓内 `HornSystem.horn_result_subset_univ`），而 `claimCase.univ` 只列了两条原子。
    这条是"每个论点都有攻击者"的枚举依据。 -/
theorem conflict_args_eq_or (a : Arg) (ha : a ∈ conflictAAF.args) :
    a = encode ClauseAtom.reductionClaim ∨ a = encode ClauseAtom.noAdjustment := by
  rcases Finset.mem_image.mp (show a ∈ namedClosure claimCase encode from ha) with ⟨x, hx, rfl⟩
  have huniv : x ∈ claimCase.univ := HornSystem.horn_result_subset_univ claimCase hx
  rcases Finset.mem_insert.mp huniv with rfl | hx2
  · exact Or.inl rfl
  · rcases Finset.mem_singleton.mp hx2 with rfl
    exact Or.inr rfl

/-- 中文证明（技术引理）：互斥边"不予调整 → 酌减请求"确在框架的攻击集里。
    法律读法：主张"约定不得调整"若成立即否定酌减请求的要件前提（数额可依法调整）。 -/
theorem attack_no_adjustment_to_reduction :
    (encode ClauseAtom.noAdjustment, encode ClauseAtom.reductionClaim) ∈ conflictAAF.attacks := by
  refine Finset.mem_image.mpr ⟨(ClauseAtom.noAdjustment, ClauseAtom.reductionClaim), ?_, rfl⟩
  refine Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨no_adjustment_derived, reduction_claim_derived_obligation⟩, ?_⟩
  exact Or.inl ⟨rfl, rfl⟩

/-- 中文证明（技术引理）：互斥边的反向"酌减请求 → 不予调整"。
    法律读法：法定调整权成立即否定约定排除。 -/
theorem attack_reduction_to_no_adjustment :
    (encode ClauseAtom.reductionClaim, encode ClauseAtom.noAdjustment) ∈ conflictAAF.attacks := by
  refine Finset.mem_image.mpr ⟨(ClauseAtom.reductionClaim, ClauseAtom.noAdjustment), ?_, rfl⟩
  refine Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨reduction_claim_derived_obligation, no_adjustment_derived⟩, ?_⟩
  exact Or.inr ⟨rfl, rfl⟩

/-- 中文证明（技术引理）：夹具里**每个**论点都带一个攻击者，故"全部攻击者都已被驳回"
    这一支在驳倒集为空时永远堵死（`adoptedStep` 里 `attackers ⊆ ∅` 必假）。 -/
theorem conflict_arg_has_attacker (a : Arg) (ha : a ∈ conflictAAF.args)
    (hsub : DungAAF.attackers conflictAAF a ⊆ (∅ : Finset Arg)) : False := by
  rcases conflict_args_eq_or a ha with rfl | rfl
  · exact notMemEmptyFinset (encode ClauseAtom.noAdjustment)
      (hsub (mem_attackers_of_mem no_adjustment_in_args attack_no_adjustment_to_reduction))
  · exact notMemEmptyFinset (encode ClauseAtom.reductionClaim)
      (hsub (mem_attackers_of_mem reduction_in_args attack_reduction_to_no_adjustment))

/-- 中文证明（技术引理）：反证规则在"空采纳集＋空驳倒集"上不产出任何东西——
    本案无材料可产反证，故该步仍为空。陈述对任意策略成立，不是夹具专属。 -/
theorem rejectedStep_empty_empty (aaf : DungAAF) (pol : TerminalPolicy aaf) :
    rejectedStep pol (∅ : Finset Arg) ∅ = ∅ := by
  refine (Finset.eq_empty_iff_forall_notMem
    (s := rejectedStep pol (∅ : Finset Arg) ∅)).mpr ?_
  intro a ha
  rcases Finset.mem_union.mp ha with h0 | h1
  · exact notMemEmptyFinset a h0
  · obtain ⟨_, hne⟩ := Finset.mem_filter.mp h1
    have hfilter : (DungAAF.attackers aaf a).filter (fun b => b ∈ (∅ : Finset Arg)) = ∅ := by
      refine (Finset.eq_empty_iff_forall_notMem
        (s := (DungAAF.attackers aaf a).filter (fun b => b ∈ (∅ : Finset Arg)))).mpr ?_
      intro b hb
      exact notMemEmptyFinset b (Finset.mem_filter.mp hb).2
    exact hne hfilter

/-- 中文证明（技术引理）：第 0 层采纳集为空——四族材料（明文／推定／妨碍／反证）全空，
    `baseSet` 的谓词两支都假。 -/
theorem conflict_baseSet_empty : baseSet conflictPolicy = ∅ := by
  refine (Finset.eq_empty_iff_forall_notMem (s := baseSet conflictPolicy)).mpr ?_
  intro a ha
  obtain ⟨_, _, hcond⟩ := Finset.mem_filter.mp ha
  cases hcond with
  | inl hc => exact notMemEmptyFinset a hc
  | inr hp => exact notMemEmptyFinset a hp.1

/-- 中文证明（技术引理·**不变式**）：互斥夹具下每一层的采纳集与驳倒集**都为空**。
    第 0 层由 `conflict_baseSet_empty`（材料全空）；归纳步由两支各自堵死：
    `adoptedStep` 那支因"每个论点都有攻击者而驳倒集为空"失败
    （`conflict_arg_has_attacker`），`rejectedStep` 那支因无材料可产反证失败。 -/
theorem conflict_rounds_empty :
    ∀ k : Nat, (rounds conflictPolicy k).1 = ∅ ∧ (rounds conflictPolicy k).2 = ∅ := by
  intro k
  induction k with
  | zero =>
      refine ⟨?_, rounds_zero_snd conflictPolicy⟩
      rw [rounds_zero_fst]
      exact conflict_baseSet_empty
  | succ n ih =>
      obtain ⟨h1, h2⟩ := ih
      refine ⟨?_, ?_⟩
      · rw [rounds_succ_fst, h1, h2, rejectedStep_empty_empty]
        refine (Finset.eq_empty_iff_forall_notMem
          (s := adoptedStep conflictPolicy (∅ : Finset Arg) ∅)).mpr ?_
        intro a ha
        rcases Finset.mem_union.mp ha with h0 | h1'
        · exact notMemEmptyFinset a h0
        · obtain ⟨hargs, hcond⟩ := Finset.mem_filter.mp h1'
          exact conflict_arg_has_attacker a hargs hcond.2.2.1
      · rw [rounds_succ_snd, h1, h2, rejectedStep_empty_empty]

/-- 中文证明（**义务闭合·第 2 条**）：互斥夹具下每一层采纳集都不含酌减请求。
    原为 `def conflict_never_adopted_obligation : Prop` 挂账项，陈述一字未改，改为 `theorem`。
    由不变式 `conflict_rounds_empty` 直接读出（该层采纳集恒为 `∅`）。 -/
theorem conflict_never_adopted_obligation :
    ∀ k : Nat, encode ClauseAtom.reductionClaim ∉ (rounds conflictPolicy k).1 := by
  intro k
  obtain ⟨h1, _⟩ := conflict_rounds_empty k
  rw [h1]
  exact notMemEmptyFinset _

/-- 中文证明（**义务闭合·第 3 条**）：酌减请求 `¬ FinalDerivable`。
    原为 `def conflict_not_final_derivable_obligation : Prop` 挂账项，陈述一字未改，改为 `theorem`。
    `FinalDerivable` 就是 `∃ k, · ∈ (rounds · k).1`，故本条是第 2 条的直接推论，
    **不含**新的数学想法（与原登记的依赖关系一致）。 -/
theorem conflict_not_final_derivable_obligation :
    ¬ FinalDerivable conflictPolicy (encode ClauseAtom.reductionClaim) := by
  rintro ⟨k, hk⟩
  exact conflict_never_adopted_obligation k hk

/-- 中文证明（**见证的非空洞性检查**）：该请求在 L2 的可采纳支持位上**读出的就是真**
    （`conflictPolicy.admissibleSupport` 即 `admissibleFromHorn claimCase encode`，
    由 `Preservation` 的 `horn_derived_is_admissible` 给出）。
    ⇒ 上一条的"永不可支持"**不是**因为支持性缺失、也不是因为论点集空（`reduction_in_args`
    已证论点集有人住），而**只**因"攻击者未被驳回"这一支被互斥环堵死。
    这条检查是必要的：没有它，`¬ FinalDerivable` 可以靠空载体空洞成立。 -/
theorem reduction_claim_support_is_true :
    conflictPolicy.admissibleSupport (encode ClauseAtom.reductionClaim) = true :=
  horn_derived_is_admissible claimCase encode ClauseAtom.reductionClaim
    reduction_claim_derived_obligation

/-- 中文说明：**本件闭合面与未闭合面的分界**（一条可复读的自述，随义务闭合改写）。
    已证：`Preservation` 一节五件（L1 闭包与 L2 论点域／支持位／攻击边的四项对应，
    外加"例外不能打断未推出的请求"）；`policyClosed_obligation_for`（T2 的 `policyClosed`
    一栏有被证明成立的实例）；本节三条义务——L1 成立、L2 每层不采纳、因而 `¬ FinalDerivable`。
    ⇒ "这一跳不可合并"现在有**机器证据**：同一结论可以 L1 成立而 L2 永不可支持，
      两层不是同一对象上的同一性质。
    仍未闭合（不得计入统一性）：T2 另两条前提 `baseInGrounded`（`AdjudicationBridge.lean:514`）
    与 `collapsesToKernel`（`:846`）。第64条第3款"不予支持"的**驳回**表达已在 §五 给出
    （`art64_no_adjustment_defeated`，并把旧状态留在 `conflict_no_adjustment_final_undetermined`
    作对照）；那是**建模选择**：本机唯一能产出 `FinalDefeated` 的入口是反证栏。 -/
theorem transitions_boundary_is_recorded :
    (∃ p q : Prop, p = (ClauseAtom.reductionClaim ∈ SourceNorms.closureAt claimCase) ∧
      q = ¬ FinalDerivable conflictPolicy (encode ClauseAtom.reductionClaim)) :=
  ⟨_, _, rfl, rfl⟩

/-! ## 五、第 64 条第 3 款"不予支持"的**驳回**表达（补 §三 登记的那一格） -/

section ArtSixtyFourClauseThree

/-- 中文说明（**建模选择**，不是对条文效果的认定）：法释〔2023〕13号第 64 条第 3 款实定
    "仅以合同约定不得调整为由主张不予调整的，人民法院不予支持"。本件把该款编成
    **一条已产出的反证材料**：酌减请求一侧（法定调整权）进 `contraryEvidence` 栏，
    其余四栏与 `conflictPolicy` 相同（明文／推定／妨碍全空）。
    为什么只有这一条路（§三 先前写作"放进 `obstructed`、或让请求进 `conclusive`"，
    **那是错的**）：本机的驳倒集只有一个生成口——`AdjudicationBridge.lean:153` 的
    `rejectedStep` 只把"攻击者落在 `contraryEvidence` 里"的论点收进来；
    `obstructed` 与 `conclusive` 两支都只作用于 `baseSet`（`:143`），
    最多让某主张**不被采纳**，永远产不出 `FinalDefeated`。
    ⇒ 这是签名级事实而非取舍；法律读法：该款不是"抗辩不成立"，而是"该抗辩被明文打回"。 -/
def art64Policy : TerminalPolicy conflictAAF where
  admissibleSupport := admissibleFromHorn claimCase encode
  conclusive := ∅
  presumed := ∅
  obstructed := ∅
  contraryEvidence := {encode ClauseAtom.reductionClaim}

/-- 中文证明：反证栏里确实是酌减请求那一侧的论点（单元素字面集的成员判定）。 -/
theorem art64_contrary_evidence_is_the_reduction_claim :
    encode ClauseAtom.reductionClaim ∈ art64Policy.contraryEvidence :=
  show encode ClauseAtom.reductionClaim ∈ ({encode ClauseAtom.reductionClaim} : Finset Arg)
    from Finset.mem_singleton.mpr rfl

/-- 中文证明：第 0 层采纳集仍为空——该款**不**改变"本案无一条明文规则直接指定采纳谁"，
    它改变的是驳倒集。 -/
theorem art64_baseSet_empty : baseSet art64Policy = ∅ := by
  refine (Finset.eq_empty_iff_forall_notMem (s := baseSet art64Policy)).mpr ?_
  intro a ha
  obtain ⟨_, _, hcond⟩ := Finset.mem_filter.mp ha
  cases hcond with
  | inl hc => exact notMemEmptyFinset a hc
  | inr hp => exact notMemEmptyFinset a hp.1

/-- 中文证明（技术引理）：被驳回那一侧的论点**确实**有一个落在反证栏里的攻击者，
    所以 `rejectedStep` 的筛子对它非空。陈述写成自己的表达式，不做 `unfold`——
    展开后交给 `mem_filter` 反推谓词会让 `pol` 这个 metavar 漂到别的策略上
    （run 37137401300 的第一处红就是这么来的）。 -/
theorem art64_no_adjustment_has_a_contrary_attacker :
    (DungAAF.attackers conflictAAF (encode ClauseAtom.noAdjustment))
      .filter (fun b => b ∈ art64Policy.contraryEvidence) ≠ ∅ := by
  intro heq
  refine notMemEmptyFinset _ ?_
  rw [← heq]
  exact Finset.mem_filter.mpr
    ⟨mem_attackers_of_mem reduction_in_args attack_reduction_to_no_adjustment,
      art64_contrary_evidence_is_the_reduction_claim⟩

/-- 中文证明（技术引理）：反证一步**确实**把"不予调整"主张收进驳倒集。
    链条：酌减请求在论点集里（`reduction_in_args`）且它攻击"不予调整"
    （`attack_reduction_to_no_adjustment`），而它又在反证栏里 ⇒ 该攻击者筛后非空。 -/
theorem art64_rejected_step_defeats_no_adjustment :
    encode ClauseAtom.noAdjustment ∈ rejectedStep art64Policy (∅ : Finset Arg) ∅ :=
  Finset.mem_union.mpr (Or.inr
    (Finset.mem_filter.mpr ⟨no_adjustment_in_args,
      art64_no_adjustment_has_a_contrary_attacker⟩))

/-- 中文证明（**G3 那一格闭合**）：第 64 条第 3 款在模型里是**驳回**
    （`FinalDefeated`），不只是"未被采纳"（`¬ FinalDerivable`）。
    层号取 1：第 0 层采纳集空（`art64_baseSet_empty`）、驳倒集空（`rounds_zero_snd`），
    第 1 层驳倒集就是上一条的反证一步。 -/
theorem art64_no_adjustment_defeated :
    FinalDefeated art64Policy (encode ClauseAtom.noAdjustment) := by
  refine ⟨1, ?_⟩
  rw [rounds_succ_snd, rounds_zero_fst, art64_baseSet_empty, rounds_zero_snd]
  exact art64_rejected_step_defeats_no_adjustment

/-- 中文证明（对照面）：**不加**反证栏时，同一互斥夹具下"不予调整"主张是**未决**——
    既未被采纳也未被驳倒（`conflict_rounds_empty` 给出两支恒空）。
    这正是 §三 登记的旧状态，本件不把它说成本条文的读法。 -/
theorem conflict_no_adjustment_final_undetermined :
    finalUndetermined conflictPolicy (encode ClauseAtom.noAdjustment) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨k, hk⟩
    obtain ⟨h1, _⟩ := conflict_rounds_empty k
    rw [h1] at hk
    exact notMemEmptyFinset _ hk
  · rintro ⟨k, hk⟩
    obtain ⟨_, h2⟩ := conflict_rounds_empty k
    rw [h2] at hk
    exact notMemEmptyFinset _ hk

/-- 中文证明（**§五 是加内容而不是换写法**）：同一主张在两个策略下读数不同——
    加反证栏者被驳回，不加者不被驳回。与上一条合起来，"驳回"相对"未决"多出的那一格
    有机器见证，不靠措辞。 -/
theorem art64_rejection_is_extra_content :
    FinalDefeated art64Policy (encode ClauseAtom.noAdjustment) ∧
      ¬ FinalDefeated conflictPolicy (encode ClauseAtom.noAdjustment) := by
  refine ⟨art64_no_adjustment_defeated, ?_⟩
  rintro ⟨k, hk⟩
  obtain ⟨_, h2⟩ := conflict_rounds_empty k
  rw [h2] at hk
  exact notMemEmptyFinset _ hk

end ArtSixtyFourClauseThree
