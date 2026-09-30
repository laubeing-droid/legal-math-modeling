import JurisLean.KernelV3
import JurisLean.DungFixedPoint
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic

/-!
P-051 / S2 —— 裁判缝合件：接地语义与"依法可支持"的接缝（心证边界的数学部分）。

## 一、法律语义（人话）
裁判者说一个论点"依法可支持"，与论证理论说它"在接地语义下被接受"，是两件不同的事：

- Dung 接地语义 `DungAAF.grounded` 只看防御结构：论点的每个攻击者是否被当前可接受集驳倒，
  取可接受性算子 `F` 的**最小不动点**。它不问法律有无明文规定、有无举证责任、有无推定。
- 依法可支持 `FinalDerivable` 问：本案**宣告的终端规则**能否把该论点推出来。明文终局采纳
  （生效裁判确认的事实、当事人自认）能让 Dung 层面"未决"的论点变成可支持；举证责任规则
  让论点因缺乏可采纳支持而不被推出，却不等于该论点事实上为假。

本件把两条线接起来而**不做同义替换**：`FinalDerivable` 由本件自写的四条规则生成，其算子带
`obstructed`（妨碍规则排除）、`admissibleSupport`（可采纳支持）、`contraryEvidence`（已产出反证）
以及"新采纳不得攻击已采纳"这三项 `F` 里没有的法律材料，故不是 `F` 的别名。
桥接定理 `grounded_support_correspondence` 只在显式宣告的片段 `policyClosed`（某层采纳集对 `F` 封闭）
下成立，方向是 `a ∈ grounded → FinalDerivable`；逆向另需独立片段 `baseInGrounded`，
两者合用才有等价式 `grounded_equivalence`。

## 二、数学对象
- `RuleFamily`：四族终端规则之名，与 `KernelV3.Exhaustion` 的四字段一一对应
  （`burdenRulesExhausted`、`presumptionRulesExhausted`、`obstructionRulesExhausted`、
  `terminalRulesExhausted`，KernelV3.lean:286-290）。
- `TerminalPolicy aaf`：终端策略 = 可采纳支持谓词 + 终局/推定/妨碍三组规则集 + 已产出反证集。
- `rounds pol n`：第 n 层的（已采纳集, 已驳倒集），由 `baseSet`（终局规则与未被反证推翻的推定规则）、
  `adoptedStep`（举证责任规则）、`rejectedStep`（反证产出即驳倒）逐层生成。
- `FinalDerivable`／`FinalDefeated`／`finalUndetermined`：某层被采纳／某层被驳倒／两者皆无。
- `EvalDomain V`（末节）：法律评价域 = 三组规则判据（何谓可采纳支持、何谓达到证明标准、
  何谓对反驳封闭）；`stableKernel`＝对一切可采纳评价的交，`allowedSet`＝对一切可采纳评价的并。

## 三、本件证什么、不证什么
证：①`two_valued_exclusion`（对层号的结构归纳；同一论点不能既被最终采纳又被最终驳倒）；
②`final_undetermined_iff_exhausted`（⇔ 四族规则穷尽，片段形式，见下）；
③`argument_undec_not_final_undetermined`（构造性见证：偶环上 Dung 判未决的论点，在终端策略下
一个被采纳、一个被驳倒，故都不是本件意义下的未决）；④`proof_failure_not_ontic_negation`
（由仓库定理 `KernelV3.judgment_notEstablished_does_not_force_truth_false` 派生，不重证）；
⑤`grounded_support_correspondence`（条件桥，坐实在 `grounded_is_least_fixed_point` 上）与
`grounded_rejection_is_not_legal_refutation`（接地失败不是法律否定，用 `labelling_partition`）；
⑥评价域一侧 `stable_kernel_singleton_of_allowed_singleton`、条件等价式
`unique_verdict_iff_stable_kernel_singletons` 与非退化边界见证 `trial_boundary`。

不证 / 片段限制（必须读）：
- `KernelV3.Exhaustion` 的四字段在仓库里是**无内容的 `Prop`**，仓库没有任何定理规定其含义。
  所以 (c) 只能相对于本件**宣告的读法** `exhaustionOf`（第 i 族穷尽＝该族规则对本论点不再发动）
  成立，这是**片段形式的 (c)**，不是仓库自身蕴含的等价式；换读法就得重证。
- `two_valued_exclusion` 需 `baseConflictFree`：终局与推定规则在第 0 层采纳的论点之间不得互相
  直接攻击（举证责任规则本身带"不得攻击已采纳论点"的条件，故只需这一条基底假设）。
  真实法秩序中推定相互冲突时本定理**不适用**（不是被反驳）。
- 桥的正向需 `policyClosed`，逆向需 `baseInGrounded`；两个都是外加片段，不是从 Dung 语义推出的。
- 本件**不**在 `FinalDerivable` 与 `KernelV3.Judgment`／`EvalResult` 之间建双向字典：
  不定义 `Judgment`、不对 `Judgment` 模式匹配、不用"判断=成立"来定义可支持性（硬红线）。
- 本件**不**证明评价域构造与 `rounds` 之间的任何关系（两套对象在本件内平行）；
  **不**认定任何真实条文、任何真实案件的心证边界（条文号见末节 `[代拟稿]`）。
- 未覆盖片段：`KernelV3.NarrowResult` 与 `finalUndetermined` 的接口；`Exhaustion` 四字段法律内容；
  "唯一判决"反向不等的完整刻画（本件只给一个反例 `trial_collapse_fails`）。

## 四、档位
定义与定理均在本件内闭合；`decide` 只用于显式有限见证的具体计算。编译认定待 CI，本地不称 PASS。
-/

namespace JurisLean.Seams.AdjudicationBridge

/-- 中文证明：空 `Finset` 不含元素（本件局部小引理，避开 Mathlib 名字漂移）。 -/
theorem notMemEmptyFinset {α : Type} [DecidableEq α] (a : α) : ¬ (a ∈ (∅ : Finset α)) :=
  (Finset.eq_empty_iff_forall_notMem (s := ∅)).mp rfl a

/-- 中文说明：四族终端规则的名字，与 `KernelV3.Exhaustion` 的四个字段一一对应。 -/
inductive RuleFamily : Type
  | burden | presumption | obstruction | terminal
deriving DecidableEq, Repr

/-- 中文说明：终端策略 = 本案四族规则的材料。`admissibleSupport` 是举证责任规则要求的"可采纳支持"；
`conclusive` 是终局规则明文采纳的论点；`presumed` 是推定规则默认采纳的论点；
`obstructed` 是妨碍规则排除的论点；`contraryEvidence` 是本案已产出的反证论点（可推翻推定）。
本件不声称这四族穷尽真实法律的全部终端规则，只声明本件使用的片段。 -/
structure TerminalPolicy (aaf : DungAAF) where
  admissibleSupport : Arg → Prop
  conclusive : Finset Arg
  presumed : Finset Arg
  obstructed : Finset Arg
  contraryEvidence : Finset Arg

variable (aaf : DungAAF)

/-- 中文说明：第 0 层采纳集。终局规则明文采纳，或推定规则采纳且没有产出反证攻击它；
被妨碍规则排除的论点两者都进不来。 -/
def baseSet (pol : TerminalPolicy aaf) : Finset Arg :=
  aaf.args.filter fun a =>
    a ∉ pol.obstructed ∧
      (a ∈ pol.conclusive ∨
        (a ∈ pol.presumed ∧
          (DungAAF.attackers aaf a).filter (fun b => b ∈ pol.contraryEvidence) = ∅))

/-- 中文说明：反证规则一步——被上一层采纳集攻击到的论点即被驳倒（累加）。 -/
def rejectedStep (pol : TerminalPolicy aaf) (inN outN : Finset Arg) : Finset Arg :=
  outN ∪ aaf.args.filter (fun a => (DungAAF.attackers aaf a).filter (fun b => b ∈ inN) ≠ ∅)

/-- 中文说明：举证责任规则一步。四个条件：不被妨碍规则排除；有可采纳支持；全部攻击者都已被驳回；
新采纳的论点不得攻击上一层已采纳的论点（禁止自相矛盾的认定）。后两项加第一项都是 `F`
里没有的法律材料，故本算子不是 `F` 的别名。 -/
def adoptedStep (pol : TerminalPolicy aaf) (inN outN : Finset Arg) : Finset Arg :=
  inN ∪ aaf.args.filter fun a =>
    a ∉ pol.obstructed ∧ pol.admissibleSupport a ∧ DungAAF.attackers aaf a ⊆ outN ∧
      ∀ a' : Arg, a' ∈ inN → (a, a') ∉ aaf.attacks

/-- 中文说明：终端策略的逐层推导 `rounds pol n = (第 n 层已采纳集, 第 n 层已驳倒集)`。 -/
def rounds (pol : TerminalPolicy aaf) : Nat → Finset Arg × Finset Arg
  | 0 => (baseSet pol, ∅)
  | n + 1 =>
      (adoptedStep pol (rounds pol n).1 (rejectedStep pol (rounds pol n).1 (rounds pol n).2),
        rejectedStep pol (rounds pol n).1 (rounds pol n).2)

/-- 中文证明：逐层定义的四条折叠/展开引理。 -/
theorem rounds_zero_fst (pol : TerminalPolicy aaf) : (rounds pol 0).1 = baseSet pol :=
  rfl

theorem rounds_zero_snd (pol : TerminalPolicy aaf) : (rounds pol 0).2 = ∅ :=
  rfl

theorem rounds_succ_fst (pol : TerminalPolicy aaf) (n : Nat) :
    (rounds pol (n + 1)).1 =
      adoptedStep pol (rounds pol n).1 (rejectedStep pol (rounds pol n).1 (rounds pol n).2) :=
  rfl

theorem rounds_succ_snd (pol : TerminalPolicy aaf) (n : Nat) :
    (rounds pol (n + 1)).2 = rejectedStep pol (rounds pol n).1 (rounds pol n).2 :=
  rfl

/-- 中文证明：`DungAAF.attackers` 与攻击关系的双向忠实（缝合件反复使用）。 -/
theorem mem_attackers {a b : Arg} (h : b ∈ DungAAF.attackers aaf a) : (b, a) ∈ aaf.attacks :=
  (Finset.mem_filter.mp h).2

theorem mem_attackers_of_mem (a : Arg) (ha : a ∈ aaf.args) {b : Arg} (hb : (b, a) ∈ aaf.attacks) :
    b ∈ DungAAF.attackers aaf a :=
  Finset.mem_filter.mpr ⟨ha, hb⟩

/-- 中文证明：第 0 层采纳集的成员刻画。 -/
theorem mem_baseSet_iff (pol : TerminalPolicy aaf) (a : Arg) :
    a ∈ baseSet pol ↔
      a ∈ aaf.args ∧ a ∉ pol.obstructed ∧
        (a ∈ pol.conclusive ∨
          (a ∈ pol.presumed ∧
            (DungAAF.attackers aaf a).filter (fun b => b ∈ pol.contraryEvidence) = ∅)) :=
  Finset.mem_filter

/-- 中文证明：逐层成员刻画（采纳侧／驳倒侧）。 -/
theorem mem_rounds_succ_fst_iff (pol : TerminalPolicy aaf) (n : Nat) (a : Arg) :
    a ∈ (rounds pol (n + 1)).1 ↔
      a ∈ (rounds pol n).1 ∨
        (a ∈ aaf.args ∧ a ∉ pol.obstructed ∧ pol.admissibleSupport a ∧
          DungAAF.attackers aaf a ⊆ (rounds pol (n + 1)).2 ∧
          ∀ a' : Arg, a' ∈ (rounds pol n).1 → (a, a') ∉ aaf.attacks) := by
  rw [rounds_succ_fst, adoptedStep, Finset.mem_union, Finset.mem_filter, ← rounds_succ_snd]

theorem mem_rounds_succ_snd_iff (pol : TerminalPolicy aaf) (n : Nat) (a : Arg) :
    a ∈ (rounds pol (n + 1)).2 ↔
      a ∈ (rounds pol n).2 ∨
        (a ∈ aaf.args ∧ (DungAAF.attackers aaf a).filter (fun b => b ∈ (rounds pol n).1) ≠ ∅) := by
  rw [rounds_succ_snd, rejectedStep, Finset.mem_union, Finset.mem_filter]

/-- 中文证明：两层集合都含于框架的论点集。 -/
theorem rounds_fst_subset_args (pol : TerminalPolicy aaf) :
    ∀ n : Nat, (rounds pol n).1 ⊆ aaf.args := by
  intro n
  induction n with
  | zero =>
      intro a ha
      rw [rounds_zero_fst, mem_baseSet_iff] at ha
      exact ha.1
  | succ n ih =>
      intro a ha
      rw [mem_rounds_succ_fst_iff] at ha
      rcases ha with (ha | ⟨har, _, _, _, _⟩)
      · exact ih a ha
      · exact har

theorem rounds_snd_subset_args (pol : TerminalPolicy aaf) :
    ∀ n : Nat, (rounds pol n).2 ⊆ aaf.args := by
  intro n
  induction n with
  | zero =>
      rw [rounds_zero_snd]
      exact fun _ hx => absurd hx (notMemEmptyFinset _)
  | succ n ih =>
      intro a ha
      rw [mem_rounds_succ_snd_iff] at ha
      rcases ha with (ha | ⟨har, _⟩)
      · exact ih a ha
      · exact har

/-- 中文证明：两层各自单调，并可累加任意多步（用于把两个层号放到同一层比较）。 -/
theorem rounds_fst_mono (pol : TerminalPolicy aaf) (n : Nat) :
    (rounds pol n).1 ⊆ (rounds pol (n + 1)).1 :=
  fun _ ha => (mem_rounds_succ_fst_iff pol n _).mpr (Or.inl ha)

theorem rounds_snd_mono (pol : TerminalPolicy aaf) (n : Nat) :
    (rounds pol n).2 ⊆ (rounds pol (n + 1)).2 :=
  fun _ ha => (mem_rounds_succ_snd_iff pol n _).mpr (Or.inl ha)

theorem rounds_fst_mono_add (pol : TerminalPolicy aaf) :
    ∀ n k : Nat, (rounds pol n).1 ⊆ (rounds pol (n + k)).1 := by
  intro n k
  induction k with
  | zero => exact fun _ ha => ha
  | succ k ih => exact fun a ha => rounds_fst_mono pol _ (ih a ha)

theorem rounds_snd_mono_add (pol : TerminalPolicy aaf) :
    ∀ n k : Nat, (rounds pol n).2 ⊆ (rounds pol (n + k)).2 := by
  intro n k
  induction k with
  | zero => exact fun _ ha => ha
  | succ k ih => exact fun a ha => rounds_snd_mono pol _ (ih a ha)

/-- 中文证明：同层被驳倒的论点必有一个同层被采纳的攻击者（不需要任何片段假设）。 -/
theorem rounds_snd_attacker (pol : TerminalPolicy aaf) :
    ∀ n : Nat, ∀ a : Arg, a ∈ (rounds pol n).2 →
      ∃ b : Arg, (b, a) ∈ aaf.attacks ∧ b ∈ (rounds pol n).1 := by
  intro n
  induction n with
  | zero =>
      intro a ha
      rw [rounds_zero_snd] at ha
      exact absurd ha (notMemEmptyFinset a)
  | succ n ih =>
      intro a ha
      rw [mem_rounds_succ_snd_iff] at ha
      rcases ha with (ha | ⟨_, hne⟩)
      · obtain ⟨b, hbAtt, hbIn⟩ := ih a ha
        exact ⟨b, hbAtt, rounds_fst_mono pol n hbIn⟩
      · obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr hne
        obtain ⟨hbF, hbIn⟩ := Finset.mem_filter.mp hb
        exact ⟨b, mem_attackers hbF, rounds_fst_mono pol n hbIn⟩

/-- 中文说明：基底无冲突片段——终局规则与推定规则在第 0 层采纳的论点之间不得互相直接攻击。
这是策略自洽性的最低要求；真实法秩序中推定相互冲突时本片段不适用。 -/
def baseConflictFree (pol : TerminalPolicy aaf) : Prop :=
  ∀ a a' : Arg, a ∈ baseSet pol → a' ∈ baseSet pol → (a, a') ∉ aaf.attacks

/-- 中文说明：第 n 层的两条安全不变量（采纳集与驳倒集不交；采纳集内部无攻击）。 -/
def roundsSafeAt (pol : TerminalPolicy aaf) (n : Nat) : Prop :=
  (rounds pol n).1 ∩ (rounds pol n).2 = ∅ ∧
    ∀ a a' : Arg, a ∈ (rounds pol n).1 → a' ∈ (rounds pol n).1 → (a, a') ∉ aaf.attacks

/-- 中文证明：两条安全不变量逐层保持（对层号归纳；契约 (b) 的结构内核）。
举证责任规则的"不得攻击已采纳论点"条件把冲突挡在门外，基底只需 `baseConflictFree`。 -/
theorem rounds_safe (pol : TerminalPolicy aaf) (hw : baseConflictFree pol) :
    ∀ n : Nat, roundsSafeAt pol n := by
  intro n
  induction n with
  | zero =>
      refine ⟨?_, ?_⟩
      · rw [rounds_zero_fst, rounds_zero_snd, Finset.inter_empty]
      · intro a a' ha ha'
        rw [rounds_zero_fst] at ha ha'
        exact hw a a' ha ha'
  | succ n ih =>
      obtain ⟨hdisjEq, hconf⟩ := ih
      rw [Finset.eq_empty_iff_forall_notMem] at hdisjEq
      -- (rounds n).1 与 (rounds (n+1)).2 不交
      have hIo : ∀ x : Arg, x ∉ (rounds pol n).1 ∩ (rounds pol (n + 1)).2 := by
        intro x hx
        obtain ⟨hxIn, hxOut⟩ := Finset.mem_inter.mp hx
        rw [mem_rounds_succ_snd_iff] at hxOut
        rcases hxOut with (hxOut | ⟨_, hne⟩)
        · exact hdisjEq x (Finset.mem_inter.mpr ⟨hxIn, hxOut⟩)
        · obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr hne
          obtain ⟨hbF, hbIn⟩ := Finset.mem_filter.mp hb
          exact hconf b x hbIn hxIn (mem_attackers hbF)
      -- 第一条：同层不交
      have h1 : ∀ x : Arg, x ∉ (rounds pol (n + 1)).1 ∩ (rounds pol (n + 1)).2 := by
        intro x hx
        obtain ⟨hxIn, hxOut⟩ := Finset.mem_inter.mp hx
        rw [mem_rounds_succ_fst_iff] at hxIn
        rcases hxIn with (hxIn | ⟨hxArgs, _, _, hxSub, _⟩)
        · rw [mem_rounds_succ_snd_iff] at hxOut
          rcases hxOut with (hxOut | ⟨_, hne⟩)
          · exact hdisjEq x (Finset.mem_inter.mpr ⟨hxIn, hxOut⟩)
          · obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr hne
            obtain ⟨hbF, hbIn⟩ := Finset.mem_filter.mp hb
            exact hIo b (Finset.mem_inter.mpr ⟨hbIn, hxSub hbF⟩)
        · rw [mem_rounds_succ_snd_iff] at hxOut
          rcases hxOut with (hxOut | ⟨_, hne⟩)
          · obtain ⟨b, hbAtt, hbIn⟩ := rounds_snd_attacker pol n x hxOut
            exact hIo b (Finset.mem_inter.mpr
              ⟨hbIn, hxSub (mem_attackers_of_mem x hxArgs hbAtt)⟩)
          · obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr hne
            obtain ⟨hbF, hbIn⟩ := Finset.mem_filter.mp hb
            exact hIo b (Finset.mem_inter.mpr ⟨hbIn, hxSub hbF⟩)
      -- 第二条：同层无冲突
      refine ⟨Finset.eq_empty_iff_forall_notMem.mpr h1, ?_⟩
      intro a a' ha ha' hatk
      rw [mem_rounds_succ_fst_iff] at ha ha'
      rcases ha with (ha | ⟨harA, hobsA, hAdm, hsubA, hnewA⟩)
      · rcases ha' with (ha' | ⟨har', _, _, hsub', _⟩)
        · exact hconf a a' ha ha' hatk
        · exact hIo a (Finset.mem_inter.mpr ⟨ha, hsub' (mem_attackers_of_mem a' har' hatk)⟩)
      · rcases ha' with (ha' | ⟨har', _, _, hsub', _⟩)
        · exact hnewA a' ha' hatk
        · exact h1 a (Finset.mem_inter.mpr
            ⟨(mem_rounds_succ_fst_iff pol n a).mpr (Or.inr ⟨harA, hobsA, hAdm, hsubA, hnewA⟩),
              hsub' (mem_attackers_of_mem a' har' hatk)⟩)

/-- 中文说明：依法可支持（终端规则意义下的最终可支持）。定义完全落在 `rounds` 上，
不引用 `KernelV3.Judgment`，也不是"判断=成立"的缩写。 -/
def FinalDerivable (pol : TerminalPolicy aaf) (a : Arg) : Prop :=
  ∃ n : Nat, a ∈ (rounds pol n).1

/-- 中文说明：终端规则意义下的最终被驳倒。 -/
def FinalDefeated (pol : TerminalPolicy aaf) (a : Arg) : Prop :=
  ∃ n : Nat, a ∈ (rounds pol n).2

/-- 中文说明：终端规则意义下的未决——既未被采纳也未被驳倒。与 Dung 的 UNDEC 分量无关，
见 `argument_undec_not_final_undetermined`。 -/
def finalUndetermined (pol : TerminalPolicy aaf) (a : Arg) : Prop :=
  ¬ FinalDerivable pol a ∧ ¬ FinalDefeated pol a

/-- 中文证明（契约 (b)）：两值互斥。把两个层号提到同一层，再用 `rounds_safe` 的同层不交性：
同一论点不可能既被终端规则最终采纳又被最终驳倒。唯一假设是基底无冲突片段。 -/
theorem two_valued_exclusion (pol : TerminalPolicy aaf) (hw : baseConflictFree pol) (a : Arg)
    (h1 : FinalDerivable pol a) (h2 : FinalDefeated pol a) : False := by
  obtain ⟨n, hn⟩ := h1
  obtain ⟨m, hm⟩ := h2
  have hdisj := (rounds_safe pol hw (n + m)).1
  rw [Finset.eq_empty_iff_forall_notMem] at hdisj
  have hn' : a ∈ (rounds pol (n + m)).1 := rounds_fst_mono_add pol n m hn
  have hm' : a ∈ (rounds pol (m + n)).2 := rounds_snd_mono_add pol m n hm
  rw [Nat.add_comm] at hm'
  exact hdisj a (Finset.mem_inter.mpr ⟨hn', hm'⟩)

/-- 中文说明：四族规则"对论点 a 发动"的本件读法。终局与推定规则在第 0 层直接发动；
举证责任规则只在把 a 新引入采纳集时发动；妨碍（反证）规则发动即 a 进入驳倒集。 -/
def terminalRuleFires (pol : TerminalPolicy aaf) (a : Arg) : Prop :=
  a ∈ aaf.args ∧ a ∉ pol.obstructed ∧ a ∈ pol.conclusive

def presumptionRuleFires (pol : TerminalPolicy aaf) (a : Arg) : Prop :=
  a ∈ aaf.args ∧ a ∉ pol.obstructed ∧ a ∈ pol.presumed ∧
    (DungAAF.attackers aaf a).filter (fun b => b ∈ pol.contraryEvidence) = ∅

def burdenRuleFires (pol : TerminalPolicy aaf) (a : Arg) : Prop :=
  ∃ n : Nat, a ∈ (rounds pol (n + 1)).1 ∧ a ∉ (rounds pol n).1

def obstructionRuleFires (pol : TerminalPolicy aaf) (a : Arg) : Prop :=
  ∃ n : Nat, a ∈ (rounds pol n).2

/-- 中文说明（契约 (c) 的片段声明）：把 `KernelV3.Exhaustion` 的四个字段**读成**四族规则不发动。
仓库里这四个字段是无内容的 `Prop`，故此读法是本件宣告的片段，不是仓库蕴含的事实。 -/
def exhaustionOf (pol : TerminalPolicy aaf) (a : Arg) : KernelV3.Exhaustion :=
  { burdenRulesExhausted := ¬ burdenRuleFires pol a
    presumptionRulesExhausted := ¬ presumptionRuleFires pol a
    obstructionRulesExhausted := ¬ obstructionRuleFires pol a
    terminalRulesExhausted := ¬ terminalRuleFires pol a }

/-- 中文证明：第 n 层被采纳 ⇒ 终局／推定／举证三族之一发动（对层号归纳；契约 (c) 的技术核）。 -/
theorem mem_rounds_fst_fires (pol : TerminalPolicy aaf) (a : Arg) :
    ∀ n : Nat, a ∈ (rounds pol n).1 →
      terminalRuleFires pol a ∨ presumptionRuleFires pol a ∨ burdenRuleFires pol a := by
  intro n
  induction n with
  | zero =>
      intro ha
      rw [rounds_zero_fst, mem_baseSet_iff] at ha
      rcases ha with ⟨har, hobs, hc⟩
      rcases hc with (hc | ⟨hpr, hce⟩)
      · exact Or.inl ⟨har, hobs, hc⟩
      · exact Or.inr (Or.inl ⟨har, hobs, hpr, hce⟩)
  | succ n ih =>
      intro ha
      rw [mem_rounds_succ_fst_iff] at ha
      rcases ha with (ha | ⟨har, hobs, hadm, hsub, hnew⟩)
      · exact ih ha
      · refine Or.inr (Or.inr ⟨n, ?_, ?_⟩)
        · rw [mem_rounds_succ_fst_iff]
          exact Or.inr ⟨har, hobs, hadm, hsub, hnew⟩
        · intro h
          exact ih h

/-- 中文证明（契约 (c)，片段形式）：终端规则意义下的未决 ↔ 宣告读法下的四类规则穷尽
（`KernelV3.FullyExhausted`）。两个方向都用到 `rounds` 的逐层结构，不是定义折叠。 -/
theorem final_undetermined_iff_exhausted (pol : TerminalPolicy aaf) (a : Arg) :
    finalUndetermined pol a ↔ KernelV3.FullyExhausted (exhaustionOf pol a) := by
  constructor
  · intro h
    obtain ⟨hnd, hno⟩ := h
    show (¬ burdenRuleFires pol a) ∧ (¬ presumptionRuleFires pol a) ∧
      (¬ obstructionRuleFires pol a) ∧ (¬ terminalRuleFires pol a)
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hb
      obtain ⟨n, hn1, _⟩ := hb
      exact hnd ⟨n + 1, hn1⟩
    · intro hp
      obtain ⟨har, hobs, hpr, hce⟩ := hp
      exact hnd ⟨0, (mem_baseSet_iff pol a).mpr ⟨har, hobs, Or.inr ⟨hpr, hce⟩⟩⟩
    · intro ho
      obtain ⟨n, hn⟩ := ho
      exact hno ⟨n, hn⟩
    · intro ht
      obtain ⟨har, hobs, hc⟩ := ht
      exact hnd ⟨0, (mem_baseSet_iff pol a).mpr ⟨har, hobs, Or.inl hc⟩⟩
  · intro h
    obtain ⟨hb, hpr, ho, ht⟩ := h
    refine ⟨?_, ?_⟩
    · intro hex
      obtain ⟨n, hn⟩ := hex
      rcases mem_rounds_fst_fires pol a n hn with (hfires | hfires | hfires)
      · exact ht hfires
      · exact hpr hfires
      · exact hb hfires
    · intro hex
      obtain ⟨n, hn⟩ := hex
      exact ho ⟨n, hn⟩

/-- 中文说明（契约 (f) 的片段声明）：第 n 层采纳集对 Dung 可接受性算子 `F` 封闭，
即该层采纳集本身已是 Dung 意义下的完备外延。 -/
def policyClosed (pol : TerminalPolicy aaf) (n : Nat) : Prop :=
  DungAAF.F aaf (rounds pol n).1 = (rounds pol n).1

/-- 中文证明（契约 (f)，条件桥）：在 `policyClosed` 片段下，接地集里的论点都被终端策略采纳。
桥坐实在仓库定理 `DungAAF.grounded_is_least_fixed_point`（最小不动点）上，而不是浮在旁边；
`FinalDerivable` 用的是本件的 `rounds`（含 `F` 没有的三项法律材料），故不是定义同义替换。 -/
theorem grounded_support_correspondence (pol : TerminalPolicy aaf) (n : Nat)
    (hclosed : policyClosed pol n) (a : Arg)
    (ha : a ∈ DungAAF.grounded aaf) : FinalDerivable pol a :=
  ⟨n, DungAAF.grounded_is_least_fixed_point aaf (rounds pol n).1 hclosed ha⟩

/-- 中文说明（逆向片段声明）：基底采纳集落在接地集内，即终局与推定规则不与 Dung 语义相左。 -/
def baseInGrounded (pol : TerminalPolicy aaf) : Prop :=
  baseSet pol ⊆ DungAAF.grounded aaf

/-- 中文证明（逆向的技术核）：`baseInGrounded` 片段下，每一层的采纳集都在接地集内、
每一层的驳倒集都有一个接地的攻击者。用仓库定理 `DungAAF.grounded_is_fixed_point`。 -/
theorem rounds_within_grounded (pol : TerminalPolicy aaf) (hb : baseInGrounded pol) :
    ∀ n : Nat, (∀ a : Arg, a ∈ (rounds pol n).1 → a ∈ DungAAF.grounded aaf) ∧
      (∀ b : Arg, b ∈ (rounds pol n).2 →
        (DungAAF.attackers aaf b).filter (fun c => c ∈ DungAAF.grounded aaf) ≠ ∅) := by
  intro n
  induction n with
  | zero =>
      refine ⟨fun a ha => hb ha, ?_⟩
      intro b hb
      rw [rounds_zero_snd] at hb
      exact absurd hb (notMemEmptyFinset b)
  | succ n ih =>
      obtain ⟨hin, hout⟩ := ih
      -- 先证同层驳倒集里都有接地的攻击者
      have h2 : ∀ b : Arg, b ∈ (rounds pol (n + 1)).2 →
          (DungAAF.attackers aaf b).filter (fun c => c ∈ DungAAF.grounded aaf) ≠ ∅ := by
        intro b hb
        rw [mem_rounds_succ_snd_iff] at hb
        rcases hb with (hb | ⟨_, hne⟩)
        · exact hout b hb
        · obtain ⟨c, hc⟩ := Finset.nonempty_iff_ne_empty.mpr hne
          obtain ⟨hcF, hcIn⟩ := Finset.mem_filter.mp hc
          exact Finset.nonempty_iff_ne_empty.mpr
            ⟨c, Finset.mem_filter.mpr ⟨hcF, hin c hcIn⟩⟩
      refine ⟨?_, h2⟩
      intro a ha
      rw [mem_rounds_succ_fst_iff] at ha
      rcases ha with (ha | ⟨har, _, _, hsub, _⟩)
      · exact hin a ha
      · have hfp := DungAAF.grounded_is_fixed_point aaf
        rw [← hfp, DungAAF.F, Finset.mem_filter]
        refine ⟨har, ?_⟩
        intro c hc
        exact h2 c (hsub hc)

/-- 中文证明（逆向，条件定理）：`baseInGrounded` 片段下，依法可支持蕴含接地成员。 -/
theorem finalDerivable_within_grounded (pol : TerminalPolicy aaf) (hb : baseInGrounded pol)
    (a : Arg) (h : FinalDerivable pol a) : a ∈ DungAAF.grounded aaf := by
  obtain ⟨n, hn⟩ := h
  exact (rounds_within_grounded pol hb n).1 a hn

/-- 中文证明（两侧合流，仍带两个片段）：`policyClosed` 与 `baseInGrounded` 同时成立时，
依法可支持与接地成员等价。缺任一片段两侧就不重合，见 `argument_undec_not_final_undetermined`。 -/
theorem grounded_equivalence (pol : TerminalPolicy aaf) (n : Nat)
    (hclosed : policyClosed pol n) (hb : baseInGrounded pol) (a : Arg) :
    FinalDerivable pol a ↔ a ∈ DungAAF.grounded aaf :=
  ⟨fun h => finalDerivable_within_grounded pol hb a h,
    fun h => grounded_support_correspondence pol n hclosed a h⟩

/-!
## 见证层：偶环与终端策略（契约 (d)、(e) 的构造性内容）
两个论点互相攻击：Dung 接地语义对偶环全体未决；终端策略让其中一个被明文终局采纳。 -/

/-- 中文说明：见证论点的字面名字（`Arg` 在仓库里是 `String`）。 -/
def pArg : Arg := "p"

def qArg : Arg := "q"

/-- 中文说明：见证框架 `cycle2`——偶环，两论点互攻。 -/
def cycle2 : DungAAF where
  args := {pArg, qArg}
  attacks := {(pArg, qArg), (qArg, pArg)}

/-- 中文说明：见证终端策略——`p` 由终局规则明文采纳（法律上如生效裁判确认的事实、当事人自认），
`q` 不受明文终局规则覆盖；两论点都有可采纳支持，都不被妨碍规则排除，未产出反证。 -/
def cycle2Policy : TerminalPolicy cycle2 where
  admissibleSupport := fun a => a = pArg ∨ a = qArg
  conclusive := {pArg}
  presumed := ∅
  obstructed := ∅
  contraryEvidence := ∅

/-- 中文证明：见证策略的字段展开与具体集算（全部是显式有限数据的判定）。 -/
theorem cycle2_admissible (a : Arg) :
    cycle2Policy.admissibleSupport a ↔ (a = pArg ∨ a = qArg) :=
  Iff.rfl

theorem cycle2_baseSet : baseSet cycle2Policy = ({pArg} : Finset Arg) := by
  decide

theorem cycle2_attackers_p : DungAAF.attackers cycle2 pArg = ({qArg} : Finset Arg) := by
  decide

theorem cycle2_attackers_q : DungAAF.attackers cycle2 qArg = ({pArg} : Finset Arg) := by
  decide

theorem cycle2_p_ne_q : ¬ (pArg = (qArg : Arg)) := by
  decide

theorem cycle2_attacks_pair_ne : (pArg, pArg) ∉ cycle2.attacks := by
  decide

/-- 中文证明：见证策略满足基底无冲突片段（片段假设在非退化实例上确实成立，不是空转）。 -/
theorem cycle2_baseConflictFree : baseConflictFree cycle2Policy := by
  intro a a' ha ha'
  rw [cycle2_baseSet, Finset.mem_singleton] at ha ha'
  subst ha
  subst ha'
  exact cycle2_attacks_pair_ne

/-- 中文证明：偶环的接地集为空（先算 `F ∅ = ∅`，再对迭代层归纳），故两论点都不在接地集内。 -/
theorem cycle2_F_empty : DungAAF.F cycle2 (∅ : Finset Arg) = ∅ := by
  decide

theorem cycle2_iter_eq_empty (n : Nat) :
    FiniteMonotoneSystem.iter (DungAAF.aafSystem cycle2) n = ∅ := by
  induction n with
  | zero => exact FiniteMonotoneSystem.iter_zero _
  | succ n ih =>
      rw [FiniteMonotoneSystem.iter_succ, ih]
      exact cycle2_F_empty

theorem cycle2_grounded_eq_empty : DungAAF.grounded cycle2 = ∅ :=
  cycle2_iter_eq_empty _

theorem cycle2_p_not_grounded : pArg ∉ DungAAF.grounded cycle2 := by
  intro h
  rw [cycle2_grounded_eq_empty] at h
  exact absurd h (notMemEmptyFinset _)

theorem cycle2_q_not_grounded : qArg ∉ DungAAF.grounded cycle2 := by
  intro h
  rw [cycle2_grounded_eq_empty] at h
  exact absurd h (notMemEmptyFinset _)

/-- 中文证明：见证策略的层不变量——采纳集始终含于 `{p}`，且 `p` 从不进入驳倒集。 -/
theorem cycle2_policy_invariant (n : Nat) :
    (rounds cycle2Policy n).1 ⊆ ({pArg} : Finset Arg) ∧
      pArg ∉ (rounds cycle2Policy n).2 := by
  induction n with
  | zero =>
      refine ⟨?_, ?_⟩
      · rw [rounds_zero_fst, cycle2_baseSet]
        exact fun _ hx => hx
      · rw [rounds_zero_snd]
        exact fun hx => absurd hx (notMemEmptyFinset _)
  | succ n ih =>
      have hOut : pArg ∉ (rounds cycle2Policy (n + 1)).2 := by
        intro h
        rw [mem_rounds_succ_snd_iff] at h
        rcases h with (h | ⟨_, hne⟩)
        · exact ih.2 h
        · obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr hne
          obtain ⟨hbF, hbIn⟩ := Finset.mem_filter.mp hb
          have hbq : b = qArg :=
            Finset.mem_singleton.mp (by rw [← cycle2_attackers_p]; exact hbF)
          have hbp : b = pArg := Finset.mem_singleton.mp (ih.1 hbIn)
          exact cycle2_p_ne_q (hbq.trans hbp.symm)
      refine ⟨?_, hOut⟩
      intro a ha
      rw [mem_rounds_succ_fst_iff] at ha
      rcases ha with (ha | ⟨_, _, hadm, hsub, _⟩)
      · exact ih.1 ha
      · rw [cycle2_admissible] at hadm
        rcases hadm with (rfl | rfl)
        · exact Finset.mem_singleton_self _
        · exact False.elim (hOut (hsub (by rw [cycle2_attackers_q];
            exact Finset.mem_singleton_self _)))

/-- 中文证明：`p` 被终端策略采纳（终局规则在第 0 层发动），`q` 被终端策略驳倒
（`p` 被采纳后反证规则在第 1 层发动），`q` 永不被采纳。 -/
theorem cycle2_finalDerivable_p : FinalDerivable cycle2Policy pArg :=
  ⟨0, by rw [rounds_zero_fst, cycle2_baseSet]; exact Finset.mem_singleton_self _⟩

theorem cycle2_finalDefeated_q : FinalDefeated cycle2Policy qArg := by
  refine ⟨1, ?_⟩
  have h : (rounds cycle2Policy 1).2 = ({qArg} : Finset Arg) := by decide
  rw [h]
  exact Finset.mem_singleton_self _

theorem cycle2_not_finalDerivable_q : ¬ FinalDerivable cycle2Policy qArg := by
  intro h
  obtain ⟨n, hn⟩ := h
  have hsub : qArg ∈ ({pArg} : Finset Arg) := (cycle2_policy_invariant n).1 hn
  exact cycle2_p_ne_q (Finset.mem_singleton.mp hsub).symm

/-- 中文证明：Dung 层面 `p` 与 `q` 都在 UNDEC 分量（用仓库定理 `undecided_characterization`）。 -/
theorem cycle2_p_undecided : pArg ∈ (DungAAF.labelling cycle2).2.2 :=
  (DungAAF.undecided_characterization cycle2 pArg (by decide)).mpr
    ⟨cycle2_p_not_grounded, by rw [cycle2_grounded_eq_empty]; decide⟩

theorem cycle2_q_undecided : qArg ∈ (DungAAF.labelling cycle2).2.2 :=
  (DungAAF.undecided_characterization cycle2 qArg (by decide)).mpr
    ⟨cycle2_q_not_grounded, by rw [cycle2_grounded_eq_empty]; decide⟩

/-- 中文证明（契约 (d)）：Dung 的 undecided 与本件的 finalUndetermined 不是同一概念。
构造性见证：同一框架同一层，Dung 判未决的 `p` 被终端策略采纳、`q` 被终端策略驳倒，
两者都不是本件意义下的未决；`q` 确实不可支持而 `p` 确实可支持，故非空洞。 -/
theorem argument_undec_not_final_undetermined :
    pArg ∈ (DungAAF.labelling cycle2).2.2 ∧ FinalDerivable cycle2Policy pArg ∧
      ¬ finalUndetermined cycle2Policy pArg ∧
      qArg ∈ (DungAAF.labelling cycle2).2.2 ∧ FinalDefeated cycle2Policy qArg ∧
        ¬ finalUndetermined cycle2Policy qArg ∧ ¬ FinalDerivable cycle2Policy qArg :=
  ⟨cycle2_p_undecided, cycle2_finalDerivable_p,
    fun h => h.1 cycle2_finalDerivable_p,
    cycle2_q_undecided, cycle2_finalDefeated_q,
    fun h => h.2 cycle2_finalDefeated_q, cycle2_not_finalDerivable_q⟩

/-- 中文证明（契约 (f) 的失败方向）：`p` 不在接地集内，但既没有被终端策略驳倒，
也不在 Dung 自己的 OUT 分量里（用仓库定理 `labelling_partition` 的分量互斥）。
故"接地失败"在法律语义上不构成否定——它与 (d)(e) 一起封住"不可支持即为假"的滑坡。 -/
theorem grounded_rejection_is_not_legal_refutation :
    pArg ∉ DungAAF.grounded cycle2 ∧ ¬ FinalDefeated cycle2Policy pArg ∧
      pArg ∉ (DungAAF.labelling cycle2).2.1 := by
  refine ⟨cycle2_p_not_grounded, ?_, ?_⟩
  · intro h
    exact two_valued_exclusion cycle2Policy cycle2_baseConflictFree pArg
      cycle2_finalDerivable_p h
  · intro h
    have hpart := (DungAAF.labelling_partition cycle2).2.2.1
    have hmem : pArg ∈ (DungAAF.labelling cycle2).2.1 ∩ (DungAAF.labelling cycle2).2.2 :=
      Finset.mem_inter.mpr ⟨h, cycle2_p_undecided⟩
    rw [hpart] at hmem
    exact absurd hmem (notMemEmptyFinset _)

/-- 中文证明（契约 (e)）：求值失败不是本体否定。仓库定理
`KernelV3.judgment_notEstablished_does_not_force_truth_false`（KernelV3.lean:81-92）给出
"真值为真而判断不成立"的记录；本件把该记录与见证策略下的"最终不可支持且已被驳倒"合流，
得到：存在对象，其真值侧为正、判断侧为不成立、而终端策略下不可支持。
本件不重证该仓库定理，只使用它——结论是它的推论，不是它的复制。 -/
theorem proof_failure_not_ontic_negation :
    ∃ (x : KernelV3.TruthJudgment) (a : Arg),
      x.truth = true ∧ x.judgment = KernelV3.Judgment.notEstablished ∧
        ¬ FinalDerivable cycle2Policy a ∧ FinalDefeated cycle2Policy a := by
  obtain ⟨x, hx, hj⟩ := KernelV3.judgment_notEstablished_does_not_force_truth_false
  exact ⟨x, qArg, hx, hj, cycle2_not_finalDerivable_q, cycle2_finalDefeated_q⟩

/-!
## P-051 心证边界（数学部分）

`[代拟稿]` 法定锚（证据裁判主义、证明标准、非法证据排除对自由心证的限定条文号由主会话补入；
本件不臆造条文编号）。法律命题：唯一判决（允许评价集为单点）严格强于"存在允许评价"；
稳定内核为单点只保证一切可采纳心证有公共结论，不保证它们只会有一个结论。 -/

/-- 中文说明：法律评价域。对同一问题的候选结论集 `Set V` 给出三组规则判据：
何谓可采纳支持、何谓达到证明标准、何谓对反驳封闭。 -/
structure EvalDomain (V : Type) where
  admissibleSupport : Set V → Prop
  sufficientStandard : Set V → Prop
  rebuttalClosed : Set V → Prop

/-- 中文说明：三组规则同时满足的评价称为可采纳评价。 -/
def Admissible {V : Type} (E : EvalDomain V) (S : Set V) : Prop :=
  E.admissibleSupport S ∧ E.sufficientStandard S ∧ E.rebuttalClosed S

/-- 中文说明：稳定内核＝对一切可采纳评价的交（所有可采纳心证都不会放弃的结论）。 -/
def stableKernel {V : Type} (E : EvalDomain V) : Set V :=
  { v : V | ∀ S : Set V, Admissible E S → v ∈ S }

/-- 中文说明：允许评价集＝对一切可采纳评价的并（至少一个可采纳心证给出的结论）。 -/
def allowedSet {V : Type} (E : EvalDomain V) : Set V :=
  { v : V | ∃ S : Set V, Admissible E S ∧ v ∈ S }

/-- 中文证明：交／并语义的成员刻画。 -/
theorem mem_stableKernel_iff {V : Type} (E : EvalDomain V) (v : V) :
    v ∈ stableKernel E ↔ ∀ S : Set V, Admissible E S → v ∈ S :=
  Iff.rfl

theorem mem_allowedSet_iff {V : Type} (E : EvalDomain V) (v : V) :
    v ∈ allowedSet E ↔ ∃ S : Set V, Admissible E S ∧ v ∈ S :=
  Iff.rfl

/-- 中文证明：内核含于每个可采纳评价；每个可采纳评价含于允许集。 -/
theorem stableKernel_subset {V : Type} (E : EvalDomain V) (S : Set V) (hS : Admissible E S) :
    stableKernel E ⊆ S :=
  fun _ hv => hv S hS

theorem subset_allowedSet {V : Type} (E : EvalDomain V) (S : Set V) (hS : Admissible E S) :
    S ⊆ allowedSet E :=
  fun _ hv => ⟨S, hS, hv⟩

/-- 中文证明：内核含于允许集需要"存在可采纳评价"，否则交为全集、并为空集。 -/
theorem stableKernel_subset_allowedSet {V : Type} (E : EvalDomain V)
    (hNE : ∃ S : Set V, Admissible E S) : stableKernel E ⊆ allowedSet E := by
  obtain ⟨S, hS⟩ := hNE
  exact Set.Subset.trans (stableKernel_subset E S hS) (subset_allowedSet E S hS)

/-- 中文证明（契约 (g) 的正方向）：允许评价集为单点 ⇒ 稳定内核同为该单点。
需要的假设是每个可采纳评价都非空白——法律上即禁止不作结论的心证。 -/
theorem stable_kernel_singleton_of_allowed_singleton {V : Type} (E : EvalDomain V) (v : V)
    (hNE : ∃ S : Set V, Admissible E S)
    (hnoBlank : ∀ S : Set V, Admissible E S → ∃ x : V, x ∈ S)
    (hv : allowedSet E = {v}) : stableKernel E = {v} := by
  obtain ⟨S₀, hS₀⟩ := hNE
  have h1 : stableKernel E ⊆ ({v} : Set V) :=
    Set.Subset.trans (stableKernel_subset E S₀ hS₀)
      (Set.Subset.trans (subset_allowedSet E S₀ hS₀)
        (by rw [hv]; exact fun _ hx => hx))
  refine Set.Subset.antisymm h1 ?_
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  intro S hS
  obtain ⟨y, hy⟩ := hnoBlank S hS
  have hy' : y ∈ allowedSet E := subset_allowedSet E S hS hy
  rw [hv, Set.mem_singleton_iff] at hy'
  subst hy'
  exact hy

/-- 中文说明（反向所需片段声明）：收缩性——每个可采纳评价都不超出稳定内核。 -/
def collapsesToKernel {V : Type} (E : EvalDomain V) : Prop :=
  ∀ S : Set V, Admissible E S → S ⊆ stableKernel E

/-- 中文证明（契约 (g)，条件等价式）：在"存在可采纳评价 + 评价收缩到内核"片段下，
唯一判决 ↔ 稳定内核为单点。缺该片段时反向不成立，见 `trial_boundary` 与 `trial_collapse_fails`。 -/
theorem unique_verdict_iff_stable_kernel_singletons {V : Type} (E : EvalDomain V) (v : V)
    (hNE : ∃ S : Set V, Admissible E S) (hcoll : collapsesToKernel E) :
    (allowedSet E = {v}) ↔ (stableKernel E = {v}) := by
  constructor
  · intro hv
    obtain ⟨S₀, hS₀⟩ := hNE
    have hv' : v ∈ allowedSet E := by
      rw [hv]
      exact Set.mem_singleton v
    obtain ⟨T, hT, hvT⟩ := hv'
    refine Set.Subset.antisymm ?_ (fun _ hx => (hcoll T hT) hvT)
    · exact Set.Subset.trans (stableKernel_subset E S₀ hS₀) (subset_allowedSet E S₀ hS₀)
  · intro hk
    have hsub : allowedSet E ⊆ stableKernel E := by
      intro x hx
      obtain ⟨S, hS, hxS⟩ := hx
      exact (hcoll S hS) hxS
    refine Set.Subset.antisymm hsub ?_
    · intro x hx
      rw [← hk]
      exact hsub hx
    · exact stableKernel_subset_allowedSet E hNE

/-- 中文说明：见证评价域。恰有两个可采纳评价 `{0,1}` 与 `{0,2}`：它们共享结论 `0`，
各自还允许另一个结论。三组规则在此例取同一判据（本例只展示边界，不区分三组的独立作用）。 -/
def trialDomain : EvalDomain (Fin 3) where
  admissibleSupport := fun S => S = ({0, 1} : Set (Fin 3)) ∨ S = ({0, 2} : Set (Fin 3))
  sufficientStandard := fun S => S = ({0, 1} : Set (Fin 3)) ∨ S = ({0, 2} : Set (Fin 3))
  rebuttalClosed := fun S => S = ({0, 1} : Set (Fin 3)) ∨ S = ({0, 2} : Set (Fin 3))

/-- 中文证明：见证域的可采纳评价恰为那两个集合。 -/
theorem admissible_trialDomain (S : Set (Fin 3)) :
    Admissible trialDomain S ↔
      S = ({0, 1} : Set (Fin 3)) ∨ S = ({0, 2} : Set (Fin 3)) :=
  ⟨fun ⟨h, _, _⟩ => h, fun h => ⟨h, h, h⟩⟩

/-- 中文证明：见证域的稳定内核是单点 `{0}`。 -/
theorem trial_stableKernel : stableKernel trialDomain = ({0} : Set (Fin 3)) := by
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    rw [mem_stableKernel_iff, admissible_trialDomain] at hx
    have h1 := hx ({0, 1} : Set (Fin 3)) (Or.inl rfl)
    have h2 := hx ({0, 2} : Set (Fin 3)) (Or.inr rfl)
    fin_cases x
    · rfl
    · exact absurd h2 (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; decide)
    · exact absurd h1 (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; decide)
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [mem_stableKernel_iff, admissible_trialDomain]
    intro S hS
    rcases hS with (rfl | rfl)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      exact Or.inl rfl
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      exact Or.inl rfl

/-- 中文证明：见证域存在可采纳评价（`{0,1}`），且它非空白。 -/
theorem trial_admissible_exists : ∃ S : Set (Fin 3), Admissible trialDomain S :=
  ⟨({0, 1} : Set (Fin 3)), (admissible_trialDomain _).mpr (Or.inl rfl)⟩

/-- 中文证明：见证域的允许评价集是 `{0,1,2}`。 -/
theorem trial_allowedSet : allowedSet trialDomain = ({0, 1, 2} : Set (Fin 3)) := by
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    rw [mem_allowedSet_iff, admissible_trialDomain] at hx
    obtain ⟨S, (rfl | rfl), hxS⟩ := hx
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxS ⊢
      rcases hxS with (h | h) <;> subst h <;> simp
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxS ⊢
      rcases hxS with (h | h) <;> subst h <;> simp
  · intro x hx
    rw [mem_allowedSet_iff, admissible_trialDomain]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with (h | h | h)
    · subst h
      exact ⟨({0, 1} : Set (Fin 3)), (admissible_trialDomain _).mpr (Or.inl rfl),
        by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; exact Or.inl rfl⟩
    · subst h
      exact ⟨({0, 1} : Set (Fin 3)), (admissible_trialDomain _).mpr (Or.inl rfl),
        by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; exact Or.inr rfl⟩
    · subst h
      exact ⟨({0, 2} : Set (Fin 3)), (admissible_trialDomain _).mpr (Or.inr rfl),
        by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; exact Or.inl rfl⟩

/-- 中文证明（契约 (g) 的非退化边界见证）：稳定内核单点 `{0}`，允许评价集却是 `{0,1,2}`；
存在属于允许集却不属于内核的结论。这就是"唯一判决严格强于有允许评价"，也是自由证明评价的边界。 -/
theorem trial_boundary :
    (∃ v : Fin 3, stableKernel trialDomain = {v}) ∧
      ∃ x y z : Fin 3, x ∈ allowedSet trialDomain ∧ y ∈ allowedSet trialDomain ∧ x ≠ y ∧
        z ∈ allowedSet trialDomain ∧ z ∉ stableKernel trialDomain :=
  ⟨⟨0, trial_stableKernel⟩, 1, 2, 1, by
    rw [trial_allowedSet]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact Or.inr (Or.inl rfl), by
    rw [trial_allowedSet]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact Or.inr (Or.inr rfl), by decide, by
    rw [trial_allowedSet]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact Or.inr (Or.inl rfl), by
    rw [trial_stableKernel]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]⟩

/-- 中文证明：见证域不满足收缩片段——故 `unique_verdict_iff_stable_kernel_singletons`
的反向假设不是空转，而是真实的边界条件。 -/
theorem trial_collapse_fails : ¬ collapsesToKernel trialDomain := by
  intro h
  have hsub := h ({0, 1} : Set (Fin 3)) ((admissible_trialDomain _).mpr (Or.inl rfl))
  have h1 : (1 : Fin 3) ∈ ({0, 1} : Set (Fin 3)) :=
    by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; exact Or.inr rfl
  have hker : (1 : Fin 3) ∈ stableKernel trialDomain := hsub h1
  rw [trial_stableKernel] at hker
  simp only [Set.mem_singleton_iff] at hker
  exact absurd hker (by decide)

end JurisLean.Seams.AdjudicationBridge
