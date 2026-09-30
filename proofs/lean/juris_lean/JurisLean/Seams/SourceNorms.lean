import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Mathlib.Order.Preorder.Finite
import JurisLean.FiniteMonotoneIteration
import JurisLean.HornDefinitions
import JurisLean.HornFixedPoint
import JurisLean.Genealogy.Part1

/-!
S1（L1 法源/规范层缝合件）—— Horn 闭包的语义双侧定理与 P-015 位阶极大元。

## 一、法律语义（人话）

"依法源能推出什么"有两层意思。一层是**程序性的**：把要件—效果规则一遍遍套用，直到不再
产生新结论，即迭代闭包；另一层是**评价性的**：在任何一个都满足了全部规则要求的"情形"
（模型）里都为真，即语义后承。判决理由其实同时要求这两层不分岔：既不能推出法源不蕴含的
结论（健全性），也不能漏掉法源必然蕴含的结论（完备性）。本件在最小正 Horn 片段上把两层
钉成一条双侧等值式 `horn_closure_semantic_iff`，这正是 `HornFixedPoint.lean:86-88`
明确让出的那道缺口（把 `TH` 的固定点与规则的模型对齐）在正片段内的补法。

第二条线是**法源位阶**。《立法法》的效力等级（宪法＞法律＞行政法规＞地方性法规＞规章）
在法律适用中的作用是"择高"：一组相互冲突的条款里，被选中适用的那一条，必须在本组内没人
能凭位阶压过它——数学上就是**极大元**。P-015 台账（`Genealogy/Part1.lean`）只有六行判定树
`resolveConflict` 与三条例外读数，没有任何极大元或无环定理；S5
（`Seams/InstitutionalEffects.lean:781-782`）只在"位次为 `Nat` 的显式表"上构造性给出极大元，
并把"一般有限无环优先关系"的版本明确递给本件。本件以 `exists_maximal_acyclic`（只要求
不自反＋传递）与 `exists_maximal_by_rank`（位阶映射形）闭合该递件，并证明位阶映射形
**按构造无环**（`no_priority_cycle`、`no_priority_cycle_walk`）。

## 二、数学对象

- `HornSystem α`（`HornDefinitions.lean:24`）：`univ : Finset α`、`initialFacts`、
  `rules : Finset (HornRule α)`；`HornRule` 只有 `premises : Finset α` 与 `conclusion : α`
  两个字段——**没有否定槽，也没有例外槽**（这是 §三 纯性边界的出发点）。
- `isModel sys M`：`M : Finset α` 含全部初始事实且对每条规则闭合。
- `entailed sys a`：`a` 属于 `sys` 的每一个模型（语义后承）。
- `closureAt sys`：`FiniteMonotoneSystem.iter (toFiniteMonotoneSystem sys) (card sys.univ)`，
  即 |univ| 步处的有限迭代闭包；用 `abbrev` 只为陈述可读，不是另一个算子。
- `outranksBy ρ x y`：`ρ x < ρ y`（y 严格压过 x）；`outranksWalk ρ` 是其"至少一步"的
  传递闭包形，用来陈述任意长度的无环。
- 时间表示：本件只碰 `P015.NormProvision.enactedDay : Nat`。仓内并存
  `LegalModelV2.Event.atDay : Int`、`KernelV3.EventHistory.factTime : Nat`（同文件的
  `eventTimes : List Nat` 从不被 `KernelV3.applicableNorm :229` 读取），以及
  `ApplicableNormQuery` 使用的 `TimePoint`；`LegalModelV2.lean:158` 与 `KernelV3.lean:224`
  还是两个同名而异义的 `EventHistory`。本件不混用它们，也不判断"某时点是否适用"
  （那是 `TemporalApplicability.lean:41` 与 `FullMath/Burden/SourceTime.lean` 的语义）。

## 三、证什么、不证什么

**证（健全性）** `closure_only_entailed`：沿迭代归纳，`iter n` 每一步都不离开任意模型
（`step_within_model` 只用模型定义的两支），取 `n = card univ`。
**证（完备性）** `entailed_in_closure`：先证迭代闭包自身是模型（`closure_is_model`，用仓内
已证的 `HornSystem.horn_result_fixed_point`，即 `TH (闭包) = 闭包`，等价于
`FiniteMonotoneIteration.lean:103` 的 `fixed_at_card`），再把 `entailed` 在该典范模型处
实例化。合成 `horn_closure_semantic_iff`；`α` 只需 `DecidableEq`，无额外结构。
**证（纯性边界）** `negLiteralStep_not_mono`（带"未被推出"前件的算子不保序）、
`negLiteralStep_not_TH`（因而它不是任何 `HornSystem` 的 `TH`，理由正是仓内 `TH_monotone`）、
`negated_step_one_step_not_entailed`（`Bool` 上的可判定见证：允许否定前件时"一步得出"
真的不再等于"在所有模型中真"）。
**不证**：本件 `isModel` 是**给定 ground 原子集上的集合级语义**，不是 Herbrand 模型语义——
没有项、没有函数符号、没有合一；`HornFixedPoint.lean:86-88` 的免责声明只被部分弥合。
位阶部分只证极大元与无环，**不**证 `resolveConflict` 覆盖一切真实冲突形态，也**不**认定
任何真实法条的位阶归属。

## 四、未覆盖片段

- 否定/例外扩展（可废止规则、AAF 攻击关系）不在本件；边界只以反例算子标出。
- 无限规则集：`isModel` 量化 `Finset α`，与"全部集合形模型"的等价需要 Fintype 化，未做。
- 平位阶冲突的"裁决"通道（特别规定与新规定不一致时报请制定机关裁决）在数学上表现为
  `resolveConflict` 返回 `none`。本件给出的是：`none` **不等于**"组内无极大元"
  （`p015_none_is_not_no_maximal`：完全平手时两条同样极大），`none` 必然意味着**平位阶**
  （`resolveConflict_none_is_rank_tie`），但平位阶也**不**迫使 `none`
  （`rank_tie_not_none`）；`some` 方向才与极大元对齐
  （`resolveConflict_some_selects_maximal`），且 `some` **不**意味着极大元唯一
  （`p015_some_not_unique_maximal`：台账的平手处理是"特别法/新法优先"的政策，不是序定理）。
  把 `none` 读成"法律上没有答案"是越界。
- 三条以上条款组成的真实冲突组的择一适用：本件只证极大元存在与两两判定的相容性。

## 五、档位

无 `sorry`/`admit`/自定义 `axiom`；`decide` 只用于 `Nat`/`Bool`/`String` 的闭式字面量。
语义双侧定理 [已证，认定待 CI]；否定前件边界 [构造性见证]；
极大元与无环 [已证，认定待 CI]；`resolveConflict` 相容性 [已证，明确记为片段]；
Herbrand 桥、多条款择一、真实条文认定 [未覆盖]。本地编译不等于 Lean PASS。
-/

namespace JurisLean.Seams.SourceNorms

variable {α : Type} [DecidableEq α]

section SemanticClosure

/-- 中文说明：**Horn 模型**。`M` 含系统全部初始事实，且对每条规则闭合：前提都在 `M` 里
    就承认结论。这是正 Horn 片段的评价性读法，与"迭代得出"是两件事。因 `HornRule` 无
    否定/例外字段，闭合条件只是"前提集合被包含"。 -/
def isModel (sys : HornSystem α) (M : Finset α) : Prop :=
  sys.initialFacts ⊆ M ∧ ∀ r ∈ sys.rules, r.premises ⊆ M → r.conclusion ∈ M

/-- 中文说明：**语义后承**。`a` 被 `sys` 蕴含，当且仅当 `a` 属于 `sys` 的每一个模型。 -/
def entailed (sys : HornSystem α) (a : α) : Prop :=
  ∀ M : Finset α, isModel sys M → a ∈ M

/-- 中文说明：**迭代闭包缩写**。它就是
    `FiniteMonotoneSystem.iter (toFiniteMonotoneSystem sys) (Finset.card sys.univ)`，
    即 |univ| 步处的有限迭代闭包；`abbrev` 不为引入新算子。 -/
abbrev closureAt (sys : HornSystem α) : Finset α :=
  FiniteMonotoneSystem.iter (HornSystem.toFiniteMonotoneSystem sys) (Finset.card sys.univ)

/-- 中文说明：**模型类非空**：全论域 `sys.univ` 自身是模型。故 `entailed` 不是空洞为真，
    完备性方向（凡被蕴含者必进闭包）才有内容。 -/
theorem isModel_univ (sys : HornSystem α) : isModel sys sys.univ :=
  ⟨sys.initialFacts_subset_univ, fun r hr _ => sys.heads_subset_univ r hr⟩

/-- 中文说明：**单步不越模型**。若 `S ⊆ M` 且 `M` 是模型，则 `TH sys S ⊆ M`。
    健全性归纳的一步，只消费模型定义的两支。 -/
theorem step_within_model (sys : HornSystem α) (M S : Finset α)
    (hM : isModel sys M) (hS : S ⊆ M) : HornSystem.TH sys S ⊆ M := by
  intro x hx
  unfold HornSystem.TH at hx
  rcases Finset.mem_union.mp hx with (hx0 | hx1)
  · exact hM.1 hx0
  · rcases Finset.mem_image.mp hx1 with ⟨r, hr, rfl⟩
    rcases Finset.mem_filter.mp hr with ⟨hrR, hprem⟩
    exact hM.2 r hrR (hS hprem)

/-- 中文说明：**健全性的归纳骨架**：任意有限阶段近似 `iter n` 都包含于每个模型。
    迭代器本身取自仓内 `FiniteMonotoneIteration.lean`，本件不重证单调与终止。 -/
theorem iter_within_model (sys : HornSystem α) (M : Finset α) (hM : isModel sys M) :
    ∀ n : Nat, FiniteMonotoneSystem.iter (HornSystem.toFiniteMonotoneSystem sys) n ⊆ M := by
  intro n
  induction n with
  | zero => exact Finset.empty_subset _
  | succ k ih =>
      rw [FiniteMonotoneSystem.iter_succ]
      exact step_within_model sys M _ hM ih

/-- 中文说明：**典范模型**：|univ| 步处的迭代闭包自身是模型。用仓内已证的固定点等式
    `HornSystem.horn_result_fixed_point`（`TH (闭包) = 闭包`）："含初始事实"与
    "对规则闭合"都从该等式的另一侧读出。完备性靠的就是这一个见证。 -/
theorem closure_is_model (sys : HornSystem α) : isModel sys (closureAt sys) := by
  have hfp : HornSystem.TH sys (closureAt sys) = closureAt sys :=
    HornSystem.horn_result_fixed_point sys
  refine ⟨?_, ?_⟩
  · intro x hx
    have hmem : x ∈ HornSystem.TH sys (closureAt sys) := Finset.mem_union.mpr (Or.inl hx)
    rw [hfp] at hmem
    exact hmem
  · intro r hr hprem
    have hmem : r.conclusion ∈ HornSystem.TH sys (closureAt sys) :=
      Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨r, Finset.mem_filter.mpr ⟨hr, hprem⟩, rfl⟩))
    rw [hfp] at hmem
    exact hmem

/-- 中文说明：**健全性**（闭包只给出被蕴含者）：凡进入迭代闭包的原子，在每个模型里都真。 -/
theorem closure_only_entailed (sys : HornSystem α) {a : α}
    (h : a ∈ closureAt sys) : entailed sys a :=
  fun M hM => iter_within_model sys M hM (Finset.card sys.univ) h

/-- 中文说明：**完备性**（被蕴含者必进闭包）：把 `entailed` 在典范模型 `closureAt sys`
    处实例化即可，不需要对模型另作有限性论证。 -/
theorem entailed_in_closure (sys : HornSystem α) {a : α} (h : entailed sys a) :
    a ∈ closureAt sys :=
  h (closureAt sys) (closure_is_model sys)

/-- 中文说明：**本件主定理（双侧）**：`a` 在 |univ| 步迭代闭包里 ⟺ `a` 是 `sys` 的语义后承。
    两个方向都在本件内实证（`closure_only_entailed` 与 `entailed_in_closure`），
    没有把任一方向写成假设。`α` 只需 `DecidableEq`。
    强度注：这是正 Horn 片段上的集合级语义等值，不是 Herbrand 模型定理。 -/
theorem horn_closure_semantic_iff (sys : HornSystem α) (a : α) :
    a ∈ closureAt sys ↔ entailed sys a :=
  ⟨closure_only_entailed sys, fun h => entailed_in_closure sys h⟩

/-- 中文说明：**语义不外溢**：被蕴含者仍在论域内。比 `HornFixedPoint.lean:73` 的载体穷尽性
    多走一步——那条只谈闭包不谈模型，本条说明语义层也走不出 `univ`。 -/
theorem entailed_only_in_univ (sys : HornSystem α) {a : α} (h : entailed sys a) :
    a ∈ sys.univ :=
  HornSystem.horn_result_subset_univ sys (entailed_in_closure sys h)

end SemanticClosure

section PurityBoundary

/-- 中文说明：**否定前件算子**（越界见证，不属于 `HornSystem`）：把"`a` 尚未被推出"当前提，
    于是集合越大结论越少。`HornRule.premises : Finset α` 只能装正文字面量，写不出它。 -/
def negLiteralStep (a c : α) : Finset α → Finset α :=
  fun S => if a ∈ S then (∅ : Finset α) else ({c} : Finset α)

/-- 中文说明：**边界见证一**：否定前件算子不保序。`∅ ⊆ {a}`，但
    `negLiteralStep a c ∅ = {c}` 而 `negLiteralStep a c {a} = ∅`，故 `{c} ⊆ ∅` 失败。 -/
theorem negLiteralStep_not_mono (a c : α) :
    ¬ ∀ (S T : Finset α), S ⊆ T →
      negLiteralStep (α := α) a c S ⊆ negLiteralStep (α := α) a c T := by
  intro hall
  have hsub : negLiteralStep (α := α) a c (∅ : Finset α) ⊆
      negLiteralStep (α := α) a c ({a} : Finset α) :=
    hall (∅ : Finset α) ({a} : Finset α) (Finset.empty_subset _)
  have hc : c ∈ negLiteralStep (α := α) a c (∅ : Finset α) := by
    unfold negLiteralStep
    by_cases ha : a ∈ (∅ : Finset α)
    · exact absurd ha (Finset.notMem_empty a)
    · rw [if_neg ha]
      exact Finset.mem_singleton_self c
  have hnc : ¬ c ∈ negLiteralStep (α := α) a c ({a} : Finset α) := by
    unfold negLiteralStep
    by_cases ha : a ∈ ({a} : Finset α)
    · rw [if_pos ha]
      exact Finset.notMem_empty c
    · exact absurd (Finset.mem_singleton_self a) ha
  exact hnc (hsub hc)

/-- 中文说明：**边界见证二**：带否定前件的算子不是任何 `HornSystem` 的 `TH`。依据是仓内
    `HornDefinitions.lean:41` 的 `TH_monotone`：任何 `TH` 都保序，而该算子不保序。
    这条把"纯性"钉在可证的位置上，而不是靠注释宣称 Horn 片段没有否定。 -/
theorem negLiteralStep_not_TH (a c : α) :
    ¬ ∃ (sys : HornSystem α), HornSystem.TH sys = negLiteralStep (α := α) a c := by
  rintro ⟨sys, hsys⟩
  refine negLiteralStep_not_mono (α := α) a c ?_
  intro S T hST
  have hS : negLiteralStep (α := α) a c S = HornSystem.TH sys S := (congrFun hsys S).symm
  have hT : negLiteralStep (α := α) a c T = HornSystem.TH sys T := (congrFun hsys T).symm
  rw [hS, hT]
  exact HornSystem.TH_monotone sys hST

/-- 中文说明：**一般算子的模型**（只用于越界见证）：`facts ⊆ M` 且 `step M ⊆ M`。
    与 `isModel` 的差别在于不要求 `step` 来自正 Horn 规则。 -/
def stepModel (step : Finset α → Finset α) (facts M : Finset α) : Prop :=
  facts ⊆ M ∧ step M ⊆ M

/-- 中文说明：一般算子的语义后承：在全部此类模型中都真。 -/
def stepEntailed (step : Finset α → Finset α) (facts : Finset α) (a : α) : Prop :=
  ∀ M, stepModel step facts M → a ∈ M

/-- 中文说明：**边界见证三（语义层真失效）**：在 `Bool` 上取否定前件算子，`true` 一步即被
    推出，但 `{false}` 是它的模型且不含 `true`。故"允许否定前件 ⇒ 健全性破"不是修辞，
    而有可判定的具体反例；本件因此不把 `horn_closure_semantic_iff` 外推到可废止规则。 -/
theorem negated_step_one_step_not_entailed :
    ∃ (step : Finset Bool → Finset Bool) (facts : Finset Bool) (a : Bool),
      a ∈ step facts ∧ ¬ stepEntailed step facts a := by
  refine ⟨negLiteralStep (α := Bool) false true, (∅ : Finset Bool), true, ?_, ?_⟩
  · simp [negLiteralStep]
  · intro hall
    have hmodel : stepModel (negLiteralStep (α := Bool) false true) (∅ : Finset Bool)
        ({false} : Finset Bool) :=
      ⟨Finset.empty_subset _, by simp [stepModel, negLiteralStep]⟩
    exact absurd (hall _ hmodel) (by simp)

end PurityBoundary

section PriorityMaximal

/-- 中文说明：**优先关系（位阶映射形）**：`outranksBy ρ x y` 意为"在位阶映射 `ρ` 下 `y`
    严格压过 `x`"。由映射诱导，故按构造无环。 -/
def outranksBy {β : Type} (ρ : β → Nat) (x y : β) : Prop := ρ x < ρ y

/-- 中文说明：**无环（三元）**：只要优先关系不自反且传递，就不存在 `x` 被 `y` 压、
    `y` 被 `z` 压、`z` 又被 `x` 压的环。位阶映射只是实例。 -/
theorem no_priority_cycle {β : Type} (r : β → β → Prop)
    (h_irrefl : ∀ x, ¬ r x x)
    (h_trans : ∀ {x y z}, r x y → r y z → r x z)
    (x y z : β) : ¬ (r x y ∧ r y z ∧ r z x) := by
  rintro ⟨hxy, hyz, hzx⟩
  exact h_irrefl x (h_trans (h_trans hxy hyz) hzx)

/-- 中文说明：**位阶映射按构造无环**（`no_priority_cycle` 在 `outranksBy` 处的实例）。 -/
theorem outranksBy_no_cycle {β : Type} (ρ : β → Nat) (x y z : β) :
    ¬ (outranksBy ρ x y ∧ outranksBy ρ y z ∧ outranksBy ρ z x) :=
  no_priority_cycle (outranksBy ρ)
    (fun w hw => absurd hw (Nat.lt_irrefl (ρ w)))
    (fun h1 h2 => Nat.lt_trans h1 h2) x y z

/-- 中文说明：**优先链**（`outranksBy` 的"至少一步"传递闭包）。用于陈述任意长度的无环，
    而不只是三元环。 -/
inductive outranksWalk {β : Type} (ρ : β → Nat) : β → β → Prop where
  /-- 中文说明：单步优先。 -/
  | base {x y} (h : outranksBy ρ x y) : outranksWalk ρ x y
  /-- 中文说明：一步优先接上一段优先链。 -/
  | cons {x y z} (h : outranksBy ρ x y) (w : outranksWalk ρ y z) : outranksWalk ρ x z

/-- 中文说明：**无环（任意长）**：一段严格升位阶的优先链不能被回边闭合。这是 S5 递来的
    "一般无环优先关系"所需的无环侧证据；只用 `Nat` 的传递与不自反。 -/
theorem no_priority_cycle_walk {β : Type} (ρ : β → Nat) {x y : β}
    (w : outranksWalk ρ x y) : ¬ outranksBy ρ y x := by
  induction w with
  | base hxy =>
      intro h
      exact absurd (Nat.lt_trans hxy h) (Nat.lt_irrefl (ρ x))
  | cons hxy w2 ih =>
      intro h
      exact ih (Nat.lt_trans h hxy)

/-- 中文说明：**极大元（位阶映射形，复用 `Finset.exists_maximalFor`）**。选它而非
    `Finset.exists_maximal` 的理由要写明：后者要求**载体自身**带 `LE`，而位阶是外挂映射；
    `exists_maximalFor` 正是 `exists_maximal` 的证明入口，形态与位阶映射吻合。
    结论读法：`m ∈ s`，且 `s` 中任何 `x` 若不比 `m` 低，则 `m` 也不比 `x` 低——
    即"`m` 没被组内成员凭位阶压过"。`β` 只需 `LE` 与 `LE` 的传递性。 -/
theorem exists_maximal_by_rank {γ β : Type} [LE β] [IsTrans β LE.le]
    (ρ : γ → β) (s : Finset γ) (hs : s.Nonempty) :
    ∃ m, m ∈ s ∧ ∀ x, x ∈ s → ρ m ≤ ρ x → ρ x ≤ ρ m := by
  obtain ⟨m, hm⟩ := Finset.exists_maximalFor ρ s hs
  exact ⟨m, hm.1, fun x hx hle => hm.2 hx hle⟩

/-- 中文说明：**极大元（一般有限无环优先关系）**：优先关系只要不自反且传递，任意有限非空
    集合就含一个不被组内成员压过的元素。这条闭合 S5 的递件
    （`Seams/InstitutionalEffects.lean:781-782` 只处理了"位次为 `Nat` 的显式表"）。
    证明按集合插入归纳，不引入 `AcyclicRel`／`WfDyMeas`（本 pin 无此二者）。 -/
theorem exists_maximal_acyclic {β : Type} [DecidableEq β]
    (r : β → β → Prop) (h_irrefl : ∀ x, ¬ r x x)
    (h_trans : ∀ {x y z}, r x y → r y z → r x z) :
    ∀ (s : Finset β), s.Nonempty → ∃ m, m ∈ s ∧ ∀ x, x ∈ s → ¬ r m x := by
  intro s
  classical
  induction s with
  | empty => exact fun hs => absurd hs Finset.not_nonempty_empty
  | insert a t hat ih =>
      intro hs
      by_cases ht : t.Nonempty
      · obtain ⟨m, hm, hmax⟩ := ih ht
        by_cases ham : r m a
        · refine ⟨a, Finset.mem_insert.mpr (Or.inl rfl), fun x hx hx' => ?_⟩
          rcases Finset.mem_insert.mp hx with rfl | hxt
          · exact h_irrefl a hx'
          · exact hmax x hxt (h_trans hx' ham)
        · refine ⟨m, Finset.mem_insert.mpr (Or.inr hm), fun x hx hx' => ?_⟩
          rcases Finset.mem_insert.mp hx with rfl | hxt
          · exact ham hx'
          · exact hmax x hxt hx'
      · refine ⟨a, Finset.mem_insert.mpr (Or.inl rfl), fun x hx hx' => ?_⟩
        rcases Finset.mem_insert.mp hx with rfl | hxt
        · exact h_irrefl a hx'
        · exact ht ⟨x, hxt⟩

/-- 中文说明：P-015 位阶映射（`Genealogy/Part1.lean:53` 的 `rankScore` 把六位阶映到 `6..1`）。
    本件不重定义位阶，只把它当作映射形陈述的实例。 -/
def provisionRank (p : P015.NormProvision) : Nat := P015.rankScore p.rank

/-- 中文说明：**P-015 有限冲突组有极大元**：非空有限条款集中存在一条，组内无人能凭位阶
    压过它。这是 `exists_maximal_acyclic` 在位阶映射处的实例，不是新的法律命题。 -/
theorem p015_exists_maximal (s : Finset P015.NormProvision) (hs : s.Nonempty) :
    ∃ m, m ∈ s ∧ ∀ x ∈ s, ¬ provisionRank m < provisionRank x :=
  exists_maximal_acyclic (fun x y => provisionRank x < provisionRank y)
    (fun p => Nat.lt_irrefl (provisionRank p))
    (fun h1 h2 => Nat.lt_trans h1 h2) s hs

/-- 中文说明：见证条款（宪法位阶、一般规定）。 -/
def constItem : P015.NormProvision :=
  { provisionId := "宪法条文X", rank := .constitution, enactedDay := 100, special := false }

/-- 中文说明：见证条款（部门规章位阶、且声明为特别规定）。 -/
def deptItem : P015.NormProvision :=
  { provisionId := "规章条文Y", rank := .departmentalRule, enactedDay := 200, special := true }

/-- 中文说明：**位阶压过特别法属性**：`{宪法X, 规章Y}` 中宪法条款是极大元，规章纵被标为
    特别规定也压不过它（`rankScore` 6 与 1 的闭式比较）。这是"上位法优于下位法"在极大元
    读法下的可判定见证，不构成对任何真实条文位阶的认定。 -/
theorem p015_const_is_maximal :
    constItem ∈ ({constItem, deptItem} : Finset P015.NormProvision) ∧
      ∀ x ∈ ({constItem, deptItem} : Finset P015.NormProvision),
        ¬ provisionRank constItem < provisionRank x :=
  ⟨Finset.mem_insert.mpr (Or.inl rfl), by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Nat.lt_irrefl _
    · rcases Finset.mem_singleton.mp hx with rfl
      decide⟩

/-- 中文说明：平位阶端点的极大性（左端）：`b` 不严格高于 `a` 时 `a` 在 `{a,b}` 中极大。 -/
theorem maximal_left_of_rank_tie (a b : P015.NormProvision)
    (h : ¬ provisionRank a < provisionRank b) :
    a ∈ ({a, b} : Finset P015.NormProvision) ∧
      ∀ x ∈ ({a, b} : Finset P015.NormProvision), ¬ provisionRank a < provisionRank x :=
  ⟨Finset.mem_insert.mpr (Or.inl rfl), by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Nat.lt_irrefl _
    · rcases Finset.mem_singleton.mp hx with rfl
      exact h⟩

/-- 中文说明：平位阶端点的极大性（右端）。 -/
theorem maximal_right_of_rank_tie (a b : P015.NormProvision)
    (h : ¬ provisionRank b < provisionRank a) :
    b ∈ ({a, b} : Finset P015.NormProvision) ∧
      ∀ x ∈ ({a, b} : Finset P015.NormProvision), ¬ provisionRank b < provisionRank x :=
  ⟨Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self b)), by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact h
    · rcases Finset.mem_singleton.mp hx with rfl
      exact Nat.lt_irrefl _⟩

/-- 中文说明：判定树第二分支的显式读数（`Genealogy/Part1.lean:70`）：首分支未命中且 `a`
    位阶严格低于 `b` 时判给 `b`。本件不修改台账定义。 -/
theorem resolveConflict_some_right_of_rank (a b : P015.NormProvision)
    (h1 : ¬ provisionRank b < provisionRank a) (h2 : provisionRank a < provisionRank b) :
    P015.resolveConflict a b = some b.provisionId := by
  simp only [provisionRank] at h1 h2
  simp [P015.resolveConflict, h1, h2]

/-- 中文说明：**平位阶区间内判定的取值范围**：只能是"判给 a"、"判给 b"或 `none` 三者之一。
    这条是 `resolveConflict_some_selects_maximal` 的技术支点，本身不含法律主张。 -/
theorem resolveConflict_tie_value_in (a b : P015.NormProvision)
    (h1 : ¬ provisionRank b < provisionRank a) (h2 : ¬ provisionRank a < provisionRank b) :
    P015.resolveConflict a b ∈
      ({some a.provisionId, some b.provisionId, none} : Finset (Option String)) := by
  cases a with
  | mk idA rA dA sA =>
    cases b with
    | mk idB rB dB sB =>
      simp only [provisionRank] at h1 h2
      unfold P015.resolveConflict
      split_ifs with hc1 hc2 h3 h4
      · exact absurd hc1 h1
      · exact absurd hc2 h2
      · cases sA <;> cases sB <;> simp
      · cases sB <;> cases sA <;> simp
      · cases sA <;> cases sB <;> simp

/-- 中文说明：**判定树选中者确是极大元**：`resolveConflict a b = some k` 时，组内存在极大
    条款 `m`，使判定结果正是 `m.provisionId`（配合假设 `h` 即得 `k = m.provisionId`，
    因返回值为 `Option` 单值）。
    片段相对：只对两元素冲突组；`enactedDay` 的新旧与特别法属性只是台账的择一政策，
    本件不把它们升格为序关系，也不声称平位阶有唯一解。 -/
theorem resolveConflict_some_selects_maximal (a b : P015.NormProvision) (k : String)
    (h : P015.resolveConflict a b = some k) :
    ∃ m ∈ ({a, b} : Finset P015.NormProvision),
      (∀ x ∈ ({a, b} : Finset P015.NormProvision), ¬ provisionRank m < provisionRank x) ∧
        P015.resolveConflict a b = some m.provisionId := by
  by_cases h1 : provisionRank b < provisionRank a
  · have hv : P015.resolveConflict a b = some a.provisionId :=
      P015.lex_superior_left a b h1
    obtain ⟨ham, hmax⟩ := maximal_left_of_rank_tie a b (Nat.lt_asymm h1)
    exact ⟨a, ham, hmax, hv⟩
  · by_cases h2 : provisionRank a < provisionRank b
    · have hv : P015.resolveConflict a b = some b.provisionId :=
        resolveConflict_some_right_of_rank a b h1 h2
      obtain ⟨hbm, hmax⟩ := maximal_right_of_rank_tie a b h1
      exact ⟨b, hbm, hmax, hv⟩
    · have hval : P015.resolveConflict a b ∈
        ({some a.provisionId, some b.provisionId, none} : Finset (Option String)) :=
        resolveConflict_tie_value_in a b h1 h2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hval
      rcases hval with hv | hv | hv
      · obtain ⟨ham, hmax⟩ := maximal_left_of_rank_tie a b h2
        exact ⟨a, ham, hmax, hv⟩
      · obtain ⟨hbm, hmax⟩ := maximal_right_of_rank_tie a b h1
        exact ⟨b, hbm, hmax, hv⟩
      · rw [hv] at h
        cases h

/-- 中文说明：`none` 的直接读数：判定树返回 `none` 时双方在位阶上互不压过（首、次分支皆
    未命中）。这是 `none` 的必要条件，不是它的全部含义。 -/
theorem resolveConflict_none_neither_outranks (a b : P015.NormProvision)
    (h : P015.resolveConflict a b = none) :
    ¬ provisionRank a < provisionRank b ∧ ¬ provisionRank b < provisionRank a := by
  refine ⟨fun ha => ?_, fun hb => ?_⟩
  · rw [resolveConflict_some_right_of_rank a b (Nat.lt_asymm ha) ha] at h
    cases h
  · rw [P015.lex_superior_left a b hb] at h
    cases h

/-- 中文说明：`none` 必然意味着**平位阶**（`rankScore` 相等）。因此把台账的 `none` 读成
    "位阶有别但无法定夺"是错的：此时位阶不提供任何胜负信息。《立法法》意义上的出路是报请
    裁决，而不是"数学上无极大元"。 -/
theorem resolveConflict_none_is_rank_tie (a b : P015.NormProvision)
    (h : P015.resolveConflict a b = none) : provisionRank a = provisionRank b := by
  obtain ⟨h1, h2⟩ := resolveConflict_none_neither_outranks a b h
  omega

/-- 中文说明：见证条款（同位阶、旧一般规定）。 -/
def oldGeneral : P015.NormProvision :=
  { provisionId := "旧一般", rank := .statute, enactedDay := 10, special := false }

/-- 中文说明：见证条款（同位阶、新特别规定）。 -/
def newSpecial : P015.NormProvision :=
  { provisionId := "新特别", rank := .statute, enactedDay := 20, special := true }

/-- 中文说明：平位阶**不**迫使 `none`：同为法律位阶时，旧一般对新特别仍判给新特别。
    故 `none` 严格弱于"位阶相同"。 -/
theorem rank_tie_not_none :
    provisionRank oldGeneral = provisionRank newSpecial ∧
      P015.resolveConflict oldGeneral newSpecial ≠ none :=
  ⟨rfl, by decide⟩

/-- 中文说明：完全平手见证（与台账 `same_rank_day_nature_unknown` 同一对字面量）：同位阶、
    同公布日、同性质 ⇒ `none`。 -/
def tieA : P015.NormProvision :=
  { provisionId := "a", rank := .statute, enactedDay := 20, special := false }

/-- 中文说明：完全平手见证的另一条款。 -/
def tieB : P015.NormProvision :=
  { provisionId := "b", rank := .statute, enactedDay := 20, special := false }

/-- 中文说明：**`none` 不等于"组内无极大元"**：完全平手时 `tieA`、`tieB` 同样极大，极大元
    集非空。台账返回 `none` 的含义是"位阶＋时间＋性质这套择一政策没给出唯一胜者"，
    不是"没有可适用的最高规范"。把两者混同即越界。 -/
theorem p015_none_is_not_no_maximal :
    P015.resolveConflict tieA tieB = none ∧
      (∀ x ∈ ({tieA, tieB} : Finset P015.NormProvision), ¬ provisionRank tieA < provisionRank x) ∧
      (∃ m ∈ ({tieA, tieB} : Finset P015.NormProvision),
          ∀ x ∈ ({tieA, tieB} : Finset P015.NormProvision), ¬ provisionRank m < provisionRank x) :=
  ⟨P015.same_rank_day_nature_unknown,
    (maximal_left_of_rank_tie tieA tieB (by decide)).2,
    tieA, Finset.mem_insert.mpr (Or.inl rfl),
    (maximal_left_of_rank_tie tieA tieB (by decide)).2⟩

/-- 中文说明：**`some` 不等于"极大元唯一"**：平位阶的旧一般对新特别有解（判给新特别），
    但两条在位阶上同样极大。可见 `resolveConflict` 的平手处理是**政策**（特别法、新法优先），
    不是从位阶序推出的定理；本件不把它写成序性质。 -/
theorem p015_some_not_unique_maximal :
    P015.resolveConflict oldGeneral newSpecial = some "新特别" ∧
      (∀ x ∈ ({oldGeneral, newSpecial} : Finset P015.NormProvision),
          ¬ provisionRank oldGeneral < provisionRank x) ∧
      (∀ x ∈ ({oldGeneral, newSpecial} : Finset P015.NormProvision),
          ¬ provisionRank newSpecial < provisionRank x) :=
  ⟨by decide,
    (maximal_left_of_rank_tie oldGeneral newSpecial (by decide)).2,
    (maximal_right_of_rank_tie oldGeneral newSpecial (by decide)).2⟩

/-- 中文说明：**判定树与极大元在具体层面的对齐**：位阶不同时判给位阶高者，而该者正是
    `{宪法X, 规章Y}` 的极大元；判给的方向与极大元方向一致（复用台账 `lex_superior_left`）。 -/
theorem resolveConflict_agrees_with_maximal_on_demo :
    P015.resolveConflict constItem deptItem = some constItem.provisionId ∧
      provisionRank deptItem < provisionRank constItem :=
  ⟨P015.lex_superior_left constItem deptItem (by decide), by decide⟩

end PriorityMaximal

end JurisLean.Seams.SourceNorms
