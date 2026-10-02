import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic
import JurisLean.KernelV3
import JurisLean.TaintNoninterference
import JurisLean.Seams.AdjudicationBridge
import JurisLean.Seams.SourceNorms
import JurisLean.Seams.Representation
import JurisLean.Seams.ClaimBasis
import JurisLean.Seams.InstitutionalEffects
import JurisLean.Seams.Uncertainty
import JurisLean.Seams.PrecedentFlow
import JurisLean.Seams.Unified

/-!
# G5 —— 统一模型 `UnifiedModel` 的诚实闭合项（`docs/master-plan/12_…_20261002.md` §五）

本件按 §5.1 的字段方案逐栏造见证，交付**一个真的 `UnifiedModel` 闭合项** `instanceM`，
并配套证明它身上那几条此前全仓无人满足的片段前提（`policyClosed`、`baseInGrounded`、
`collapsesToKernel`）**同时成立**。本件**不**改 `AdjudicationBridge.lean`、`Seams/Transitions.lean`；
`Seams/Unified.lean` 本轮只动 Owner 授权的一处契约增量：`UnifiedModel` 增 `observation` 栏，既有定理文本一字未改。

## §为什么不能用现成的两个见证（§5.1 的两次避开）
1. **`aaf/pol` 不能取 `cycle2`/`cycle2Policy`**（`AdjudicationBridge.lean:583/:589`）：
   它的第 0 层采纳集是 `{p}`（`cycle2_baseSet :601`），而偶环的接地集是 `∅`
   （`cycle2_grounded_eq_empty :636`），与 `UnifiedModel` 要求的 `baseInGrounded`
   （`AdjudicationBridge.lean:514`，`baseSet ⊆ grounded`）**互斥**。
   本件改取**攻击集为空**的字面框架，此时 `baseSet = args = grounded`，两侧同时成立。
2. **`evalDom` 不能取 `trialDomain`**（`:884`）：它有两个可采纳评价 `{0,1}` 与 `{0,2}`，
   于是 `collapsesToKernel`（`:846`）被 `trial_collapse_fails`（`:964`）**证否**，
   而 `UnifiedModel.hCollapse` 一栏正要求它。本件新造 `verdictDomain`：**恰有一个**
   可采纳评价 `S = {0}`，此时收缩性与"可采纳评价非空"同时为真（`verdictDomain_collapse_and_nonempty`）。
   非平凡性照 §5.1 的要求做成结构性的：三组规则判据**各自**都至少有两个成员
   （`verdictDomain_support_not_decisive` 等三条），单支都定不出判决，
   合取才恰好收到一个评价——不是把 `Admissible` 写成 `S = {0}` 的同义反复假见证。

## §`collapsesToKernel` 的分离（§5.2）与本轮的判断
§5.2 预备的分离方案（`structure UnifiedModelOnKernel extends UnifiedModel where hCollapse : …`，
主定理签名把该字段变成显式参数）是为"仓内造不出满足收缩性的评价域"这一情形准备的退路。
**本轮不需要这条退路**：`verdictDomain` 本身就满足收缩性，故 `instanceM` 按契约
（`Seams/Unified.lean:96` 的字段表；本轮只加 Owner 授权的 `observation` 一栏）直接闭合。
分离方案不等于改窄的理由（照 §5.2）：`AdjudicationBridge.lean:855` 本来就以 `hcoll` 作显式参数，
字段与参数是同一命题的两种写法——任何带该字段的 `M` 可降格、任何 `M` 加一条证明可升格，
其余四条合取支陈述一字不动。本件把同一口径用在**观测槽**上（见下一节）。

## §缺的那一环（G5 收尾·非退化关于 𝔐，§5.4）
§5.4 要求非退化的**分开者必须是 𝔐 自己声明的观测**。增栏之前契约里确实没有这一栏：
`Seams/Unified.lean:96` 的字段表**没有 `Representation.Fragment` 形制的观测槽**，
也没有任何 `ClaimBasis.Status` 形制的载体。本轮按 Owner 授权把该槽**做进本体**：
`UnifiedModel.observation : Representation.Fragment ClaimBasis.Status`。于是分三步登记：
- 加宽契约 `UnifiedModelObs`（一栏 `model : UnifiedModel V Rel` 加一栏
  `observation : Representation.Fragment ClaimBasis.Status`；不用 `extends` 只为避开
  父结构带实例隐式参数时的构造子问题，降格/升格两侧都有具名项：
  `forgetObservation` 与 `liftWithObservation`）**原样保留作对照**；`instanceM_nondegenerate`
  现读 `instanceM.observation`：对象是仓内真见证 `ClaimBasis.Status.suspended`／`.unenforceable`
  （互异引 `ClaimBasis.status_five_labels_pairwise_distinct :187`），
  分开者是**模型自己声明的观测字段**（`statusObsM`，定义在本件），
  **不是**拿 `ClaimBasis.fires`（`:95`，别文件的 def）冒充"本模型声明的观测"；
- "观测由 𝔐 决定"这一必要条件在本体上已证（`model_equality_determines_observation`）；
  加宽侧的必要条件 `observationDeterminedByModel` 与钉住旧事实的定理
  `observation_not_determined_by_the_model`（同一个 𝔐 载体可在**模型外面**再配一份
  取值不同的观测）**文本一字未改**——它们记录的就是"当初为何必须增栏"；
- 义务位 `def instanceM_nondegenerate_obligation : Prop` **保留、仍不含证明**：它量化的是
  `UnifiedModelObs` **外层**那一栏，增栏不消解它；消解动作是让加宽结构退役，见该条注释。

## §卡点与对策（§5.3 的工程说明）
`SourceNorms.closureAt`（`SourceNorms.lean:108`）是 `abbrev`，`decide` 穿不过
`FiniteMonotoneSystem.iter` 与 `HornSystem.TH` 的 `filter/image`。本件对策与 §5.3 一致：
闭合项里 `aaf.args` 那一栏直接用**字面 `Finset`**，不穿过 Horn 迭代；
需要闭包成员结论时走仓内典范模型 `SourceNorms.closure_is_model`（固定点一侧），
不做逐层计算，也不拿 `decide` 冒充未算出的等式。

## §纪律
零 `sorry`／`admit`／`native_decide`，零新增 `axiom`，不把结论写进前提，
不为过编译改窄任何陈述。Lean 权威认定只走 CI；本地 `lake build` 仅为预检（provisional）。
本件不对任何真实案件、任何真实法条适用性作认定；实例是**夹具**，法律读法逐条写在字段旁。

## §未覆盖片段
1. `PrecedentFlow.EnvWf` 的闭合见证是本件新造的（§5.1 登记：全仓零闭合实例）；
   它只证明"这一栏有人住"，**不**证明前例回流对真实法源集合成立。
2. 非退化已改证在 𝔐 **本体**的 `observation` 栏上；加宽结构 `UnifiedModelObs` 的外层那一栏仍不由 𝔐 决定（见上节义务）。
3. 端到端条文链（G6）不在本件：`Probability` 与 `ClaimBasis` 互相零 import，
   `badFaith` 位与 `Stage/Status` 之间无桥（§5.5 缺三环）。
-/

open BigOperators
open JurisLean.Seams.AdjudicationBridge

namespace JurisLean.Seams.UnifiedInstance

/-! ## 一、评价域见证（§5.1 第 2 条·交付项 1）-/

section EvalDomainWitness

/-- 中文说明：**恰有一个可采纳评价**的评价域（G5 的 `evalDom` 栏）。
    法律读法：`admissibleSupport`＝举证材料可采纳（两种心证：只认定结论 0，或连带认定结论 1）；
    `sufficientStandard`＝达到证明标准（两种：只认定 0，或连带认定 2）；
    `rebuttalClosed`＝对反驳封闭（三种：`{0}`、`{0,1}`、`{0,2}`）。
    三支**各自**都不唯一，合取却只剩 `{0}`——故"唯一判决"在这里是由三组法律判据
    **共同**逼出的。载体取 `Fin 3` 与 `trialDomain` 同，便于逐点比对
    （`verdictDomain_ne_trialDomain`）。 -/
def verdictDomain : EvalDomain (Fin 3) where
  admissibleSupport := fun S => S = ({0} : Set (Fin 3)) ∨ S = ({0, 1} : Set (Fin 3))
  sufficientStandard := fun S => S = ({0} : Set (Fin 3)) ∨ S = ({0, 2} : Set (Fin 3))
  rebuttalClosed := fun S => S = ({0} : Set (Fin 3)) ∨ S = ({0, 1} : Set (Fin 3)) ∨
    S = ({0, 2} : Set (Fin 3))

/-- 中文证明：`1` 不在 `{0}` 里（后面反复使用的成员事实）。 -/
theorem one_notin_singleton : ¬ ((1 : Fin 3) ∈ ({0} : Set (Fin 3))) := by simp

/-- 中文证明：`2` 不在 `{0}` 里。 -/
theorem two_notin_singleton : ¬ ((2 : Fin 3) ∈ ({0} : Set (Fin 3))) := by simp

/-- 中文证明：`0` 在 `{0}` 里。 -/
theorem zero_mem_singleton : (0 : Fin 3) ∈ ({0} : Set (Fin 3)) := by simp

/-- 中文证明：`{0,1}` 与 `{0}` 是两个不同的评价。判定走成员事实，不用 `decide`——
    `Set α` 在本 pin 没有可计算的 `DecidableEq`。 -/
theorem set01_ne_set0 : (({0, 1} : Set (Fin 3)) ≠ ({0} : Set (Fin 3))) := by
  intro h
  have h1 : (1 : Fin 3) ∈ ({0} : Set (Fin 3)) := by rw [← h]; simp
  exact absurd h1 one_notin_singleton

/-- 中文证明：`{0,2}` 与 `{0}` 不同。 -/
theorem set02_ne_set0 : (({0, 2} : Set (Fin 3)) ≠ ({0} : Set (Fin 3))) := by
  intro h
  have h2 : (2 : Fin 3) ∈ ({0} : Set (Fin 3)) := by rw [← h]; simp
  exact absurd h2 two_notin_singleton

/-- 中文证明：`{0,1}` 与 `{0,2}` 不同（`1` 在前者而不在后者）。 -/
theorem set01_ne_set02 : (({0, 1} : Set (Fin 3)) ≠ ({0, 2} : Set (Fin 3))) := by
  intro h
  have h1 : (1 : Fin 3) ∈ ({0, 2} : Set (Fin 3)) := by rw [← h]; simp
  exact absurd h1 (by simp)

/-- 中文证明：**可采纳评价恰是 `{0}` 一个**（三支合取后唯一）。
    这就是 `collapsesToKernel` 在本实例上成立的全部原因。 -/
theorem verdictDomain_admissible (S : Set (Fin 3)) :
    Admissible verdictDomain S ↔ S = ({0} : Set (Fin 3)) :=
  ⟨fun ⟨h₁, h₂, _⟩ => by
    rcases h₁ with rfl | rfl
    · rfl
    · rcases h₂ with h | h
      · exact absurd h set01_ne_set0
      · exact absurd h set01_ne_set02,
    fun h => by
      subst h
      exact ⟨Or.inl rfl, Or.inl rfl, Or.inl rfl⟩⟩

/-- 中文证明：恰存在**唯一**一个可采纳评价（§5.1 要的"恰有一个可采纳评价"）。 -/
theorem verdictDomain_admissible_unique : ∃! S : Set (Fin 3), Admissible verdictDomain S :=
  ⟨({0} : Set (Fin 3)), (verdictDomain_admissible _).mpr rfl,
    fun T hT => (verdictDomain_admissible T).mp hT⟩

/-- 中文证明：可采纳评价非空（`UnifiedModel.hAdmissibleNonempty` 那一栏）。 -/
theorem verdictDomain_admissibleNonempty : ∃ S : Set (Fin 3), Admissible verdictDomain S :=
  ⟨({0} : Set (Fin 3)), (verdictDomain_admissible _).mpr rfl⟩

/-- 中文证明：稳定核是单点 `{0}`。 -/
theorem verdictDomain_stableKernel : stableKernel verdictDomain = ({0} : Set (Fin 3)) := by
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    rw [mem_stableKernel_iff] at hx
    exact hx ({0} : Set (Fin 3)) ((verdictDomain_admissible _).mpr rfl)
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [mem_stableKernel_iff]
    intro S hS
    rw [verdictDomain_admissible] at hS
    subst hS
    exact zero_mem_singleton

/-- 中文证明：允许评价集也是单点 `{0}`（与核重合，正是收缩性的内容）。 -/
theorem verdictDomain_allowedSet : allowedSet verdictDomain = ({0} : Set (Fin 3)) := by
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    rw [mem_allowedSet_iff] at hx
    obtain ⟨S, hS, hxS⟩ := hx
    rw [verdictDomain_admissible] at hS
    rw [hS] at hxS
    exact hxS
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [mem_allowedSet_iff]
    exact ⟨({0} : Set (Fin 3)), (verdictDomain_admissible _).mpr rfl, zero_mem_singleton⟩

/-- 中文证明：**核为单点**的存在形陈述（与 `AdjudicationBridge.trial_boundary :948` 同形状，
    但本实例还满足收缩性）。 -/
theorem verdictDomain_kernel_is_singleton : ∃ v : Fin 3, stableKernel verdictDomain = {v} :=
  ⟨0, verdictDomain_stableKernel⟩

/-- 中文证明（§5.1 的关键交付）：**收缩性成立**。逐元素读：可采纳评价只能是 `{0}`，
    而核也正是 `{0}`，故每个可采纳评价都不超出核。 -/
theorem verdictDomain_collapse : collapsesToKernel verdictDomain := by
  intro S hS x hx
  rw [mem_stableKernel_iff]
  intro T hT
  have hS' : S = ({0} : Set (Fin 3)) := (verdictDomain_admissible S).mp hS
  have hT' : T = ({0} : Set (Fin 3)) := (verdictDomain_admissible T).mp hT
  rw [hS'] at hx
  rw [hT']
  exact hx

/-- 中文证明：收缩性与可采纳评价非空**同时**成立——这是 `UnifiedModel` 的
    `hAdmissibleNonempty` 与 `hCollapse` 两栏能同时填满的机器证据。
    `trialDomain` 做不到（`trial_collapse_fails :964` 证否其收缩性），故本栏必须新造。 -/
theorem verdictDomain_collapse_and_nonempty :
    collapsesToKernel verdictDomain ∧ ∃ S : Set (Fin 3), Admissible verdictDomain S :=
  ⟨verdictDomain_collapse, verdictDomain_admissibleNonempty⟩

/-- 中文证明：仓内条件等价式 `unique_verdict_iff_stable_kernel_singletons`（`:855`）
    在本实例上**真的可用**（两条片段都交出来了，不是空转）。 -/
theorem verdictDomain_unique_verdict :
    allowedSet verdictDomain = ({0} : Set (Fin 3)) ↔
      stableKernel verdictDomain = ({0} : Set (Fin 3)) :=
  unique_verdict_iff_stable_kernel_singletons verdictDomain 0
    verdictDomain_admissibleNonempty verdictDomain_collapse

/-- 中文证明：旧见证 `trialDomain` 在 `{0}` 处不可采纳——本件的新域不是把旧域抄一遍。 -/
theorem trialDomain_not_admissible_at_singleton :
    ¬ trialDomain.admissibleSupport ({0} : Set (Fin 3)) := by
  intro h
  rcases h with (h | h)
  · exact absurd h set01_ne_set0.symm
  · exact absurd h set02_ne_set0.symm

/-- 中文证明：新评价域与旧见证域**不是同一份数据**（只需 `admissibleSupport` 一支在 `{0}`
    处取值不同即可判定结构不等）。 -/
theorem verdictDomain_ne_trialDomain :
    (verdictDomain : EvalDomain (Fin 3)) ≠ trialDomain := by
  intro h
  have hcongr : verdictDomain.admissibleSupport ({0} : Set (Fin 3)) =
      trialDomain.admissibleSupport ({0} : Set (Fin 3)) :=
    congrFun (congrArg (fun (E : EvalDomain (Fin 3)) => E.admissibleSupport) h)
      ({0} : Set (Fin 3))
  have hv : verdictDomain.admissibleSupport ({0} : Set (Fin 3)) := Or.inl rfl
  have ht : trialDomain.admissibleSupport ({0} : Set (Fin 3)) := by rw [← hcongr]; exact hv
  exact trialDomain_not_admissible_at_singleton ht

/-- 中文证明（**非平凡性之一**）：`admissibleSupport` 一支自己定不出判决——它至少放过两个评价。 -/
theorem verdictDomain_support_not_decisive :
    ∃ S T : Set (Fin 3), S ≠ T ∧ verdictDomain.admissibleSupport S ∧
      verdictDomain.admissibleSupport T ∧ ¬ verdictDomain.sufficientStandard T := by
  refine ⟨({0} : Set (Fin 3)), ({0, 1} : Set (Fin 3)), set01_ne_set0.symm, Or.inl rfl,
    Or.inr rfl, ?_⟩
  intro h
  rcases h with (h | h)
  · exact absurd h set01_ne_set0
  · exact absurd h set01_ne_set02

/-- 中文证明（**非平凡性之二**）：`sufficientStandard` 一支自己定不出判决。 -/
theorem verdictDomain_standard_not_decisive :
    ∃ S T : Set (Fin 3), S ≠ T ∧ verdictDomain.sufficientStandard S ∧
      verdictDomain.sufficientStandard T ∧ ¬ verdictDomain.admissibleSupport T := by
  refine ⟨({0} : Set (Fin 3)), ({0, 2} : Set (Fin 3)), set02_ne_set0.symm, Or.inl rfl,
    Or.inr rfl, ?_⟩
  intro h
  rcases h with (h | h)
  · exact absurd h set02_ne_set0
  · exact absurd h set01_ne_set02.symm

/-- 中文证明（**非平凡性之三**）：`rebuttalClosed` 一支放过三个评价，更定不出判决。 -/
theorem verdictDomain_rebuttal_not_decisive :
    ∃ S T : Set (Fin 3), S ≠ T ∧ verdictDomain.rebuttalClosed S ∧
      verdictDomain.rebuttalClosed T ∧ ¬ Admissible verdictDomain T := by
  refine ⟨({0} : Set (Fin 3)), ({0, 1} : Set (Fin 3)), set01_ne_set0.symm, Or.inl rfl,
    Or.inr (Or.inl rfl), ?_⟩
  rw [verdictDomain_admissible]
  intro h
  exact set01_ne_set0 h

end EvalDomainWitness

/-! ## 二、L1 源规范层的闭合 Horn 系统（§5.1 第 3 条） -/

section NormsLayer

/-- 中文说明：本实例的 L1 栏——一个**闭合的** `HornSystem (Fin 2)`。
    §5.1 登记：仓内此前唯一的闭合 Horn 系统是 `Seams/Transitions.lean` 的 `claimCase`，
    而本件不 import 该件（单写者文件，另有代理在改）。
    法律读法（夹具，不是对任何真实条文的认定）：
    `0`＝"请求权成立的要件已成就"，`1`＝"可依法请求酌减"；
    一条无前提规则给出 `0`，一条以 `0` 为前提的规则给出 `1`——即"酌减的可能以成立为前提"。 -/
def normsM : HornSystem (Fin 2) where
  univ := {0, 1}
  initialFacts := {0}
  rules := {{ premises := {0}, conclusion := 1 }}
  initialFacts_subset_univ := by decide
  heads_subset_univ := by decide

/-- 中文说明：`normsM` 唯一的那条规则（写成可命名的项，便于在成员判定处引用）。 -/
def ruleM : HornRule (Fin 2) := { premises := {0}, conclusion := 1 }

/-- 中文说明：本实例的待判原子（`UnifiedModel.atom` 栏）。 -/
def atomM : Fin 2 := 1

/-- 中文证明：那条规则确在 `normsM.rules` 里（有限集字面量的成员判定，
    不涉及 `closureAt` 的迭代计算，故 `decide` 在此可用）。 -/
theorem ruleM_mem_rules : ruleM ∈ normsM.rules := by decide

/-- 中文证明（技术引理）：初始事实 `0` 在迭代闭包里。
    走仓内典范模型 `SourceNorms.closure_is_model`（固定点一侧）的"含初始事实"支，
    **不**穿过 `FiniteMonotoneSystem.iter` 的逐层计算——§5.3 登记的卡点就在这里绕开。 -/
theorem zero_in_closureM : (0 : Fin 2) ∈ SourceNorms.closureAt normsM :=
  (SourceNorms.closure_is_model normsM).1 (by decide)

/-- 中文证明（技术引理）：结论 `1` 也在迭代闭包里——前提 `{0}` 已含于闭包。
    同样走典范模型的闭合支，不做逐层计算。 -/
theorem one_in_closureM : (1 : Fin 2) ∈ SourceNorms.closureAt normsM :=
  (SourceNorms.closure_is_model normsM).2 ruleM ruleM_mem_rules
    (Finset.singleton_subset_iff.mpr zero_in_closureM)

/-- 中文证明：待判原子**语义上被蕴含**（`UnifiedChainCorrespondence` 第一条合取支的正方向，
    经仓内 `horn_closure_semantic_iff :171` 从闭包成员读出）。 -/
theorem atomM_entailed : SourceNorms.entailed normsM atomM :=
  (SourceNorms.horn_closure_semantic_iff normsM atomM).mp one_in_closureM

/-- 中文证明：`normsM` 的模型类非空（仓内 `isModel_univ`），故上一条不是空洞真。 -/
theorem normsM_model_class_nonempty :
    ∃ M : Finset (Fin 2), SourceNorms.isModel normsM M :=
  ⟨normsM.univ, SourceNorms.isModel_univ normsM⟩

end NormsLayer

/-! ## 三、L2 裁判层：攻击集为空的字面框架 + 论点全集的终端策略（§5.3 候选 A·交付项 2） -/

section AdjudicationLayer

/-- 中文说明：本实例的两个论点（`Arg` 在仓内就是 `String`，`DungDefinitions.lean:14`）。
    法律读法：`reduction_claim`＝"约定违约金过高，请求酌减"；
    `no_adjustment`＝"合同已约定不得调整，故不予调整"。仅为夹具标签，不认定任何条文。 -/
def claimReduction : Arg := "reduction_claim"

/-- 中文说明：第二个论点的字面标签。 -/
def claimNoAdjustment : Arg := "no_adjustment"

/-- 中文证明：两个论点确实是不同的字符串。
    工程说明：`Arg = String`，字面量不等**不能**用 `cases`（本 pin 的已知坑），走 `decide`。 -/
theorem claimReduction_ne_noAdjustment : claimReduction ≠ claimNoAdjustment := by decide

/-- 中文说明：**攻击集为空**的字面框架（§5.1 第 1 条要求的"改取攻击集为空的字面框架"）。
    `args` 一栏直接写**字面 `Finset`**，不取 `namedClosure` 之类的像——
    §5.3 登记的工程卡点（`decide` 穿不过 `iter`+`TH` 的 `filter/image`）就此绕过。
    法律读法：本案没有例外／抗辩规范打成的攻击边。 -/
def aafM : DungAAF := { args := {claimReduction, claimNoAdjustment}, attacks := ∅ }

/-- 中文证明：框架的攻击边集确实为空（字面量的自明等式）。 -/
theorem aafM_attacks_eq_empty : aafM.attacks = (∅ : Finset (Arg × Arg)) := rfl

/-- 中文说明：终端策略（§5.3 候选 A）：`conclusive` 取**整个论点集**，
    推定／妨碍／反证三支置空，`admissibleSupport` 恒真。
    法律读法：本案每条主张都有明文规则直接指定采纳，无推定、无妨碍、无相反证据。
    注意候选 B（`round := card univ`）按 §5.3 会退化回 A：`adoptedStep`
    （`AdjudicationBridge.lean:165`）含 `F` 没有的三项法律材料，要重合必须外加真空条件，
    故本件直接取 `round = 0`。 -/
def polM : TerminalPolicy aafM where
  admissibleSupport := fun _ => true
  conclusive := aafM.args
  presumed := ∅
  obstructed := ∅
  contraryEvidence := ∅

/-- 中文说明：本实例的争议论点（`UnifiedModel.disputed` 栏）。 -/
def disputedM : Arg := claimReduction

/-- 中文证明（技术引理，对任意框架成立）：攻击边为空 ⇒ 每个论点的攻击者集为空。
    `DungAAF.attackers aaf a`（`DungDefinitions.lean:24`）就是 `aaf.args` 按"攻击 `a`"来筛，
    边集空则该筛必空。 -/
theorem attackers_eq_empty_of_attacks_empty (aaf : DungAAF) (a : Arg)
    (h : aaf.attacks = (∅ : Finset (Arg × Arg))) : DungAAF.attackers aaf a = ∅ := by
  refine (Finset.eq_empty_iff_forall_notMem (s := DungAAF.attackers aaf a)).mpr ?_
  intro b hb
  have hb' : (b, a) ∈ aaf.attacks := (Finset.mem_filter.mp hb).2
  rw [h] at hb'
  exact absurd hb' (notMemEmptyFinset (b, a))

/-- 中文证明（技术引理，`policyClosed` 的技术核）：攻击边为空 ⇒ `F aaf S` 对**任何** `S`
    都等于论点集——`DungDefinitions.lean:30` 的判定式"每个攻击者都被 `S` 打回"因攻击者集空而
    **真空成立**。工程说明：用 `Finset.ext` 手工展开成员刻画，不用 `decide`——
    本 pin 的 `decide` 穿不过 `Finset.filter` 的 `Decidable.rec`。 -/
theorem F_eq_args_of_attacks_empty (aaf : DungAAF) (S : Finset Arg)
    (h : aaf.attacks = (∅ : Finset (Arg × Arg))) : DungAAF.F aaf S = aaf.args := by
  refine Finset.ext ?_
  intro a
  refine ⟨fun ha => (Finset.mem_filter.mp ha).1, fun ha => Finset.mem_filter.mpr ⟨ha, ?_⟩⟩
  intro b hb
  have hba : DungAAF.attackers aaf a = ∅ := attackers_eq_empty_of_attacks_empty aaf a h
  rw [hba] at hb
  exact absurd hb (notMemEmptyFinset b)

/-- 中文证明（技术引理）：`F` 恒等于论点集 ⇒ 迭代从第 1 层起就是论点集。 -/
theorem iter_pos_eq_args (aaf : DungAAF) (hF : ∀ T, DungAAF.F aaf T = aaf.args) :
    ∀ n : Nat, FiniteMonotoneSystem.iter (DungAAF.aafSystem aaf) (n + 1) = aaf.args := by
  intro n
  induction n with
  | zero =>
      show (DungAAF.aafSystem aaf).step
        (FiniteMonotoneSystem.iter (DungAAF.aafSystem aaf) 0) = aaf.args
      rw [FiniteMonotoneSystem.iter_zero]
      show DungAAF.F aaf (∅ : Finset Arg) = aaf.args
      exact hF ∅
  | succ k ih =>
      show (DungAAF.aafSystem aaf).step
        (FiniteMonotoneSystem.iter (DungAAF.aafSystem aaf) (k + 1)) = aaf.args
      rw [ih]
      show DungAAF.F aaf aaf.args = aaf.args
      exact hF aaf.args

/-- 中文证明（技术引理）：攻击边为空 ⇒ **接地集等于论点集**。
    路线：`F` 恒等论点集（上一条）⇒ 第 1 层起迭代停在论点集；`args = ∅` 时两侧同退化。
    分两个方向讲清楚：`grounded_is_least_fixed_point` 只给 `grounded ⊆ args`（反方向），
    本条要的是 `args ⊆ grounded`，故必须走迭代下界而不是最小不动点。 -/
theorem grounded_eq_args_of_attacks_empty (aaf : DungAAF)
    (h : aaf.attacks = (∅ : Finset (Arg × Arg))) : DungAAF.grounded aaf = aaf.args := by
  have hF : ∀ T, DungAAF.F aaf T = aaf.args := fun T => F_eq_args_of_attacks_empty aaf T h
  unfold DungAAF.grounded
  show FiniteMonotoneSystem.iter (DungAAF.aafSystem aaf) (Finset.card aaf.args) = aaf.args
  rcases Nat.eq_zero_or_pos (Finset.card aaf.args) with hcard | hpos
  · have hargs : aaf.args = ∅ := (Finset.card_eq_zero.mp hcard)
    rw [hargs, Finset.card_empty, FiniteMonotoneSystem.iter_zero]
  · obtain ⟨k, hk⟩ : ∃ k, Finset.card aaf.args = k + 1 :=
      Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
    rw [hk]
    exact iter_pos_eq_args aaf hF k

/-- 中文证明（技术引理）：第 0 层采纳集恰是论点集。
    `baseSet`（`AdjudicationBridge.lean:143`）的谓词是"不被妨碍 ∧（明文 ∨（推定 ∧ 无反证攻击））"；
    本策略妨碍集空、明文集＝论点集，故谓词对每个论点都真。 -/
theorem baseSet_polM_eq_args : baseSet polM = aafM.args := by
  refine Finset.ext ?_
  intro a
  refine ⟨fun ha => (Finset.mem_filter.mp ha).1,
    fun ha => Finset.mem_filter.mpr ⟨ha, ⟨fun h => notMemEmptyFinset a h, Or.inl ha⟩⟩⟩

/-- 中文证明（**交付项 2 之一**）：`policyClosed polM 0`——第 0 层采纳集对 Dung 算子 `F` 封闭。
    链条：`policyClosed` 展开 → `rounds_zero_fst`（`:178`，第 0 层＝`baseSet`）→
    `baseSet_polM_eq_args` → `F_eq_args_of_attacks_empty`。
    这是 `UnifiedModel.hPolicyClosed`（`Seams/Unified.lean:106`）那一栏在本实例上的证明。 -/
theorem policyClosed_polM_zero : policyClosed polM 0 := by
  show DungAAF.F aafM (rounds polM 0).1 = (rounds polM 0).1
  rw [rounds_zero_fst, baseSet_polM_eq_args]
  exact F_eq_args_of_attacks_empty aafM aafM.args aafM_attacks_eq_empty

/-- 中文证明（**交付项 2 之二**）：`baseInGrounded polM`——基底采纳集落在接地集内。
    两头都等于论点集，故 inclusion 是同一集合含于自身。
    对照：`cycle2Policy` 填不了这一栏，因为它两头分别是 `{p}`（`:601`）与 `∅`（`:636`）。 -/
theorem baseInGrounded_polM : baseInGrounded polM := by
  intro a ha
  rw [baseSet_polM_eq_args] at ha
  rw [grounded_eq_args_of_attacks_empty aafM aafM_attacks_eq_empty]
  exact ha

/-- 中文证明：基底无冲突片段（`UnifiedModel.hBaseConflictFree` 那一栏）——
    攻击边为空，任何两个被采纳的论点之间都没有攻击。 -/
theorem baseConflictFree_polM : baseConflictFree polM := by
  intro a a' _ _
  show ((a, a') : Arg × Arg) ∉ (∅ : Finset (Arg × Arg))
  exact notMemEmptyFinset (a, a')

/-- 中文证明：本实例的 L2 层不是空转——争议论点确在接地集内，
    故 `grounded_equivalence`（`:567`）在本实例上两侧都有内容。 -/
theorem disputedM_is_grounded : disputedM ∈ DungAAF.grounded aafM := by
  rw [grounded_eq_args_of_attacks_empty aafM aafM_attacks_eq_empty]
  exact Finset.mem_insert_self claimReduction {claimNoAdjustment}

/-- 中文证明：本实例的 L2 层**不退化**——论点集里确实有两个不同对象。 -/
theorem aafM_args_has_two_distinct :
    ∃ a b : Arg, a ∈ aafM.args ∧ b ∈ aafM.args ∧ a ≠ b :=
  ⟨claimReduction, claimNoAdjustment, by decide, by decide, claimReduction_ne_noAdjustment⟩

end AdjudicationLayer

/-! ## 四、L5／L7／XT／XU 各栏的字面见证 -/

section OtherLayers

/-- 中文说明：XU 栏的质量载体（`Fin 2 → ℚ`，与契约的字段类型一致）。
    法律读法：两个状态等权的先验心证，不认定任何真实概率。 -/
def weightM : Fin 2 → ℚ := fun _ => (1 : ℚ) / 2

/-- 中文证明：质量处处为正（`hWeightPos` 栏）。`ℚ` 上的不等式走 `norm_num`，不赌 `decide`。 -/
theorem weightM_pos : ∀ a : Fin 2, (0 : ℚ) < weightM a :=
  fun _ => show (0 : ℚ) < (1 : ℚ) / 2 from by norm_num

/-- 中文证明：质量归一（`hWeightTotal` 栏）。走 `Fin.sum_univ_two` 把两点求和展成加法，
    再算 `ℚ`——不引入任何新的求和机器。 -/
theorem weightM_total : ∑ a : Fin 2, weightM a = (1 : ℚ) := by
  rw [Fin.sum_univ_two]
  show (1 : ℚ) / 2 + (1 : ℚ) / 2 = (1 : ℚ)
  norm_num

/-- 中文说明：XU 栏的污染案例（§5.1 登记：`Uncertainty.ContaminatedCase :344` 全仓无闭合实例）。
    法律读法：两份证据，一份干净一份受污染，质量各为一。 -/
def contaminatedM : Uncertainty.ContaminatedCase where
  inputs := [{ subject := "doc-1", taint := Taint.clean },
             { subject := "doc-2", taint := Taint.tainted }]
  weight := fun _ => (1 : ℚ)

/-- 中文证明：`PrecedentFlow.envOld` 的版本表只有一个元素 `oldV`
    （`rw` 的匹配只做到可约化展开，穿不过 `envOld.versions` 这一投影，故先用 `simpa` 归一）。 -/
theorem mem_envOld {v : SourceVersionRecord} (hv : v ∈ PrecedentFlow.envOld.versions) :
    v = PrecedentFlow.oldV := by
  simpa [PrecedentFlow.envOld] using hv

/-- 中文证明（**新造的 L7 栏**）：`EnvWf` 的闭合见证。§5.1 登记此栏全仓零闭合实例。
    逐支内容：①原环境唯一记录 `oldV` 的区间良态（右端 `none` ⇒ 该式就是 `True`）；
    ②新记录 `newV` 区间良态（同样右端 `none`）；③新记录登记时为 `active`；
    ④新快照不在原环境里（两条 `LegalId` 的 payload 是不同字符串字面量）；
    ⑤新记录的快照就是决策声明的新快照。 -/
def envWfDemo : PrecedentFlow.EnvWf PrecedentFlow.envOld PrecedentFlow.demoAuthorized where
  intervals := by
    intro v hv
    have hv' : v = PrecedentFlow.oldV := mem_envOld hv
    subst hv'
    exact trivial
  newRecordValid := trivial
  newRecordActive := rfl
  fresh := by
    intro v hv
    have hv' : v = PrecedentFlow.oldV := mem_envOld hv
    subst hv'
    intro h
    exact absurd h (by decide)
  recordMatchesSnapshot := rfl

end OtherLayers

/-! ## 五、闭合项 `instanceM : UnifiedModel (Fin 3) (Fin 1)`（§5.1 字段方案·交付项 3） -/

section ClosedInstance

/-- 中文说明：**本件声明的观测**（`Representation.Fragment` 形制，载体取真实法律对象层
    `ClaimBasis.Status`）。观测指标只有一个（`Fin 1`），取值是 `Bool`：
    "行使段障碍除去（第580条式的障碍被排除）能否改变该法律地位"。
    `statusObsM.obs` 的**材料**取自仓内裁决表 `ClaimBasis.fires :95`，
    但**声明**这一动作发生在本件、并落在下面的字段 `observation` 上——
    §5.4 不许的是把 `fires` 这个别文件的 def 直接顶替成"𝔐 声明的观测"，本件不那么做。
    位置说明：因 `Seams/Unified.lean` 的 `UnifiedModel` 新增 `observation` 栏（Owner 授权的
    契约增量），本定义须先于 `instanceM` 出现，故从 §六**整体上移到此处**；**定义体一字未改**，
    §六 的读数与定理仍按原名 `statusObsM` 引用本件这一份声明。 -/
def statusObsM : Representation.Fragment ClaimBasis.Status where
  β := ClaimBasis.Status
  ι := Fin 1
  γ := Bool
  obs := fun _ s =>
    ClaimBasis.fires s ClaimBasis.Stage.exercisable ClaimBasis.Polarity.defuse true
  enc := id
  dec := id

/-- **统一模型 𝔐 的诚实闭合项**（G5 的判定对象：`UnifiedModel` 第一次有闭合项）。
    每一栏都写字面见证或被证明成立的片段，缺任一条都构造不出来。
    载体选择按契约原样：`V := Fin 3`（评价域候选结论）、`Rel := Fin 1`（机构效果关系），
    与 `Seams/Unified.lean:31` 登记的"错位登记 #1–#7"一致——本件不假装这些载体彼此相等。

    法律读法（夹具，逐栏）：
    * `norms/atom`：L1 的正 Horn 片段与待判原子（§四的 `normsM`）；
    * `aaf/pol/round`：L2 无例外攻击边、全部论点被明文规则采纳、第 0 层（§5.3 候选 A）；
    * `evalDom/candidate`：L2 评价通道——恰一个可采纳评价，候选结论取 `0`；
    * `ledger/…`：L5 空账本与一次成立、一次履行的事件材料；
    * `env/ad/hwf/…`：L7 前例环境与**被证明良构**的更新入口；`production` 取**未授权**产出，
      与契约里 `hUnauthorized` 那一栏相符；
    * `asOf/past/future₁/future₂/someLate`：XT 只有一条 `Int` 时间线（错位登记 #6 的实例）；
    * `weight/truthAssessment/hWeightPos/hWeightTotal`：XU 在 `ℚ` 上的等权心证；
    * `contaminated`：XU 的污染案例（本件新造）；
    * `observation`：𝔐 **自己声明**的观测族，本件交 `statusObsM`——
      契约增量那一栏，非退化性（`instanceM_nondegenerate`）就读它，不再读模型外面的槽。 -/
def instanceM : UnifiedModel (Fin 3) (Fin 1) where
  norms := normsM
  atom := atomM
  aaf := aafM
  pol := polM
  disputed := disputedM
  hBaseConflictFree := baseConflictFree_polM
  round := 0
  hPolicyClosed := policyClosed_polM_zero
  hBaseInGrounded := baseInGrounded_polM
  evalDom := verdictDomain
  candidate := 0
  hAdmissibleNonempty := verdictDomain_admissibleNonempty
  hCollapse := verdictDomain_collapse
  ledger := []
  eventId := "e-form-1"
  relFormed := 0
  relObserved := 0
  performEventId := "e-perf-1"
  obligor := "obligor-1"
  performAmount := 100
  env := PrecedentFlow.envOld
  ad := PrecedentFlow.demoAuthorized
  hwf := envWfDemo
  atDay := 60
  production := PrecedentFlow.lowerCourtDraft
  hUnauthorized := PrecedentFlow.lower_court_draft_unauthorized
  asOf := 60
  past := [(0, 0)]
  future₁ := [(70, 1)]
  future₂ := [(71, 0)]
  hFuture₁ := by
    intro x hx
    have hx' : x = (70, 1) := by simpa using hx
    subst hx'
    decide
  hFuture₂ := by
    intro x hx
    have hx' : x = (71, 0) := by simpa using hx
    subst hx'
    decide
  someLate := (-5, 0)
  weight := weightM
  truthAssessment := fun _ => ⟨true, KernelV3.Judgment.established⟩
  hWeightPos := weightM_pos
  hWeightTotal := weightM_total
  contaminated := contaminatedM
  observation := statusObsM

/-- 中文证明：闭合项的 `hCollapse` 栏（换个角度重述，便于按栏引用）。 -/
theorem instanceM_collapse : collapsesToKernel instanceM.evalDom := verdictDomain_collapse

/-- 中文证明：闭合项的评价非空栏。 -/
theorem instanceM_admissibleNonempty : ∃ S : Set (Fin 3), Admissible instanceM.evalDom S :=
  verdictDomain_admissibleNonempty

/-- 中文证明：闭合项的 `policyClosed` 栏（第 0 层）。 -/
theorem instanceM_policyClosed : policyClosed instanceM.pol instanceM.round :=
  policyClosed_polM_zero

/-- 中文证明：闭合项的 `baseInGrounded` 栏。 -/
theorem instanceM_baseInGrounded : baseInGrounded instanceM.pol := baseInGrounded_polM

/-- 中文证明（**G5 的判定式**）：闭合项确实存在，且四条片段在它身上同时成立。
    这四条此前在全仓**没有任何闭合实例**（§5.1 登记：`EnvWf`、`contaminated` 零闭合实例，
    `policyClosed`/`baseInGrounded`/`collapsesToKernel` 三栏无人满足）。 -/
theorem unified_model_has_closed_inhabitant :
    ∃ M : UnifiedModel (Fin 3) (Fin 1),
      collapsesToKernel M.evalDom ∧ (∃ S : Set (Fin 3), Admissible M.evalDom S) ∧
        policyClosed M.pol 0 ∧ baseInGrounded M.pol :=
  ⟨instanceM, instanceM_collapse, instanceM_admissibleNonempty, policyClosed_polM_zero,
    baseInGrounded_polM⟩

/-- 中文证明（**接上 T2**）：闭合项喂进主定理——T2 的五条合取支在**这一个** 𝔐 上同时成立。
    证明项就是 `Seams/Unified.lean:236` 的原定理作用于 `instanceM`，本件不重证任何一支，
    也不改窄其陈述（契约文件一字未动）。 -/
theorem instanceM_satisfies_declared_fragment :
    UnifiedNonDegenerate ∧ UnifiedInterpretationPreserved (Fin 3) (Fin 1) instanceM ∧
      UnifiedChainCorrespondence (Fin 3) (Fin 1) instanceM ∧
        UnifiedFiniteProcessComposition (Fin 3) (Fin 1) instanceM ∧
          UnifiedTimeAndUncertaintyPreserved (Fin 3) (Fin 1) instanceM :=
  unified_legal_derivation_on_declared_fragment instanceM

end ClosedInstance

/-! ## 六、非退化**关于实例**：观测槽与它缺的那一环（§5.4·交付项 4） -/

section ObservationSlot

/-- 中文说明：第二个观测——登记侧只记"是否已入簿"，对这两个地位**不加区分**（常值 `false`）。
    它在本件只用于把"**加宽结构外层那一栏**观测不由 𝔐 决定"这件事证成定理
    （同一个 𝔐 载体可在**模型外面**再配一份不同的观测）。 -/
def statusObsRegister : Representation.Fragment ClaimBasis.Status where
  β := ClaimBasis.Status
  ι := Fin 1
  γ := Bool
  obs := fun _ _ => false
  enc := id
  dec := id

/-- 中文证明：`statusObsM` 双向忠实（往返＋覆盖）——它不是随手编的映射。 -/
theorem statusObsM_faithful : Representation.FaithfulRep statusObsM :=
  ⟨fun _ => rfl, fun b => ⟨b, rfl⟩⟩

/-- 中文证明：观测在"被阻却"地位上取值 `false`（裁决表的兜底行）。 -/
theorem statusObsM_value_suspended :
    statusObsM.obs (0 : Fin 1) ClaimBasis.Status.suspended = false := rfl

/-- 中文证明：观测在"存续但不得强制实现"地位上取值 `true`（裁决表第 580 条那一行）。 -/
theorem statusObsM_value_unenforceable :
    statusObsM.obs (0 : Fin 1) ClaimBasis.Status.unenforceable = true := rfl

/-- 中文证明：登记式常值观测对任何地位都取 `false`。 -/
theorem statusObsRegister_value_any (s : ClaimBasis.Status) :
    statusObsRegister.obs (0 : Fin 1) s = false := rfl

/-- 中文说明：**加宽契约**——照 §5.2 的分离口径在 𝔐 之外再挂一栏观测。
    本结构的**字段表未改**；但 `Seams/Unified.lean` 的 `UnifiedModel` 现已自带
    `observation` 栏（Owner 授权的契约增量），故外层这一栏与 `M.model.observation` 是
    **两个槽**，本件不再用它承担"非退化关于 𝔐"的读数（那条读数已搬进
    `UnifiedNonDegenerateOn`）。`model` 一支是降格，`liftWithObservation` 是升格，
    两者互逆到字段级，故加宽既不使任何既有陈述变弱，也不引入新前提
    （见 `widening_is_conservative`）。 -/
structure UnifiedModelObs (V Rel : Type) [DecidableEq Rel] where
  model : UnifiedModel V Rel
  observation : Representation.Fragment ClaimBasis.Status

/-- 中文说明：降格（加宽实例 → 原契约）。 -/
def forgetObservation (V Rel : Type) [DecidableEq Rel]
    (M : UnifiedModelObs V Rel) : UnifiedModel V Rel := M.model

/-- 中文说明：升格（原契约 + 一条观测声明 → 加宽实例）。 -/
def liftWithObservation (M : UnifiedModel (Fin 3) (Fin 1))
    (o : Representation.Fragment ClaimBasis.Status) : UnifiedModelObs (Fin 3) (Fin 1) :=
  { model := M, observation := o }

/-- 中文说明：**契约 (1')：非退化关于实例**。
    两个不同法律对象要被**该实例自己声明的观测**（`M.observation`）分开；
    分开者不来自实例外部（§5.4 的红线）。 -/
def ObservedNonDegenerate (V Rel : Type) [DecidableEq Rel]
    (M : UnifiedModelObs V Rel) : Prop :=
  ∃ (x y : ClaimBasis.Status) (i : M.observation.ι),
    x ≠ y ∧ M.observation.obs i x ≠ M.observation.obs i y

/-- 中文说明（**契约 (1'')：非退化关于 𝔐 本体**）：两个不同的法律对象（`ClaimBasis.Status`）
    要被**模型自己那一栏声明的观测**（`M.observation`）分开。
    这正是 §5.4 要的字段形陈述——增栏之前它"连写都写不出来"（`M.observation` 不存在），
    增栏之后它就是 𝔐 的读数，不再需要 `UnifiedModelObs` 作中介。
    与 `ObservedNonDegenerate` 的关系：逻辑内容同形（同一对对象、同一份声明观测），
    区别只在分开者取自**模型内**的栏位而非模型外的槽。 -/
def UnifiedNonDegenerateOn (V Rel : Type) [DecidableEq Rel]
    (M : UnifiedModel V Rel) : Prop :=
  ∃ (x y : ClaimBasis.Status) (i : M.observation.ι),
    x ≠ y ∧ M.observation.obs i x ≠ M.observation.obs i y

/-- 中文说明：本实例的加宽形态——𝔐 的闭合项 + 本件声明的观测。 -/
def instanceMObs : UnifiedModelObs (Fin 3) (Fin 1) :=
  { model := instanceM, observation := statusObsM }

/-- 中文证明（**交付项 4**）：非退化**关于 𝔐 本体**——分开者是 `instanceM.observation`，
    即模型**自己声明**的那一栏观测，不再是加宽结构外面的槽。
    对象是仓内两条真见证所用的法律地位——`suspended`（`ClaimBasis.lean:348` 的
    `witness_defense_suspends_not_extinguishes`）与 `unenforceable`（`:376` 的
    `witness_enforceability_blocked`），互异由 `status_five_labels_pairwise_distinct :187` 交出。
    本条与增栏前的版本**同内容**：那条读 `instanceMObs.observation`，本条读
    `instanceM.observation`，而 `instanceM.observation` 就是本件声明的 `statusObsM`
    （见 `instanceMObs_nondegenerate` 把旧读数原样保留为推论）；证明项一字未改。 -/
theorem instanceM_nondegenerate :
    UnifiedNonDegenerateOn (Fin 3) (Fin 1) instanceM := by
  obtain ⟨_, _, _, _, _, _, _, _, hne, _⟩ := ClaimBasis.status_five_labels_pairwise_distinct
  refine ⟨ClaimBasis.Status.suspended, ClaimBasis.Status.unenforceable, (0 : Fin 1), hne, ?_⟩
  show statusObsM.obs (0 : Fin 1) ClaimBasis.Status.suspended ≠
      statusObsM.obs (0 : Fin 1) ClaimBasis.Status.unenforceable
  rw [statusObsM_value_suspended, statusObsM_value_unenforceable]
  intro h
  cases h

/-- 中文证明（**旧读数不丢**）：加宽实例上的非退化仍在——它现在只是 𝔐 本体那条读数的
    同一个命题换了写法（两个 `observation` 槽在本实例上都是 `statusObsM`）。 -/
theorem instanceMObs_nondegenerate :
    ObservedNonDegenerate (Fin 3) (Fin 1) instanceMObs :=
  instanceM_nondegenerate

/-- 中文证明（**字段形必要条件在本体上成立**）：观测既是 𝔐 的一栏数据，
    "模型相同 ⇒ 观测相同"就是投影的直接结果，不必经过加宽结构。
    注意本式**不等于**义务位 `instanceM_nondegenerate_obligation`：后者量化的是
    `UnifiedModelObs` **自己外层**那一栏观测，与本式不是同一个命题。 -/
theorem model_equality_determines_observation {V Rel : Type} [DecidableEq Rel]
    (M N : UnifiedModel V Rel) (h : M = N) : M.observation = N.observation := by
  cases h
  rfl

/-- 中文证明：加宽是**保守扩张**——任何加宽实例的 𝔐 投影照样满足 T2 的五条合取支，
    故"把观测做成 𝔐 的字段"不会使任何既有陈述变窄（§5.2 的字段↔参数同一命题口径）。 -/
theorem widening_is_conservative (M : UnifiedModelObs (Fin 3) (Fin 1)) :
    UnifiedNonDegenerate ∧ UnifiedInterpretationPreserved (Fin 3) (Fin 1) M.model ∧
      UnifiedChainCorrespondence (Fin 3) (Fin 1) M.model ∧
        UnifiedFiniteProcessComposition (Fin 3) (Fin 1) M.model ∧
          UnifiedTimeAndUncertaintyPreserved (Fin 3) (Fin 1) M.model :=
  unified_legal_derivation_on_declared_fragment M.model

/-- 中文证明（**缺口的具体证据**）：本件声明的观测与"登记式常值观测"在**同一个法律对象**上
    取值不同。𝔐 的数据（`instanceM` 的 38 栏）对这件事**没有任何说法**——
    同一个 𝔐 载体既可以配 `statusObsM` 也可以配 `statusObsRegister`，
    所以"观测由 𝔐 决定"（下一条义务）在当前契约里不成立。
    工程说明：这里刻意只比 `Bool` 取值，不比两份 `Fragment` 本身——
    `Fragment.obs` 的定义域 `f.ι` 依赖 `f`，`rw`/`congrFun` 在这种依赖槽上造不出动机
    （本 pin 实测：`motive is not type correct`），故避开而不是硬做。 -/
theorem observation_not_determined_by_the_model :
    statusObsM.obs (0 : Fin 1) ClaimBasis.Status.unenforceable ≠
      statusObsRegister.obs (0 : Fin 1) ClaimBasis.Status.unenforceable := by
  rw [statusObsM_value_unenforceable, statusObsRegister_value_any]
  intro h
  cases h

/-- 中文说明：**字段形要求的可表达形态**。"观测是 𝔐 的一栏数据"的必要条件是：
    模型相同 ⇒ 观测相同（观测由 𝔐 的数据决定）。
    本件把加宽实例的配对写成 `M.model` 与 `M.observation` 两栏，故此式可直接陈述。 -/
def observationDeterminedByModel (V Rel : Type) [DecidableEq Rel] : Prop :=
  ∀ M N : UnifiedModelObs V Rel, M.model = N.model → M.observation = N.observation

/-- 义务·**仍未闭合，且本次契约增量并不消解它**（G5 收尾·§5.4）。两面都要说清：
    ①**已闭合的一半**：`Seams/Unified.lean` 的 `UnifiedModel` 现带
      `observation : Representation.Fragment ClaimBasis.Status` 一栏（Owner 授权的契约增量），
      于是当初"连写都写不出来"的字段形陈述现在**写得出来也证得出来**——它就是
      `UnifiedNonDegenerateOn` 配 `instanceM_nondegenerate`，分开者读 `instanceM.observation`；
      本体的"模型相同 ⇒ 观测相同"也已证（`model_equality_determines_observation`）。
    ②**本义务本身留 `def … : Prop` 位，不含证明**。理由不是"没试"，而是**载体不同**：
      本式 `observationDeterminedByModel (Fin 3) (Fin 1)` 量化的是**加宽结构**
      `UnifiedModelObs` **自己外层**那一栏 `observation`，它与 `M.model.observation` 是两个槽；
      `liftWithObservation` 允许同一个 `model` 分别配 `statusObsM` 与 `statusObsRegister`，
      故外层栏仍不由 𝔐 决定。要在本式上交付，先得有 `statusObsM ≠ statusObsRegister`，
      而那一步仍被 `Fragment.obs` 的依赖槽挡住（本 pin 实测 `motive is not type correct`，
      见 `observation_not_determined_by_the_model` 的工程说明）。
      ⇒ 消解本式的动作是**让加宽结构退役**（调用方一律改读 `M.observation`，
      并把本式重述到 `UnifiedModel` 上，即 `model_equality_determines_observation` 那一形），
      那属于下一步的清理，不在本轮边界内；本轮**不删本义务、不给假证明**。 -/
def instanceM_nondegenerate_obligation : Prop :=
  observationDeterminedByModel (Fin 3) (Fin 1)

end ObservationSlot

end JurisLean.Seams.UnifiedInstance
