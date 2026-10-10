import Mathlib

/-
Unified trajectory state/kernel foundations (W1-2; master plan §W1-2, review
item 7 of docs/master-plan/20261010_接续方案评审_Codex_R1.md, spec §9.3).

The eight mandated obligations, and where each lives:

1. TRAJECTORY SPACE — `Traj State = Π n : ℕ, XConst State n`, the dependent
   product over the constant family `X n := State` (i.e. `ℕ → State`), exactly
   the shape the pinned Mathlib Ionescu-Tulcea development consumes
   (`ProbabilityTheory.Kernel.trajMeasure`; local source
   Mathlib/Probability/Kernel/IonescuTulcea/Traj.lean:762-791, whose index
   interval is `Finset.Iic` — the spelling used throughout this file).  Not a
   general function space: no `ℝ → ℕ` anywhere.
2. REAL STATE ENCODING — `State = Disc ⊕ Param`: a countable discrete syntactic
   identity layer (`Disc`, six procedure identities incl. the §9.3 diagnostic
   terminal `noLegalSelection`) and a finite-dimensional Borel parameter piece
   (`Param = Fin 3 → ℝ`).  The measurable space is induced by the sum
   structure.  `StandardBorelSpace` is PROVED for `Disc` (countable +
   discrete-measurable chain), for `Param` (countable-pi instance) and for the
   companion product encoding `StateP = Disc × Param` (product instance).  For
   the sum encoding itself mathlib has no `StandardBorelSpace (α ⊕ β)`
   instance and no `borel (α ⊕ β) = Sum.instMeasurableSpace` lemma at the
   pinned commit, so that single condition is carried as an EXPLICIT NAMED
   HYPOTHESIS in §八 (`condDistrib_boundary_stateFull`) — recorded open
   material, not faked.
3. STEP / OBSERVATION / POLICY MEASURABILITY — `discSucc` (discrete
   enumeration step), `paramStep` (finite comparison `v 0 ≤ v 1`, branch,
   addition), `step` (tag dispatch), `obs` (observation map), `policy`
   (observation-adapted strategy with the terminal absorbing branch); each
   carries a `Measurable` theorem.
4. INITIAL PROBABILITY — `mu0 = dirac (inl filing)` with an
   `IsProbabilityMeasure` instance, plus a constructive discrete-weighted
   variant from any `HasSum w 1` (`isProbabilityMeasure_weightedDirac`).
5. MARKOV KERNEL NORMALIZATION — `legalChain n` is a deterministic kernel with
   an `IsMarkovKernel` instance for every n; "each row has mass 1" IS the
   `IsMarkovKernel` semantics, stated pointwise in
   `legalChain_row_probability`.
6. CYLINDER / PROJECTION COMPATIBILITY — general projection lemma
   `compProd_projection` (consuming `Measure.fst_compProd`), the §9.3 recursion
   `legal_prefix_joint` (consuming the pinned
   `map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure`: the prefix
   measure composed with `κ b` equals the joint distribution of (prefix,
   next)), the projection back `legal_prefix_projection` (dropping the last
   coordinate returns the prefix measure), and the iterated-prefix structure
   `prefix_iterate_compose` (consuming `partialTraj_comp_partialTraj`).
7. TRAJECTORY EXISTENCE & UNIQUENESS — existence: probability instance on
   `trajMeasure μ₀ legalChain` after verifying every hypothesis of the pinned
   trajMeasure (markov chain + initial probability measure); uniqueness:
   `traj_unique_prefix` (consuming `eq_traj`); cylinder values
   `traj_prefix_value` (consuming `traj_map_frestrictLe_apply`); Markov
   property `traj_markov_property` (consuming `map_traj_succ_self`).
8. CONDITIONAL-DISTRIBUTION BOUNDARY — `condDistrib_boundary` states the exact
   applicability conditions of the pinned `condDistrib_trajMeasure` (target
   standard Borel + nonempty); satisfied-side readouts for Disc / Param /
   StateP; the empty target is the failing side (`nonempty_empty_target`);
   the full Sum-state needs the explicit hypothesis.  Per §9.3 the regular
   conditional distribution is claimed only μ-a.s. (the `=ᵐ` in the
   statement) — never pointwise on zero-mass events.

Scope, honestly: this module wires the pinned mathlib Ionescu-Tulcea machinery
onto a concrete legal state space and proves every hypothesis it consumes.
It does NOT reprove Ionescu-Tulcea (consumed from mathlib); it does not give
the Sum-encoded `State` a `StandardBorelSpace` instance (the missing
`borel_sum`-type material is recorded, a named hypothesis instead); the
concrete maps `discSucc`/`paramStep`/`policy` are an illustrative legal
reading (acceptance→merits→judgment→enforcement→remedy→diagnostic-terminal,
with amount growth by an increment under a threshold) — the deliverable is the
measurability of the shape, not the choice of rule; the §9.3 nonempty-fiber
selection kernel (a genuinely normalized measurable selection, not the Dirac
absorption used here) remains a separately-wired obligation; and no claim is
made about conditioning on zero-probability events beyond the μ-a.s. `=ᵐ`
statements.

STATUS: theorems pending their CI compile round; this file contains no sorry,
no admit, no custom axiom, no `: True :=` placeholder.
-/

namespace JurisLean.Seams.UnifiedTrajectory

open MeasureTheory ProbabilityTheory Preorder
open scoped ProbabilityTheory ENNReal

/-! ## 一、轨迹空间：依赖积 Π n : ℕ, X n（第 1 项） -/

/-- 常值状态族：`X n := State`。依赖积 `Π n : ℕ, X n` 正是锁定提交
`Mathlib/Probability/Kernel/IonescuTulcea/Traj.lean` 中 `trajMeasure` 消费的形状。
显式不用一般全函数空间（`ℝ → ℕ` 等）。 -/
@[reducible]
def XConst (S : Type) : ℕ → Type := fun _ => S

/-- 轨迹空间＝依赖积。 -/
def Traj (S : Type) : Type := Π n : ℕ, XConst S n

/-- 轨迹空间就是该依赖积（恒等读出）。 -/
example : Traj State = (Π n : ℕ, XConst State n) := rfl

/-- 常值族下依赖积即 `ℕ → State`（评审第 7 条要求的形态）。 -/
example : (Π n : ℕ, XConst State n) = (ℕ → State) := rfl

/-! ## 二、真实状态编码（第 2 项） -/

/-- 可数离散语法身份层：受理→实体审理→裁判→执行→救济，加 §9.3 的
独立诊断终态 `noLegalSelection`（无合法选择时 Dirac 进入、保持质量、不映为胜负）。 -/
inductive Disc where
  | filing          -- 受理登记
  | merits          -- 实体审理
  | judgment        -- 裁判作出
  | enforcement     -- 执行
  | remedy          -- 救济/再审
  | noLegalSelection -- §9.3 诊断终态
  deriving DecidableEq

/-- 离散层的可测结构：幂集（可数离散身份的标准读法）。 -/
instance : MeasurableSpace Disc := ⊤

/-- 单点可测（幂集下平凡）。 -/
instance : MeasurableSingletonClass Disc := ⟨fun _ => trivial⟩

/-- 全体可测（幂集下平凡；直接具名声明，避免依赖 ⊤ 实例的展开匹配）。 -/
instance : DiscreteMeasurableSpace Disc := ⟨fun _ => trivial⟩

/-- 显式枚举编码，证可数。 -/
def enc : Disc → ℕ
  | .filing => 0
  | .merits => 1
  | .judgment => 2
  | .enforcement => 3
  | .remedy => 4
  | .noLegalSelection => 5

theorem enc_injective : Function.Injective enc := by
  intro a b h
  cases a <;> cases b <;> simp_all [enc]

/-- Disc 可数：单射入 ℕ 直接给出 `Countable`（定义场 `exists_injective_nat'`）。 -/
instance instCountableDisc : Countable Disc := ⟨enc, enc_injective⟩

/-- 实参数片：有限维（k = 3）Borel 域。第 0 分量取"债权额/本金"，第 1 分量取
"对照阈值"，第 2 分量取"增量（迟延步长）"；具体语义为示意，交付物是形状可测性。 -/
abbrev Param := Fin 3 → ℝ

/-- 真实状态 = 离散语法身份 ⊕ 实参数 Borel 片（spec §9.3 的可数并读法）。
可测空间由 sum 结构诱导。 -/
abbrev State := Disc ⊕ Param

/-- 乘积编码伴随物：每个状态同时携带语法身份与实参数。
它整链无条件满足标准 Borel（见 §八 `condDistrib_boundary_stateP`）。 -/
abbrev StateP := Disc × Param

/-- 常值族上的可测结构（trajMeasure 的 `∀ n, MeasurableSpace (X n)` 前提）。 -/
instance measXConstState : ∀ n : ℕ, MeasurableSpace (XConst State n) := fun _ => inferInstance

instance measXConstStateP : ∀ n : ℕ, MeasurableSpace (XConst StateP n) := fun _ => inferInstance

/-! ### 实例可用性核对读出 -/

/-- Disc 标准 Borel：可数 ＋ 离散可测（`standardBorelSpace_of_discreteMeasurableSpace` 链）。 -/
theorem disc_standardBorel : StandardBorelSpace Disc := by infer_instance

/-- Param 标准 Borel：可数指标积（`StandardBorelSpace.pi_countable` ＋ `BorelSpace ℝ`）。 -/
theorem param_standardBorel : StandardBorelSpace Param := by infer_instance

/-- 乘积编码标准 Borel：`StandardBorelSpace.prod` 实例。 -/
theorem stateP_standardBorel : StandardBorelSpace StateP := by infer_instance

/- **如实记录的开放点**：mathlib 在锁定提交处没有 `StandardBorelSpace (α ⊕ β)` 实例，
也没有 `borel (α ⊕ β) = Sum.instMeasurableSpace` 型引理；因此 Sum 编码全状态的标准 Borel
条件在本模块中以显式具名假设传递（§八 `condDistrib_boundary_stateFull`），不伪造实例。 -/

/-! ## 三、步 / 观察 / 策略可测性（第 3 项） -/

noncomputable section

/-- 离散确定性子步：程序序列的固定后继；诊断终态吸收。 -/
def discSucc : Disc → Disc
  | .filing => .merits
  | .merits => .judgment
  | .judgment => .enforcement
  | .enforcement => .remedy
  | .remedy => .noLegalSelection
  | .noLegalSelection => .noLegalSelection

/-- 离散子步可测（离散可测域上任意函数可测）。 -/
theorem measurable_discSucc : Measurable discSucc := Measurable.of_discrete

/-- 实参数确定性子步：**有限比较**（`v 0 ≤ v 1`）＋**分支**（ite）＋**代数运算**（加法）：
阈值之下则各分量增加增量，否则不动。 -/
def paramStep (v : Param) : Param := fun i =>
  if v 0 ≤ v 1 then v i + v 2 else v i

/-- 实参数子步可测：比较的可测集（`measurableSet_le`）分支（`Measurable.ite`）
加法（`Measurable.add`）。 -/
theorem measurable_paramStep : Measurable paramStep := by
  refine measurable_pi_lambda paramStep fun i => ?_
  exact Measurable.ite (measurableSet_le (measurable_pi_apply 0) (measurable_pi_apply 1))
    ((measurable_pi_apply i).add (measurable_pi_apply 2)) (measurable_pi_apply i)

/-- 确定性推前 `Step`：按 tag 分派（Sum.elim）。 -/
def step : State → State :=
  Sum.elim (fun d => Sum.inl (discSucc d)) (fun v => Sum.inr (paramStep v))

/-- 推前可测：两支各自可测，`Measurable.sumElim` 合成。 -/
theorem measurable_step : Measurable step :=
  (measurable_inl.comp measurable_discSucc).sumElim
    (measurable_inr.comp measurable_paramStep)

/-- **观察映射**：报告状态的语法身份。离散态报告自身（恒等支）；纯参数态处于
实体审理片，报告 `merits`。 -/
def obs : State → Disc := Sum.elim id (fun _ => Disc.merits)

/-- **观察映射可测性定理**。 -/
theorem measurable_obs : Measurable obs :=
  measurable_id.sumElim measurable_const

/-- **观察适应策略**：观察到诊断终态身份时保持状态不动（§9.3 诊断终态吸收，
质量不删、不映为胜负）；否则按确定性推前走一步。§9.3 的"非空纤维可测归一选择核"
（真正的合法选择核）另接，此处交付策略映射可测性。 -/
def policy : Disc → State → State := fun d s =>
  if d = Disc.noLegalSelection then s else step s

/-- **策略映射可测性定理**（联合可测：观察 × 状态 → 状态）。 -/
theorem measurable_policy : Measurable fun p : Disc × State => policy p.1 p.2 := by
  have hcond : MeasurableSet {p : Disc × State | p.1 = Disc.noLegalSelection} :=
    measurable_fst (measurableSet_singleton Disc.noLegalSelection)
  have hf : Measurable (Prod.snd : Disc × State → State) := measurable_snd
  have hg : Measurable fun p : Disc × State => step p.2 :=
    measurable_step.comp measurable_snd
  exact Measurable.ite hcond hf hg

/-- 策略映射逐观察可测（策略是观察适应的）。 -/
theorem measurable_policy_apply (o : Disc) : Measurable (policy o) := by
  by_cases h : o = Disc.noLegalSelection
  · show Measurable fun s => if o = Disc.noLegalSelection then s else step s
    rw [if_pos h]
    exact measurable_id'
  · show Measurable fun s => if o = Disc.noLegalSelection then s else step s
    rw [if_neg h]
    exact measurable_step

/-- 完整转移：观察 → 策略 → 推前。 -/
def next : State → State := fun s => step (policy (obs s) s)

/-- 转移可测。 -/
theorem measurable_next : Measurable next :=
  measurable_step.comp (measurable_policy.comp (measurable_obs.prodMk measurable_id))

end

/-! ## 四、初始概率（第 4 项） -/

noncomputable section

/-- 初始分布：Dirac 于受理态（离散身份 `filing`，参数全零）。 -/
def mu0 : Measure State := Measure.dirac (Sum.inl Disc.filing)

instance mu0_isProbabilityMeasure : IsProbabilityMeasure mu0 :=
  Measure.dirac.isProbabilityMeasure

/-- **构造性离散加权初始分布**：任给权和为 1 的非负权 `w`，把质量放在
离散身份层上（`w d • dirac (inl d)` 的可数和）得到初始概率。 -/
theorem isProbabilityMeasure_weightedDirac {w : Disc → ℝ≥0∞} (hw : HasSum w 1) :
    IsProbabilityMeasure (Measure.sum fun d : Disc => w d • Measure.dirac (Sum.inl d : State)) :=
  HasSum.isProbabilityMeasure_sum_dirac_ennreal hw

/-! ## 五、Markov 核归一（第 5 项） -/

/-! ### 一般确定性链构造 -/

/-- 末坐标上的转移步（`chainOn` 的确定性核体；index interval 取 mathlib
Ionescu-Tulcea 开发所用的 `Finset.Iic`）。 -/
def stepOn {S : Type} [MeasurableSpace S] (next : S → S) (hnext : Measurable next) (n : ℕ) :
    (Π i : Finset.Iic n, XConst S i) → S :=
  fun h => next (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩)

/-- 末坐标转移可测。 -/
theorem measurable_stepOn {S : Type} [MeasurableSpace S] (next : S → S) (hnext : Measurable next)
    (n : ℕ) :
    Measurable fun h : Π i : Finset.Iic n, XConst S i =>
      next (h (⟨n, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic n)) :=
  hnext.comp (measurable_pi_apply (⟨n, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic n))

/-- 一般确定性链：给定任意可测状态空间 `S` 上的可测转移 `next`，
返回 Ionescu–Tulcea 机制消费的 κ 族——第 n 核从"至时刻 n 的前缀"出发，
在末坐标上施加转移的确定性核。 -/
def chainOn {S : Type} [MeasurableSpace S]
    (next : S → S) (hnext : Measurable next) (n : ℕ) :
    Kernel (Π i : Finset.Iic n, XConst S i) (XConst S (n + 1)) :=
  Kernel.deterministic (stepOn next hnext n) (measurable_stepOn next hnext n)

/-- 一般确定性链的 Markov 归一：每行都是概率测度。 -/
instance chainOn_isMarkovKernel {S : Type} [MeasurableSpace S]
    (next : S → S) (hnext : Measurable next) (n : ℕ) :
    IsMarkovKernel (chainOn next hnext n) :=
  Kernel.isMarkovKernel_deterministic (stepOn next hnext n) (measurable_stepOn next hnext n)

/-! ### 法律链 -/

/-- 法律转移核链：`legalChain n` 把确定性推前 `next` 施加在前缀末坐标上。 -/
def legalChain (n : ℕ) :
    Kernel (Π i : Finset.Iic n, XConst State i) (XConst State (n + 1)) :=
  chainOn next measurable_next n

/-- 法律链逐核 Markov（`∀ n` 形实例，trajMeasure 的前提）。 -/
instance legalChain_isMarkovKernel : ∀ n : ℕ, IsMarkovKernel (legalChain n) :=
  chainOn_isMarkovKernel next measurable_next

/-- **「每行质量 1」的逐点读出**：`IsMarkovKernel` 的语义正是逐行概率测度——
这就是 §9.3 "每行质量 1 来自各核归一"的形式化（非假设：由确定性核构造性成立）。 -/
theorem legalChain_row_probability (n : ℕ) (h : Π i : Finset.Iic n, XConst State i) :
    IsProbabilityMeasure (legalChain n h) := inferInstance

/-! ## 六、柱集投影对应（第 6 项） -/

/-- **一般投影引理**（消费 mathlib `Measure.fst_compProd`）：有限前缀测度递推
`μ_{n+1} = μ_n ⊗ₘ P(·,·)` 中，投影掉末坐标回到 `μ_n`——由 Markov 核归一
`P(h, S) = 1` 保证，对任意 s-finite 初始测度与 Markov 核成立。 -/
theorem compProd_projection {H S : Type} [MeasurableSpace H] [MeasurableSpace S]
    (μ : Measure H) [SFinite μ] (P : Kernel H S) [IsMarkovKernel P] :
    (Measure.compProd μ P).map Prod.fst = μ :=
  Measure.fst_compProd μ P

section Traj

variable (μ₀ : Measure State) [IsProbabilityMeasure μ₀]

/-- **§9.3 有限前缀测度递推**（消费锁定提交的
`map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure`）：前缀测度与第 b 核的
compProd 等于 (前缀, 下一状态) 的联合分布——即 `μ_{b+1}(A × B) = ∫_A P(h, B) dμ_b(h)`。 -/
theorem legal_prefix_joint (b : ℕ) :
    Measure.compProd ((Kernel.trajMeasure μ₀ legalChain).map (frestrictLe b)) (legalChain b)
      = (Kernel.trajMeasure μ₀ legalChain).map
          (fun x : Π n, XConst State n => (frestrictLe b x, x (b + 1))) :=
  Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure (a := b)

/-- **投影相容（丢末坐标回到 μ_b）**：联合分布投影回前缀即前缀测度——
由 `compProd_projection`（即 mathlib `Measure.fst_compProd`）给出。 -/
theorem legal_prefix_projection (b : ℕ) :
    (Measure.compProd ((Kernel.trajMeasure μ₀ legalChain).map (frestrictLe b))
        (legalChain b)).map Prod.fst
      = (Kernel.trajMeasure μ₀ legalChain).map (frestrictLe b) := by
  show Measure.fst (Measure.compProd _ _) = _
  exact Measure.fst_compProd _ _

/-- **遍历结构**（消费 `partialTraj_comp_partialTraj`）：有限前缀测度的迭代拼接
（a≤b≤c）：先到 b 再到 c 的前缀分布等于直接到 c 的前缀分布。 -/
theorem prefix_iterate_compose (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    Kernel.partialTraj legalChain b c ∘ₖ Kernel.partialTraj legalChain a b
      = Kernel.partialTraj legalChain a c :=
  Kernel.partialTraj_comp_partialTraj (κ := legalChain) hab hbc

/-- 柱集值读出：从给定点 `x₀` 出发的轨迹测度限制到前 b 位即有限前缀测度。 -/
theorem traj_prefix_value (x₀ : Π i : Finset.Iic 0, XConst State i) (b : ℕ) :
    (Kernel.traj legalChain 0 x₀).map (frestrictLe b)
      = Kernel.partialTraj legalChain 0 b x₀ :=
  Kernel.traj_map_frestrictLe_apply (κ := legalChain) 0 b x₀

/-! ## 七、轨迹存在唯一（第 7 项） -/

/-- **存在性**：trajMeasure 的全部假设已在本模块验证——
`legalChain_isMarkovKernel : ∀ n, IsMarkovKernel (legalChain n)`（第五节）与
`IsProbabilityMeasure μ₀`（本节前提）——由此 mathlib 给出无限轨迹概率测度。 -/
instance isProbabilityMeasure_trajMeasure_legalChain :
    IsProbabilityMeasure (Kernel.trajMeasure μ₀ legalChain) :=
  inferInstance

/-- 具体初始分布 `mu0` 的实例化读出。 -/
example : IsProbabilityMeasure (Kernel.trajMeasure mu0 legalChain) := by
  exact isProbabilityMeasure_trajMeasure_legalChain mu0

/-- **唯一性**（消费 `eq_traj`）：任何与 `partialTraj legalChain 0 b` 逐位相容的核
必等于 `traj legalChain 0`——柱集值唯一决定无限轨迹分布。 -/
theorem traj_unique_prefix
    (η : Kernel (Π i : Finset.Iic 0, XConst State i) (Π n, XConst State n))
    (hη : ∀ b : ℕ, η.map (frestrictLe b) = Kernel.partialTraj legalChain 0 b) :
    η = Kernel.traj legalChain 0 :=
  Kernel.eq_traj (κ := legalChain) η hη

/-- **Markov 性**（消费 `map_traj_succ_self`）：轨迹核推前到第 b+1 位的分布恰是
第 b 核——条件于前缀的下一坐标分布就是 `legalChain b`。 -/
theorem traj_markov_property (b : ℕ) :
    (Kernel.traj legalChain b).map (fun x : Π n, XConst State n => x (b + 1))
      = legalChain b :=
  Kernel.map_traj_succ_self (κ := legalChain)

/-! ## 八、条件分布适用边界（第 8 项） -/

/-- **边界定理（本项主交付）**：正规条件分布 `condDistrib` 的全部适用条件，逐条显式：
目标空间 `X (a+1)` 须为 StandardBorelSpace 且 Nonempty；结论只在
`(trajMeasure μ₀ κ).map (frestrictLe a)`-a.s. 成立（`=ᵐ`）——零概率事件的条件化
不取事件比值，按 §9.3 只在 μ-a.s. 唯一范围声明版本不变。本定理把两个前提作为
显式实例前提摆出：满足则直接消费锁定提交的 `condDistrib_trajMeasure`。 -/
theorem condDistrib_boundary (a : ℕ)
    [StandardBorelSpace (XConst State (a + 1))] [Nonempty (XConst State (a + 1))] :
    ProbabilityTheory.condDistrib (fun x : Π n, XConst State n => x (a + 1))
        (frestrictLe a) (Kernel.trajMeasure μ₀ legalChain)
      =ᵐ[(Kernel.trajMeasure μ₀ legalChain).map (frestrictLe a)] legalChain a :=
  Kernel.condDistrib_trajMeasure (X := XConst State) (κ := legalChain) (μ₀ := μ₀)

/-- **满足侧读出（可数离散目标）**：Disc 是 StandardBorelSpace 且 Nonempty，
以 Disc 为观察目标时边界定理前提成立。 -/
theorem disc_target_satisfies : StandardBorelSpace Disc ∧ Nonempty Disc :=
  ⟨infer_instance, ⟨Disc.filing⟩⟩

/-- **满足侧读出（实值目标）**：Param = Fin 3 → ℝ 是 StandardBorelSpace 且 Nonempty，
以实参数为观察目标时边界定理前提成立。 -/
theorem param_target_satisfies : StandardBorelSpace Param ∧ Nonempty Param :=
  ⟨infer_instance, ⟨fun _ => (0 : ℝ)⟩⟩

/-- **不满足侧（空目标）**：空空间无 Nonempty（且不可能有）——
`condDistrib_trajMeasure` 的 Nonempty 前提对空目标不可满足。 -/
theorem nonempty_empty_target : ¬ Nonempty Empty := fun h => h.elim fun a => a.elim

/-! ### 全 Sum 态：显式具名假设版 -/

/-- **Sum 编码全 State 的边界**：标准 Borel 条件作为显式具名假设 `stateSB` 传入
（mathlib 缺 Sum 实例，见 §二开放点记录），其余全部无条件——前提齐备时结论照常成立。 -/
theorem condDistrib_boundary_stateFull (a : ℕ)
    (stateSB : StandardBorelSpace State) :
    ProbabilityTheory.condDistrib (fun x : Π n, XConst State n => x (a + 1))
        (frestrictLe a) (Kernel.trajMeasure μ₀ legalChain)
      =ᵐ[(Kernel.trajMeasure μ₀ legalChain).map (frestrictLe a)] legalChain a := by
  haveI : StandardBorelSpace (XConst State (a + 1)) := stateSB
  haveI : Nonempty (XConst State (a + 1)) := ⟨Sum.inl Disc.filing⟩
  exact Kernel.condDistrib_trajMeasure (X := XConst State) (κ := legalChain) (μ₀ := μ₀)

/-! ### 乘积编码 StateP：端到端无条件成立 -/

/-- 乘积编码上的同一确定性推前结构。 -/
def nextP : StateP → StateP := fun p => (discSucc p.1, paramStep p.2)

theorem measurable_nextP : Measurable nextP :=
  (measurable_discSucc.comp measurable_fst).prodMk
    (measurable_paramStep.comp measurable_snd)

/-- 乘积编码的链。 -/
def chainP (n : ℕ) :
    Kernel (Π i : Finset.Iic n, XConst StateP i) (XConst StateP (n + 1)) :=
  chainOn nextP measurable_nextP n

instance chainP_isMarkovKernel : ∀ n : ℕ, IsMarkovKernel (chainP n) :=
  chainOn_isMarkovKernel nextP measurable_nextP

/-- 乘积编码的初始分布：Dirac 于 (受理, 零参数)。 -/
def mu0P : Measure StateP := Measure.dirac (Disc.filing, fun _ => (0 : ℝ))

instance mu0P_isProbabilityMeasure : IsProbabilityMeasure mu0P :=
  Measure.dirac.isProbabilityMeasure

/-- 乘积编码轨迹的无限概率测度存在（全部假设无条件成立）。 -/
instance isProbabilityMeasure_trajMeasure_chainP :
    IsProbabilityMeasure (Kernel.trajMeasure mu0P chainP) :=
  inferInstance

/-- **端到端无条件成立的条件分布读出**：StateP 是 StandardBorelSpace（乘积实例）
且 Nonempty，故边界定理前提无需任何额外假设即满足——这是"单个
StandardBorelSpace 实例不算完成"的反面：完整 IT 接线在标准 Borel 目标上闭环。 -/
theorem condDistrib_boundary_stateP (a : ℕ) :
    ProbabilityTheory.condDistrib (fun x : Π n, XConst StateP n => x (a + 1))
        (frestrictLe a) (Kernel.trajMeasure mu0P chainP)
      =ᵐ[(Kernel.trajMeasure mu0P chainP).map (frestrictLe a)] chainP a := by
  haveI : Nonempty (XConst StateP (a + 1)) := ⟨(Disc.filing, fun _ => (0 : ℝ))⟩
  exact Kernel.condDistrib_trajMeasure (X := XConst StateP) (κ := chainP) (μ₀ := mu0P)

end Traj

end

end JurisLean.Seams.UnifiedTrajectory
