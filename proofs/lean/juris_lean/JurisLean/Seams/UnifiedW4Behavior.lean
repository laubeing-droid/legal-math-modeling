import Mathlib.Tactic

/-!
W4 行为批 T116–T121 —— 六件套之 Lean 合同件（分包 O）。

出处（施工合同）：
- `docs/spec/20261007-统一法律数学模型_附录K_全量目标落实表.md:2545`（T116：
  §8.4 多议题非凸 IR 和 argmax，不假设凸/唯一）、`:2546`（T117：§8.4 共享 θ
  稳健情景树，非矩形反例 θ+(1−θ)）、`:2547`（T118：§8.4,12.5 权限成本 VOI、
  有限期停时、非单调补证）、`:2548`（T119：§8.5 因果、法律责任、效用同轨迹
  不同投影）、`:2549`（T120：§8.5 合规激励比较含实际违规行动及制裁/执行）、
  `:2550`（T121：§9.1,9.4 行为实际事件→效力/观察→同一规则重新评价）。
- `docs/spec/20261007-统一法律数学模型_全量施工方案.md:531-547`（§8.4/§8.5）、
  同文件 `:563-575`（§9.1）与 `:616-620`（§9.4）。

六件套分工：本件＝新合同（六项各自独立结论定理＋六项旗舰＋总旗舰
`w4_behavior_flagship`）。Python 入口 `behavior_ref.py`、独立 checker
`behavior_check.py`、正反例测试 `test_behavior_w4.py`、下游消费走
`tools/unified_math_v2` 既有 `step_event`/`run_trace` 公开入口（不改
pipeline.py/case.py，详见报告）。

可消费模块关系（如实声明）：本件为自含模块（仅 `import Mathlib.Tactic`），
与 `Seams/UnifiedTrajectory.lean` 的轨迹空间取**有限轨迹读法**（本件 `Trace`
为有限实际事件序列；无限轨迹核构造以 UnifiedTrajectory 为准，本件不重复、
不消费其 API 以免引入未过 CI 的跨模块风险）；`Seams/UnifiedNeedlesGapLate.lean`
的 `explicit_backflow_restores_readability` 是**版本回流**接口，本件 T121 的
行为回流（事件→观察→同规则重评）与其形状对齐，但仅作接口参考、未 import
（该件尚未过 CI，消费须报告声明——本报告如实声明此参考关系）。

## 一、法律语义（人话）

- **T116（多议题谈判）**：合法和解集由请求、处分权与数量公式产生；个体理性集
  `S_IR = {s : u_i(s) ≥ d_i, ∀i}` 直接定义，**可空、不假设凸/单分量**（§8.4，
  见证 `t116_ir_can_be_empty`）；argmax 是全体最大化元的集合，**非凸域保留全
  argmax，不冒称唯一**（见证 `t116_argmax_not_unique`：两协议点同为 argmax
  且同为 Pareto）。旗舰 `wsum_max_is_pareto`：正权和的最大点是 Pareto 点
  （若被支配，正权和严格增，矛盾）；反向不成立（权重扫不全非凸前沿），本件
  不证反向。
- **T117（稳健行动）**：稳健值 `sup_π inf_θ E_θ^π u` 把**同一个** θ 贯穿全
  策略（EXT08：共享参数不被消去）；情景树取本反例所需**有限深度 2** 的显式
  两层形状、共享 θ 贯穿两期求值（一般深树＝同一"同一 θ 逐层贯穿"构造的
  叠加，不在本件泛化域——开放点见头注二）；稳健
  行动＝在全部情景满足约束（`IsRobust`，对阈值交封闭）。旗舰
  `shared_theta_not_rectangular`：闭式反例——θ∈{0,1} 决定两期收益 θ 与 1−θ，
  共享 θ 总收益恒 1（稳健值 1），而矩形逐期最坏相加伪造 0；矩形逐期范围之积
  还允许混合点 (1,1)，共享 θ 下永不可达——只有矩形独立的不确定核才可逐步
  Bellman min-max，本例恰不满足。
- **T118（信息取得与停止）**：毛信息价值 ≥ 0（同模型、同合法行动、允许忽略；
  由逐格最优见证函数给出——见证存在性是显式前提，不冒充已构造），**净信息
  价值还减权限成本，可为负**（闭式见证）；有限期限取证/停时用 Snell 递推
  `V_{r+1}(t) = max(g_t, V_r(t+1) − c_t)`，期限终态强制停（不任意 max），
  **最优性**：任意适应停时收益 ≤ V（`stopPayoff_le_snell`）；**存在性**：
  Snell 策略（首次满足停分支即停）取到 V（`snell_policy_achieves`）；
  **非单调补证反例**：再取一条反向证据后期望决策值下降（9/10 → 4/5 合成例，
  独立保留——毛信息价值是先验期望上的不等式，不是逐路径单调性）。
- **T119（行为评价）**：因果效果、法律责任、私人收益是**同一路径的三种投影**
  （§8.5）——形式化为同一轨迹到三种读数的三个函数（输入只有轨迹，无旁路
  通道，`projection_functional`）；旗舰 `projection_separation`：同一轨迹
  （特权防卫致害）因果投影说"致害发生"、法律责任投影说"该行为人不担责"
  （合法性标记击败因果归责）、效用投影给出第三读数——同轨迹不同投影结论
  不同，三投影不互相替代。
- **T120（合规激励）**：有限行动空间**含实际违规行动**（不删违规选项制造
  定理——反例与数值例的行动表都保留违规行动参与比较）；制裁/执行以 ℚ 参数化
  （期望效用 `eu = gain − p·F`）。旗舰 `compliance_dominance`：逐项威慑条件
  （每个违规行动的期望 ≤ 被见证合规行动的期望）给出
  `sup_{Permitted} Eu ≥ sup_{Phys\Permitted} Eu`——§8.5 的准确命题形；
  威慑**可以失败**（`deterrence_can_fail`：低罚/低执行反例独立保留），也有
  达标数值例（`strong_deterrence_dominates`）。
- **T121（行为回流）**：实际事件→观察层更新→**同一规则**重新评价（§9.1
  Step 第 1/3/5 步与 §9.4：评价只读可见观察，结论不被事件直写）；旗舰
  `backflow_chain_general`：事件把观察值从阈下推到阈上时，同一规则的重新
  评价结论翻转（前 false 后 true，含具体见证 `backflow_chain_witness`）；
  无权限的变更不改规则（`unauthorized_keeps_rule`，§9.4 规范回流须有权/
  程序/生效）；观察相同则评价相同（`same_obs_same_eval`，LegalDerives 只读
  V 与 Γ——隐藏余额可以已变而法庭未见，认识/现实分离）。

## 二、显式假设开放点（如实列出，不伪造）

- T116 `wsum_max_is_pareto` 的正向（和最大 ⇒ Pareto）无条件成立；**反向不证**
  （§8.4：不能用权重扫全非凸 Pareto 前沿）。
- T118 毛信息价值的一般形以**逐格最优见证函数** `arg` 为显式前提
  （`hatt : ∀ c k, u c k ≤ u c (arg c)`）——有限格上可枚举其存在，本件作为
  具名假设摆出而非冒充构造；停时定理是**确定性** ℚ 版本（期限、继续成本、
  止损收益全部 ℚ 显式），带转移核的期望版另接 §9.3 核构造，本件不假设。
- T119 三投影的类型即"同路径"：三条读数都以**同一条轨迹**为唯一输入；投影
  分离给分离见证，不主张三投影一般互斥。
- T120 占优定理是**条件式**（威慑条件成立才占优）——这正是 §8.5 的准确命题；
  条件可失败的反例与达标数值例各自独立保留。
- T121 链式定理的一般形要求事件键对准规则键且观察值从阈下推到阈上
  （显式前提 `hkey/hbelow/habove`）；见证实例给出满足前提的具体三元组。

## 三、本件证明 API 纪律（沿 UnifiedW4Interp 第一轮教训，全部按 v4.30
工具链源码/本仓已绿模块核实）

- 合取命题不 `:= rfl`（term-rfl 只对 Eq）——逐分量 `⟨rfl, …⟩` 或 `refine ⟨…⟩`；
- `Bool.and_eq_true` 是 **Prop 等式形**（SimpLemmas:366）——只作 `simp only`/
  `rw` 引理；与 `decide_eq_true_iff`（PropLemmas:510）联用拆 `decide` 合取；
- 自家 Iff 定理投影一律显式 `Iff.mp`/`Iff.mpr`；`decide_eq_false_iff_not`
  （SimpLemmas:402）转 `decide = false`；
- `if_pos`/`if_neg`（core Init/Core.lean:1180/:1185）带条件证明直接 `rw`；
- 自备 `vmax`/`vmin`/`listMax`（if-then-else 定义＋自证引理）替代 `max`/`min`/
  `Finset.sup'`，绕开对 order 库引理面的依赖；
- 求和阶不等式只用已绿模块在用的 `Finset.sum_le_sum`（Probability.lean:280）与
  `Finset.sum_lt_sum`（Uncertainty.lean:155，签名 `(hle) (hlt)`）＋
  `mul_le_mul_of_nonneg_left`/`mul_lt_mul_of_pos_left`（GroupWithZero
  Unbundled/Defs.lean:226/:234，经 ContractionCondition.lean 浅 import 已证
  可达）；
- `lt_of_not_ge`（Mathlib/Order/Defs/LinearOrder.lean:95，签名 `(h : ¬b ≤ a) :
  a < b`）与 `le_antisymm`（Order/Basic:202 别名链）均按源码核名；
- v4.30 `List.mem_filter` 分量序＝⟨成员, 谓词⟩；`List.any_eq_true` 分量序＝
  ⟨成员∈表, 谓词值⟩；
- ℚ 目标只用 `norm_num`/`linarith`/`decide`，禁 `omega`。

### CI 轮 1（run 38109835203，12 真错）新增教训（已全部修复并固化）

- **经函数子项递归的 match 定义会落 WF recursion，kernel 不可折叠**——
  `evalUnder (ch θ) θ` 的子项 `ch θ` 不是构造子子项，`rfl`/kernel 直算全部
  失败。修法：T117 载体改**非递归**显式两层 `STree`（深度 2 如实声明）；
  证 `rfl` 只留给无递归、无 ℚ-order 实例的闭式。
- **ℚ 的 `ite`（经 `LinearOrder.toDecidableLE` 实例）kernel/rfl 项不可直算**，
  但 elaboration 期 `if_pos (by norm_num)`／`rw` 路径可靠——数值见证一律
  `rfl`-have 布尔叶值＋`rw`＋`if_pos/if_neg (by norm_num)` 组合。
- **`simp only` 不做收尾 `rfl`**——目标两侧打印相同也不闭合，须显式
  `exact Finset.sum_le_sum fun i _ => le_refl _` 之类的构造证明。
- **`if` 条件已被 simp only 归约成 `True` 后**，`rw [if_pos rfl]` 找不到
  `?c = ?c` 模式——改全量 `simp [defs]`（`if_true` 归约＋收尾）。
- **`rw` 穿 `decide` 的依赖实例会产生 motive is not type correct**——把键
  重写提升到**无 decide 包裹的普通目标**上先做（`have hab' : … := by
  rw [hkey]; exact habove`），再走 `if_pos`＋`decide_eq_true_iff.mpr`。
- **rcases 模式没有 `()` 字面**（Unit 零参构造）——`rintro ⟨s, hIR⟩` 后
  `cases s`。

**证**：本文件全部定理，零 sorry / 零自定义 axiom / 零 `True :=` 逃避。
CI 模块轮为唯一 Lean 权威（本地不编译，协议禁止）。
-/

namespace JurisLean.Seams.UnifiedW4Behavior

/-! ## 通用二元逐点最值（自备，绕开 order 库引理依赖） -/

/-- 逐点二元最大（if-then-else 定义；引理全部自证）。 -/
def vmax (a b : ℚ) : ℚ := if a ≤ b then b else a

theorem le_vmax_left (a b : ℚ) : a ≤ vmax a b := by
  unfold vmax
  by_cases h : a ≤ b
  · rw [if_pos h]; exact h
  · rw [if_neg h]

theorem le_vmax_right (a b : ℚ) : b ≤ vmax a b := by
  unfold vmax
  by_cases h : a ≤ b
  · rw [if_pos h]
  · rw [if_neg h]
    exact le_of_lt (lt_of_not_ge h)

theorem vmax_le (a b c : ℚ) (ha : a ≤ c) (hb : b ≤ c) : vmax a b ≤ c := by
  unfold vmax
  by_cases h : a ≤ b
  · rw [if_pos h]; exact hb
  · rw [if_neg h]; exact ha

/-- 逐点二元最小（同上自备）。 -/
def vmin (a b : ℚ) : ℚ := if a ≤ b then a else b

theorem vmin_le_left (a b : ℚ) : vmin a b ≤ a := by
  unfold vmin
  by_cases h : a ≤ b
  · rw [if_pos h]
  · rw [if_neg h]
    exact le_of_lt (lt_of_not_ge h)

theorem vmin_le_right (a b : ℚ) : vmin a b ≤ b := by
  unfold vmin
  by_cases h : a ≤ b
  · rw [if_pos h]; exact h
  · rw [if_neg h]

theorem le_vmin (a b c : ℚ) (ha : c ≤ a) (hb : c ≤ b) : c ≤ vmin a b := by
  unfold vmin
  by_cases h : a ≤ b
  · rw [if_pos h]; exact ha
  · rw [if_neg h]; exact hb

/-! ## T116：多议题谈判（§8.4）——非凸 IR 与全 argmax -/

section T116

variable {I : Type} [Fintype I] {A : Type} [DecidableEq A]

/-- 加权和目标：`∑_i w_i · u_i(s)`（正权和——§8.4 Pareto 判据的权重侧）。 -/
def wsum (u : I → A → ℚ) (w : I → ℚ) (s : A) : ℚ := ∑ i, w i * u i s

/-- 个体理性（直接定义，不假设凸/单分量/非空）：`s` 可行且各方不低于外部
选项（§8.4：`S_IR = {s ∈ S : u_i(s) ≥ d_i, ∀i}`）。 -/
abbrev IsIR (feas : List A) (u : I → A → ℚ) (d : I → ℚ) (s : A) : Prop :=
  s ∈ feas ∧ ∀ i, d i ≤ u i s

/-- 全体 argmax（§8.4：非凸域保留全 argmax，不冒称唯一）。 -/
abbrev IsArgmaxW (feas : List A) (u : I → A → ℚ) (w : I → ℚ) (s : A) : Prop :=
  s ∈ feas ∧ ∀ t ∈ feas, wsum u w t ≤ wsum u w s

/-- Pareto 支配：所有目标不差且至少一项更好。 -/
abbrev dominates (u : I → A → ℚ) (s t : A) : Prop :=
  (∀ i, u i s ≤ u i t) ∧ ∃ i₀, u i₀ s < u i₀ t

/-- Pareto 点：可行且无其他可行点支配它（§8.4 的偏序定义，不立全序）。 -/
abbrev IsPareto (feas : List A) (u : I → A → ℚ) (s : A) : Prop :=
  s ∈ feas ∧ ¬ ∃ t ∈ feas, dominates u s t

/-- Pareto 的 Bool 参考核（对可行表与有限议题逐项 decide）。 -/
def paretoB (feas : List A) (u : I → A → ℚ) (s : A) : Bool :=
  decide (s ∈ feas) && !(feas.any (fun t => decide (dominates u s t)))

/-- Pareto 考核双侧互译：Bool 检查器 ↔ Prop 定义（检查器不比定义多判少判）。 -/
theorem paretoB_iff (feas : List A) (u : I → A → ℚ) (s : A) :
    paretoB feas u s = true ↔ IsPareto feas u s := by
  constructor
  · intro h
    simp only [paretoB, Bool.and_eq_true, decide_eq_true_iff] at h
    refine ⟨h.1, ?_⟩
    rintro ⟨t, ht, hle, i₀, hlt⟩
    have hany : feas.any (fun x => decide (dominates u s x)) = true :=
      List.any_eq_true.mpr ⟨t, ht, decide_eq_true_iff.mpr ⟨hle, i₀, hlt⟩⟩
    rw [hany, Bool.not_true] at h
    exact Bool.noConfusion h.2
  · rintro ⟨hmem, hno⟩
    simp only [paretoB, Bool.and_eq_true, decide_eq_true_iff]
    refine ⟨hmem, ?_⟩
    cases hany : feas.any (fun x => decide (dominates u s x)) with
    | true =>
      obtain ⟨t, ht, htval⟩ := List.any_eq_true.mp hany
      exact absurd (⟨t, ht, decide_eq_true_iff.mp htval⟩ :
        ∃ t ∈ feas, dominates u s t) hno
    | false => rfl

/-- **T116 旗舰（正权和最大点必是 Pareto 点）**：权重全正时，若 `s` 是可行集
上的加权和最大元，则没有任何可行点支配它——被支配则正权和严格增，与最大性
矛盾（§8.4）。反向（Pareto ⇒ 某权和最大）本件不证：不能用权重扫全非凸
前沿。 -/
theorem wsum_max_is_pareto (feas : List A) (u : I → A → ℚ) (w : I → ℚ)
    (hw : ∀ i, 0 < w i) (s : A) (hmax : IsArgmaxW feas u w s) :
    IsPareto feas u s := by
  obtain ⟨hmem, hall⟩ := hmax
  simp only [wsum] at hall
  refine ⟨hmem, ?_⟩
  rintro ⟨t, ht, hle, i₀, hlt⟩
  have hpt : ∀ i, w i * u i s ≤ w i * u i t := fun i =>
    mul_le_mul_of_nonneg_left (hle i) (le_of_lt (hw i))
  have hsum : (∑ i, w i * u i s) < ∑ i, w i * u i t :=
    Finset.sum_lt_sum (fun i _ => hpt i) ⟨i₀, Finset.mem_univ i₀,
      mul_lt_mul_of_pos_left hlt (hw i₀)⟩
  linarith [hall t ht]

/-- Pareto 检查器与旗舰的连接：和最大元过检查器（`paretoB` 接受）。 -/
theorem wsum_max_passes_paretoB (feas : List A) (u : I → A → ℚ) (w : I → ℚ)
    (hw : ∀ i, 0 < w i) (s : A) (hmax : IsArgmaxW feas u w s) :
    paretoB feas u s = true :=
  Iff.mpr (paretoB_iff feas u s) (wsum_max_is_pareto feas u w hw s hmax)

end T116

/-! ### T116 闭式见证：IR 可空、argmax 不唯一 -/

/-- T116 反面见证（IR 可空，独立保留）：唯一可行点的效用 0 低于外部选项 1，
个体理性集为空——空集单列，不伪造协议（§8.4：可非凸、多分量**或空**）。 -/
theorem t116_ir_can_be_empty :
    ¬ ∃ s : Unit, IsIR [()] (fun (_ : Fin 1) (_ : Unit) => (0:ℚ))
      (fun _ => 1) s := by
  rintro ⟨s, hIR⟩
  cases s
  have h := hIR.2 0
  exact absurd h (by norm_num)

/-- T116 见证效用面：一个议题、两个协议点，效用恒 5、权重 1。 -/
def negoU : Fin 1 → Fin 2 → ℚ := fun _ _ => 5
def negoW : Fin 1 → ℚ := fun _ => 1

/-- T116 见证：两点都是个体理性的 argmax（权重全正）。 -/
theorem t116_both_argmax :
    IsIR [0, 1] negoU (fun _ => 0) 0 ∧ IsIR [0, 1] negoU (fun _ => 0) 1 ∧
    IsArgmaxW [0, 1] negoU negoW 0 ∧ IsArgmaxW [0, 1] negoU negoW 1 := by
  refine ⟨⟨by simp, fun i => by norm_num [negoU]⟩,
    ⟨by simp, fun i => by norm_num [negoU]⟩, ⟨by simp, ?_⟩, ⟨by simp, ?_⟩⟩
  · intro t _
    simp only [wsum, negoU, negoW]
    exact Finset.sum_le_sum fun i _ => le_refl _
  · intro t _
    simp only [wsum, negoU, negoW]
    exact Finset.sum_le_sum fun i _ => le_refl _

/-- **T116 见证（argmax 不唯一）**：两点同为 argmax、同为 Pareto 且互异——
非凸（此处离散）域保留全 argmax，不冒称唯一（§8.4；模型对协议空间不作任何
凸性假设）。 -/
theorem t116_argmax_not_unique :
    IsPareto [0, 1] negoU 0 ∧ IsPareto [0, 1] negoU 1 ∧ (0:Fin 2) ≠ 1 := by
  refine ⟨⟨by simp, ?_⟩, ⟨by simp, ?_⟩, by decide⟩
  · rintro ⟨t, _, hle, i₀, hlt⟩
    exact absurd hlt (by norm_num [negoU])
  · rintro ⟨t, _, hle, i₀, hlt⟩
    exact absurd hlt (by norm_num [negoU])

/-- T116 检查器读数：两点都过 `paretoB`（与 Prop 侧见证一致）。 -/
theorem t116_paretoB_readings :
    paretoB [0, 1] negoU 0 = true ∧ paretoB [0, 1] negoU 1 = true :=
  ⟨Iff.mpr (paretoB_iff [0, 1] negoU 0) (t116_argmax_not_unique).1,
   Iff.mpr (paretoB_iff [0, 1] negoU 1) (t116_argmax_not_unique).2.1⟩

/-! ## T117：稳健行动（§8.4, EXT08）——共享 θ 情景树与矩形反例 -/

/-- 两期共享 θ 情景树（本反例所需**有限深度 2** 的显式两层形状，不引入
递归求值）：第一期收益 `r1 θ`，其后按**同一** θ 走到第二期叶 `r2 θ`。
更深有限树是同一"同一 θ 逐层贯穿"构造的叠加，不在本件泛化域内（如实
声明，见头注开放点）。 -/
structure STree (Θ : Type) where
  r1 : Θ → ℚ
  r2 : Θ → ℚ

/-- 共享 θ 求值：**同一个** θ 读两期叶（EXT08：共享参数不被消去）。 -/
def evalUnder {Θ : Type} (t : STree Θ) (θ : Θ) : ℚ := t.r1 θ + t.r2 θ

/-- 稳健行动（约束读法）：一个行动方案在**全部情景**下满足阈值约束
（§8.4：稳健行动在全部情景满足约束）。 -/
abbrev IsRobust {Θ : Type} (pay : Θ → ℚ) (v : ℚ) : Prop := ∀ θ, v ≤ pay θ

/-- 反例实例的逐期收益：第一期 θ、第二期 1−θ（θ∈{0,1}；§8.4 非矩形例）。 -/
def rT (θ : Bool) : ℚ := if θ then 1 else 0
def rF (θ : Bool) : ℚ := if θ then 0 else 1

/-- 两期情景树：第一期后按同一 θ 走到第二期，叶上取两期总收益。 -/
def twoPeriod : STree Bool := ⟨rT, rF⟩

/-- 共享 θ 的两期总收益恒等于 1（逐期 θ 与 1−θ 互补相消）。 -/
theorem shared_total_identity (θ : Bool) :
    evalUnder twoPeriod θ = 1 := by
  cases θ with
  | false => rfl
  | true => rfl

/-- 矩形（逐期独立最坏）估值：`min r₁ + min r₂`——逐期各取最坏相加。 -/
def rectVal : ℚ :=
  vmin (rT false) (rT true) + vmin (rF false) (rF true)

/-- 共享 θ 稳健估值：两期总收益在全部情景上的最坏值。 -/
def sharedVal : ℚ :=
  vmin (evalUnder twoPeriod false) (evalUnder twoPeriod true)

theorem rectVal_zero : rectVal = 0 := by
  have h1 : rT false = 0 := rfl
  have h2 : rT true = 1 := rfl
  have h3 : rF false = 1 := rfl
  have h4 : rF true = 0 := rfl
  unfold rectVal vmin
  rw [h1, h2, h3, h4]
  rw [if_pos (by norm_num), if_neg (by norm_num)]
  norm_num

theorem shared_val_one : sharedVal = 1 := by
  unfold sharedVal vmin
  rw [shared_total_identity, shared_total_identity]
  rw [if_pos (by norm_num)]

theorem rectVal_lt_sharedVal : rectVal < sharedVal := by
  rw [rectVal_zero, shared_val_one]
  norm_num

/-- **T117 旗舰（非矩形闭式反例）**：共享 θ 时两期总收益恒 1（稳健值 1），
而矩形逐期最坏相加为 0——逐步 min-max 伪造 1 个单位收益；同时矩形逐期范围
之积允许混合点 (1,1)，共享 θ 下它不可达。只有矩形独立的不确定核及适用的
信息结构才可逐步 Bellman min-max，本例恰不满足（§8.4；EXT08 共享参数不被
消去）。 -/
theorem shared_theta_not_rectangular :
    (∀ θ : Bool, evalUnder twoPeriod θ = 1) ∧
    sharedVal = 1 ∧ rectVal = 0 ∧ rectVal < sharedVal ∧
    ((rT true, rF true) = ((1:ℚ), 0) ∧ (rT false, rF false) = ((0:ℚ), 1)) ∧
    ¬ ∃ θ : Bool, rT θ = 1 ∧ rF θ = 1 := by
  refine ⟨shared_total_identity, shared_val_one, rectVal_zero,
    rectVal_lt_sharedVal, ⟨rfl, rfl⟩, ?_⟩
  rintro ⟨θ, h1, h2⟩
  cases θ with
  | false => norm_num [rT, rF] at h1
  | true => norm_num [rT, rF] at h2

/-- 稳健行动的交封闭：在全部情景满足 v1 与 v2 的方案，在全部情景满足
min(v1, v2)（min ≤ v1 已足够，故 v2 约束仅作记录）。 -/
theorem robust_intersects {pay : Bool → ℚ} {v1 v2 : ℚ}
    (h1 : IsRobust pay v1) (_h2 : IsRobust pay v2) :
    IsRobust pay (vmin v1 v2) :=
  fun θ => le_trans (vmin_le_left v1 v2) (h1 θ)

/-- 共享 θ 树的稳健阈值读数：该方案在全部情景至少收益 1——矩形分解给出的
0 不是它的稳健值。 -/
theorem robust_shared_threshold : IsRobust (evalUnder twoPeriod) 1 :=
  fun θ => le_of_eq (shared_total_identity θ).symm

/-! ## T118：信息取得与停止（§8.4,12.5）——VOI、Snell、非单调补证 -/

section T118

variable {C : Type} [Fintype C] {K : Type} [Fintype K]

/-- 毛信息价值下界链（§8.4：免费可选信息且允许忽略时，有信息决策值 ≥ 无信息
决策值）。显式前提＝逐格最优见证函数 `arg`（`hatt`；有限格上可枚举其存在，
作为具名假设摆出，不冒充已构造——开放点见头注二）。 -/
theorem gross_voi_nonneg (w : C → ℚ) (hw : ∀ c, 0 ≤ w c) (u : C → K → ℚ)
    (k₀ : K) (arg : C → K) (hatt : ∀ c k, u c k ≤ u c (arg c)) :
    (∑ c, w c * u c k₀) ≤ ∑ c, w c * u c (arg c) :=
  Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hatt c k₀) (hw c)

/-- 净信息价值＝有信息值 − 无信息值 − 权限成本（ℚ 显式算术；可为负）。 -/
def netVoi (withI wo cost : ℚ) : ℚ := withI - wo - cost

/-- **净信息价值可为负（闭式见证，独立保留）**：信息无增量（有信息值＝无
信息值 1/2）而权限成本 1 时，净信息价值 −1——扣成本后可负（§8.4）。 -/
theorem net_voi_can_be_negative :
    netVoi (1/2) (1/2) 1 = -1 ∧ netVoi (1/2) (1/2) 1 < 0 := by
  refine ⟨?_, ?_⟩ <;> norm_num [netVoi]

end T118

/-- 有限期停时价值（Snell 递推，确定性 ℚ 版本）：余量 0 强制停（期限终态，
不任意 max）；否则取 max（停则 `g t`；续则 `V(t+1) − c_t`）——§8.4。 -/
def snell (g c : ℕ → ℚ) : ℕ → ℕ → ℚ
  | 0, t => g t
  | r+1, t => vmax (g t) (snell g c r (t+1) - c t)

/-- 停时规则：`σ r t = true` 表示在余量 `r`、时点 `t` 停；false 则继续。
期限强制：余量 0 处必停（规则读不到选择）。 -/
def stopPayoff (g c : ℕ → ℚ) (σ : ℕ → ℕ → Bool) : ℕ → ℕ → ℚ
  | 0, t => g t
  | r+1, t => if σ r t then g t else stopPayoff g c σ r (t+1) - c t

/-- **T118 最优性（任意适应停时不超过 Snell 值）**：对全部余量与时点，后向
归纳给 `payoff(σ) ≤ V`。 -/
theorem stopPayoff_le_snell (g c : ℕ → ℚ) (σ : ℕ → ℕ → Bool) :
    ∀ r t, stopPayoff g c σ r t ≤ snell g c r t := by
  intro r
  induction r with
  | zero => intro t; exact le_refl _
  | succ r ih =>
    intro t
    simp only [stopPayoff, snell]
    by_cases h : σ r t
    · rw [if_pos h]; exact le_vmax_left _ _
    · rw [if_neg h]
      have h1 := ih (t+1)
      have h2 := le_vmax_right (g t) (snell g c r (t+1) - c t)
      linarith

/-- Snell 停时策略：继续值不低于即期止损时继续，否则停（首达停分支即合法
停时）。 -/
def snellPolicy (g c : ℕ → ℚ) (r t : ℕ) : Bool :=
  decide (snell g c r (t+1) - c t ≤ g t)

/-- **T118 存在性（Snell 策略取到 V）**：后向归纳证该合法停时的收益恰等于
Snell 值——递推闭合并。 -/
theorem snell_policy_achieves (g c : ℕ → ℚ) :
    ∀ r t, stopPayoff g c (snellPolicy g c) r t = snell g c r t := by
  intro r
  induction r with
  | zero => intro t; rfl
  | succ r ih =>
    intro t
    simp only [stopPayoff, snell]
    rw [ih (t+1)]
    unfold snellPolicy
    by_cases h : snell g c r (t+1) - c t ≤ g t
    · have hd : (decide (snell g c r (t+1) - c t ≤ g t)) = true :=
        decide_eq_true_iff.mpr h
      rw [if_pos hd]
      unfold vmax
      by_cases h2 : g t ≤ snell g c r (t+1) - c t
      · rw [if_pos h2, le_antisymm h h2]
      · rw [if_neg h2]
    · have hd : ¬ ((decide (snell g c r (t+1) - c t ≤ g t)) = true) := by
        rw [decide_eq_false_iff_not.mpr h]; simp
      rw [if_neg hd]
      unfold vmax
      rw [if_pos (le_of_lt (lt_of_not_ge h))]

/-- 后验评价读数：两状态信念 (q, 1−q) 与两个行动（期望 q 与 1−q）下的决策
值。 -/
def decVal (q : ℚ) : ℚ := vmax q (1 - q)

theorem decVal_nine : decVal (9/10) = 9/10 := by
  unfold decVal vmax
  rw [if_neg (by norm_num)]

theorem decVal_one_fifth : decVal (1/5) = 4/5 := by
  unfold decVal vmax
  rw [if_pos (by norm_num)]
  norm_num

/-- **T118 非单调补证反例（合成例，独立保留）**：第一条证据把信念推到
9/10（决策值 9/10），再取一条反向证据把信念落到 1/5（决策值只剩 4/5）——
**期望决策值下降**：补证的价值沿路径非单调；毛信息价值 ≥ 0 是先验期望上的
不等式，不是逐路径单调性。 -/
theorem evidence_value_nonmonotone :
    decVal (9/10) = 9/10 ∧ decVal (1/5) = 4/5 ∧ decVal (1/5) < decVal (9/10) := by
  refine ⟨decVal_nine, decVal_one_fifth, ?_⟩
  rw [decVal_nine, decVal_one_fifth]
  norm_num

/-! ## T119：行为评价（§8.5）——同一轨迹三种投影 -/

/-- 单次行为事件：行为人、是否特权（正当防卫/有权行为等合法性层标记）、
物理致害（因果层）、行为人私人净得（效用层）。四字段同属**同一事件**——
三种投影沿同一路径读取（§8.5：同路径投影）。 -/
structure Act where
  actor : Nat
  privileged : Bool
  harm : ℚ
  gain : ℚ
deriving DecidableEq, Repr

/-- 行为轨迹＝实际事件序列（有限；无限轨迹核构造以 UnifiedTrajectory 为准，
本件取有限轨迹读法）。 -/
abbrev Trace := List Act

/-- 投影一（因果解释）：轨迹的物理致害总量——只读 harm 字段。 -/
def causalReading (t : Trace) : ℚ := (t.map (fun a => a.harm)).sum

/-- 投影二（法律责任归属）：行为人担责当且仅当其有非特权的致害行为——
合法性标记击败因果归责（特权防卫致害不担责）。 -/
def liableB (t : Trace) (n : Nat) : Bool :=
  t.any (fun a =>
    decide (a.actor = n) && decide (a.privileged = false) && decide (0 < a.harm))

/-- 投影三（效用度量）：行为人的私人净得和——只读 gain 字段。 -/
def utilityReading (t : Trace) (n : Nat) : ℚ :=
  ((t.filter (fun a => decide (a.actor = n))).map (fun a => a.gain)).sum

/-- 特权防卫见证事件：行为人 7 在特权状态下致害 5、无私人净得。 -/
def selfDefense : Act := ⟨7, true, 5, 0⟩

/-- **T119 旗舰（投影分离）**：同一轨迹（特权防卫致害）——因果投影说"致害
发生"（总量 5 > 0）、法律责任投影说"行为人 7 不担责"（特权击败）、效用投影
给出第三个读数（0 ≠ 5）。同轨迹不同投影给出不同结论，三投影不互相替代。 -/
theorem projection_separation :
    (0:ℚ) < causalReading [selfDefense] ∧
    liableB [selfDefense] 7 = false ∧
    causalReading [selfDefense] ≠ utilityReading [selfDefense] 7 := by
  refine ⟨?_, rfl, ?_⟩
  · norm_num [causalReading, selfDefense]
  · norm_num [causalReading, utilityReading, selfDefense]

/-- 同路径读法：三条投影的输入都只有同一条轨迹（无旁路通道）——同一轨迹给
同一读数（函数性）。 -/
theorem projection_functional (t t' : Trace) (n : Nat) (h : t = t') :
    causalReading t = causalReading t' ∧ liableB t n = liableB t' n ∧
      utilityReading t n = utilityReading t' n := by
  rw [h]
  exact ⟨rfl, rfl, rfl⟩

/-! ## T120：合规激励（§8.5）——含实际违规行动的占优比较 -/

/-- 合规行动档案：合法标记、毛收益、制裁罚额、执行概率（全部 ℚ）。 -/
structure Action where
  aid : Nat
  permitted : Bool
  gain : ℚ
  fine : ℚ
  pExec : ℚ
deriving DecidableEq, Repr

/-- 期望效用：毛收益减去制裁的期望负担 `p·F`（§8.5：罚则通过金额、执行概率
影响两侧）。 -/
def eu (a : Action) : ℚ := a.gain - a.pExec * a.fine

/-- 行动档案良态：执行概率是概率、罚额非负（Python 构造门 fail-fast 的
Lean 对应谓词）。 -/
def ActionOK (a : Action) : Prop := 0 ≤ a.pExec ∧ a.pExec ≤ 1 ∧ 0 ≤ a.fine

/-- 合规行动的期望效用表。 -/
def compliantEus (acts : List Action) : List ℚ :=
  (acts.filter (fun a => a.permitted)).map eu

/-- 自备列表最大（非空表的最大元；空表读 0——本件只对非空表调用）。 -/
def listMax : List ℚ → ℚ
  | [] => 0
  | x :: xs => vmax x (listMax xs)

theorem mem_le_listMax : ∀ (l : List ℚ) (x : ℚ), x ∈ l → x ≤ listMax l := by
  intro l
  induction l with
  | nil => intro x hx; cases hx
  | cons y ys ih =>
    intro x hx
    rcases List.mem_cons.mp hx with h | h
    · rw [h]; exact le_vmax_left _ _
    · exact le_trans (ih x h) (le_vmax_right _ _)

/-- **T120 旗舰（合规占优条件定理）**：威慑条件成立——每个违规行动的期望
不超过被见证的合规行动——则违规侧处处不超过合规行动效用表的最大值：
`sup_{a∈Permitted} Eu(a) ≥ sup_{a∈Phys\Permitted} Eu(a)`（§8.5 的准确命题形；
条件不成立时见 `deterrence_can_fail` 反例）。违规行动**留在行动空间内**参与
比较（前提逐项量化 `a ∈ acts`），不删选项制造定理。 -/
theorem compliance_dominance (acts : List Action) (b : Action)
    (hbmem : b ∈ acts) (hbperm : b.permitted = true)
    (hdeter : ∀ a ∈ acts, a.permitted = false → eu a ≤ eu b) :
    (eu b ∈ compliantEus acts) ∧
    ∀ a ∈ acts, a.permitted = false → eu a ≤ listMax (compliantEus acts) := by
  have hbmem' : eu b ∈ (acts.filter (fun a => a.permitted)).map eu :=
    List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨hbmem, hbperm⟩, rfl⟩
  refine ⟨hbmem', ?_⟩
  intro a ha haperm
  exact le_trans (hdeter a ha haperm) (mem_le_listMax _ _ hbmem')

/-- 数值例（合规占优成立）：合规净得 5；违规毛得 10、罚 12、执行概率 1/2 →
期望 4 < 5——威慑条件成立，旗舰定理给合规占优。违规行动**保留在表内**。 -/
def actComply : Action := ⟨0, true, 5, 0, 0⟩
def actViolate : Action := ⟨1, false, 10, 12, 1/2⟩
def strongDeterrence : List Action := [actComply, actViolate]

theorem strong_deterrence_values :
    eu actComply = 5 ∧ eu actViolate = 4 := by
  refine ⟨?_, ?_⟩ <;> norm_num [actComply, actViolate, eu]

theorem strong_deterrence_dominates :
    ∀ a ∈ strongDeterrence, a.permitted = false →
      eu a ≤ listMax (compliantEus strongDeterrence) := by
  intro a ha haperm
  have hb : eu actComply ∈ compliantEus strongDeterrence :=
    List.mem_map.mpr ⟨actComply, List.mem_filter.mpr
      ⟨by simp [strongDeterrence], rfl⟩, rfl⟩
  have hval : eu actViolate ≤ eu actComply := by
    rw [strong_deterrence_values.2, strong_deterrence_values.1]
    norm_num
  rcases List.mem_cons.mp ha with heq | hin
  · rw [heq] at haperm
    simp [actComply] at haperm
  · rcases List.mem_cons.mp hin with heq2 | hnil
    · rw [heq2]
      exact le_trans hval (mem_le_listMax _ _ hb)
    · cases hnil

/-- **T120 反例（威慑失败，独立保留）**：违规毛得 10、罚 4、执行概率 1/2 →
期望 8 > 合规 5——占优命题的条件可失败；违规行动仍在行动空间内参与比较
（§8.5：不能删掉违规选项制造定理）。 -/
def weakViolate : Action := ⟨1, false, 10, 4, 1/2⟩
def weakDeterrence : List Action := [actComply, weakViolate]

theorem deterrence_can_fail :
    actViolate.permitted = false ∧ weakViolate.permitted = false ∧
    eu actComply = 5 ∧ eu weakViolate = 8 ∧ (8:ℚ) > 5 ∧
    ActionOK weakViolate := by
  refine ⟨rfl, rfl, ?_, ?_, by norm_num, ?_⟩ <;>
    norm_num [actComply, weakViolate, eu, ActionOK]

/-! ## T121：行为回流（§9.1,9.4）——事件→观察→同一规则重新评价 -/

/-- 观察层：有限键值表（只记录可见材料；找不到键读 0）。 -/
def obsGet (o : List (Nat × ℚ)) (k : Nat) : ℚ :=
  match o with
  | [] => 0
  | (k', v) :: rest => if k' = k then v else obsGet rest k

/-- 实际行为事件：对象键、数量、规范回流权限位（§9.1：事件带实际行为人与
效力时点；§9.4：规范回流必须是有权限、有程序、有生效条件的事件）。 -/
structure Ev where
  key : Nat
  amount : ℚ
  authorized : Bool
deriving DecidableEq, Repr

/-- 事件施加：只更新**观察层**（可见记录追加），不直写任何评价结论
（§9.1 Step 第 3 步；§9.4：结论由同一规则重新评价产生）。 -/
def applyObs (o : List (Nat × ℚ)) (e : Ev) : List (Nat × ℚ) :=
  (e.key, obsGet o e.key + e.amount) :: o

/-- 同一规则：键上的阈值判定（评价函数在事件前后是**同一个**）。 -/
structure Rule where
  rkey : Nat
  threshold : ℚ
deriving DecidableEq, Repr

/-- 规则评价：只读观察层（§9.4：观察相同的两段历史，评价完全相同）。 -/
def ruleEval (r : Rule) (o : List (Nat × ℚ)) : Bool :=
  decide (r.threshold ≤ obsGet o r.rkey)

/-- 事件改变观察（逐点读出）：施加后该键的观察值＝旧值＋数量。 -/
theorem event_changes_observation (o : List (Nat × ℚ)) (e : Ev) :
    obsGet (applyObs o e) e.key = obsGet o e.key + e.amount := by
  simp [applyObs, obsGet]

/-- **T121 旗舰（回流链式定理）**：事件把观察值从阈下推到阈上时，同一规则
的重新评价结论翻转：前 false、后 true——事件改变观察、观察改变规则评价
结论，而结论始终由同一评价函数产生（不被事件直写）。 -/
theorem backflow_chain_general (o : List (Nat × ℚ)) (e : Ev) (r : Rule)
    (hkey : e.key = r.rkey)
    (hbelow : obsGet o r.rkey < r.threshold)
    (habove : r.threshold ≤ obsGet o r.rkey + e.amount) :
    ruleEval r o = false ∧ ruleEval r (applyObs o e) = true := by
  have hab' : r.threshold ≤ obsGet o e.key + e.amount := by
    rw [hkey]
    exact habove
  refine ⟨?_, ?_⟩
  · simp only [ruleEval]
    rw [decide_eq_false_iff_not]
    linarith
  · simp only [ruleEval, applyObs, obsGet]
    rw [if_pos hkey]
    exact decide_eq_true_iff.mpr hab'

/-- 见证实例：观察 (0↦5)、事件（键 0、量 6、有权）、规则（键 0、阈 10）——
同一规则前 false 后 true。 -/
def bfObs : List (Nat × ℚ) := [(0, 5)]
def bfEv : Ev := ⟨0, 6, true⟩
def bfRule : Rule := ⟨0, 10⟩

theorem backflow_chain_witness :
    ruleEval bfRule bfObs = false ∧ ruleEval bfRule (applyObs bfObs bfEv) = true ∧
      obsGet (applyObs bfObs bfEv) 0 = 11 := by
  have h5 : obsGet bfObs bfRule.rkey = 5 := rfl
  have h := backflow_chain_general bfObs bfEv bfRule rfl
    (by rw [h5]; norm_num [bfRule])
    (by rw [h5]; norm_num [bfRule, bfEv])
  exact ⟨h.1, h.2, by norm_num [bfObs, bfEv, applyObs, obsGet]⟩

/-- §9.4 权限分离：无权限的变更不改规则——普通草案/学习参数不写规范域。 -/
def ruleAfter (r newRule : Rule) (e : Ev) : Rule :=
  if e.authorized then newRule else r

theorem unauthorized_keeps_rule (r newRule : Rule) (e : Ev)
    (ha : e.authorized = false) : ruleAfter r newRule e = r := by
  unfold ruleAfter
  rw [if_neg (by rw [ha]; simp)]

/-- §9.4 观察相同⇒评价相同（LegalDerives 只读 V 与 Γ；隐藏余额可以已变而
法庭未见——认识/现实分离，不是假设裁判永真）。 -/
theorem same_obs_same_eval (r : Rule) (o o' : List (Nat × ℚ))
    (h : ∀ k, obsGet o k = obsGet o' k) :
    ruleEval r o = ruleEval r o' := by
  simp only [ruleEval]
  rw [h r.rkey]

/-- 无权限事件不触发规则翻转（对 `ruleAfter` 的评价读出：规则原样）。 -/
theorem unauthorized_no_flip (r newRule : Rule) (e : Ev)
    (ha : e.authorized = false) :
    ruleEval (ruleAfter r newRule e) = ruleEval r := by
  rw [unauthorized_keeps_rule r newRule e ha]

/-! ## 总旗舰：六项独立结论打包 -/

/-- **W4 行为批总旗舰**：六项各自独立结论的合取——T116 IR 可空且 argmax
不唯一（Pareto 检查器贯通）、T117 共享 θ 非矩形闭式反例、T118 停时最优/
存在＋净信息价值可负＋补证非单调、T119 同轨迹三投影分离、T120 合规占优
条件（一般形，含达标例）、T121 回流链式翻转（含见证与权限分离）。 -/
theorem w4_behavior_flagship :
    (¬ ∃ s : Unit, IsIR [()] (fun (_ : Fin 1) (_ : Unit) => (0:ℚ))
      (fun _ => 1) s) ∧
    (IsPareto [0, 1] negoU 0 ∧ IsPareto [0, 1] negoU 1 ∧ (0:Fin 2) ≠ 1) ∧
    ((∀ θ : Bool, evalUnder twoPeriod θ = 1) ∧ sharedVal = 1 ∧ rectVal = 0 ∧
      rectVal < sharedVal) ∧
    (∀ g c : ℕ → ℚ, ∀ r t,
      stopPayoff g c (snellPolicy g c) r t = snell g c r t) ∧
    (netVoi (1/2) (1/2) 1 < 0 ∧ decVal (1/5) < decVal (9/10)) ∧
    ((0:ℚ) < causalReading [selfDefense] ∧ liableB [selfDefense] 7 = false ∧
      causalReading [selfDefense] ≠ utilityReading [selfDefense] 7) ∧
    (∀ acts : List Action, ∀ b : Action, b ∈ acts → b.permitted = true →
      (∀ a ∈ acts, a.permitted = false → eu a ≤ eu b) →
        ∀ a ∈ acts, a.permitted = false → eu a ≤ listMax (compliantEus acts)) ∧
    (ruleEval bfRule bfObs = false ∧
      ruleEval bfRule (applyObs bfObs bfEv) = true) ∧
    (∀ (r newRule : Rule) (e : Ev), e.authorized = false →
      ruleEval (ruleAfter r newRule e) = ruleEval r) :=
  ⟨t116_ir_can_be_empty, t116_argmax_not_unique,
    ⟨shared_total_identity, shared_val_one, rectVal_zero, rectVal_lt_sharedVal⟩,
    snell_policy_achieves,
    ⟨(net_voi_can_be_negative).2, (evidence_value_nonmonotone).2.2⟩,
    projection_separation,
    fun acts b h1 h2 h3 => (compliance_dominance acts b h1 h2 h3).2,
    ⟨backflow_chain_witness.1, backflow_chain_witness.2.1⟩,
    fun r newRule e ha => unauthorized_no_flip r newRule e ha⟩

end JurisLean.Seams.UnifiedW4Behavior
