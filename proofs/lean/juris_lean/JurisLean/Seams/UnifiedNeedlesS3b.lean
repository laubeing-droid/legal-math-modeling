import Mathlib.Tactic
import JurisLean.FullMath.Probability.Conditioning
import JurisLean.ExactNumericContract

/-!
# S3 族第 22–26 针（附录 I.13 逐名承接，UnifiedNeedlesS3b）

本件承接 `docs/spec/20261007-统一法律数学模型_附录I_Lean施工明细.md` §I.13 中
S3 族的最后 5 针（#22–#26），绑定表见 `docs/full-math/BINDING_217_and_60.md` 第三节。
五针全部是**新合同**（表内标"拟"）：22/24/26 在绑定表中原为 UNBOUND（无锚），
23/25 有同名弱式锚（`Seams/Probability.lean:345`、`:401`），本件在
`JurisLean.Seams.UnifiedNeedlesS3b` 命名空间下按新合同重建，不与锚文件同名销账。

## 一、五针的法律语义（人话）

**22 `beta_interval_posterior_mass`（闭区间质量＝CDF 差）**：主文 §7.4 的"模型内
可信质量"读法——一个（后验）分布落在闭区间 `[lo, hi]` 的质量，等于 CDF 在两端点
取值之差，**前提是左端点无原子**。连续分布里"无原子性"是全称条件；在有限支撑
离散载体上非退化分布不可能处处无原子，故本件的诚实形态是**端点无原子**
（秩等于 lo 的状态质量为 0）。边界定理 `closed_mass_needs_atomfree_endpoint`
给出反例：左端点带原子时等式失效，端点原子被 CDF 差数掉一次。

**23 `selection_transport_from_shared_mechanism`（共享机制＋选择消因子）**：
主文 §7.3：同一法律观察的似然必须含选择因子；只有当选择只读与参数无关的
共享机制分量、且相应设计已条件化时，选择因子才在"参数后验边际"里**约去**。
本件把共享生成机制建成有限乘积空间 `Θ × Nty` 上的因子化联合
`sharedJoint π q = π(θ)·q(n)`：观察读 θ、选择读 n，则"观察∧选择"双重条件化后的
参数边际＝仅观察条件化的参数边际（选择因子 c_S 在分子分母同时出现而约去）。
边界定理 `parameter_reading_selection_enters_likelihood`：选择改读参数坐标时
搬运逐点失效（§7.3 的 θ² 似然现象的有限形态）——参数相关选择必须进入完整似然。

**24 `posterior_predictive_legal_target`（后验预测＝同一 Y 的显式和）**：
主文 §7.1/§7.3：法律事件的采样机制给出"事件 → 材料 → 裁判观察 Y"的联合，
后验预测是对**同一个 Y** 按后验积分（有限支撑下是显式有限和），不另造目标。
本件建 `PredictiveLegalModel`（先验＋材料通道＋观察通道，三者有限支撑、逐行归一），
证两件事：(i) 对完整联合按材料证据条件化后取 Y 边际，恰等于"逐 θ 用同一观察
通道加权后验"的显式和（同一 Y 读数）；(ii) 后验均值可交换求和序
（有限 Fubini）。配归一化定理、数值见证与"换通道即换预测"见证（不另造目标：
预测必须读取声明的那个观察通道）。

**25 `exact_amount_denotation`（数量 AST 的有理嵌入/除法 guard/单位）**：
锚 `Seams/Probability.lean:401` 只读 `exactAmountQ`；本件建完整数量 AST
`QtyAst`（整字面量/加/乘/带 guard 的除/挂单位），指称到 `Option QtyVal`
（ℚ 值＋单位串）：整叶按 ℤ→ℚ 精确嵌入；除法节点要求除数无量纲且非零
（否则 `none`，fail-closed）；加法要求单位一致（否则 `none`）；乘法要求
一侧无量纲（量纲纪律）；挂单位保值改标。结构归纳定理：无除节点的 AST 只要
指称成功，其值必是某整数的 ℚ 像（全程无舍入、无浮点）。
`exactAmount_bridge` 把 `ExactAmountM5` 桥到本 AST（与锚文件的 `exactAmountQ`
在最小货币单位上定义一致）。

**26 `rounding_matches_rule`（七字段规则记录＋带符号商余数＋半值分支）**：
主文 §6.5："舍入记录依据、单位、刻度、方向、半值处理、发生节点、输入基数"
——七字段 `RoundingRule`。舍入核心不依赖语言默认除法：自建 `natQR`
（结构递归的欧几里得商余数，`m = d·q + r ∧ r < d` 由归纳证明），带符号值按
正负分支处理；nearest 比较 `2r` 与 `d`，半值按具名策略（halfUp＝数轴向 +∞、
halfDown＝向 −∞）。七字段全部被 `applyRule` 读取：依据空／节点不符／刻度为零
三者 fail-closed 返回 `none`（policy 不是无效装饰）；单位、输入基数、节点回执
进输出；方向与半值进算术分支。误差界在节点处证明（nearest 的
`2·|取整值 − n| ≤ d`），floor/ceil 各有单侧刻度界。

## 二、数学对象

- 离散 CDF：`cdfAt ρ p b = ∑ x, if ρ x ≤ b then p x else 0`（ρ 为秩函数）；
  闭区间质量 `bandMass ρ p lo hi = ∑ x, if lo ≤ ρ x ∧ ρ x ≤ hi then p x else 0`。
- 共享机制：`sharedJoint π q : Θ × Nty → ℚ`；参数边际 `paramMarginal`＝对条件化
  结果按 Nty 求和。
- 预测模型：`PredictiveLegalModel`（prior/material/obs 三通道＋九条非负与归一
  字段）；联合 `legalJoint`、材料事件 `materialEvent`、材料后验 `matPosterior`、
  后验预测 `posteriorPredictive`。
- 数量 AST：`QtyAst` 五构造子；`QtyVal = { val : ℚ, unit : String }`；
  `divFree` 布尔谓词标记无除片段。
- 舍入：`natQR : ℕ → ℕ → ℕ × ℕ`（欧几里得商余数）；`RoundDir`（floor/ceil/nearest）
  与 `HalfPolicy`（halfUp/halfDown）；`candLow/candHigh` 候选倍数；
  `pickPos/pickNeg` 正负基数上的方向选择；`roundCore` 带符号合成；
  `RoundingRule` 七字段＋`RoundedOutcome` 四字段回执＋`applyRule`。

## 三、证与不证

**证**：§22 的 CDF 单调性、端点无原子下闭区间质量＝CDF 差、原子反例、后验实例
化（针名主定理）；§23 的观察/选择两因子分解引理、双重条件化正性、消因子搬运
主定理、参数读选择失效见证；§24 的联合-材料质量恒等、同一 Y 边际＝显式和、
后验均值交换、预测归一、数值见证与通道追踪见证；§25 的整叶嵌入、除零
fail-closed、单位失配 fail-closed、挂单位保值、无除片段整值结构归纳、五合一
针名主定理、ExactAmountM5 桥、乘/除数值见证；§26 的 natQR 归纳规范、floor/ceil
单侧界、nearest 双侧误差界、七字段回执与 fail-closed 三定理、针名主定理、
发生节点承重见证、正负半值数值见证。零 `sorry`／零 `admit`／零自定义 `axiom`。

**不证**（全部是刻意的降级，不是疏漏）：

- §22/§23/§24 一律是**有限支撑（Fintype）离散**版本：不证连续 Beta 测度的
  区间质量（连续侧已有 `BetaInterval.betaMass`＝CDF 差的定义式，本件不重证、
  不冒称等价）、不证连续 θ 的 Beta(3,1) 对 Beta(2,1)（边界见证是它的有限形态）、
  不证 Dirichlet 积分比 `(α_i+n_i)/(Σα+n)` 的测度论推导（其权重层恒等式在
  `DirichletPosterior.dirWeights` 内自证）。
- §22 不外推固定参数频率覆盖：闭区间质量是模型内可信质量，不是频率覆盖，
  更不是个案事实成立（主文 §7.4 明文），本件不含任何覆盖性声明。
- §23 不证任意（非嵌套、非因子化）制度对的选择可忽略性；不接连续机制核
  `Q_θ(de,dz|h,a)` 的测度论形态；识别失败（只有样本胜率、不知选择机制）的
  识别集输出未建。
- §24 不证 `Y_actual` 与 `Y_allowed` 的相等或投影对应（主文 §7.1 要求显式假设
  才可桥接，本件只建同一 Y 的读数定理）；不证停止规则/删失/未选样本的设计
  修正；不声称任何真实案件的预测。
- §25 不建超越函数 AST、不做区间算术、不证指称的唯一规范化（分母既约性）；
  单位代数只有"同单位相加、单侧无量纲相乘、除数无量纲"三条纪律，不建完整
  量纲演算；`withUnit` 允许显式改标（改标是显式动作，不冒称单位守恒）。
- §26 不证最优性/唯一性/法定舍入策略的正确性（七字段语义是显式声明，
  `halfUp` 的"向 +∞"是本件的具名定义，不是任何法条的转写）；不接货币汇率
  或最小单位换算；误差界只到刻度级（`2|Δ| ≤ d`），不做下游传播放大。
- 全件不运行 Lean（本机无 Lean，见 AGENTS.md 执行边界），所有证明的编译
  认定以 GitHub Actions 为唯一权威；本地状态 `CI_NOT_RUN`（fail-closed）。

## 四、未覆盖片段

1. 连续 Beta/Dirichlet 测度层与有限支撑离散层的**同构桥**（除定义式
   `betaMass` 外无定理）。
2. 选择因子的可忽略性一般刻画（何时仍可搬运的完整条件），本件只有因子化
   机制下的正向定理＋读参数时的单点失效。
3. `Y_actual`＝`Y_allowed` 的支持条件与投影对应。
4. 数量 AST 的量纲演算与既约有理规范化。
5. 舍入误差的下游传播链（主文 §6.5"再经下游运算放大"未接）。
6. 与 `Seams/Probability.lean` 既有 `BetaGenModel` 的读数统一（本件不 import
   该模块，避免同名弱式冒充新合同）。

## 五、档位

`SEAM_S3B_LOCAL_PROVISIONAL`：本地单模块静态写成，未编译（`CI_NOT_RUN`，
fail-closed）。BLOCKER：无（五针主定理均已按上述离散有限支撑合同写出完整
证明；若 CI 编译报错，按仓规修复后重新触发模块矩阵，不得以 sorry 销账）。
禁止把本件读成"22–26 针已闭环"或"连续概率层已形式化"。
-/

namespace JurisLean.Seams.UnifiedNeedlesS3b

open Finset
open JurisLean.FullMath.Probability

/-! ## 一、针 22：闭区间质量＝CDF 差（端点无原子） -/

section Needle22

variable {X : Type} [Fintype X]

/-- 离散 CDF（按秩函数 ρ）：秩不超过 b 的状态质量之和。
    载体是有限支撑（Fintype）——这是本件的显式合同，不是连续测度的 CDF。 -/
def cdfAt (ρ : X → ℕ) (p : X → ℚ) (b : ℕ) : ℚ :=
  ∑ x, if ρ x ≤ b then p x else 0

/-- 闭区间 [lo, hi] 的质量：秩落在区间内的状态质量之和。 -/
def bandMass (ρ : X → ℕ) (p : X → ℚ) (lo hi : ℕ) : ℚ :=
  ∑ x, if lo ≤ ρ x ∧ ρ x ≤ hi then p x else 0

/-- CDF 单调：质量非负时 CDF 随阈值不减（离散 CDF 的基本性质）。 -/
theorem cdfAt_mono (ρ : X → ℕ) (p : X → ℚ) (hp : ∀ x, 0 ≤ p x) (b b' : ℕ)
    (h : b ≤ b') : cdfAt ρ p b ≤ cdfAt ρ p b' := by
  unfold cdfAt
  refine Finset.sum_le_sum (fun x _ => ?_)
  by_cases hx : ρ x ≤ b
  · rw [if_pos hx, if_pos (Nat.le_trans hx h)]
  · by_cases hy : ρ x ≤ b'
    · rw [if_neg hx, if_pos hy]; exact hp x
    · rw [if_neg hx, if_neg hy]

/-- 逐点分解：右侧两支（区间内＋左闭以下）之和恰是"CDF 于 hi"的逐项贡献，
    唯一的多算点在秩恰为 lo 的状态上——那里由端点无原子假设清零。 -/
theorem closed_band_mass_eq_cdf_diff (ρ : X → ℕ) (p : X → ℚ) (lo hi : ℕ)
    (hle : lo ≤ hi) (hAtom : ∀ x, ρ x = lo → p x = 0) :
    bandMass ρ p lo hi = cdfAt ρ p hi − cdfAt ρ p lo := by
  have key : ∀ x : X, (if ρ x ≤ hi then p x else 0)
      = (if lo ≤ ρ x ∧ ρ x ≤ hi then p x else 0) + (if ρ x ≤ lo then p x else 0) := by
    intro x
    rcases Nat.lt_trichotomy (ρ x) lo with hlt | heq | hgt
    · rw [if_pos (by omega : ρ x ≤ hi), if_neg (by omega : ¬(lo ≤ ρ x ∧ ρ x ≤ hi)),
        if_pos (by omega : ρ x ≤ lo)]
      ring
    · have hpx : p x = 0 := hAtom x heq
      rw [if_pos (by omega : ρ x ≤ hi),
        if_pos (by omega : lo ≤ ρ x ∧ ρ x ≤ hi), if_pos (by omega : ρ x ≤ lo), hpx]
      ring
    · rcases Nat.lt_trichotomy (ρ x) hi with hlt2 | heq2 | hgt2
      · rw [if_pos (by omega : ρ x ≤ hi),
          if_pos (by omega : lo ≤ ρ x ∧ ρ x ≤ hi), if_neg (by omega : ¬(ρ x ≤ lo))]
        ring
      · rw [if_pos (by omega : ρ x ≤ hi),
          if_neg (by omega : ¬(lo ≤ ρ x ∧ ρ x ≤ hi)), if_neg (by omega : ¬(ρ x ≤ lo))]
        ring
  have hsum : cdfAt ρ p hi = bandMass ρ p lo hi + cdfAt ρ p lo := by
    unfold cdfAt bandMass
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun x _ => key x)
  linarith

/-- 端点无原子不可去：秩 0 上有原子的两点分布，闭区间质量 ≠ CDF 差。
    有限支撑非退化分布必有原子，故"无原子性"只能落在端点上——这正是连续版
    与离散版的强度差，本条把它钉成机器反例。 -/
def rankTwo : Bool → ℕ := fun b => if b then 1 else 0

/-- 边界反例数据：全部质量放在秩 0。 -/
def atomAtLow : Bool → ℚ := fun b => if b then 0 else 1

theorem closed_mass_needs_atomfree_endpoint :
    ¬ (bandMass rankTwo atomAtLow 0 1 = cdfAt rankTwo atomAtLow 1 − cdfAt rankTwo atomAtLow 0) := by
  intro h
  have h1 : bandMass rankTwo atomAtLow 0 1 = 1 := by
    simp only [bandMass, Fin.sum_univ_two]; norm_num
  have h2 : cdfAt rankTwo atomAtLow 1 = 1 := by
    simp only [cdfAt, Fin.sum_univ_two]; norm_num
  have h3 : cdfAt rankTwo atomAtLow 0 = 1 := by
    simp only [cdfAt, Fin.sum_univ_two]; norm_num
  rw [h1, h2, h3] at h
  norm_num at h

/-- 针 22 主定理（原验收名 `beta_interval_posterior_mass`）：对任意有限支撑
    条件化后验（`Conditioning.posterior`），若区间左端点的秩上无原子，则闭区间
    后验质量＝CDF 差。诚实声明：这是**有限支撑离散**版——载体是 `Fintype X` 上的
    质量函数，不是连续 Beta 测度；连续侧对应物是 `BetaInterval.betaMass`
    （已是 CDF 差的定义式，本件不重证、不冒称两层等价）。可信质量不是频率覆盖。 -/
theorem beta_interval_posterior_mass {X : Type} [Fintype X] [DecidableEq X]
    (ρ : X → ℕ) (p₀ : X → ℚ) (e : X → Bool) (hZ : 0 < evMass p₀ e) (lo hi : ℕ)
    (hle : lo ≤ hi) (hAtom : ∀ x, ρ x = lo → posterior p₀ e hZ x = 0) :
    bandMass ρ (posterior p₀ e hZ) lo hi
      = cdfAt ρ (posterior p₀ e hZ) hi − cdfAt ρ (posterior p₀ e hZ) lo :=
  closed_band_mass_eq_cdf_diff ρ (posterior p₀ e hZ) lo hi hle hAtom

end Needle22

/-! ## 二、针 23：共享机制＋选择条件消因子 -/

section Needle23

variable {Θ : Type} [Fintype Θ] {Nty : Type} [Fintype Nty]

/-- 共享生成机制的因子化联合：参数分量 π(θ) 与共享无关分量 q(n) 的乘积。
    主文 §7.3 的"共享机制"在有限支撑下的机器形态。 -/
def sharedJoint (π : Θ → ℚ) (q : Nty → ℚ) : Θ × Nty → ℚ :=
  fun ω => π ω.1 * q ω.2

/-- 参数边际：把条件化后的联合按共享分量求和，得到参数 θ 的（非归一）边际读数。
    hZ 是证据质量为正的显式前提（沿用 `Conditioning` 的 fail-closed 合同）。 -/
def paramMarginal (p : Θ × Nty → ℚ) (ev : Θ × Nty → Bool)
    (hZ : 0 < evMass p ev) (θ : Θ) : ℚ :=
  ∑ n, posterior p ev hZ (θ, n)

/-- 观察读 θ 时的证据质量：因子化联合上只按 θ 侧观察条件化，证据质量就是
    参数侧的观察质量（共享分量按归一化吸收）。 -/
theorem evMass_shared_obs (π : Θ → ℚ) (q : Nty → ℚ) (E : Θ → Bool)
    (hq1 : ∑ n, q n = 1) :
    evMass (sharedJoint π q) (fun ω => E ω.1) = ∑ θ, if E θ then π θ else 0 := by
  unfold evMass sharedJoint
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun θ _ => ?_)
  by_cases hE : E θ = true
  · rw [if_pos hE, ← Finset.mul_sum, hq1, mul_one]
  · rw [if_neg hE]
    simp

/-- 选择读 n 时的双重证据质量因子分解：观察（读 θ）∧选择（读 n）的证据质量
    ＝参数侧观察质量 × 选择质量。选择质量因子 c_S 是后面被约掉的那个因子。 -/
theorem evMass_shared_sel_obs (π : Θ → ℚ) (q : Nty → ℚ) (E : Θ → Bool) (S : Nty → Bool) :
    evMass (sharedJoint π q) (fun ω => E ω.1 && S ω.2)
      = (∑ θ, if E θ then π θ else 0) * (∑ n, if S n then q n else 0) := by
  unfold evMass sharedJoint
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun θ _ => ?_)
  by_cases hE : E θ = true
  · simp only [hE, Bool.true_and, if_pos hE, ← Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    by_cases hS : S n = true
    · rw [if_pos hS, if_pos hS, mul_comm]
    · rw [if_neg hS, if_neg hS, mul_zero]
  · simp only [hE, Bool.false_and, if_neg hE, mul_zero]
    simp

/-- 双重条件化的两个正性前提都可由"参数侧观察质量＞0 ∧ 选择质量＞0"导出，
    主定理里的正性假设不是白拿的。 -/
theorem shared_selection_masses_pos (π : Θ → ℚ) (q : Nty → ℚ) (E : Θ → Bool)
    (S : Nty → Bool) (hq1 : ∑ n, q n = 1)
    (hZe : 0 < ∑ θ, if E θ then π θ else 0) (hS : 0 < ∑ n, if S n then q n else 0) :
    0 < evMass (sharedJoint π q) (fun ω => E ω.1 && S ω.2) ∧
      0 < evMass (sharedJoint π q) (fun ω => E ω.1) := by
  rw [evMass_shared_sel_obs, evMass_shared_obs _ _ _ hq1]
  exact ⟨mul_pos hZe hS, by rw [mul_one]; exact hZe⟩

/-- 针 23 主定理（原验收名 `selection_transport_from_shared_mechanism`）：
    共享生成机制（因子化联合）＋选择只读共享无关分量时，选择条件在参数后验
    边际中**约去**——"观察∧选择"双重条件化后的参数边际＝仅观察条件化的参数边际。
    机制是函数（`sharedJoint π q`），制度是谓词（E 读 θ、S 读 n），
    搬运方程就是这条逐 θ 等式。诚实声明（降级）：有限支撑版；只覆盖因子化机制
    与"选择不读参数"的制度；参数相关选择不成立（见下条边界）。 -/
theorem selection_transport_from_shared_mechanism (π : Θ → ℚ) (q : Nty → ℚ)
    (E : Θ → Bool) (S : Nty → Bool) (hq1 : ∑ n, q n = 1)
    (hZb : 0 < evMass (sharedJoint π q) (fun ω => E ω.1 && S ω.2))
    (hZo : 0 < evMass (sharedJoint π q) (fun ω => E ω.1)) :
    ∀ θ : Θ, paramMarginal (sharedJoint π q) (fun ω => E ω.1 && S ω.2) hZb θ
      = paramMarginal (sharedJoint π q) (fun ω => E ω.1) hZo θ := by
  have hZbeq : evMass (sharedJoint π q) (fun ω => E ω.1 && S ω.2)
      = (∑ θ, if E θ then π θ else 0) * (∑ n, if S n then q n else 0) :=
    evMass_shared_sel_obs π q E S
  have hZoeq : evMass (sharedJoint π q) (fun ω => E ω.1) = ∑ θ, if E θ then π θ else 0 :=
    evMass_shared_obs π q E hq1
  have hZP : (∑ θ', if E θ' then π θ' else 0) ≠ 0 := by
    rw [← hZoeq]; exact ne_of_gt hZo
  have hSne : (∑ n, if S n then q n else 0) ≠ 0 := by
    intro hc
    rw [hZbeq, hc, mul_zero] at hZb
    exact absurd hZb (by norm_num)
  intro θ
  by_cases hE : E θ = true
  · have hL : paramMarginal (sharedJoint π q) (fun ω => E ω.1 && S ω.2) hZb θ
        = ((π θ * (∑ n, if S n then q n else 0))
            / evMass (sharedJoint π q) (fun ω => E ω.1 && S ω.2)) := by
    unfold paramMarginal posterior sharedJoint
    have hstep : ∀ n : Nty,
        (if E θ && S n then π θ * q n / evMass (sharedJoint π q) (fun ω => E ω.1 && S ω.2)
          else 0)
        = (if S n then π θ * q n else 0)
            / evMass (sharedJoint π q) (fun ω => E ω.1 && S ω.2) := by
      intro n
      simp only [hE, Bool.true_and]
      by_cases hS : S n = true
      · rw [if_pos hS, if_pos hS]
      · rw [if_neg hS, if_neg hS, zero_div]
    calc ∑ n, (if E θ && S n
            then π θ * q n / evMass (sharedJoint π q) (fun ω => E ω.1 && S ω.2) else 0)
        = ∑ n, (if S n then π θ * q n else 0)
            / evMass (sharedJoint π q) (fun ω => E ω.1 && S ω.2) :=
          Finset.sum_congr rfl (fun n _ => hstep n)
      _ = (∑ n, if S n then π θ * q n else 0)
            / evMass (sharedJoint π q) (fun ω => E ω.1 && S ω.2) := Finset.sum_div
      _ = (π θ * (∑ n, if S n then q n else 0))
            / evMass (sharedJoint π q) (fun ω => E ω.1 && S ω.2) := by
          rw [← Finset.mul_sum]
          exact Finset.sum_congr rfl (fun n _ => by
            by_cases hS : S n = true
            · rw [if_pos hS, if_pos hS, mul_comm]
            · rw [if_neg hS, if_neg hS, mul_zero])
  · have hR : paramMarginal (sharedJoint π q) (fun ω => E ω.1) hZo θ
        = ((π θ * (∑ n, q n)) / evMass (sharedJoint π q) (fun ω => E ω.1)) := by
    unfold paramMarginal posterior sharedJoint
    have hstep : ∀ n : Nty,
        (if E θ then π θ * q n / evMass (sharedJoint π q) (fun ω => E ω.1) else 0)
        = (π θ * q n) / evMass (sharedJoint π q) (fun ω => E ω.1) := by
      intro n
      rw [if_pos hE]
    calc ∑ n, (if E θ then π θ * q n / evMass (sharedJoint π q) (fun ω => E ω.1) else 0)
        = ∑ n, (π θ * q n) / evMass (sharedJoint π q) (fun ω => E ω.1) :=
          Finset.sum_congr rfl (fun n _ => hstep n)
      _ = (∑ n, π θ * q n) / evMass (sharedJoint π q) (fun ω => E ω.1) := Finset.sum_div
      _ = (π θ * (∑ n, q n)) / evMass (sharedJoint π q) (fun ω => E ω.1) := by
          rw [← Finset.mul_sum]
    rw [hL, hR, hZbeq, hZoeq, hq1, mul_one]
    field_simp [hZP, hSne]
  · simp only [Bool.not_eq_true] at hE
    have hzeroB : ∀ n : Nty,
        posterior (sharedJoint π q) (fun ω => E ω.1 && S ω.2) hZb (θ, n) = 0 := by
      intro n
      unfold posterior
      simp only [hE, Bool.false_and]
      rw [if_neg (by decide)]
    have hzeroO : ∀ n : Nty,
        posterior (sharedJoint π q) (fun ω => E ω.1) hZo (θ, n) = 0 := by
      intro n
      unfold posterior
      simp only [hE]
      rw [if_neg (by decide)]
    unfold paramMarginal
    rw [Finset.sum_congr rfl (fun n _ => hzeroB n),
      Finset.sum_congr rfl (fun n _ => hzeroO n)]

/-- 针 23 边界（参数相关选择进入完整似然）：选择改读参数坐标（`ω.1`）时，
    "观察∧选择"的参数边际不再等于仅观察的参数边际。这是主文 §7.3
    "仅 S⊥Y|θ,x 不够（似然变 θ²）"现象的有限支撑机器见证：均匀 π、均匀 q、
    全真观察 E；选择读参数时 θ=true 的边际从 1/2 变成 1——选择携带参数信息，
    必须留在完整似然里，不能当可忽略因子约掉。 -/
theorem parameter_reading_selection_enters_likelihood :
    paramMarginal (sharedJoint (fun _ => (1 / 2 : ℚ)) (fun _ => (1 / 2 : ℚ)))
      (fun ω : Bool × Bool => true && ω.1)
      (by simp only [evMass, sharedJoint, Fintype.sum_prod_type, Fin.sum_univ_two]; norm_num)
      true
    ≠ paramMarginal (sharedJoint (fun _ => (1 / 2 : ℚ)) (fun _ => (1 / 2 : ℚ)))
      (fun _ => true)
      (by simp only [evMass, sharedJoint, Fintype.sum_prod_type, Fin.sum_univ_two]; norm_num)
      true := by
  intro h
  simp only [paramMarginal, posterior, evMass, sharedJoint, Fintype.sum_prod_type,
    Fin.sum_univ_two] at h
  norm_num at h

end Needle23

/-! ## 三、针 24：后验预测＝同一 Y 的显式和 -/

section Needle24

variable {Θ : Type} [Fintype Θ] [DecidableEq Θ]
variable {Mt : Type} [Fintype Mt] [DecidableEq Mt]
variable {Yty : Type} [Fintype Yty] [DecidableEq Yty]

/-- 后验预测法律模型：事件 θ（先验）→ 材料 m（材料通道）→ 裁判观察 y（观察通道），
    三者有限支撑、逐行非负归一。材料与观察在给定 θ 下条件独立——由联合的
    因子化定义承载（主文 §7.3"须给同一法律观察 Y 的条件机制"）。 -/
structure PredictiveLegalModel where
  /-- 事件类型上的先验。 -/
  prior : Θ → ℚ
  /-- 材料通道：P(材料 m | 事件 θ)。 -/
  material : Θ → Mt → ℚ
  /-- 观察通道：P(观察 y | 事件 θ)——后验预测读取的同一 Y。 -/
  obs : Θ → Yty → ℚ
  /-- 先验逐点非负。 -/
  prior_nonneg : ∀ θ, 0 ≤ prior θ
  /-- 材料通道逐点非负。 -/
  material_nonneg : ∀ θ m, 0 ≤ material θ m
  /-- 观察通道逐点非负。 -/
  obs_nonneg : ∀ θ y, 0 ≤ obs θ y
  /-- 先验归一。 -/
  prior_one : ∑ θ, prior θ = 1
  /-- 材料通道逐行归一。 -/
  material_one : ∀ θ, ∑ m, material θ m = 1
  /-- 观察通道逐行归一。 -/
  obs_one : ∀ θ, ∑ y, obs θ y = 1

/-- 完整联合：P(θ, m, y) = 先验 × 材料通道 × 观察通道（条件独立的因子化形态）。 -/
def legalJoint (mdl : PredictiveLegalModel) : Θ × Mt × Yty → ℚ :=
  fun w => mdl.prior w.1 * mdl.material w.2.1 * mdl.obs w.2.2

/-- 材料证据事件：联合状态的第二分量恰为观察到的材料 m。 -/
def materialEvent (m : Mt) : Θ × Mt × Yty → Bool :=
  fun w => decide (m = w.2.1)

/-- 材料证据质量：∑_θ 先验×材料。 -/
def matMass (mdl : PredictiveLegalModel) (m : Mt) : ℚ :=
  ∑ θ, mdl.prior θ * mdl.material θ m

/-- 材料后验：θ 的后验读数。hZ 为正性前提（fail-closed）。 -/
def matPosterior (mdl : PredictiveLegalModel) (m : Mt)
    (hZ : 0 < matMass mdl m) (θ : Θ) : ℚ :=
  mdl.prior θ * mdl.material θ m / matMass mdl m

/-- 后验预测：对**同一观察通道**按后验加权的显式有限和（有限支撑版的
    "积分后验预测"）。 -/
def posteriorPredictive (mdl : PredictiveLegalModel) (m : Mt)
    (hZ : 0 < matMass mdl m) (y : Yty) : ℚ :=
  ∑ θ, mdl.obs θ y * matPosterior mdl m hZ θ

/-- 联合按材料证据条件化的证据质量恰等于材料质量——两个正性前提互通。 -/
theorem legalJoint_material_mass (mdl : PredictiveLegalModel) (m : Mt) :
    evMass (legalJoint mdl) (materialEvent m) = matMass mdl m := by
  unfold evMass legalJoint materialEvent matMass
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun θ _ => ?_)
  have hY : ∀ mt : Mt, ∑ y : Yty,
      (if m = mt then mdl.prior θ * mdl.material θ mt * mdl.obs θ y else 0)
      = (if m = mt then mdl.prior θ * mdl.material θ mt else 0) := by
    intro mt
    by_cases hm : m = mt
    · rw [if_pos hm, if_pos hm, mdl.obs_one θ, mul_one]
    · rw [if_neg hm, if_neg hm]
  simp only [hY]
  exact Fintype.sum_ite_eq m (fun mt => mdl.prior θ * mdl.material θ mt)

/-- 针 24 主定理（原验收名 `posterior_predictive_legal_target`）：
    (i) 同一 Y 读数——对完整联合按材料证据条件化后取 Y 边际，恰等于"逐 θ 用
    声明的观察通道加权材料后验"的显式和（后验预测不另造目标，读取的就是
    联合里的那个 Y 坐标）；
    (ii) 后验均值交换——任意读数函数 v 之下，先对 Y 求均值再对 θ 积分
    ＝先按同一通道算逐 θ 均值再加权后验（有限 Fubini 的显式和形态）。
    诚实声明：有限支撑（Fintype）版；`Y_actual` 与 `Y_allowed` 的相等或投影
    对应不在本定理内（须显式假设，主文 §7.1）。 -/
theorem posterior_predictive_legal_target (mdl : PredictiveLegalModel) (m : Mt)
    (hZ : 0 < matMass mdl m)
    (hZj : 0 < evMass (legalJoint mdl) (materialEvent m)) :
    (∀ y : Yty, ∑ θ, ∑ mt, posterior (legalJoint mdl) (materialEvent m) hZj (θ, mt, y)
        = posteriorPredictive mdl m hZ y)
    ∧ (∀ v : Yty → ℚ, ∑ y, v y * posteriorPredictive mdl m hZ y
        = ∑ θ, (∑ y, v y * mdl.obs θ y) * matPosterior mdl m hZ θ) := by
  refine ⟨?_, ?_⟩
  · intro y
    simp only [posterior, legalJoint, materialEvent, decide_eq_true_eq]
    refine Finset.sum_congr rfl (fun θ _ => ?_)
    rw [Fintype.sum_ite_eq, legalJoint_material_mass mdl m]
    simp only [posteriorPredictive, matPosterior]
    refine Finset.sum_congr rfl (fun θ _ => ?_)
    rw [mul_div_assoc]
    ring
  · intro v
    simp only [posteriorPredictive, matPosterior]
    have hstep : ∀ y : Yty, v y * ∑ θ, mdl.obs θ y
          * (mdl.prior θ * mdl.material θ m / matMass mdl m)
        = ∑ θ, v y * mdl.obs θ y * (mdl.prior θ * mdl.material θ m / matMass mdl m) := by
      intro y
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun θ _ => by ring)
    simp only [hstep]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun θ _ => ?_)
    rw [← Finset.sum_mul]
    exact Finset.sum_congr rfl (fun y _ => by ring)

/-- 后验预测归一：显式和是一份分布（材料后验与观察通道各自归一的合成）。 -/
theorem posterior_predictive_normalizes (mdl : PredictiveLegalModel) (m : Mt)
    (hZ : 0 < matMass mdl m) : ∑ y, posteriorPredictive mdl m hZ y = 1 := by
  simp only [posteriorPredictive, matPosterior]
  rw [Finset.sum_comm]
  have key : ∀ θ : Θ, ∑ y, mdl.obs θ y * (mdl.prior θ * mdl.material θ m / matMass mdl m)
      = (mdl.prior θ * mdl.material θ m / matMass mdl m) * 1 := by
    intro θ
    rw [← Finset.sum_mul, mdl.obs_one θ, mul_one]
  simp only [key, mul_one]
  rw [← Finset.sum_div]
  rw [show ∑ θ, mdl.prior θ * mdl.material θ m = matMass mdl m from rfl]
  exact div_self (ne_of_gt hZ)

end Needle24
