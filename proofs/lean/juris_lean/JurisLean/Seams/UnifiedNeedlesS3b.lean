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
可信质量"读法——一个（后验）分布落在闭区间 `[lo, hi]` 的质量等于 CDF 在两端点
取值之差，前提是左端点无原子。连续分布里"无原子性"是全称条件；有限支撑非退化
离散分布不可能处处无原子，故本件的诚实形态是**端点无原子**（秩等于 lo 的状态
质量为 0）。边界定理 `closed_mass_needs_atomfree_endpoint` 给出反例：左端点带
原子时等式失效。

**23 `selection_transport_from_shared_mechanism`（共享机制＋选择消因子）**：
主文 §7.3：似然必须含选择；只有当选择只读与参数无关的共享机制分量、且相应设计
已条件化时，选择因子才在参数后验边际里约去。本件把共享机制建成有限乘积空间
`Θ × Nty` 上的因子化联合 `sharedJoint π q`：观察读 θ、选择读 n，则双重条件化后
的参数边际＝仅观察条件化的参数边际（选择质量因子在分子分母同时出现而约去）。
边界定理 `parameter_reading_selection_enters_likelihood`：选择改读参数坐标时
搬运逐点失效（§7.3"仅独立不够、似然变 θ²"现象的有限形态）。

**24 `posterior_predictive_legal_target`（后验预测＝同一 Y 的显式和）**：
主文 §7.1/§7.3：事件 → 材料 → 裁判观察 Y 的联合由同一采样机制给出，后验预测是
对**同一个 Y** 按后验积分（有限支撑下是显式有限和），不另造目标。证两件事：
(i) 对完整联合按材料证据条件化后取 Y 边际＝逐 θ 用同一观察通道加权后验的显式和；
(ii) 后验均值可交换求和序（有限 Fubini）。配归一化、数值见证与"换通道即换预测"
见证（预测必须读取声明的那个观察通道）。

**25 `exact_amount_denotation`（数量 AST 的有理嵌入/除法 guard/单位）**：
锚 `Seams/Probability.lean:401` 只读 `exactAmountQ`；本件建完整数量 AST `QtyAst`
（整叶/加/乘/带 guard 除/挂单位），指称到 `Option QtyVal`：整叶按 ℤ→ℚ 精确嵌入；
除法节点要求除数无量纲且非零（否则 `none`，fail-closed）；加法要求同单位（否则
`none`）；乘法要求一侧无量纲（量纲纪律）；挂单位保值改标。结构归纳定理：无除
片段只要指称成功，其值必是某整数的 ℚ 像（全程无舍入、无浮点）。
`exactAmount_bridge` 把 `ExactAmountM5` 桥到本 AST（与锚文件 `exactAmountQ` 的
最小货币单位读数定义一致）。

**26 `rounding_matches_rule`（七字段规则记录＋带符号商余数＋半值分支）**：
主文 §6.5："舍入记录依据、单位、刻度、方向、半值处理、发生节点、输入基数"——
七字段 `RoundingRule`。舍入核心不依赖语言默认除法：自建 `natQR`（结构递归的
欧几里得商余数，规范由归纳证明），带符号值按正负分支处理；nearest 比较 `2r`
与 `d`，半值按具名策略（halfUp＝数轴向 +∞、halfDown＝向 -∞）。七字段全部被
`applyRule` 读取：依据空／节点不符／刻度为零 fail-closed 返回 `none`（policy
不是无效装饰）；单位、输入基数、节点回执进输出；方向与半值进算术分支。误差界
在节点处证明（nearest 的 `2·(取整值 - n)` 双侧界），floor/ceil 各有单侧刻度界。

## 二、数学对象

- 离散 CDF：`cdfAt ρ p b = ∑ x, if ρ x ≤ b then p x else 0`（ρ 为秩函数）；
  闭区间质量 `bandMass ρ p lo hi`。
- 共享机制：`sharedJoint π q : Θ × Nty → ℚ`；参数边际 `paramMarginal`＝条件化
  结果按 Nty 求和。
- 预测模型：`PredictiveLegalModel`（prior/material/obs 三通道＋非负归一字段）；
  联合 `legalJoint`、材料事件 `materialEvent`、材料后验 `matPosterior`、后验预测
  `posteriorPredictive`。
- 数量 AST：`QtyAst` 五构造子；`QtyVal = { val : ℚ, unit : String }`；`divFree`
  布尔谓词标记无除片段。
- 舍入：`natQR : ℕ → ℕ → ℕ × ℕ`；`RoundDir`／`HalfPolicy`；候选倍数
  `candLow/candHigh`；正负基数选择 `pickPos/pickNeg`；带符号合成 `roundCore`；
  七字段 `RoundingRule`＋回执 `RoundedOutcome`＋`applyRule`。

## 三、证与不证

**证**：§22 CDF 单调、端点无原子下闭区间质量＝CDF 差、原子反例、后验实例化
（针名主定理）；§23 观察/选择因子分解、双重条件化正性、消因子搬运主定理、
参数读选择失效见证；§24 联合-材料质量恒等、同一 Y 边际＝显式和、后验均值交换、
预测归一、数值见证与通道追踪见证；§25 整叶嵌入、除零 fail-closed、单位失配
fail-closed、挂单位保值、无除片段整值结构归纳、五合一针名主定理、
ExactAmountM5 桥、乘/除数值见证；§26 natQR 归纳规范、floor/ceil 单侧界、
nearest 双侧误差界、fail-closed 三定理、七字段回执主定理、发生节点承重见证、
正负半值数值见证。零 `sorry`／零 `admit`／零自定义 `axiom`。

**不证**（全部是刻意的降级，不是疏漏）：

- §22/§23/§24 一律是**有限支撑（Fintype）离散**版本：不证连续 Beta 测度的区间
  质量（连续侧 `BetaInterval.betaMass` 已是 CDF 差的定义式，本件不重证、不冒称
  等价）、不证连续 θ 的 Beta(3,1) 对 Beta(2,1)（边界见证是其有限形态）、不证
  Dirichlet 积分比 `(α_i+n_i)/(Σα+n)` 的测度论推导（权重层恒等式在
  `DirichletPosterior.dirWeights` 内自证）。
- §22 不外推固定参数频率覆盖：闭区间质量是模型内可信质量，不是频率覆盖，更
  不是个案事实成立（主文 §7.4 明文），本件不含任何覆盖性声明。
- §23 不证任意（非嵌套、非因子化）制度对的选择可忽略性；不接连续机制核
  `Q_θ(de,dz|h,a)`；识别失败的识别集输出未建。
- §24 不证 `Y_actual` 与 `Y_allowed` 的相等或投影对应（须显式假设才可桥接）；
  不证停止规则/删失/未选样本的设计修正；不声称任何真实案件的预测。
- §25 不建超越函数 AST、不做区间算术、不证既约有理规范化；单位代数只有
  "同单位相加、单侧无量纲相乘、除数无量纲"三条纪律，不建完整量纲演算；
  `withUnit` 允许显式改标（改标是显式动作，不冒称单位守恒）。
- §26 不证最优性/唯一性/任何法定舍入策略的正确性（`halfUp` 的"向 +∞"是本件
  的具名定义，不是法条转写）；不接货币汇率或最小单位换算；误差界只到刻度级，
  不做下游传播放大。
- 全件不在本机运行 Lean（AGENTS.md 执行边界）：编译认定以 GitHub Actions 为
  唯一权威；本地状态 `CI_NOT_RUN`（fail-closed）。

## 四、未覆盖片段

1. 连续 Beta/Dirichlet 测度层与有限支撑离散层的同构桥（除定义式 `betaMass`
   外无定理）。
2. 选择因子可忽略性的一般刻画（何时仍可搬运的完整条件）。
3. `Y_actual`＝`Y_allowed` 的支持条件与投影对应。
4. 数量 AST 的量纲演算与既约有理规范化。
5. 舍入误差的下游传播链（主文 §6.5"再经下游运算放大"未接）。
6. 与 `Seams/Probability.lean` 既有 `BetaGenModel` 的读数统一（本件不 import
   该模块，避免同名弱式冒充新合同）。

## 五、档位

`SEAM_S3B_LOCAL_PROVISIONAL`：本地单模块静态写成，未编译（`CI_NOT_RUN`，
fail-closed）。BLOCKER：无（五针主定理均已按上述离散有限支撑合同写出完整证明；
若 CI 编译报错，按仓规修复后重新触发模块矩阵，不得以 sorry 销账）。
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

/-- CDF 单调：质量非负时 CDF 随阈值不减。 -/
theorem cdfAt_mono (ρ : X → ℕ) (p : X → ℚ) (hp : ∀ x, 0 ≤ p x) (b b' : ℕ)
    (h : b ≤ b') : cdfAt ρ p b ≤ cdfAt ρ p b' := by
  unfold cdfAt
  refine Finset.sum_le_sum (fun x _ => ?_)
  by_cases hx : ρ x ≤ b
  · rw [if_pos hx, if_pos (Nat.le_trans hx h)]
  · by_cases hy : ρ x ≤ b'
    · rw [if_neg hx, if_pos hy]; exact hp x
    · rw [if_neg hx, if_neg hy]

/-- 逐点分解：闭区间项＋左闭以下项之和恰是"CDF 于 hi"的逐项贡献；
    唯一的多算点在秩恰为 lo 的状态上——由端点无原子假设清零。 -/
theorem closed_band_mass_eq_cdf_diff (ρ : X → ℕ) (p : X → ℚ) (lo hi : ℕ)
    (hle : lo ≤ hi) (hAtom : ∀ x, ρ x = lo → p x = 0) :
    bandMass ρ p lo hi = cdfAt ρ p hi - cdfAt ρ p lo := by
  have key : ∀ x : X, (if ρ x ≤ hi then p x else 0)
      = (if lo ≤ ρ x ∧ ρ x ≤ hi then p x else 0) + (if ρ x ≤ lo then p x else 0) := by
    intro x
    rcases Nat.lt_trichotomy (ρ x) lo with hlt | heq | hgt
    · rw [if_pos (show ρ x ≤ hi from by omega), if_neg (show ¬(lo ≤ ρ x ∧ ρ x ≤ hi) from by omega),
        if_pos (show ρ x ≤ lo from by omega)]
      ring
    · have hpx : p x = 0 := hAtom x heq
      rw [if_pos (show ρ x ≤ hi from by omega),
        if_pos (show lo ≤ ρ x ∧ ρ x ≤ hi from by omega), if_pos (show ρ x ≤ lo from by omega), hpx]
      ring
    · rcases Nat.lt_trichotomy (ρ x) hi with hlt2 | heq2 | hgt2
      · rw [if_pos (Nat.le_of_lt hlt2),
          if_pos ⟨Nat.le_of_lt hgt, Nat.le_of_lt hlt2⟩,
          if_neg (Nat.not_le.mpr hgt)]
        ring
      · rw [if_pos (show ρ x ≤ hi from by omega),
          if_pos (show lo ≤ ρ x ∧ ρ x ≤ hi from by omega),
          if_neg (Nat.not_le.mpr hgt)]
        ring
      · rw [if_neg (show ¬(ρ x ≤ hi) from by omega),
          if_neg (show ¬(lo ≤ ρ x ∧ ρ x ≤ hi) from by omega),
          if_neg (Nat.not_le.mpr hgt)]
        ring
  have hsum : cdfAt ρ p hi = bandMass ρ p lo hi + cdfAt ρ p lo := by
    unfold cdfAt bandMass
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun x _ => key x)
  linarith

/-- 边界反例数据：秩函数 0/1。 -/
def rankTwo : Bool → ℕ := fun b => if b then 1 else 0

/-- 边界反例分布：全部质量放在秩 0（端点原子）。 -/
def atomAtLow : Bool → ℚ := fun b => if b then 0 else 1

/-- 端点无原子不可去：秩 0 上有原子时，闭区间质量 ≠ CDF 差。
    有限支撑非退化分布必有原子，故"无原子性"只能落在端点上——这正是连续版
    与离散版的强度差，本条把它钉成机器反例。 -/
theorem closed_mass_needs_atomfree_endpoint :
    ¬ (bandMass rankTwo atomAtLow 0 1 = cdfAt rankTwo atomAtLow 1 - cdfAt rankTwo atomAtLow 0) := by
  intro h
  have h1 : bandMass rankTwo atomAtLow 0 1 = 1 := by
    simp [bandMass, rankTwo, atomAtLow]
  have h2 : cdfAt rankTwo atomAtLow 1 = 1 := by
    simp [cdfAt, rankTwo, atomAtLow]
  have h3 : cdfAt rankTwo atomAtLow 0 = 1 := by
    simp [cdfAt, rankTwo, atomAtLow]
  rw [h1, h2, h3] at h
  norm_num at h

/-- 针 22 主定理（原验收名 `beta_interval_posterior_mass`）：对任意有限支撑
    条件化后验（`Conditioning.posterior`），若区间左端点的秩上无原子，则闭区间
    后验质量＝CDF 差。诚实声明：这是**有限支撑离散**版——载体是 `Fintype X` 上
    的质量函数，不是连续 Beta 测度；连续侧对应物是 `BetaInterval.betaMass`
    （已是 CDF 差的定义式，本件不重证、不冒称两层等价）。可信质量不是频率覆盖。 -/
theorem beta_interval_posterior_mass [DecidableEq X]
    (ρ : X → ℕ) (p₀ : X → ℚ) (e : X → Bool) (hZ : 0 < evMass p₀ e) (lo hi : ℕ)
    (hle : lo ≤ hi) (hAtom : ∀ x, ρ x = lo → posterior p₀ e hZ x = 0) :
    bandMass ρ (posterior p₀ e hZ) lo hi
      = cdfAt ρ (posterior p₀ e hZ) hi - cdfAt ρ (posterior p₀ e hZ) lo :=
  closed_band_mass_eq_cdf_diff ρ (posterior p₀ e hZ) lo hi hle hAtom

end Needle22

/-! ## 二、针 23：共享机制＋选择条件消因子 -/

section Needle23

variable {Θ : Type} [Fintype Θ] [DecidableEq Θ]
variable {Nty : Type} [Fintype Nty] [DecidableEq Nty]

/-- 共享生成机制的因子化联合：参数分量 π(θ) 与共享无关分量 q(n) 的乘积。
    主文 §7.3"共享机制"在有限支撑下的机器形态。 -/
def sharedJoint (π : Θ → ℚ) (q : Nty → ℚ) : Θ × Nty → ℚ :=
  fun ω => π ω.1 * q ω.2

/-- 参数边际：把条件化后的联合按共享分量求和，得到参数 θ 的边际读数。
    hZ 是证据质量为正的显式前提（沿用 `Conditioning` 的 fail-closed 合同）。 -/
def paramMarginal (p : Θ × Nty → ℚ) (ev : Θ × Nty → Bool)
    (hZ : 0 < evMass p ev) (θ : Θ) : ℚ :=
  ∑ n, posterior p ev hZ (θ, n)

/-- 观察读 θ 时的证据质量：因子化联合上只按 θ 侧观察条件化，证据质量就是参数侧
    观察质量（共享分量按归一化被吸收）。 -/
theorem evMass_shared_obs (π : Θ → ℚ) (q : Nty → ℚ) (E : Θ → Bool)
    (hq1 : ∑ n, q n = 1) :
    evMass (sharedJoint π q) (fun ω => E ω.1) = ∑ θ, if E θ then π θ else 0 := by
  unfold evMass sharedJoint
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun θ _ => ?_)
  dsimp only
  cases hE : E θ with
  | true =>
      rw [if_pos hE]
      simp only [Finset.mul_sum]
      rw [hq1]
      ring
  | false =>
      rw [if_neg (show ¬(E θ = true) from by simp [hE])]
      simp

/-- 选择读 n 时的双重证据质量因子分解：观察（读 θ）∧选择（读 n）的证据质量
    ＝参数侧观察质量 × 选择质量。选择质量因子是后面被约掉的那个因子。 -/
theorem evMass_shared_sel_obs (π : Θ → ℚ) (q : Nty → ℚ) (E : Θ → Bool)
    (S : Nty → Bool) :
    evMass (sharedJoint π q) (fun ω => E ω.1 && S ω.2)
      = (∑ θ, if E θ then π θ else 0) * (∑ n, if S n then q n else 0) := by
  simp [evMass, sharedJoint, Fintype.sum_prod_type, Finset.mul_sum]

/-- 双重条件化的两个正性前提都可由"参数侧观察质量＞0 ∧ 选择质量＞0"导出，
    主定理里的正性假设不是白拿的。 -/
theorem shared_selection_masses_pos (π : Θ → ℚ) (q : Nty → ℚ) (E : Θ → Bool)
    (S : Nty → Bool) (hq1 : ∑ n, q n = 1)
    (hZe : 0 < ∑ θ, if E θ then π θ else 0) (hS : 0 < ∑ n, if S n then q n else 0) :
    0 < evMass (sharedJoint π q) (fun ω => E ω.1 && S ω.2) ∧
      0 < evMass (sharedJoint π q) (fun ω => E ω.1) := by
  rw [evMass_shared_sel_obs, evMass_shared_obs _ _ _ hq1]
  refine ⟨mul_pos hZe hS, ?_⟩
  simpa using hZe

/-- 针 23 主定理（原验收名 `selection_transport_from_shared_mechanism`）：
    共享生成机制（因子化联合）＋选择只读共享无关分量时，选择条件在参数后验
    边际中**约去**——"观察∧选择"双重条件化后的参数边际＝仅观察条件化的参数
    边际。机制是函数（`sharedJoint π q`），制度是谓词（E 读 θ、S 读 n），
    搬运方程就是这条逐 θ 等式。诚实声明（降级）：有限支撑版；只覆盖因子化
    机制与"选择不读参数"的制度；参数相关选择不成立（见下条边界）。 -/
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
  cases hE : E θ with
  | true =>
    have hL : paramMarginal (sharedJoint π q) (fun ω => E ω.1 && S ω.2) hZb θ
        = ((π θ * (∑ n, if S n then q n else 0))
            / evMass (sharedJoint π q) (fun ω => E ω.1 && S ω.2)) := by
      have hstep : ∀ n : Nty,
          (if E θ && S n then (sharedJoint π q) (θ, n)
              / evMass (sharedJoint π q) (fun ω => E ω.1 && S ω.2) else 0)
          = (if S n then π θ * q n else 0)
              / evMass (sharedJoint π q) (fun ω => E ω.1 && S ω.2) := by
        intro n
        by_cases hS : S n = true
        · rw [if_pos (show (E θ && S n) = true from by simp [hE, hS]), if_pos hS]
        · rw [if_neg (show ¬((E θ && S n) = true) from by simp [hE, hS]), if_neg hS, zero_div]
          rfl
      simp only [paramMarginal, posterior, hstep]
      rw [Finset.sum_div]
      rw [show (∑ n, if S n then π θ * q n else 0)
            = π θ * (∑ n, if S n then q n else 0) from by
          rw [← Finset.mul_sum]
          exact Finset.sum_congr rfl (fun n _ => by
            by_cases hS : S n = true
            · rw [if_pos hS, if_pos hS, mul_comm]
            · rw [if_neg hS, if_neg hS, mul_zero])]
    have hR : paramMarginal (sharedJoint π q) (fun ω => E ω.1) hZo θ
        = ((π θ * (∑ n, q n)) / evMass (sharedJoint π q) (fun ω => E ω.1)) := by
      have hstep : ∀ n : Nty,
          (if E θ then (sharedJoint π q) (θ, n)
              / evMass (sharedJoint π q) (fun ω => E ω.1) else 0)
          = (sharedJoint π q) (θ, n) / evMass (sharedJoint π q) (fun ω => E ω.1) := by
        intro n
        rw [if_pos hE]
      simp only [paramMarginal, posterior, hstep]
      rw [Finset.sum_div]
      rw [show (∑ n, (sharedJoint π q) (θ, n)) = ∑ n, π θ * q n from by
          simp only [sharedJoint], ← Finset.mul_sum]
    rw [hL, hR, hZbeq, hZoeq, hq1, mul_one]
    field_simp [hZP, hSne]
  | false =>
    have hzeroB : ∀ n : Nty,
        posterior (sharedJoint π q) (fun ω => E ω.1 && S ω.2) hZb (θ, n) = 0 := by
      intro n
      simp only [posterior, hE, Bool.false_and]
      rw [if_neg (by decide)]
    have hzeroO : ∀ n : Nty,
        posterior (sharedJoint π q) (fun ω => E ω.1) hZo (θ, n) = 0 := by
      intro n
      simp only [posterior, hE]
      rw [if_neg (by decide)]
    simp only [paramMarginal, hzeroB, hzeroO]

/-- 针 23 边界（参数相关选择进入完整似然）：选择改读参数坐标（`ω.1`）时，
    "观察∧选择"的参数边际不再等于仅观察的参数边际。这是主文 §7.3
    "仅 S⊥Y|θ,x 不够（似然变 θ²）"现象的有限支撑机器见证：均匀 π、均匀 q、
    全真观察 E；选择读参数时 θ=true 的边际从 1/2 变成 1——选择携带参数信息，
    必须留在完整似然里，不能当可忽略因子约掉。 -/
theorem parameter_reading_selection_enters_likelihood :
    paramMarginal (sharedJoint (fun _ => (1 / 2 : ℚ)) (fun _ => (1 / 2 : ℚ)))
      (fun ω : Bool × Bool => true && ω.1)
      (by norm_num [evMass, sharedJoint, Fintype.sum_prod_type, Finset.mul_sum])
      true
    ≠ paramMarginal (sharedJoint (fun _ => (1 / 2 : ℚ)) (fun _ => (1 / 2 : ℚ)))
      (fun _ => true)
      (by norm_num [evMass, sharedJoint, Fintype.sum_prod_type, Finset.mul_sum])
      true := by
  intro h
  norm_num [paramMarginal, posterior, evMass, sharedJoint, Fintype.sum_prod_type,
    Finset.mul_sum] at h

end Needle23

/-! ## 三、针 24：后验预测＝同一 Y 的显式和 -/

section Needle24

variable {Θ : Type} [Fintype Θ] [DecidableEq Θ]
variable {Mt : Type} [Fintype Mt] [DecidableEq Mt]
variable {Yty : Type} [Fintype Yty] [DecidableEq Yty]

/-- 后验预测法律模型：事件 θ（先验）→ 材料 m（材料通道）→ 裁判观察 y（观察通道），
    三者有限支撑、逐行非负归一。材料与观察在给定 θ 下条件独立——由联合的
    因子化定义承载（主文 §7.3"须给同一法律观察 Y 的条件机制"）。 -/
structure PredictiveLegalModel (Θ Mt Yty : Type) [Fintype Θ] [Fintype Mt]
    [Fintype Yty] where
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

/-- 联合按材料证据条件化的证据质量恰等于材料质量——`hZ` 与 `hZj` 两个正性
    前提互通（`legalJoint_material_mass` 是它们的桥）。 -/
theorem legalJoint_material_mass (mdl : PredictiveLegalModel) (m : Mt) :
    evMass (legalJoint mdl) (materialEvent m) = matMass mdl m := by
  unfold evMass legalJoint materialEvent matMass
  simp only [Fintype.sum_prod_type, decide_eq_true_eq]
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
    simp only [posteriorPredictive, matPosterior]
    refine Finset.sum_congr rfl (fun θ _ => ?_)
    rw [show (∑ mt, posterior (legalJoint mdl) (materialEvent m) hZj (θ, mt, y))
        = legalJoint mdl (θ, m, y)
            / evMass (legalJoint mdl) (materialEvent m) from by
          simp only [posterior, materialEvent, decide_eq_true_eq]
          exact Fintype.sum_ite_eq m (fun mt =>
            legalJoint mdl (θ, mt, y) / evMass (legalJoint mdl) (materialEvent m)),
        legalJoint_material_mass mdl m]
    simp only [legalJoint]
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
  rw [Finset.sum_div]
  rw [show (∑ θ, mdl.prior θ * mdl.material θ m) = matMass mdl m from rfl]
  exact div_self (ne_of_gt hZ)

end Needle24

/-! ### 针 24 见证：数值算例与通道追踪（不另造目标） -/

section Needle24Witness

/-- 见证先验：Bool 上的均匀分布。 -/
def wprior : Bool → ℚ := fun _ => 1 / 2

/-- 见证材料通道：真事件偏向真材料、假事件偏向假材料。 -/
def wmat : Bool → Bool → ℚ :=
  fun θ m => if θ then (if m then 3 / 4 else 1 / 4) else (if m then 1 / 4 else 3 / 4)

/-- 见证观察通道（声明的那一个 Y）。 -/
def wobs : Bool → Bool → ℚ :=
  fun θ y => if θ then (if y then 2 / 3 else 1 / 3) else (if y then 1 / 3 else 2 / 3)

/-- 对照观察通道：不读 θ 的常数通道。 -/
def wobsAlt : Bool → Bool → ℚ := fun _ _ => 1 / 3

/-- 见证模型。 -/
def witnessModel : PredictiveLegalModel Bool Bool Bool where
  prior := wprior
  material := wmat
  obs := wobs
  prior_nonneg := by intro θ; simp [wprior]; norm_num
  material_nonneg := by intro θ m; cases θ <;> cases m <;> simp [wmat] <;> norm_num
  obs_nonneg := by intro θ y; cases θ <;> cases y <;> simp [wobs] <;> norm_num
  prior_one := by simp [wprior]; norm_num
  material_one := by intro θ; cases θ <;> simp [wmat] <;> norm_num
  obs_one := by intro θ; cases θ <;> simp [wobs] <;> norm_num

/-- 对照模型：只换观察通道，先验与材料通道不变。 -/
def witnessModelAlt : PredictiveLegalModel where
  prior := wprior
  material := wmat
  obs := wobsAlt
  prior_nonneg := by intro θ; simp [wprior]; norm_num
  material_nonneg := by intro θ m; cases θ <;> cases m <;> simp [wmat] <;> norm_num
  obs_nonneg := by intro θ y; simp [wobsAlt]; norm_num
  prior_one := by simp [wprior]; norm_num
  material_one := by intro θ; cases θ <;> simp [wmat] <;> norm_num
  obs_one := by intro θ; simp [wobsAlt]; norm_num

/-- 数值见证：材料后验 3/4、1/4，后验预测（同一 Y）读到 7/12
    （2/3·3/4 + 1/3·1/4），闭式有理、无浮点。 -/
theorem posterior_predictive_bool_witness :
    posteriorPredictive witnessModel true
      (by simp [matMass, witnessModel, wprior, wmat]; norm_num) true = 7 / 12 := by
  simp [posteriorPredictive, matPosterior, matMass, witnessModel, wprior, wmat, wobs]
  norm_num

/-- 通道追踪见证（不另造目标）：只把观察通道换成不读 θ 的常数通道，后验预测
    就从 7/12 变成 1/3——预测读取的是**声明的那个**观察通道，换通道即换预测，
    不存在与通道无关的"天然目标"。 -/
theorem predictive_tracks_declared_channel :
    posteriorPredictive witnessModel true
      (by simp [matMass, witnessModel, wprior, wmat]; norm_num) true
    ≠ posteriorPredictive witnessModelAlt true
      (by simp [matMass, witnessModelAlt, wprior, wmat]; norm_num) true := by
  intro h
  simp [posteriorPredictive, matPosterior, matMass, witnessModel, witnessModelAlt,
    wprior, wmat, wobs, wobsAlt] at h
  norm_num at h

end Needle24Witness

/-! ## 四、针 25：数量 AST 的有理嵌入／除法 guard／单位 -/

section Needle25

/-- 数量 AST：整数叶、加、乘、带 guard 的除、挂单位。 -/
inductive QtyAst where
  /-- 整数叶（最小货币单位／计数），有理嵌入无舍入。 -/
  | intLit (k : ℤ)
  /-- 同单位加法（单位失配 fail-closed）。 -/
  | add (a b : QtyAst)
  /-- 乘法：一侧必须无量纲（量纲纪律）。 -/
  | mul (a b : QtyAst)
  /-- 除法：除数必须无量纲且非零（guard，fail-closed）。 -/
  | divGuard (a b : QtyAst)
  /-- 挂单位：保值改标（显式重标签，不冒称单位守恒）。 -/
  | withUnit (u : String) (a : QtyAst)

/-- 数量值：ℚ 值＋单位串。 -/
structure QtyVal where
  /-- 精确有理值（全程无浮点）。 -/
  val : ℚ
  /-- 单位标签。 -/
  unit : String

/-- 指称：Option 语义，任何 guard 失败（除零、单位失配、双量纲乘法、子项失败）
    一律 `none`。 -/
def qtyDenote : QtyAst → Option QtyVal
  | .intLit k => some ⟨(k : ℚ), ""⟩
  | .add a b =>
      match qtyDenote a, qtyDenote b with
      | some x, some y => if x.unit = y.unit then some ⟨x.val + y.val, x.unit⟩ else none
      | _, _ => none
  | .mul a b =>
      match qtyDenote a, qtyDenote b with
      | some x, some y =>
          if x.unit = "" then some ⟨x.val * y.val, y.unit⟩
          else if y.unit = "" then some ⟨x.val * y.val, x.unit⟩
          else none
      | _, _ => none
  | .divGuard a b =>
      match qtyDenote a, qtyDenote b with
      | some x, some y =>
          if y.unit = "" ∧ y.val ≠ 0 then some ⟨x.val / y.val, x.unit⟩ else none
      | _, _ => none
  | .withUnit u a =>
      match qtyDenote a with
      | some z => some ⟨z.val, u⟩
      | none => none

/-- 无除片段标记：`divGuard` 节点出现即 false。 -/
def divFree : QtyAst → Bool
  | .intLit _ => true
  | .add a b => divFree a && divFree b
  | .mul a b => divFree a && divFree b
  | .divGuard _ _ => false
  | .withUnit _ a => divFree a

/-- 整叶的有理嵌入：定义即 ℤ→ℚ 精确像、无量纲、无舍入。 -/
theorem qtyDenote_intLit (k : ℤ) : qtyDenote (.intLit k) = some ⟨(k : ℚ), ""⟩ := rfl

/-- 挂单位保值改标：子项指称成功时，改挂只换标签不改值。 -/
theorem qtyDenote_withUnit (u : String) (a : QtyAst) (z : QtyVal)
    (h : qtyDenote a = some z) : qtyDenote (.withUnit u a) = some ⟨z.val, u⟩ := by
  simp only [qtyDenote]
  rw [h]

/-- 除法 guard（fail-closed）：除数指称为零值时，除节点指称 `none`。 -/
theorem qtyDivGuard_fail_closed (a b : QtyAst) (z : QtyVal)
    (h : qtyDenote b = some z) (hz : z.val = 0) : qtyDenote (.divGuard a b) = none := by
  simp only [qtyDenote]
  rw [h]
  rcases ha : qtyDenote a with _ | x <;> simp [hz]

/-- 单位失配 fail-closed：同单位加法在单位不同时拒绝给值。 -/
theorem qtyDenote_add_unit_mismatch (a b : QtyAst) (x y : QtyVal)
    (hA : qtyDenote a = some x) (hB : qtyDenote b = some y) (hne : x.unit ≠ y.unit) :
    qtyDenote (.add a b) = none := by
  simp only [qtyDenote]
  rw [hA, hB]
  simp [hne]

/-- 结构归纳主定理：无除片段只要指称成功，其值必是某整数的 ℚ 像
    （加、乘保持整值，挂单位保值——全程无舍入、无浮点）。 -/
theorem qtyDenote_divFree_int_valued :
    ∀ (a : QtyAst), divFree a = true →
      ∀ z : QtyVal, qtyDenote a = some z → ∃ k : ℤ, z.val = (k : ℚ) := by
  intro a
  induction a with
  | intLit k =>
      intro _ z h
      refine ⟨k, ?_⟩
      have h' : some ⟨(k : ℚ), ""⟩ = some z := h
      injection h' with hz
      exact (congrArg QtyVal.val hz).symm
  | add a b ihA ihB =>
      intro hfree
      simp only [divFree, Bool.and_eq_true] at hfree
      obtain ⟨hA', hB'⟩ := hfree
      simp only [qtyDenote]
      rcases ha : qtyDenote a with _ | x
      · intro z h; simp at h
      · rcases hb : qtyDenote b with _ | y
        · intro z h; simp at h
        · intro z h
          by_cases hu : x.unit = y.unit
          · rw [if_pos hu] at h
            injection h with hz
            injection hz with e1 e2
            obtain ⟨k1, hk1⟩ := ihA hA' x ha
            obtain ⟨k2, hk2⟩ := ihB hB' y hb
            exact ⟨k1 + k2, by rw [← e1, hk1, hk2]; push_cast; ring⟩
          · rw [if_neg hu] at h
            simp at h
  | mul a b ihA ihB =>
      intro hfree
      simp only [divFree, Bool.and_eq_true] at hfree
      obtain ⟨hA', hB'⟩ := hfree
      simp only [qtyDenote]
      rcases ha : qtyDenote a with _ | x
      · intro z h; simp at h
      · rcases hb : qtyDenote b with _ | y
        · intro z h; simp at h
        · intro z h
          by_cases hu : x.unit = ""
          · rw [if_pos hu] at h
            injection h with hz
            injection hz with e1 e2
            obtain ⟨k1, hk1⟩ := ihA hA' x ha
            obtain ⟨k2, hk2⟩ := ihB hB' y hb
            exact ⟨k1 * k2, by rw [← e1, hk1, hk2]; push_cast; ring⟩
          · rw [if_neg hu] at h
            by_cases hv : y.unit = ""
            · rw [if_pos hv] at h
              injection h with hz
              injection hz with e1 e2
              obtain ⟨k1, hk1⟩ := ihA hA' x ha
              obtain ⟨k2, hk2⟩ := ihB hB' y hb
              exact ⟨k1 * k2, by rw [← e1, hk1, hk2]; push_cast; ring⟩
            · rw [if_neg hv] at h
              simp at h
  | divGuard a b ihA ihB =>
      intro hfree
      simp [divFree] at hfree
  | withUnit u a ihA =>
      intro hfree
      simp only [qtyDenote]
      rcases ha : qtyDenote a with _ | x
      · intro z h; simp at h
      · intro z h
        have h' : some ⟨x.val, u⟩ = some z := h
        injection h' with hz
        injection hz with e1 e2
        obtain ⟨k, hk⟩ := ihA hfree x ha
        exact ⟨k, e1.trans hk⟩

/-- 针 25 主定理（原验收名 `exact_amount_denotation`）：五合一——
    (i) 整叶有理嵌入（定义事实）；
    (ii) 除法 guard：除数零值 ⇒ `none`（fail-closed）；
    (iii) 结构归纳：无除片段指称成功 ⇒ 值是整数的 ℚ 像（无舍入面）；
    (iv) 挂单位保值改标（单位面）；
    (v) 同单位加法在单位失配时 fail-closed（量纲纪律面）。 -/
theorem exact_amount_denotation :
    (∀ k : ℤ, qtyDenote (.intLit k) = some ⟨(k : ℚ), ""⟩)
    ∧ (∀ (a b : QtyAst) (z : QtyVal), qtyDenote b = some z → z.val = 0 →
          qtyDenote (.divGuard a b) = none)
    ∧ (∀ (a : QtyAst), divFree a = true → ∀ z : QtyVal, qtyDenote a = some z →
          ∃ k : ℤ, z.val = (k : ℚ))
    ∧ (∀ (u : String) (a : QtyAst) (z : QtyVal), qtyDenote a = some z →
          qtyDenote (.withUnit u a) = some ⟨z.val, u⟩)
    ∧ (∀ (a b : QtyAst) (x y : QtyVal), qtyDenote a = some x → qtyDenote b = some y →
          x.unit ≠ y.unit → qtyDenote (.add a b) = none) :=
  ⟨fun k => rfl,
    fun a b z h hz => qtyDivGuard_fail_closed a b z h hz,
    fun a hfree z h => qtyDenote_divFree_int_valued a hfree z h,
    fun u a z h => qtyDenote_withUnit u a z h,
    fun a b x y hA hB hne => qtyDenote_add_unit_mismatch a b x y hA hB hne⟩

/-- 与锚文件的桥：`ExactAmountM5` 的最小货币单位读数（即
    `Seams.Probability.exactAmountQ` 的定义体 `a.minorUnits`）恰是本 AST
    `withUnit currency (intLit minorUnits)` 的指称值——锚 :401 的"只读
    exactAmountQ"升级为完整 AST 上的结构化读数，两条读数在叶上定义一致。 -/
theorem exactAmount_bridge (a : ExactAmountM5) :
    qtyDenote (.withUnit a.currency (.intLit a.minorUnits))
      = some ⟨(a.minorUnits : ℚ), a.currency⟩ :=
  qtyDenote_withUnit a.currency (.intLit a.minorUnits) ⟨(a.minorUnits : ℚ), ""⟩ rfl

/-- 除法 guard 数值见证：除数为 0 ⇒ `none`。 -/
theorem qtyDivGuard_zero_witness :
    qtyDenote (.divGuard (.intLit 100) (.intLit 0)) = none := by decide

/-- 除法 guard 数值见证：除数非 0 ⇒ 精确有理商（100/4 = 25，无舍入）。 -/
theorem qtyDivGuard_nonzero_witness :
    qtyDenote (.divGuard (.intLit 100) (.intLit 4)) = some ⟨(25 : ℚ), ""⟩ := by decide

/-- 量纲纪律数值见证：无量纲 × 带单位 ⇒ 带单位（7 × 13 fen = 91 fen）。 -/
theorem qtyMulUnit_witness :
    qtyDenote (.mul (.intLit 7) (.withUnit "CNY-fen" (.intLit 13)))
      = some ⟨(91 : ℚ), "CNY-fen"⟩ := by decide

end Needle25

/-! ## 五、针 26：七字段舍入规则＋带符号商余数＋半值分支 -/

section Needle26

/-- 欧几里得商余数（结构递归，不依赖语言默认除法）：m 逐步分 d，
    余数满 d 则进位。规范由 `natQR_spec` 归纳证明。 -/
def natQR : ℕ → ℕ → ℕ × ℕ
  | 0, _ => (0, 0)
  | m + 1, d =>
      if (natQR m d).2 + 1 < d then ((natQR m d).1, (natQR m d).2 + 1)
      else ((natQR m d).1 + 1, 0)

/-- natQR 的归纳规范：d > 0 时 m = d·q + r 且 r < d（主文 §6.5 的
    "n = dq + r, 0 ≤ r < d"在非负基数上的形态）。 -/
theorem natQR_spec : ∀ (d : ℕ), 0 < d → ∀ (m : ℕ),
    ∃ q r, natQR m d = (q, r) ∧ m = d * q + r ∧ r < d := by
  intro d hd m
  induction m with
  | zero => exact ⟨0, 0, rfl, by omega, hd⟩
  | succ m ih =>
      obtain ⟨q0, r0, hqr, hEq0, hLt0⟩ := ih
      have hEq : m = d * q0 + r0 := hEq0
      have hLt : r0 < d := hLt0
      rw [natQR, hqr]
      by_cases hc : r0 + 1 < d
      · exact ⟨q0, r0 + 1, by simp [hc], by omega, hc⟩
      · exact ⟨q0 + 1, 0, by simp [hc], by omega, by omega⟩

/-- 舍入方向：floor（向 -∞）／ceil（向 +∞）／nearest（最近值，半值按策略）。 -/
inductive RoundDir where
  | floorDir
  | ceilDir
  | nearestDir

/-- 半值策略（具名）：halfUp＝数轴向 +∞ 取上候选；halfDown＝向 -∞ 取下候选。
    这是本件的显式定义，不是任何法条的转写。 -/
inductive HalfPolicy where
  | halfUp
  | halfDown

/-- 低候选倍数 q·d。 -/
def candLow (q d : ℕ) : ℤ := (q : ℤ) * (d : ℤ)

/-- 高候选倍数 (q+1)·d。 -/
def candHigh (q d : ℕ) : ℤ := ((q : ℤ) + 1) * (d : ℤ)

/-- 非负基数上的方向选择：floor 取低候选；ceil 在整除时取低候选否则高候选；
    nearest 比较 2r 与 d，半值（2r = d）按具名策略。 -/
def pickPos (d : ℕ) (dir : RoundDir) (hp : HalfPolicy) (q r : ℕ) : ℤ :=
  match dir with
  | .floorDir => candLow q d
  | .ceilDir => if r = 0 then candLow q d else candHigh q d
  | .nearestDir =>
      if 2 * r < d then candLow q d
      else if d < 2 * r then candHigh q d
      else match hp with
        | .halfUp => candHigh q d
        | .halfDown => candLow q d

/-- 负基数上的方向选择（数轴语义镜像）：floor(-m) = -ceil(m)、ceil(-m) = -floor(m)；
    nearest 对称（距离同为 r 与 d-r），半值的上/下候选按数轴方向对换。 -/
def pickNeg (d : ℕ) (dir : RoundDir) (hp : HalfPolicy) (q r : ℕ) : ℤ :=
  match dir with
  | .floorDir => if r = 0 then -(candLow q d) else -(candHigh q d)
  | .ceilDir => -(candLow q d)
  | .nearestDir =>
      if 2 * r < d then -(candLow q d)
      else if d < 2 * r then -(candHigh q d)
      else match hp with
        | .halfUp => -(candLow q d)
        | .halfDown => -(candHigh q d)

/-- 带符号舍入核心：按符号分支，在 |n| 的商余数上选择候选倍数。
    负数按定义处理（正负两支显式给出），不依赖语言默认除法。 -/
def roundCore (d : ℕ) (dir : RoundDir) (hp : HalfPolicy) (n : ℤ) : ℤ :=
  if 0 ≤ n then pickPos d dir hp (natQR n.natAbs d).1 (natQR n.natAbs d).2
  else pickNeg d dir hp (natQR n.natAbs d).1 (natQR n.natAbs d).2

/-- 七字段舍入规则记录（主文 §6.5：依据、单位、刻度、方向、半值处理、
    发生节点、输入基数）。 -/
structure RoundingRule where
  /-- 依据：法源/规范依据标签（空 ⇒ fail-closed）。 -/
  basis : String
  /-- 单位（进入输出回执）。 -/
  unit : String
  /-- 刻度 d（正数；0 ⇒ fail-closed）。 -/
  scale : ℕ
  /-- 方向。 -/
  dir : RoundDir
  /-- 半值处理。 -/
  half : HalfPolicy
  /-- 发生节点（当前节点不匹配 ⇒ fail-closed；实际发生的节点进回执）。 -/
  node : String
  /-- 输入基数（被舍入的法定基数，进输出回执——不把 policy 当无效装饰）。 -/
  inputBase : ℤ

/-- 舍入回执：取整值＋单位＋基数＋节点四字段。 -/
structure RoundedOutcome where
  /-- 取整后的值（最小货币单位）。 -/
  value : ℤ
  /-- 单位回执。 -/
  unit : String
  /-- 输入基数回执。 -/
  base : ℤ
  /-- 发生节点回执。 -/
  node : String

/-- 规则施加：七字段全部被读取——依据为守卫、节点为守卫、刻度为算术输入、
    方向与半值为算术分支、单位与输入基数为回执。任一守卫失败 ⇒ `none`。 -/
def applyRule (rule : RoundingRule) (cur : String) (n : ℤ) : Option RoundedOutcome :=
  if rule.basis = "" then none
  else if cur ≠ rule.node then none
  else if rule.scale = 0 then none
  else some { value := roundCore rule.scale rule.dir rule.half n, unit := rule.unit,
              base := rule.inputBase, node := rule.node }

/-- 守卫一：依据为空 ⇒ fail-closed。 -/
theorem applyRule_fail_closed_on_empty_basis (rule : RoundingRule) (cur : String) (n : ℤ)
    (h : rule.basis = "") : applyRule rule cur n = none := by
  rw [applyRule, if_pos h]

/-- 守卫二：节点不符 ⇒ fail-closed（发生节点是承重字段，不是装饰）。 -/
theorem applyRule_fail_closed_on_foreign_node (rule : RoundingRule) (cur : String) (n : ℤ)
    (h : cur ≠ rule.node) : applyRule rule cur n = none := by
  by_cases hb : rule.basis = ""
  · rw [applyRule, if_pos hb]
  · rw [applyRule, if_neg hb, if_pos h]

/-- 守卫三：刻度为零 ⇒ fail-closed。 -/
theorem applyRule_fail_closed_on_zero_scale (rule : RoundingRule) (cur : String) (n : ℤ)
    (h : rule.scale = 0) : applyRule rule cur n = none := by
  by_cases hb : rule.basis = ""
  · rw [applyRule, if_pos hb]
  · by_cases hn : cur ≠ rule.node
    · rw [applyRule, if_neg hb, if_pos hn]
    · rw [applyRule, if_neg hb, if_neg hn, if_pos h]

/-- floor 的单侧刻度界：取整值 ≤ n < 取整值 + d。 -/
theorem roundCore_floor_spec (d : ℕ) (hd : 0 < d) (hp : HalfPolicy) (n : ℤ) :
    roundCore d .floorDir hp n ≤ n ∧ n < roundCore d .floorDir hp n + (d : ℤ) := by
  obtain ⟨q, r, hqr, hEq0, hLt0⟩ := natQR_spec d hd n.natAbs
  have hLt : r < d := hLt0
  have hEq' : n.natAbs = q * d + r := by rw [Nat.mul_comm q d]; exact hEq0
  have hEq2 : (n.natAbs : ℤ) = (q : ℤ) * (d : ℤ) + (r : ℤ) := by exact_mod_cast hEq'
  have hHigh : ((q : ℤ) + 1) * (d : ℤ) = (q : ℤ) * (d : ℤ) + (d : ℤ) := by ring
  rw [roundCore]
  by_cases hn : 0 ≤ n
  · have hc : (n.natAbs : ℤ) = n := by omega
    rw [if_pos hn]
    simp only [hqr, pickPos, candLow]
    constructor <;> omega
  · have hc : (n.natAbs : ℤ) = -n := by omega
    rw [if_neg hn]
    simp only [hqr, pickNeg]
    by_cases hr : r = 0
    · rw [if_pos hr, candLow]
      constructor <;> omega
    · rw [if_neg hr, candHigh]
      constructor <;> omega

/-- ceil 的单侧刻度界：n ≤ 取整值 < n + d。 -/
theorem roundCore_ceil_spec (d : ℕ) (hd : 0 < d) (hp : HalfPolicy) (n : ℤ) :
    n ≤ roundCore d .ceilDir hp n ∧ roundCore d .ceilDir hp n - (d : ℤ) < n := by
  obtain ⟨q, r, hqr, hEq0, hLt0⟩ := natQR_spec d hd n.natAbs
  have hLt : r < d := hLt0
  have hEq' : n.natAbs = q * d + r := by rw [Nat.mul_comm q d]; exact hEq0
  have hEq2 : (n.natAbs : ℤ) = (q : ℤ) * (d : ℤ) + (r : ℤ) := by exact_mod_cast hEq'
  have hHigh : ((q : ℤ) + 1) * (d : ℤ) = (q : ℤ) * (d : ℤ) + (d : ℤ) := by ring
  rw [roundCore]
  by_cases hn : 0 ≤ n
  · have hc : (n.natAbs : ℤ) = n := by omega
    rw [if_pos hn]
    simp only [hqr, pickPos]
    by_cases hr : r = 0
    · rw [if_pos hr, candLow]
      constructor <;> omega
    · rw [if_neg hr, candHigh]
      constructor <;> omega
  · have hc : (n.natAbs : ℤ) = -n := by omega
    rw [if_neg hn]
    simp only [hqr, pickNeg, candLow]
    constructor <;> omega

/-- nearest 的双侧误差界（主文 §6.5"误差界在该节点证明"）：半值分支取到
    d/2，非半值分支严格小于 d/2，故 2·(取整值 - n) 落在 [-d, d]。 -/
theorem roundCore_near_error (d : ℕ) (hd : 0 < d) (hp : HalfPolicy) (n : ℤ) :
    2 * (roundCore d .nearestDir hp n - n) ≤ (d : ℤ)
      ∧ -((d : ℤ)) ≤ 2 * (roundCore d .nearestDir hp n - n) := by
  obtain ⟨q, r, hqr, hEq0, hLt0⟩ := natQR_spec d hd n.natAbs
  have hLt : r < d := hLt0
  have hEq' : n.natAbs = q * d + r := by rw [Nat.mul_comm q d]; exact hEq0
  have hEq2 : (n.natAbs : ℤ) = (q : ℤ) * (d : ℤ) + (r : ℤ) := by exact_mod_cast hEq'
  have hHigh : ((q : ℤ) + 1) * (d : ℤ) = (q : ℤ) * (d : ℤ) + (d : ℤ) := by ring
  rw [roundCore]
  by_cases hn : 0 ≤ n
  · have hc : (n.natAbs : ℤ) = n := by omega
    rw [if_pos hn]
    simp only [hqr]
    rw [pickPos]
    by_cases h2r : 2 * r < d
    · rw [if_pos h2r, candLow] <;> omega
    · rw [if_neg h2r]
      by_cases hd2 : d < 2 * r
      · rw [if_pos hd2, candHigh] <;> omega
      · rw [if_neg hd2]
        cases hp <;> simp only [candLow, candHigh] <;> omega
  · have hc : (n.natAbs : ℤ) = -n := by omega
    rw [if_neg hn]
    simp only [hqr]
    rw [pickNeg]
    by_cases h2r : 2 * r < d
    · rw [if_pos h2r, candLow] <;> omega
    · rw [if_neg h2r]
      by_cases hd2 : d < 2 * r
      · rw [if_pos hd2, candHigh] <;> omega
      · rw [if_neg hd2]
        cases hp <;> simp only [candLow, candHigh] <;> omega

/-- 针 26 主定理（原验收名 `rounding_matches_rule`）：守卫全开时，规则施加
    返回回执——值＝按七字段算术核计算的取整值，单位/基数/节点逐字段回读；
    且方向为 nearest 时误差界在节点处成立。policy 不是无效装饰：每个字段
    都被 `applyRule` 消费（三个 fail-closed 守卫＋四字段回执）。 -/
theorem rounding_matches_rule (rule : RoundingRule) (cur : String) (n : ℤ)
    (hb : rule.basis ≠ "") (hs : 0 < rule.scale) (hcur : cur = rule.node) :
    applyRule rule cur n = some { value := roundCore rule.scale rule.dir rule.half n,
        unit := rule.unit, base := rule.inputBase, node := rule.node }
      ∧ (rule.dir = .nearestDir → 2 * (roundCore rule.scale rule.dir rule.half n - n)
            ≤ (rule.scale : ℤ)
          ∧ -((rule.scale : ℤ)) ≤ 2 * (roundCore rule.scale rule.dir rule.half n - n)) := by
  refine ⟨?_, ?_⟩
  · rw [applyRule, if_neg hb, if_neg (fun h => hcur h), if_neg (by omega)]
  · intro hdir
    rw [hdir]
    exact roundCore_near_error rule.scale hs rule.half n

/-- 示例规则：刻度 10、nearest、halfUp、节点 "judgment-render"、基数 25。 -/
def demoRule : RoundingRule where
  basis := "demo-basis"
  unit := "CNY-fen"
  scale := 10
  dir := .nearestDir
  half := .halfUp
  node := "judgment-render"
  inputBase := 25

/-- 回执见证：命中节点时 25 按 halfUp 舍到 30，回执四字段逐字回读七字段。 -/
theorem applyRule_demo_node_hit :
    applyRule demoRule "judgment-render" 25
      = some { value := 30, unit := "CNY-fen", base := 25, node := "judgment-render" } := by
  decide

/-- 发生节点承重见证：同一规则、同一输入，节点不符 ⇒ `none`
    （节点守卫区分输出，不是装饰）。 -/
theorem node_guard_is_load_bearing :
    applyRule demoRule "elsewhere" 25 = none := by decide

/-- 带符号半值分支数值见证：25 于刻度 10 半值（2r = d）——
    halfUp 向 +∞ 取 30；-25 的 halfUp 取 -20、halfDown 取 -30（数轴语义，
    非语言默认除法截断）；floor(-25) = -30（欧几里得 floor ≠ 截断 -20）；
    ceil(-25) = -20；24 与 26 落在非半值分支各取 20/30。 -/
theorem rounding_near_signed_witnesses :
    roundCore 10 .nearestDir .halfUp 25 = 30
      ∧ roundCore 10 .nearestDir .halfUp (-(25 : ℤ)) = -(20 : ℤ)
      ∧ roundCore 10 .nearestDir .halfDown (-(25 : ℤ)) = -(30 : ℤ)
      ∧ roundCore 10 .floorDir .halfUp (-(25 : ℤ)) = -(30 : ℤ)
      ∧ roundCore 10 .ceilDir .halfUp (-(25 : ℤ)) = -(20 : ℤ)
      ∧ roundCore 10 .nearestDir .halfUp 24 = 20
      ∧ roundCore 10 .nearestDir .halfUp 26 = 30 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end Needle26

end JurisLean.Seams.UnifiedNeedlesS3b
