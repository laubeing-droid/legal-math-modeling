import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic
import JurisLean.FullMath.Probability.Conditioning
import JurisLean.FullMath.Probability.DirichletPosterior
import JurisLean.FullMath.Probability.BetaInterval
import JurisLean.ExactNumericContract

/-!
S3 —— L4 概率层缝合件：P-114 概率桥、β 后验的五段推导、P-098 违约金酌减关系。

## 一、法律语义（人话）

本件把 L4 概率层缝到三处接缝上，并把项目里互不相干的四个概率读数还原为
**同一个生成模型的几段推导**。

**(1) P-114 概率桥。** 仓内的概率对象一律是有理分布 `p : S → ℚ`（逐点非负、`∑ p = 1`、
`[Fintype S]`），而随仓的外部博弈论载体（`External/GameTheory/Math/ProbabilityMassFunction.lean`）
用的是 Mathlib 自己的 `PMF α`（`= { f : α → ℝ≥0∞ // HasSum f 1 }`）。两边从未被正式连起来：
13 个 `FullMath/Probability/*` 模块一个都没有 import Mathlib 的概率模块。本件交出这座桥
`finite_distribution_to_pmf`，并证它原子质量守恒（`finite_distribution_to_pmf_apply`）、
可逆不丢信息（`finite_distribution_to_pmf_injective`）、支撑与逐原子界可回读
（`finite_distribution_to_pmf_mem_support`、`finite_distribution_to_pmf_atom_le_one`），
以及条件化所用的证据质量在桥下保持（`rationalMass_evMass`）。
法律读法：一旦声称"我们的有理分布就是文献里的质量函数"，必须能指出原子对应、总质量对应、
且搬运可逆；少一条就只能说"两者看起来一样"。

**(2) β 后验的五段推导。** 同一套"胜/负计数 + 形状参数"在本项目里被读成四种量：
条件化后验（`Conditioning.posterior`）、模型平均权重（`ModelAveraging.hyperWeights`）、
Dirichlet/Beta 共轭更新（`DirichletPosterior.dirWeights`）、精确 Beta CDF 的区间质量
（`BetaInterval.betaMass`）。本件声明**一个** ℚ 上的生成模型 `BetaGenModel`
（先验形状 `shape`、似然折叠出的计数 `counts`、后验形状 `foldedShape = shape + counts`），
在其中四读数的**三个**（`Conditioning`、`DirichletPosterior`、`BetaInterval`）之间交出
五段推导：
段一 先验读出归一 `prior_readout_normalizes`；
段二 后验形状等于"先验 + 似然计数" `beta_posterior_from_likelihood`；
段三 后验读出归一 `posterior_readout_normalizes`（前提 `shape_add_counts_pos`）；
段四 同一机制在两种选择/观察制度下的读数互相搬运 `selection_transport_from_shared_mechanism`
（配 `evMass_posterior_refined`、`transport_regime_positivity` 与边界 `transport_boundary_needs_nesting`）；
段五 读出段的精确金额不经任何舍入 `exact_amount_denotation`（配概率面
`beta_predictive_bracket_survives_update`）。
第四个读数 `ModelAveraging.hyperWeights` **没有**被接进这个模型（本件不 import 它），
列为未覆盖片段第 3 项；五段全是 ℚ 上的读数/权重恒等式，一段都不是测度论积分。
法律读法：胜诉率、违约金酌减幅度、模型权重这些"三个数"常常出自同一生成过程的不同制度；
只有把机制写成函数、把制度写成谓词，才能说清它们凭什么可以互相换算。

**(3) P-098 违约金酌减是关系，不是钳制。** 《民法典》第585条第2款：
"约定的违约金低于造成的损失的，人民法院或者仲裁机构可以根据当事人的请求予以增加；
约定的违约金过分高于造成的损失的，人民法院或者仲裁机构可以根据当事人的请求予以适当减少。"
《最高人民法院关于适用〈中华人民共和国民法典〉合同编通则若干问题的解释》（法释〔2023〕13号）
第65条："……人民法院应当以民法典第五百八十四条规定的损失为基础，兼顾合同主体、交易类型、
合同的履行情况、当事人的过错程度、履约背景等因素，遵循公平原则和诚信原则进行衡量，并作出裁判。
约定的违约金超过造成的损失的百分之三十的，人民法院一般可以认定为过分高于造成的损失。
恶意违约的当事人一方请求减少违约金的，人民法院一般不予支持。"同解释第64条第2款（**已按最高法
官网权威发布页逐字核验**，https://www.court.gov.cn/fabu/xiangqing/419382.html，2026-10-01）：
"违约方主张约定的违约金过分高于违约造成的损失，请求予以适当减少的，应当承担举证责任。
非违约方主张约定的违约金合理的，也应当提供相应的证据。"——《民法典》第585条引自政府域名
转载全文（湖南省审计厅 sjt.hunan.gov.cn，人大官网一手页 403，标点全半角从转载）。
本件把这四条做成**有限条件集** `ReductionCondition`，再由条件集合成闸门
`reductionGate` 与准许关系 `Allow`；30% 门槛取精确有理比较 `(13/10 : ℚ) * 损失 < 约定额`
（整数等价式 `13 * 损失 < 10 * 约定额`，二者的等价性本件证明）。
关键立场：65条第2款说的是"一般**可以**认定"（许可式），所以门槛只是 `Allow` 的**准入条件**，
不是把结果算出来的规则；同一款的"恶意违约……一般**不予**支持"在本件里按默认情形建成
硬关闸（`bad_faith_bar`），其"一般"留出的例外面未建模（§四第 7 项）；
65条第1款列举的衡量因素面本件刻意留作自由输入 `factors : F`，
不写成定理。据此给出反例对 `clamp_is_not_reduction`：一个满足区间归入（仓库现有 clamp 的形状）
的金额，在恶意违约数据上仍然违反 `Allow` —— 归入区间不是法律性质。

## 二、数学对象
- `rationalMass p a := ENNReal.ofReal (p a)`；`finite_distribution_to_pmf := PMF.ofFintype`。
- `BetaGenModel`：`shape counts : Fin 2 → ℚ` 加非负性与先验总质量正的字段。
  `priorReadout = dirWeights shape 0`、`posteriorReadout = dirWeights shape counts`、
  `foldedShape i = shape i + counts i`。
- 制度谓词：`e o : S → Bool`（`Conditioning.evMass` / `Conditioning.posterior` 的既有语言）。
- `Amount := ℤ`（最小货币单位，与 `ExactNumericContract` 的 `ExactAmountM5.minorUnits` 同域）；
  `amountQ`、`exactAmountQ` 是进入 ℚ 比例比较的唯一通道。
- `ReductionCondition`：六个法定条件名（请求、过分高于、30% 门槛、恶意违约、举证、衡量因素）；
  `ReductionData F` 是条件位 + 两个金额 + 因素面 `F`。
- `TwoSidedBurden.BurdenRecord F`：`ReductionData F` 再加一个**守约方举证位**（第64条第2款的
  另一侧）。配套的 `twoSidedGate`/`AllowTwo` 是**对照物**，用来把"本件主契约只登记了单向举证"
  这件事量化成定理；本件主张的法律关系仍是下面的 `Allow`。
- `Allow c x := (闸门开 → 下界 ≤ x ≤ 约定额) ∧ (闸门开 ∨ x = 约定额)`；`choose c` 分闸门取
  下界或维持约定额。

## 三、证与不证
**证**：桥的构造 `finite_distribution_to_pmf` 与总质量搬运 `rationalMass_sum_eq_one`，
外加四条守恒/回读性质（原子质量 `…_apply`、`HasSum`/`tsum` 形态 `…_hasSum`、`…_tsum`、
支撑 `…_mem_support`、单射 `…_injective`、逐原子界 `…_atom_le_one`）与证据质量在桥下保持
`rationalMass_evMass`；五段推导逐一见 §一(2) 的段号——其中段二以
`DirichletPosterior.dirWeights_update_compose` 为唯一实质引理（未重证），段三引用
`dirWeights_normalizes` 并先证更新后总质量仍正 `shape_add_counts_pos`，段四的
`evMass_posterior_refined` 给搬运方程、`transport_regime_positivity` 给其正性前提，
段四主定理给"两重条件化等于一重条件化"，边界 `transport_boundary_needs_nesting` 给
非嵌套时的逐点失效面；段五的五条给出带显式舍入政策时精确金额读数就是其有理像、
与政策取值无关、政策缺失即 fail-closed、且读数币种盲，概率面
`beta_predictive_bracket_survives_update` 引用 `BetaInterval.beta_mass_total_one`；
P-098 侧证 30% 门槛的四种等价形态（`thirty_percent_rational_exact`、
`overThirtyThreshold_iff_intTest`、`overThirtyThreshold_iff_excess`、
`overThirtyTest_true_iff`）、下界不退化 `reductionFloor_le_agreed`、
`∀ c, Allow c (choose c)`（`reduction_admits_declared_conditions`）、钳制的归入性
`clampReduction_in_band` 与其不等价于 `Allow` 的反例 `clamp_is_not_reduction`、
归入性不蕴含准许的一般形式 `band_containment_is_not_allow`、三份见证数据的闭式事实
（`maliciousData_gate/_choose/_clamp/_floor`、`lossBasedData_facts`、`lossBasedData_overThirty`、
`otherGroundData_not_overThirty`）、门槛既不强制也不排斥认定（双向见证）、
以及准许额在约定额非负时非负 `allowed_amount_nonneg_of_nonneg_agreed`。

**不证**（全部是刻意的降级，不是疏漏）：
- 不证 P-114 的**测度侧**：桥只到 `PMF` 对象与原子质量为止。`PMF.cond` / `PMF.toMeasure`
  需要 `MeasurableSpace`、`a.e.` 与 `ENNReal` 上的条件化，本件未接；因此不得声称
  "条件化在 Mathlib 概率层已被证明"，也不得声称 P-114 已闭环。
- 不证 `VE(query,e) = Enumerate(query,e)`：`VariableElimination.elim_swap_adjacent` 的免责声明
  （`:7-8`）说明那只是等式背后的代数，本件没有推进这一步。
- 不把 `E01Contract.cantelli_core`（`:97`，`m`、`sigma` 为未解释 ℚ 常数、带 `hkey` 假设的
  抽象二次核）升级成概率尾界；不碰其 `:11-12`、`:47` 免责声明。
- `BetaInterval.beta_mixture_mass`（`:71`）只有两支混合的结论，任意 n 支未证；本件不复证也不推广。
- 不接第四个读数：`ModelAveraging.hyperWeights` 与 `BetaGenModel` 的共轭读数之间没有定理，
  本件甚至不 import 该模块；"四读数同出一模型"只在**三个**读数上成立。
- 不作任何校准/得分主张：本件不 import `Brier.lean`，其 `:8-10` 声明"样本得分不证明校准"，
  本件也没有把任何读数解释成校准度。
- 不证 n 段以上生成模型的可组合性；`selection_transport_from_shared_mechanism` 只在
  **制度嵌套**（`o ⊑ e`）时成立，非嵌套情形由 `transport_boundary_needs_nesting` 给出
  逐点失效面（被排除的状态在两侧和项上不相等）。
- 不把 65条第1款的衡量因素写成定理，不认定任何真实案件的事实与数额，不作任何裁判结论。
- 不声称 `choose` 是最优、唯一或与任何运行时实现相 refinement。
- 恶意违约条文的"一般**不予**支持"同为许可式：本件把 `badFaith` 建成硬关闸（只实现默认情形），
  法院在恶意违约下仍酌减的例外面未建模。

## 四、未覆盖片段
1. `FullMath` 有理分布 → `PMF` 之后的**条件化桥**（`pmfCond` / `Measure.cond`）：未接。
   本件成立的是质量层与 `PMF` 对象层（§三 第一条），不是 P-114 的闭环。
2. 有理分布 → `Measure`/`ProbabilityTheory`：未接（且 `Mandate/ZeroSumSion.lean:14` 记录
   本 pin 无 `Probability.Simplex`）。
3. 第四个读数 `ModelAveraging.hyperWeights` 与 `BetaGenModel` 的共轭读数之间：无任何定理，
   本件不 import 该模块。模型平均权重的归一化只在 `DirichletPosterior` 内自证，未与
   胜/负计数模型相连。
4. 任意 n 支模型平均与 n 段生成模型的推导闭合：未证（`Beta_mixture` 面只有两支）。
5. 非嵌套制度下的搬运：不成立面只给了单点见证，一般刻画未做。
6. 酌减"适当"幅度的量定规则、衡量因素的加权函数：刻意不建。
7. 恶意违约"一般不予支持"的例外面（许可式的另一半）：未建模，闸门按默认情形硬关。
8. 真实数据的校验义务（`E01Contract` 的 `REAL_VALIDATION_REQUIRED`）：外部义务，本件不伪造。

## 五、档位
`SEAM_S3_LOCAL_PROVISIONAL`：仅在本地单模块编译通过，CI 未跑（`CI_NOT_RUN`，fail-closed）。
桥的部分成立（质量层与对象级 `PMF` 已建，测度级未建）；§一(2) 的五段读数推导全部落地，
放弃的是测度级条件化桥与第四读数（模型平均）；P-098 只到"关系 + 反例"，
未做任何量刑/酌定结论。禁止把本件读成"P-114 已闭环"或"违约金酌减已被形式化决定"。
-/

namespace JurisLean.Seams.Probability

open BigOperators Finset ENNReal
open JurisLean.FullMath.Probability

section Bridge

variable {α : Type} [Fintype α]

/-- 有理分布在 `ℝ≥0∞` 上的质量像：原子的质量就是该原子概率的有理→实数→`ℝ≥0∞` 嵌入。
    这是 P-114 桥的原子层，也是 `PMF` 载体上唯一被本件用到的构造。 -/
def rationalMass (p : α → ℚ) (a : α) : ℝ≥0∞ := ENNReal.ofReal (p a)

/-- 桥的构造前提：逐点非负且总和为 1 的有理分布，其质量像在 `ℝ≥0∞` 上的有限和仍为 1。
    法律读法：换了载体不许悄悄改总质量。 -/
theorem rationalMass_sum_eq_one (p : α → ℚ) (hp0 : ∀ a, 0 ≤ p a)
    (hp1 : ∑ a : α, p a = 1) : ∑ a, rationalMass p a = (1 : ℝ≥0∞) := by
  simp only [rationalMass]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => by exact_mod_cast hp0 a)]
  rw [← Rat.cast_sum, hp1, Rat.cast_one]
  exact ENNReal.ofReal_one

/-- P-114 桥（对象级）：把 `FullMath` 的有限有理分布变成 Mathlib 的 `PMF α`，
    用 `PMF.ofFintype`，其唯一前提是有限和为 1。
    本件只到 `PMF` 对象与原子质量为止，测度侧（`toMeasure`、`pmfCond`）未接。 -/
def finite_distribution_to_pmf (p : α → ℚ) (hp0 : ∀ a, 0 ≤ p a)
    (hp1 : ∑ a : α, p a = 1) : PMF α :=
  PMF.ofFintype (rationalMass p) (rationalMass_sum_eq_one p hp0 hp1)

/-- 原子质量守恒：桥上每个原子的质量定义ally 就是有理概率的 `ENNReal` 像。 -/
theorem finite_distribution_to_pmf_apply (p : α → ℚ) (hp0 : ∀ a, 0 ≤ p a)
    (hp1 : ∑ a : α, p a = 1) (a : α) :
    finite_distribution_to_pmf p hp0 hp1 a = ENNReal.ofReal (p a) :=
  PMF.ofFintype_apply _ a

/-- 桥落进了 `HasSum` 的世界：质量像以 1 为和。这条不是本地重证，而是从 `PMF` 对象取回。 -/
theorem finite_distribution_to_pmf_hasSum (p : α → ℚ) (hp0 : ∀ a, 0 ≤ p a)
    (hp1 : ∑ a : α, p a = 1) : HasSum (rationalMass p) 1 :=
  (finite_distribution_to_pmf p hp0 hp1).hasSum_coe_one

/-- 桥保持总质量（`tsum` 形态）。 -/
theorem finite_distribution_to_pmf_tsum (p : α → ℚ) (hp0 : ∀ a, 0 ≤ p a)
    (hp1 : ∑ a : α, p a = 1) : ∑' a, rationalMass p a = 1 :=
  (finite_distribution_to_pmf p hp0 hp1).tsum_coe

/-- 支撑回读：桥上的支撑恰是正概率原子。法律读法：模型里的"可能"必须对应法律上有非零
    可能性的情形，不得凭空多出支撑点。 -/
theorem finite_distribution_to_pmf_mem_support (p : α → ℚ) (hp0 : ∀ a, 0 ≤ p a)
    (hp1 : ∑ a : α, p a = 1) (a : α) :
    a ∈ (finite_distribution_to_pmf p hp0 hp1).support ↔ 0 < p a := by
  rw [← PMF.apply_pos_iff, finite_distribution_to_pmf_apply, ENNReal.ofReal_pos, Rat.cast_pos]

/-- 桥不丢信息（单射）：两个有理分布的 `PMF` 相等则逐点相等。
    法律读法：这座桥可以做翻译用，但不能把两个不同分布压成一个。 -/
theorem finite_distribution_to_pmf_injective (p q : α → ℚ) (hp0 : ∀ a, 0 ≤ p a)
    (hq0 : ∀ a, 0 ≤ q a) (hp1 : ∑ a : α, p a = 1) (hq1 : ∑ a : α, q a = 1) :
    finite_distribution_to_pmf p hp0 hp1 = finite_distribution_to_pmf q hq0 hq1 → p = q := by
  intro h
  have hatoms (a : α) : ENNReal.ofReal (p a) = ENNReal.ofReal (q a) := by
    have h' : finite_distribution_to_pmf p hp0 hp1 a = finite_distribution_to_pmf q hq0 hq1 a := by
      rw [h]
    rwa [finite_distribution_to_pmf_apply, finite_distribution_to_pmf_apply] at h'
  funext a
  have hiff : ENNReal.ofReal (p a) = ENNReal.ofReal (q a) ↔ (p a : ℝ) = (q a : ℝ) :=
    ENNReal.ofReal_eq_ofReal_iff (Rat.cast_nonneg.mpr (hp0 a)) (Rat.cast_nonneg.mpr (hq0 a))
  exact_mod_cast hiff.mp (hatoms a)

/-- 界可回读：PMF 侧 `coe_le_one` 搬回 ℚ 侧，得每个原子的概率不超过 1。
    法律读法：外部载体的性质可以回供给仓内有理算法，不需要重新验证。 -/
theorem finite_distribution_to_pmf_atom_le_one (p : α → ℚ) (hp0 : ∀ a, 0 ≤ p a)
    (hp1 : ∑ a : α, p a = 1) (a : α) : p a ≤ 1 := by
  have h : finite_distribution_to_pmf p hp0 hp1 a ≤ (1 : ℝ≥0∞) :=
    (finite_distribution_to_pmf p hp0 hp1).coe_le_one a
  rw [finite_distribution_to_pmf_apply p hp0 hp1 a] at h
  exact_mod_cast ENNReal.ofReal_le_one.mp h

/-- 证据质量在桥下保持：条件化用的 `evMass`（ℚ 侧）与质量像的指示和（`ℝ≥0∞` 侧）互为像。
    这是把 `Conditioning.lean` 接到 `PMF` 侧的那块板，本件只证到质量层，
    不接 `PMF.cond` / `Measure.cond`。 -/
theorem rationalMass_evMass (p : α → ℚ) (hp0 : ∀ a, 0 ≤ p a) (e : α → Bool) :
    ∑ a, (if e a = true then rationalMass p a else 0) = ENNReal.ofReal (evMass p e) := by
  unfold rationalMass evMass
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => by exact_mod_cast hp0 a)]
  rw [← Rat.cast_sum]

end Bridge

section FiveSegments

/-- 声明的 β 生成模型（全部 ℚ）：二类目（胜 / 负）上的形状先验与计数似然。
    `shape` 是先验形状参数，`counts` 是似然折叠出的计数；后验形状是逐点相加。
    本件只用这一个模型统一四段读数，不声称它是任何真实统计模型的正式化。 -/
structure BetaGenModel where
  /-- 先验形状 `(α_胜, α_输)`。 -/
  shape : Fin 2 → ℚ
  /-- 似然折叠出的计数 `(赢, 输)`。 -/
  counts : Fin 2 → ℚ
  /-- 先验形状逐点非负。 -/
  hshape : ∀ i, 0 ≤ shape i
  /-- 计数逐点非负。 -/
  hcounts : ∀ i, 0 ≤ counts i
  /-- 先验总质量为正（否则归一化不可做，`Conditioning` 会走 incompatible 分支）。 -/
  hpos : 0 < ∑ i : Fin 2, shape i

/-- 后验形状：先验形状加似然计数（段 L3→L4 的"参数更新"面）。 -/
def foldedShape (m : BetaGenModel) : Fin 2 → ℚ := fun i => m.shape i + m.counts i

/-- 先验读出：形状的归一化 `α_i / Σ α`。它与 `dirWeights α 0` 表示同一个量
    （见 `priorReadout_eq_dirWeights_zero`），这里用直接形式是为了避开"加零"的可判定表述。 -/
def priorReadout (m : BetaGenModel) : Fin 2 → ℚ :=
  fun i => m.shape i / ∑ j : Fin 2, m.shape j

/-- 先验读出与 `dirWeights shape 0` 相同：本件的共轭推导只用后者。 -/
theorem priorReadout_eq_dirWeights_zero (m : BetaGenModel) :
    priorReadout m = dirWeights m.shape (0 : Fin 2 → ℚ) := by
  funext i
  simp only [priorReadout, dirWeights, Pi.zero_apply, add_zero]

/-- 后验读出：形状 + 计数后的归一化权重。 -/
def posteriorReadout (m : BetaGenModel) : Fin 2 → ℚ := dirWeights m.shape m.counts

/-- 更新后的总质量仍为正：先验总质量为正且计数非负。
    法律读法：观测不会把一个非退化的先验凭空变成零证据质量。 -/
theorem shape_add_counts_pos (m : BetaGenModel) :
    0 < ∑ i : Fin 2, (m.shape i + m.counts i) := by
  have hle : (∑ i : Fin 2, m.shape i) ≤ ∑ i : Fin 2, (m.shape i + m.counts i) :=
    Finset.sum_le_sum fun i _ => le_add_of_nonneg_right (m.hcounts i)
  exact lt_of_lt_of_le m.hpos hle

/-- 段 L3→L4（契约要求的 `beta_posterior_from_likelihood`）：
    先把似然计数折进形状再归一化，与直接用计数更新算子归一化，是同一个量。
    实质引理只有 `DirichletPosterior.dirWeights_update_compose`（本件不重证），
    外加"计数加零不变"。
    诚实声明：这是 ℚ 上的**权重层**共轭恒等式，不是 Beta 密度的测度论推导；
    后者涉及 `Real.Gamma`，仓内只在 `DirichletPosterior.beta_ratio`（ℝ 侧）证过比值恒等式。 -/
theorem beta_posterior_from_likelihood (m : BetaGenModel) :
    dirWeights (foldedShape m) (0 : Fin 2 → ℚ) = posteriorReadout m := by
  have hnum : ∀ i : Fin 2, m.counts i + (0 : Fin 2 → ℚ) i = m.counts i := fun i => add_zero _
  have hcomp : dirWeights (fun i => m.shape i + m.counts i) (0 : Fin 2 → ℚ)
      = dirWeights m.shape (fun i => m.counts i + (0 : Fin 2 → ℚ) i) :=
    dirWeights_update_compose m.shape m.counts (0 : Fin 2 → ℚ)
  rw [show foldedShape m = (fun i : Fin 2 => m.shape i + m.counts i) from rfl, hcomp]
  refine congrArg (dirWeights m.shape) ?_
  exact funext (fun i => hnum i)

/-- 段 L2：先验读出归一（由 `dirWeights` 的定义直接算出；分母非零来自先验总质量为正）。 -/
theorem prior_readout_normalizes (m : BetaGenModel) : ∑ i, priorReadout m i = 1 := by
  unfold priorReadout
  rw [← Finset.sum_div, div_self (ne_of_gt m.hpos)]

/-- 段 L4：后验读出归一（引用 `dirWeights_normalizes`，不重证）。 -/
theorem posterior_readout_normalizes (m : BetaGenModel) : ∑ i, posteriorReadout m i = 1 :=
  dirWeights_normalizes m.shape m.counts (shape_add_counts_pos m)

/-- 段 L5 的概率面：整数形状参数更新后，精确 Beta CDF 的括号质量仍恰为 1
    （引用 `BetaInterval.beta_mass_total_one`）。
    法律读法：更新不会把"区间端点是精确的"这一性质弄丢。 -/
theorem beta_predictive_bracket_survives_update (a b w l : ℕ) (ha : 0 < a) (hb : 0 < b) :
    betaMass (a + w) (b + l) 0 1 = 1 :=
  beta_mass_total_one (a + w) (b + l) (by omega) (by omega)

/-- 嵌套制度下的证据质量搬运：先按 `e` 条件化、再按 `o` 取证据质量，等于把 `o` 的证据质量
    除以 `e` 的证据质量。前提 `o ⊑ e`（`o` 成就之处 `e` 必成就）是本定理的适用边界。 -/
theorem evMass_posterior_refined {S : Type} [Fintype S] [DecidableEq S] (p : S → ℚ)
    (e o : S → Bool) (hE : 0 < evMass p e)
    (href : ∀ s, o s = true → e s = true) :
    evMass (posterior p e hE) o = evMass p o / evMass p e := by
  show ∑ s, (if o s = true then posterior p e hE s else 0)
      = (∑ s, if o s = true then p s else 0) / evMass p e
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  by_cases ho : o s = true
  · rw [if_pos ho, if_pos ho]
    show (if e s = true then p s / evMass p e else 0) = p s / evMass p e
    rw [if_pos (href s ho)]
  · rw [if_neg ho, if_neg ho, zero_div]

/-- 双重制度的证据质量自动为正：所以搬运定理里的正性假设不是白拿的。 -/
theorem transport_regime_positivity {S : Type} [Fintype S] [DecidableEq S] (p : S → ℚ)
    (e o : S → Bool) (hE : 0 < evMass p e) (hO : 0 < evMass p o)
    (href : ∀ s, o s = true → e s = true) :
    0 < evMass (posterior p e hE) o := by
  rw [evMass_posterior_refined p e o hE href]
  exact div_pos hO hE

/-- 段 L2↔L4（契约要求的 `selection_transport_from_shared_mechanism`）：
    同一个机制（`Conditioning.posterior`）在两种制度下的读数互相搬运——
    先按宽制度 `e` 条件化、再按窄制度 `o` 条件化，等于直接按 `o` 条件化。
    机制是函数、制度是谓词，搬运方程就是这条等式。
    诚实声明（降级）：只证**嵌套**制度（`href`）；非嵌套情形不成立，
    见 `transport_boundary_needs_nesting` 给出的逐点失效见证。一般（任意制度对）刻画列为未覆盖片段。 -/
theorem selection_transport_from_shared_mechanism {S : Type} [Fintype S] [DecidableEq S]
    (p : S → ℚ) (e o : S → Bool) (hE : 0 < evMass p e) (hO : 0 < evMass p o)
    (href : ∀ s, o s = true → e s = true)
    (hV : 0 < evMass (posterior p e hE) o) :
    posterior (posterior p e hE) o hV = posterior p o hO := by
  have hscale : evMass (posterior p e hE) o = evMass p o / evMass p e :=
    evMass_posterior_refined p e o hE href
  have hZ : evMass p e ≠ 0 := ne_of_gt hE
  have hW : evMass p o ≠ 0 := ne_of_gt hO
  funext s
  show (if o s = true then posterior p e hE s / evMass (posterior p e hE) o else 0) =
    (if o s = true then p s / evMass p o else 0)
  by_cases ho : o s = true
  · rw [if_pos ho, if_pos ho, hscale]
    show (if e s = true then p s / evMass p e else 0) / (evMass p o / evMass p e) =
      p s / evMass p o
    rw [if_pos (href s ho)]
    field_simp [hZ, hW]
  · rw [if_neg ho, if_neg ho]

/-- 段 L2↔L4 的适用边界（降级声明，非疏漏）：搬运定理的前提 `href` 不能去掉。
    只要存在一个被窄制度 `o` 选中、却被宽制度 `e` 排除、且概率为正的状态，
    该状态在搬运方程两侧的和项就不相等——左端把它归零，右端仍给出正的贡献。
    法律读法：换了观察口径，"同一批数据"可能在第二个口径下被排除；此时不能继续沿用
    上一个口径的后验，更不能把被排除的情形当作零证据质量后的残余概率。
    本件只给出逐点失效面，未给出"何时仍可调运"的完整刻画（列为未覆盖片段）。 -/
theorem transport_boundary_needs_nesting {S : Type} [Fintype S] [DecidableEq S] (p : S → ℚ)
    (e o : S → Bool) (hE : 0 < evMass p e) (s : S)
    (hs_o : o s = true) (hs_e : ¬ (e s = true)) (hs_p : 0 < p s) :
    (if o s = true then p s / evMass p e else 0) ≠
      (if o s = true then (if e s = true then p s / evMass p e else 0) else 0) := by
  rw [if_pos hs_o, if_pos hs_o, if_neg hs_e]
  exact ne_of_gt (div_pos hs_p hE)

/-- 精确金额的有理像：`Int` 最小货币单位直接置入 ℚ；这是金额进入比例比较的唯一通道，
    中间不含任何舍入步骤。 -/
def exactAmountQ (a : ExactAmountM5) : ℚ := a.minorUnits

/-- 带政策门的读数：政策缺失时不给出读数（沿用 `ExactNumericContract` 的 fail-closed 合同：
    `decisiveWithRounding` 要求 `policy.isSome`；本件用 `match` 而不是 `if`，
    因为 `decisiveWithRounding` 不是可判定谓词，用 `if` 会引入经典性选择）。 -/
def denotateWithPolicy (a : ExactAmountM5) (policy : Option RoundingPolicy) : Option ℚ :=
  match policy with
  | some _ => some (exactAmountQ a)
  | none => none

/-- 读数存在当且仅当政策在场（形状与 `decisiveWithRounding` 一致）：
    有政策时读数就是有理像，无政策时读数为 `none`；两条都是定义的展开。 -/
theorem denotate_some_none (a : ExactAmountM5) (p : RoundingPolicy) :
    denotateWithPolicy a (some p) = some (exactAmountQ a) ∧
      denotateWithPolicy a none = none := ⟨rfl, rfl⟩

/-- 段 L5（契约要求的 `exact_amount_denotation`）：显式舍入政策下，精确金额的读数
    就是它的最小货币单位有理像。"无舍入"不是本件的假设而是定义的事实：
    读数函数里根本没有舍入映射，政策只决定 decisive。
    实质引用：`explicit_rounding_decisive`（`ExactNumericContract.lean:68`），不重证。 -/
theorem exact_amount_denotation (a : ExactAmountM5) (p : RoundingPolicy) :
    denotateWithPolicy a (some p) = some (exactAmountQ a) ∧ decisiveWithRounding (some p) :=
  ⟨rfl, explicit_rounding_decisive p⟩

/-- 读数与政策取值无关：任一显式政策给出同一个 ℚ。
    法律读法：政策选择是程序问题，不许改变数额本身。 -/
theorem denotation_independent_of_policy (a : ExactAmountM5) (p q : RoundingPolicy) :
    denotateWithPolicy a (some p) = denotateWithPolicy a (some q) :=
  (exact_amount_denotation a p).1.trans ((exact_amount_denotation a q).1.symm)

/-- 政策缺失时读数不存在，并同时挂上仓内既有结论
    `missing_rounding_not_decisive`（`ExactNumericContract.lean:62`；本件只引用，不重证）。 -/
theorem denotation_blocked_without_policy (a : ExactAmountM5) :
    denotateWithPolicy a none = none ∧ ¬ decisiveWithRounding (none : Option RoundingPolicy) :=
  ⟨rfl, missing_rounding_not_decisive⟩

/-- 读数是币种盲的：整数位相同而币种不同的两笔金额有相同的有理像、却是不同的金额对象。
    法律读法：数值相等绝不等于同一笔钱；桥只搬数量，不搬币种。 -/
theorem exact_amount_denotation_is_currency_blind :
    ∃ x y : ExactAmountM5, exactAmountQ x = exactAmountQ y ∧ x ≠ y :=
  ⟨{ minorUnits := 100, currency := "CNY" }, { minorUnits := 100, currency := "USD" }, rfl,
    fun h => absurd (congrArg ExactAmountM5.currency h) (by decide)⟩

end FiveSegments

section PenaltyReduction

/-- 金额：整数最小货币单位（与 `ExactAmountM5.minorUnits` 同域；正式路径禁止二进制浮点）。
    用 `abbrev` 而非 `def`，好让整数的算术与序实例直接可用（数值仍是 ℤ）。 -/
abbrev Amount := ℤ

/-- 金额的有理像：比例与门槛比较一律在此进行（`ℚ` 精确，绝无 `Float`）。 -/
def amountQ (x : Amount) : ℚ := x

/-- 酌减的法定条件集（有限、可判定；条目名逐字对应已核验条文，不增不减）：
    `request_by_party` 与 `discretionary_finding` 出自《民法典》第585条第2款
    （"可以根据当事人的请求予以适当减少"）与法释〔2023〕13号第65条第2款的"一般可以认定"；
    `thirty_percent_ground` 是第65条第2款的百分之三十门槛；
    `bad_faith_bar` 是第65条第3款"恶意违约……一般不予支持"；
    `burden_of_proof` 是第64条第2款的举证责任；
    `balancing_factors` 是第65条第1款列举的衡量因素面（刻意不产出结论）。 -/
inductive ReductionCondition where
  | request_by_party
  | discretionary_finding
  | thirty_percent_ground
  | bad_faith_bar
  | burden_of_proof
  | balancing_factors
  deriving DecidableEq

/-- 条件数据：两个金额、四个条件位，外加一个自由输入的因素面 `F`
    （第65条第1款的"合同主体、交易类型、合同的履行情况、当事人的过错程度、履约背景"
    在本件里始终是 `F` 中的一个未解释输入，本件不把它写成定理）。 -/
structure ReductionData (F : Type) where
  /-- 约定的违约金（最小货币单位）。 -/
  agreed : Amount
  /-- 《民法典》第584条规定的损失基础（最小货币单位）。 -/
  loss : Amount
  /-- 第585条第2款：是否有当事人请求。 -/
  requested : Bool
  /-- 第65条第3款：是否恶意违约。 -/
  badFaith : Bool
  /-- 第64条第2款：违约方是否完成"过分高于"的举证。 -/
  proved : Bool
  /-- 第65条第2款："一般可以认定"的裁定位（许可，不是强制）。 -/
  overFound : Bool
  /-- 第65条第3款"一般不予支持"的**例外面**（2026-10-04 增，17_ 卷 R5）：
      `reductionGate` 里 `!badFaith` 是"一般"的机器形态；本位是法院认定例外情形的
      **独立认定位**——例外的开启不靠把恶意违约位改小，而靠另行认定。默认 false，
      所有既有夹具的读数不变。 -/
  maliciousException : Bool := false
  /-- 第65条第1款的衡量因素面：自由输入。 -/
  factors : F

/-- 30% 门槛的精确有理陈述：约定的违约金超过造成的损失的百分之三十，
    即 `约定额 > 损失 × (1 + 30/100) = 损失 × 13/10`。 -/
def overThirtyThreshold {F : Type} (c : ReductionData F) : Prop :=
  (13 / 10 : ℚ) * amountQ c.loss < amountQ c.agreed

/-- 门槛的可判定整数形态：两边同乘正数 10，得 `13 * 损失 < 10 * 约定额`。 -/
def overThirtyTest {F : Type} (c : ReductionData F) : Bool :=
  if 13 * c.loss < 10 * c.agreed then true else false

/-- 百分之三十的精确有理表示：`30/100 = 3/10`，`1 + 3/10 = 13/10`（全程 ℚ，无浮点）。 -/
theorem thirty_percent_rational_exact :
    (30 : ℚ) / 100 = 3 / 10 ∧ (1 : ℚ) + 3 / 10 = 13 / 10 := by
  constructor <;> norm_num

/-- 门槛的两种形态等价：ℚ 比较与整数比较说的是同一件事（乘正数 10 保序）。 -/
theorem overThirtyThreshold_iff_intTest {F : Type} (c : ReductionData F) :
    overThirtyThreshold c ↔ (13 : Amount) * c.loss < 10 * c.agreed := by
  unfold overThirtyThreshold amountQ
  have key : (13 / 10 : ℚ) * (c.loss : ℚ) = (13 : ℚ) * (c.loss : ℚ) / 10 := by
    field_simp
  rw [key, div_lt_iff₀' (show (0 : ℚ) < 10 by norm_num)]
  constructor <;> intro h <;> exact_mod_cast h

/-- 门槛的"超出部分"读法：门槛成立当且仅当超出损失的部分大于损失的 30%。
    法律读法：条文说的是"超过……百分之三十"，本件把这句话写成可核验的等价式。 -/
theorem overThirtyThreshold_iff_excess {F : Type} (c : ReductionData F) :
    overThirtyThreshold c ↔ amountQ (c.agreed - c.loss) > (3 / 10 : ℚ) * amountQ c.loss := by
  have key : (13 / 10 : ℚ) * amountQ c.loss =
      amountQ c.loss + (3 / 10 : ℚ) * amountQ c.loss := by
    ring
  have hsub : amountQ (c.agreed - c.loss) = amountQ c.agreed - amountQ c.loss :=
    Int.cast_sub _ _
  rw [show overThirtyThreshold c = ((13 / 10 : ℚ) * amountQ c.loss < amountQ c.agreed) from rfl,
      key, hsub]
  constructor <;> intro h <;> linarith

/-- 门槛的 Bool 判定正确：`overThirtyTest c = true` 恰是整数形态的门槛成立。 -/
theorem overThirtyTest_true_iff {F : Type} (c : ReductionData F) :
    overThirtyTest c = true ↔ (13 : Amount) * c.loss < 10 * c.agreed := by
  unfold overThirtyTest
  constructor
  · intro h
    by_cases hh : (13 : Amount) * c.loss < 10 * c.agreed
    · exact hh
    · rw [if_neg hh] at h
      exact absurd h Bool.false_ne_true
  · intro h
    exact if_pos h

/-- 条件成就表：把有限条件集里的每一条映射到条件数据上的一个可判定事实。
    `balancing_factors` 恒成就但从不进入闸门——它就是本件刻意不建定理的那一面。 -/
def conditionHolds {F : Type} (k : ReductionCondition) (c : ReductionData F) : Bool :=
  match k with
  | .request_by_party => c.requested
  | .discretionary_finding => c.overFound
  | .thirty_percent_ground => overThirtyTest c
  | .bad_faith_bar => c.badFaith
  | .burden_of_proof => c.proved
  | .balancing_factors => true

/-- 酌减闸门：由条件集合成——有请求 ∧ 非恶意违约 ∧ 违约方已举证 ∧
    （法院认定过分高于 ∨ 30% 门槛成立）。
    注意 `balancing_factors` 被刻意排除在闸门之外。 -/
def reductionGate {F : Type} (c : ReductionData F) : Bool :=
  conditionHolds .request_by_party c && !conditionHolds .bad_faith_bar c &&
    conditionHolds .burden_of_proof c &&
    (conditionHolds .discretionary_finding c || conditionHolds .thirty_percent_ground c)

/-- 准许下界：以第584条损失为基础，但不越过约定额（`min 约定额 (max 损失 0)`）。
    法律读法：酌减的基准是损失，不是约定额本身；下界也不会因损失为负而失真。 -/
def reductionFloor {F : Type} (c : ReductionData F) : Amount := min c.agreed (max c.loss 0)

/-- 下界永远不超过约定额（准入区间因此永不为空）。 -/
theorem reductionFloor_le_agreed {F : Type} (c : ReductionData F) :
    reductionFloor c ≤ c.agreed := by
  unfold reductionFloor
  exact min_le_left _ _

/-- 允许酌减关系 `Allow`（P-098 的核心：这是一个**关系**，不是钳制函数）：
    (i) 闸门开时下界到约定额之间的额都可准许；
    (ii) 闸门关时唯一可准许的是维持约定额（不告不理、恶意违约不予支持、举证不能、
        未认定过分高于——四种关闸理由各自的法条依据见 `ReductionCondition`）。
    30% 门槛通过 `reductionGate` 里的 `conditionHolds .thirty_percent_ground` 进入本关系，
    其地位是准入条件而非计算规则。 -/
def Allow {F : Type} (c : ReductionData F) (x : Amount) : Prop :=
  (reductionGate c = true → reductionFloor c ≤ x ∧ x ≤ c.agreed) ∧
    (reductionGate c = true ∨ x = c.agreed)

/-- 闸门开时的准入判据：给出落在 `[下界, 约定额]` 内的额即可被准许。 -/
theorem allow_of_gate_open {F : Type} (c : ReductionData F) (x : Amount)
    (hg : reductionGate c = true) (hband : reductionFloor c ≤ x ∧ x ≤ c.agreed) :
    Allow c x := ⟨fun _ => hband, Or.inl hg⟩

/-- 闸门关时的唯一准许：只有维持约定额。 -/
theorem allow_of_gate_closed {F : Type} (c : ReductionData F) (x : Amount)
    (hg : reductionGate c ≠ true) (hx : x = c.agreed) : Allow c x :=
  ⟨fun h => absurd h hg, Or.inr hx⟩

/-- 声明的酌减选择函数 `choose`（契约里的 choose）：闸门开取损失基础上的下界，
    闸门关维持约定额。本件不声称它是最优或唯一选择（见 `allow_does_not_determine_amount`）。 -/
def choose {F : Type} (c : ReductionData F) : Amount :=
  if reductionGate c = true then reductionFloor c else c.agreed

/-- 契约要求：选择函数给出的额总是被准许关系接受（对一切条件数据成立，
    不依赖任何数值假设——因为下界与约定额的区间永不退化）。 -/
theorem reduction_admits_declared_conditions {F : Type} (c : ReductionData F) :
    Allow c (choose c) := by
  refine ⟨?_, ?_⟩
  · intro hg
    rw [choose, if_pos hg]
    exact ⟨le_refl _, reductionFloor_le_agreed c⟩
  · by_cases hg : reductionGate c = true
    · rw [choose, if_pos hg]
      exact Or.inl hg
    · rw [choose, if_neg hg]
      exact Or.inr rfl

/-- 区间归入性（现有 clamp 定理的形状）：带有效时钳制值必落在带内。
    这是对仓库 `Genealogy/Part5.lean` 的 `P098.clamp` / `clamp_below_in_band` 等定理的
    ℤ 版本镜像；原定理一律不动。 -/
def clampInt (lo hi x : Amount) : Amount :=
  if x < lo then lo else if hi < x then hi else x

/-- 钳制式"酌减"提案：把损失钳进 `[0, 约定额]`。 -/
def clampReduction {F : Type} (c : ReductionData F) : Amount := clampInt 0 c.agreed c.loss

/-- 钳制的归入性：只要约定额非负，钳制值就在带内（这正是 clamp 被误当成酌减的原因）。 -/
theorem clampReduction_in_band {F : Type} (c : ReductionData F) (h : (0 : Amount) ≤ c.agreed) :
    (0 : Amount) ≤ clampReduction c ∧ clampReduction c ≤ c.agreed := by
  unfold clampReduction clampInt
  split_ifs with h1 h2
  · exact ⟨le_refl _, h⟩
  · exact ⟨h, le_refl _⟩
  · exact ⟨not_lt.mp h1, not_lt.mp h2⟩

/-- 恶意违约的条件数据：请求、举证、认定过分高于皆备，约定额 200、损失 100（门槛成立），
    但当事人恶意违约（第65条第3款）。 -/
def maliciousData : ReductionData Unit :=
  { agreed := 200, loss := 100, requested := true, badFaith := true, proved := true,
    overFound := true, factors := () }

/-- 恶意违约把闸门关掉：`reductionGate maliciousData = false`（第65条第3款），
    即使其余三个条件位全为真、30% 门槛也成立。闭式 Bool/ℤ 计算，不用浮点。 -/
theorem maliciousData_gate : reductionGate maliciousData = false := by
  simp [reductionGate, conditionHolds, overThirtyTest, maliciousData]

/-- 恶意违约时唯一准许额是维持约定额：`choose` 给出的正是 200。 -/
theorem maliciousData_choose : choose maliciousData = (200 : Amount) := by
  have hg : reductionGate maliciousData ≠ true := by simp [maliciousData_gate]
  rw [choose, if_neg hg]
  rfl

/-- 恶意违约数据上钳制值 = 100（落在带内，却低于约定额）。 -/
theorem maliciousData_clamp : clampReduction maliciousData = (100 : Amount) := by
  simp [clampReduction, clampInt, maliciousData]

/-- 中文说明（**例外通道**，17_ 卷 R5）：第 65 条第 3 款是"一般不予支持"，不是"一律"。
    本通道与 `reductionGate` 并行：同样的三个条件位（请求、举证、认定过分高于或 30% 门槛），
    但**不读 badFaith**、改读**独立认定的例外面** `maliciousException`。
    法律读法：例外不是把恶意违约当没看见，而是法院另行认定本案属例外情形。 -/
def exceptionGate {F : Type} (c : ReductionData F) : Bool :=
  conditionHolds .request_by_party c && conditionHolds .burden_of_proof c &&
    (conditionHolds .discretionary_finding c || conditionHolds .thirty_percent_ground c) &&
    c.maliciousException

/-- 中文证明（**例外通道对恶意违约位色盲**）：这正是"例外归例外、一般归一般"的机器形态——
    改 `badFaith` 不改例外通道的读数，正如改例外面不动"一般"闸门。 -/
theorem exception_gate_does_not_read_bad_faith {F : Type} (c : ReductionData F) (b b' : Bool) :
    exceptionGate { c with badFaith := b } = exceptionGate { c with badFaith := b' } := by
  simp [exceptionGate, conditionHolds]

/-- 中文证明（**例外必须被显式认定**）：例外通道开启 ⇒ 例外面位为真。
    这条堵住"输出层静默降档"——任何经例外通道的酌减都必须能指回一项认定。 -/
theorem exception_gate_requires_explicit_finding {F : Type} (c : ReductionData F)
    (h : exceptionGate c = true) : c.maliciousException = true := by
  simp [exceptionGate] at h
  exact h.2.2.1

/-- 中文见证（**一般闸门与例外通道在同一份数据上分道**）：`maliciousData` 上
    "一般"闸门关（既有定理），把例外面认定为真后例外通道开——同一份恶意违约数据，
    两条路给出不同读数，且各自都要指回自己的认定。 -/
def maliciousExceptData : ReductionData Unit :=
  { agreed := 200, loss := 100, requested := true, badFaith := true, proved := true,
    overFound := true, maliciousException := true, factors := () }

theorem ordinary_gate_still_blocks_maliciousExceptData :
    reductionGate maliciousExceptData = false := by
  simp [reductionGate, conditionHolds, overThirtyTest, maliciousExceptData]

theorem exception_gate_opens_on_explicit_finding :
    exceptionGate maliciousExceptData = true := by
  simp [exceptionGate, conditionHolds, overThirtyTest, maliciousExceptData]

/-- 中文证明（**两条通道不可同时混用**）：例外通道开不改变"一般"闸门关；
    反之亦然。把 R5 的修法说死：例外是并行的第二读数，不是对第一读数的改写。 -/
theorem exception_does_not_rewrite_the_ordinary_gate {F : Type} (c : ReductionData F) :
    reductionGate { c with maliciousException := true } = reductionGate c := by
  simp [reductionGate, conditionHolds]

/-- 恶意违约数据的下界同样是 100：钳制与下界在此例重合，正是误导之处。 -/
theorem maliciousData_floor : reductionFloor maliciousData = (100 : Amount) := by
  simp [reductionFloor, maliciousData]

/-- 契约要求的反例对 `clamp_is_not_reduction`：钳制值满足区间归入（0 ≤ 100 ≤ 200），
    却在同一份条件数据上违反 `Allow`——因为恶意违约使闸门关闭，此时唯一可准许的是
    维持约定额。结论：区间归入**不是**法律上的可酌减性质。 -/
theorem clamp_is_not_reduction :
    (0 ≤ clampReduction maliciousData ∧ clampReduction maliciousData ≤ maliciousData.agreed) ∧
      ¬ Allow maliciousData (clampReduction maliciousData) := by
  have hb : 0 ≤ clampReduction maliciousData ∧
      clampReduction maliciousData ≤ maliciousData.agreed := by
    refine ⟨?_, ?_⟩
    · rw [maliciousData_clamp]
      decide
    · rw [maliciousData_clamp]
      simp only [maliciousData]
      decide
  refine ⟨hb, ?_⟩
  intro hall
  obtain ⟨_, h2⟩ := hall
  cases h2 with
  | inl hg => exact absurd hg (by simp [maliciousData_gate])
  | inr he =>
      have hne : clampReduction maliciousData ≠ maliciousData.agreed := by
        rw [maliciousData_clamp]
        simp only [maliciousData]
        decide
      exact hne he

/-- 归入性不等于准许的一般形式：存在条件数据与金额，满足下界与上界，却不被 `Allow` 接受。 -/
theorem band_containment_is_not_allow :
    ∃ (c : ReductionData Unit) (x : Amount),
      reductionFloor c ≤ x ∧ x ≤ c.agreed ∧ ¬ Allow c x := by
  refine ⟨maliciousData, reductionFloor maliciousData, le_refl _,
    reductionFloor_le_agreed maliciousData, ?_⟩
  intro hall
  obtain ⟨_, h2⟩ := hall
  cases h2 with
  | inl hg => exact absurd hg (by simp [maliciousData_gate])
  | inr he =>
      rw [maliciousData_floor, maliciousData] at he
      exact absurd he (by decide)

/-- 门槛齐备但非恶意、法院未另行认定的条件数据：闸门只因 30% 门槛而开
    （"可以认定"是许可，不是必须）。 -/
def lossBasedData : ReductionData Unit :=
  { agreed := 200, loss := 100, requested := true, badFaith := false, proved := true,
    overFound := false, factors := () }

/-- 门槛不成立、但法院依第65条第1款的因素面另行认定过分高于的条件数据
    （约定额 120、损失 100：`13 * 100 = 1300 ≥ 10 * 120 = 1200`）。 -/
def otherGroundData : ReductionData Unit :=
  { agreed := 120, loss := 100, requested := true, badFaith := false, proved := true,
    overFound := true, factors := () }

/-- 见证数据的数值事实（由 `simp` 在 ℤ/Bool 上闭式算出，不用浮点、不用经典性）：
    门槛使 `lossBasedData` 开闸，恶意违约使 `maliciousData` 关闸，
    因素面认定使 `otherGroundData` 开闸。 -/
theorem lossBasedData_facts :
    reductionGate lossBasedData = true ∧ reductionFloor lossBasedData = (100 : Amount) ∧
      reductionGate maliciousData = false ∧ choose maliciousData = (200 : Amount) ∧
      choose lossBasedData = (100 : Amount) ∧ reductionGate otherGroundData = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [reductionGate, conditionHolds, overThirtyTest, lossBasedData]
  · simp [reductionFloor, lossBasedData]
  · simp [reductionGate, conditionHolds, overThirtyTest, maliciousData]
  · simp [choose, reductionGate, conditionHolds, overThirtyTest, maliciousData]
  · simp [choose, reductionFloor, reductionGate, conditionHolds, overThirtyTest, lossBasedData]
  · simp [reductionGate, conditionHolds, overThirtyTest, otherGroundData]

/-- 门槛在 `lossBasedData` 上成立（ℚ 精确比较：`13/10 * 100 = 130 < 200`）。 -/
theorem lossBasedData_overThirty : overThirtyThreshold lossBasedData := by
  rw [overThirtyThreshold_iff_intTest]
  simp only [lossBasedData]
  decide

/-- 门槛在 `otherGroundData` 上不成立（`1300 < 1200` 为假）。 -/
theorem otherGroundData_not_overThirty : ¬ overThirtyThreshold otherGroundData := by
  rw [overThirtyThreshold_iff_intTest]
  simp only [otherGroundData]
  decide

/-- 门槛成立并不自动使法院的认定成立（许可式）：存在门槛成立而认定位为假的数据。
    法律读法：65条第2款是"可以认定"，不是"应当认定"。 -/
theorem threshold_does_not_force_the_finding :
    ∃ (c : ReductionData Unit), overThirtyThreshold c ∧ c.overFound = false :=
  ⟨lossBasedData, lossBasedData_overThirty, rfl⟩

/-- 认定成立并不必来自门槛（第65条第1款的因素面可另行认定）：
    存在门槛不成立而认定位为真的数据，而且闸门仍开。 -/
theorem finding_does_not_require_the_threshold :
    ∃ (c : ReductionData Unit), ¬ overThirtyThreshold c ∧ c.overFound = true ∧
      reductionGate c = true :=
  ⟨otherGroundData, otherGroundData_not_overThirty, rfl,
    by simp [reductionGate, conditionHolds, overThirtyTest, otherGroundData]⟩

end PenaltyReduction

section Limitation

/-- 契约要求的限制定理（D）：满足 `Allow` 并不把酌减后的额唯一决定——
    同一份条件数据上，下界（100）与约定额（200）都被准许且互不相等。
    镜像 `Seams/Representation.lean` 的 `observations_do_not_separate_until_declared` 的诚实写法：
    交出见证，不交出"唯一性"。
    法律读法："适当减少"的幅度是量定面，本件只刻画可准入性，不把量定写成定理。 -/
theorem allow_does_not_determine_amount :
    ∃ (c : ReductionData Unit) (x y : Amount),
      x ≠ y ∧ Allow c x ∧ Allow c y := by
  have hgate : reductionGate lossBasedData = true :=
    by simp [reductionGate, conditionHolds, overThirtyTest, lossBasedData]
  have hfloor : reductionFloor lossBasedData = (100 : Amount) :=
    by simp [reductionFloor, lossBasedData]
  refine ⟨lossBasedData, 100, 200, by decide, ?_, ?_⟩
  · exact allow_of_gate_open lossBasedData 100 hgate
      ⟨le_of_eq hfloor, by simp [lossBasedData]⟩
  · exact allow_of_gate_open lossBasedData 200 hgate
      ⟨hfloor ▸ (by decide : (100 : Amount) ≤ 200), le_refl _⟩

/-- 更强形式的同一限制：30% 门槛成立、全部条件齐备，金额仍不唯一决定
    （沿用 `allow_does_not_determine_amount` 的同一见证 `lossBasedData`）。 -/
theorem threshold_does_not_determine_amount :
    ∃ (c : ReductionData Unit), overThirtyThreshold c ∧
      ∃ x y : Amount, x ≠ y ∧ Allow c x ∧ Allow c y := by
  have hgate : reductionGate lossBasedData = true :=
    by simp [reductionGate, conditionHolds, overThirtyTest, lossBasedData]
  have hfloor : reductionFloor lossBasedData = (100 : Amount) :=
    by simp [reductionFloor, lossBasedData]
  refine ⟨lossBasedData, lossBasedData_overThirty, 100, 200, by decide, ?_, ?_⟩
  · exact allow_of_gate_open lossBasedData 100 hgate
      ⟨le_of_eq hfloor, by simp [lossBasedData]⟩
  · exact allow_of_gate_open lossBasedData 200 hgate
      ⟨hfloor ▸ (by decide : (100 : Amount) ≤ 200), le_refl _⟩

/-- 选择函数不被 `Allow` 刻画：存在被准许的额不等于 `choose` 给出的额。
    法律读法：交出任何一个具体酌减额，都不可能是"由关系决定出来的"唯一结果。 -/
theorem choose_is_not_determined_by_allow :
    ∃ (c : ReductionData Unit) (x : Amount), Allow c x ∧ x ≠ choose c := by
  have hgate : reductionGate lossBasedData = true :=
    by simp [reductionGate, conditionHolds, overThirtyTest, lossBasedData]
  have hfloor : reductionFloor lossBasedData = (100 : Amount) :=
    by simp [reductionFloor, lossBasedData]
  have hch : choose lossBasedData = (100 : Amount) := by
    rw [choose, if_pos hgate, hfloor]
  refine ⟨lossBasedData, 200,
    allow_of_gate_open lossBasedData 200 hgate ⟨hfloor ▸ (by decide : (100 : Amount) ≤ 200),
      le_refl _⟩, ?_⟩
  rw [hch]
  decide

/-- 准许额在约定额非负时自动非负：下界的构造保证的不是这个性质，而是区间不退化。 -/
theorem allowed_amount_nonneg_of_nonneg_agreed {F : Type} (c : ReductionData F)
    (h : (0 : Amount) ≤ c.agreed) (hg : reductionGate c = true) (x : Amount)
    (hx : Allow c x) : (0 : Amount) ≤ x := by
  obtain ⟨himp, _⟩ := hx
  have hband := himp hg
  have h0 : (0 : Amount) ≤ reductionFloor c := by
    unfold reductionFloor
    exact le_min h (le_max_right _ _)
  exact le_trans h0 hband.1

end Limitation

/- 第64条第2款的举证责任是**双向**的（代拟稿；条文已按最高法官网权威发布页逐字核验，
    https://www.court.gov.cn/fabu/xiangqing/419382.html，2026-10-01：
    违约方就"约定违约金过分高于损失"举证，守约方就其"约定合理"的主张举证。
    本件主契约 `ReductionData` 只有违约方那一侧的 `proved` 位，因此这一侧在本仓当前模型里
    **没有被表达**。本 namespace 不改动任何既有定义与定理，而是把这一缺口做成可点的事实：
    (i) 附一个只多一个位的结构；(ii) 证既有准许关系对该位**完全盲区**（同一底数据、两个取值
    的准许集相同）；(iii) 证一个双向闸门**能**区分它，从而"缺口可补、当前未补"是定理而非注释。 -/
namespace TwoSidedBurden

/-- 主契约加一个守约方举证位。`extends` 使底数据可原样取回，故不触碰任何既有陈述。 -/
structure BurdenRecord (F : Type) extends ReductionData F where
  /-- 守约方是否就"约定金额合理"完成举证（第64条第2款的另一侧）。 -/
  compliantProved : Bool

/-- 把现有准许关系搬到双向记录上：它只看底数据，因此对新增位必然盲区。 -/
def AllowOf {F : Type} (b : BurdenRecord F) (x : Amount) : Prop :=
  Allow b.toReductionData x

/-- **盲区定理**：同一底数据下，守约方举证与否**不改变**准许集。
    这不是"法律如此"，而是"本件当前模型如此"——它把未建模的一侧量化成一个可检验的事实。 -/
theorem allow_blind_to_compliant_side {F : Type} (d : ReductionData F) (x : Amount) :
    AllowOf ⟨d, true⟩ x ↔ AllowOf ⟨d, false⟩ x :=
  ⟨fun h => h, fun h => h⟩

/-- 双向闸门：现有闸门 **且** 守约方已完成其一侧举证。 -/
def twoSidedGate {F : Type} (b : BurdenRecord F) : Bool :=
  reductionGate b.toReductionData && b.compliantProved

/-- 双向口径下的准许关系，形状与 `Allow` 一致，只是闸门换成双向闸门。 -/
def AllowTwo {F : Type} (b : BurdenRecord F) (x : Amount) : Prop :=
  (twoSidedGate b = true → reductionFloor b.toReductionData ≤ x ∧ x ≤ b.toReductionData.agreed) ∧
    (twoSidedGate b = true ∨ x = b.toReductionData.agreed)

/-- 底数据取自 `ExactNumericContract` 那一路的小额夹具：约定 300、损失 100（最小货币单位），
    有请求、非恶意、违约方已举证、门槛成立，闸门因此开。 -/
def openGateData : ReductionData Unit := {
  agreed := 300, loss := 100, requested := true, badFaith := false,
  proved := true, overFound := true, factors := () }

/-- 闸门开是可判定的事实，不是假设（约定 300、损失 100：`13·100 < 10·300`）。 -/
theorem openGateData_gate : reductionGate openGateData = true := by
  unfold reductionGate conditionHolds overThirtyTest openGateData
  decide

/-- 守约方位为假时双向闸门必关，与底数据的闸门开无关。 -/
theorem twoSidedGate_false_of_no_compliant_proof {F : Type} (d : ReductionData F) :
    twoSidedGate (⟨d, false⟩ : BurdenRecord F) = false := by
  simp [twoSidedGate]

/-- **区分定理**：把守约方位关掉，双向闸门即关，于是"取下界"这一额在 `AllowTwo` 下不再被准许，
    而在现有 `Allow` 下仍被准许。故新增位不是装饰：它改变外延。 -/
theorem compliant_side_changes_extension :
    AllowOf (⟨openGateData, false⟩ : BurdenRecord Unit) (reductionFloor openGateData) ∧
      ¬ AllowTwo (⟨openGateData, false⟩ : BurdenRecord Unit)
        (reductionFloor openGateData) := by
  have hclosed := twoSidedGate_false_of_no_compliant_proof openGateData
  constructor
  · exact allow_of_gate_open openGateData _ openGateData_gate
      ⟨le_refl _, reductionFloor_le_agreed openGateData⟩
  · intro h
    obtain ⟨_, hor⟩ := h
    rw [hclosed] at hor
    exact absurd hor (by decide)

/-- 守约方位单独不足以开门：底数据闸门关（恶意违约）时，双向闸门也关。
    这一条挡住"把双向举证读成唯一要件"的过度主张。 -/
theorem compliant_alone_does_not_open_gate {F : Type} (d : ReductionData F) (cp : Bool)
    (h : reductionGate d = false) : twoSidedGate ⟨d, cp⟩ = false := by
  simp [twoSidedGate, h]

/-- 法律读法的边界（§五 禁止越界）：本 namespace 只说明**模型对某一侧盲区**，
    不认定任何真实案件中举证责任分配的效果，也不把 `AllowTwo` 说成现行法的关系——
    它是把缺口显形用的对照物。法条一侧的核验状态见 07 卷 §四·一。 -/
theorem twoSided_is_not_the_current_relation_witness :
    ∃ (b : BurdenRecord Unit) (x : Amount), AllowOf b x ∧ ¬ AllowTwo b x :=
  ⟨⟨openGateData, false⟩, reductionFloor openGateData,
    compliant_side_changes_extension.1, compliant_side_changes_extension.2⟩

end TwoSidedBurden

end JurisLean.Seams.Probability
