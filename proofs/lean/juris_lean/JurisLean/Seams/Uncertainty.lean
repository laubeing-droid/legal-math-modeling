import Mathlib
import JurisLean.KernelV3
import JurisLean.TaintNoninterference
import JurisLean.Mandate.ReLUApprox
import JurisLean.FullMath.Probability.Conditioning

/-!
# 缝合件 XU —— 不确定性横切（X-CUT · UNCERTAINTY）

namespace `JurisLean.Seams.Uncertainty`。本件与 L4（概率层）和 L7（闭合层）并行运行，
管三件事：有限正支撑上的**真值桥**、**污染条件化**（taint 代数 ↔ 概率层）、
以及神经网络**输出区间证书的可靠性**。另附两条边界声明：模型类强度（Leshno 型稠密性）
不能充当证书；允许集/稳定核的不确定性记账（法律内容在 S2，不在本件）。

## §法律语义（人话）
1. **概率 1 不等于法律上已认定，也不等于法律上不成立。** 认定（`Judgment.established`）
   是规范评价的结果；概率 1 只是"在有限且每点正质量的支撑上，真值事件覆盖了全部支撑"。
   本件把这句话拆成可证的两半：(a) 有限载体 + 每点正质量时，"真值事件质量为 1"
   与"每个状态本体为真"**互相推出**（`finite_positive_support_truth_bridge`）；
   (b) 一旦支撑上出现零质量原子、或载体不再有限，这座桥就**塌**（两个反例定理）。
   并且即便概率 1 落在"真值事件"上，`KernelV3` 的分层见证仍允许某状态的判断是
   `notEstablished`（`probability_one_on_truth_event_still_allows_not_established`）；
   反向也一样，概率 1 落在"不成立"事件上并不给出本体为假
   （`probability_one_on_not_established_allows_truth_true`，见证取自
   `KernelV3.lean:81-92 judgment_notEstablished_does_not_force_truth_false`）。
2. **被污染的证据不能参与归一化。** 本件把 taint 代数（`TaintNoninterference.lean`，
   纯标签代数、无数值载体）与概率层（`FullMath/Probability/Conditioning.lean` 的
   `evMass`/`posterior`）接起来：归一化的分母**只由干净子集合的质量构成**
   （`xuc_conditioning_denominator_is_clean_mass`），且重复提交同一条污染输入
   **不会改善**采信份额（`copying_tainted_input_never_improves_share`），
   与 taint 侧的 `majority_cannot_clean` / `repetition_does_not_clean` 对齐。
   还要说清：仓库里这两层**原本没有数值链接**，本件的 `ContaminatedCase` 是
   **新声明的接口**，不是把既有两件东西"发现"为已连通。
3. **证书必须"被接受时就可靠"。** 区间证书是数据（半径 `E`、下界 `lo`、上界 `hi`），
   可靠性 = 只要它通过接受检查，真实输出就落在区间内。本件对
   `Mandate/ReLUApprox.lean` 的那个具体网络（两输入、两隐元、一输出）**证明了**这一点，
   复用该文件已证的 `out_stable`（`:135`），不重推 Lipschitz 算术。

## §数学对象
- `evMass`（概率层既有定义，`Conditioning.lean:26`）：`∑ s, if e s then p s else 0`。
- `truthEvent`：把 `KernelV3.TruthJudgment`（`KernelV3.lean:75-77`）的 `truth : Bool`
  分量取出来当概率事件用；`Truth = Bool` 是 `KernelV3.lean:40` 的 abbrev。
- 质量：一律 `ℚ`；计数 `ℕ`；金额：`Int`（`ExactNumericContract.lean:14-15` 口径）；
  二进制浮点全库禁用，本件零出现。
- `ContaminatedCase`：`List FormalInput`（taint 侧）+ `FormalInput → ℚ`（质量侧）。
  干净子集合由 `taintCleanList` 取；`cleanEvidenceMass` 按 `Taint` 分支直接递归，
  并证明它等于"先取干净子集合、再求和"（`cleanEvidenceMass_eq_on_clean_inputs`）。
- `RadiusCert anchor` / `withinBall` / `admitsRadiusCert`：证书片段机件；`anchor` 是
  已知点，`E` 是输入扰动半径，接受检查要求 `[lo, hi]` **包含**可达带
  `[out anchor − lip·E, out anchor + lip·E]`。
- `uncertaintyAllowed` / `uncertaintyKernel`：三值裁决上的最小记账机件（允许集 =
  各可容许评价给出的裁决之集合；稳定核 = 允许集中同时是各评价不动点的那些）。
  名字与 S2（`Seams/AdjudicationBridge.lean` 的 `allowedSet`/`stableKernel`）**刻意不同**。

## §证与不证
已证（本文件内，全部无 `sorry`）：
- `finite_positive_support_truth_bridge`（双向）、`finite_positive_support_truth_mass_iff`
  （非零质量 ↔ 支撑上存在该状态）、`posterior_preserves_positive_truth_mass`
  （概率层的后验在正质量支撑上仍为正）、
  `probability_one_on_truth_event_still_allows_not_established`、
  `probability_one_on_not_established_allows_truth_true`、
  `bridge_fails_without_positivity`（零质量原子反例）、
  `bridge_fails_without_support_finiteness`（无限载体反例）、
  `no_positive_normalisation_on_growing_windows`、`window_mass_stays_below_one`。
- `xuc_conditioning_denominator_is_clean_mass`、`cleanEvidenceMass_eq_on_clean_inputs`、
  `cleanEvidenceMass_cons_tainted`、`copying_tainted_input_never_improves_share`、
  小实例等式 `xuc_case_share`（三条输入、其中一条污染、权重各 1 ⇒ 份额 2/3）、
  `contamination_and_conditioning_do_not_commute`（参数化族，见 §未覆盖片段第 2 条）。
- `nn_interval_certificate_sound_of_two_inputs_two_hidden_one_output`、
  `certificate_rejects_vacuous_interval`、片段的接受/拒绝见证
  `declared_radius_certificate_is_admitted`、`vacuous_interval_is_not_admitted`。
- `rational_target_has_no_least_error`、`probe_agreement_bounds_no_stability_constant`。
- `uncertainty_allowed_non_singleton_with_singleton_kernel`（及其两个分量定理）。
不证（明确禁止本件声称）：
- 不证任何**测度论**意义下的几乎必然/支配收敛；全部推理在 `ℚ` 上的有限和里。
- 不证网络对**任意宽度/深度**的证书可靠性；`ReLUApprox.lean:34-40` 已声明片段边界，
  本件照抄该边界，且**不主张** `lip` 是最小 Lipschitz 常数。
- 不把 `BanachCertificate.lean:103 certificate_error_within_tolerance` 当证明引用：
  它是字段投影（假设的输出，不是证出的界），`:13` 的文档也自陈"certificate schema only"。
- 不给 P-119 与 Leshno 建立对应关系（台账 `docs/master-plan/02_复用总账.md:191` 把 P-119
  记入"UNKNOWN 家规定理群（KernelV3 未决窄化）"，与 Leshno 不是同一件）。

## §未覆盖片段（降级声明，不是证明）
1. **真值桥的法律侧对接**：`KernelV3` 的 `Exhaustion` 四个字段（`:286-290`）是裸 `Prop`，
   与任何求值器没有计算链接；因此"概率 1 ↔ 判断成立"这类** iff 需要显式假设**，
   本件不为其新增 `axiom`，只把桥落在 `truth` 分量上。求值器一侧的对接未覆盖。
2. **污染与条件化的不可交换性**：本件证的是**参数化族**（三状态片段、证据 `{0,1}`、
   假设 `{0}`、`ε` 固定为 `1/2`、先验两点质量 `x, y` 为自由参数，约束 `y ≠ 2x`）。
   它**不是**任意 `ε`、任意宽度空间的定理；`Misspecification.lean:47` 的对应定理同样
   只给了一个硬编码三点实例，本件不声称超越了"参数化族"这一层级。
3. **稠密性不提供证书**：`External/NeuralNetworkProofs/UniversalApproximation/Leshno/`
   的 `Theorem.lean:110 leshno_dense_iff` 需要强制的 `ClassM σ` 假设，
   `DenselyApproximates`（`Family.lean:149`）是紧支撑域上的**非构造存在性**，
   既无速率也无证书。本件**不导入**该模块，只用两条可证定理
   （`rational_target_has_no_least_error`、`probe_agreement_bounds_no_stability_constant`）
   说明"逼近质量不提供参数/误差上界"这一机制。一般 σ 的"稠密性 ⇒ 无上界"未证，
   属于**文档化边界**。
4. **`nn_interval_certificate_sound` 的完整形态**（任意网络、可检查的接受判据、
   与外部证书格式的对接）未覆盖：`External/NeuralNetworkProofs/**` 中
   `certificate`/`_sound` 声明数为零，本件给出的是片段证明，不是通用证书定理。

## §档位
档位 **B（片段已证 + 边界声明）**：(A) 桥与两反例为完整证明；(B) 污染条件化为
新声明接口上的完整证明（不可交换性只到参数化族）；(C) 证书可靠性只对
两输入/两隐元/一输出片段成立；(D) 两条机制定理已证、一般陈述为文档边界；
(E) 记账类比已证，法律内容归 S2。本文件未进入任何构建认定；状态由 CI 判定。
-/

open JurisLean.KernelV3 (TruthJudgment Judgment)
open JurisLean.FullMath.Probability (evMass posterior)
open JurisLean.Mandate.ReLUApprox (out lip lip_pos lip_eq out_stable out_origin out_at_one)
open BigOperators Finset

namespace JurisLean.Seams.Uncertainty

/-! ## XU-A 有限正支撑真值桥 -/

/-- §法律语义：一个状态的本体真值分量。§数学对象：把 `KernelV3.TruthJudgment`
    （`KernelV3.lean:75-77`）的 `truth : Bool` 取成概率事件，供概率层 `evMass` 使用。
    只取真值分量，绝不取判断分量——二者在 `KernelV3` 里是刻意分层的。 -/
def truthEvent {α : Type} (w : α → TruthJudgment) (a : α) : Bool := (w a).truth

/-- §证与不证：Bool 载体上的有限和分解，供反例计算使用。 -/
theorem sum_bool_eq (f : Bool → ℚ) : (∑ b : Bool, f b) = f true + f false := by
  rw [show (∑ b : Bool, f b) = Finset.sum (Finset.univ : Finset Bool) f from rfl]
  rw [Fintype.univ_bool]
  simp

/-- §法律语义+§数学对象：**主桥**。有限载体 + 每点严格正质量 + 总质量归一 ⇒
    "本体为真这个事件的概率等于 1" 与 "每个状态本体为真" 互相推出。
    这是本件能给的**双向**陈述，两个方向都用了正质量假设；
    没有正质量或载体不有限时桥会塌（见下面两个反例定理）。
    §证与不证：桥只落在 `truth` 分量上，不涉及 `judgment`，也不涉及测度论。 -/
theorem finite_positive_support_truth_bridge
    {α : Type} [Fintype α] [DecidableEq α]
    (p : α → ℚ) (w : α → TruthJudgment)
    (hpos : ∀ a, 0 < p a) (htotal : ∑ a : α, p a = 1) :
    evMass p (truthEvent w) = 1 ↔ ∀ a, (w a).truth = true := by
  constructor
  · intro hme a
    by_contra hna
    have hle : ∀ b, (if truthEvent w b then p b else 0) ≤ p b := by
      intro b
      by_cases hb : (w b).truth = true
      · simp only [truthEvent, if_pos hb]
        exact le_rfl
      · simp only [truthEvent, if_neg hb]
        exact le_of_lt (hpos b)
    have hlt : ∃ b, b ∈ (Finset.univ : Finset α) ∧
        (if truthEvent w b then p b else 0) < p b :=
      ⟨a, Finset.mem_univ a, by
        simp only [truthEvent, if_neg hna]
        exact hpos a⟩
    have hsum : (∑ b, (if truthEvent w b then p b else 0)) < ∑ b, p b :=
      Finset.sum_lt_sum (fun b _ => hle b) hlt
    have heq : evMass p (truthEvent w) = ∑ b, (if truthEvent w b then p b else 0) := rfl
    rw [← heq, hme, htotal] at hsum
    linarith
  · intro hA
    have h1 : evMass p (truthEvent w) = ∑ b : α, p b := by
      unfold evMass
      refine Finset.sum_congr rfl (fun b _ => ?_)
      simp only [truthEvent]
      rw [if_pos (hA b)]
    rw [h1, htotal]

/-- §法律语义：桥的另一半——"非零概率"对应"支撑上真的存在这样一个状态"。
    §数学对象：`0 < evMass p (truthEvent w) ↔ ∃ a, (w a).truth = true`。
    两个方向都只用正质量，不用归一化。 -/
theorem finite_positive_support_truth_mass_iff
    {α : Type} [Fintype α] [DecidableEq α]
    (p : α → ℚ) (w : α → TruthJudgment) (hpos : ∀ a, 0 < p a) :
    0 < evMass p (truthEvent w) ↔ ∃ a, (w a).truth = true := by
  constructor
  · intro hgt
    by_contra hne
    have hall : ∀ b, (if truthEvent w b then p b else 0) = 0 := by
      intro b
      by_cases hb : (w b).truth = true
      · exact absurd hb (fun h => hne (Exists.intro b h))
      · simp only [truthEvent, if_neg hb]
    have hz : evMass p (truthEvent w) = 0 := by
      unfold evMass
      refine Finset.sum_eq_zero ?_
      intro b _
      exact hall b
    linarith [hgt, hz]
  · intro ⟨a, ha⟩
    have hnonneg : ∀ b, 0 ≤ (if truthEvent w b then p b else 0) := by
      intro b
      by_cases hb : (w b).truth = true
      · simp only [truthEvent, if_pos hb]
        exact le_of_lt (hpos b)
      · simp only [truthEvent, if_neg hb]
        exact le_rfl
    have hle := Finset.single_le_sum (fun b _ => hnonneg b) (Finset.mem_univ a)
    have h1 : (if truthEvent w a then p a else 0) = p a := by
      simp only [truthEvent, if_pos ha]
    rw [h1] at hle
    show 0 < ∑ b, (if truthEvent w b then p b else 0)
    exact lt_of_lt_of_le (hpos a) hle

/-- §法律语义：概率层的归一化**不会**把正质量的状态压成零——后验仍在真值为真的状态上为正。
    §数学对象：直接对既有定义 `JurisLean.FullMath.Probability.posterior`
    （`Conditioning.lean:49`）与 `evMass`（`Conditioning.lean:26`）陈述。
    这是本件与概率层的**真实调用关系**，不是并列引用。 -/
theorem posterior_preserves_positive_truth_mass
    {α : Type} [Fintype α] [DecidableEq α]
    (p : α → ℚ) (w : α → TruthJudgment) (hpos : ∀ a, 0 < p a)
    (hZ : 0 < evMass p (truthEvent w)) (a : α) (ha : (w a).truth = true) :
    0 < posterior p (truthEvent w) hZ a := by
  show 0 < (if truthEvent w a = true then p a / evMass p (truthEvent w) else 0)
  rw [if_pos (show truthEvent w a = true from ha)]
  exact div_pos (hpos a) hZ

/-- §数学对象（反例 (i) 的载体）：Bool 上的质量，`false` 处质量为零。 -/
def pZeroAtom : Bool → ℚ := fun b => if b = true then 1 else 0

/-- §证与不证：**正质量假设不可去掉**。存在 `Bool` 上的质量 `p` 与真值记录 `w`，
    满足非负、归一、真值事件概率为 1，但**并非**每个状态本体为真：
    零质量原子 `false` 让桥的正向推理失效。 -/
theorem bridge_fails_without_positivity :
    ∃ (p : Bool → ℚ) (w : Bool → TruthJudgment),
      (∀ b, 0 ≤ p b) ∧ (∑ b : Bool, p b = 1) ∧
        evMass p (truthEvent w) = 1 ∧ ¬ (∀ b, (w b).truth = true) := by
  refine ⟨pZeroAtom, fun b => ⟨b, Judgment.undetermined⟩, ?_, ?_, ?_, ?_⟩
  · intro b
    show 0 ≤ (if b = true then (1 : ℚ) else 0)
    by_cases hb : b = true <;> simp [hb]
  · rw [sum_bool_eq]
    simp [pZeroAtom]
  · unfold evMass
    rw [sum_bool_eq]
    simp [pZeroAtom, truthEvent]
  · intro h
    exact absurd (h false) (by decide)

/-- §数学对象（反例 (ii) 的载体）：`ℕ` 上只在状态 0 有质量；真值事件 `AOnlyZero`
    在可见支撑上恒真、在支撑外恒假。 -/
def pNatTail : ℕ → ℚ := fun i => if i = 0 then 1 else 0

/-- §数学对象（反例 (ii)）：可见支撑上的真值事件。 -/
def AOnlyZero : ℕ → Bool := fun i => decide (i = 0)

/-- §证与不证：**支撑有限性假设不可去掉**。在无限载体 `ℕ` 上，可见窗口 `s = {0}`
    里每点质量严格为正、窗口内质量恰好为 1、窗口内真值处处为真，
    但 `∀ i : ℕ, AOnlyZero i = true` 是假的。也就是说"窗口内概率 1"
    永远推不出载体上的逐点真值——桥的正向方向在无限情形直接失效。 -/
theorem bridge_fails_without_support_finiteness :
    ∃ (p : ℕ → ℚ) (A : ℕ → Bool) (s : Finset ℕ),
      (∀ i, 0 ≤ p i) ∧ (∀ i ∈ s, 0 < p i) ∧ s.sum p = 1 ∧
        (∀ i ∈ s, A i = true) ∧ ¬ (∀ i : ℕ, A i = true) := by
  refine ⟨pNatTail, AOnlyZero, {0}, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    show 0 ≤ (if i = 0 then (1 : ℚ) else 0)
    split <;> norm_num
  · intro i hi
    rw [Finset.mem_singleton] at hi
    subst hi
    show 0 < (if (0 : ℕ) = 0 then (1 : ℚ) else 0)
    rw [if_pos rfl]
    norm_num
  · rw [Finset.sum_singleton]
    show (if (0 : ℕ) = 0 then (1 : ℚ) else 0) = 1
    rw [if_pos rfl]
  · intro i hi
    rw [Finset.mem_singleton] at hi
    subst hi
    rfl
  · intro h
    exact (by decide : ¬ (AOnlyZero 1 = true)) (h 1)

/-- §数学对象：窗口放大定理。逐点严格正的 `ℚ` 质量一旦在某个窗口上已经和为 1，
    窗口再放大就必然超过 1。§证与不证：这说明无限载体上"处处正质量"与
    "有限窗口归一"这两件事不能同时维持——桥的两个假设在无限情形互相排斥。 -/
theorem no_positive_normalisation_on_growing_windows
    (p : ℕ → ℚ) (hpos : ∀ i, 0 < p i) (n : ℕ)
    (hsum : ∑ i ∈ Finset.range n, p i = 1) :
    ∑ i ∈ Finset.range (n + 1), p i > 1 := by
  rw [Finset.sum_range_succ, hsum]
  linarith [hpos n]

/-- §数学对象：未处理尾部质量的下界形状（对应
    `FullMath/Probability/UnprocessedMass.lean:20 unprocessed_mass_bounds` 与
    `:39 unprocessed_mass_degenerate`）。可见质量 `visible` 加上未处理的 `tail`
    之后，可见事件的归一化质量**严格小于 1**，因此桥的假设"概率等于 1"
    在有未处理质量时根本取不到。 -/
theorem window_mass_stays_below_one (visible tail : ℚ) (hv : 0 ≤ visible) (ht : 0 < tail) :
    visible / (visible + tail) < 1 := by
  rw [div_lt_one (by linarith)]
  linarith

/-- §数学对象：同一形状的正面半边——可见质量为正时归一化质量确实为正。 -/
theorem window_mass_is_positive (visible tail : ℚ) (hv : 0 < visible) (ht : 0 ≤ tail) :
    0 < visible / (visible + tail) :=
  div_pos hv (by linarith)

/-- §法律语义：概率 1 落在"本体为真"事件上，仍然允许某个状态的判断是**不成立**；
    按 `KernelV3.lean:81-92 judgment_notEstablished_does_not_force_truth_false`，
    反过来也不给本体为假。§证与不证：这里**证明**的是"相容性"
    （存在这样一个配置），不是"可推出"。法律上的读法：满概率的证据既不自动构成认定，
    也不自动构成否认。 -/
theorem probability_one_on_truth_event_still_allows_not_established
    {α : Type} [Fintype α] [DecidableEq α]
    (p : α → ℚ) (a₀ : α) (htotal : ∑ a : α, p a = 1) :
    ∃ (w : α → TruthJudgment),
      evMass p (truthEvent w) = 1 ∧ (w a₀).judgment = Judgment.notEstablished := by
  refine ⟨fun _ => ⟨true, Judgment.notEstablished⟩, ?_, rfl⟩
  have h1 : evMass p (truthEvent (fun _ => ⟨true, Judgment.notEstablished⟩))
      = ∑ b : α, p b := by
    unfold evMass
    refine Finset.sum_congr rfl (fun b _ => ?_)
    simp [truthEvent]
  rw [h1, htotal]

/-- §数学对象：把"判断为不成立"取成概率事件（与 `truthEvent` 对偶，只取 `judgment` 分量）。 -/
def judgmentEvent {α : Type} (w : α → TruthJudgment) (a : α) : Bool :=
  decide ((w a).judgment = Judgment.notEstablished)

/-- §法律语义：概率 1 落在"判断不成立"事件上，也不给出本体为假——同一配置里
    每个状态的本体真值都是真。§证与不证：与上一条合起来就是"概率 1 在两个方向都
    不产生本体否认/肯定"；见证形状取自 `KernelV3.lean:81`（
    `judgment_notEstablished_does_not_force_truth_false`），未新增任何假设。 -/
theorem probability_one_on_not_established_allows_truth_true
    {α : Type} [Fintype α] [DecidableEq α]
    (p : α → ℚ) (a₀ : α) (htotal : ∑ a : α, p a = 1) :
    ∃ (w : α → TruthJudgment),
      evMass p (judgmentEvent w) = 1 ∧ (w a₀).truth = true := by
  refine ⟨fun _ => ⟨true, Judgment.notEstablished⟩, ?_, rfl⟩
  have h1 : evMass p
      (judgmentEvent (fun _ => ⟨true, Judgment.notEstablished⟩)) = ∑ b : α, p b := by
    unfold evMass
    refine Finset.sum_congr rfl (fun b _ => ?_)
    simp [judgmentEvent]
  rw [h1, htotal]

/-! ## XU-B 污染条件化：taint 代数 ↔ 概率层 -/

/-- §法律语义+§数学对象：**新声明的接口**。仓库里 `TaintNoninterference.lean` 是
    一个在 `List FormalInput` 上的三构造子 `inductive Taint`，没有数值载体，也不与
    `FullMath/Probability` 互相导入；概率层则完全不认识污点。本结构把两侧配对：
    `inputs` 是 taint 侧的证据副本列表，`weight` 是给每条证据的 `ℚ` 质量。
    这不是"发现"两层已经连通，而是**新建**一个可计算的桥，故所有定理都在本结构上陈述。 -/
structure ContaminatedCase where
  inputs : List FormalInput
  weight : FormalInput → ℚ

/-- §数学对象：干净子集合（把 tainted 输入整条剔除）。 -/
def taintCleanList : List FormalInput → List FormalInput
  | [] => []
  | x :: xs => if x.taint = Taint.clean then x :: taintCleanList xs else taintCleanList xs

/-- §数学对象：`ℚ` 质量的列表求和。 -/
def massSum : List ℚ → ℚ
  | [] => 0
  | x :: xs => x + massSum xs

/-- §数学对象：干净证据质量——只累加 taint 为 clean 的输入。 -/
def cleanEvidenceMass (w : FormalInput → ℚ) : List FormalInput → ℚ
  | [] => 0
  | x :: xs => if x.taint = Taint.clean then w x + cleanEvidenceMass w xs
                 else cleanEvidenceMass w xs

/-- §数学对象：总证据质量——含 tainted 输入的质量，即污染前的分母。 -/
def totalEvidenceMass (w : FormalInput → ℚ) : List FormalInput → ℚ
  | [] => 0
  | x :: xs => w x + totalEvidenceMass w xs

/-- §数学对象：采信份额 = 干净质量 / 总质量。分母含污染质量，分子不含。 -/
def caseShare (w : FormalInput → ℚ) (xs : List FormalInput) : ℚ :=
  cleanEvidenceMass w xs / totalEvidenceMass w xs

/-- §证：`Taint.tainted ≠ Taint.clean`（纯构造子论证，无假设）。 -/
theorem tainted_ne_clean : Taint.tainted ≠ Taint.clean := by
  intro h
  cases h

/-- §证：tainted 输入不是 clean。 -/
theorem not_clean_of_tainted (x : FormalInput) (hx : x.taint = Taint.tainted) :
    ¬ (x.taint = Taint.clean) := by
  intro hc
  rw [hx] at hc
  exact absurd hc tainted_ne_clean

/-- §证：干净子集合把 tainted 输入整条丢掉。 -/
theorem taintCleanList_cons_tainted (x : FormalInput) (xs : List FormalInput)
    (hx : x.taint = Taint.tainted) : taintCleanList (x :: xs) = taintCleanList xs := by
  simp only [taintCleanList]
  exact if_neg (not_clean_of_tainted x hx)

/-- §证：干净子集合保留 clean 输入。 -/
theorem taintCleanList_cons_clean (x : FormalInput) (xs : List FormalInput)
    (hx : x.taint = Taint.clean) : taintCleanList (x :: xs) = x :: taintCleanList xs := by
  simp only [taintCleanList]
  exact if_pos hx

/-- §证：干净质量丢掉 tainted 输入。 -/
theorem cleanEvidenceMass_cons_tainted (w : FormalInput → ℚ) (x : FormalInput)
    (xs : List FormalInput) (hx : x.taint = Taint.tainted) :
    cleanEvidenceMass w (x :: xs) = cleanEvidenceMass w xs := by
  simp only [cleanEvidenceMass]
  exact if_neg (not_clean_of_tainted x hx)

/-- §证：干净质量累加 clean 输入。 -/
theorem cleanEvidenceMass_cons_clean (w : FormalInput → ℚ) (x : FormalInput)
    (xs : List FormalInput) (hx : x.taint = Taint.clean) :
    cleanEvidenceMass w (x :: xs) = w x + cleanEvidenceMass w xs := by
  simp only [cleanEvidenceMass]
  exact if_pos hx

theorem cleanEvidenceMass_nil (w : FormalInput → ℚ) : cleanEvidenceMass w [] = 0 := rfl
theorem totalEvidenceMass_nil (w : FormalInput → ℚ) : totalEvidenceMass w [] = 0 := rfl

/-- §证：总质量在 cons 处递推（tainted 输入也进分母，这就是污染的作用点）。 -/
theorem totalEvidenceMass_cons (w : FormalInput → ℚ) (x : FormalInput)
    (xs : List FormalInput) :
    totalEvidenceMass w (x :: xs) = w x + totalEvidenceMass w xs := rfl

/-- §证：`massSum` 在 cons 处的递推（自备机件，避免依赖外部列表求和引理名）。 -/
theorem massSum_cons (q : ℚ) (qs : List ℚ) : massSum (q :: qs) = q + massSum qs := by
  simp only [massSum]

/-- §证：**条件化只由干净子集合计算**（列表层）。干净质量等于"先取干净子集合、
    再把权重映射求和"。这是本缝合一侧的实等式，不是口头声明。 -/
theorem cleanEvidenceMass_eq_on_clean_inputs (w : FormalInput → ℚ) (xs : List FormalInput) :
    cleanEvidenceMass w xs = massSum (List.map w (taintCleanList xs)) := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
      cases y with
      | mk subj tnt =>
          cases tnt
          · have hy : ({ subject := subj, taint := Taint.clean } : FormalInput).taint =
                Taint.clean := rfl
            rw [cleanEvidenceMass_cons_clean _ _ _ hy, taintCleanList_cons_clean _ _ hy,
              List.map_cons, massSum_cons, ih]
          · have hy : ({ subject := subj, taint := Taint.tainted } : FormalInput).taint =
                Taint.tainted := rfl
            rw [cleanEvidenceMass_cons_tainted _ _ _ hy,
              taintCleanList_cons_tainted _ _ hy, ih]

/-- §数学对象：把案例的干净质量交给概率层的证据形状（`Bool` 上的质量函数，
    `true` 处放干净质量，`false` 处放 0）。这是 `ContaminatedCase` 作为**新接口**
    的第二半：它让 `FullMath.Probability.evMass` 可以直接作用在 taint 层的量上。 -/
def caseMassOnBool (c : ContaminatedCase) : Bool → ℚ :=
  fun b => if b = true then cleanEvidenceMass c.weight c.inputs else 0

/-- §证：跨层等式——概率层算出的证据质量，就是 taint 层的干净质量。
    于是 `condition`/`posterior` 的除数是干净子集合的和，**不含**被污染输入的质量。
    §证与不证：等式在本件的 `caseMassOnBool` 与既有 `evMass` 之间，
    不声称既有代码路径已被改写。 -/
theorem xuc_conditioning_denominator_is_clean_mass (c : ContaminatedCase) :
    evMass (caseMassOnBool c) id = cleanEvidenceMass c.weight c.inputs := by
  unfold evMass
  rw [sum_bool_eq]
  show caseMassOnBool c true + 0 = cleanEvidenceMass c.weight c.inputs
  rw [show caseMassOnBool c true = cleanEvidenceMass c.weight c.inputs from rfl, add_zero]

/-- §数学对象（可判定小实例）：三条证据，中间一条被污染，权重各 1。 -/
def xuStatute : FormalInput := ⟨"statute", Taint.clean⟩

/-- §数学对象：小实例中被污染的那条。 -/
def xuRumor : FormalInput := ⟨"rumor", Taint.tainted⟩

/-- §数学对象：小实例中另一条干净证据。 -/
def xuRegister : FormalInput := ⟨"register", Taint.clean⟩

/-- §数学对象：小实例权重（各 1）。 -/
def xuWeightOne : FormalInput → ℚ := fun _ => 1

/-- §证：小实例的权重取值（供 `decide`/`norm_num` 使用的显式等式）。 -/
theorem xuWeightOne_apply (x : FormalInput) : xuWeightOne x = 1 := rfl

/-- §证：小实例的干净质量是 2。 -/
theorem xuc_case_clean_mass :
    cleanEvidenceMass xuWeightOne [xuStatute, xuRumor, xuRegister] = 2 := by
  rw [cleanEvidenceMass_cons_clean xuWeightOne xuStatute _
        (show xuStatute.taint = Taint.clean from rfl),
    cleanEvidenceMass_cons_tainted xuWeightOne xuRumor _
        (show xuRumor.taint = Taint.tainted from rfl),
    cleanEvidenceMass_cons_clean xuWeightOne xuRegister _
        (show xuRegister.taint = Taint.clean from rfl),
    cleanEvidenceMass_nil, xuWeightOne_apply, xuWeightOne_apply]
  norm_num

/-- §证：小实例的总质量是 3（污染那条也进了分母）。 -/
theorem xuc_case_total_mass :
    totalEvidenceMass xuWeightOne [xuStatute, xuRumor, xuRegister] = 3 := by
  rw [totalEvidenceMass_cons, totalEvidenceMass_cons, totalEvidenceMass_cons,
    totalEvidenceMass_nil, xuWeightOne_apply, xuWeightOne_apply, xuWeightOne_apply]
  norm_num

/-- §证：小实例的干净子集合恰是两条干净证据。 -/
theorem xuc_case_clean_list :
    taintCleanList [xuStatute, xuRumor, xuRegister] = [xuStatute, xuRegister] := by
  rw [taintCleanList_cons_clean xuStatute _ (show xuStatute.taint = Taint.clean from rfl),
    taintCleanList_cons_tainted xuRumor _ (show xuRumor.taint = Taint.tainted from rfl),
    taintCleanList_cons_clean xuRegister _ (show xuRegister.taint = Taint.clean from rfl)]
  rfl

/-- §证：**可判定小实例等式**：采信份额 = 2/3，即污染那条的 1 份质量只稀释分母、
    完全不进分子。 -/
theorem xuc_case_share :
    caseShare xuWeightOne [xuStatute, xuRumor, xuRegister] = 2 / 3 := by
  rw [caseShare, xuc_case_clean_mass, xuc_case_total_mass]

/-- §证：**重复提交污染证据不会改善保证**（数值侧，对齐
    `TaintNoninterference.lean:80 majority_cannot_clean` 与 `:95 repetition_does_not_clean`）。
    在同一条 tainted 输入上再加一份副本，分子不变、分母增加，份额不升。
    §证与不证：只在这一形式下陈述"不改善"，不声称任何最优性。 -/
theorem copying_tainted_input_never_improves_share (w : FormalInput → ℚ) (x : FormalInput)
    (xs : List FormalInput) (ht : x.taint = Taint.tainted) (hwx : 0 ≤ w x)
    (hC : 0 ≤ cleanEvidenceMass w xs) (hT : 0 < totalEvidenceMass w xs) :
    caseShare w (x :: x :: xs) ≤ caseShare w (x :: xs) := by
  have hc : cleanEvidenceMass w (x :: x :: xs) = cleanEvidenceMass w xs := by
    rw [cleanEvidenceMass_cons_tainted w x (x :: xs) ht,
      cleanEvidenceMass_cons_tainted w x xs ht]
  have hcs : cleanEvidenceMass w (x :: xs) = cleanEvidenceMass w xs :=
    cleanEvidenceMass_cons_tainted w x xs ht
  have ht1 : totalEvidenceMass w (x :: xs) = w x + totalEvidenceMass w xs :=
    totalEvidenceMass_cons w x xs
  have ht2 : totalEvidenceMass w (x :: x :: xs) = w x + (w x + totalEvidenceMass w xs) := by
    rw [totalEvidenceMass_cons, ht1]
  show cleanEvidenceMass w (x :: x :: xs) / totalEvidenceMass w (x :: x :: xs)
      ≤ cleanEvidenceMass w (x :: xs) / totalEvidenceMass w (x :: xs)
  rw [hc, hcs, ht2, ht1]
  have hD : 0 < w x + totalEvidenceMass w xs := by linarith
  have hinv : 1 / (w x + (w x + totalEvidenceMass w xs)) ≤ 1 / (w x + totalEvidenceMass w xs) :=
    one_div_le_one_div_of_le hD (by linarith)
  have hmul : cleanEvidenceMass w xs * (1 / (w x + (w x + totalEvidenceMass w xs)))
      ≤ cleanEvidenceMass w xs * (1 / (w x + totalEvidenceMass w xs)) :=
    mul_le_mul_of_nonneg_left hinv hC
  rw [div_eq_mul_one_div (cleanEvidenceMass w xs) (w x + (w x + totalEvidenceMass w xs)),
    div_eq_mul_one_div (cleanEvidenceMass w xs) (w x + totalEvidenceMass w xs)]
  exact hmul

/-- §数学对象：**先污染后条件化**（片段：三状态、假设 `{0}`、证据 `{0,1}`、`ε = 1/2`）。
    先验在证据两点上的质量各为 `x`，杂质分布在两点上为 `y` 与 `0`。 -/
def contaminateThenCondition (x y : ℚ) : ℚ := (x + y) / (2 * x + y)

/-- §数学对象：**先条件化后污染**（同一片段、同一 `ε = 1/2`）。
    先验后验是 `x/(x+x)`，杂质后验是 `y/(y+0)`，再按 `ε` 混合。 -/
def conditionThenContaminate (x y : ℚ) : ℚ :=
  (1 / 2) * (x / (x + x)) + (1 / 2) * (y / (y + 0))

/-- §证：后条件化侧在本片段上恒等于 `3/4`，与自由参数 `x, y` 无关
    （只要它们为正）。这是两个后验值可比较的前提。 -/
theorem condition_then_contaminate_is_three_quarters (x y : ℚ)
    (hx : 0 < x) (hy : 0 < y) :
    conditionThenContaminate x y = 3 / 4 := by
  unfold conditionThenContaminate
  have h1 : x / (x + x) = 1 / 2 := by
    field_simp
    ring
  have h2 : y / (y + 0) = 1 := by
    rw [add_zero]
    exact div_self (ne_of_gt hy)
  rw [h1, h2]
  norm_num

/-- §证：**污染与条件化不可交换**，且是对**参数化族**证明的
    （`x, y` 为自由 `ℚ` 参数，约束 `0 < x`、`0 < y`、`y ≠ 2·x`），
    不是 `Misspecification.lean:47` 那种硬编码单例。
    §证与不证：片段固定为三状态、证据 `{0,1}`、假设 `{0}`、`ε = 1/2`；
    任意 `ε`、任意状态数的情形未证，见 §未覆盖片段第 2 条。
    法律读法：先验阶段的容差 `ε` 绝不能跨过条件化被复用到后验上。 -/
theorem contamination_and_conditioning_do_not_commute (x y : ℚ)
    (hx : 0 < x) (hy : 0 < y) (hne : y ≠ 2 * x) :
    contaminateThenCondition x y ≠ conditionThenContaminate x y := by
  rw [condition_then_contaminate_is_three_quarters x y hx hy, contaminateThenCondition]
  intro h
  field_simp at h
  ring_nf at h
  exact hne (by linarith)

/-! ## XU-C 神经网络输出区间证书的可靠性（声明片段） -/

/-- §数学对象：半径证书 = 数据。只装半径 `E` 与区间端点 `lo, hi`，
    **不装**任何证明字段；接受与否由 `admitsRadiusCert` 判定，
    于是"被接受"与"已证"是两件不同的事（对齐 `DerivedCertificate.lean` 的
    `admits_iff`（`:116`）口径）。 -/
structure RadiusCert (anchor : ℚ × ℚ) where
  E : ℚ
  lo : ℚ
  hi : ℚ

/-- §数学对象：输入扰动球——两坐标各移动不超过 `E`，与 `ReLUApprox.lean:135`
    `out_stable` 的假设形状一致（`ℚ × ℚ` 是该片段的全部输入维度）。 -/
def withinBall (E : ℚ) (x y : ℚ × ℚ) : Prop :=
  -E ≤ x.1 - y.1 ∧ x.1 - y.1 ≤ E ∧ -E ≤ x.2 - y.2 ∧ x.2 - y.2 ≤ E

/-- §数学对象：接受判据——半径非负，且区间 `[lo, hi]` **包含**可达带
    `[out anchor − lip·E, out anchor + lip·E]`。`lip` 来自
    `Mandate/ReLUApprox.lean:67`（按权重行读出的常数，非最小常数）。 -/
def admitsRadiusCert (anchor : ℚ × ℚ) (c : RadiusCert anchor) : Prop :=
  0 ≤ c.E ∧ c.lo ≤ out anchor - lip * c.E ∧ out anchor + lip * c.E ≤ c.hi

/-- §法律语义+§证：证书可靠性——被接受就一定可靠：真实输出落在声明区间内。
    §证与不证：片段写进定理名字里——**两输入、两隐元、一输出**，即
    `Mandate/ReLUApprox.lean` 的那个网络；证明只复用该文件已证的 `out_stable`（`:135`），
    不重推逐层算术。不主张任意宽度/深度、不主张 `lip` 最小（`:34-40` 的非主张照抄）。
    这是仓库里第一个真正**证出**的网络输出区间可靠性定理；
    `nn_interval_certificate_sound` 这个通用名字仍属未覆盖（§未覆盖片段第 4 条）。 -/
theorem nn_interval_certificate_sound_of_two_inputs_two_hidden_one_output
    {anchor : ℚ × ℚ} (c : RadiusCert anchor) (hc : admitsRadiusCert anchor c)
    {x : ℚ × ℚ} (hx : withinBall c.E x anchor) :
    c.lo ≤ out x ∧ out x ≤ c.hi := by
  obtain ⟨hE, hlo, hhi⟩ := hc
  obtain ⟨l1, u1, l2, u2⟩ := hx
  have hband := out_stable hE l1 u1 l2 u2
  have hleft : out anchor - lip * c.E ≤ out x := by linarith [hband.1]
  have hright : out x ≤ out anchor + lip * c.E := by linarith [hband.2]
  exact ⟨le_trans hlo hleft, le_trans hright hhi⟩

/-- §证：可达带确实含住锚点自己的输出（半径非负 + `lip > 0`）。
    这是下一条"拒绝空区间"方向的算术前提。 -/
theorem anchor_output_is_inside_band {anchor : ℚ × ℚ} (c : RadiusCert anchor)
    (hE : 0 ≤ c.E) :
    out anchor - lip * c.E ≤ out anchor ∧ out anchor ≤ out anchor + lip * c.E := by
  have hband : 0 ≤ lip * c.E := mul_nonneg (le_of_lt lip_pos) hE
  exact ⟨by linarith, by linarith⟩

/-- §证：**拒绝方向**——区间没有真的包住算出来的值，就不被接受
    （对照 `Mandate/DerivedCertificate.lean:138 not_admits_negative`：引用，不重证其内容）。
    §证与不证：陈述的是本件接受判据与 `out anchor` 的关系，不涉及任何外部证书格式。 -/
theorem certificate_rejects_vacuous_interval {anchor : ℚ × ℚ} (c : RadiusCert anchor)
    (hvac : ¬ (c.lo ≤ out anchor ∧ out anchor ≤ c.hi)) :
    ¬ admitsRadiusCert anchor c := by
  rintro ⟨hE, hlo, hhi⟩
  obtain ⟨h1, h2⟩ := anchor_output_is_inside_band (c := c) hE
  exact hvac ⟨le_trans hlo h1, le_trans h2 hhi⟩

/-- §证：片段上的一个**真能被接受**的证书（锚点 `(0,0)`、半径 1、区间 `[-4, 12]`）：
    `out (0,0) = 4`、`lip = 8` 都由 `ReLUApprox.lean:154` 与 `:74` 算出，故可达带是 `[-4, 12]`。
    于是上面的可靠性定理在这个实例上不是空转。 -/
theorem declared_radius_certificate_is_admitted :
    admitsRadiusCert ((0, 0)) ⟨1, -4, 12⟩ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [out_origin, lip_eq]
    norm_num
  · rw [out_origin, lip_eq]
    norm_num

/-- §证：同一锚点上一个**没包住算出来的值**的区间不被接受（`[3,3]` 不含 `out (0,0) = 4`）。
    这是 `certificate_rejects_vacuous_interval` 的具体见证。 -/
theorem vacuous_interval_is_not_admitted :
    ¬ admitsRadiusCert ((0, 0)) ⟨0, 3, 3⟩ := by
  rintro ⟨_, _, hhi⟩
  rw [out_origin, lip_eq] at hhi
  norm_num at hhi

/-- §数学对象：片段网络在 `(2,1)` 处的输出，由 `norm_num` 算出（不是假设）。
    用于下一条定理，说明"零半径只在锚点上可靠"。 -/
theorem xuc_out_at_two_one : out (2, 1) = 7 := by
  norm_num [JurisLean.Mandate.ReLUApprox.out, JurisLean.Mandate.ReLUApprox.h1,
    JurisLean.Mandate.ReLUApprox.h2, JurisLean.Mandate.ReLUApprox.relu]

/-- §证：零半径证书的可达带只覆盖锚点自己——同一个网络在 `(1,0)` 处取值 `5`
    （`ReLUApprox.lean:157 out_at_one`），故 `out (0,0) = 4 < 5`。
    法律/工程读法：把误差预算记成 0 的证书只能声明锚点，不能外推到任何别的输入；
    该网络非常数（`:160 out_not_constant`），所以外推必然越界。 -/
theorem zero_radius_band_does_not_cover_other_inputs : (4 : ℚ) < out (1, 0) := by
  rw [out_at_one]
  norm_num

/-! ## XU-D 模型类强度检查（Leshno 型稠密性不能充当证书） -/

/-- §证：`ℚ` 没有最小正元——任意误差目标 `ε` 都有更小的 `ε/2`。
    §证与不证：这条刻画的正是"只有存在性、没有速率"的陈述为什么提供不了证书：
    误差目标可以无限收紧，而收紧本身不交出任何可检查的界。 -/
theorem rational_target_has_no_least_error (ε : ℚ) (hε : 0 < ε) :
    ∃ ε' : ℚ, 0 < ε' ∧ ε' < ε :=
  ⟨ε / 2, half_pos hε, half_lt_self_iff.mpr hε⟩

/-- §证：**在声明的探针集 `{(0,0),(1,0)}` 上与网络完全一致，不给任何稳定常数**。
    对每个 `B` 都造出一个在这两点与 `out` 取值相同、却在 `(0,0)` 与 `(2,1)` 之间
    突破 `B` 倍半径界的函数。§证与不证：这是 (D) 的机制性证明——
    只说"逼近/一致不提供参数或误差上界"，不导入 Leshno 模块，
    也不声称 `DenselyApproximates` 的一般性质（见 §未覆盖片段第 3 条）。
    片段：两输入、两隐元、一输出，探针集两点，`E = 2`。 -/
theorem probe_agreement_bounds_no_stability_constant (B : ℚ) :
    ∃ g : ℚ × ℚ → ℚ,
      g (0, 0) = out (0, 0) ∧ g (1, 0) = out (1, 0) ∧
        ¬ (∀ x y : ℚ × ℚ, withinBall 2 x y →
          -(B * 2) ≤ g x - g y ∧ g x - g y ≤ B * 2) := by
  refine ⟨fun z => out z + (B + 1) * (z.1 * (z.1 - 1)) * z.2, ?_, ?_, ?_⟩
  · show out (0, 0) + (B + 1) * ((0 : ℚ) * (0 - 1)) * 0 = out (0, 0)
    ring
  · show out (1, 0) + (B + 1) * ((1 : ℚ) * (1 - 1)) * 0 = out (1, 0)
    ring
  · intro hall
    have hwithin : withinBall 2 ((0, 0) : ℚ × ℚ) (2, 1) := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num
    obtain ⟨hlo, _⟩ := hall (0, 0) (2, 1) hwithin
    have hxu : (fun z : ℚ × ℚ => out z + (B + 1) * (z.1 * (z.1 - 1)) * z.2) (0, 0)
        - (fun z : ℚ × ℚ => out z + (B + 1) * (z.1 * (z.1 - 1)) * z.2) (2, 1)
        = -5 - 2 * B := by
      show (out (0, 0) + (B + 1) * ((0 : ℚ) * (0 - 1)) * 0)
          - (out (2, 1) + (B + 1) * ((2 : ℚ) * (2 - 1)) * 1) = -5 - 2 * B
      rw [out_origin, xuc_out_at_two_one]
      ring
    rw [hxu] at hlo
    linarith

/-! ## XU-E 允许集/稳定核的不确定性记账（法律内容在 S2） -/

/-- §数学对象：第一个可容许评价（本机件自带的最小版本；S2 的 `allowedSet`/`stableKernel`
    在 `Seams/AdjudicationBridge.lean`，本件**不导入**它，名字也刻意不同）。 -/
def uncertaintyEval₁ : Judgment → Judgment :=
  fun v => if v = Judgment.established then Judgment.established else Judgment.undetermined

/-- §数学对象：第二个可容许评价——与第一个在被问事实上的判断不同。 -/
def uncertaintyEval₂ : Judgment → Judgment :=
  fun v => if v = Judgment.notEstablished then Judgment.established else Judgment.undetermined

/-- §数学对象：允许集 = 各可容许评价在初始裁决 `v₀` 上得到的裁决。 -/
def uncertaintyAllowedList (v₀ : Judgment) : List Judgment :=
  [uncertaintyEval₁ v₀, uncertaintyEval₂ v₀]

/-- §数学对象：允许集成员判据。 -/
def uncertaintyAllowed (v₀ v : Judgment) : Prop := v ∈ uncertaintyAllowedList v₀

/-- §数学对象：稳定核 = 允许集中同时是两个评价不动点的裁决。 -/
def uncertaintyKernel (v₀ v : Judgment) : Prop :=
  uncertaintyAllowed v₀ v ∧ uncertaintyEval₁ v = v ∧ uncertaintyEval₂ v = v

/-- §证：允许集可以有两个不同成员（对"哪一个可容许评价成立"存在真实不确定性）。 -/
theorem uncertainty_allowed_has_two_members :
    uncertaintyAllowed Judgment.established Judgment.established ∧
      uncertaintyAllowed Judgment.established Judgment.undetermined :=
  ⟨List.Mem.head _, List.Mem.tail _ (List.Mem.head _)⟩

/-- §证：允许集不是单点集。 -/
theorem uncertainty_allowed_is_not_a_singleton :
    ¬ ∃! v, uncertaintyAllowed Judgment.established v := by
  rintro ⟨v, _, hv⟩
  obtain ⟨h1, h2⟩ := uncertainty_allowed_has_two_members
  have he : Judgment.established = v := hv Judgment.established h1
  have hu : Judgment.undetermined = v := hv Judgment.undetermined h2
  exact absurd (he.trans hu.symm) (by decide)

/-- §证：稳定核恰好是单点集 `{undetermined}`。 -/
theorem uncertainty_kernel_is_a_singleton :
    ∃! v, uncertaintyKernel Judgment.established v := by
  obtain ⟨_, h2⟩ := uncertainty_allowed_has_two_members
  refine ⟨Judgment.undetermined, ⟨h2, rfl, rfl⟩, ?_⟩
  intro w ⟨hmem, e1, e2⟩
  cases w with
  | established =>
      have hh : uncertaintyEval₂ Judgment.established = Judgment.undetermined := rfl
      rw [hh] at e2
      exact absurd e2 (by decide)
  | notEstablished =>
      exact absurd hmem (by simp [uncertaintyAllowed, uncertaintyAllowedList,
        uncertaintyEval₁, uncertaintyEval₂])
  | undetermined => rfl

/-- §法律语义+§证：**主陈述（记账层类比，不是 S2 的定理）**：允许集非单点
    而稳定核单点，同时成立。法律读法：对"究竟哪一个可容许评价成立"有不确定性
    （允许集有两个成员），并不等于"没有唯一结论"（迭代到不动点的稳定核仍只有一个成员）。
    §证与不证：本定理是数值/结构层面的类比；S2 才是法律内容的归属地，
    本件不导入 `Seams/AdjudicationBridge.lean`，也不声称与它等价。 -/
theorem uncertainty_allowed_non_singleton_with_singleton_kernel :
    (¬ ∃! v, uncertaintyAllowed Judgment.established v) ∧
      ∃! v, uncertaintyKernel Judgment.established v :=
  ⟨uncertainty_allowed_is_not_a_singleton, uncertainty_kernel_is_a_singleton⟩

end JurisLean.Seams.Uncertainty
