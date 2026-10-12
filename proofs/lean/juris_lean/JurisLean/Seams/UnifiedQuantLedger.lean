import Mathlib
import JurisLean.FullMath.Numeric.Quantities
import JurisLean.FullMath.Numeric.Intervals
import JurisLean.Seams.UnifiedQuantities

/-!
# W2-A 前置共享构造：数量账本 ＋ 法律区间（UnifiedQuantLedger）

服务批次 B06（组06 D047–D056 借贷/担保/共同债务）与 B07（组07 D057–D064
侵权/损害），并作为 W2-B N01（单位/来源/舍入解释器）与 N02（区间解释健全）
的同源共享 AST 底座。施工依据：

- `docs/full-math/W2B_CLASSIFICATION.md` §5.3 行 B06/B07：B06 依赖
  “FourteenFamilies＋数量账本构造（与 W2-B N01 同源，先做共享 AST）”；
  B07 依赖“数量/区间构造（与 N01/N02 同源）”。
- `docs/full-math/ALL_134_MATH_CONTRACTS.md` D047–D064 十八行加粗合同句
  （本件构造范围由此反推；本件**不写** demand 合同本身，只交地基）。
- `docs/full-math/MATHEMATICS_SPEC.md` §5（数量/账本：R=C−U 分解、
  `a_{p,o}≥0, Σ_o a_{p,o}≤amount(p)`、同一支付不重复、连带外部/内部
  分层、不把月换 30 天——本件利息用整数天分段，不换算月）、§6
  （区间：表达式归纳包含、乘法四端点、除法零排除——本件区间端点代数
  与 FullMath/Numeric/Intervals 同口径）。

## 复用清单（既有件 → 本件消费方式）

| 既有件 | 复用内容 |
|---|---|
| `FullMath/Numeric/Quantities.lean` | `covered`/`uncovered`/`conservation`（追偿池＝缺额池的互补分解） |
| `FullMath/Numeric/Intervals.lean` | `Iv` 载体与 `add_sound`/`mul_sound`（cause×loss 分担区间的内核） |
| `Seams/UnifiedQuantities.lean` | `waterfall`/`remainingAfter` 及其守恒/T25/非负定理（抵充分配、担保物价款分配、补充责任顺位的同核复用） |
| `Seams/UnifiedNeedlesGapMid.lean` 针 37 | `stepAlloc` min 递推构造风格与 `DebtItem` 分型思想（本件债项身份是其七字段扩展；定理另行重述，不跨文件依赖） |

本件为**补强/扩展**而非重建：分配核直接调 `waterfall`，区间核直接建在
`Iv` 上，残余分解直接调 `covered/uncovered/conservation`；新增部分是
B06/B07 合同句所需的债项身份字段、利息/罚息/复利分段、政策上限、区间
端点代数（非负缩放/取负/相减/相交/包含）、法律区间类型标签、成立门/
份额、按份-连带-补充、损失账本去重、非金钱救济、同一场景见证。

## fail-closed 声明

1. 金额一律 ℚ、天数/标识一律 ℕ，零浮点（仓规 LegalTech 约束 2）。
2. 抵充顺序由调用方供给（D048“按准入顺序”＝列序），本件只给
   `statRank` 一个 [代拟稿] 基线（民法典 561 条费用→利息→主债务结构），
   逾期利息/违约金/本金之间的细序是政策数据，不在本件钦定。
3. 数值见证（利率、债项额、损失额）全部为 [代拟稿] 合成材料，无经验校准。
4. 本件只做共享构造：不含任何 `demand_D0xx` 合同；D047–D064 的
   Acceptance 重绑由 B06/B07 施工包完成。
5. 区间相交为空时返回 `none`（fail-closed），不静默返回空区间或全域。
-/

namespace JurisLean.Seams.UnifiedQuantLedger

open JurisLean.FullMath.Numeric (Iv covered uncovered conservation)
open JurisLean.Seams.UnifiedQuantities (waterfall remainingAfter)

/-! ## 一、分项债项账本（D047/D048/D056 的共享 AST） -/

/-- 债项分型：本金 / 借期利息 / 逾期利息 / 违约金 / 律师费 / 诉讼费 / 保全费。
D049 三组件与 D056 三费用的分项载体。 -/
inductive DebtKind : Type
  | principal | interest | overdueInterest | penalty
  | attorneyFee | courtFee | preservationFee
  deriving DecidableEq

/-- 债项基础（D056：独立债项/基础/受益人/请求状态）。 -/
inductive FeeBasis : Type
  | contractStip | statutory | courtOrder | selfQuoted
  deriving DecidableEq

/-- 请求状态。 -/
inductive ClaimStatus : Type
  | claimed | supported | unsupported
  deriving DecidableEq

/-- 债项身份：标识 + 分型 + 基础 + 受益人 + 请求状态 + 到期金额（全 ℚ）。 -/
structure LedgerItem where
  ident : Nat
  kind : DebtKind
  basis : FeeBasis
  beneficiary : Nat
  status : ClaimStatus
  amount : ℚ

/-- 债项列的金额面。 -/
def liAmounts (items : List LedgerItem) : List ℚ := items.map LedgerItem.amount

/-- 账本余额：未清偿总额。 -/
def outstanding (items : List LedgerItem) : ℚ := (liAmounts items).sum

/-- 单笔支付按准入顺序（列序）逐项 min 递推的分配额
（与 `UnifiedQuantities.waterfall` 同合同；与针 37 `stepAlloc` 同核）。 -/
def allocsOf (p : ℚ) : List LedgerItem → List ℚ
  | [] => []
  | it :: rest => min p it.amount :: allocsOf (p - min p it.amount) rest

/-- 单笔支付后的账本（债项身份保持、金额扣减）。 -/
def afterPay (p : ℚ) : List LedgerItem → List LedgerItem
  | [] => []
  | it :: rest => { it with amount := it.amount - min p it.amount } ::
      afterPay (p - min p it.amount) rest

/-- 分配核与瀑布逐字相等：债项列上的准入顺序分配就是金额面上的瀑布。 -/
theorem allocsOf_eq_waterfall (p : ℚ) : ∀ items : List LedgerItem,
    allocsOf p items = waterfall (liAmounts items) p := by
  intro items
  induction items generalizing p with
  | nil => rfl
  | cons it rest ih =>
      show min p it.amount :: allocsOf (p - min p it.amount) rest
          = waterfall (it.amount :: liAmounts rest) p
      rw [UnifiedQuantities.waterfall_cons, ih]

/-- D048：每笔分配的每一项非负（债项额与付款额非负时）。 -/
theorem allocsOf_mem_nonneg (items : List LedgerItem) (p : ℚ)
    (hnn : ∀ it ∈ items, 0 ≤ it.amount) (hp : 0 ≤ p) :
    ∀ a ∈ allocsOf p items, 0 ≤ a := by
  rw [allocsOf_eq_waterfall]
  refine UnifiedQuantities.waterfall_mem_nonneg _ ?_ p hp
  intro d hd
  obtain ⟨it, hit, rfl⟩ := List.mem_map.mp hd
  exact hnn it hit

/-- D048：每笔分配总额不超过该笔付款（`AllocLegal` 逐付款界的账本形）。 -/
theorem allocsOf_sum_le (items : List LedgerItem) (p : ℚ) (hp : 0 ≤ p) :
    (allocsOf p items).sum ≤ p := by
  rw [allocsOf_eq_waterfall]
  exact UnifiedQuantities.waterfall_sum_le _ p hp

/-- D048：单笔支付守恒——分配和＋余款＝付款额（复用瀑布守恒）。 -/
theorem allocsOf_sum_add_remaining (items : List LedgerItem) (p : ℚ) :
    (allocsOf p items).sum + remainingAfter (liAmounts items) p = p := by
  rw [allocsOf_eq_waterfall]
  exact UnifiedQuantities.waterfall_conservation _ p

/-- 瀑布和＝min 付款 债项和（付款与债项非负）——账本余额钳制定理的核。 -/
theorem waterfall_sum_eq_min : ∀ (L : List ℚ) (p : ℚ), 0 ≤ p →
    (∀ d ∈ L, 0 ≤ d) → (waterfall L p).sum = min p L.sum := by
  intro L
  induction L with
  | nil =>
      intro p hp _
      show (0 : ℚ) = min p 0
      rw [min_eq_right hp]
  | cons d ds ih =>
      intro p hp hnn
      have hds : ∀ x ∈ ds, 0 ≤ x := fun x hx => hnn x (List.mem_cons_of_mem _ hx)
      have hS : 0 ≤ ds.sum := List.sum_nonneg hds
      have hp2 : 0 ≤ p - min p d := sub_nonneg.mpr (min_le_left p d)
      rw [UnifiedQuantities.waterfall_cons, List.sum_cons, ih (p - min p d) hp2 hds]
      rw [List.sum_cons]
      rcases le_total p d with hpd | hdp
      · rw [min_eq_left hpd, sub_self]
        rw [min_eq_left (by linarith : p ≤ d + ds.sum)]
        have h0 : min (0 : ℚ) ds.sum = 0 := min_eq_left (by linarith)
        rw [h0]
        ring
      · rw [min_eq_right hdp]
        rcases le_total (p - d) ds.sum with h | h
        · rw [min_eq_left h, min_eq_left (by linarith : p ≤ d + ds.sum)]
          linarith
        · rw [min_eq_right h, min_eq_right (by linarith : d + ds.sum ≤ p)]

/-- 单笔支付分配总额＝min 付款 账本余额。 -/
theorem allocsOf_sum_eq_min (items : List LedgerItem) (p : ℚ)
    (hp : 0 ≤ p) (hnn : ∀ it ∈ items, 0 ≤ it.amount) :
    (allocsOf p items).sum = min p (outstanding items) := by
  rw [allocsOf_eq_waterfall, outstanding, liAmounts]
  refine waterfall_sum_eq_min _ p hp ?_
  intro d hd
  obtain ⟨it, hit, rfl⟩ := List.mem_map.mp hd
  exact hnn it hit

/-- D048：余额可追踪——支付后债项身份逐笔保持。 -/
theorem afterPay_idents (p : ℚ) : ∀ items : List LedgerItem,
    (afterPay p items).map LedgerItem.ident = items.map LedgerItem.ident := by
  intro items
  induction items generalizing p with
  | nil => rfl
  | cons it rest ih =>
      show LedgerItem.ident { it with amount := it.amount - min p it.amount } ::
          (afterPay (p - min p it.amount) rest).map LedgerItem.ident
          = it.ident :: rest.map LedgerItem.ident
      exact congrArg (fun l => it.ident :: l) (ih (p - min p it.amount))

/-- D048：支付后无负余额（每项分配不超过对应债项）。 -/
theorem afterPay_amounts_nonneg : ∀ (items : List LedgerItem) (p : ℚ),
    ∀ it ∈ afterPay p items, 0 ≤ it.amount := by
  intro items
  induction items with
  | nil => intro p it hit; simp [afterPay] at hit
  | cons it rest ih =>
      intro p it' hit'
      simp only [afterPay] at hit'
      rcases List.mem_cons.1 hit' with hit | hit
      · subst hit
        have hmin := min_le_right p it.amount
        show 0 ≤ it.amount - min p it.amount
        linarith
      · exact ih (p - min p it.amount) it' hit

/-- 支付后余额＝债项和−分配和（逐项望远镜）。 -/
theorem outstanding_afterPay (p : ℚ) : ∀ items : List LedgerItem,
    outstanding (afterPay p items) = outstanding items - (allocsOf p items).sum := by
  intro items
  induction items generalizing p with
  | nil => simp [outstanding, afterPay, allocsOf]
  | cons it rest ih =>
      have ih' := ih (p - min p it.amount)
      show (it.amount - min p it.amount)
            + (liAmounts (afterPay (p - min p it.amount) rest)).sum
          = (it.amount + (liAmounts rest).sum)
            - (min p it.amount + (allocsOf (p - min p it.amount) rest).sum)
      rw [show (liAmounts (afterPay (p - min p it.amount) rest)).sum
            = (liAmounts rest).sum - (allocsOf (p - min p it.amount) rest).sum
            by rw [← outstanding, ← outstanding, ih']]
      ring

/-- 支付后余额＝max(余额−付款, 0)：不压成负债务（溢余另账思想的余额侧）。 -/
theorem outstanding_afterPay_clamp (items : List LedgerItem) (p : ℚ)
    (hnn : ∀ it ∈ items, 0 ≤ it.amount) (hp : 0 ≤ p) :
    outstanding (afterPay p items) = max (outstanding items - p) 0 := by
  rw [outstanding_afterPay, allocsOf_sum_eq_min items p hp hnn]
  rcases le_total p (outstanding items) with h | h
  · rw [min_eq_left h, max_eq_left (by linarith : 0 ≤ outstanding items - p)]
  · rw [min_eq_right h, sub_self, max_eq_right (by linarith : outstanding items - p ≤ 0)]

/-! ### 支付流（多笔支付逐笔按准入顺序抵充） -/

/-- 支付流后的账本。 -/
def afterStream : List ℚ → List LedgerItem → List LedgerItem
  | [], items => items
  | p :: ps, items => afterStream ps (afterPay p items)

/-- 支付流的逐笔分配记录。 -/
def streamAllocs : List ℚ → List LedgerItem → List (List ℚ)
  | [], _ => []
  | p :: ps, items => allocsOf p items :: streamAllocs ps (afterPay p items)

/-- 钳位合成：两次钳位合并为一次（支付流余额定理的算术核；后续付款非负）。 -/
theorem clamp_clamp (x p q : ℚ) (hq : 0 ≤ q) :
    max (max (x - p) 0 - q) 0 = max (x - (p + q)) 0 := by
  rcases le_total (p + q) x with h | h
  · have h1 : max (x - p) 0 = x - p := max_eq_left (by linarith)
    have h2 : max (x - p - q) 0 = x - p - q := max_eq_left (by linarith)
    have h3 : max (x - (p + q)) 0 = x - (p + q) := max_eq_left (by linarith)
    rw [h1, h2, h3]
    linarith
  · rcases le_total p x with hp | hp
    · have h1 : max (x - p) 0 = x - p := max_eq_left (by linarith)
      have h2 : max (x - p - q) 0 = 0 := max_eq_right (by linarith)
      have h3 : max (x - (p + q)) 0 = 0 := max_eq_right (by linarith)
      rw [h1, h2, h3]
    · have h1 : max (x - p) 0 = 0 := max_eq_right (by linarith)
      have h2 : max (0 - q) 0 = 0 := max_eq_right (by linarith)
      have h3 : max (x - (p + q)) 0 = 0 := max_eq_right (by linarith)
      rw [h1, h2, h3]

/-- 非负账项表的总额非负（余额非负引理）。 -/
theorem outstanding_nonneg (items : List LedgerItem)
    (hnn : ∀ it ∈ items, 0 ≤ it.amount) : 0 ≤ outstanding items := by
  rw [outstanding, liAmounts]
  exact List.sum_nonneg (fun d hd => by
    obtain ⟨it, hit, rfl⟩ := List.mem_map.mp hd
    exact hnn it hit)

/-- 支付流端到端：余额＝max(初始余额−总支付, 0)。 -/
theorem outstanding_afterStream (ps : List ℚ) (items : List LedgerItem)
    (hnn : ∀ it ∈ items, 0 ≤ it.amount) (hps : ∀ p ∈ ps, 0 ≤ p) :
    outstanding (afterStream ps items) = max (outstanding items - ps.sum) 0 := by
  induction ps generalizing items with
  | nil =>
      have hO := outstanding_nonneg items hnn
      simp only [afterStream, List.sum_nil, sub_zero]
      exact (max_eq_left hO).symm
  | cons p ps ih =>
      have hp : 0 ≤ p := hps p (by simp)
      have hps' : ∀ q ∈ ps, 0 ≤ q := fun q hq => hps q (List.mem_cons_of_mem _ hq)
      have h1 := outstanding_afterPay_clamp items p hnn hp
      have h2 := ih (afterPay p items) (afterPay_amounts_nonneg items p) hps'
      show outstanding (afterStream ps (afterPay p items))
          = max (outstanding items - (p :: ps).sum) 0
      rw [h2, h1, List.sum_cons]
      exact clamp_clamp (outstanding items) p ps.sum (List.sum_nonneg hps')

/-- D047：清偿判定——余额为零 ⇔ 总支付已覆盖全部到期额。 -/
theorem discharged_iff_paid_covered (items : List LedgerItem)
    (hnn : ∀ it ∈ items, 0 ≤ it.amount) (ps : List ℚ) (hps : ∀ p ∈ ps, 0 ≤ p) :
    outstanding (afterStream ps items) = 0 ↔ outstanding items ≤ ps.sum := by
  rw [outstanding_afterStream ps items hnn hps]
  constructor
  · intro h
    rcases le_total (outstanding items) ps.sum with hle | hle
    · exact hle
    · rw [max_eq_left (by linarith : 0 ≤ outstanding items - ps.sum)] at h
      linarith
  · intro h
    rw [max_eq_right (by linarith : outstanding items - ps.sum ≤ 0)]
/-- D048：支付流每一行都是一笔 `allocsOf`——行行非负、行行不超初始余额。 -/
theorem streamAllocs_rows_legal (ps : List ℚ) (items : List LedgerItem)
    (hnn : ∀ it ∈ items, 0 ≤ it.amount) (hps : ∀ p ∈ ps, 0 ≤ p) :
    ∀ as ∈ streamAllocs ps items, (∀ a ∈ as, 0 ≤ a) ∧ as.sum ≤ outstanding items := by
  induction ps generalizing items with
  | nil => intro as has; simp [streamAllocs] at has
  | cons p ps ih =>
      intro as has
      simp only [streamAllocs] at has
      have hp0 : 0 ≤ p := hps p (by simp)
      rcases List.mem_cons.1 has with rfl | has
      · refine ⟨allocsOf_mem_nonneg items p hnn hp0, ?_⟩
        rw [allocsOf_sum_eq_min items p hp0 hnn]
        exact min_le_right p (outstanding items)
      · have hmono : outstanding (afterPay p items) ≤ outstanding items := by
          rw [outstanding_afterPay]
          have hage := List.sum_nonneg (allocsOf_mem_nonneg items p hnn hp0)
          linarith
        have hrec := ih (afterPay p items) (afterPay_amounts_nonneg items p)
          (fun q hq => hps q (by simp [hq])) as has
        exact ⟨hrec.1, le_trans hrec.2 hmono⟩

/-! ### 支付身份与流合法性（同一支付 ID 不重复） -/

/-- 支付（身份, 金额）。 -/
abbrev Payment := Nat × ℚ

/-- 流合法性：ID 无重复 ＋ 金额非负（同一支付不可重复计入两次）。 -/
def StreamLegal (ps : List Payment) : Prop :=
    (ps.map Prod.fst).Nodup ∧ ∀ q ∈ ps, 0 ≤ q.2

/-- D048 反例：同一支付 ID 出现两次 ⇒ 流非法。 -/
theorem duplicate_payment_rejected : ¬ StreamLegal [(7, 100), (7, 50)] := by
  intro h
  simp only [StreamLegal] at h
  have hmap : (([(7, 100), (7, 50)] : List Payment)).map Prod.fst = [7, 7] := rfl
  rw [hmap] at h
  rcases List.nodup_cons.mp h.1 with ⟨h7, _⟩
  exact h7 (by simp)

/-! ### 借款交付与清偿分立（D047） -/

/-- 借款账本：已实际交付才入账（未交付 ⇒ 空账本，不能凭借条记账）。 -/
def loanLedger (delivered : Bool) (id : Nat) (principal : ℚ) : List LedgerItem :=
  if delivered = true then
    [{ ident := id, kind := DebtKind.principal, basis := FeeBasis.statutory,
       beneficiary := 0, status := ClaimStatus.supported, amount := principal }]
  else []

theorem outstanding_loanLedger (id : Nat) (principal : ℚ) :
    outstanding (loanLedger true id principal) = principal ∧
    outstanding (loanLedger false id principal) = 0 := by
  constructor
  · simp [loanLedger, outstanding, liAmounts]
  · simp [loanLedger, outstanding, liAmounts]

/-- D047 见证：交付 200、还款流 150 ⇒ 余额 50；仅有交付记录（无还款）⇒ 余额 200
——交付事实与清偿事实分别进入责任链。 -/
theorem delivery_repayment_separate_readout :
    outstanding (afterStream [150] (loanLedger true 1 200)) = 50 ∧
    outstanding (loanLedger true 1 200) = 200 := by
  have hnn : ∀ it ∈ loanLedger true 1 200, 0 ≤ it.amount := by
    intro it hit
    simp only [loanLedger] at hit
    split at hit
    · rcases List.mem_cons.1 hit with rfl | hit
      · norm_num
      · cases hit
    · cases hit
  refine ⟨?_, (outstanding_loanLedger 1 200).1⟩
  rw [outstanding_afterStream [150] _ hnn (by norm_num)]
  rw [(outstanding_loanLedger 1 200).1]
  norm_num

/-! ### 费用债项的独立性（D056） -/

/-- 费用基础可支撑性：自身工时报价不自动可支撑。 -/
def feeSupported : FeeBasis → Bool
  | .contractStip => true
  | .statutory => true
  | .courtOrder => true
  | .selfQuoted => false

/-- 请求状态与基础的一致性：supported 状态要求可支撑基础。 -/
def statusConsistent (it : LedgerItem) : Prop :=
    it.status ≠ ClaimStatus.supported ∨ feeSupported it.basis = true

/-- D056 反例：自身工时报价的律师费不得自动进入 supported 状态。 -/
theorem self_quoted_not_supported :
    ¬ statusConsistent
      { ident := 5, kind := DebtKind.attorneyFee, basis := FeeBasis.selfQuoted,
        beneficiary := 2, status := ClaimStatus.supported, amount := 3000 } := by
  intro h
  rcases h with h | h
  · exact h rfl
  · simp [feeSupported] at h

/-- 分组守恒（D053/D056）：按 Bool 谓词二分组的分组和相加＝总额。 -/
theorem sum_filter_partition (f : LedgerItem → Bool) (items : List LedgerItem) :
    ((items.filter f).map LedgerItem.amount).sum
      + ((items.filter (fun it => !f it)).map LedgerItem.amount).sum
      = (items.map LedgerItem.amount).sum := by
  induction items with
  | nil => simp
  | cons it rest ih =>
      by_cases hf : f it = true
      · have h1 : (it :: rest).filter f = it :: rest.filter f := by
          simp [hf]
        have h2 : (it :: rest).filter (fun x => !f x) = rest.filter (fun x => !f x) := by
          simp [hf]
        simp only [h1, h2, List.map_cons, List.sum_cons]
        linarith [ih]
      · have h1 : (it :: rest).filter f = rest.filter f := by
          simp [hf]
        have h2 : (it :: rest).filter (fun x => !f x)
            = it :: rest.filter (fun x => !f x) := by
          simp [hf]
        simp only [h1, h2, List.map_cons, List.sum_cons]
        linarith [ih]

/-- 按受益人分组的求和载体。 -/
def sumWhereBeneficiary (b : Nat) (items : List LedgerItem) : ℚ :=
    ((items.filter (fun it => it.beneficiary == b)).map LedgerItem.amount).sum

/-! ## 二、利息、罚息与复利的分段计算（D049） -/

/-- 计息段：基数、每期利率、整数天数、期分母（365/360 等约定）。
不把月一律换 30 天——期间一律以整数天供给（规格 §5）。 -/
structure InterestSeg where
  base : ℚ
  rate : ℚ
  days : ℕ
  denom : ℕ

/-- 段利息：基数 × 利率 × 天数 / 期分母（段内不舍入，舍入只在具名政策节点）。 -/
def segInterest (s : InterestSeg) : ℚ :=
  s.base * s.rate * s.days / s.denom

theorem segInterest_zero_days (s : InterestSeg) (h : s.days = 0) :
    segInterest s = 0 := by
  simp only [segInterest]
  rw [h]
  simp

theorem segInterest_nonneg (s : InterestSeg) (hb : 0 ≤ s.base) (hr : 0 ≤ s.rate)
    (hd : 0 < s.denom) : 0 ≤ segInterest s := by
  have hD : (0 : ℚ) ≤ s.denom := by exact_mod_cast hd.le
  have h1 : 0 ≤ s.base * s.rate * s.days :=
    mul_nonneg (mul_nonneg hb hr) (Nat.cast_nonneg s.days)
  exact div_nonneg h1 hD

/-- 分段可加：在任意天数处切开，两段利息之和＝原段利息（跨段累计的算术根据）。 -/
theorem seg_split (s : InterestSeg) (d1 d2 : ℕ) (hd : s.denom ≠ 0)
    (h : s.days = d1 + d2) :
    segInterest { s with days := d1 } + segInterest { s with days := d2 }
      = segInterest s := by
  simp only [segInterest]
  rw [h, Nat.cast_add]
  have hD : (s.denom : ℚ) ≠ 0 := by exact_mod_cast hd
  field_simp

/-- 三组件载体：借期利息、逾期利息、违约金分别计算（D049 前半句）。 -/
structure LoanCharges where
  principal : ℚ
  denom : ℕ
  termRate : ℚ
  termDays : ℕ
  overdueRate : ℚ
  overdueDays : ℕ
  penaltyRate : ℚ
  penaltyDays : ℕ

/-- 借期利息组件。 -/
def termInterest (c : LoanCharges) : ℚ :=
  segInterest ⟨c.principal, c.termRate, c.termDays, c.denom⟩

/-- 逾期利息组件。 -/
def overdueInterest (c : LoanCharges) : ℚ :=
  segInterest ⟨c.principal, c.overdueRate, c.overdueDays, c.denom⟩

/-- 违约金组件。 -/
def penaltyCharge (c : LoanCharges) : ℚ :=
  segInterest ⟨c.principal, c.penaltyRate, c.penaltyDays, c.denom⟩

/-- 组件组合总额。 -/
def totalCharges (c : LoanCharges) : ℚ :=
  termInterest c + overdueInterest c + penaltyCharge c

/-- 组件独立：借期利息不随逾期参数变化（分别形成计算组件，非一个混合率）。 -/
theorem termInterest_indep (c : LoanCharges) (r : ℚ) (d : ℕ) :
    termInterest { c with overdueRate := r, overdueDays := d } = termInterest c := rfl

/-- 组合受适用政策限制：总额不超过政策上限（上限数值是政策数据）。 -/
def ChargesWithin (cap : ℚ) (c : LoanCharges) : Prop := totalCharges c ≤ cap

/-- D049 反例见证：本金 100、三组件各 10（相似百分比），全叠加 30 超上限 24
被拒；去掉违约金组件 20 在限内——相似百分比不能默认三项全叠加。 -/
def sampleAll : LoanCharges :=
  ⟨100, 1, 1 / 10, 1, 1 / 10, 1, 1 / 10, 1⟩

def sampleNoPenalty : LoanCharges :=
  ⟨100, 1, 1 / 10, 1, 1 / 10, 1, 1 / 10, 0⟩

theorem stacking_not_default :
    ¬ ChargesWithin 24 sampleAll ∧ ChargesWithin 24 sampleNoPenalty := by
  constructor
  · intro h
    norm_num [ChargesWithin, totalCharges, termInterest, overdueInterest,
      penaltyCharge, segInterest, sampleAll] at h
  · norm_num [ChargesWithin, totalCharges, termInterest, overdueInterest,
      penaltyCharge, segInterest, sampleNoPenalty]

/-- 复利：资本化一步＝基数＋当段利息。 -/
def capitalize (b r : ℚ) (days : ℕ) (D : ℕ) : ℚ :=
  b + segInterest ⟨b, r, days, D⟩

/-- 复利两期分解：两期复利＝两段单利之和＋“利息的利息”
（复利不等于分段单利相加的代数根据）。 -/
theorem compound_two_periods (b r : ℚ) (d1 d2 D : ℕ) :
    capitalize (capitalize b r d1 D) r d2 D
      = capitalize b r d1 D + segInterest ⟨b, r, d2, D⟩
        + segInterest ⟨segInterest ⟨b, r, d1, D⟩, r, d2, D⟩ := by
  simp only [capitalize, segInterest]
  ring

/-- 复利不小于对应两段单利之和（基数、利率非负、分母为正）：差额恰是
利息的利息。 -/
theorem compound_ge_simple (b r : ℚ) (d1 d2 D : ℕ) (hb : 0 ≤ b) (hr : 0 ≤ r)
    (hD : 0 < D) :
    capitalize b r d1 D + segInterest ⟨b, r, d2, D⟩
      ≤ capitalize (capitalize b r d1 D) r d2 D := by
  have hsplit := compound_two_periods b r d1 d2 D
  have hnn : 0 ≤ segInterest ⟨segInterest ⟨b, r, d1, D⟩, r, d2, D⟩ :=
    segInterest_nonneg _ (segInterest_nonneg _ hb hr hD) hr hD
  linarith

/-! ## 三、担保构造：设立事件与优先顺位（D050/D051） -/

/-- 担保类型：保证 / 抵押 / 质押。 -/
inductive SecKind : Type
  | suretyship | mortgage | pledge
  deriving DecidableEq

/-- 设立事件：签署 / 登记 / 交付 / 董事会等内部决议。 -/
inductive SecEvent : Type
  | signed | registered | delivered | boardResolution
  deriving DecidableEq

/-- 各类型的设立要件事件（[代拟稿]：保证—合同；抵押—登记；质押—交付）。 -/
def requiredEvent : SecKind → SecEvent
  | .suretyship => .signed
  | .mortgage => .registered
  | .pledge => .delivered

/-- 担保设立：要件事件在事实集中才设立。 -/
def secEstablished (k : SecKind) (evs : List SecEvent) : Prop :=
    requiredEvent k ∈ evs

/-- D050 反例：签担保文件不自动证明登记完成（抵押）。 -/
theorem signing_not_mortgage_established :
    ¬ secEstablished SecKind.mortgage [SecEvent.signed] := by
  simp [secEstablished, requiredEvent]

/-- D050 反例：签担保文件不自动证明财产已交付（质押）。 -/
theorem signing_not_pledge_established :
    ¬ secEstablished SecKind.pledge [SecEvent.signed] := by
  simp [secEstablished, requiredEvent]

/-- 公司保证路径：决议＋签署两个要件（D051 的决议门）。 -/
def corpSuretyEstablished (evs : List SecEvent) : Prop :=
    SecEvent.boardResolution ∈ evs ∧ SecEvent.signed ∈ evs

/-- D051 反例：仅无决议不得一刀切——同一事件集下公司保证未设立而自然人保证设立，
无效力须走类型化要件而非统一规则。 -/
theorem no_blanket_invalidation :
    ¬ corpSuretyEstablished [SecEvent.signed] ∧
    secEstablished SecKind.suretyship [SecEvent.signed] := by
  constructor
  · intro ⟨hres, _⟩
    simp at hres
  · simp [secEstablished, requiredEvent]

/-- 担保物变现价款按顺位的优先分配：顺位债权列上的瀑布。 -/
def distributeProceeds (claims : List ℚ) (proceeds : ℚ) : List ℚ :=
  waterfall claims proceeds

/-- D050：价款分配守恒——各顺位受偿和＋剩余价款＝变现价款（复用瀑布守恒）。 -/
theorem distribute_conserve (claims : List ℚ) (proceeds : ℚ) :
    (distributeProceeds claims proceeds).sum
      + remainingAfter claims proceeds = proceeds :=
  UnifiedQuantities.waterfall_conservation claims proceeds

/-- D050：后顺位得正 ⇒ 前顺位债权全清（优先顺位的 T25 形，复用瀑布定理）。 -/
theorem distribute_priority (claims : List ℚ) (hnn : ∀ c ∈ claims, 0 ≤ c)
    (proceeds : ℚ) (k : ℕ)
    (hpos : 0 < (List.drop k (distributeProceeds claims proceeds)).sum) :
    List.take k (distributeProceeds claims proceeds) = List.take k claims :=
  UnifiedQuantities.waterfall_t25_prefix claims hnn proceeds k hpos

/-! ## 四、区间构造：端点代数与包含/相交（B07 / N02 同源） -/

namespace QIv

/-- 非负缩放：份额/比例乘区间（端点同乘，序保持）。 -/
def vscale (c : ℚ) (hc : 0 ≤ c) (i : Iv) : Iv where
  lo := c * i.lo
  hi := c * i.hi
  hle := mul_le_mul_of_nonneg_left i.hle hc

/-- 取负。 -/
def vneg (i : Iv) : Iv where
  lo := -i.hi
  hi := -i.lo
  hle := by linarith [i.hle]

/-- 相减（经取负的加法）。 -/
def vsub (i j : Iv) : Iv := Iv.add i (vneg j)

/-- 相交：两端 max(lo)/min(hi)；空交返回 none（fail-closed，不静默给全域）。 -/
def vinter (i j : Iv) : Option Iv :=
  if hcond : max i.lo j.lo ≤ min i.hi j.hi then
    some ⟨max i.lo j.lo, min i.hi j.hi, hcond⟩
  else none

/-- 包含关系：i ⊆ j。 -/
def Cont (i j : Iv) : Prop := j.lo ≤ i.lo ∧ i.hi ≤ j.hi

/-- 端点相等 ⇒ 区间相等（证明域由证明无关性闭合）。 -/
theorem eq_of_lo_hi {i j : Iv} (h1 : i.lo = j.lo) (h2 : i.hi = j.hi) : i = j := by
  rcases i with ⟨⟩
  rcases j with ⟨⟩
  cases h1
  cases h2
  rfl

/-- 缩放健全：x ∈ i ⇒ c·x ∈ c·i。 -/
theorem vscale_sound (c : ℚ) (hc : 0 ≤ c) (i : Iv) (x : ℚ) (hx : Iv.mem x i) :
    Iv.mem (c * x) (vscale c hc i) :=
  ⟨mul_le_mul_of_nonneg_left hx.1 hc, mul_le_mul_of_nonneg_left hx.2 hc⟩

/-- 取负健全。 -/
theorem vneg_sound (i : Iv) (x : ℚ) (hx : Iv.mem x i) :
    Iv.mem (-x) (vneg i) := by
  obtain ⟨h1, h2⟩ := hx
  simp only [vneg, Iv.mem]
  constructor <;> linarith

/-- 相减健全。 -/
theorem vsub_sound (i j : Iv) (x y : ℚ) (hx : Iv.mem x i) (hy : Iv.mem y j) :
    Iv.mem (x - y) (vsub i j) := by
  obtain ⟨h1, h2⟩ := Iv.add_sound i (vneg j) x (-y) hx (vneg_sound j y hy)
  obtain ⟨h3, h4⟩ := hy
  simp only [vsub, Iv.add, vneg, Iv.mem] at h1 h2 ⊢
  constructor <;> linarith

/-- 相交健全（Some 支）。 -/
theorem vinter_sound {i j k : Iv} (h : vinter i j = some k) (x : ℚ)
    (hx : Iv.mem x i) (hy : Iv.mem x j) : Iv.mem x k := by
  rw [vinter] at h
  split at h
  · obtain rfl := Option.some.inj h
    exact ⟨max_le_iff.mpr ⟨hx.1, hy.1⟩, le_min_iff.mpr ⟨hx.2, hy.2⟩⟩
  · exact absurd h (by simp)

/-- 相交为空（None 支）：两区间无公共点。 -/
theorem vinter_none_disjoint {i j : Iv} (h : vinter i j = none) (x : ℚ) :
    ¬ (Iv.mem x i ∧ Iv.mem x j) := by
  intro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  rw [vinter] at h
  split at h
  · exact absurd h (by simp)
  · next hcond =>
    exact hcond (le_trans (max_le_iff.mpr ⟨h1, h3⟩) (le_min_iff.mpr ⟨h2, h4⟩))

/-- 包含自反。 -/
theorem Cont_refl (i : Iv) : Cont i i := ⟨le_refl _, le_refl _⟩

/-- 包含传递。 -/
theorem Cont_trans {i j k : Iv} (h1 : Cont i j) (h2 : Cont j k) : Cont i k :=
  ⟨le_trans h2.1 h1.1, le_trans h1.2 h2.2⟩

/-- 加法对包含单调。 -/
theorem Cont_add {i j k l : Iv} (h1 : Cont i j) (h2 : Cont k l) :
    Cont (Iv.add i k) (Iv.add j l) :=
  ⟨add_le_add h1.1 h2.1, add_le_add h1.2 h2.2⟩

/-- 非负缩放对包含单调。 -/
theorem Cont_scale (c : ℚ) (hc : 0 ≤ c) {i j : Iv} (h : Cont i j) :
    Cont (vscale c hc i) (vscale c hc j) :=
  ⟨mul_le_mul_of_nonneg_left h.1 hc, mul_le_mul_of_nonneg_left h.2 hc⟩

/-- 相交结果包含于两区间（Some 支）。 -/
theorem vinter_contained {i j k : Iv} (h : vinter i j = some k) :
    Cont k i ∧ Cont k j := by
  rw [vinter] at h
  split at h
  · obtain rfl := Option.some.inj h
    exact ⟨⟨le_max_left i.lo j.lo, min_le_left i.hi j.hi⟩,
            ⟨le_max_right i.lo j.lo, min_le_right i.hi j.hi⟩⟩
  · exact absurd h (by simp)

/-- 端点代数——加法结合。 -/
theorem vadd_assoc (i j k : Iv) :
    Iv.add (Iv.add i j) k = Iv.add i (Iv.add j k) := by
  refine eq_of_lo_hi ?_ ?_
  · simp only [Iv.add]; ring
  · simp only [Iv.add]; ring

/-- 端点代数——加法交换。 -/
theorem vadd_comm (i j : Iv) : Iv.add i j = Iv.add j i := by
  refine eq_of_lo_hi ?_ ?_
  · simp only [Iv.add]; ring
  · simp only [Iv.add]; ring

/-- 端点代数——缩放对加法分配。 -/
theorem scale_distrib (c : ℚ) (hc : 0 ≤ c) (i j : Iv) :
    vscale c hc (Iv.add i j) = Iv.add (vscale c hc i) (vscale c hc j) := by
  refine eq_of_lo_hi ?_ ?_
  · simp only [Iv.add, vscale]; ring
  · simp only [Iv.add, vscale]; ring

/-- 端点代数——缩放结合。 -/
theorem scale_assoc (c1 c2 : ℚ) (h1 : 0 ≤ c1) (h2 : 0 ≤ c2) (i : Iv) :
    vscale c1 h1 (vscale c2 h2 i) = vscale (c1 * c2) (mul_nonneg h1 h2) i := by
  refine eq_of_lo_hi ?_ ?_
  · simp only [vscale]; ring
  · simp only [vscale]; ring

end QIv

/-! ### 法律区间类型标签：损失 / 因果度量 / 过错比例 -/

/-- 区间标签：损失（金额量纲）/ 因果度量（无量纲比例）/ 过错比例（[0,1] 比例）。 -/
inductive IvTag : Type
  | loss | cause | fault
  deriving DecidableEq

/-- 带标签区间：跨标签运算在类型层被拒绝（N01 声明单位纪律的区间面）。 -/
structure TIv (t : IvTag) where
  iv : Iv

/-- 同标签加法。 -/
def tAdd {t : IvTag} (a b : TIv t) : TIv t := ⟨Iv.add a.iv b.iv⟩

/-- 非负缩放。 -/
def tScale {t : IvTag} (c : ℚ) (hc : 0 ≤ c) (a : TIv t) : TIv t :=
  ⟨QIv.vscale c hc a.iv⟩

/-- 同标签成员。 -/
def tMem {t : IvTag} (x : ℚ) (a : TIv t) : Prop := Iv.mem x a.iv

/-- 同标签包含。 -/
def tCont {t : IvTag} (a b : TIv t) : Prop := QIv.Cont a.iv b.iv

theorem tAdd_sound {t : IvTag} (a b : TIv t) (x y : ℚ)
    (hx : tMem x a) (hy : tMem y b) : tMem (x + y) (tAdd a b) :=
  Iv.add_sound a.iv b.iv x y hx hy

theorem tScale_sound {t : IvTag} (c : ℚ) (hc : 0 ≤ c) (a : TIv t) (x : ℚ)
    (hx : tMem x a) : tMem (c * x) (tScale c hc a) :=
  QIv.vscale_sound c hc a.iv x hx

/-- 过错比例区间的良构：端点落在 [0,1]。 -/
def FaultOK (a : TIv IvTag.fault) : Prop := 0 ≤ a.iv.lo ∧ a.iv.hi ≤ 1

/-- 良构在 [0,1] 内缩放下保持。 -/
theorem FaultOK_scale (a : TIv IvTag.fault) (ha : FaultOK a) (c : ℚ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) : FaultOK (tScale c hc0 a) := by
  obtain ⟨h1, h2⟩ := ha
  show 0 ≤ c * a.iv.lo ∧ c * a.iv.hi ≤ 1
  refine ⟨mul_nonneg hc0 h1, ?_⟩
  have h3 : 0 ≤ a.iv.hi := le_trans h1 a.iv.hle
  have h4 : c * a.iv.hi ≤ c * 1 := mul_le_mul_of_nonneg_left h2 hc0
  rw [mul_one] at h4
  linarith

/-- 因果度量区间 × 损失区间 → 损失区间（统计因果度量的分担乘积；
内核是 `Iv.mul_sound` 四端点乘法）。 -/
def causeTimesLoss (ci : TIv IvTag.cause) (li : TIv IvTag.loss) :
    TIv IvTag.loss := ⟨Iv.mul ci.iv li.iv⟩

theorem causeTimesLoss_sound (ci : TIv IvTag.cause) (li : TIv IvTag.loss)
    (x y : ℚ) (hx : tMem x ci) (hy : tMem y li) :
    tMem (x * y) (causeTimesLoss ci li) :=
  Iv.mul_sound ci.iv li.iv x y hx hy

/-- 见证区间（[代拟稿] 合成材料）。 -/
def ivLossA : Iv := ⟨100, 200, by norm_num⟩

def ivLossB : Iv := ⟨150, 300, by norm_num⟩

def ivInter : Iv := ⟨150, 200, by norm_num⟩

def ivCause : TIv IvTag.cause := ⟨⟨1 / 3, 2 / 3, by norm_num⟩⟩

def ivLossC : TIv IvTag.loss := ⟨⟨90, 120, by norm_num⟩⟩

/-- 区间端点代数 ℚ 见证：损失 [100,200] 与 [150,300] 相交得 [150,200]；
按份额 1/4 缩放得 [25,50]；因果度量 [1/3,2/3] 乘损失 [90,120] 得 [30,80]。 -/
theorem interval_readout :
    QIv.vinter ivLossA ivLossB = some ivInter ∧
    (QIv.vscale (1 / 4) (by norm_num : 0 ≤ (1 / 4 : ℚ)) ivLossA).lo = 25 ∧
    (QIv.vscale (1 / 4) (by norm_num : 0 ≤ (1 / 4 : ℚ)) ivLossA).hi = 50 ∧
    (causeTimesLoss ivCause ivLossC).iv.lo = 30 ∧
    (causeTimesLoss ivCause ivLossC).iv.hi = 80 := by
  constructor
  · rw [QIv.vinter]
    split
    · refine congrArg some (QIv.eq_of_lo_hi ?_ ?_)
      · show max (100 : ℚ) 150 = 150
        exact max_eq_right (by norm_num)
      · show min (200 : ℚ) 300 = 200
        exact min_eq_left (by norm_num)
    · next hcond =>
      have hmax : max (100 : ℚ) 150 = 150 := max_eq_right (by norm_num)
      have hmin : min (200 : ℚ) 300 = 200 := min_eq_left (by norm_num)
      have hkey : max (100 : ℚ) 150 ≤ min 200 300 := by
        rw [hmax, hmin]
        norm_num
      exact absurd hkey hcond
  · constructor
    · show (1 / 4 : ℚ) * 100 = 25
      norm_num
    · constructor
      · show (1 / 4 : ℚ) * 200 = 50
        norm_num
      · constructor
        · show min (min ((1 / 3 : ℚ) * 90) ((1 / 3 : ℚ) * 120))
              (min ((2 / 3 : ℚ) * 90) ((2 / 3 : ℚ) * 120)) = 30
          have a1 : (1 / 3 : ℚ) * 90 = 30 := by norm_num
          have a2 : (1 / 3 : ℚ) * 120 = 40 := by norm_num
          have a3 : (2 / 3 : ℚ) * 90 = 60 := by norm_num
          have a4 : (2 / 3 : ℚ) * 120 = 80 := by norm_num
          rw [a1, a2, a3, a4,
            min_eq_left (by norm_num : (30 : ℚ) ≤ 40),
            min_eq_left (by norm_num : (60 : ℚ) ≤ 80),
            min_eq_left (by norm_num : (30 : ℚ) ≤ 60)]
        · show max (max ((1 / 3 : ℚ) * 90) ((1 / 3 : ℚ) * 120))
              (max ((2 / 3 : ℚ) * 90) ((2 / 3 : ℚ) * 120)) = 80
          have a1 : (1 / 3 : ℚ) * 90 = 30 := by norm_num
          have a2 : (1 / 3 : ℚ) * 120 = 40 := by norm_num
          have a3 : (2 / 3 : ℚ) * 90 = 60 := by norm_num
          have a4 : (2 / 3 : ℚ) * 120 = 80 := by norm_num
          rw [a1, a2, a3, a4,
            max_eq_right (by norm_num : (30 : ℚ) ≤ 40),
            max_eq_right (by norm_num : (60 : ℚ) ≤ 80),
            max_eq_right (by norm_num : (40 : ℚ) ≤ 80)]

/-! ## 五、成立门与责任份额（D059） -/

/-- 份额配置：成立门（gate）与份额（share）分开选择。 -/
structure Shares (ι : Type) [Fintype ι] where
  gate : ι → Bool
  share : ι → ℚ

/-- 份额合法性：门关 ⇒ 份额为零；份额非负；全员门开 ⇒ 份额和为一。 -/
def LegalShares {ι : Type} [Fintype ι] (s : Shares ι) : Prop :=
    (∀ i, s.gate i = false → s.share i = 0) ∧
    (∀ i, 0 ≤ s.share i) ∧
    ((∀ i, s.gate i = true) → ∑ i, s.share i = 1)

/-- D059：无责任不得被赋正赔偿份额——门关者份额为零。 -/
theorem no_resp_zero_share {ι : Type} [Fintype ι] (s : Shares ι)
    (h : LegalShares s) (i : ι) (hg : s.gate i = false) : s.share i = 0 :=
  h.1 i hg

/-- 反例份额（D059 反例用）。 -/
def badGate : Fin 2 → Bool
  | 0 => false
  | 1 => true

def badShare : Fin 2 → ℚ
  | 0 => 1 / 10
  | 1 => 9 / 10

def badShares : Shares (Fin 2) := ⟨badGate, badShare⟩

/-- D059 反例见证：门关却赋 1/10 份额（用小比例掩盖根本不承担责任的主体）非法。 -/
theorem small_share_mask_rejected : ¬ LegalShares badShares := by
  intro ⟨h1, _, _⟩
  have h0 := h1 0 rfl
  simp only [badShares, badShare] at h0
  norm_num at h0

/-- 合法份额见证：两方各 1/4、3/4，门全开。 -/
def goodGate : Fin 2 → Bool
  | 0 => true
  | 1 => true

def goodShare : Fin 2 → ℚ
  | 0 => 1 / 4
  | 1 => 3 / 4

def goodShares : Shares (Fin 2) := ⟨goodGate, goodShare⟩

theorem goodShares_legal : LegalShares goodShares := by
  refine ⟨fun i hg => ?_, fun i => ?_, fun _ => ?_⟩
  · fin_cases i <;> simp [goodShares, goodGate] at hg
  · fin_cases i <;> simp only [goodShares, goodShare] <;> norm_num
  · rw [Fin.sum_univ_two]
    simp only [goodShares, goodShare]
    norm_num

/-! ## 六、责任方式：按份 / 连带 / 补充（D060/D062） -/

/-- 责任方式。 -/
inductive RespMode : Type
  | several | joint | supplementary
  deriving DecidableEq

/-- 外部给付义务：按份＝内部份额；连带＝全额损失；补充＝主责任人未清部分
（以补充责任额封顶）。 -/
def externalDue (m : RespMode) (loss internalShare primaryDue secondaryDue : ℚ) : ℚ :=
  match m with
  | .several => internalShare
  | .joint => loss
  | .supplementary => min (max (loss - primaryDue) 0) secondaryDue

/-- D062：共享损失基数一致——份额和为一 ⇒ 逐方按份给付之和＝损失基数。 -/
theorem pays_sum_base {ι : Type} [Fintype ι] (base : ℚ) (share : ι → ℚ)
    (h : ∑ i, share i = 1) : ∑ i, share i * base = base := by
  rw [← Finset.sum_mul, h, one_mul]

/-- D060：连带外部偿付总约束——受偿总额不超过损失（两人各负 100 不相加成 200）。 -/
def JointRecoveryOK (loss : ℚ) (recoveries : List ℚ) : Prop := recoveries.sum ≤ loss

/-- D060 反例见证：多个连带债务人全额相加造成超额受偿，违反外部总约束。 -/
theorem joint_double_full_violates : ¬ JointRecoveryOK 100 [100, 100] := by
  intro h
  norm_num [JointRecoveryOK] at h

/-- D062 反例见证：把外部连带金额按内部份额削减，语义不符
（连带方外部义务＝全额损失，不等于内部份额）。 -/
theorem joint_external_not_share_reduced (loss share : ℚ) (_hloss : 0 < loss)
    (hshare : share < loss) :
    externalDue RespMode.joint loss share 0 0 ≠ share := by
  intro h
  simp only [externalDue] at h
  linarith

/-- 内部追偿额：多付部分（对“付款−内部份额”取正部，复用 N01 covered 分解）。 -/
def recourseOf (paid internalShare : ℚ) : ℚ := covered (paid - internalShare)

/-- 内部缺额：少付部分（uncovered 分解）。 -/
def deficitOf (paid internalShare : ℚ) : ℚ := uncovered (paid - internalShare)

/-- D060/D062：追偿池平衡——总付款＝总内部份额时，多付总额＝缺额总额
（内部追偿在金额上闭合，无中生有的追偿不可能）。 -/
theorem recourse_pool_balanced {ι : Type} [Fintype ι]
    (paid internalShare : ι → ℚ)
    (hsum : ∑ i, paid i = ∑ i, internalShare i) :
    ∑ i, recourseOf (paid i) (internalShare i)
      = ∑ i, deficitOf (paid i) (internalShare i) := by
  have hper : ∀ i, covered (paid i - internalShare i)
      - uncovered (paid i - internalShare i) = paid i - internalShare i :=
    fun i => conservation (paid i - internalShare i)
  have hsum1 : ∑ i, (covered (paid i - internalShare i)
      - uncovered (paid i - internalShare i)) = ∑ i, (paid i - internalShare i) :=
    Finset.sum_congr rfl (fun i _ => hper i)
  rw [Finset.sum_sub_distrib] at hsum1
  have hsum2 : ∑ i, (paid i - internalShare i) = 0 := by
    rw [Finset.sum_sub_distrib, hsum, sub_self]
  show ∑ i, covered (paid i - internalShare i)
      = ∑ i, uncovered (paid i - internalShare i)
  linarith

/-- 补充责任：主责任人顺位在前的瀑布——补充方只在未清偿部分内承担。 -/
def suppDistribution (primaryDue secondaryDue loss : ℚ) : List ℚ :=
  waterfall [primaryDue, secondaryDue] loss

/-- 补充责任展开形。 -/
theorem supp_unfold (primaryDue secondaryDue loss : ℚ) :
    suppDistribution primaryDue secondaryDue loss
      = [min loss primaryDue, min (loss - min loss primaryDue) secondaryDue] := rfl

/-- D060：主责任人足额清偿 ⇒ 补充方分配为零（补充责任的顺序语义）。 -/
theorem supp_zero_when_primary_covers (primaryDue secondaryDue loss : ℚ)
    (hcover : loss ≤ primaryDue) (hs : 0 ≤ secondaryDue) :
    suppDistribution primaryDue secondaryDue loss = [loss, 0] := by
  rw [supp_unfold]
  have h1 : min loss primaryDue = loss := min_eq_left hcover
  rw [h1, sub_self, min_eq_left hs]

/-! ## 七、损失账本：去重与聚合（D061） -/

/-- 损失键：（损害事件, 受益人, 项目, 时间）。 -/
abbrev LossKey := Nat × Nat × Nat × Nat

/-- 损失账项：键 + 金额。 -/
structure LossEntry where
  key : LossKey
  amount : ℚ

/-- 损失总额。 -/
def lossTotal (l : List LossEntry) : ℚ := (l.map LossEntry.amount).sum

/-- 去重递推：同键只保留首见（发票额与同一损失的评估额同键只计一次）。 -/
def dedupAux : List LossKey → List LossEntry → List LossEntry
  | _, [] => []
  | seen, e :: es =>
      if e.key ∈ seen then dedupAux seen es
      else e :: dedupAux (e.key :: seen) es

/-- 首见去重。 -/
def dedupFirst (l : List LossEntry) : List LossEntry := dedupAux [] l

/-- 去重规格：结果键无重复，且与已见集不交（归纳强化不变量）。 -/
theorem dedupAux_spec : ∀ (l : List LossEntry) (seen : List LossKey),
    ((dedupAux seen l).map LossEntry.key).Nodup ∧
    (∀ k ∈ (dedupAux seen l).map LossEntry.key, k ∉ seen) := by
  intro l
  induction l with
  | nil => intro _; exact ⟨List.nodup_nil, by intro k hk; cases hk⟩
  | cons e es ih =>
      intro seen
      rw [dedupAux]
      split
      · exact ih seen
      · next hne =>
          have hrec := ih (e.key :: seen)
          refine ⟨List.nodup_cons.mpr ⟨?_, hrec.1⟩, ?_⟩
          · intro hk
            exact hrec.2 e.key hk (by simp)
          · intro k hk
            rcases List.mem_cons.1 hk with hk | hk
            · subst hk; exact hne
            · exact fun hseen => hrec.2 k hk (by simp [hseen])

/-- D061：去重后键无重复。 -/
theorem dedupFirst_keys_nodup (l : List LossEntry) :
    ((dedupFirst l).map LossEntry.key).Nodup :=
  (dedupAux_spec l []).1

/-- D061：去重不虚增——非负账项下去重后总额不超过原总额（无双计）。 -/
theorem dedup_sum_le : ∀ (l : List LossEntry) (seen : List LossKey),
    (∀ e ∈ l, 0 ≤ e.amount) → lossTotal (dedupAux seen l) ≤ lossTotal l := by
  intro l
  induction l with
  | nil => intro seen _; simp [lossTotal, dedupAux]
  | cons e es ih =>
      intro seen hnn
      rw [dedupAux]
      split
      · have htail := ih seen (fun e' he' => hnn e' (List.mem_cons_of_mem _ he'))
        have hpos := hnn e (by simp)
        simp only [lossTotal] at htail ⊢
        simp only [List.map_cons, List.sum_cons]
        linarith
      · have htail := ih (e.key :: seen)
          (fun e' he' => hnn e' (List.mem_cons_of_mem _ he'))
        simp only [lossTotal] at htail ⊢
        simp only [List.map_cons, List.sum_cons]
        exact add_le_add (le_refl _) htail

/-- 键本无重复 ⇒ 去重不改账（恒等）。 -/
theorem dedupFirst_id_of_nodup (l : List LossEntry)
    (hnd : (l.map LossEntry.key).Nodup) : dedupFirst l = l := by
  have hind : ∀ (l : List LossEntry) (seen : List LossKey),
      (l.map LossEntry.key).Nodup →
      (∀ k ∈ l.map LossEntry.key, k ∉ seen) → dedupAux seen l = l := by
    intro l
    induction l with
    | nil => intro seen _ _; rfl
    | cons e es ih =>
        intro seen hnd' hdisj
        have hne : e.key ∉ seen := hdisj e.key (by simp)
        rw [dedupAux, if_neg hne]
        refine congrArg (fun rest => e :: rest) (ih (e.key :: seen) ?_ ?_)
        · exact (List.nodup_cons.mp hnd').2
        · intro k hk hmem
          rcases List.mem_cons.1 hmem with rfl | hmem
          · exact absurd hk (List.nodup_cons.mp hnd').1
          · exact hdisj k (by simp [hk]) hmem
  exact hind l [] hnd (by intro k _ hk; simp at hk)

/-- D061 反例见证：发票额 1000 与同一损失键的评估额 800 双计 1800 被去重防线
压回 1000（首见保留）。 -/
def invoiceEntry : LossEntry := ⟨(1, 2, 3, 4), 1000⟩
def appraisalEntry : LossEntry := ⟨(1, 2, 3, 4), 800⟩

theorem invoice_appraisal_single_count :
    dedupFirst [invoiceEntry, appraisalEntry] = [invoiceEntry] := by
  rw [dedupFirst, dedupAux]
  rfl

theorem invoice_double_count_prevented :
    lossTotal (dedupFirst [invoiceEntry, appraisalEntry]) = 1000 ∧
    lossTotal [invoiceEntry, appraisalEntry] = 1800 := by
  constructor
  · rw [invoice_appraisal_single_count]
    norm_num [lossTotal, invoiceEntry]
  · norm_num [lossTotal, invoiceEntry, appraisalEntry]

/-! ## 八、非金钱救济（D063） -/

/-- 救济载体：金钱赔偿 / 恢复原状 / 停止侵害 / 赔礼道歉。 -/
inductive Remedy : Type
  | moneyAmt (q : ℚ) | restitution | cessation | apology
  deriving DecidableEq

/-- 救济的金额视图：非金钱救济没有金额（Option，不伪装成 0）。 -/
def amountOf : Remedy → Option ℚ
  | .moneyAmt q => some q
  | .restitution => none
  | .cessation => none
  | .apology => none

theorem nonmonetary_no_amount :
    amountOf Remedy.restitution = none ∧
    amountOf Remedy.cessation = none ∧
    amountOf Remedy.apology = none :=
  ⟨rfl, rfl, rfl⟩

/-- 救济清单的金钱总额（只累计金钱项）。 -/
def monetaryTotal : List Remedy → ℚ
  | [] => 0
  | Remedy.moneyAmt q :: rs => q + monetaryTotal rs
  | _ :: rs => monetaryTotal rs

/-- D063 反例见证：两份清单金钱总额相同而非金钱义务不同——金钱投影是盲区，
道歉或禁令不能当赔偿金额零而消失（清单身份仍区分）。 -/
theorem monetary_total_blind_spot :
    monetaryTotal [Remedy.moneyAmt 100, Remedy.apology] = 100 ∧
    monetaryTotal [Remedy.moneyAmt 100] = 100 ∧
    [Remedy.moneyAmt 100, Remedy.apology] ≠ [Remedy.moneyAmt 100] := by
  refine ⟨by norm_num [monetaryTotal], by norm_num [monetaryTotal], ?_⟩
  decide

/-! ## 九、同一场景见证（D064） -/

/-- 场景见证：比例与数值来自同一场景。 -/
structure ScenarioWitness where
  scenId : Nat
  ratios : List ℚ
  values : List ℚ

/-- 裁判总结记录。 -/
structure SummaryRecord where
  scenId : Nat
  ratios : List ℚ
  values : List ℚ
  limit : ℚ

/-- 总结来自同一见证：各字段＝该见证的对应投影。 -/
def FromSameWitness (r : SummaryRecord) (w : ScenarioWitness) : Prop :=
    r.scenId = w.scenId ∧ r.ratios = w.ratios ∧ r.values = w.values

/-- D064：同一见证 ⇒ 总结继承见证的比例守恒。 -/
theorem same_witness_consistent (r : SummaryRecord) (w : ScenarioWitness)
    (h : FromSameWitness r w) (hw : w.ratios.sum = 1) : r.ratios.sum = 1 := by
  rw [h.2.1, hw]

/-- D064 反例见证：两个场景各取一部分拼成的记录不是任何单一场景的总结。 -/
def wA : ScenarioWitness := ⟨1, [1], [100]⟩
def wB : ScenarioWitness := ⟨2, [1], [999]⟩

def mixedRecord : SummaryRecord := ⟨1, [1], [999], 0⟩

theorem cross_scenario_mix_rejected :
    ¬ FromSameWitness mixedRecord wA ∧ ¬ FromSameWitness mixedRecord wB := by
  constructor
  · intro ⟨_, _, hv⟩
    simp [mixedRecord, wA] at hv
  · intro ⟨hid, _, _⟩
    simp [mixedRecord, wB] at hid

/-! ## 十、轻量事实/类型候选件（D055/D057/D058 的共享底座） -/

/-- 事实候选：有来源 / 无来源（fail-closed：无来源不进事实）。 -/
inductive FactCand : Type
  | sourced (id : Nat) | unsourced (id : Nat)
  deriving DecidableEq

/-- 准入判定。 -/
def admittedFact : FactCand → Bool
  | .sourced _ => true
  | .unsourced _ => false

theorem unsourced_not_admitted (id : Nat) :
    ¬ (admittedFact (FactCand.unsourced id) = true) := by simp [admittedFact]

/-- D055 反例载体：从“收入低”到“不可能现金出借”没有任何获准规则
（[代拟稿] 空规则基——模型不虚构负事实）。 -/
inductive CashFact : Type
  | incomeLow | cashImpossible
  deriving DecidableEq

/-- 获准推理规则集（本件为空：收入低不生成任何负事实）。 -/
inductive CashRule : CashFact → CashFact → Prop

theorem income_not_impossible : ¬ CashRule CashFact.incomeLow CashFact.cashImpossible :=
  fun h => nomatch h

/-- 侵权类型候选。 -/
inductive TortKind : Type
  | general | product | employment | medical | environmental | openResidual
  deriving DecidableEq

/-- 类型候选：类型 + 要件是否满足。 -/
structure TortCand where
  kind : TortKind
  elementsMet : Bool

/-- 要件选择：只取要件满足的候选。 -/
def selectByElements (cands : List TortCand) : List TortCand :=
  cands.filter (fun c => c.elementsMet)

/-- 开放残余：要件未满足的候选保留在残余桶，不强塞既有类别。 -/
def toResidual (cands : List TortCand) : List TortCand :=
  cands.filter (fun c => !c.elementsMet)

/-- D057：要件未满足 ⇒ 不入选择、必入残余（双向 filter 刻画）。 -/
theorem unmatched_partition (cands : List TortCand) (c : TortCand)
    (hc : c ∈ cands) (hmet : c.elementsMet = false) :
    c ∈ toResidual cands ∧ c ∉ selectByElements cands := by
  constructor
  · exact List.mem_filter.mpr ⟨hc, by simp [hmet]⟩
  · intro hmem
    have := (List.mem_filter.mp hmem).2
    simp [hmet] at this

/-- D057 反例见证：分类器不认识的新情形保留在残余桶，不返回空账（仍有请求权载体）。 -/
theorem unknown_kept_in_residual :
    (toResidual [⟨TortKind.openResidual, false⟩, ⟨TortKind.general, true⟩]).length = 1 ∧
    (selectByElements [⟨TortKind.openResidual, false⟩, ⟨TortKind.general, true⟩]).length = 1 := by
  constructor <;> simp [toResidual, selectByElements]

/-- D058：法律归责门与统计因果度量分层——归责需要门开且因果度量区间下界为正。 -/
def imputed (legalGate : Bool) (ci : TIv IvTag.cause) : Prop :=
    legalGate = true ∧ 0 < ci.iv.lo

/-- D058 反例见证：统计因果度量再强（[9/10, 1]），法律归责门不开 ⇒ 不归责。 -/
def ivStrongCause : TIv IvTag.cause := ⟨⟨9 / 10, 1, by norm_num⟩⟩

theorem correlation_not_imputation : ¬ imputed false ivStrongCause := by
  intro ⟨h1, _⟩
  exact Bool.noConfusion h1

/-! ## 十一、法定抵充顺位基线与闭式读数（[代拟稿] 合成材料） -/

/-- 债项分型的法定顺位基线（[代拟稿]：按民法典 561 条费用→利息→主债务结构
编码；逾期利息/违约金/本金之间的细序是政策数据，调用方可另供 rank）。 -/
def statRank : DebtKind → ℕ
  | .attorneyFee => 0
  | .courtFee => 0
  | .preservationFee => 0
  | .interest => 1
  | .overdueInterest => 2
  | .penalty => 3
  | .principal => 4

/-- 列按给定 rank 非降序排列（准入顺序的检查谓词）。 -/
def RankOrdered (rank : DebtKind → ℕ) : List LedgerItem → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => rank a.kind ≤ rank b.kind ∧ RankOrdered rank (b :: rest)

/-- B06 消费见证：费用 10 → 利息 100 → 本金 200 的账本在 statRank 下有序。 -/
def demoLedger : List LedgerItem :=
  [ { ident := 1, kind := DebtKind.attorneyFee, basis := FeeBasis.statutory,
      beneficiary := 0, status := ClaimStatus.supported, amount := 10 },
    { ident := 2, kind := DebtKind.interest, basis := FeeBasis.contractStip,
      beneficiary := 0, status := ClaimStatus.supported, amount := 100 },
    { ident := 3, kind := DebtKind.principal, basis := FeeBasis.contractStip,
      beneficiary := 0, status := ClaimStatus.supported, amount := 200 } ]

theorem demoLedger_ordered : RankOrdered statRank demoLedger := by
  show statRank DebtKind.attorneyFee ≤ statRank DebtKind.interest ∧
    (statRank DebtKind.interest ≤ statRank DebtKind.principal ∧ True)
  exact ⟨Nat.le_succ 0, by decide, trivial⟩

theorem demoLedger_nonneg : ∀ it ∈ demoLedger, 0 ≤ it.amount := by
  intro it hit
  simp only [demoLedger, List.mem_cons] at hit
  rcases hit with rfl | rfl | rfl | h
  · norm_num
  · norm_num
  · norm_num
  · cases h

/-- 闭式读数（B06 消费见证）：支付 150 逐项抵充 (10, 100, 40)、余额 160；
支付 350 全额清偿、余额 0。 -/
theorem demoLedger_readout :
    allocsOf 150 demoLedger = [10, 100, 40] ∧
    outstanding (afterPay 150 demoLedger) = 160 ∧
    allocsOf 350 demoLedger = [10, 100, 200] ∧
    outstanding (afterStream [350] demoLedger) = 0 := by
  have hO : outstanding demoLedger = 310 := by
    norm_num [outstanding, liAmounts, demoLedger]
  have h1 : allocsOf 150 demoLedger = [10, 100, 40] := by
    norm_num [allocsOf, demoLedger, min_def]
  have h2 : allocsOf 350 demoLedger = [10, 100, 200] := by
    norm_num [allocsOf, demoLedger, min_def]
  have hsum1 : ([10, 100, 40] : List ℚ).sum = 150 := by
    show (10 : ℚ) + (100 + (40 + 0)) = 150
    norm_num
  have hsum2 : ([10, 100, 200] : List ℚ).sum = 310 := by
    show (10 : ℚ) + (100 + (200 + 0)) = 310
    norm_num
  have h4 : outstanding (afterPay 150 demoLedger) = 160 := by
    rw [outstanding_afterPay, h1, hO, hsum1]
    norm_num
  have h3 : outstanding (afterStream [350] demoLedger) = 0 := by
    rw [outstanding_afterStream [350] demoLedger demoLedger_nonneg
      (by norm_num), hO]
    norm_num
  exact ⟨h1, h4, h2, h3⟩

end JurisLean.Seams.UnifiedQuantLedger
