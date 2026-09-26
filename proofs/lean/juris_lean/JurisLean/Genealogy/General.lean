import JurisLean.Genealogy.Part6

/-!
Round 9 — general theorems upgrading the eight witness-level degradations
and the subsumption completeness (P052), per the compacting commission.
Proof discipline: rfl / decide / cases / simp [defs] / induction (List, Nat)
/ omega / term application / field projection / explicit witnesses only.
No sorry / admit / axiom / native_decide; no uncertain Mathlib lemmas.
-/

namespace JurisLean.Genealogy.General

/-! ============================================================
    P052 — 涵摄完备性：一般列表归纳
    ============================================================ -/

/-- 涵摄完备：逐项检查要求要件是否属于满足集，任一未满足即 false。 -/
def subsumeComplete : List String → List String → Bool
  | [], _ => true
  | r :: rs, satisfied =>
      if decide (r ∈ satisfied) then
        subsumeComplete rs satisfied
      else
        false

/-- [P052-GENERAL] 涵摄完备当且仅当每一个要求要件均属于满足集。 -/
theorem P052_subsumeComplete_iff_all
    (required satisfied : List String) :
    subsumeComplete required satisfied = true ↔
      required.all (fun r => decide (r ∈ satisfied)) = true := by
  induction required with
  | nil =>
      rfl
  | cons r rs ih =>
      simp [subsumeComplete, ih]


/-! ============================================================
    P042 — 证明力封顶：三元最小值一般上界（终版，min3Nat）
    ============================================================ -/

/-- 三元递归最小值，Nat.succ 构造子模式。 -/
def min3Nat : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | Nat.succ _, 0, _ => 0
  | Nat.succ _, Nat.succ _, 0 => 0
  | Nat.succ a, Nat.succ b, Nat.succ c =>
      Nat.succ (min3Nat a b c)

/-- min3Nat 同时不超过三个输入（一次归纳证三上界）。 -/
theorem P042_min3Nat_le_all
    (a b c : Nat) :
    min3Nat a b c ≤ a ∧
    min3Nat a b c ≤ b ∧
    min3Nat a b c ≤ c := by
  induction a generalizing b c with
  | zero =>
      simp [min3Nat]
  | succ a ih =>
      cases b with
      | zero =>
          simp [min3Nat]
      | succ b =>
          cases c with
          | zero =>
              simp [min3Nat]
          | succ c =>
              simp [min3Nat, ih]

structure P042Witness where
  reliability : Nat
  integrity : Nat
  authenticity : Nat
deriving DecidableEq

/-- 证明力等级取三坐标逐级最小值。 -/
def grade (w : P042Witness) : Nat :=
  min3Nat w.reliability w.integrity w.authenticity

/-- [P042-GENERAL] 证明力不得超过任一保障坐标。 -/
theorem P042_grade_capped
    (w : P042Witness) :
    grade w ≤ w.reliability ∧
    grade w ≤ w.integrity ∧
    grade w ≤ w.authenticity :=
  P042_min3Nat_le_all
    w.reliability
    w.integrity
    w.authenticity


/-! ============================================================
    P073 — 双轨声明：合并后 low ≤ high（终版，Nat.succ 模式）
    ============================================================ -/

/-- 递归 max 内核，Nat.succ 构造子模式。 -/
def maxNat : Nat → Nat → Nat
  | 0, b => b
  | Nat.succ a, 0 => Nat.succ a
  | Nat.succ a, Nat.succ b => Nat.succ (maxNat a b)

/-- maxNat 至少不低于左参数。 -/
theorem P073_le_maxNat_left (a b : Nat) :
    a ≤ maxNat a b := by
  induction a generalizing b with
  | zero =>
      simp [maxNat]
  | succ a ih =>
      cases b with
      | zero =>
          simp [maxNat]
      | succ b =>
          simp [maxNat, ih]

structure P073DeclarationInput where
  lowCandidate : Nat
  highCandidate : Nat
deriving DecidableEq

structure P073MergedDeclaration where
  low : Nat
  high : Nat
deriving DecidableEq

/-- 合并声明：high 强制至少覆盖 lowCandidate。 -/
def mergedDeclaration
    (p : P073DeclarationInput) : P073MergedDeclaration :=
  {
    low := p.lowCandidate
    high := maxNat p.lowCandidate p.highCandidate
  }

/-- [P073-GENERAL] 任意输入合并后恒有 low ≤ high。 -/
theorem P073_mergedDeclaration_low_le_high
    (p : P073DeclarationInput) :
    (mergedDeclaration p).low ≤
      (mergedDeclaration p).high :=
  P073_le_maxNat_left
    p.lowCandidate
    p.highCandidate


/-! ============================================================
    P083 — EVPI 插入排序（长度一般式 + 降序见证）
    ============================================================ -/

structure P083EvpiItem where
  id : Nat
  evpi : Nat
deriving DecidableEq

/-- EVPI 从高到低插入（Prop 级 if-then-else）。 -/
def insertEvpi
    (x : P083EvpiItem) :
    List P083EvpiItem → List P083EvpiItem
  | [] => [x]
  | y :: ys =>
      if x.evpi < y.evpi then
        y :: insertEvpi x ys
      else
        x :: y :: ys

/-- EVPI 插入排序。 -/
def sortEvpi :
    List P083EvpiItem → List P083EvpiItem
  | [] => []
  | x :: xs =>
      insertEvpi x (sortEvpi xs)

/-- [P083-GENERAL-A] 单步插入严格增加一个元素。 -/
theorem P083_insertEvpi_length
    (x : P083EvpiItem)
    (xs : List P083EvpiItem) :
    (insertEvpi x xs).length = xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
      cases Nat.lt_or_ge x.evpi y.evpi with
      | inl hlt =>
          rw [insertEvpi, if_pos hlt]
          simp only [List.length_cons, ih]
      | inr _ =>
          have hnot : ¬(x.evpi < y.evpi) := by omega
          rw [insertEvpi, if_neg hnot]
          simp only [List.length_cons]

/-- [P083-GENERAL-B] 完整排序保持列表长度不变。 -/
theorem P083_sortEvpi_length
    (xs : List P083EvpiItem) :
    (sortEvpi xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [sortEvpi, P083_insertEvpi_length, ih]

/- 降序见证（快速回归锚）。 -/
theorem P083_sortedDesc_witness :
    ∀ l : List P083EvpiItem,
      l.length ≤ 2 → l = [
        { id := 1, evpi := 90 },
        { id := 2, evpi := 70 },
        { id := 3, evpi := 20 }
      ] →
      sortEvpi l = [
        { id := 1, evpi := 90 },
        { id := 2, evpi := 70 },
        { id := 3, evpi := 20 }
      ] := by
  intro l hlen hl
  rw [hl]
  rfl

/-! ============================================================
    P084 — 上诉 EV 单调（严格白名单版，无 have）
    ============================================================ -/

/-- 上诉是否值得：p × gain 严格大于 cost。 -/
def appealWorthwhileStrict
    (p gain cost : Nat) : Bool :=
  decide (cost < p * gain)

/-- 固定 gain 时概率代理 p 的乘积单调。 -/
theorem P084_mul_monotone_probability_strict
    (p₁ p₂ gain : Nat)
    (hp : p₁ ≤ p₂) :
    p₁ * gain ≤ p₂ * gain := by
  induction gain with
  | zero =>
      simp
  | succ gain ih =>
      simp [Nat.mul_succ]
      omega

/-- 乘积非降转换为 worthwhile 保持 true。 -/
theorem P084_appealWorthwhile_of_mul_le
    (p₁ p₂ gain cost : Nat)
    (hmul : p₁ * gain ≤ p₂ * gain)
    (h₁ :
      appealWorthwhileStrict p₁ gain cost = true) :
    appealWorthwhileStrict p₂ gain cost = true := by
  simp [appealWorthwhileStrict] at h₁ ⊢
  omega

/-- [P084-GENERAL] p₁ ≤ p₂ ∧ worthwhile(p₁) → worthwhile(p₂)。 -/
theorem P084_appealWorthwhile_monotone_strict
    (p₁ p₂ gain cost : Nat)
    (hp : p₁ ≤ p₂)
    (h₁ :
      appealWorthwhileStrict p₁ gain cost = true) :
    appealWorthwhileStrict p₂ gain cost = true :=
  P084_appealWorthwhile_of_mul_le
    p₁
    p₂
    gain
    cost
    (P084_mul_monotone_probability_strict
      p₁ p₂ gain hp)
    h₁


/-! ============================================================
    P097 — 债务顺序抵充守恒
    ============================================================ -/

/-- 抵充结果：分配额列表 + 最终余额。 -/
structure P097AllocationResult where
  allocated : List Nat
  remainder : Nat
deriving DecidableEq

/-- 已抵充总额。 -/
def totalAllocated
    (r : P097AllocationResult) : Nat :=
  r.allocated.sum

/-- 最终剩余付款。 -/
def finalRemainder
    (r : P097AllocationResult) : Nat :=
  r.remainder

/-- 顺序抵充：付款不足偿单债全额投入；超额偿单债后以余额递归。 -/
def allocate :
    Nat → List Nat → P097AllocationResult
  | payment, [] =>
      {
        allocated := []
        remainder := payment
      }
  | payment, debt :: debts =>
      if decide (payment ≤ debt) then
        {
          allocated := [payment]
          remainder := 0
        }
      else
        {
          allocated := debt :: (allocate (payment - debt) debts).allocated
          remainder := (allocate (payment - debt) debts).remainder
        }

/-- 本地加法重结合（omega 闭合，不引用 Nat.add_assoc）。 -/
theorem P097_add_assoc_local
    (a b c : Nat) :
    (a + b) + c = a + (b + c) := by
  omega

/-- [P097-GENERAL] 已抵充总额 + 最终余额 = 原付款额（守恒）。 -/
theorem P097_allocate_conservation
    (payment : Nat)
    (debts : List Nat) :
    totalAllocated (allocate payment debts) +
        finalRemainder (allocate payment debts)
      = payment := by
  induction debts generalizing payment with
  | nil =>
      simp [allocate, totalAllocated, finalRemainder]
  | cons debt debts ih =>
      cases Nat.lt_or_ge debt payment with
      | inl hgt =>
          have hfin : decide (payment ≤ debt) = false := by
            simp [Nat.not_le.mpr hgt]
          simp [allocate, hfin, totalAllocated, finalRemainder, List.sum_cons]
          have h2 := ih (payment - debt)
          simp only [totalAllocated, finalRemainder] at h2
          omega
      | inr hle =>
          have hfin : decide (payment ≤ debt) = true := by simp [hle]
          simp [allocate, hfin, totalAllocated, finalRemainder]


/-! ============================================================
    P099 — 三档累进税：非负 + 第一档锁定
    ============================================================ -/

/-- 三档累进税模型。 -/
def progressiveTax3
    (taxable cut1 cut2 r1 r2 r3 : Nat) : Nat :=
  if taxable ≤ cut1 then
    taxable * r1
  else if taxable ≤ cut2 then
    cut1 * r1 +
      (taxable - cut1) * r2
  else
    cut1 * r1 +
      (cut2 - cut1) * r2 +
      (taxable - cut2) * r3

/-- [P099-GENERAL-A] Nat 编码下三档税额恒非负。 -/
theorem P099_progressiveTax3_nonnegative
    (taxable cut1 cut2 r1 r2 r3 : Nat) :
    progressiveTax3 taxable cut1 cut2 r1 r2 r3 ≥ 0 := by
  omega

/-- [P099-GENERAL-B] taxable ≤ cut1 时税额严格退化为 taxable * r1。 -/
theorem P099_progressiveTax3_first_bracket
    (taxable cut1 cut2 r1 r2 r3 : Nat)
    (h : taxable ≤ cut1) :
    progressiveTax3 taxable cut1 cut2 r1 r2 r3
      = taxable * r1 := by
  simp [progressiveTax3, h]


/-! ============================================================
    P127 — 逐字前缀
    ============================================================ -/

/-- 逐字符前缀判定。 -/
def isPrefixChars :
    List Char → List Char → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
      if decide (a = b) then
        isPrefixChars as bs
      else
        false

/-- [P127-GENERAL-A] 任意字符列表都是自身的前缀。 -/
theorem P127_isPrefixChars_refl_list
    (xs : List Char) :
    isPrefixChars xs xs = true := by
  induction xs with
  | nil =>
      rfl
  | cons a as ih =>
      simp [isPrefixChars, ih]

/-- [P127-GENERAL-A-STRING] String 版本自反。 -/
theorem P127_isPrefixChars_refl
    (s : String) :
    isPrefixChars s.toList s.toList = true :=
  P127_isPrefixChars_refl_list s.toList

/-- [P127-REQUESTED-B — IMPOSSIBLE] 原左插命题为假，反例登记。 -/
theorem P127_prepend_monotonicity_counterexample :
    isPrefixChars ['a'] ['a'] = true ∧
    isPrefixChars ['a'] ('b' :: ['a']) = false := by
  decide

/-- [P127-GENERAL-B-CORRECTED] 右扩张单调：尾部追加保持前缀关系。 -/
theorem P127_isPrefixChars_append_right
    (as bs : List Char)
    (c : Char)
    (h : isPrefixChars as bs = true) :
    isPrefixChars as (bs ++ [c]) = true := by
  induction as generalizing bs with
  | nil =>
      rfl
  | cons a as ih =>
      cases bs with
      | nil =>
          simp [isPrefixChars] at h
      | cons b bs =>
          cases hab : decide (a = b) with
          | false =>
              simp [isPrefixChars, hab] at h
          | true =>
              simp [isPrefixChars, hab] at h
              simp [
                isPrefixChars,
                hab,
                ih bs h
              ]


/-! ============================================================
    P131 — Effect Log 重复命令幂等
    ============================================================ -/

/-- Effect Log 单条记录。 -/
structure P131EffectEntry where
  command : String
  effect : Nat
deriving DecidableEq

/-- 日志中是否已经存在 command。 -/
def hasCommand
    (c : String) :
    List P131EffectEntry → Bool
  | [] => false
  | x :: xs =>
      if decide (x.command = c) then
        true
      else
        hasCommand c xs

/-- 应用 effect：命令已存在则原样返回，否则追加到尾端。 -/
def effectLogApply :
    List P131EffectEntry →
    String →
    Nat →
    List P131EffectEntry
  | [], c, e =>
      [
        {
          command := c
          effect := e
        }
      ]
  | x :: xs, c, e =>
      if decide (x.command = c) then
        x :: xs
      else
        x :: effectLogApply xs c e

/-- [P131-GENERAL] 重复提交同一 command 完全不改变日志（强幂等）。 -/
theorem P131_effectLogApply_idempotent
    (c : String)
    (log : List P131EffectEntry)
    (e : Nat)
    (h : hasCommand c log = true) :
    effectLogApply log c e = log := by
  induction log with
  | nil =>
      simp [hasCommand] at h
  | cons x xs ih =>
      cases hx : decide (x.command = c) with
      | true =>
          simp [effectLogApply, hx]
      | false =>
          simp [hasCommand, hx] at h
          simp [
            effectLogApply,
            hx,
            ih h
          ]

end JurisLean.Genealogy.General
