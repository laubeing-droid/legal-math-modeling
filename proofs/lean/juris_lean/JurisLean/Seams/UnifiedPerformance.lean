import Mathlib.Tactic

/-
Unified performance and sanctions, layer L (plan §9; I.4.9 L09,
fragment for U14–U16, U21).

The dual-track performance face, mirroring the Python event layer's
gross/satisfied split (`tools/unified_math_v2/unified/process.py`):

* Gross track: `grossReceived` records ACTUAL inflows — reality may
  overpay (`gross_can_exceed`); the ledger decomposition never assumes
  payments stay inside the debt.
* Satisfied track: legal offset `satisfiedBy = min gross amount`;
  `outstanding_conservation` : satisfied + outstanding = amount (the
  repo's N01 conservation family, restated for this carrier).
* Excess is a NUMBER relative to a named basis; restitution reads the
  CIVIL CODE 985 / CPL 244 elements instead —
  `same_excess_different_restitution` witnesses amount following the
  basis, not the excess.
* `allocated_not_double_counted`: per-payment allocation totals stay
  within the payment's recorded amount; `double_spend_rejected`
  witnesses the guard catching a double spend.
* Sanctions: `sanctionAmount` reads a named trigger and a DERIVED basis
  (the outstanding, never hand-filled); `sanction_trigger_iff` and
  `sanction_reads_derived_basis`.
* `confirmatory_preserves_ontic_state`: a bookkeeping view never edits
  the ontic inflow list — scope honestly limited to projections that
  create no new substantive object (res judicata / enforcement effects
  are not claimed here).

Scope, honestly: single-obligation fragment over ℚ with list ledgers.
The recognizePerformance InputResolution gate, multi-obligation
waterfalls (layer F owns those), and unit calendars stay on their own
tracks.
-/

namespace JurisLean.Seams.UnifiedPerformance

/-! ## 一、双轨账：实收与依法冲抵 -/

/-- 义务（具名载体，金额非负由 WF 承载）。 -/
structure Obligation where
  /-- 义务号。 -/
  id : ℕ
  /-- 本金。 -/
  amount : ℚ
  deriving DecidableEq

/-- 实际流入账（gross 轨道：只记事实，不截断）。 -/
structure GrossLedger where
  /-- 实际流入列表。 -/
  inflows : List ℚ

/-- 实收总额。 -/
def grossReceived (g : GrossLedger) : ℚ := g.inflows.sum

/-- 依法冲抵（satisfied 轨道）：不超过本金。 -/
def satisfiedBy (obl : Obligation) (g : GrossLedger) : ℚ :=
  min (grossReceived g) obl.amount

/-- 剩余义务。 -/
def outstanding (obl : Obligation) (g : GrossLedger) : ℚ :=
  obl.amount - satisfiedBy obl g

/-- **守恒**：冲抵＋剩余＝本金。 -/
theorem outstanding_conservation (obl : Obligation) (g : GrossLedger) :
    satisfiedBy obl g + outstanding obl g = obl.amount := by
  unfold satisfiedBy outstanding
  rcases le_total (grossReceived g) obl.amount with h | h
  · rw [min_eq_left h]; ring
  · rw [min_eq_right h]; ring

/-- 剩余非负（本金非负时）。 -/
theorem outstanding_nonneg (obl : Obligation) (g : GrossLedger)
    (h : 0 ≤ obl.amount) : 0 ≤ outstanding obl g := by
  unfold outstanding satisfiedBy
  rcases le_total (grossReceived g) obl.amount with h' | h'
  · rw [min_eq_left h']; linarith
  · rw [min_eq_right h']; linarith

/-- **Gross 可超付**：现实可以超额流入——账的分解不假设永不超付。 -/
theorem gross_can_exceed (obl : Obligation) (g : GrossLedger)
    (h : obl.amount < grossReceived g) : satisfiedBy obl g = obl.amount := by
  unfold satisfiedBy
  rw [min_eq_right h.le]

/-- 相对具名基数的超额数值。 -/
def excessOver (obl : Obligation) (g : GrossLedger) : ℚ :=
  max (grossReceived g - obl.amount) 0

/-! ## 二、超额≠返还：返还读民法985/民诉244要件 -/

/-- 返还依据（具名要件载体：无法律根据获利/执行依据撤销）。 -/
inductive RestitutionBasis : Type
  | unjustEnrichment (noLegalBasis : Bool) (enrichment : ℚ) (loss : ℚ)
  | executionRevoked (execId : ℕ) (paidAmount : ℚ)
  deriving DecidableEq

/-- 返还金额：读要件——985 无法律根据时取获利与损失之小；执行撤销取已付。 -/
def restitutionDue (b : RestitutionBasis) : ℚ :=
  match b with
  | .unjustEnrichment true en loss => min en loss
  | .unjustEnrichment false _ _ => 0
  | .executionRevoked _ paid => paid

/-- **同额超额、不同返还**：超额是数值，返还读要件——无法律根据缺失时
    返还 0，要件齐备时取 min(获利,损失)，两案 excess 可以同为 40。 -/
theorem same_excess_different_restitution :
    restitutionDue (.unjustEnrichment false 40 40) = 0
      ∧ restitutionDue (.unjustEnrichment true 40 25) = 25 := by
  norm_num [restitutionDue]

/-! ## 三、抵充不双花 -/

/-- 每笔付款的具名额度。 -/
abbrev PaymentCap := ℕ → ℚ

/-- 抵充合法性：每笔付款的抵充总额不超过其额度
    （同一付款标识不得跨义务重复花用）。 -/
def allocLegal (caps : PaymentCap) (a : List (ℕ × ℚ)) : Prop :=
  ∀ p : ℕ, ((a.filter (fun x => x.1 = p)).map Prod.snd).sum ≤ caps p

/-- **抵充不双花**（逐付款读数）。 -/
theorem allocated_not_double_counted (caps : PaymentCap)
    (a : List (ℕ × ℚ)) (h : allocLegal caps a) (p : ℕ) :
    ((a.filter (fun x => x.1 = p)).map Prod.snd).sum ≤ caps p :=
  h p

/-- **双花被拒**（见证：额度 100 的付款被两次抵充 60）。 -/
theorem double_spend_rejected (caps : PaymentCap) (hcap : caps 7 = 100) :
    ¬ allocLegal caps [(7, 60), (7, 60)] := by
  intro h
  have hsum := h 7
  simp at hsum
  rw [hcap] at hsum
  norm_num at hsum

/-! ## 四、制裁：具名触发＋派生基数 -/

/-- 制裁规则（具名触发位＋倍率，如双倍利息 rate=2）。 -/
structure SanctionRule where
  /-- 触发（来自具名违反条件，非默认）。 -/
  trigger : Bool
  /-- 倍率。 -/
  rate : ℚ
  deriving DecidableEq

/-- 制裁金额：触发时＝倍率×基数，未触发为 0。 -/
def sanctionAmount (r : SanctionRule) (basis : ℚ) : ℚ :=
  if r.trigger then r.rate * basis else 0

/-- **触发 iff**：金额非零当且仅当触发位真、倍率与基数皆非零。 -/
theorem sanction_trigger_iff (r : SanctionRule) (basis : ℚ) :
    sanctionAmount r basis ≠ 0 ↔
      r.trigger = true ∧ r.rate ≠ 0 ∧ basis ≠ 0 := by
  unfold sanctionAmount
  by_cases h : r.trigger = true
  · rw [if_pos h]
    constructor
    · intro hne
      rcases eq_or_ne r.rate 0 with hr | hr
      · rw [hr, zero_mul] at hne; exact absurd rfl hne
      · rcases eq_or_ne basis 0 with hb | hb
        · rw [hb, mul_zero] at hne; exact absurd rfl hne
        · exact ⟨h, hr, hb⟩
    · intro ⟨_, hr, hb⟩
      exact mul_ne_zero hr hb
  · rw [if_neg h]
    constructor
    · intro hne; exact absurd rfl hne
    · intro ⟨h1, _, _⟩; exact absurd h1 h

/-- **制裁读派生基数**：触发时制裁金额恰为倍率×剩余
    （基数从案卷守恒式一路生成，不手填）。 -/
theorem sanction_reads_derived_basis (r : SanctionRule)
    (obl : Obligation) (g : GrossLedger) :
    sanctionAmount r (outstanding obl g)
      = if r.trigger then r.rate * outstanding obl g else 0 := rfl

/-! ## 五、记账投影不造实体 -/

/-- 记账视图（携带同一账本与派生读数）。 -/
def ledgerView (obl : Obligation) (g : GrossLedger) :
    GrossLedger × ℚ := (g, outstanding obl g)

/-- **记账投影保持本体状态**：视图里的账本与原账本逐字相同
    ——只限不新造实体对象的投影；既判力/执行效力/证据状态的变化
    不在本片段冒称。 -/
theorem confirmatory_preserves_ontic_state (obl : Obligation) (g : GrossLedger) :
    (ledgerView obl g).1.inflows = g.inflows := rfl

end JurisLean.Seams.UnifiedPerformance
