import JurisLean.Candidates.W6JudgmentCashAudit20261104
import JurisLean.Candidates.Final20261021.Acceptance

/-!
新增义务：只补冻结09.8 L204的rPrime/q/实际事件连接、L206的同对象分项账、
L208的有限条件合成。既有无现金、有限现金守恒和连续轨迹不变量直接复用。
SOURCE_PENDING_CI / PARTIAL_09_8。
Extractor是原题给定有效提取在本有限接口中的完整PaymentRequest输出；本稿不证明
现实来源真实或通用解析器正确。decision是Θ对该输入已明确的返还规则输出；none不准入，
不在这里裁决规范冲突。数学生产者与现有RestPay的接线边界分开证明。
-/
namespace JurisLean.Candidates.RestitutionFiniteClosureAudit20261104

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.W6JudgmentCashAudit20261104
open scoped BigOperators

/-- Θ明示的本次返还规则；不从现金守恒推导它。 -/
structure RefundRule where
  original : PaymentRequest
  payment : PaymentRequest
  claim : Ledger.RestClaimWitness
  eligibilityEvidence : SourceRef
  credit : ℚ
  deriving DecidableEq

abbrev Extractor := SourceRef → PaymentId → Option PaymentRequest

/-- 原题条件都是输入/前态条件；没有最终守恒或最终后态作为字段。 -/
structure Ready (g : Gamma) (extract : Extractor) (s : Ledger.State)
    (decision : Option RefundRule) (r : RefundRule) : Prop where
  authorized : decision = some r
  originalExtracted : extract r.original.payload.source r.original.key = some r.original
  refundExtracted : extract r.payment.payload.source r.payment.key = some r.payment
  originalIdentified : r.original.interpretedPayment = some r.original.key
  refundIdentified : r.payment.interpretedPayment = some r.payment.key
  originalCase : r.original.payload.caseId = g.caseId
  refundCase : r.payment.payload.caseId = g.caseId
  refundRevision : r.payment.payload.caseRevision = g.caseRevision
  refundNorm : r.payment.payload.normVersion = g.normVersion
  refundDate : r.payment.payload.factDate = g.lawDate
  procedureGate : r.payment.applicable = .yes
  originalRelation : r.original.payload.relation = s.debt.relation
  originalCash : cashFromPayload r.original.payload ∈ s.cash
  newPayment : r.payment.key ≠ r.original.key
  unusedPayment : r.payment.key ∉ s.used
  newRelation : r.claim.relation ≠ s.debt.relation
  unusedRelation : r.claim.relation ∉ s.formations
  refundRelation : r.payment.payload.relation = r.claim.relation
  refundPayer : r.payment.payload.payer = r.claim.obligor
  refundPayee : r.payment.payload.payee = r.claim.creditor
  refundUnit : r.payment.payload.amount.tag = r.claim.amount.tag
  originalUnit : r.original.payload.amount.tag = r.payment.payload.amount.tag
  ledgerUnit : s.debt.amount.tag = r.payment.payload.amount.tag
  nonnegClaim : 0 ≤ r.claim.amount.value
  nonnegAmount : 0 ≤ r.payment.payload.amount.value
  nonnegCredit : 0 ≤ r.credit
  creditBound : r.credit ≤ min r.payment.payload.amount.value r.claim.amount.value
  freshCash : (s.cash ++ s.refundCash).any
    (fun e => e.id == r.payment.payload.cashId) = false

def activeDebt (r : RefundRule) (eligible : Bool) : Ledger.RestDebt :=
  ⟨r.claim.relation, r.claim.obligor, r.claim.creditor, r.claim.amount,
    eligible, r.claim.evidence, if eligible then some r.eligibilityEvidence else none⟩

def claimPost (s : Ledger.State) (r : RefundRule) : Ledger.State :=
  { s with
    rest := some (activeDebt r false)
    formations := s.formations ++ [r.claim.relation] }

def eligiblePost (s : Ledger.State) (r : RefundRule) : Ledger.State :=
  { claimPost s r with rest := some (activeDebt r true) }

/-- 由Θ给定k的有限效果；原paid/allocated/surplus和旧cash保留为历史分项。 -/
def refundPost (s : Ledger.State) (r : RefundRule) : Ledger.State :=
  { eligiblePost s r with
    rest := some { activeDebt r true with
      amount := { r.claim.amount with value := r.claim.amount.value - r.credit } },
    refundCash := s.refundCash ++ [cashFromPayload r.payment.payload] }

/-- q是PaymentId；event身份保留在完整payload.cashId，二者不按数值混同。 -/
structure RefundReceipt where
  originalPayment : PaymentId
  q : PaymentId
  payload : PaymentPayload
  normEvidence : SourceRef
  eligibilityEvidence : SourceRef
  applied : ℚ
  deriving DecidableEq

def refundReceipt (r : RefundRule) : RefundReceipt :=
  ⟨r.original.key, r.payment.key, r.payment.payload,
    r.claim.evidence, r.eligibilityEvidence, r.credit⟩

def effectPair (s : Ledger.State) (r : RefundRule) : Ledger.State × RefundReceipt :=
  (refundPost s r, refundReceipt r)

noncomputable def checkedEffect (g : Gamma) (extract : Extractor) (s : Ledger.State)
    (decision : Option RefundRule) (r : RefundRule) : Option (Ledger.State × RefundReceipt) := by
  classical
  exact if Ready g extract s decision r then some (effectPair s r) else none

/-- 新返还债额是独立Option投影；不把没有该关系当作债量0。 -/
def restitutionQuantity (s : Ledger.State) (relation : RelationId) : Option ℚ :=
  match s.rest with
  | none => none
  | some r => if r.relation = relation then some r.amount.value else none

def refundTotal (s : Ledger.State) : ℚ :=
  (s.refundCash.map (fun e => e.amount.value)).sum

def Stages (s : Ledger.State) (r : RefundRule) : Prop :=
  Ledger.RestClaim s r.claim = .known (claimPost s r) ∧
  Ledger.ExecEligible (claimPost s r) r.claim.relation r.eligibilityEvidence =
    .known (eligiblePost s r) ∧
  (claimPost s r).cash = s.cash ∧ (claimPost s r).refundCash = s.refundCash ∧
  (eligiblePost s r).cash = s.cash ∧ (eligiblePost s r).refundCash = s.refundCash

theorem first_two_stages_no_cash
    {g : Gamma} {extract : Extractor} {s : Ledger.State}
    {decision : Option RefundRule} {r : RefundRule} (h : Ready g extract s decision r) :
    Stages s r := by
  have hclaim : Ledger.RestClaim s r.claim = .known (claimPost s r) := by
    simp [Ledger.RestClaim, claimPost, activeDebt,
      h.newRelation, h.unusedRelation, not_lt.mpr h.nonnegClaim]
  have heligible : Ledger.ExecEligible (claimPost s r) r.claim.relation
      r.eligibilityEvidence = .known (eligiblePost s r) := by
    simp [Ledger.ExecEligible, claimPost, eligiblePost, activeDebt]
  have hc := Ledger.rest_claim_no_cash s r.claim (claimPost s r) hclaim
  have he := Ledger.rest_eligibility_no_cash (claimPost s r) r.claim.relation
    r.eligibilityEvidence (eligiblePost s r) heligible
  exact ⟨hclaim, heligible, hc.1, hc.2, he.1.trans hc.1, he.2.1.trans hc.2⟩

theorem checkedEffect_of_ready
    {g : Gamma} {extract : Extractor} {s : Ledger.State}
    {decision : Option RefundRule} {r : RefundRule} (h : Ready g extract s decision r) :
    checkedEffect g extract s decision r = some (effectPair s r) := by
  classical
  simp [checkedEffect, h]

theorem q_receipt_is_actual_event_and_history
    {g : Gamma} {extract : Extractor} {s : Ledger.State}
    {decision : Option RefundRule} {r : RefundRule} (h : Ready g extract s decision r) :
    (effectPair s r).2.q = r.payment.key ∧
    (effectPair s r).2.originalPayment = r.original.key ∧
    (effectPair s r).2.q ≠ (effectPair s r).2.originalPayment ∧
    (effectPair s r).2.payload = r.payment.payload ∧
    (effectPair s r).2.normEvidence = r.claim.evidence ∧
    (effectPair s r).2.eligibilityEvidence = r.eligibilityEvidence ∧
    (effectPair s r).2.payload.relation = r.claim.relation ∧
    (effectPair s r).1.refundCash = s.refundCash ++
      [cashFromPayload (effectPair s r).2.payload] ∧
    (effectPair s r).1.cash = s.cash ∧
    (effectPair s r).1.debt = s.debt ∧
    (effectPair s r).1.formations = s.formations ++ [r.claim.relation] ∧
    Ledger.quantity (effectPair s r).1 s.debt.relation =
      Ledger.quantity s s.debt.relation ∧
    r.original.interpretedPayment = some r.original.key ∧
    cashFromPayload r.original.payload ∈ s.cash := by
  refine ⟨rfl, rfl, h.newPayment, rfl, rfl, rfl, h.refundRelation,
    rfl, rfl, rfl, rfl, ?_, h.originalIdentified, h.originalCash⟩
  have hne : s.debt.relation ≠ r.claim.relation := Ne.symm h.newRelation
  simp [effectPair, refundPost, eligiblePost, claimPost, Ledger.quantity, hne]

def QuantityConclusion (s : Ledger.State) (r : RefundRule) : Prop :=
  Ledger.Conserves (refundPost s r) ∧ Ledger.CashConsistent (refundPost s r) ∧
  s.initialDebt + s.newDebt + s.accrual =
    (refundPost s r).allocated + Ledger.balance (refundPost s r) +
      (refundPost s r).writtenOff ∧
  (refundPost s r).paid = s.paid ∧
  (refundPost s r).paid = (refundPost s r).allocated + (refundPost s r).surplus ∧
  restitutionQuantity (refundPost s r) r.claim.relation =
    some (r.claim.amount.value - r.credit) ∧
  0 ≤ r.claim.amount.value - r.credit ∧
  0 ≤ r.payment.payload.amount.value - r.credit ∧
  r.claim.amount.value = r.credit + (r.claim.amount.value - r.credit) ∧
  r.payment.payload.amount.value = r.credit + (r.payment.payload.amount.value - r.credit) ∧
  (refundPost s r).cash = s.cash ∧
  refundTotal (refundPost s r) = refundTotal s + r.payment.payload.amount.value ∧
  (refundPost s r).rest = some { activeDebt r true with
    amount := { r.claim.amount with value := r.claim.amount.value - r.credit } }

theorem separated_quantity_and_cash_components
    {g : Gamma} {extract : Extractor} {s : Ledger.State}
    {decision : Option RefundRule} {r : RefundRule} (h : Ready g extract s decision r)
    (hs : Ledger.Conserves s) (hc : Ledger.CashConsistent s) :
    QuantityConclusion s r := by
  have hqty := hs
  rcases hqty with ⟨_, _, _, _, _, _, _, hquantity, hpaid⟩
  have hk : r.credit ≤ r.claim.amount.value :=
    le_trans h.creditBound (min_le_right _ _)
  have hka : r.credit ≤ r.payment.payload.amount.value :=
    le_trans h.creditBound (min_le_left _ _)
  unfold QuantityConclusion
  refine ⟨hs, hc, ?_, rfl, hpaid, ?_, ?_, ?_, ?_, ?_, rfl, ?_, rfl⟩
  · change s.initialDebt + s.newDebt + s.accrual =
      s.allocated + Ledger.balance s + s.writtenOff
    linarith
  · simp [restitutionQuantity, refundPost, activeDebt]
  · linarith
  · linarith
  · ring
  · ring
  · simp [refundTotal, refundPost, cashFromPayload, List.map_append, List.sum_append]

/-- 每个索引必须投影到原CashEvent的实际付款/收款主体；完整性在定理中连接。 -/
structure BookedCash (A : Type) (party : A → PartyId) where
  event : CashEvent
  payerAccount : A
  payeeAccount : A
  payerMatches : party payerAccount = event.payer
  payeeMatches : party payeeAccount = event.payee

def delta {A : Type} [DecidableEq A] {party : A → PartyId}
    (e : BookedCash A party) (a : A) : ℚ :=
  (if a = e.payeeAccount then e.event.amount.value else 0) -
    (if a = e.payerAccount then e.event.amount.value else 0)

theorem delta_balanced {A : Type} [Fintype A] [DecidableEq A]
    {party : A → PartyId} (e : BookedCash A party) : ∑ a, delta e a = 0 := by
  simp [delta, Finset.sum_sub_distrib]

theorem coordinates_are_actual_event {A : Type} [DecidableEq A]
    {party : A → PartyId} (hinj : Function.Injective party)
    (e : BookedCash A party) (a : A) :
    delta e a =
      (if party a = e.event.payee then e.event.amount.value else 0) -
      (if party a = e.event.payer then e.event.amount.value else 0) := by
  have hto : party a = e.event.payee ↔ a = e.payeeAccount := by
    constructor
    · intro h
      exact hinj (h.trans e.payeeMatches.symm)
    · intro h
      subst a
      exact e.payeeMatches
  have hfrom : party a = e.event.payer ↔ a = e.payerAccount := by
    constructor
    · intro h
      exact hinj (h.trans e.payerMatches.symm)
    · intro h
      subst a
      exact e.payerMatches
  simp only [delta, hto, hfrom]

theorem actual_closed_account_conservation
    {A : Type} [Fintype A] [DecidableEq A] {party : A → PartyId}
    (hinj : Function.Injective party) (s : Ledger.State) (r : RefundRule)
    (events : List (BookedCash A party)) (fresh : BookedCash A party)
    (hcomplete : events.map (·.event) = s.cash ++ s.refundCash)
    (hfresh : fresh.event = cashFromPayload r.payment.payload)
    (hunit : ∀ e ∈ events, e.event.amount.tag = r.payment.payload.amount.tag) :
    (events ++ [fresh]).map (·.event) =
      (refundPost s r).cash ++ (refundPost s r).refundCash ∧
    (∀ e ∈ events ++ [fresh], e.event.amount.tag = r.payment.payload.amount.tag) ∧
    (∀ e ∈ events ++ [fresh], ∀ a, delta e a =
      (if party a = e.event.payee then e.event.amount.value else 0) -
      (if party a = e.event.payer then e.event.amount.value else 0)) ∧
    ∑ a, Ledger.cashVector ((events ++ [fresh]).map delta) a = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [List.map_append, List.map_cons, List.map_nil]
    rw [hcomplete, hfresh]
    simp [refundPost, eligiblePost, claimPost, List.append_assoc]
  · intro e he
    rcases List.mem_append.mp he with he | he
    · exact hunit e he
    · have heq : e = fresh := by simpa using he
      subst e
      simp [hfresh, cashFromPayload]
  · intro e _ a
    exact coordinates_are_actual_event hinj e a
  · apply Ledger.u09_2_cash_by_account
    intro v hv
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp hv
    exact delta_balanced e

/-- Initial is supplied by a named existing result such as
Trace.initial_invariant or Acceptance.a_opening_invariant; it is not a final conclusion. -/
theorem joint_from_actual_trace
    {A : Type} [Fintype A] [DecidableEq A] {party : A → PartyId}
    (hinj : Function.Injective party) (start base : Ledger.Handle)
    (initial : Trace.Invariant start) (path : Trace.Path start base)
    (extract : Extractor) (decision : Option RefundRule) (r : RefundRule)
    (h : Ready base.gamma extract base.state decision r)
    (events : List (BookedCash A party)) (fresh : BookedCash A party)
    (hcomplete : events.map (·.event) = base.state.cash ++ base.state.refundCash)
    (hfresh : fresh.event = cashFromPayload r.payment.payload)
    (hunit : ∀ e ∈ events, e.event.amount.tag = r.payment.payload.amount.tag) :
    Stages base.state r ∧
    checkedEffect base.gamma extract base.state decision r = some (effectPair base.state r) ∧
    QuantityConclusion base.state r ∧
    (events ++ [fresh]).map (·.event) =
      (refundPost base.state r).cash ++ (refundPost base.state r).refundCash ∧
    ∑ a, Ledger.cashVector ((events ++ [fresh]).map delta) a = 0 := by
  have hi := Trace.u10_2_finite_trace_composition path initial
  have hcash := actual_closed_account_conservation hinj base.state r events fresh
    hcomplete hfresh hunit
  exact ⟨first_two_stages_no_cash h, checkedEffect_of_ready h,
    separated_quantity_and_cash_components h hi.1 hi.2.1, hcash.1, hcash.2.2.2⟩

/-- 只连接旧实现的min分支及其金额门控；一般Θ给定k不被缩成此分支。 -/
theorem legacy_RestPay_is_min_branch
    {g : Gamma} {extract : Extractor} {s : Ledger.State}
    {decision : Option RefundRule} {r : RefundRule} (h : Ready g extract s decision r)
    (hk : r.credit = min r.payment.payload.amount.value r.claim.amount.value)
    (hpaid : r.payment.payload.amount.value ≠ s.paid) :
    Ledger.RestPay (eligiblePost s r) (cashFromPayload r.payment.payload) =
      .known (refundPost s r) := by
  simp [Ledger.RestPay, eligiblePost, claimPost, activeDebt, refundPost,
    cashFromPayload, h.refundPayer, h.refundPayee, h.refundUnit,
    not_lt.mpr h.nonnegAmount, h.freshCash, hpaid, hk]

theorem cash_balance_does_not_supply_admission
    {A : Type} [Fintype A] [DecidableEq A] {party : A → PartyId}
    (g : Gamma) (extract : Extractor) (s : Ledger.State)
    (decision : Option RefundRule) (r : RefundRule) (e : BookedCash A party)
    (he : e.event = cashFromPayload r.payment.payload) :
    e.event = cashFromPayload r.payment.payload ∧ (∑ a, delta e a = 0) ∧
    checkedEffect g extract s none r = none ∧
    (r.payment.applicable ≠ .yes → checkedEffect g extract s decision r = none) ∧
    (min r.payment.payload.amount.value r.claim.amount.value < r.credit →
      checkedEffect g extract s decision r = none) := by
  classical
  have hn : ¬ Ready g extract s none r := by
    intro h
    cases h.authorized
  refine ⟨he, delta_balanced e, ?_, ?_, ?_⟩
  · simp [checkedEffect, hn]
  · intro hp
    have hnot : ¬ Ready g extract s decision r := fun h => hp h.procedureGate
    simp [checkedEffect, hnot]
  · intro hk
    have hnot : ¬ Ready g extract s decision r := by
      intro h
      exact (not_lt_of_ge h.creditBound) hk
    simp [checkedEffect, hnot]

/-- 两个已给定合成来源的完整规范化提取；身份和事件不靠金额匹配。 -/
def twoPaymentExtractor (original payment : PaymentRequest) : Extractor :=
  fun source key =>
    if source = original.payload.source ∧ key = original.key then some original
    else if source = payment.payload.source ∧ key = payment.key then some payment
    else none

def twoAccountParty (b : Bool) : PartyId :=
  match b with
  | false => ⟨1⟩
  | true => ⟨2⟩

theorem twoAccountParty_injective : Function.Injective twoAccountParty := by
  intro a b h
  cases a <;> cases b <;> simp_all [twoAccountParty]

/-- 10/7/7后由合成Θ明确给出返还债4及实际返还4；不自动从surplus生成请求权。 -/
def tenPayload : PaymentPayload :=
  ⟨Acceptance.gamma.caseId, Acceptance.gamma.caseRevision, ⟨2⟩, ⟨2⟩, ⟨1⟩,
    ⟨4, Acceptance.tag⟩, ⟨102⟩, ⟨3⟩, Acceptance.gamma.normVersion, Acceptance.gamma.lawDate⟩
def tenPayment : PaymentRequest := ⟨⟨3⟩, ⟨3⟩, tenPayload, .yes, some ⟨3⟩⟩
def tenRule : RefundRule :=
  ⟨Acceptance.request 2, tenPayment,
    ⟨⟨2⟩, ⟨2⟩, ⟨1⟩, ⟨4, Acceptance.tag⟩, ⟨100⟩⟩, ⟨101⟩, 4⟩
def tenExtractor : Extractor := twoPaymentExtractor tenRule.original tenRule.payment

theorem ten_ready : Ready Acceptance.gamma tenExtractor Acceptance.post2.state
    (some tenRule) tenRule := by
  constructor <;> decide +kernel

theorem ten_actual_path : Trace.Path Acceptance.opening Acceptance.post2 := by
  have first : Trace.Step Acceptance.opening Acceptance.post1 :=
    Trace.u10_2_committed_executor_is_step Acceptance.opening Acceptance.opening
      (Acceptance.request 1) true .submit
      (Ledger.commitPayment Acceptance.opening (Acceptance.request 1)).1
      Acceptance.post1 (by decide +kernel)
  have second : Trace.Step Acceptance.post1 Acceptance.post2 :=
    Trace.u10_2_committed_executor_is_step Acceptance.post1 Acceptance.post1
      (Acceptance.request 2) true .submit
      (Ledger.commitPayment Acceptance.post1 (Acceptance.request 2)).1
      Acceptance.post2 (by decide +kernel)
  exact .cons first (.cons second (.nil _))

def tenEvents : List (BookedCash Bool twoAccountParty) :=
  [⟨cashFromPayload (Acceptance.payload 1), false, true, rfl, rfl⟩,
   ⟨cashFromPayload (Acceptance.payload 2), false, true, rfl, rfl⟩]
def tenFresh : BookedCash Bool twoAccountParty :=
  ⟨cashFromPayload tenPayload, true, false, rfl, rfl⟩

theorem ten_complete : tenEvents.map (·.event) =
    Acceptance.post2.state.cash ++ Acceptance.post2.state.refundCash := by decide +kernel

theorem ten_units : ∀ e ∈ tenEvents, e.event.amount.tag = tenRule.payment.payload.amount.tag := by
  intro e he
  simp [tenEvents] at he
  rcases he with rfl | rfl <;> rfl

def TenNumbers : Prop :=
  Ledger.balance (refundPost Acceptance.post2.state tenRule) = 0 ∧
  (refundPost Acceptance.post2.state tenRule).allocated = 10 ∧
  (refundPost Acceptance.post2.state tenRule).paid = 14 ∧
  (refundPost Acceptance.post2.state tenRule).surplus = 4 ∧
  restitutionQuantity (refundPost Acceptance.post2.state tenRule) tenRule.claim.relation = some 0 ∧
  refundTotal (refundPost Acceptance.post2.state tenRule) = 4

theorem ten_seven_seven_nonempty_witness :
    Ready Acceptance.gamma tenExtractor Acceptance.post2.state (some tenRule) tenRule ∧
    Stages Acceptance.post2.state tenRule ∧
    checkedEffect Acceptance.gamma tenExtractor Acceptance.post2.state (some tenRule) tenRule =
      some (effectPair Acceptance.post2.state tenRule) ∧
    QuantityConclusion Acceptance.post2.state tenRule ∧
    (tenEvents ++ [tenFresh]).map (·.event) =
      (refundPost Acceptance.post2.state tenRule).cash ++
        (refundPost Acceptance.post2.state tenRule).refundCash ∧
    (∑ a, Ledger.cashVector ((tenEvents ++ [tenFresh]).map delta) a) = 0 ∧
    (Ledger.balance Acceptance.post1.state = 3 ∧ Ledger.balance Acceptance.post2.state = 0 ∧
      Acceptance.post2.state.allocated = 10 ∧ Acceptance.post2.state.paid = 14 ∧
      Acceptance.post2.state.surplus = 4) ∧ TenNumbers ∧
    Ledger.RestPay (eligiblePost Acceptance.post2.state tenRule)
      (cashFromPayload tenRule.payment.payload) =
      .known (refundPost Acceptance.post2.state tenRule) := by
  have hj := joint_from_actual_trace twoAccountParty_injective
    Acceptance.opening Acceptance.post2 Acceptance.a_opening_invariant ten_actual_path
    tenExtractor (some tenRule) tenRule ten_ready tenEvents tenFresh ten_complete rfl ten_units
  rcases hj with ⟨hs, he, hq, hr, hc⟩
  exact ⟨ten_ready, hs, he, hq, hr, hc, Acceptance.a_u09_continuous_10_7_7,
    (by unfold TenNumbers; decide +kernel),
    legacy_RestPay_is_min_branch ten_ready (by decide +kernel) (by decide +kernel)⟩

/-- 同一W6+数值/现金/J/V对象为新返还的起点，保持原程序未证状态。 -/
def refundW6Context : ToyContext :=
  ⟨Acceptance.gamma, ⟨1⟩, ⟨1⟩, ⟨2⟩, ⟨10⟩, ⟨0⟩,
    ⟨11⟩, ⟨1⟩, ⟨1⟩, ⟨12⟩, ⟨2⟩, ⟨13⟩, ⟨2⟩, ⟨3⟩⟩
def refundW6Base : Ledger.Handle :=
  ⟨refundW6Context.gamma, 0, (stage3 refundW6Context true false false).ledger⟩
def refundW6Original : PaymentRequest :=
  ⟨⟨2⟩, ⟨2⟩, secondPayment refundW6Context, .yes, some ⟨2⟩⟩
def refundW6Payload : PaymentPayload :=
  ⟨refundW6Context.gamma.caseId, refundW6Context.gamma.caseRevision,
    ⟨2⟩, ⟨2⟩, ⟨1⟩, amountSix, ⟨14⟩, ⟨3⟩,
    refundW6Context.gamma.normVersion, refundW6Context.gamma.lawDate⟩
def refundW6Payment : PaymentRequest :=
  ⟨⟨3⟩, ⟨3⟩, refundW6Payload, .yes, some ⟨3⟩⟩
def refundW6Rule : RefundRule :=
  ⟨refundW6Original, refundW6Payment,
    ⟨⟨2⟩, ⟨2⟩, ⟨1⟩, amountSix, ⟨15⟩⟩, ⟨16⟩, 6⟩
def refundW6Extractor : Extractor :=
  twoPaymentExtractor refundW6Rule.original refundW6Rule.payment

theorem refundW6_ready : Ready refundW6Base.gamma refundW6Extractor refundW6Base.state
    (some refundW6Rule) refundW6Rule := by
  constructor <;> decide +kernel

theorem refundW6_initial : Trace.Invariant refundW6Base := by
  have hi := raw_stages_reuse_existing_invariants refundW6Context true false false
  rcases hi with ⟨_, _, _, _, _, _, hn, hc⟩
  refine ⟨hn, hc, ?_, ?_⟩
  · rfl
  · simp [Ledger.ReceiptCoherent, refundW6Base, stage3, mkW6, ledger3, ledger1,
      ledger0, Ledger.performance, Trace.initial]

def refundW6Events : List (BookedCash Bool twoAccountParty) :=
  [⟨cashFromPayload (firstPayment refundW6Context), false, true, rfl, rfl⟩,
   ⟨cashFromPayload (secondPayment refundW6Context), false, true, rfl, rfl⟩]
def refundW6Fresh : BookedCash Bool twoAccountParty :=
  ⟨cashFromPayload refundW6Payload, true, false, rfl, rfl⟩

theorem refundW6_complete : refundW6Events.map (·.event) =
    refundW6Base.state.cash ++ refundW6Base.state.refundCash := by decide +kernel

theorem refundW6_units : ∀ e ∈ refundW6Events,
    e.event.amount.tag = refundW6Rule.payment.payload.amount.tag := by
  intro e he
  simp [refundW6Events] at he
  rcases he with rfl | rfl <;> rfl

def refundW6After : ToyW6State :=
  { stage3 refundW6Context true false false with
    ledger := refundPost refundW6Base.state refundW6Rule }

def W6RefundNumbers : Prop :=
  Ledger.balance (refundPost refundW6Base.state refundW6Rule) = 0 ∧
  (refundPost refundW6Base.state refundW6Rule).paid = 12 ∧
  (refundPost refundW6Base.state refundW6Rule).allocated = 6 ∧
  (refundPost refundW6Base.state refundW6Rule).surplus = 6 ∧
  refundTotal (refundPost refundW6Base.state refundW6Rule) = 6 ∧
  restitutionQuantity (refundPost refundW6Base.state refundW6Rule)
    refundW6Rule.claim.relation = some 0 ∧
  refundW6After.V.status = .insufficient ∧
  refundW6After.J = some (paymentSixDocument refundW6Context)

theorem w6_nonempty_witness :
    Ready refundW6Base.gamma refundW6Extractor refundW6Base.state
      (some refundW6Rule) refundW6Rule ∧
    Stages refundW6Base.state refundW6Rule ∧
    checkedEffect refundW6Base.gamma refundW6Extractor refundW6Base.state
      (some refundW6Rule) refundW6Rule = some (effectPair refundW6Base.state refundW6Rule) ∧
    QuantityConclusion refundW6Base.state refundW6Rule ∧
    (refundW6Events ++ [refundW6Fresh]).map (·.event) =
      (refundPost refundW6Base.state refundW6Rule).cash ++
        (refundPost refundW6Base.state refundW6Rule).refundCash ∧
    (∑ a, Ledger.cashVector ((refundW6Events ++ [refundW6Fresh]).map delta) a) = 0 ∧
    (Ledger.balance refundW6Base.state = 0 ∧ Ledger.cashTotal refundW6Base.state = 12 ∧
      refundW6Base.state.paid = 12 ∧ refundW6Base.state.allocated = 6 ∧
      refundW6Base.state.surplus = 6) ∧
    W6RefundNumbers ∧ cashProjection refundW6After = refundW6After.ledger.cash ∧
    Ledger.RestPay (eligiblePost refundW6Base.state refundW6Rule)
      (cashFromPayload refundW6Rule.payment.payload) =
      .known (refundPost refundW6Base.state refundW6Rule) := by
  have hj := joint_from_actual_trace twoAccountParty_injective
    refundW6Base refundW6Base refundW6_initial (.nil _) refundW6Extractor
    (some refundW6Rule) refundW6Rule refundW6_ready refundW6Events refundW6Fresh
    refundW6_complete rfl refundW6_units
  rcases hj with ⟨hs, he, hq, hr, hc⟩
  have hw := four_stage_numeric_and_cash_witness refundW6Context true false false
    (by decide +kernel)
  rcases hw with ⟨_, _, _, _, _, _, _, _, _, _, _, hb, _, hcash, hpaid,
    halloc, hsurplus, _, _, _, _, _, _⟩
  refine ⟨refundW6_ready, hs, he, hq, hr, hc, ⟨hb, hcash, hpaid, halloc, hsurplus⟩,
    ?_, ?_, legacy_RestPay_is_min_branch refundW6_ready (by decide +kernel)
      (by decide +kernel)⟩
  · unfold W6RefundNumbers
    decide +kernel
  · exact (timed_X_is_actual_cash_projection refundW6Context true false false).2.2.2

#check RefundRule
#check Ready
#check first_two_stages_no_cash
#print axioms first_two_stages_no_cash
#check q_receipt_is_actual_event_and_history
#print axioms q_receipt_is_actual_event_and_history
#check separated_quantity_and_cash_components
#print axioms separated_quantity_and_cash_components
#check actual_closed_account_conservation
#print axioms actual_closed_account_conservation
#check joint_from_actual_trace
#print axioms joint_from_actual_trace
#check legacy_RestPay_is_min_branch
#print axioms legacy_RestPay_is_min_branch
#check cash_balance_does_not_supply_admission
#print axioms cash_balance_does_not_supply_admission
#check ten_seven_seven_nonempty_witness
#print axioms ten_seven_seven_nonempty_witness
#check w6_nonempty_witness
#print axioms w6_nonempty_witness
end JurisLean.Candidates.RestitutionFiniteClosureAudit20261104
