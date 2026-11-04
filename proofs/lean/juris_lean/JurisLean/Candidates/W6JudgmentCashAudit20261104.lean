import JurisLean.Candidates.Final20261021.Trace
import JurisLean.Seams.InstitutionalEffects

/-!
新增义务：仅补冻结09.7 L187–200所要求的有限四阶段W6同体账、V未证清偿状态、同一抽象Theta下的三条语义非蕴含，以及条件性的独立rJ记录边界；不扩成现实法域或通用模型。
SOURCE_PENDING_CI / PARTIAL_09_7。
所有时间、来源、主体、对象、规范事实和现金输入均是显式玩具上下文。raw Ledger.performance不是validated-protocol acceptance，也不证明真实世界付款已发生。PaymentPayload.factDate仍是LawDate；本稿不把它转换为Instant。
-/

namespace JurisLean.Candidates.W6JudgmentCashAudit20261104

open JurisLean.Candidates.Final20261021

/-- 一个有限原题玩具场景；实际付款/文书Instant与source都由输入分列。 -/
structure ToyContext where
  gamma : Gamma
  relation : RelationId
  payer : PartyId
  payee : PartyId
  debtSource : SourceRef
  debtAt : Instant
  firstSource : SourceRef
  firstId : EventId
  firstAt : Instant
  documentSource : SourceRef
  documentAt : Instant
  secondSource : SourceRef
  secondId : EventId
  secondAt : Instant

structure ToyBoolFact where
  value : Bool
  subject : PartyId
  object : ObjectId
  atTime : Instant
  source : SourceRef
  deriving DecidableEq

/-- V是清偿证明状态；insufficient表示本玩具证据不足以确认清偿，不表示清偿为假。 -/
structure ToyDischargeAssessment where
  status : Judgment
  subject : PartyId
  object : ObjectId
  atTime : Instant
  source : SourceRef
  deriving DecidableEq

/-- J文书有同一请求人、关系对象、命令时点、来源及typed金额6内容；不携带cashId。 -/
structure ToyPaymentDocument where
  subject : PartyId
  object : ObjectId
  atTime : Instant
  source : SourceRef
  contentAmount : Amount
  contentText : String
  deriving DecidableEq

/-- 每条cash投影以显式Instant附着到相同CashEvent身份/来源/双方/金额。 -/
structure TimedCash where
  subject : PartyId
  object : ObjectId
  atTime : Instant
  source : SourceRef
  event : CashEvent

structure ToyW6State where
  context : ToyContext
  ledger : Ledger.State
  debtFact : ToyBoolFact
  V : ToyDischargeAssessment
  J : Option ToyPaymentDocument
  physicalTreatment : ToyBoolFact
  normCondition : ToyBoolFact
  executionReady : ToyBoolFact
  Bp : ToyBoolFact
  Bn : ToyBoolFact
  E : ToyBoolFact
  X : List TimedCash

def toyTag : AmountTag := ⟨"toy", "toy-unit", 0⟩
def amountSix : Amount := ⟨6, toyTag⟩
def toyDebt (c : ToyContext) : DebtRecord :=
  ⟨c.relation, c.payer, c.payee, amountSix, "toy formed debt"⟩

def firstPayment (c : ToyContext) : PaymentPayload :=
  ⟨c.gamma.caseId, c.gamma.caseRevision, c.relation, c.payer, c.payee,
    amountSix, c.firstSource, c.firstId, c.gamma.normVersion, c.gamma.lawDate⟩
def secondPayment (c : ToyContext) : PaymentPayload :=
  ⟨c.gamma.caseId, c.gamma.caseRevision, c.relation, c.payer, c.payee,
    amountSix, c.secondSource, c.secondId, c.gamma.normVersion, c.gamma.lawDate⟩

def scopedBool (c : ToyContext) (value : Bool) : ToyBoolFact :=
  ⟨value, c.payer, .relation c.relation, c.documentAt, c.documentSource⟩
def debtWitness (c : ToyContext) : ToyBoolFact :=
  ⟨true, c.payer, .relation c.relation, c.debtAt, c.debtSource⟩
def dischargeAssessment (c : ToyContext) : ToyDischargeAssessment :=
  ⟨.insufficient, c.payer, .relation c.relation, c.documentAt, c.documentSource⟩
def paymentSixDocument (c : ToyContext) : ToyPaymentDocument :=
  ⟨c.payer, .relation c.relation, c.documentAt, c.documentSource,
    amountSix, "payment amount 6"⟩
def cashFromPayload (p : PaymentPayload) : CashEvent :=
  ⟨p.cashId, p.source, p.payer, p.payee, p.amount⟩
def firstTimedCash (c : ToyContext) : TimedCash :=
  ⟨c.payer, .relation c.relation, c.firstAt, c.firstSource,
    cashFromPayload (firstPayment c)⟩
def secondTimedCash (c : ToyContext) : TimedCash :=
  ⟨c.payer, .relation c.relation, c.secondAt, c.secondSource,
    cashFromPayload (secondPayment c)⟩

/-- Fixed toy Theta: Bp=physicalTreatment, Bn=normCondition, E=normCondition∧executionReady. -/
def mkW6 (c : ToyContext) (physical norm ready : Bool)
    (ledger : Ledger.State) (document : Option ToyPaymentDocument)
    (cashX : List TimedCash) : ToyW6State :=
  { context := c
    ledger := ledger
    debtFact := debtWitness c
    V := dischargeAssessment c
    J := document
    physicalTreatment := scopedBool c physical
    normCondition := scopedBool c norm
    executionReady := scopedBool c ready
    Bp := scopedBool c physical
    Bn := scopedBool c norm
    E := scopedBool c (norm && ready)
    X := cashX }

def ledger0 (c : ToyContext) : Ledger.State :=
  (Trace.initial c.gamma (toyDebt c)).state
def ledger1 (c : ToyContext) : Ledger.State :=
  Ledger.performance (ledger0 c) (firstPayment c)
def ledger3 (c : ToyContext) : Ledger.State :=
  Ledger.performance (ledger1 c) (secondPayment c)

def stage0 (c : ToyContext) (physical norm ready : Bool) : ToyW6State :=
  mkW6 c physical norm ready (ledger0 c) none []
def stage1 (c : ToyContext) (physical norm ready : Bool) : ToyW6State :=
  mkW6 c physical norm ready (ledger1 c) none [firstTimedCash c]
/-- 命令只加入J文书；同一Ledger.State、V和现金X均沿用第一阶段后态。 -/
def stage2 (c : ToyContext) (physical norm ready : Bool) : ToyW6State :=
  mkW6 c physical norm ready (ledger1 c) (some (paymentSixDocument c)) [firstTimedCash c]
def stage3 (c : ToyContext) (physical norm ready : Bool) : ToyW6State :=
  mkW6 c physical norm ready (ledger3 c) (some (paymentSixDocument c))
    [firstTimedCash c, secondTimedCash c]

def cashProjection (w : ToyW6State) : List CashEvent := w.X.map (·.event)

structure ObservedW6 where
  context : ToyContext
  ledger : Ledger.State
  debtFact : ToyBoolFact
  V : ToyDischargeAssessment
  J : Option ToyPaymentDocument
  X : List TimedCash

def observe (w : ToyW6State) : ObservedW6 :=
  ⟨w.context, w.ledger, w.debtFact, w.V, w.J, w.X⟩

/-- 完整stage2观察固定；Theta输入值可变，但文书、V、债务与X投影不变。 -/
theorem four_stage_numeric_and_cash_witness
    (c : ToyContext) (physical norm ready : Bool)
    (hids : c.firstId ≠ c.secondId) :
    Ledger.balance (stage0 c physical norm ready).ledger = 6 ∧
    Ledger.quantity (stage0 c physical norm ready).ledger c.relation = some 6 ∧
    Ledger.cashTotal (stage0 c physical norm ready).ledger = 0 ∧
    Ledger.balance (stage1 c physical norm ready).ledger = 0 ∧
    Ledger.quantity (stage1 c physical norm ready).ledger c.relation = some 0 ∧
    Ledger.cashTotal (stage1 c physical norm ready).ledger = 6 ∧
    (stage2 c physical norm ready).ledger = (stage1 c physical norm ready).ledger ∧
    (stage2 c physical norm ready).J = some (paymentSixDocument c) ∧
    Ledger.balance (stage2 c physical norm ready).ledger = 0 ∧
    Ledger.cashTotal (stage2 c physical norm ready).ledger = 6 ∧
    (stage2 c physical norm ready).V.status = .insufficient ∧
    Ledger.balance (stage3 c physical norm ready).ledger = 0 ∧
    Ledger.quantity (stage3 c physical norm ready).ledger c.relation = some 0 ∧
    Ledger.cashTotal (stage3 c physical norm ready).ledger = 12 ∧
    (stage3 c physical norm ready).ledger.paid = 12 ∧
    (stage3 c physical norm ready).ledger.allocated = 6 ∧
    (stage3 c physical norm ready).ledger.surplus = 6 ∧
    (stage3 c physical norm ready).ledger.newDebt = 0 ∧
    (stage3 c physical norm ready).ledger.debt.relation = c.relation ∧
    (stage3 c physical norm ready).ledger.formations = [c.relation] ∧
    (stage3 c physical norm ready).V.status = .insufficient ∧
    (stage3 c physical norm ready).X.map (fun x => x.event.id) = [c.firstId, c.secondId] ∧
    c.firstId ≠ c.secondId := by
  norm_num [stage0, stage1, stage2, stage3, mkW6, scopedBool,
    debtWitness, dischargeAssessment, paymentSixDocument, cashFromPayload,
    firstTimedCash, secondTimedCash, toyDebt, amountSix, toyTag,
    ledger0, ledger1, ledger3, firstPayment, secondPayment,
    Trace.initial, Ledger.performance, Ledger.balance, Ledger.quantity,
    Ledger.cashTotal, hids]

theorem timed_X_is_actual_cash_projection (c : ToyContext)
    (physical norm ready : Bool) :
    cashProjection (stage0 c physical norm ready) = (stage0 c physical norm ready).ledger.cash ∧
    cashProjection (stage1 c physical norm ready) = (stage1 c physical norm ready).ledger.cash ∧
    cashProjection (stage2 c physical norm ready) = (stage2 c physical norm ready).ledger.cash ∧
    cashProjection (stage3 c physical norm ready) = (stage3 c physical norm ready).ledger.cash := by
  simp [cashProjection, stage0, stage1, stage2, stage3, mkW6,
    firstTimedCash, secondTimedCash, cashFromPayload, firstPayment,
    secondPayment, ledger0, ledger1, ledger3, toyDebt, amountSix,
    toyTag, Trace.initial, Ledger.performance]

theorem raw_stages_reuse_existing_invariants (c : ToyContext)
    (physical norm ready : Bool) :
    Ledger.Conserves (stage0 c physical norm ready).ledger ∧
    Ledger.CashConsistent (stage0 c physical norm ready).ledger ∧
    Ledger.Conserves (stage1 c physical norm ready).ledger ∧
    Ledger.CashConsistent (stage1 c physical norm ready).ledger ∧
    Ledger.Conserves (stage2 c physical norm ready).ledger ∧
    Ledger.CashConsistent (stage2 c physical norm ready).ledger ∧
    Ledger.Conserves (stage3 c physical norm ready).ledger ∧
    Ledger.CashConsistent (stage3 c physical norm ready).ledger := by
  have h0 := Trace.initial_invariant c.gamma (toyDebt c) (by norm_num [toyDebt, amountSix])
  have h1c := Ledger.u09_1_quantity_conservation (ledger0 c) (firstPayment c)
    h0.1 (by norm_num [firstPayment, amountSix])
  have h1cash := Ledger.performance_cash_consistent (ledger0 c) (firstPayment c) h0.2.1
  have h3c := Ledger.u09_1_quantity_conservation (ledger1 c) (secondPayment c)
    h1c (by norm_num [secondPayment, amountSix])
  have h3cash := Ledger.performance_cash_consistent (ledger1 c) (secondPayment c) h1cash
  exact ⟨h0.1, h0.2.1, h1c, h1cash, h1c, h1cash, h3c, h3cash⟩
theorem payment_and_document_metadata_are_explicit (c : ToyContext) :
    (paymentSixDocument c).subject = c.payer ∧
    (paymentSixDocument c).object = .relation c.relation ∧
    (paymentSixDocument c).atTime = c.documentAt ∧
    (paymentSixDocument c).source = c.documentSource ∧
    (paymentSixDocument c).contentAmount = amountSix ∧
    (firstTimedCash c).subject = c.payer ∧
    (firstTimedCash c).object = .relation c.relation ∧
    (firstTimedCash c).atTime = c.firstAt ∧
    (firstTimedCash c).source = c.firstSource ∧
    (firstTimedCash c).event.id = c.firstId ∧
    (secondTimedCash c).subject = c.payer ∧
    (secondTimedCash c).object = .relation c.relation ∧
    (secondTimedCash c).atTime = c.secondAt ∧
    (secondTimedCash c).source = c.secondSource ∧
    (secondTimedCash c).event.id = c.secondId := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem two_payment_payloads_share_context_but_cash_ids_differ
    (c : ToyContext) (hids : c.firstId ≠ c.secondId) :
    (firstPayment c).caseId = (secondPayment c).caseId ∧
    (firstPayment c).caseRevision = (secondPayment c).caseRevision ∧
    (firstPayment c).relation = (secondPayment c).relation ∧
    (firstPayment c).payer = (secondPayment c).payer ∧
    (firstPayment c).payee = (secondPayment c).payee ∧
    (firstPayment c).amount = (secondPayment c).amount ∧
    (cashFromPayload (firstPayment c)).id ≠ (cashFromPayload (secondPayment c)).id := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, hids⟩

/-- Theta models constrain the same actual stage2 ledger, V, J, debt and cash; output facts are derived. -/
structure ToyWorld where
  state : ToyW6State

def toyWorld (c : ToyContext) (physical norm ready : Bool) : ToyWorld :=
  ⟨stage2 c physical norm ready⟩

def ModelsTheta (c : ToyContext) (w : ToyWorld) : Prop :=
  w.state.context = c ∧
  w.state.ledger = ledger1 c ∧
  w.state.debtFact = debtWitness c ∧
  w.state.V = dischargeAssessment c ∧
  w.state.J = some (paymentSixDocument c) ∧
  w.state.X = [firstTimedCash c] ∧
  w.state.physicalTreatment = scopedBool c w.state.physicalTreatment.value ∧
  w.state.normCondition = scopedBool c w.state.normCondition.value ∧
  w.state.executionReady = scopedBool c w.state.executionReady.value ∧
  w.state.Bp = scopedBool c w.state.physicalTreatment.value ∧
  w.state.Bn = scopedBool c w.state.normCondition.value ∧
  w.state.E = scopedBool c (w.state.normCondition.value && w.state.executionReady.value)

def Bp (w : ToyWorld) : Bool := w.state.Bp.value
def Bn (w : ToyWorld) : Bool := w.state.Bn.value
def E (w : ToyWorld) : Bool := w.state.E.value
/-- X由同一state的timed cash事件列表查第二个真实cashId，不是自由布尔位。 -/
def X (w : ToyWorld) : Bool :=
  decide (w.state.context.secondId ∈ w.state.X.map (fun x => x.event.id))

def semanticEntails (c : ToyContext) (premise conclusion : ToyWorld → Bool) : Prop :=
  ∀ w, ModelsTheta c w → premise w = true → conclusion w = true

theorem toyWorld_is_a_Theta_model (c : ToyContext) (physical norm ready : Bool) :
    ModelsTheta c (toyWorld c physical norm ready) := by
  simp [ModelsTheta, toyWorld, stage2, stage1, stage0, mkW6]

theorem toyWorlds_satisfy_one_Theta (c : ToyContext) :
    ModelsTheta c (toyWorld c true false false) ∧
    ModelsTheta c (toyWorld c false true false) ∧
    ModelsTheta c (toyWorld c true true true) := by
  exact ⟨toyWorld_is_a_Theta_model c true false false,
    toyWorld_is_a_Theta_model c false true false,
    toyWorld_is_a_Theta_model c true true true⟩

theorem toyWorlds_share_same_observed_W6 (c : ToyContext) :
    observe (toyWorld c true false false).state =
      observe (toyWorld c false true false).state ∧
    observe (toyWorld c false true false).state =
      observe (toyWorld c true true true).state := by
  constructor <;> rfl

theorem toyWorld_layer_values (c : ToyContext) :
    Bp (toyWorld c true false false) = true ∧
    Bn (toyWorld c true false false) = false ∧
    E (toyWorld c true false false) = false ∧
    Bp (toyWorld c false true false) = false ∧
    Bn (toyWorld c false true false) = true ∧
    E (toyWorld c false true false) = false ∧
    Bp (toyWorld c true true true) = true ∧
    Bn (toyWorld c true true true) = true ∧
    E (toyWorld c true true true) = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem toyWorld_values_100 (c : ToyContext) :
    Bp (toyWorld c true false false) = true ∧
    Bn (toyWorld c true false false) = false ∧
    E (toyWorld c true false false) = false := by
  exact ⟨rfl, rfl, rfl⟩

theorem toyWorld_values_010 (c : ToyContext) :
    Bp (toyWorld c false true false) = false ∧
    Bn (toyWorld c false true false) = true ∧
    E (toyWorld c false true false) = false := by
  exact ⟨rfl, rfl, rfl⟩

theorem toyWorld_values_111 (c : ToyContext) :
    Bp (toyWorld c true true true) = true ∧
    Bn (toyWorld c true true true) = true ∧
    E (toyWorld c true true true) = true := by
  exact ⟨rfl, rfl, rfl⟩
theorem toyWorld_X_is_absent_before_second_cash (c : ToyContext)
    (hids : c.firstId ≠ c.secondId) :
    X (toyWorld c true false false) = false ∧
    X (toyWorld c false true false) = false ∧
    X (toyWorld c true true true) = false := by
  have hsecond : c.secondId ≠ c.firstId := Ne.symm hids
  simp [X, toyWorld, stage2, stage1, stage0, mkW6, firstTimedCash,
    firstPayment, cashFromPayload, ledger0, ledger1, toyDebt, amountSix,
    toyTag, Trace.initial, Ledger.performance, hsecond]

theorem Bp_does_not_semantically_entail_Bn (c : ToyContext) :
    ¬ semanticEntails c Bp Bn := by
  intro h
  have hm := (toyWorlds_satisfy_one_Theta c).1
  have hp : Bp (toyWorld c true false false) = true := (toyWorld_layer_values c).1
  have hn := h (toyWorld c true false false) hm hp
  rw [(toyWorld_values_100 c).2.1] at hn
  cases hn

theorem Bn_does_not_semantically_entail_E (c : ToyContext) :
    ¬ semanticEntails c Bn E := by
  intro h
  have hm := (toyWorlds_satisfy_one_Theta c).2.1
  have hp : Bn (toyWorld c false true false) = true := (toyWorld_values_010 c).2.1
  have he := h (toyWorld c false true false) hm hp
  rw [(toyWorld_values_010 c).2.2] at he
  cases he

theorem E_does_not_semantically_entail_X (c : ToyContext)
    (hids : c.firstId ≠ c.secondId) :
    ¬ semanticEntails c E X := by
  intro h
  have hm := (toyWorlds_satisfy_one_Theta c).2.2
  have he : E (toyWorld c true true true) = true := (toyWorld_values_111 c).2.2
  have hx := h (toyWorld c true true true) hm he
  rw [(toyWorld_X_is_absent_before_second_cash c hids).2.2] at hx
  cases hx

/-- A conditional independent-rJ record branch; it is not inserted into the old relation ledger. -/
structure ToyRjRecord where
  relation : RelationId
  subject : PartyId
  object : ObjectId
  atTime : Instant
  source : SourceRef
  amount : Amount

def toyJudgmentRelation (c : ToyContext) : RelationId := ⟨c.relation.value + 1⟩
def separateRjRecord (c : ToyContext) (amount : Amount) : ToyRjRecord :=
  ⟨toyJudgmentRelation c, c.payer, .relation (toyJudgmentRelation c),
    c.documentAt, c.documentSource, amount⟩
def thetaConditionalRjBranch (c : ToyContext) (thetaProvidesIndependentRj : Bool)
    (amount : Amount) : Option ToyRjRecord :=
  if thetaProvidesIndependentRj then some (separateRjRecord c amount) else none

theorem conditional_rJ_branch_is_separate_and_source_bound
    (c : ToyContext) (amount : Amount) :
    (separateRjRecord c amount).relation = toyJudgmentRelation c ∧
    (separateRjRecord c amount).subject = c.payer ∧
    (separateRjRecord c amount).object = .relation (toyJudgmentRelation c) ∧
    (separateRjRecord c amount).atTime = c.documentAt ∧
    (separateRjRecord c amount).source = c.documentSource ∧
    toyJudgmentRelation c ≠ c.relation := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro h
  have hv := congrArg RelationId.value h
  have hsucc : c.relation.value = c.relation.value + 1 := by simpa [toyJudgmentRelation] using hv.symm
  exact (Nat.ne_of_lt (Nat.lt_succ_self c.relation.value)) hsucc

/-
Boundary: thetaConditionalRjBranch is an optional separate record only when its input explicitly says Theta supplies it.
No rule here maps an old payment onto rJ, offsets the new record, or prevents a second remedy; each would need its own stated Theta/evidence premise. None is inferred from the old relation's D=0 or cash X.
-/

#check JurisLean.Candidates.W6JudgmentCashAudit20261104.four_stage_numeric_and_cash_witness
#print axioms JurisLean.Candidates.W6JudgmentCashAudit20261104.four_stage_numeric_and_cash_witness
#check JurisLean.Candidates.W6JudgmentCashAudit20261104.timed_X_is_actual_cash_projection
#print axioms JurisLean.Candidates.W6JudgmentCashAudit20261104.timed_X_is_actual_cash_projection
#check JurisLean.Candidates.W6JudgmentCashAudit20261104.raw_stages_reuse_existing_invariants
#print axioms JurisLean.Candidates.W6JudgmentCashAudit20261104.raw_stages_reuse_existing_invariants
#check JurisLean.Candidates.W6JudgmentCashAudit20261104.toyWorlds_satisfy_one_Theta
#print axioms JurisLean.Candidates.W6JudgmentCashAudit20261104.toyWorlds_satisfy_one_Theta
#check JurisLean.Candidates.W6JudgmentCashAudit20261104.toyWorlds_share_same_observed_W6
#print axioms JurisLean.Candidates.W6JudgmentCashAudit20261104.toyWorlds_share_same_observed_W6
#check JurisLean.Candidates.W6JudgmentCashAudit20261104.Bp_does_not_semantically_entail_Bn
#print axioms JurisLean.Candidates.W6JudgmentCashAudit20261104.Bp_does_not_semantically_entail_Bn
#check JurisLean.Candidates.W6JudgmentCashAudit20261104.Bn_does_not_semantically_entail_E
#print axioms JurisLean.Candidates.W6JudgmentCashAudit20261104.Bn_does_not_semantically_entail_E
#check JurisLean.Candidates.W6JudgmentCashAudit20261104.E_does_not_semantically_entail_X
#print axioms JurisLean.Candidates.W6JudgmentCashAudit20261104.E_does_not_semantically_entail_X
#check JurisLean.Candidates.W6JudgmentCashAudit20261104.conditional_rJ_branch_is_separate_and_source_bound
#print axioms JurisLean.Candidates.W6JudgmentCashAudit20261104.conditional_rJ_branch_is_separate_and_source_bound
#check JurisLean.Candidates.W6JudgmentCashAudit20261104.ModelsTheta
#check JurisLean.Candidates.W6JudgmentCashAudit20261104.X

end JurisLean.Candidates.W6JudgmentCashAudit20261104
