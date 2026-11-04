/-
本证明仅补冻结09.5 L171/173的同一Theta可实现性与三语义非蕴含，以及L175同内容文书的不同效力和条件桥；旧事件位分离不能替代。
此处所有标识符、制度与事实均为明确的玩具输入，不表示任何真实法域。
-/
import Mathlib.Tactic

namespace JurisLean.Candidates.SemanticIndependenceAudit20261104

/-- 玩具动作将“应支付6”直接编码为带金额的动作。 -/
inductive ToyAction where
  | pay (amount : Nat)
  deriving DecidableEq

/-- 玩具文书内容是有类型的付款金额，而不是与金额无关的效果位。 -/
inductive ToyContent where
  | paymentDue (amount : Nat)
  deriving DecidableEq

/-- 单一固定玩具语境；所有三个模型共享这些主体、动作、对象、时点、文书与来源。 -/
structure ToyContext where
  actor : Nat
  action : ToyAction
  object : Nat
  time : Nat
  document : Nat
  source : Nat
  content : ToyContent
  received : Bool
  authentic : Bool
  effective : Bool
  objectMatches : Bool
  scopeMatches : Bool
  deriving DecidableEq

def toyContext : ToyContext :=
  { actor := 1
    action := .pay 6
    object := 2
    time := 3
    document := 4
    source := 5
    content := .paymentDue 6
    received := true
    authentic := true
    effective := true
    objectMatches := true
    scopeMatches := true }

/-- 完整小模型含许可 l、触发 g、行为 b、权限能力及三种语义值 P/O/X。 -/
structure ToyModel where
  context : ToyContext
  l : Bool
  g : Bool
  b : Bool
  competentIssuer : Bool
  p : Bool
  o : Bool
  x : Bool
  deriving DecidableEq

def Power (m : ToyModel) : Bool := m.p
def Obligation (m : ToyModel) : Bool := m.o
def Occurred (m : ToyModel) : Bool := m.x

def documentTrigger (c : ToyContext) (m : ToyModel) : Bool :=
  c.received &&
    decide (c.action = ToyAction.pay 6) &&
    decide (c.content = ToyContent.paymentDue 6) &&
    c.authentic && m.competentIssuer && c.effective &&
    c.objectMatches && c.scopeMatches

/-- 玩具制度 Theta：P=l、O=l∧g、X=b；g 当且仅当收到同一 pay-6 内容，
    且文书真实、发布者有权限、已生效、对象和范围匹配。 -/
def ModelsTheta (c : ToyContext) (m : ToyModel) : Prop :=
  m.context = c ∧
  m.p = m.l ∧
  m.o = (m.l && m.g) ∧
  m.x = m.b ∧
  m.g = documentTrigger m.context m

/-- 此处语义蕴含只量化固定玩具 Theta 的实际满足模型。 -/
def semanticEntails
    (premise conclusion : ToyModel → Prop) : Prop :=
  ∀ m, ModelsTheta toyContext m → premise m → conclusion m

def hasPower (m : ToyModel) : Prop := Power m = true
def hasObligation (m : ToyModel) : Prop := Obligation m = true
def hasOccurred (m : ToyModel) : Prop := Occurred m = true

/-- 在此玩具中，l=false是未获许可，g=false是文书触发条件未满足，b=false是行为未发生；它们不是任意可替换的false位。 -/
def model100 : ToyModel :=
  { context := toyContext, l := true, g := false, b := false, competentIssuer := false,
    p := true, o := false, x := false }

/-- (l,g,b)=(1,1,0)：义务已触发，但行为尚未发生。 -/
def model110 : ToyModel :=
  { context := toyContext, l := true, g := true, b := false, competentIssuer := true,
    p := true, o := true, x := false }

/-- (l,g,b)=(0,0,1)：未获许可，但实际行为已发生。 -/
def model001 : ToyModel :=
  { context := toyContext, l := false, g := false, b := true, competentIssuer := false,
    p := false, o := false, x := true }

theorem three_complete_witness_models :
    ModelsTheta toyContext model100 ∧
    ModelsTheta toyContext model110 ∧
    ModelsTheta toyContext model001 ∧
    (model100.l = true ∧ model100.g = false ∧ model100.competentIssuer = model100.g ∧ model100.b = false ∧
      Power model100 = true ∧ Obligation model100 = false ∧ Occurred model100 = false) ∧
    (model110.l = true ∧ model110.g = true ∧ model110.competentIssuer = model110.g ∧ model110.b = false ∧
      Power model110 = true ∧ Obligation model110 = true ∧ Occurred model110 = false) ∧
    (model001.l = false ∧ model001.g = false ∧ model001.competentIssuer = model001.g ∧ model001.b = true ∧
      Power model001 = false ∧ Obligation model001 = false ∧ Occurred model001 = true) := by
  simp [ModelsTheta, documentTrigger, toyContext, model100, model110, model001,
    Power, Obligation, Occurred]

theorem obligation_semantically_entails_power :
    semanticEntails hasObligation hasPower := by
  intro m hmodel ho
  rcases hmodel with ⟨hctx, hp, hoDef, hx, hg⟩
  change m.o = true at ho
  change m.p = true
  have hAnd : m.l && m.g = true := by
    rw [hoDef] at ho
    exact ho
  cases hl : m.l with
  | false => simp [hl] at hAnd
  | true =>
      calc
        m.p = m.l := hp
        _ = true := hl

theorem power_does_not_semantically_entail_obligation :
    ¬ semanticEntails hasPower hasObligation := by
  intro h
  have hm : ModelsTheta toyContext model100 := by
    simp [ModelsTheta, documentTrigger, toyContext, model100]
  have ho : hasObligation model100 := h model100 hm (by simp [hasPower, Power, model100])
  simp [hasObligation, Obligation, model100] at ho

theorem obligation_does_not_semantically_entail_occurred :
    ¬ semanticEntails hasObligation hasOccurred := by
  intro h
  have hm : ModelsTheta toyContext model110 := by
    simp [ModelsTheta, documentTrigger, toyContext, model110]
  have hx : hasOccurred model110 := h model110 hm (by simp [hasObligation, Obligation, model110])
  simp [hasOccurred, Occurred, model110] at hx

theorem occurred_does_not_semantically_entail_power :
    ¬ semanticEntails hasOccurred hasPower := by
  intro h
  have hm : ModelsTheta toyContext model001 := by
    simp [ModelsTheta, documentTrigger, toyContext, model001]
  have hp : hasPower model001 := h model001 hm (by simp [hasOccurred, Occurred, model001])
  simp [hasPower, Power, model001] at hp

theorem same_received_pay6_document_different_obligation :
    ModelsTheta toyContext model100 ∧
    ModelsTheta toyContext model110 ∧
    model100.context = model110.context ∧
    model100.context.actor = 1 ∧
    model100.context.action = ToyAction.pay 6 ∧
    model100.context.object = 2 ∧
    model100.context.time = 3 ∧
    model100.context.document = 4 ∧
    model100.context.source = 5 ∧
    model100.context.content = ToyContent.paymentDue 6 ∧
    model100.context.received = true ∧
    model100.context.authentic = true ∧
    model100.context.effective = true ∧
    model100.context.objectMatches = true ∧
    model100.context.scopeMatches = true ∧
    model100.competentIssuer = false ∧
    model110.competentIssuer = true ∧
    Obligation model100 = false ∧
    Obligation model110 = true := by
  simp [ModelsTheta, documentTrigger, toyContext, model100, model110,
    Obligation]

theorem received_content_and_permission_entail_obligation :
    semanticEntails
      (fun m => Power m = true ∧ documentTrigger m.context m = true)
      (fun m => Obligation m = true) := by
  intro m hmodel hpremise
  rcases hmodel with ⟨hctx, hp, hoDef, hx, hg⟩
  rcases hpremise with ⟨hPower, hDocument⟩
  have hLicensed : m.l = true := by
    calc
      m.l = m.p := hp.symm
      _ = true := hPower
  have hTriggered : m.g = true := by
    rw [hg]
    exact hDocument
  rw [hoDef, hLicensed, hTriggered]
  rfl

end SemanticIndependenceAudit20261104

#check JurisLean.Candidates.SemanticIndependenceAudit20261104.three_complete_witness_models
#print axioms JurisLean.Candidates.SemanticIndependenceAudit20261104.three_complete_witness_models
#check JurisLean.Candidates.SemanticIndependenceAudit20261104.obligation_semantically_entails_power
#print axioms JurisLean.Candidates.SemanticIndependenceAudit20261104.obligation_semantically_entails_power
#check JurisLean.Candidates.SemanticIndependenceAudit20261104.power_does_not_semantically_entail_obligation
#print axioms JurisLean.Candidates.SemanticIndependenceAudit20261104.power_does_not_semantically_entail_obligation
#check JurisLean.Candidates.SemanticIndependenceAudit20261104.obligation_does_not_semantically_entail_occurred
#print axioms JurisLean.Candidates.SemanticIndependenceAudit20261104.obligation_does_not_semantically_entail_occurred
#check JurisLean.Candidates.SemanticIndependenceAudit20261104.occurred_does_not_semantically_entail_power
#print axioms JurisLean.Candidates.SemanticIndependenceAudit20261104.occurred_does_not_semantically_entail_power
#check JurisLean.Candidates.SemanticIndependenceAudit20261104.same_received_pay6_document_different_obligation
#print axioms JurisLean.Candidates.SemanticIndependenceAudit20261104.same_received_pay6_document_different_obligation
#check JurisLean.Candidates.SemanticIndependenceAudit20261104.received_content_and_permission_entail_obligation
#print axioms JurisLean.Candidates.SemanticIndependenceAudit20261104.received_content_and_permission_entail_obligation
#check JurisLean.Candidates.SemanticIndependenceAudit20261104.ModelsTheta
#check JurisLean.Candidates.SemanticIndependenceAudit20261104.semanticEntails
