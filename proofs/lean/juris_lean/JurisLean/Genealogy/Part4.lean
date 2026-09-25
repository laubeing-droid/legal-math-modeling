import JurisLean.Genealogy.Part3

/-!
Genealogy Part4 — L4 argumentation, interpretation, discretion, negotiation,
and strategy structures. Theorems state only structural discipline.
-/

namespace JurisLean.Genealogy.Part4

namespace P057

structure AnalogyProbe where
  sharedStructure : Bool
  sharedRule : Bool
  distinguishingFactor : Bool
deriving DecidableEq, Repr

def analogousApplication (p : AnalogyProbe) : Bool :=
  p.sharedStructure && p.sharedRule && !p.distinguishingFactor

/-- Structural sameness + rule sameness + no distinction permits analogy. -/
theorem analogy_three_conditions :
    analogousApplication
      { sharedStructure := true, sharedRule := true, distinguishingFactor := false } = true := rfl
-- [rfl] 置信：Bool 三条件字面量直接归约。

/-- A distinguishing factor blocks analogy. -/
theorem distinction_blocks_analogy (s r : Bool) :
    analogousApplication
      { sharedStructure := s, sharedRule := r, distinguishingFactor := true } = false := by
  cases s <;> cases r <;> rfl
-- [cases+rfl] 置信：四个 Bool 组合均因 `!true=false` 归约为 false。

end P057

namespace P058

structure ToulminArgument where
  claim : Option String
  grounds : List String
  warrant : Option String
  backing : List String
  qualifier : Option String
  rebuttals : List String
deriving DecidableEq, Repr

def wellFormed (a : ToulminArgument) : Bool :=
  Part0.Util.present a.claim &&
  !a.grounds.isEmpty &&
  Part0.Util.present a.warrant &&
  !a.backing.isEmpty &&
  Part0.Util.present a.qualifier

/-- Six slots exist by type; the five nonempty-required slots pass in the witness. -/
theorem toulmin_six_slot_witness :
    wellFormed
      { claim := some "C", grounds := ["G"], warrant := some "W",
        backing := ["B"], qualifier := some "Q", rebuttals := [] } = true := by
  decide
-- [decide] 置信：Option/List 非空性均为闭式构造子计算；rebuttal 槽允许显式空表。

end P058

namespace P060

inductive InterpretationMethod where
  | literal
  | systematic
  | purposive
  | historical
  | constitutional
deriving DecidableEq, Repr

inductive Interpretation where
  | literal (reading : String)
  | systematic (reading : String)
  | purposive (reading : String)
  | historical (reading : String)
  | constitutional (reading : String)
deriving DecidableEq, Repr

structure EvaluatedReading where
  method : InterpretationMethod
  reading : String
deriving DecidableEq, Repr

def methodOf : Interpretation → InterpretationMethod
  | .literal _ => .literal
  | .systematic _ => .systematic
  | .purposive _ => .purposive
  | .historical _ => .historical
  | .constitutional _ => .constitutional

def evaluateIsolated : Interpretation → EvaluatedReading
  | .literal r => { method := .literal, reading := r }
  | .systematic r => { method := .systematic, reading := r }
  | .purposive r => { method := .purposive, reading := r }
  | .historical r => { method := .historical, reading := r }
  | .constitutional r => { method := .constitutional, reading := r }

/-- Isolated evaluation preserves the constructor family before any comparison. -/
theorem isolated_branch_preserved (i : Interpretation) :
    (evaluateIsolated i).method = methodOf i := by
  cases i <;> rfl
-- [cases+rfl] 置信：五个构造子逐一映射到同名 method。

end P060

namespace P061

structure ReadingAttack where
  attackerId : String
  targetId : String
  attackerPrecedence : Nat
deriving DecidableEq, Repr

def attackAdmissible
    (attack : ReadingAttack) (targetPinned : Bool) (targetPrecedence : Nat) : Bool :=
  match targetPinned with
  | false => true
  | true => if attack.attackerPrecedence ≤ targetPrecedence then false else true

/-- A pinned reading is immune to an attack no stronger than its precedence. -/
theorem pinned_reading_immune_to_low_attack
    (attack : ReadingAttack) (targetPrecedence : Nat)
    (h : attack.attackerPrecedence ≤ targetPrecedence) :
    attackAdmissible attack true targetPrecedence = false := by
  simp [attackAdmissible, h]
-- [定义展开] 置信：pinned=true 且次序条件由 `h` 锁死到 false 分支。

end P061

namespace P062

inductive AmbiguityState where
  | ambiguous
  | resolved
  | insufficient
deriving DecidableEq, Repr

structure AmbiguityProbe where
  candidateSenses : List String
  contextProvided : Bool
deriving DecidableEq, Repr

def ambiguityState (p : AmbiguityProbe) : AmbiguityState :=
  match p.contextProvided with
  | true => .resolved
  | false =>
      if 2 ≤ p.candidateSenses.length then .ambiguous else .insufficient

/-- Two candidate senses without context are ambiguous. -/
theorem two_senses_without_context_ambiguous :
    ambiguityState
      { candidateSenses := ["sense-1", "sense-2"], contextProvided := false }
      = .ambiguous := by
  decide
-- [decide] 置信：列表长度为 2，Nat 比较闭式计算。

/-- Any supplied context resolves the ambiguity state at this structural layer. -/
theorem context_resolves (senses : List String) :
    ambiguityState { candidateSenses := senses, contextProvided := true } = .resolved := rfl
-- [rfl] 置信：函数先匹配 contextProvided=true，候选列表不再参与分支。

end P062

namespace P063

inductive NormKind where
  | rule
  | principle
deriving DecidableEq, Repr

inductive NormContribution where
  | ruleSatisfied
  | ruleViolated
  | principleWeight (weight : Nat)
  | principleNoWeight
deriving DecidableEq, Repr

def normContribution
    (kind : NormKind) (satisfied : Bool) (weight : Option Nat) : NormContribution :=
  match kind with
  | .rule => match satisfied with | true => .ruleSatisfied | false => .ruleViolated
  | .principle =>
      match weight with
      | none => .principleNoWeight
      | some 0 => .principleNoWeight
      | some n => .principleWeight n

/-- Rules are all-or-nothing. -/
theorem rule_all_or_nothing_true (w : Option Nat) :
    normContribution .rule true w = .ruleSatisfied := rfl
-- [rfl] 置信：rule 分支不读取 weight。

/-- A principle contributes only a weight constructor, not a rule verdict constructor. -/
theorem principle_positive_weight_is_weight_only (n : Nat) :
    normContribution .principle true (some (n + 1)) = .principleWeight (n + 1) := rfl
-- [rfl] 置信：`n+1` 不匹配 `0` 构造模式，直接进入 weight 分支。

end P063

namespace P064

inductive ValueNode where
  | a | b | c | d
deriving DecidableEq, Repr

inductive ValueRelation where
  | le
  | ge
  | incomparable
deriving DecidableEq, Repr

def valueRelation : ValueNode → ValueNode → ValueRelation
  | .a, .a => .le
  | .b, .b => .le
  | .c, .c => .le
  | .d, .d => .le
  | .a, .b => .le
  | .b, .c => .le
  | .a, .c => .le
  | .b, .a => .ge
  | .c, .b => .ge
  | .c, .a => .ge
  | _, _ => .incomparable

/-- Concrete preorder witness: a≤b, b≤c, while c and d remain incomparable. -/
theorem preorder_with_legal_incomparability :
    valueRelation .a .b = .le ∧
    valueRelation .b .c = .le ∧
    valueRelation .c .d = .incomparable := by
  decide
-- [decide] 置信：有限四节点关系表全为构造子归约。

end P064

namespace P065

structure LawmakingSignals where
  noApplicableRule : Bool
  analogyFails : Bool
  gapPresent : Bool
deriving DecidableEq, Repr

def lawmakingFlagged (s : LawmakingSignals) : Bool :=
  s.noApplicableRule && s.analogyFails && s.gapPresent

/-- Judicial-lawmaking detection fires only on all three signals. -/
theorem lawmaking_requires_three_true :
    lawmakingFlagged
      { noApplicableRule := true, analogyFails := true, gapPresent := true } = true := rfl
-- [rfl] 置信：三 Bool 字面量合取归约。

/-- Any missing signal blocks the flag in the concrete witness. -/
theorem missing_gap_signal_blocks :
    lawmakingFlagged
      { noApplicableRule := true, analogyFails := true, gapPresent := false } = false := rfl
-- [rfl] 置信：末项 false 直接使合取为 false。

end P065

namespace P066

inductive GapSignal where
  | intentionalGap
  | unintentionalGap
  | ruleConflict
deriving DecidableEq, Repr

/-- Output type contains only detection data; there is no Judgment or Relation field. -/
structure GapDetectionOutput where
  signals : List GapSignal
  detected : Bool
deriving DecidableEq, Repr

def detectGap (signals : List GapSignal) : GapDetectionOutput :=
  match signals with
  | [] => { signals := [], detected := false }
  | _ :: _ => { signals := signals, detected := true }

/-- Positive boundary theorem: detection preserves exactly the input signal roster. -/
theorem gap_detection_preserves_signal_roster (signals : List GapSignal) :
    (detectGap signals).signals = signals := by
  cases signals <;> rfl
-- [cases+rfl] 置信：空/非空两种 List 构造均原样返回 signals。

/-- Nonempty signal input produces only a positive detection bit. -/
theorem gap_signal_detected (s : GapSignal) (ss : List GapSignal) :
    (detectGap (s :: ss)).detected = true := rfl
-- [rfl] 置信：非空 List 构造直接进入 detected=true 分支；输出类型无续造内容槽位。

end P066

namespace P068

inductive LiabilityForm where
  | joint
  | several (shares : List Nat)
  | supplementary
deriving DecidableEq, Repr

def wellFormed : LiabilityForm → Bool
  | .joint => true
  | .supplementary => true
  | .several shares => !shares.isEmpty

/-- Several liability must carry at least one explicit share. -/
theorem several_without_share_invalid :
    wellFormed (.several []) = false := rfl
-- [rfl] 置信：空列表 `isEmpty=true`，取反即 false。

/-- A nonempty share roster is structurally well formed. -/
theorem several_with_share_valid (n : Nat) (ns : List Nat) :
    wellFormed (.several (n :: ns)) = true := rfl
-- [rfl] 置信：非空列表 `isEmpty=false`，取反即 true。

end P068

namespace P070

inductive DamageMeasure where
  | repairCost
  | lostProfit
  | mentalDistress
  | unknown
 deriving DecidableEq, Repr

inductive DamageKind where
  | actual
  | expectation
  | spiritual
 deriving DecidableEq, Repr

def classifyDamage : DamageMeasure → Option DamageKind
  | .repairCost => some .actual
  | .lostProfit => some .expectation
  | .mentalDistress => some .spiritual
  | .unknown => none

/-- Unknown damage measures fail closed. -/
theorem unknown_damage_none : classifyDamage .unknown = none := rfl
-- [rfl] 置信：unknown 构造子直接映射 none。

/-- The three registered measures have total table entries. -/
theorem registered_damage_witness :
    classifyDamage .repairCost = some .actual ∧
    classifyDamage .lostProfit = some .expectation ∧
    classifyDamage .mentalDistress = some .spiritual := by
  decide
-- [decide] 置信：有限枚举查表闭式归约。

end P070

namespace P073

structure DualTrackParams where
  responsibilityLow : Nat
  responsibilityHigh : Nat
  preventionLow : Nat
  preventionHigh : Nat
deriving DecidableEq, Repr

structure DeclaredBand where
  low : Nat
  high : Nat
deriving DecidableEq, Repr

def mergedDeclaration (p : DualTrackParams) : DeclaredBand :=
  let lo := Nat.max p.responsibilityLow p.preventionLow
  let hi := Nat.max (Nat.max p.responsibilityHigh p.preventionHigh) lo
  { low := lo, high := hi }

/-- Tracks merge only in the declaration function and the floor is max of the two floors. -/
theorem declaration_floor_is_max (p : DualTrackParams) :
    (mergedDeclaration p).low = Nat.max p.responsibilityLow p.preventionLow := rfl
-- [rfl] 置信：low 字段就是 let-bound Nat.max。

/-- Concrete witness that the declared ceiling does not fall below the floor. -/
theorem declaration_band_order_witness :
    let b := mergedDeclaration
      { responsibilityLow := 5, responsibilityHigh := 7,
        preventionLow := 8, preventionHigh := 6 }
    b.low ≤ b.high := by
  decide
-- [decide] 置信：闭式 Nat.max 与 ≤ 计算；不引用一般 max 次序引理。

end P073

namespace P074

inductive LegalityVerdict where
  | legal
  | illegal
  | violation
 deriving DecidableEq, Repr

def assessLegality (prohibited : Bool) (unlawful : Option Bool) : LegalityVerdict :=
  match prohibited with
  | true => .illegal
  | false =>
      match unlawful with
      | none => .violation
      | some true => .violation
      | some false => .legal

/-- Prohibition maps to ILLEGAL. -/
theorem prohibited_is_illegal (u : Option Bool) :
    assessLegality true u = .illegal := rfl
-- [rfl] 置信：prohibited=true 首分支直接返回 illegal。

/-- Unknown unlawfulness stays at VIOLATION and never escalates to ILLEGAL. -/
theorem unknown_unlawfulness_is_violation :
    assessLegality false none = .violation := rfl
-- [rfl] 置信：false/none 构造子直接归约。

end P074

namespace P078

structure Band where
  low : Nat
  high : Nat
 deriving DecidableEq, Repr

def mediationIntersection (a b : Band) : Option Band :=
  let lo := Nat.max a.low b.low
  let hi := Nat.min a.high b.high
  if lo ≤ hi then some { low := lo, high := hi } else none

/-- Overlapping ranges produce a nonempty mediation zone. -/
theorem mediation_overlap_witness :
    mediationIntersection { low := 10, high := 30 } { low := 20, high := 40 }
      = some { low := 20, high := 30 } := by
  decide
-- [decide] 置信：Nat.max/min/≤ 均为闭式字面量计算。

/-- Disjoint ranges produce none. -/
theorem mediation_disjoint_witness :
    mediationIntersection { low := 10, high := 15 } { low := 20, high := 30 }
      = none := by
  decide
-- [decide] 置信：交集端点 20≤15 为 false，fail-closed。

end P078

namespace P079

structure SettlementDecision where
  evSettle : Int
  evLitigate : Int
  riskPremium : Int
 deriving DecidableEq, Repr

def acceptSettlement (d : SettlementDecision) : Bool :=
  decide (d.evLitigate - d.riskPremium ≤ d.evSettle)

/-- Concrete witness for EV settlement acceptance. -/
theorem settlement_ev_accept_witness :
    acceptSettlement { evSettle := 80, evLitigate := 100, riskPremium := 25 } = true := by
  decide
-- [decide] 置信：Int 减法与 ≤ 对字面量闭式计算。

/-- Concrete rejection witness. -/
theorem settlement_ev_reject_witness :
    acceptSettlement { evSettle := 70, evLitigate := 100, riskPremium := 20 } = false := by
  decide
-- [decide] 置信：阈值 80≤70 为 false。

end P079

namespace P080

inductive PleaStage where
  | voluntariness
  | factAdmission
  | sentenceProposal
  | courtReview
  | verdict
 deriving DecidableEq, Repr

def nextPleaStage : List PleaStage → Option PleaStage
  | [] => some .voluntariness
  | [.voluntariness] => some .factAdmission
  | [.voluntariness, .factAdmission] => some .sentenceProposal
  | [.voluntariness, .factAdmission, .sentenceProposal] => some .courtReview
  | [.voluntariness, .factAdmission, .sentenceProposal, .courtReview] => some .verdict
  | [.voluntariness, .factAdmission, .sentenceProposal, .courtReview, .verdict] => none
  | _ => none

/-- The fixed five-stage sequence advances one stage at a time. -/
theorem plea_fixed_prefix_advances :
    nextPleaStage [.voluntariness, .factAdmission] = some .sentenceProposal := rfl
-- [rfl] 置信：精确匹配第二个合法前缀模式。

/-- A skipped first stage fails closed. -/
theorem plea_skip_fails_closed :
    nextPleaStage [.factAdmission] = none := rfl
-- [rfl] 置信：不匹配任何合法前缀，进入 wildcard none。

end P080

namespace P081

structure EthicsViolations where
  fraud : Bool
  coercion : Bool
  professionalBoundary : Bool
 deriving DecidableEq, Repr

def tacticPermitted (v : EthicsViolations) : Bool :=
  !(v.fraud || v.coercion || v.professionalBoundary)

/-- Any recorded ethical violation voids the tactic. -/
theorem fraud_voids_tactic (c b : Bool) :
    tacticPermitted { fraud := true, coercion := c, professionalBoundary := b } = false := by
  cases c <;> cases b <;> rfl
-- [cases+rfl] 置信：fraud=true 已使析取恒 true，再取反恒 false。

end P081

namespace P082

structure SuitStrategy where
  preservationNeeded : Bool
  preservationGround : Bool
 deriving DecidableEq, Repr

def feasible (s : SuitStrategy) : Bool :=
  match s.preservationNeeded, s.preservationGround with
  | true, false => false
  | _, _ => true

/-- Preservation requested without a ground is infeasible. -/
theorem preservation_without_ground_infeasible :
    feasible { preservationNeeded := true, preservationGround := false } = false := rfl
-- [rfl] 置信：构造对精确命中唯一拒绝分支。

end P082

namespace P083

structure EvidenceItemEVPI where
  itemId : String
  evpi : Nat
 deriving DecidableEq, Repr

def insertEvpi (x : EvidenceItemEVPI) : List EvidenceItemEVPI → List EvidenceItemEVPI
  | [] => [x]
  | y :: ys =>
      if y.evpi ≤ x.evpi then x :: y :: ys
      else y :: insertEvpi x ys

def sortEvpi : List EvidenceItemEVPI → List EvidenceItemEVPI
  | [] => []
  | x :: xs => insertEvpi x (sortEvpi xs)

/-- Concrete witness: larger EVPI is ordered first. -/
theorem evpi_descending_witness :
    sortEvpi
      [{ itemId := "low", evpi := 1 }, { itemId := "high", evpi := 3 }]
      = [{ itemId := "high", evpi := 3 }, { itemId := "low", evpi := 1 }] := by
  decide
-- [decide] 置信：两元素插入排序只需一次 Nat ≤ 判定。

/-- Concrete witness: equal EVPI preserves insertion order. -/
theorem evpi_tie_stability_witness :
    sortEvpi
      [{ itemId := "first", evpi := 2 }, { itemId := "second", evpi := 2 }]
      = [{ itemId := "first", evpi := 2 }, { itemId := "second", evpi := 2 }] := by
  decide
-- [decide] 置信：相等时 `≤` 为 true，原 head 插在已排 tail 前。

end P083

namespace P084

def appealWorthwhile (probability gain cost : Nat) : Bool :=
  decide (cost < probability * gain)

/-- Concrete positive appeal-EV witness. -/
theorem appeal_ev_positive_witness :
    appealWorthwhile 3 10 20 = true := by
  decide
-- [decide] 置信：20 < 3*10 为闭式 Nat 计算。

/-- Concrete negative appeal-EV witness. -/
theorem appeal_ev_negative_witness :
    appealWorthwhile 2 10 20 = false := by
  decide
-- [decide] 置信：严格不等式 20 < 20 为 false。

end P084

namespace P085

inductive FeeMode where
  | hourly
  | contingency
  | hybrid
 deriving DecidableEq, Repr

def feeQuote (mode : FeeMode) (disclosed : Bool) : Option FeeMode :=
  match disclosed with
  | false => none
  | true => some mode

/-- Undisclosed fee mode cannot produce a quote. -/
theorem undisclosed_fee_none (mode : FeeMode) :
    feeQuote mode false = none := rfl
-- [rfl] 置信：false 分支固定返回 none。

end P085

namespace P086

def expectedFee (winRate feeRate base cap : Nat) : Nat :=
  Nat.min (winRate * feeRate * base) cap

/-- Concrete cap witness. -/
theorem contingency_fee_cap_witness :
    expectedFee 2 3 10 50 = 50 := by
  decide
-- [decide] 置信：min(60,50) 闭式计算。

/-- Concrete uncapped witness. -/
theorem contingency_fee_below_cap_witness :
    expectedFee 1 2 10 50 = 20 := by
  decide
-- [decide] 置信：min(20,50) 闭式计算。

end P086

namespace P087

inductive SameCaseEffect where
  | shouldFollow
  | distinguishedWithReason
 deriving DecidableEq, Repr

def discharge (distinguishingReasonRecorded : Bool) : SameCaseEffect :=
  match distinguishingReasonRecorded with
  | false => .shouldFollow
  | true => .distinguishedWithReason

/-- SHOULD_FOLLOW iff no distinguishing reason is recorded. -/
theorem should_follow_iff_reason_absent (reason : Bool) :
    discharge reason = .shouldFollow ↔ reason = false := by
  cases reason <;> decide
-- [cases+decide] 置信：Bool 两构造子逐一化为真/假命题。

end P087

namespace P089

structure RetrievalDutyRecord where
  searchPerformed : Bool
  reportFiled : Bool
 deriving DecidableEq, Repr

def compliant (r : RetrievalDutyRecord) : Bool :=
  r.searchPerformed && r.reportFiled

/-- Search and report must both be true. -/
theorem retrieval_two_true_compliant :
    compliant { searchPerformed := true, reportFiled := true } = true := rfl
-- [rfl] 置信：Bool 合取字面量归约。

/-- Missing the report is noncompliant. -/
theorem retrieval_missing_report_noncompliant :
    compliant { searchPerformed := true, reportFiled := false } = false := rfl
-- [rfl] 置信：true && false 直接归约为 false。

end P089

end JurisLean.Genealogy.Part4
