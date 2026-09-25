import JurisLean.Genealogy.Part6

namespace JurisLean.Genealogy.TSpectrum

/-!
# TSpectrum Batch 1
T01–T20

口径：
- 每项 T 均建立独立子命名空间；
- 每项均有最小形式载体；
- 每项至少有一条正面 theorem；
- 本批只闭合“结构纪律层”，不把尚未形式化的强语义假装为已证明；
- 禁止 sorry / admit / axiom / native_decide；
- tactic 仅使用白名单中的 rfl / decide / cases / simp / induction；
- 其余证明尽量直接使用项、字段投影和递归子项。
-/


/- ============================================================
   T01
   TermAlgebra.lean::eval_substitution
   ============================================================ -/

namespace T01

inductive Term where
  | atom (code : Nat)
  | plus (left : Term) (right : Term)

structure Substitution where
  mapTerm : Nat → Term

structure Valuation where
  valueOf : Nat → Nat

def applySubstitution (theta : Substitution) : Term → Term
  | .atom code =>
      theta.mapTerm code
  | .plus left right =>
      .plus
        (applySubstitution theta left)
        (applySubstitution theta right)

def eval (nu : Valuation) : Term → Nat
  | .atom code =>
      nu.valueOf code
  | .plus left right =>
      eval nu left + eval nu right

def liftedValuation
    (theta : Substitution)
    (nu : Valuation) : Valuation :=
  {
    valueOf := fun code =>
      eval nu (theta.mapTerm code)
  }

theorem eval_substitution
    (term : Term)
    (theta : Substitution)
    (nu : Valuation) :
    eval nu (applySubstitution theta term) =
      eval (liftedValuation theta nu) term := by
  induction term with
  | atom code =>
      rfl
  | plus left right ihLeft ihRight =>
      simp [
        applySubstitution,
        eval,
        liftedValuation,
        ihLeft,
        ihRight
      ]

/-
降级注：
本定理已经闭合“代入后求值 = 在提升赋值下求值”的结构递归律。

T01 完整陈述仍缺：
1. 多排序/类型化 Term；
2. well-formedness 判定；
3. theta 的保型条件；
4. variable/context typing judgment；
5. substitution 对 binder / capture avoidance 的处理；
6. 对任意语义域而非当前 Nat 解释的泛化。
因此这里不声称已闭合“任意良构保型项”的完整元定理。
-/

end T01


/- ============================================================
   T02
   GroundInstances.lean::finite_ground_instances
   ============================================================ -/

namespace T02

structure FiniteCarrier where
  constantCodes : List Nat

structure GroundingInput where
  predicateCodes : List Nat
  carrier : FiniteCarrier

structure GroundInstance where
  predicateCode : Nat
  constantCode : Nat

def groundInstances
    (input : GroundingInput) : List GroundInstance :=
  input.predicateCodes.flatMap
    (fun predicateCode =>
      input.carrier.constantCodes.map
        (fun constantCode =>
          {
            predicateCode := predicateCode
            constantCode := constantCode
          }))

theorem finite_ground_instances
    (input : GroundingInput) :
    ∃ instances : List GroundInstance,
      instances = groundInstances input :=
  ⟨groundInstances input, rfl⟩

/-
降级注：
有限载体前提没有被删除：
- predicate carrier 是 List；
- constant carrier 是 List；
- groundInstances 的输出仍是 List。

这保证当前结构层不存在“从无限 universe 无条件枚举全部 ground instance”
这一语义偷换。

T02 完整陈述仍缺：
1. predicate arity；
2. 多元 ground tuple；
3. function symbols；
4. Herbrand universe；
5. 每个 sort 的有限性证明；
6. ground instance 与原规则 substitution instance 的双向对应；
7. Finite/Finset 层面的基数上界定理。
-/

end T02


/- ============================================================
   T03
   FiniteMonotoneIteration.lean::iter_subset_of_prefixed
   ============================================================ -/

namespace T03

def State :=
  Nat → Prop

def Subset
    (left : State)
    (right : State) : Prop :=
  ∀ code, left code → right code

def Monotone
    (transformer : State → State) : Prop :=
  ∀ {left right : State},
    Subset left right →
      Subset (transformer left) (transformer right)

structure IterationKernel where
  carrierCodes : List Nat
  transformer : State → State
  monotoneLaw : Monotone transformer

def iterate
    (transformer : State → State) :
    Nat → State → State
  | Nat.zero, initial =>
      initial
  | Nat.succ count, initial =>
      transformer (iterate transformer count initial)

theorem iter_subset_of_prefixed
    (kernel : IterationKernel)
    (count : Nat)
    (initial prefixed : State)
    (initialBound : Subset initial prefixed)
    (prefixedLaw :
      Subset
        (kernel.transformer prefixed)
        prefixed) :
    Subset
      (iterate kernel.transformer count initial)
      prefixed :=
  Nat.rec
    initialBound
    (fun _ previousBound code derivedFact =>
      prefixedLaw
        code
        (kernel.monotoneLaw
          previousBound
          code
          derivedFact))
    count

/-
降级注：
这里已经闭合原内核所需的“前缀点最小性方向”：
若 initial ⊆ prefixed，
且 F(prefixed) ⊆ prefixed，
且 F 单调，
则任意有限轮 F^n(initial) ⊆ prefixed。

T03 完整陈述仍缺：
1. carrierCodes 与 State 支持集之间的封闭关系；
2. 真正有限格而非“附带一个有限代码表”的 State；
3. 稳定轮数上界；
4. fixpoint convergence；
5. least fixed point 的存在与等价刻画；
6. 与原 Horn closure engine 的逐步对应。
-/

end T03


/- ============================================================
   T04
   HornModelBridge.lean::derived_iff_rule_model_entails
   ============================================================ -/

namespace T04

structure ModelBridge where
  derived : Nat → Prop
  ruleModelEntails : Nat → Prop

  soundLaw :
    ∀ code,
      derived code →
        ruleModelEntails code

  completeLaw :
    ∀ code,
      ruleModelEntails code →
        derived code

theorem derived_iff_rule_model_entails
    (bridge : ModelBridge)
    (code : Nat) :
    bridge.derived code ↔
      bridge.ruleModelEntails code :=
  ⟨
    bridge.soundLaw code,
    bridge.completeLaw code
  ⟩

/-
降级注：
结构纪律已经锁死：
“实际推导”和“规则模型后承”必须是两个不同字段，
桥接必须同时提供 soundLaw 与 completeLaw，
不能仅凭名称把两者定义成同一个谓词后宣布等价。

T04 完整陈述仍缺：
1. Horn rule syntax；
2. independent rule-model satisfaction relation；
3. interpretation/model 定义；
4. immediate consequence operator；
5. least model；
6. proof derivation tree；
7. derived ↔ all rule models entail 的完整模型论证明。

因此当前 theorem 是 bridge contract 的定理级载体，
不是完整 Horn completeness theorem。
-/

end T04


/- ============================================================
   T05
   AttackLifting.lean::undercut_defeat_independent_of_preference
   ============================================================ -/

namespace T05

inductive AttackKind where
  | undercut
  | rebuttal

structure DefeatPolicy where
  preference : Nat → Nat → Bool

def defeats
    (policy : DefeatPolicy)
    (attackKind : AttackKind)
    (attacker target : Nat) : Bool :=
  match attackKind with
  | .undercut =>
      true
  | .rebuttal =>
      policy.preference attacker target

theorem undercut_defeat_independent_of_preference
    (firstPolicy secondPolicy : DefeatPolicy)
    (attacker target : Nat) :
    defeats
        firstPolicy
        .undercut
        attacker
        target =
      defeats
        secondPolicy
        .undercut
        attacker
        target :=
  rfl

theorem rebuttal_counterexample :
    defeats
        {
          preference := fun _ _ => true
        }
        .rebuttal
      ≠
    defeats
        {
          preference := fun _ _ => false
        }
        .rebuttal
        1 := by
  decide

/-
降级注：
本项明确选择一种 defeat discipline：
- undercut 一旦成立，其 defeat 不依赖 preference；
- rebuttal 可以依赖 preference。

同时保留了明确反例 rebuttal_counterexample，
所以没有推出“所有 attack 都与 preference 无关”，
也没有虚构无条件满足冲突自由/可接受性/恢复等三公设。

T05 完整陈述仍缺：
1. Argument / Attack graph；
2. premise attack / conclusion attack；
3. undercut 的正式语法判定；
4. preference preorder；
5. lifting operator；
6. Dung semantics；
7. 对三类公设逐项条件化证明和反模型。
-/

end T05


/- ============================================================
   T06
   ReferenceSemantics.lean::transition_origin
   ============================================================ -/

namespace T06

structure LegalState where
  statusCode : Nat

inductive LegalEvent where
  | noChange
  | setStatus (newStatus : Nat)

structure TransitionRule where
  enabled : Bool

def applyEvent
    (state : LegalState)
    (legalEvent : LegalEvent) : LegalState :=
  match legalEvent with
  | .noChange =>
      state
  | .setStatus newStatus =>
      {
        statusCode := newStatus
      }

def transition
    (rule : TransitionRule)
    (legalEvent : LegalEvent)
    (state : LegalState)
    (_computationPhase : Nat) : LegalState :=
  if rule.enabled = true then
    applyEvent state legalEvent
  else
    state

theorem transition_origin
    (rule : TransitionRule)
    (legalEvent : LegalEvent)
    (state : LegalState)
    (firstPhase secondPhase : Nat) :
    transition
        rule
        legalEvent
        state
        firstPhase =
      transition
        rule
        legalEvent
        state
        secondPhase :=
  rfl

/-
降级注：
状态转移只读取：
- 原法律状态；
- 法律事件；
- transition rule。

computationPhase 被明确排除出状态变动原因，
所以单纯“计算跑到另一个阶段”不能制造法律地位变化。

T06 完整陈述仍缺：
1. event history H；
2. rule applicability；
3. jurisdiction/time/version；
4. constitutive rules；
5. 多事件顺序；
6. retrospective/prospective effects；
7. 法律状态与认识状态 K 的严格分离；
8. transition provenance theorem。
-/

end T06


/- ============================================================
   T07
   ExactExpr.lean::eval_exactexpr_denotation
   ============================================================ -/

namespace T07

inductive ExactExpr where
  | literal (value : Nat)
  | add (left : ExactExpr) (right : ExactExpr)
  | mul (left : ExactExpr) (right : ExactExpr)

def denotation : ExactExpr → Nat
  | .literal value =>
      value
  | .add left right =>
      denotation left + denotation right
  | .mul left right =>
      denotation left * denotation right

def evalExact : ExactExpr → Nat
  | .literal value =>
      value
  | .add left right =>
      evalExact left + evalExact right
  | .mul left right =>
      evalExact left * evalExact right

theorem eval_exactexpr_denotation
    (expression : ExactExpr) :
    evalExact expression =
      denotation expression := by
  induction expression with
  | literal value =>
      rfl
  | add left right ihLeft ihRight =>
      simp [
        evalExact,
        denotation,
        ihLeft,
        ihRight
      ]
  | mul left right ihLeft ihRight =>
      simp [
        evalExact,
        denotation,
        ihLeft,
        ihRight
      ]

/-
降级注：
当前已经给 ExactExpr 建立了独立 evaluator / denotation，
并以结构归纳证明二者相同。

T07 完整陈述仍缺：
1. Int/Rat 等精确数域；
2. subtraction/division；
3. domain errors；
4. units；
5. variables/environment；
6. symbolic normalization；
7. overflow-free implementation bridge；
8. 对工程 evaluator 的 refinement proof。
-/

end T07


/- ============================================================
   T08
   DivisionDomain.lean::division_total_iff_domain_empty
   ============================================================ -/

namespace T08

structure DivisionSpec where
  variableCodes : List Nat
  numerator : List Int → Int
  denominator : List Int → Int
  undefinedInputs : List (List Int)

def divisionTotal
    (specification : DivisionSpec) : Prop :=
  specification.undefinedInputs = []

theorem division_total_iff_domain_empty
    (specification : DivisionSpec) :
    divisionTotal specification ↔
      specification.undefinedInputs = [] :=
  Iff.rfl

/-
降级注：
结构纪律：
1. numerator / denominator 接受同一个 valuation vector，
   因而不会偷偷使用不同变量空间；
2. undefinedInputs 是显式定义域异常槽；
3. “total”不能绕过定义域记录，而是定义为 undefinedInputs 为空。

T08 完整陈述仍缺：
1. valuation 长度与 variableCodes 的对应；
2. denominator x = 0 ↔ x ∈ undefinedInputs；
3. 非零分母上的精确 quotient；
4. Rat/field semantics；
5. finite/infinite domain 区分；
6. undefinedInputs 的 completeness；
7. division evaluator 的 progress/preservation。
-/

end T08


/- ============================================================
   T09
   RoundingPolicy.lean::rounding_without_basis_unknown
   ============================================================ -/

namespace T09

inductive RoundingBasis where
  | statute
  | contract
  | accounting
  | custom

structure RoundingPolicy where
  scale : Nat
  roundMode : Nat
  tieMode : Nat
  unitCode : Nat
  stageCode : Nat
  sourceCode : Nat
  basis : Option RoundingBasis

inductive RoundingResult where
  | rounded (value : Int)
  | unknown

def applyRounding
    (policy : RoundingPolicy)
    (value : Int) : RoundingResult :=
  match policy.basis with
  | none =>
      .unknown
  | some _ =>
      .rounded value

theorem rounding_without_basis_unknown
    (policy : RoundingPolicy)
    (value : Int)
    (noBasis : policy.basis = none) :
    applyRounding policy value =
      .unknown := by
  simp [
    applyRounding,
    noBasis
  ]

/-
降级注：
七槽位已经显式存在：
1. scale
2. roundMode
3. tieMode
4. unitCode
5. stageCode
6. sourceCode
7. basis

且 basis 缺失时不能静默采用默认舍入，
只能输出 unknown。

T09 完整陈述仍缺：
1. 七槽位各自的强类型；
2. decimal/rational rounding 算法；
3. tie-breaking；
4. legal basis provenance；
5. 多阶段舍入顺序；
6. 单位转换；
7. round error bound；
8. 每种合法 policy 的计算正确性。
-/

end T09


/- ============================================================
   T10
   TemporalSelection.lean::select_version_unique_or_unknown
   ============================================================ -/

namespace T10

structure Version where
  versionCode : Nat
  effectiveFrom : Nat

inductive SelectionResult where
  | selectedUnique (version : Version)
  | unknown

def selectVersion
    (versions : List Version)
    (eligible : Version → Bool) : SelectionResult :=
  match versions.filter eligible with
  | [version] =>
      .selectedUnique version
  | _ =>
      .unknown

theorem select_version_unique_or_unknown
    (versions : List Version)
    (eligible : Version → Bool) :
    (∃ version,
        selectVersion versions eligible =
          .selectedUnique version) ∨
      selectVersion versions eligible =
        .unknown := by
  cases selectionEquation :
      selectVersion versions eligible with
  | selectedUnique version =>
      simp [selectionEquation]
  | unknown =>
      simp [selectionEquation]

/-
降级注：
selector 不允许在 0 个或多个 candidate 时任意挑一个。
只有恰好一个 eligible version 才输出 selectedUnique；
其余全部降为 unknown。

T10 完整陈述仍缺：
1. effectiveFrom/effectiveTo interval；
2. promulgation/effect/amendment/repeal；
3. temporal fact；
4. legal event time；
5. retroactivity；
6. overlap resolution；
7. version priority；
8. selectedUnique 对“唯一适用规范版本”的法律语义证明。
-/

end T10


/- ============================================================
   T11
   JurisdictionRouting.lean::one_hop_renvoi_terminates
   ============================================================ -/

namespace T11

structure RenvoiRule where
  targetJurisdiction : Option Nat

structure RouteResult where
  jurisdiction : Nat
  hops : Nat

def oneHopRenvoi
    (originJurisdiction : Nat)
    (renvoiRule : RenvoiRule) : RouteResult :=
  match renvoiRule.targetJurisdiction with
  | none =>
      {
        jurisdiction := originJurisdiction
        hops := 0
      }
  | some targetJurisdiction =>
      {
        jurisdiction := targetJurisdiction
        hops := 1
      }

theorem one_hop_renvoi_terminates
    (originJurisdiction : Nat)
    (renvoiRule : RenvoiRule) :
    (oneHopRenvoi
      originJurisdiction
      renvoiRule).hops ≤ 1 := by
  cases targetEquation :
      renvoiRule.targetJurisdiction with
  | none =>
      simp [
        oneHopRenvoi,
        targetEquation
      ]
  | some targetJurisdiction =>
      simp [
        oneHopRenvoi,
        targetEquation
      ]

/-
降级注：
当前 routing operator 的类型结构只允许：
- 0 hop；
- 1 hop。

因此不存在二次递归反致，也不存在循环调用路径。

T11 完整陈述仍缺：
1. jurisdiction graph；
2. choice-of-law rule；
3. renvoi eligibility；
4. remission/transmission 区分；
5. one-hop 后实体法选择；
6. route provenance；
7. 与真实法域冲突规范对应。
-/

end T11


/- ============================================================
   T12
   scoped_override_preserves_unaffected_rules
   ============================================================ -/

namespace T12

structure ScopedRule where
  scopeCode : Nat
  ruleCode : Nat
  payloadCode : Nat

def scopedOverride
    (targetScope : Nat)
    (replacement : ScopedRule)
    (current : ScopedRule) : ScopedRule :=
  if current.scopeCode = targetScope then
    replacement
  else
    current

theorem scoped_override_preserves_unaffected_rules
    (targetScope : Nat)
    (replacement current : ScopedRule)
    (unaffected :
      current.scopeCode ≠ targetScope) :
    scopedOverride
        targetScope
        replacement
        current =
      current := by
  simp [
    scopedOverride,
    unaffected
  ]

/-
降级注：
override 只允许作用于目标 scope。
任何 scopeCode ≠ targetScope 的规则保持原值。

T12 完整陈述仍缺：
1. hierarchical scope；
2. rule identity；
3. replacement compatibility；
4. precedence；
5. multiple overrides；
6. override composition；
7. semantic equivalence of all unaffected derivations。
-/

end T12


/- ============================================================
   T13
   ParallelJurisdictions.lean::parallel_projection
   ============================================================ -/

namespace T13

structure JurisdictionResult where
  valueCode : Nat

def ParallelState :=
  Nat → JurisdictionResult

def parallelUpdate
    (state : ParallelState)
    (targetJurisdiction : Nat)
    (newResult : JurisdictionResult) :
    ParallelState :=
  fun jurisdiction =>
    if jurisdiction = targetJurisdiction then
      newResult
    else
      state jurisdiction

def parallelProjection
    (state : ParallelState)
    (jurisdiction : Nat) :
    JurisdictionResult :=
  state jurisdiction

theorem parallel_projection
    (state : ParallelState)
    (targetJurisdiction observedJurisdiction : Nat)
    (newResult : JurisdictionResult)
    (distinctJurisdictions :
      observedJurisdiction ≠ targetJurisdiction) :
    parallelProjection
        (parallelUpdate
          state
          targetJurisdiction
          newResult)
        observedJurisdiction =
      parallelProjection
        state
        observedJurisdiction := by
  simp [
    parallelProjection,
    parallelUpdate,
    distinctJurisdictions
  ]

/-
降级注：
修改一个 jurisdiction branch，
不会改变另一 jurisdiction 的 projection。

T13 完整陈述仍缺：
1. jurisdiction-qualified facts；
2. jurisdiction-qualified rules；
3. parallel derivation；
4. conflict/non-merging discipline；
5. cross-jurisdiction reference；
6. merge operator；
7. provenance separation；
8. 整个推导闭包的非干扰定理。
-/

end T13


/- ============================================================
   T14
   ComplianceOrder.lean::strictest_is_join
   ============================================================ -/

namespace T14

def ComplianceProfile :=
  Nat → Prop

/-
ComplianceLe left right：
right 所允许的每项也必须被 left 允许。

因此顺序方向设计为：
越严格的 profile 越“高”。

在这一顺序下，
两个允许集合的交集是 join。
-/
def ComplianceLe
    (left right : ComplianceProfile) : Prop :=
  ∀ item,
    right item →
      left item

def strictest
    (left right : ComplianceProfile) :
    ComplianceProfile :=
  fun item =>
    left item ∧ right item

structure JoinWitness
    (left right joined : ComplianceProfile) where

  leftLe :
    ComplianceLe left joined

  rightLe :
    ComplianceLe right joined

  universalLaw :
    ∀ candidate,
      ComplianceLe left candidate →
      ComplianceLe right candidate →
        ComplianceLe joined candidate

theorem strictest_is_join
    (left right : ComplianceProfile) :
    JoinWitness
      left
      right
      (strictest left right) :=
  {
    leftLe :=
      fun _ joinedProof =>
        joinedProof.1

    rightLe :=
      fun _ joinedProof =>
        joinedProof.2

    universalLaw :=
      fun _ leftBound rightBound item candidateProof =>
        ⟨
          leftBound item candidateProof,
          rightBound item candidateProof
        ⟩
  }

/-
降级注：
这里已经明确给出：
- order；
- strictest operator；
- 两个 upper-bound 条件；
- universal property。

因此“从严 = join”不是口号，而是当前 order 下的结构定理。

T14 完整陈述仍缺：
1. reflexive/transitive/antisymmetric；
2. quotient 后 partial order；
3. arbitrary joins；
4. legal requirement semantics；
5. conflict/inconsistency；
6. obligation/prohibition/permission 多模态组合；
7. 空交/不可满足 profile 的法律语义。
-/

end T14


/- ============================================================
   T15
   PredicateQuotient.lean::truth_vector_bisimulation
   ============================================================ -/

namespace T15

structure BState where
  bVector : List Bool

def BEquivalent
    (left right : BState) : Prop :=
  left.bVector = right.bVector

structure BSystem where
  step : BState → BState

  preservesB :
    ∀ left right,
      BEquivalent left right →
        BEquivalent
          (step left)
          (step right)

structure BisimulationWitness
    (system : BSystem)
    (left right : BState) : Prop where

  currentEquivalent :
    BEquivalent left right

  nextEquivalent :
    BEquivalent
      (system.step left)
      (system.step right)

theorem truth_vector_bisimulation
    (system : BSystem)
    (left right : BState)
    (equivalent :
      BEquivalent left right) :
    BisimulationWitness
      system
      left
      right :=
  {
    currentEquivalent :=
      equivalent

    nextEquivalent :=
      system.preservesB
        left
        right
        equivalent
  }

/-
降级注：
bVector 相等被正式登记为 quotient observation；
系统还必须显式提供 preservesB，
才能从当前等价推出一步后的等价。

所以不能仅因“两个对象当前 b 向量相同”
就无条件宣布未来行为相同。

T15 完整陈述仍缺：
1. predicate universe；
2. quotient relation 的 equivalence proof；
3. transition relation 而非 deterministic step；
4. forth/back 双向条件；
5. coinductive bisimulation；
6. quotient transition well-defined；
7. arbitrary trace preservation；
8. 与原法律 predicate semantics 的对应。
-/

end T15


/- ============================================================
   T16
   AFMC.lean::check_af_sound
   ============================================================ -/

namespace T16

structure SCCSummary where
  hasLeast : Bool
  hasGreatest : Bool

def checkAF
    (summary : SCCSummary) : Bool :=
  !(summary.hasLeast && summary.hasGreatest)

def AlternationFree
    (summary : SCCSummary) : Prop :=
  checkAF summary = true

theorem check_af_sound
    (summary : SCCSummary)
    (accepted :
      checkAF summary = true) :
    AlternationFree summary :=
  accepted

/-
降级注：
这里先锁定 checker/soundness contract：
checkAF = true 的对象一定满足当前定义的 AlternationFree predicate。

并且 checker 至少明确拒绝
“同一 SCC 同时含 least 与 greatest”这一结构摘要。

T16 完整陈述仍缺：
1. μ-calculus formula AST；
2. variable dependency graph；
3. SCC computation；
4. μ/ν binding；
5. alternation depth；
6. 当前 SCCSummary 与真实公式 SCC 的抽取正确性；
7. semantic model checking；
8. “checker true → 真实 AF fragment”完整 soundness。
因此本条只是 checker contract 层，未假装完成 AFMC 文献级证明。
-/

end T16


/- ============================================================
   T17
   DateAnchors.lean::anchor_selected_by_rule
   ============================================================ -/

namespace T17

inductive AnchorKind where
  | occurrence
  | knowledge
  | filing

structure DateAnchors where
  occurrenceDate : Nat
  knowledgeDate : Nat
  filingDate : Nat

structure AnchorRule where
  anchorKind : AnchorKind

def anchorValue
    (anchors : DateAnchors)
    (anchorKind : AnchorKind) : Nat :=
  match anchorKind with
  | .occurrence =>
      anchors.occurrenceDate
  | .knowledge =>
      anchors.knowledgeDate
  | .filing =>
      anchors.filingDate

def selectAnchor
    (anchorRule : AnchorRule)
    (anchors : DateAnchors) : Nat :=
  anchorValue
    anchors
    anchorRule.anchorKind

theorem anchor_selected_by_rule
    (anchorRule : AnchorRule)
    (anchors : DateAnchors) :
    selectAnchor anchorRule anchors =
      anchorValue
        anchors
        anchorRule.anchorKind :=
  rfl

/-
降级注：
起算锚不能由计算器自行猜测；
selector 只能读取 rule.anchorKind。

T17 完整陈述仍缺：
1. 日期强类型；
2. event history；
3. 多候选事实；
4. knowledge 的事实认定；
5. occurrence/completion/discovery 等更多锚；
6. anchor rule 的法源；
7. conflict resolution；
8. “某法律规则依法选中某实际日期”的实体法证明。
-/

end T17


/- ============================================================
   T18
   PeriodMatrix.lean::period_effect_bound_to_kind
   ============================================================ -/

namespace T18

inductive PeriodKind where
  | limitation
  | repose
  | procedural

inductive PeriodEffect where
  | defenseBar
  | rightExtinction
  | processBar

structure PeriodSpec where
  periodKind : PeriodKind
  lengthDays : Nat

def effectForKind :
    PeriodKind → PeriodEffect
  | .limitation =>
      .defenseBar
  | .repose =>
      .rightExtinction
  | .procedural =>
      .processBar

def periodEffect
    (specification : PeriodSpec) :
    PeriodEffect :=
  effectForKind
    specification.periodKind

theorem period_effect_bound_to_kind
    (specification : PeriodSpec) :
    periodEffect specification =
      effectForKind
        specification.periodKind :=
  rfl

/-
降级注：
effect 不作为任意可写字段存入 PeriodSpec；
它只能由 periodKind 派生。
因此不能构造“类型是 limitation、效果却随意填 rightExtinction”
这一类结构错配。

T18 完整陈述仍缺：
1. 中国法真实期间类型全集；
2. limitation/repose/procedural 的法域化定义；
3. suspension/interruption/extension；
4. court invocation；
5. party invocation；
6. expiry semantics；
7. 各种 kind→effect 映射的实体法法源证明。

当前三类映射只是结构示范，
不声称三种英文标签已穷尽中国法期间制度。
-/

end T18


/- ============================================================
   T19
   ExactConstructors.lean::progressive_and_multiplier_correct
   ============================================================ -/

namespace T19

structure ExactConstructorInput where
  baseAmount : Nat
  steps : List Nat
  multiplierFactor : Nat

def progressive : List Nat → Nat
  | [] =>
  | step :: remaining =>
      step + progressive remaining

def progressiveAmount
    (input : ExactConstructorInput) : Nat :=
  input.baseAmount +
    progressive input.steps

def multipliedAmount
    (input : ExactConstructorInput) : Nat :=
  progressiveAmount input *
    input.multiplierFactor

theorem progressive_and_multiplier_correct
    (input : ExactConstructorInput) :
    progressiveAmount input =
        input.baseAmount +
          progressive input.steps
      ∧
    multipliedAmount input =
        (input.baseAmount +
          progressive input.steps) *
            input.multiplierFactor :=
  ⟨rfl, rfl⟩

/-
降级注：
本条先把两个 constructor 的解释锁死：
1. progressive constructor = base + steps 的结构累加；
2. multiplier constructor = progressive 结果 × multiplierFactor。

T19 完整陈述仍缺：
1. 真正分段区间；
2. threshold；
3. marginal rate；
4. fixed deduction；
5. Rat/decimal；
6. progressive tariff 的分段正确性；
7. multiplier 与法定基数、封顶/保底的结合；
8. 对具体赔偿/利息/费用规则的 law-specific correctness。
-/

end T19


/- ============================================================
   T20
   DecisionTables.lean::route_and_exclusion_sound
   ============================================================ -/

namespace T20

structure DecisionRow
    (Input Output : Type) where
  condition : Input → Prop
  exclusion : Input → Prop
  output : Output

structure RouteCertificate
    (Input Output : Type)
    (table : List (DecisionRow Input Output))
    (input : Input) where

  row : DecisionRow Input Output

  rowInTable :
    row ∈ table

  conditionHolds :
    row.condition input

  exclusionClear :
    ¬ row.exclusion input

def route
    {Input Output : Type}
    {table : List (DecisionRow Input Output)}
    {input : Input}
    (certificate :
      RouteCertificate
        Input
        Output
        table
        input) :
    Output :=
  certificate.row.output

theorem route_and_exclusion_sound
    {Input Output : Type}
    {table : List (DecisionRow Input Output)}
    {input : Input}
    (certificate :
      RouteCertificate
        Input
        Output
        table
        input) :
    route certificate =
        certificate.row.output
      ∧
    certificate.row ∈ table
      ∧
    certificate.row.condition input
      ∧
    ¬ certificate.row.exclusion input :=
  ⟨
    rfl,
    ⟨
      certificate.rowInTable,
      ⟨
        certificate.conditionHolds,
        certificate.exclusionClear
      ⟩
    ⟩
  ⟩

/-
降级注：
route 结果必须附着于 certificate：
- row 确实属于 decision table；
- positive condition 成立；
- exclusion 不成立；
- 输出只能来自该 certified row。

因此“命中正向条件但同时位于负向清单”
不能取得合法 RouteCertificate。

T20 完整陈述仍缺：
1. 自动 table traversal；
2. row priority；
3. multi-match conflict；
4. no-match UNKNOWN；
5. condition decidability；
6. exclusion checker；
7. 自动 router 生成 certificate 的 completeness；
8. 对具体法律决策表的实体语义 soundness。
-/

end T20


/- ============================================================
   Batch 1 self-check
   ============================================================

A. 新标识符关键字冲突检查

T01:
Term
atom
plus
Substitution
mapTerm
Valuation
valueOf
applySubstitution
eval
liftedValuation
eval_substitution

T02:
FiniteCarrier
constantCodes
GroundingInput
predicateCodes
carrier
GroundInstance
predicateCode
constantCode
groundInstances
finite_ground_instances

T03:
State
Subset
Monotone
IterationKernel
carrierCodes
transformer
monotoneLaw
iterate
iter_subset_of_prefixed

T04:
ModelBridge
derived
ruleModelEntails
soundLaw
completeLaw
derived_iff_rule_model_entails

T05:
AttackKind
undercut
rebuttal
DefeatPolicy
preference
defeats
undercut_defeat_independent_of_preference
rebuttal_counterexample

T06:
LegalState
statusCode
LegalEvent
noChange
setStatus
TransitionRule
enabled
applyEvent
transition
transition_origin

T07:
ExactExpr
literal
add
mul
denotation
evalExact
eval_exactexpr_denotation

T08:
DivisionSpec
variableCodes
numerator
denominator
undefinedInputs
divisionTotal
division_total_iff_domain_empty

T09:
RoundingBasis
statute
contract
accounting
custom
RoundingPolicy
scale
roundMode
tieMode
unitCode
stageCode
sourceCode
basis
RoundingResult
rounded
unknown
applyRounding
rounding_without_basis_unknown

T10:
Version
versionCode
effectiveFrom
SelectionResult
selectedUnique
unknown
selectVersion
select_version_unique_or_unknown

T11:
RenvoiRule
targetJurisdiction
RouteResult
jurisdiction
hops
oneHopRenvoi
one_hop_renvoi_terminates

T12:
ScopedRule
scopeCode
ruleCode
payloadCode
scopedOverride
scoped_override_preserves_unaffected_rules

T13:
JurisdictionResult
valueCode
ParallelState
parallelUpdate
parallelProjection
parallel_projection

T14:
ComplianceProfile
ComplianceLe
strictest
JoinWitness
leftLe
rightLe
universalLaw
strictest_is_join

T15:
BState
bVector
BEquivalent
BSystem
step
preservesB
BisimulationWitness
currentEquivalent
nextEquivalent
truth_vector_bisimulation

T16:
SCCSummary
hasLeast
hasGreatest
checkAF
AlternationFree
check_af_sound

T17:
AnchorKind
occurrence
knowledge
filing
DateAnchors
occurrenceDate
knowledgeDate
filingDate
AnchorRule
anchorKind
anchorValue
selectAnchor
anchor_selected_by_rule

T18:
PeriodKind
limitation
repose
procedural
PeriodEffect
defenseBar
rightExtinction
processBar
PeriodSpec
periodKind
lengthDays
effectForKind
periodEffect
period_effect_bound_to_kind

T19:
ExactConstructorInput
baseAmount
steps
multiplierFactor
progressive
progressiveAmount
multipliedAmount
progressive_and_multiplier_correct

T20:
DecisionRow
condition
exclusion
output
RouteCertificate
row
rowInTable
conditionHolds
exclusionClear
route
route_and_exclusion_sound

检查结果：
上述新声明名及构造子名未使用以下 Lean 关键字作为标识符：
partial
match
abbrev
deriving
decide
open
end
namespace
variable
theorem
def
lemma
example
structure
inductive
instance
with
where
if
then
else
let
in
do
return
class

代码中出现的 `match` / `if` / `inductive` / `structure` 等仅作为语法关键字，
没有作为构造子或字段名。

B. tactic 白名单检查

实际 tactic 使用：
- induction
- simp
- cases
- decide

另有：
- rfl 作为证明项；
- Iff.rfl；
- Nat.rec；
- 函数项应用；
- structure 字段投影；
- And / Or / Exists 的直接项构造。

未使用：
intro
exact
apply
constructor
aesop
tauto
omega
linarith
nlinarith
norm_num
ring
ring_nf
simp_all
simpa
subst
contradiction
by_contra
by_cases
funext
ext
rcases
obtain
specialize
have
rw
native_decide
sorry
admit
axiom

C. 九轮 CI 三类教训专项检查

1. 无 `simp only`；
2. 无 dite；
3. 无 if-decide 组合；
4. T12/T13 的 ite 均直接以 Prop equality 为条件并交给完整 `simp`；
5. 未把 Lean 关键字作为 constructor / field / def 名；
6. T10/T11 的分支证明使用 `cases` + 完整 `simp`；
7. 未依赖 if_pos / if_neg / dite_eq 等形状敏感引理。

D. Mathlib 不确定引用检查

没有引用任何不确定 Mathlib 定理名。

实际依赖的具名基础对象只有：
- Nat
- Int
- Bool
- Option
- List
- List.map
- List.flatMap
- List.filter
- List.Mem / `∈`
- Nat.rec
- Iff.rfl

其余证明由定义展开、递归、字段投影、simp/cases/induction/decide 完成。

E. 禁止项检查

全文：
- 0 × sorry
- 0 × admit
- 0 × axiom
- 0 × native_decide

F. 本批闭合口径

T01–T20：
20 / 20 均已有 theorem-level carrier。
20 / 20 均无 OPEN 占位。
20 / 20 均显式写明完整 T 陈述尚缺的升级条件。

这里的“无 OPEN”仅指：
本轮要求的结构纪律层 theorem carrier 已全部给出；
不等于降级注中列出的文献级、模型论级、实体法律语义级命题已经证明。
-/

end JurisLean.Genealogy.TSpectrum