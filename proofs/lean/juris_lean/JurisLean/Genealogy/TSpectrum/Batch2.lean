import JurisLean.Genealogy.TSpectrum.Batch1

namespace JurisLean.Genealogy.TSpectrum

/-!
# TSpectrum Batch 2
T21–T40

本批继续采用结构纪律层口径：
- 每个 T 独立子命名空间；
- 每项建立最小形式载体；
- 每项至少一条正面 theorem；
- 不把结构层 theorem 冒充完整文献级/实体法级证明；
- 禁止 sorry / admit / axiom / native_decide；
- tactic 限定在既定白名单。
-/


/- ============================================================
   T21
   利息分段累计精化
   IntLi 分段利率 → 分段和 = 整段和
   ============================================================ -/

namespace T21

structure InterestSlice where
  principal : Int
  rateFactor : Int
  durationFactor : Int

def sliceInterest
    (slice : InterestSlice) : Int :=
  slice.principal *
    slice.rateFactor *
      slice.durationFactor

def segmentedInterest :
    List InterestSlice → Int
  | [] =>
  | slice :: remaining =>
      sliceInterest slice +
        segmentedInterest remaining

theorem interest_segment_refinement
    (left right : List InterestSlice) :
    segmentedInterest (left ++ right) =
      segmentedInterest left +
        segmentedInterest right := by
  induction left with
  | nil =>
      simp [segmentedInterest]
  | cons head tail inductionHypothesis =>
      simp [segmentedInterest] at inductionHypothesis ⊢
      omega

/-
降级注：

已闭合：
对任意两个利息分段列表 left/right，
将其拼接后整体累计，与分别累计后求和相同。

这给出了 IntLi 分段累计的加法精化骨架，
并且不是只证明固定两段，而是对任意 List 归纳。

T21 完整陈述仍缺：
1. 利率采用 Rat/百分比的真实精确表示；
2. 日利率、年利率及计息基准转换；
3. 起止日期与实际计息天数；
4. 分段边界无重叠、无遗漏；
5. 本金变化；
6. 停息/复息规则；
7. 分段计划与“未分段整段公式”之间的实体数学等价条件；
8. 与具体 IntLi 工程实现的 refinement bridge。
-/

end T21


/- ============================================================
   T22
   支付抵充守恒
   任意付款 × 任意债务列表归纳
   ============================================================ -/

namespace T22

def residualPayment :
    List Nat → Nat → Nat
  | [], payment =>
      payment
  | debt :: remaining, payment =>
      residualPayment
        remaining
        (payment - debt)

def appliedPayment
    (debts : List Nat)
    (payment : Nat) : Nat :=
  payment -
    residualPayment debts payment

theorem residual_payment_le
    (debts : List Nat) :
    ∀ payment : Nat,
      residualPayment debts payment ≤ payment :=
  List.rec
    (fun payment => by
      simp [residualPayment])
    (fun debt remaining inductionHypothesis payment => by
      have tailBound :
          residualPayment
              remaining
              (payment - debt) ≤
            payment - debt :=
        inductionHypothesis
          (payment - debt)

      simp [residualPayment]
      omega)
    debts

theorem payment_offset_conservation
    (debts : List Nat)
    (payment : Nat) :
    appliedPayment debts payment +
        residualPayment debts payment =
      payment := by
  have residualBound :
      residualPayment debts payment ≤ payment :=
    residual_payment_le debts payment

  simp [appliedPayment]
  omega

/-
降级注：

已闭合：
对任意 Nat payment 和任意 List Nat debts，
递归抵充后：

    已抵充付款 + 未抵充付款 = 原始付款。

证明不是固定长度展开，而是对任意债务列表成立。

T22 完整陈述仍缺：
1. 每一笔债务的剩余余额列表；
2. 部分抵充后的逐债务更新；
3. 本金/利息/费用等债务类型；
4. 指定抵充与法定抵充顺序；
5. payment ≤ / > 总债务两类行为的完整输出；
6. “债务减少量 = appliedPayment”的第二守恒式；
7. 金额从 Nat 升级到精确货币域；
8. 与实际 payment allocator 的 refinement proof。
-/

end T22


/- ============================================================
   T23
   固定方案守恒
   瀑布总额 = 输入
   ============================================================ -/

namespace T23

def trancheTotal :
    List Nat → Nat
  | [] =>
  | amount :: remaining =>
      amount +
        trancheTotal remaining

structure FixedWaterfallPlan where
  inputAmount : Nat
  tranches : List Nat

  conservationLaw :
    trancheTotal tranches =
      inputAmount

def waterfallTotal
    (plan : FixedWaterfallPlan) : Nat :=
  trancheTotal plan.tranches

theorem fixed_scheme_conservation
    (plan : FixedWaterfallPlan) :
    waterfallTotal plan =
      plan.inputAmount := by
  simp [
    waterfallTotal,
    plan.conservationLaw
  ]

/-
降级注：

固定方案的守恒不是事后猜测：
FixedWaterfallPlan 本身必须携带 conservationLaw。

因此一个总 tranche 金额与 inputAmount 不一致的固定方案，
不能取得合法的 FixedWaterfallPlan 证明载体。

T23 完整陈述仍缺：
1. 自动生成 tranche；
2. cap/floor；
3. 优先顺位；
4. 余款；
5. 不足额情形；
6. 金额精确域；
7. 动态 waterfall；
8. 由工程输入自动验证 conservationLaw。
-/

end T23


/- ============================================================
   T24
   资产池不重复消费
   ============================================================ -/

namespace T24

structure AssetPoolLedger where
  consumedBy :
    Nat → Option Nat

def AssetConsumedBy
    (ledger : AssetPoolLedger)
    (assetCode consumerCode : Nat) : Prop :=
  ledger.consumedBy assetCode =
    some consumerCode

theorem asset_pool_no_duplicate_consumption
    (ledger : AssetPoolLedger)
    (assetCode firstConsumer secondConsumer : Nat)
    (firstConsumption :
      AssetConsumedBy
        ledger
        assetCode
        firstConsumer)
    (secondConsumption :
      AssetConsumedBy
        ledger
        assetCode
        secondConsumer) :
    firstConsumer =
      secondConsumer := by
  have sameOwner :
      (some firstConsumer : Option Nat) =
        some secondConsumer :=
    firstConsumption.symm.trans
      secondConsumption

  cases sameOwner
  rfl

/-
降级注：

consumedBy 的类型是：

    asset → Option consumer

而不是：

    asset → List consumer

因此在同一 ledger 状态中，
一个 asset 不可能同时拥有两个不同消费主体。

T24 完整陈述仍缺：
1. consume transition；
2. 未消费→已消费状态变化；
3. transaction history；
4. 并发写入；
5. rollback；
6. partial consumption；
7. 可分割资产；
8. 整个 execution trace 上的全局 no-double-spend 定理。
-/

end T24


/- ============================================================
   T25
   顺位瀑布单调
   高顺位 → 低顺位不增
   ============================================================ -/

namespace T25

structure PriorityWaterfall where
  allocations : List Nat

  adjacentMonotone :
    ∀ higher lower remaining,
      allocations =
        higher :: lower :: remaining →
      lower ≤ higher

theorem priority_waterfall_monotone
    (waterfall : PriorityWaterfall)
    (higher lower : Nat)
    (remaining : List Nat)
    (shape :
      waterfall.allocations =
        higher :: lower :: remaining) :
    lower ≤ higher :=
  waterfall.adjacentMonotone
    higher
    lower
    remaining
    shape

/-
降级注：

已锁定相邻顺位纪律：

    higher allocation ≥ lower allocation。

任何声称自己是 PriorityWaterfall 的对象，
必须提供 adjacentMonotone 见证。

T25 完整陈述仍缺：
1. 全部非相邻顺位 i < j → allocation[j] ≤ allocation[i]；
2. rank 类型；
3. 同顺位并列；
4. 可用资产总量约束；
5. waterfall allocator；
6. 瀑布不足额传播；
7. 优先权法律来源；
8. 从 allocator 算法自动推出单调性的实现证明。
-/

end T25


/- ============================================================
   T26
   执行中断恢复检查点
   中断/恢复不丢检查点
   ============================================================ -/

namespace T26

structure Checkpoint where
  cursorCode : Nat
  payloadCode : Nat

structure RuntimeState where
  checkpoint : Checkpoint
  phaseCode : Nat

def interrupt
    (state : RuntimeState) :
    Checkpoint :=
  state.checkpoint

def resume
    (checkpoint : Checkpoint) :
    RuntimeState :=
  {
    checkpoint := checkpoint
    phaseCode := 0
  }

theorem interruption_resume_preserves_checkpoint
    (state : RuntimeState) :
    interrupt
        (resume
          (interrupt state)) =
      interrupt state :=
  rfl

/-
降级注：

已闭合最基础 checkpoint preservation：

    interrupt
      → resume
      → interrupt

得到完全相同的 checkpoint。

运行阶段 phaseCode 可以重新建立，
但 checkpoint 本身不得被重算或丢失。

T26 完整陈述仍缺：
1. execution stack；
2. pending work；
3. result cache；
4. deterministic replay；
5. 多检查点；
6. crash persistence；
7. resume 后后续执行与未中断执行的 trace equivalence；
8. side-effect exactly-once 语义。
-/

end T26


/- ============================================================
   T27
   规则四闸准入
   准入必带四见证
   ============================================================ -/

namespace T27

structure FourGateWitness where
  sourceGate : Prop
  scopeGate : Prop
  temporalGate : Prop
  semanticGate : Prop

  sourceWitness :
    sourceGate

  scopeWitness :
    scopeGate

  temporalWitness :
    temporalGate

  semanticWitness :
    semanticGate

structure AdmittedRule where
  ruleCode : Nat
  gates : FourGateWitness

theorem admitted_rule_has_four_witnesses
    (rule : AdmittedRule) :
    rule.gates.sourceGate ∧
      rule.gates.scopeGate ∧
      rule.gates.temporalGate ∧
      rule.gates.semanticGate :=
  ⟨
    rule.gates.sourceWitness,
    ⟨
      rule.gates.scopeWitness,
      ⟨
        rule.gates.temporalWitness,
        rule.gates.semanticWitness
      ⟩
    ⟩
  ⟩

/-
降级注：

AdmittedRule 不能只保存一个 admitted = true。

合法准入对象必须同时携带四个独立证明见证：
1. source；
2. scope；
3. temporal；
4. semantic。

因此准入结果具有 proof-carrying 结构。

T27 完整陈述仍缺：
1. 四闸的具体 predicate；
2. source hierarchy；
3. jurisdiction scope；
4. temporal validity；
5. semantic compatibility；
6. 自动准入算法；
7. rejection reason；
8. algorithm → witness 的 soundness/completeness。
-/

end T27


/- ============================================================
   T28
   编译结构保持
   AST → 执行语义保构
   ============================================================ -/

namespace T28

inductive SourceAst where
  | literalNode (value : Nat)
  | addNode
      (left : SourceAst)
      (right : SourceAst)

inductive RuntimeAst where
  | runtimeLiteral (value : Nat)
  | runtimeAdd
      (left : RuntimeAst)
      (right : RuntimeAst)

def compileAst :
    SourceAst → RuntimeAst
  | .literalNode value =>
      .runtimeLiteral value
  | .addNode left right =>
      .runtimeAdd
        (compileAst left)
        (compileAst right)

def sourceDenotation :
    SourceAst → Nat
  | .literalNode value =>
      value
  | .addNode left right =>
      sourceDenotation left +
        sourceDenotation right

def runtimeDenotation :
    RuntimeAst → Nat
  | .runtimeLiteral value =>
      value
  | .runtimeAdd left right =>
      runtimeDenotation left +
        runtimeDenotation right

theorem compile_structure_preserving
    (source : SourceAst) :
    runtimeDenotation
        (compileAst source) =
      sourceDenotation source := by
  induction source with
  | literalNode value =>
      rfl
  | addNode left right leftHypothesis rightHypothesis =>
      simp [
        compileAst,
        sourceDenotation,
        runtimeDenotation,
        leftHypothesis,
        rightHypothesis
      ]

/-
降级注：

已经证明一个真正的结构归纳编译正确性骨架：

    eval_runtime(compile(ast))
      =
    eval_source(ast)。

T28 完整陈述仍缺：
1. 实际法律 AST；
2. predicate/rule/modal node；
3. variables；
4. environments；
5. type preservation；
6. rule priority；
7. failure/UNKNOWN；
8. compiler optimization；
9. 实际执行引擎语义；
10. 原工程 compiler 的 refinement。
-/

end T28


/- ============================================================
   T29
   多法域求值
   evaluate_multi_contract
   ============================================================ -/

namespace T29

structure JurisdictionContract where
  jurisdictionCode : Nat
  evaluator :
    Nat → Nat

structure EvaluationResult where
  jurisdictionCode : Nat
  value : Nat

def evaluateContract
    (contract : JurisdictionContract)
    (inputValue : Nat) :
    EvaluationResult :=
  {
    jurisdictionCode :=
      contract.jurisdictionCode

    value :=
      contract.evaluator inputValue
  }

def evaluateMultiContract :
    List JurisdictionContract →
      Nat →
        List EvaluationResult
  | [], _ =>
      []
  | contract :: remaining, inputValue =>
      evaluateContract
          contract
          inputValue
        ::
      evaluateMultiContract
        remaining
        inputValue

theorem evaluate_multi_contract
    (contract : JurisdictionContract)
    (remaining : List JurisdictionContract)
    (inputValue : Nat) :
    evaluateMultiContract
        (contract :: remaining)
        inputValue =
      evaluateContract
          contract
          inputValue
        ::
      evaluateMultiContract
        remaining
        inputValue :=
  rfl

/-
降级注：

multi-contract evaluator 的递归结构已经固定：

每个 jurisdiction contract 独立调用自身 evaluator，
结果按合同列表逐项产生，
而不是先把法域规则混成一个 evaluator 再求值。

T29 完整陈述仍缺：
1. 输入事实的 jurisdiction projection；
2. 共享事实与法域特有事实；
3. 输出 provenance；
4. jurisdiction collision；
5. parallel execution；
6. 每一项结果对单法域 evaluator 的全列表 membership theorem；
7. 与实际 evaluate_multi_contract 工程接口的 refinement。
-/

end T29


/- ============================================================
   T30
   版本包隔离
   ============================================================ -/

namespace T30

structure VersionPackage where
  versionCode : Nat
  payloadCode : Nat

def PackageStore :=
  Nat → VersionPackage

def replaceVersionPackage
    (store : PackageStore)
    (targetVersion : Nat)
    (replacement : VersionPackage) :
    PackageStore :=
  fun queriedVersion =>
    if queriedVersion = targetVersion then
      replacement
    else
      store queriedVersion

theorem version_package_isolation
    (store : PackageStore)
    (targetVersion observedVersion : Nat)
    (replacement : VersionPackage)
    (differentVersion :
      observedVersion ≠ targetVersion) :
    replaceVersionPackage
        store
        targetVersion
        replacement
        observedVersion =
      store observedVersion := by
  simp [
    replaceVersionPackage,
    differentVersion
  ]

/-
降级注：

更新 targetVersion 时，
任意 observedVersion ≠ targetVersion 的包保持不变。

这是版本包非干扰性的结构层定理。

T30 完整陈述仍缺：
1. package content map；
2. schema version；
3. dependency package；
4. atomic replacement；
5. rollback；
6. package hash；
7. cross-version reference 禁止规则；
8. 整个 evaluator 对旧版本结果的 observational non-interference。
-/

end T30


/- ============================================================
   T31
   记录覆盖审计
   ============================================================ -/

namespace T31

structure RecordValue where
  stateCode : Nat

structure AuditEntry where
  recordCode : Nat
  oldStateCode : Nat
  newStateCode : Nat

structure OverrideResult where
  updatedRecord : RecordValue
  auditEntry : AuditEntry

def overrideRecord
    (recordCode : Nat)
    (current : RecordValue)
    (newStateCode : Nat) :
    OverrideResult :=
  {
    updatedRecord :=
      {
        stateCode := newStateCode
      }

    auditEntry :=
      {
        recordCode := recordCode
        oldStateCode := current.stateCode
        newStateCode := newStateCode
      }
  }

theorem record_override_audit
    (recordCode : Nat)
    (current : RecordValue)
    (newStateCode : Nat) :
    (overrideRecord
        recordCode
        current
        newStateCode).updatedRecord.stateCode =
        newStateCode
      ∧
    (overrideRecord
        recordCode
        current
        newStateCode).auditEntry.recordCode =
        recordCode
      ∧
    (overrideRecord
        recordCode
        current
        newStateCode).auditEntry.oldStateCode =
        current.stateCode
      ∧
    (overrideRecord
        recordCode
        current
        newStateCode).auditEntry.newStateCode =
        newStateCode :=
  ⟨
    rfl,
    ⟨
      rfl,
      ⟨
        rfl,
        rfl
      ⟩
    ⟩
  ⟩

/-
降级注：

覆盖动作与审计记录由同一个 constructor 同时产生。

因此结构层禁止：
“记录已经变了，但覆盖来源、旧值、新值没有进入审计对象”。

T31 完整陈述仍缺：
1. actor；
2. timestamp；
3. reason；
4. source；
5. immutable audit log；
6. 多次覆盖链；
7. audit sequence continuity；
8. storage transaction 原子性。
-/

end T31


/- ============================================================
   T32
   运行时参考一致
   ============================================================ -/

namespace T32

structure ReferenceToken where
  sourceCode : Nat
  versionCode : Nat

structure RuntimeReferenceContract where
  compiledReference : ReferenceToken
  runtimeReference : ReferenceToken

  consistencyLaw :
    runtimeReference =
      compiledReference

theorem runtime_reference_consistency
    (contract : RuntimeReferenceContract) :
    contract.runtimeReference =
      contract.compiledReference :=
  contract.consistencyLaw

/-
降级注：

compile-time reference 和 runtime reference
不能仅靠“约定上应该一样”。

RuntimeReferenceContract 必须携带 consistencyLaw。

T32 完整陈述仍缺：
1. reference resolution；
2. source locator；
3. version/package locator；
4. dynamic loading；
5. stale reference；
6. cache；
7. hash/content identity；
8. runtime resolver 自动满足 consistencyLaw 的证明。
-/

end T32


/- ============================================================
   T33
   对外不重贴标签
   ============================================================ -/

namespace T33

structure InternalJudgment where
  legalLabelCode : Nat
  payloadCode : Nat
  internalNoteCode : Nat

structure ExternalJudgment where
  legalLabelCode : Nat
  payloadCode : Nat

def externalize
    (judgment : InternalJudgment) :
    ExternalJudgment :=
  {
    legalLabelCode :=
      judgment.legalLabelCode

    payloadCode :=
      judgment.payloadCode
  }

theorem external_output_does_not_relabel
    (judgment : InternalJudgment) :
    (externalize judgment).legalLabelCode =
      judgment.legalLabelCode :=
  rfl

/-
降级注：

externalize 可以删除 internalNote，
但不能重新生成或替换 legalLabelCode。

即：
展示层不得把内部法律判断重新贴一个新的法律标签。

T33 完整陈述仍缺：
1. 丰富 label 类型；
2. redaction；
3. presentation formatting；
4. multilingual rendering；
5. UNKNOWN/HYPOTHETICAL 等输出状态；
6. 外部文本生成器；
7. “自然语言表述不改变法律分类”的语义保持证明。
-/

end T33


/- ============================================================
   T34
   经营不污染法律
   ============================================================ -/

namespace T34

structure CombinedState where
  legalStateCode : Nat
  businessStateCode : Nat

def updateBusinessState
    (state : CombinedState)
    (newBusinessStateCode : Nat) :
    CombinedState :=
  {
    legalStateCode :=
      state.legalStateCode

    businessStateCode :=
      newBusinessStateCode
  }

theorem business_does_not_pollute_legal
    (state : CombinedState)
    (newBusinessStateCode : Nat) :
    (updateBusinessState
        state
        newBusinessStateCode).legalStateCode =
      state.legalStateCode :=
  rfl

/-
降级注：

经营状态更新只能修改 businessStateCode，
legalStateCode 结构上保持不变。

这锁住“商业考虑可以影响行动选择，
但不能偷偷改写法律本体判断”的最小分层纪律。

T34 完整陈述仍缺：
1. 法律状态 R；
2. business utility；
3. strategy/action layer；
4. legal conclusion → decision input；
5. decision → legal conclusion 的禁止反馈边；
6. negotiation/business optimization；
7. 整个决策系统的 non-interference theorem。
-/

end T34


/- ============================================================
   T35
   论文主张一致
   ============================================================ -/

namespace T35

structure PaperClaimContract where
  formalClaimCode : Nat
  paperClaimCode : Nat

  consistencyLaw :
    paperClaimCode =
      formalClaimCode

theorem paper_claim_consistency
    (claim : PaperClaimContract) :
    claim.paperClaimCode =
      claim.formalClaimCode :=
  claim.consistencyLaw

/-
降级注：

论文中的 claim 不能脱离形式化 claim 独立升级。

PaperClaimContract 要求二者存在明确一致见证。

T35 完整陈述仍缺：
1. claim AST；
2. theorem identifier；
3. natural-language claim extraction；
4. 强弱关系；
5. “论文表述不得强于 Lean theorem”的 preorder；
6. 自动 claim checker；
7. 论文全文级 consistency audit。
-/

end T35


/- ============================================================
   T36
   完成验收
   ============================================================ -/

namespace T36

structure CompletionWitness where
  compileAccepted : Prop
  proofAccepted : Prop
  testAccepted : Prop
  auditAccepted : Prop

  compileWitness :
    compileAccepted

  proofWitness :
    proofAccepted

  testWitness :
    testAccepted

  auditWitness :
    auditAccepted

structure CompletedArtifact where
  artifactCode : Nat
  acceptance : CompletionWitness

theorem completion_acceptance
    (artifact : CompletedArtifact) :
    artifact.acceptance.compileAccepted ∧
      artifact.acceptance.proofAccepted ∧
      artifact.acceptance.testAccepted ∧
      artifact.acceptance.auditAccepted :=
  ⟨
    artifact.acceptance.compileWitness,
    ⟨
      artifact.acceptance.proofWitness,
      ⟨
        artifact.acceptance.testWitness,
        artifact.acceptance.auditWitness
      ⟩
    ⟩
  ⟩

/-
降级注：

CompletedArtifact 不是布尔 completed = true。

要取得“完成”类型，
必须同时携带：
- compile witness；
- proof witness；
- test witness；
- audit witness。

T36 完整陈述仍缺：
1. 各验收项的真实 CI predicate；
2. coverage threshold；
3. repository state；
4. artifact hash；
5. reproducibility；
6. release gate；
7. CI 运行结果 → CompletionWitness 的可信桥接。
-/

end T36


/- ============================================================
   T37
   统一概率对象
   法律身份保持
   ============================================================ -/

namespace T37

structure LegalIdentity where
  jurisdictionCode : Nat
  relationCode : Nat
  propositionCode : Nat

structure UnifiedProbabilityObject where
  legalIdentity : LegalIdentity
  support : List Nat
  weight :
    Nat → ℚ

def reweight
    (object : UnifiedProbabilityObject)
    (newWeight : Nat → ℚ) :
    UnifiedProbabilityObject :=
  {
    legalIdentity :=
      object.legalIdentity

    support :=
      object.support

    weight :=
      newWeight
  }

theorem unified_probability_preserves_legal_identity
    (object : UnifiedProbabilityObject)
    (newWeight : Nat → ℚ) :
    (reweight
        object
        newWeight).legalIdentity =
      object.legalIdentity :=
  rfl

/-
降级注：

概率更新允许改变 weight，
但不得改变：
- jurisdiction；
- legal relation；
- proposition identity。

因此“概率化”不能通过重新编码对象身份，
把原法律命题偷偷换成另一个命题。

T37 完整陈述仍缺：
1. probability normalization；
2. evidence variable；
3. conditional probability；
4. posterior update；
5. legal identity equivalence；
6. random variable semantics；
7. uncertainty 类型区分；
8. 概率模型与法律真值/裁判判断之间的分层桥。
-/

end T37


/- ============================================================
   T38
   有限有理概率 + 条件化
   ============================================================ -/

namespace T38

structure FiniteRationalProbability where
  support : List Nat
  weight :
    Nat → ℚ

def eventMass
    (probability : FiniteRationalProbability)
    (event : Nat → Bool) :
    List Nat → ℚ
  | [] =>
  | outcome :: remaining =>
      (if event outcome then
          probability.weight outcome
       else
          0)
        +
      eventMass
        probability
        event
        remaining

def totalEventMass
    (probability : FiniteRationalProbability)
    (event : Nat → Bool) : ℚ :=
  eventMass
    probability
    event
    probability.support

def conditionedWeight
    (probability : FiniteRationalProbability)
    (event : Nat → Bool)
    (outcome : Nat) : ℚ :=
  if event outcome then
    probability.weight outcome /
      totalEventMass
        probability
        event
  else

inductive ConditioningResult where
  | undefinedCondition
  | conditioned
      (weight : Nat → ℚ)

def conditionProbability
    (probability : FiniteRationalProbability)
    (event : Nat → Bool) :
    ConditioningResult :=
  if decide
      (totalEventMass
          probability
          event = 0)
  then
    .undefinedCondition
  else
    .conditioned
      (conditionedWeight
        probability
        event)

theorem conditioning_zero_mass_unknown
    (probability : FiniteRationalProbability)
    (event : Nat → Bool)
    (zeroMass :
      totalEventMass
          probability
          event = 0) :
    conditionProbability
        probability
        event =
      .undefinedCondition := by
  simp [
    conditionProbability,
    zeroMass
  ]

theorem conditioning_excludes_false_event
    (probability : FiniteRationalProbability)
    (event : Nat → Bool)
    (outcome : Nat)
    (excluded :
      event outcome = false) :
    conditionedWeight
        probability
        event
        outcome =
      0 := by
  simp [
    conditionedWeight,
    excluded
  ]

/-
降级注：

本项已经形成：
1. List 有限 support；
2. ℚ 精确权重；
3. event mass；
4. 条件化；
5. 零条件质量时明确 undefined；
6. event 外 outcome 条件权重为 0。

没有使用浮点概率。

T38 完整陈述仍缺：
1. 非负权重；
2. 原始 support 权重总和 = 1；
3. 无重复 outcome；
4. event mass > 0 时条件概率归一化 = 1；
5. Bayes；
6. product space；
7. finite rational probability 的完整合法性 structure；
8. 条件化后 support 的精化。
-/

end T38


/- ============================================================
   T39
   变量消元实现 = 独立枚举
   ============================================================ -/

namespace T39

def BoolPotential :=
  Bool → ℚ

def eliminateBooleanVariable
    (potential : BoolPotential) : ℚ :=
  potential false +
    potential true

def booleanAssignments :
    List Bool :=
  [false, true]

def independentEnumeration
    (potential : BoolPotential) : ℚ :=
  booleanAssignments.foldr
    (fun value accumulated =>
      potential value +
        accumulated)

theorem variable_elimination_equals_independent_enumeration
    (potential : BoolPotential) :
    eliminateBooleanVariable potential =
      independentEnumeration potential := by
  simp [
    eliminateBooleanVariable,
    independentEnumeration,
    booleanAssignments
  ]

/-
降级注：

这里故意保留两条独立计算路径：

1. eliminateBooleanVariable
   直接消去 Bool variable；

2. independentEnumeration
   显式枚举 [false, true] 后 fold。

二者不是通过一个共同 alias 定义，
而是由 theorem 证明结果一致。

T39 完整陈述仍缺：
1. 多变量；
2. factor；
3. factor multiplication；
4. elimination order；
5. intermediate factor；
6. arbitrary finite domain；
7. 完整变量消元算法；
8. 与全 assignments 独立枚举的归纳等价；
9. complexity 与 semantic preservation。
-/

end T39


/- ============================================================
   T40
   观测同一性
   ============================================================ -/

namespace T40

structure ObservableState where
  internalStateCode : Nat
  observationCode : Nat

def observe
    (state : ObservableState) : Nat :=
  state.observationCode

def ObservationallyIdentical
    (left right : ObservableState) : Prop :=
  observe left =
    observe right

theorem observational_identity
    (left right : ObservableState)
    (sameObservation :
      observe left =
        observe right) :
    ObservationallyIdentical
      left
      right :=
  sameObservation

def replaceHiddenState
    (state : ObservableState)
    (newInternalStateCode : Nat) :
    ObservableState :=
  {
    internalStateCode :=
      newInternalStateCode

    observationCode :=
      state.observationCode
  }

theorem hidden_change_preserves_observation
    (state : ObservableState)
    (newInternalStateCode : Nat) :
    ObservationallyIdentical
      state
      (replaceHiddenState
        state
        newInternalStateCode) :=
  rfl

/-
降级注：

当前观测等价由 observe 明确定义。

内部状态不同，
只要 observationCode 保持，
即可保持当前 observation identity。

T40 完整陈述仍缺：
1. observation alphabet；
2. trace；
3. action；
4. transition；
5. future observations；
6. contextual equivalence；
7. bisimulation；
8. 对外 API / 用户可见结果的真实 observational equivalence。
-/

end T40


/- ============================================================
   Batch 2 self-check
   ============================================================

A. T21–T40 theorem-level carrier

T21
  interest_segment_refinement

T22
  residual_payment_le
  payment_offset_conservation

T23
  fixed_scheme_conservation

T24
  asset_pool_no_duplicate_consumption

T25
  priority_waterfall_monotone

T26
  interruption_resume_preserves_checkpoint

T27
  admitted_rule_has_four_witnesses

T28
  compile_structure_preserving

T29
  evaluate_multi_contract

T30
  version_package_isolation

T31
  record_override_audit

T32
  runtime_reference_consistency

T33
  external_output_does_not_relabel

T34
  business_does_not_pollute_legal

T35
  paper_claim_consistency

T36
  completion_acceptance

T37
  unified_probability_preserves_legal_identity

T38
  conditioning_zero_mass_unknown
  conditioning_excludes_false_event

T39
  variable_elimination_equals_independent_enumeration

T40
  observational_identity
  hidden_change_preserves_observation


B. 新标识符关键字检查

T21:
InterestSlice
principal
rateFactor
durationFactor
sliceInterest
segmentedInterest
interest_segment_refinement

T22:
residualPayment
appliedPayment
residual_payment_le
payment_offset_conservation

T23:
trancheTotal
FixedWaterfallPlan
inputAmount
tranches
conservationLaw
waterfallTotal
fixed_scheme_conservation

T24:
AssetPoolLedger
consumedBy
AssetConsumedBy
asset_pool_no_duplicate_consumption

T25:
PriorityWaterfall
allocations
adjacentMonotone
priority_waterfall_monotone

T26:
Checkpoint
cursorCode
payloadCode
RuntimeState
checkpoint
phaseCode
interrupt
resume
interruption_resume_preserves_checkpoint

T27:
FourGateWitness
sourceGate
scopeGate
temporalGate
semanticGate
sourceWitness
scopeWitness
temporalWitness
semanticWitness
AdmittedRule
ruleCode
gates
admitted_rule_has_four_witnesses

T28:
SourceAst
literalNode
addNode
RuntimeAst
runtimeLiteral
runtimeAdd
compileAst
sourceDenotation
runtimeDenotation
compile_structure_preserving

T29:
JurisdictionContract
jurisdictionCode
evaluator
EvaluationResult
value
evaluateContract
evaluateMultiContract
evaluate_multi_contract

T30:
VersionPackage
versionCode
payloadCode
PackageStore
replaceVersionPackage
version_package_isolation

T31:
RecordValue
stateCode
AuditEntry
recordCode
oldStateCode
newStateCode
OverrideResult
updatedRecord
auditEntry
overrideRecord
record_override_audit

T32:
ReferenceToken
sourceCode
versionCode
RuntimeReferenceContract
compiledReference
runtimeReference
consistencyLaw
runtime_reference_consistency

T33:
InternalJudgment
legalLabelCode
payloadCode
internalNoteCode
ExternalJudgment
externalize
external_output_does_not_relabel

T34:
CombinedState
legalStateCode
businessStateCode
updateBusinessState
business_does_not_pollute_legal

T35:
PaperClaimContract
formalClaimCode
paperClaimCode
consistencyLaw
paper_claim_consistency

T36:
CompletionWitness
compileAccepted
proofAccepted
testAccepted
auditAccepted
compileWitness
proofWitness
testWitness
auditWitness
CompletedArtifact
artifactCode
acceptance
completion_acceptance

T37:
LegalIdentity
jurisdictionCode
relationCode
propositionCode
UnifiedProbabilityObject
legalIdentity
support
weight
reweight
unified_probability_preserves_legal_identity

T38:
FiniteRationalProbability
support
weight
eventMass
totalEventMass
conditionedWeight
ConditioningResult
undefinedCondition
conditioned
conditionProbability
conditioning_zero_mass_unknown
conditioning_excludes_false_event

T39:
BoolPotential
eliminateBooleanVariable
booleanAssignments
independentEnumeration
variable_elimination_equals_independent_enumeration

T40:
ObservableState
internalStateCode
observationCode
observe
ObservationallyIdentical
observational_identity
replaceHiddenState
hidden_change_preserves_observation

上述新标识符未使用以下关键字作为名称：

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


C. tactic 白名单检查

本文件实际使用的 tactic：

- induction
- simp
- omega
- cases
- have
- rfl

其中 have 仅用于从已存在归纳假设/前提导出当前上下文中需要的中间事实：
- T22 tailBound
- T22 residualBound
- T24 sameOwner

其余证明使用：
- 结构字段投影；
- 函数项应用；
- List.rec；
- 构造子；
- equality transitivity；
- 直接 proof term。

未使用：

intro
exact
apply
constructor
aesop
tauto
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
assumption
native_decide
sorry
admit
axiom


D. 九轮 CI 教训专项检查

1. 0 × `simp only`。

2. 0 × dependent if / dite。

3. T38 使用：
   `if decide (mass = 0) then ... else ...`
   为纯 ite；
   theorem 通过完整 `simp [conditionProbability, zeroMass]`
   消解，不使用 `if_pos` / `if_neg` / dite 引理。

4. T30 的 ite 使用普通 proposition equality，
   由：
   `simp [replaceVersionPackage, differentVersion]`
   处理。

5. 没有使用 Lean 关键字作为 constructor 名。

6. 没有依赖形状敏感的 dite equality lemma。

7. 没有 `native_decide`。


E. Mathlib 不确定引用检查

本文件没有调用不确定的专用 Mathlib theorem 名。

显式使用的基础设施只有：

Nat
Int
Bool
Option
List
List.rec
List.foldr
ℚ

以及基础：
- 加法；
- 乘法；
- Nat subtraction；
- ≤；
- Option.some；
- List append；
- List constructors；
- equality；
- conjunction；
- decide；
- omega。

没有引用：
List.sum_append
Finset
Fintype
ProbabilityTheory
MeasureTheory
Bayes theorem
图算法库
编译器专用库
或其他可能发生版本名称漂移的高级 Mathlib API。


F. 禁止项检查

全文目标：

0 × sorry
0 × admit
0 × axiom
0 × native_decide


G. 本批结构闭合状态

T21–T40：

20 / 20 已建立独立 namespace。

20 / 20 已建立最小结构载体。

20 / 20 已有至少一条正面 theorem。

20 / 20 无 OPEN 占位。

其中：
- T21：任意分段列表拼接累计守恒；
- T22：任意 payment × 任意 debt list 付款守恒；
- T23：固定瀑布方案总额守恒；
- T24：单资产不可归属两个不同消费者；
- T25：顺位相邻 allocation 不增；
- T26：中断恢复 checkpoint 保持；
- T27：准入对象必携四闸见证；
- T28：AST 编译求值保持；
- T29：多法域 evaluator 逐 contract 独立递归；
- T30：版本包更新非干扰；
- T31：覆盖动作同步生成旧值/新值审计；
- T32：运行时引用必须与编译引用一致；
- T33：externalize 不重贴法律标签；
- T34：经营状态更新不修改法律状态；
- T35：论文 claim 与 formal claim 带一致见证；
- T36：完成对象必须携带四项验收见证；
- T37：概率重加权不改变法律身份；
- T38：有限 ℚ 条件化 + 零质量 UNKNOWN；
- T39：Bool 变量消元 = 独立枚举；
- T40：隐藏状态变化不改变既定 observation。

以上“闭合”均仅指十轮问约定的
theorem-level 结构纪律层载体闭合；
各 T 降级注列出的强量化、算法正确性、
实体法律语义及工程 refinement
仍不冒充已经完成。
-/

end JurisLean.Genealogy.TSpectrum