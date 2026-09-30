import JurisLean.ULM14CoverageTrust
import JurisLean.TaintNoninterference
import JurisLean.AuthorityLattice

/-!
# 六类不可表达边界的界定定理（封闭性 · 片段强度）

> 契约来源：`docs/master-plan/06_六类边界绑定表.md`。
> §二给出六条边界的类型层载体与 file:line；§三给出三档口径；§五列出禁止的主张；
> §六给出六条界定陈述（草案）与各自前置。本文件按 §六 施工，只做**片段强度**。

## §法律语义

①失败不得被改写成正常载荷；②声称结果不完备时必须交出一个仍未关闭的义务；
③声称扩展族为空时必须交出空性证明；④求解不完备不得被改写成不利裁判；
⑤聚合不得提高保证；⑥重复提交受污输入不得使之变干净。
六条都是对本仓类型与函数的陈述，不指向任何真实案件或真实法规则（§五）。

## §数学对象

每条边界先固定一个**声明操作族**（归纳类型 + 该族的解释函数），再对该族证封闭性：

- ①② `OutcomeMapOp`（map / addObligations / compose）
- ③ `EmptyReportOp`（attest / substitute / byFlag）
- ④ `AdjudicationRewriter`（skip / supplyAuthority / supplyProcedural / seq）
- ⑤ `TrustAggregateOp`（主干内信任向量版）、`ConsensusOp`（主干外权限秩版）——两版各自成族
- ⑥ `TaintPipeline` + `CarriesTaint`（§六要求的归纳类）

## §证与不证

- 证：对上面这些归纳族的封闭性，全部按族的归纳证明；本文件无占位证明、无放行式收尾、无新公理声明。
- 不证：全调用链意义上的"任何写法都不能绕过该要求"。§三第 2 档引用的仓内 FAIL 判据
  （`docs/history/evidence-archive/0923_四报告与锤击/法律统一数学模型_四报告与跨仓审查_20260923.md:555`）
  仍然成立，本文件把它钉成正定理 `delimitation_is_not_general`：族外**确实**存在
  忽略输入、直接返回 `complete` 的 Lean 函数。
- 不证：⑤两版之间的桥接（信任向量 meet 与权限秩升级）。§五禁止六类之间的桥接等价主张，
  本文件不定义任何转换函数。
- 不证：②④与求解器状态之间的精化、③所需的 profile 语义完备定理 —— 前置在仓内不存在。
- 局部反例（污染筛选 99.02%、同率不同后验、先付后息、周期二不收敛）一律不作为封闭性证明（§五）。

## §未覆盖片段

- 族外函数：任何不在上述归纳族里的 Lean 定义都未被排除（每条 doc-comment 重复此句）。
- 封装：主干 `Outcome.map`、`adjudicate`、`consensusRank` 等是公开 `def`，
  调用方可不经本文件的操作族直接使用它们。
- ③：主干判据 `evaluateProfile`（`ULM11BranchQuery.lean:49-57`）的可靠性方向
  （`extensionsForProfile` 为空 ⇔ 语义族真的没有扩张）不在族内，需 §六要求的完备定理。
- ⑤：`TrustLE` 与 `authorityRank` 之间无桥接；`AutoEscalationMechanism` 四种自动机制
  不是 `ConsensusOp` 的生成方式，其无效性由主干 `no_auto_escalation` 单独陈述。
- ⑥：`TaintPipeline` 只枚举 input / stage / merge / resubmit 四条传播路径；
  真实多 Agent 运行期的其它传播路径（缓存、重试计数器、外部日志回填）不在族内。

## §档位

按 §三三档：类型层已实现（六条皆有载体）＋界定定理（封闭性）**片段强度已证、一般式未证**
＋公理审计面（本文件的定理名尚未并入 `AxiomAudit`，属下一针施工；在此之前一律 `CI_NOT_RUN`）。
-/

namespace JurisLean.Seams.BoundaryClosure

open JurisLean.ULM

/-! ============================================================
    第一节 ①②：`Outcome` 上的声明操作族
    ============================================================ -/

/-- 中文说明：①②的声明操作族。三条生成方式恰好是主干在 `JurisLean.ULM.Outcome`
上写得出的结局映射：`map`（`ULM02Outcome.lean:37-43` 的 `Outcome.map`）、
`addObligations`（只能给 partial 结果**追加**未关闭义务）、`compose`（族内复合）。
"忽略输入、返回 `complete`" 的常数写法**不是**族成员。 -/
inductive OutcomeMapOp : Type → Type → Type 1 where
  | map {α β : Type} (f : α → β) : OutcomeMapOp α β
  | addObligations {α : Type} (extra : Finset OpenObligation) : OutcomeMapOp α α
  | compose {α β γ : Type} (g : OutcomeMapOp β γ) (f : OutcomeMapOp α β) : OutcomeMapOp α γ

namespace OutcomeMapOp

/-- 中文说明：给一个 partial 载荷追加若干未关闭义务；只增不减。
非空性由主干字段 `open_nonempty`（`ULM02Outcome.lean:16`）沿 `⊆` 传递。 -/
def addExtra {α : Type} (p : PartialPayload α) (extra : Finset OpenObligation) :
    PartialPayload α :=
  { value := p.value,
    openObligations := p.openObligations ∪ extra,
    open_nonempty := Finset.Nonempty.mono Finset.subset_union_left p.open_nonempty }

/-- 中文说明：族的语义 —— 把族成员解释为一个 `Outcome α → Outcome β` 函数。 -/
def run {α β : Type} : OutcomeMapOp α β → Outcome α → Outcome β
  | .map f => Outcome.map f
  | .addObligations extra => fun
      | .complete x => .complete x
      | .partialResult p => .partialResult (addExtra p extra)
      | .failure e => .failure e
  | .compose g f => fun x => g.run (f.run x)

/-- 中文说明（界定定理①·封闭性）：族内任一运算作用在 `failure` 输入上，
输出**逐字**仍是同一个 `failure`，故族内不存在把失败改写成正常载荷的写法。
证明是 `OutcomeMapOp` 上的结构归纳，三个生成方式各一支；`map` 一支复用主干
`map_never_upgrades_failure`（`ULM02Outcome.lean:68`）。
本条只对该归纳族封闭；族外的写法未被排除（见 `delimitation_is_not_general`）。 -/
theorem closure_boundary1_no_failure_upgrade {α β : Type} (op : OutcomeMapOp α β) :
    ∀ (e : FailureCore), op.run (.failure e) = (.failure e : Outcome β) := by
  induction op with
  | map f => intro e; exact Outcome.map_never_upgrades_failure f e
  | addObligations extra => intro e; rfl
  | compose g f ihg ihf =>
      intro e
      show g.run (f.run (.failure e)) = .failure e
      rw [ihf e, ihg e]

/-- 中文说明（①·推论）：族内运算不得把 failure 判成 complete
（主干 `failure_ne_complete`，`ULM02Outcome.lean:58`）。 -/
theorem closure_boundary1_not_complete {α β : Type} (op : OutcomeMapOp α β)
    (e : FailureCore) (x : β) : op.run (.failure e) ≠ Outcome.complete x := by
  rw [closure_boundary1_no_failure_upgrade op e]
  exact Outcome.failure_ne_complete e x

/-- 中文说明（界定定理②·封闭性）：族内任一运算作用在 `partialResult` 上，
输出仍是 `partialResult`，且交出的未关闭义务集合**包含**输入的义务集合：
族内既不能把不完备结果洗成完备，也不能缩小交出的义务集合。
本条只对该归纳族封闭；族外的写法未被排除。 -/
theorem closure_boundary2_partial_preserved {α β : Type} (op : OutcomeMapOp α β) :
    ∀ (p : PartialPayload α),
      ∃ q : PartialPayload β,
        op.run (Outcome.partialResult p) = Outcome.partialResult q ∧
          p.openObligations ⊆ q.openObligations := by
  induction op with
  | map f =>
      intro p
      exact ⟨{ value := f p.value, openObligations := p.openObligations,
               open_nonempty := p.open_nonempty },
        Outcome.map_partial f p, Finset.Subset.refl _⟩
  | addObligations extra =>
      intro p
      exact ⟨addExtra p extra, rfl, Finset.subset_union_left⟩
  | compose g f ihg ihf =>
      intro p
      obtain ⟨q, hq, hsub⟩ := ihf p
      obtain ⟨r, hr, hsub'⟩ := ihg q
      refine ⟨r, ?_, Finset.Subset.trans hsub hsub'⟩
      show g.run (f.run (.partialResult p)) = .partialResult r
      rw [hq, hr]

/-- 中文说明（界定定理②·主文）：族内运算不得把不完备结果洗成完备结果
（主干 `partial_ne_complete`，`ULM02Outcome.lean:63`）。
诚实边界：交出的那个载荷自带非空义务集合，这一事实**不是**族性质而是类型层事实 ——
`PartialPayload.open_nonempty` 是字段（`ULM02Outcome.lean:13-16`），对族内族外一律成立；
真正需要封闭性的是"不得洗成 complete / 不得缩小义务集合"。
§六为②要求的前置（交出义务与求解器实际未关闭义务集合之间的精化）在仓内不存在，
故②的一般式记为**未证**。本条只对该归纳族封闭；族外的写法未被排除。 -/
theorem closure_boundary2_no_partial_laundering {α β : Type} (op : OutcomeMapOp α β)
    (p : PartialPayload α) (x : β) : op.run (Outcome.partialResult p) ≠ Outcome.complete x := by
  obtain ⟨q, hq, _⟩ := closure_boundary2_partial_preserved op p
  rw [hq]
  exact Outcome.partial_ne_complete q x

/-- 中文说明：旁记载体 `Genealogy/Boundary.lean:59`
（`partialValue_openObligations_nonempty`）在本文件里的对应物。 -/
theorem boundary2_obligations_hand_over {α β : Type} (op : OutcomeMapOp α β)
    (p : PartialPayload α) (q : PartialPayload β)
    (_h : op.run (Outcome.partialResult p) = Outcome.partialResult q) :
    q.openObligations.Nonempty :=
  q.open_nonempty

end OutcomeMapOp

/-! ============================================================
    第二节 ③：无扩张声称的声明操作族
    ============================================================ -/

/-- 中文说明：③的输出形状。`claims p` 是"声称 profile p 的扩张族为空"，
`abstains` 是"不声称"。声称本身不带证明参数：证明由族成员的构造前提给出，
于是下一条封闭性定理是关于**该前提能被复合保持**的陈述，不是构造子签名的复读。 -/
inductive EmptinessVerdict : Type
  | claims (profile : SemanticProfile)
  | abstains

/-- 中文说明：界定定理③的声明操作族，三种写法：
`attest p h` 直接交出空性证明（对应主干构造子 `EvalResult.noExtension`，
其第三参就是 `emptyProof : extensionsForProfile profile af = ∅`，
`ULM11BranchQuery.lean:30-32`）；`substitute p q heq h` 沿"两个 profile 的扩张族相等"
把空性声称搬运到 q；`byFlag p flag` 只握有一个 `Bool` 判空标志。 -/
inductive EmptyReportOp (af : DefeatAF) : Type where
  | attest (p : SemanticProfile) (h : extensionsForProfile p af = ∅) : EmptyReportOp af
  | substitute (p q : SemanticProfile)
      (heq : extensionsForProfile p af = extensionsForProfile q af)
      (h : extensionsForProfile p af = ∅) : EmptyReportOp af
  | byFlag (p : SemanticProfile) (flag : Bool) : EmptyReportOp af

/-- 中文说明：族的语义。注意 `byFlag` 一支恒为 `abstains` ——
Bool 判空标志在本族内得不到声称。 -/
def EmptyReportOp.run {af : DefeatAF} : EmptyReportOp af → EmptinessVerdict
  | .attest p _ => .claims p
  | .substitute _ q _ _ => .claims q
  | .byFlag _ _ => .abstains

/-- 中文说明（界定定理③·封闭性）：族内任一成员一旦交出"无扩张"声称，
被声称的那个 profile 的扩张族**确实**是空集；只握有 `Bool` 判空标志的成员交不出声称。
证明是 `EmptyReportOp` 上的结构归纳；`substitute` 一支真正用到 `heq` 的等式传递
（搬运后的声称仍然成立），不是把证明换个名字复读。
诚实边界：主干判据 `evaluateProfile`（`ULM11BranchQuery.lean:49-57`）的可靠性方向
——"空性判据与语义族构造完全对应"——不在族内，需 §六要求的 profile 语义完备定理；
该前置在仓内不存在，故③的一般式记为**未证**。本条只对该归纳族封闭；族外的写法未被排除。 -/
theorem closure_boundary3_no_unproved_emptiness {af : DefeatAF} (op : EmptyReportOp af) :
    ∀ (p : SemanticProfile),
      op.run = EmptinessVerdict.claims p → extensionsForProfile p af = ∅ := by
  induction op with
  | attest p hEmpty =>
      intro p' h
      have h2 : EmptinessVerdict.claims p = EmptinessVerdict.claims p' := h
      cases (EmptinessVerdict.claims.inj h2)
      exact hEmpty
  | substitute p q heq hEmpty =>
      intro p' h
      have h2 : EmptinessVerdict.claims q = EmptinessVerdict.claims p' := h
      cases (EmptinessVerdict.claims.inj h2)
      exact heq.symm.trans hEmpty
  | byFlag p flag =>
      intro p' h
      have h2 : EmptinessVerdict.abstains = EmptinessVerdict.claims p' := h
      cases h2

/-- 中文说明：③的旁记载体 `Genealogy/Boundary.lean:108,133`
（`NoExtensionsCertificate` / `noExtensions_family_empty`）的对应物：
族内的 `attest` 成员把空性证明作为构造前提，声称与证明同生。 -/
theorem boundary3_attested_carries_proof {af : DefeatAF} (p : SemanticProfile)
    (h : extensionsForProfile p af = ∅) :
    (EmptyReportOp.attest p h).run = EmptinessVerdict.claims p := rfl

/-! ============================================================
    第三节 ④：裁判输入改写的声明操作族
    ============================================================ -/

/-- 中文说明：界定定理④的声明操作族 —— 主干可写出的裁判**输入**改写：
补交请求绑定权源并以 `withFinding` 改认定（`ULM12Procedure.lean:195-203`）、
附程序性处置、族内顺序复合。族内**没有**更换 `evaluation` 字段的运算
（换一次求解结果是合法的补交证据路径，不是本条要禁的写法）。 -/
inductive AdjudicationRewriter (af : DefeatAF) : Type where
  | skip : AdjudicationRewriter af
  | supplyAuthority (a : ValidatedAdjudicationAuthority af.request)
      (finding : ProofFinding) : AdjudicationRewriter af
  | supplyProcedural (s : ProceduralStatusFor af.request) : AdjudicationRewriter af
  | seq (g h : AdjudicationRewriter af) : AdjudicationRewriter af

/-- 中文说明：族的语义 —— 只改写 `AdjudicationInput` 的两个可选字段。 -/
def AdjudicationRewriter.apply {af : DefeatAF} :
    AdjudicationRewriter af → AdjudicationInput af → AdjudicationInput af
  | .skip => fun input => input
  | .supplyAuthority a finding => fun input =>
      { input with authority := some (a.withFinding finding) }
  | .supplyProcedural s => fun input => { input with proceduralOnly := some s }
  | .seq g h => fun input => h.apply (g.apply input)

/-- 中文说明：技术支点 —— 族内改写永不触碰 `evaluation` 字段。 -/
theorem AdjudicationRewriter.apply_preserves_evaluation {af : DefeatAF}
    (op : AdjudicationRewriter af) :
    ∀ (input : AdjudicationInput af), (op.apply input).evaluation = input.evaluation := by
  induction op with
  | skip => intro input; rfl
  | supplyAuthority a finding => intro input; rfl
  | supplyProcedural s => intro input; rfl
  | seq g h ihg ihh =>
      intro input
      exact ((ihh (g.apply input)).trans (ihg input))

/-- 中文说明：主干 `adjudicate` 只看 `evaluation` 是否为 incomplete ——
该字段等于 `EvalResult.incomplete` 时结果即 `solverIncomplete`，与另两字段无关。
这是主干 `adjudicate_incomplete`（`ULM12Procedure.lean:175`，只指定输入）的任意输入版。 -/
theorem adjudicate_of_incomplete_evaluation {af : DefeatAF} (input : AdjudicationInput af)
    (profile : SemanticProfile) (pr : IncompleteEvaluation af profile)
    (h : input.evaluation = EvalResult.incomplete profile pr) :
    adjudicate input = ProcedureAdjudicateResult.solverIncomplete pr.openObligations := by
  cases input with
  | mk ev authority proceduralOnly =>
      have h2 : ev = EvalResult.incomplete profile pr := h
      cases h2
      exact adjudicate_incomplete af profile pr authority proceduralOnly

/-- 中文说明：主干意义上的"不利实体裁判" —— 由 `finding = unmet` 的请求绑定权源
产生的实体状态集，即 `ULM12Procedure.lean:165,173` 的 `.unmet` 分支。 -/
def AdverseAdjudication {request : RequestKey}
    (r : ProcedureAdjudicateResult request) : Prop :=
  ∃ (a : ValidatedAdjudicationAuthority request),
    a.1.finding = ProofFinding.unmet ∧
      r = ProcedureAdjudicateResult.adjudicatedStatus (failureStatuses a)

/-- 中文说明（界定定理④·封闭性·等式形）：族内任意有限复合的输入改写之后，
incomplete 求解结果仍只能是 `solverIncomplete`。 -/
theorem closure_boundary4_solverIncomplete {af : DefeatAF} (op : AdjudicationRewriter af)
    (input : AdjudicationInput af) (profile : SemanticProfile)
    (pr : IncompleteEvaluation af profile)
    (h : input.evaluation = EvalResult.incomplete profile pr) :
    adjudicate (op.apply input) =
      ProcedureAdjudicateResult.solverIncomplete pr.openObligations :=
  adjudicate_of_incomplete_evaluation (op.apply input) profile pr
    ((AdjudicationRewriter.apply_preserves_evaluation op input).trans h)

/-- 中文说明（界定定理④·主文）：族内任意复合改写都不可能把求解不完备
改写成不利裁判，也不可能改写成"待实体裁判"。等式一支复用主干
`solverIncomplete_ne_adjudicated`（`ULM12Procedure.lean:256-262`）。
本条只对该归纳族封闭；族外的写法未被排除：`adjudicate` 是公开 `def`，
调用方可不经本族直接构造 `AdjudicationInput`。§六为④要求的前置
（调用链任意组合下的封装，以及与②共用的求解器状态建模）在仓内不存在，
故④的一般式记为**未证**。 -/
theorem closure_boundary4_incomplete_not_adverse {af : DefeatAF}
    (op : AdjudicationRewriter af) (input : AdjudicationInput af)
    (profile : SemanticProfile) (pr : IncompleteEvaluation af profile)
    (h : input.evaluation = EvalResult.incomplete profile pr) :
    ¬ AdverseAdjudication (adjudicate (op.apply input)) := by
  rintro ⟨a, _, hr⟩
  exact solverIncomplete_ne_adjudicated pr.openObligations (failureStatuses a)
    ((closure_boundary4_solverIncomplete op input profile pr h).symm.trans hr)

/-- 中文说明：④的另一面 —— 族内改写也不能把 incomplete 伪装成待裁判后溜过去。 -/
theorem closure_boundary4_not_pending {af : DefeatAF} (op : AdjudicationRewriter af)
    (input : AdjudicationInput af) (profile : SemanticProfile)
    (pr : IncompleteEvaluation af profile) (m : Finset String)
    (h : input.evaluation = EvalResult.incomplete profile pr) :
    adjudicate (op.apply input) ≠
      ProcedureAdjudicateResult.pendingLegalJudgment m := by
  rw [closure_boundary4_solverIncomplete op input profile pr h]
  intro hEq
  cases hEq

/-! ============================================================
    第四节 ⑤：两套聚合，各自成族（无桥接）
    ============================================================ -/

/-- 中文说明：`TrustLE`（`ULM14CoverageTrust.lean:85-90`）的自反性，族归纳用。 -/
theorem trustLE_refl (a : TrustVector) : TrustLE a a :=
  ⟨le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩

/-- 中文说明：`TrustLE` 的传递性，族归纳用。 -/
theorem trustLE_trans {a b c : TrustVector} (hab : TrustLE a b) (hbc : TrustLE b c) :
    TrustLE a c := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hab
  obtain ⟨k1, k2, k3, k4, k5⟩ := hbc
  exact ⟨le_trans h1 k1, le_trans h2 k2, le_trans h3 k3, le_trans h4 k4, le_trans h5 k5⟩

/-- 中文说明：界定定理⑤（主干内·信任向量版）的声明操作族：恒等、
与一份信任向量取逐坐标 meet（`ULM14CoverageTrust.lean:78` 的 `TrustVector.meet`）、
族内复合。族内**没有**取 max、取均值、追加保证的任何运算。 -/
inductive TrustAggregateOp : Type where
  | identity : TrustAggregateOp
  | meetWith (a : TrustVector) (g : TrustAggregateOp) : TrustAggregateOp
  | compose (h g : TrustAggregateOp) : TrustAggregateOp

/-- 中文说明：族的语义。 -/
def TrustAggregateOp.run : TrustAggregateOp → TrustVector → TrustVector
  | .identity => fun t => t
  | .meetWith a g => fun t => TrustVector.meet (g.run t) a
  | .compose h g => fun t => h.run (g.run t)

/-- 中文说明（界定定理⑤·主干版封闭性）：族内任一运算的输出在逐坐标序下**不高于**输入，
即有限次 meet 与有限次复合都不能提高保证；用主干 `trust_meet_le_left`
（`ULM14CoverageTrust.lean:92`）与上面的传递性做族归纳。
本条只对该归纳族封闭；族外的写法未被排除（例如自己写一个逐坐标取 max 的函数）。 -/
theorem closure_boundary5_trust_not_raised (op : TrustAggregateOp) :
    ∀ (t : TrustVector), TrustLE (op.run t) t := by
  induction op with
  | identity => intro t; exact trustLE_refl t
  | meetWith a g ih =>
      intro t
      exact trustLE_trans (trust_meet_le_left (g.run t) a) (ih t)
  | compose h g ihh ihg =>
      intro t
      exact trustLE_trans (ihh (g.run t)) (ihg t)

/-- 中文说明：⑤主干版的具体化 —— proof 坐标不因族内聚合而升高。 -/
theorem closure_boundary5_trust_proof_le (op : TrustAggregateOp) (t : TrustVector) :
    (op.run t).proof ≤ t.proof := by
  obtain ⟨_, _, _, hproof, _⟩ := closure_boundary5_trust_not_raised op t
  exact hproof

/-- 中文说明：界定定理⑤（主干外·权限秩版）的声明操作族：单层投票、
同层重复 n 轮、族内并行合并（秩的聚合是 `ReceiptAuthority.lean:102` 的 `consensusRank`）。
族内**没有** authority receipt，也没有任何"取更大秩"的运算；
`AuthorityLattice.lean:12-17` 的四种自动晋级机制不是本族的生成方式。 -/
inductive ConsensusOp : Type where
  | vote (l : AuthorityLevel) : ConsensusOp
  | rounds (n : Nat) (l : AuthorityLevel) : ConsensusOp
  | merge (a b : ConsensusOp) : ConsensusOp

/-- 中文说明：族的语义 —— 该共识结构实际收到的层级多重集。 -/
def ConsensusOp.levels : ConsensusOp → List AuthorityLevel
  | .vote l => [l]
  | .rounds n l => List.replicate n l
  | .merge a b => a.levels ++ b.levels

/-- 中文说明：`consensusRank`（秩的 foldr-max）不超过一个界，
只要每个投票的秩都不超过该界。 -/
theorem consensusRank_le_of_le {levels : List AuthorityLevel} {K : Nat}
    (h : ∀ l ∈ levels, authorityRank l ≤ K) : consensusRank levels ≤ K := by
  induction levels with
  | nil => exact Nat.zero_le K
  | cons y ys ih =>
      have hy : authorityRank y ≤ K := h y List.mem_cons_self
      have hi : consensusRank ys ≤ K := ih (fun l hl => h l (List.mem_cons_of_mem y hl))
      show max (authorityRank y) (consensusRank ys) ≤ K
      exact Nat.max_le.2 ⟨hy, hi⟩

/-- 中文说明（界定定理⑤·主干外版权限秩版封闭性）：族内任意复合共识的秩
不超过任何一个"所有投票都不超过"的界；特别地，同级任意多次共识不能把秩抬到该级之上。
证明是 `ConsensusOp` 上的结构归纳。
诚实边界：主干外三条载体 `consensus_does_not_escalate`（`ReceiptAuthority.lean:106`）、
`no_auto_escalation` 与 `escalation_requires_rank_increase`（`AuthorityLattice.lean:24,30`）
同主干内的 `TrustVector.meet` 之间**仍无桥接定理**，本文件不定义任何转换，
两版各自对自己族封闭（§五禁止六类之间的桥接等价主张）。
本条只对该归纳族封闭；族外的写法未被排除。 -/
theorem closure_boundary5_consensus_not_escalating (op : ConsensusOp) :
    ∀ (bound : AuthorityLevel),
      (∀ e ∈ op.levels, authorityRank e ≤ authorityRank bound) →
        consensusRank op.levels ≤ authorityRank bound := by
  induction op with
  | vote l => intro bound hb; exact consensusRank_le_of_le hb
  | rounds n l =>
      intro bound hb
      refine consensusRank_le_of_le ?_
      intro e he
      simp only [ConsensusOp.levels, List.mem_replicate] at he
      rw [he.2]
      exact hb l (List.mem_replicate.mpr ⟨he.1, rfl⟩)
  | merge a b _ha _hb => intro bound hb; exact consensusRank_le_of_le hb

/-- 中文说明：⑤主干外版推论 —— 族内共识不可能恰好跳到比界高一级的位置，
与主干 `escalation_requires_rank_increase`（`AuthorityLattice.lean:30`）同型。 -/
theorem consensus_cannot_reach_next_rank (op : ConsensusOp) (bound : AuthorityLevel)
    (hb : ∀ e ∈ op.levels, authorityRank e ≤ authorityRank bound) :
    authorityRank bound + 1 ≠ consensusRank op.levels := by
  intro h
  have hle := closure_boundary5_consensus_not_escalating op bound hb
  rw [← h] at hle
  exact Nat.not_succ_le_self _ hle

/-! ============================================================
    第五节 ⑥：污染传播路径的归纳类与真封闭
    ============================================================ -/

/-- 中文说明：污点 join 的枚举事实（二元格，逐情形 `rfl`）；
主干 `joinTaint` 见 `TaintNoninterference.lean:25-27`。 -/
theorem joinTaint_clean_right (t : Taint) : joinTaint t .clean = t := by
  cases t <;> rfl

theorem joinTaint_clean_left (t : Taint) : joinTaint .clean t = t := by
  cases t <;> rfl

theorem joinTaint_tainted_left (t : Taint) : joinTaint .tainted t = .tainted := by
  cases t <;> rfl

theorem joinTaint_idem (t : Taint) : joinTaint t t = t := by
  cases t <;> rfl

theorem joinTaint_assoc (a b c : Taint) :
    joinTaint (joinTaint a b) c = joinTaint a (joinTaint b c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- 中文说明：主干 `taintOfInputs`（`TaintNoninterference.lean:30-32`）的两条计算式。 -/
theorem taintOfInputs_nil : taintOfInputs ([] : List FormalInput) = .clean := rfl

theorem taintOfInputs_cons (x : FormalInput) (xs : List FormalInput) :
    taintOfInputs (x :: xs) = joinTaint x.taint (taintOfInputs xs) := rfl

/-- 中文说明：主干 `stageOutput`（`TaintNoninterference.lean:36-37`）的污点
就是输入池的 join —— 这正是⑥的类型层载体。 -/
theorem stageOutput_taint (xs : List FormalInput) (c : String) :
    (stageOutput xs c).taint = taintOfInputs xs := rfl

/-- 中文说明：输入池拼接的总污点等于两半总污点的 join。 -/
theorem taintOfInputs_append (xs ys : List FormalInput) :
    taintOfInputs (xs ++ ys) = joinTaint (taintOfInputs xs) (taintOfInputs ys) := by
  induction xs with
  | nil => simp only [List.nil_append, taintOfInputs_nil, joinTaint_clean_left]
  | cons x xs ih =>
      rw [List.cons_append, taintOfInputs_cons, ih, taintOfInputs_cons, joinTaint_assoc]

/-- 中文说明：尾部追加一个输入后的总污点。 -/
theorem taintOfInputs_snoc (xs : List FormalInput) (y : FormalInput) :
    taintOfInputs (xs ++ [y]) = joinTaint (taintOfInputs xs) y.taint := by
  rw [taintOfInputs_append, taintOfInputs_cons, taintOfInputs_nil, joinTaint_clean_right]

/-- 中文说明：界定定理⑥的声明操作族 —— §六要求"把 stage 集合形式化为归纳类"，即此族：
注入一个形式输入、施加一次推导阶段（Horn / AAF / solver 的统一抽象）、
合并两条流水线、整份重复上送。 -/
inductive TaintPipeline : Type where
  | input (x : FormalInput) : TaintPipeline
  | stage (p : TaintPipeline) (conclusion : String) : TaintPipeline
  | merge (p q : TaintPipeline) : TaintPipeline
  | resubmit (p : TaintPipeline) : TaintPipeline

/-- 中文说明：族的输入池语义 —— `stage` 把推出物也放回输入池，
`resubmit` 把整池复制一份（重复提交）。 -/
def TaintPipeline.inputs : TaintPipeline → List FormalInput
  | .input x => [x]
  | .stage p c => p.inputs ++ [stageOutput p.inputs c]
  | .merge p q => p.inputs ++ q.inputs
  | .resubmit p => p.inputs ++ p.inputs

/-- 中文说明：族的根污点语义；它与主干 `taintOfInputs` 的一致性由
`poolTaint_eq_taintOfInputs` 钉住，否则本定义只是自造玩具。 -/
def TaintPipeline.poolTaint : TaintPipeline → Taint
  | .input x => x.taint
  | .stage p _ => p.poolTaint
  | .merge p q => joinTaint p.poolTaint q.poolTaint
  | .resubmit p => p.poolTaint

/-- 中文说明：可信性桥接 —— 归纳族的根污点**就是**输入池在主干 `taintOfInputs`
下的总污点。四条生成方式各一支，其中 `merge` / `resubmit` / `stage` 三支用到
join 的结合律、幺元与幂等。 -/
theorem poolTaint_eq_taintOfInputs (p : TaintPipeline) :
    p.poolTaint = taintOfInputs p.inputs := by
  induction p with
  | input x =>
      show x.taint = joinTaint x.taint .clean
      rw [joinTaint_clean_right]
  | stage p c ih =>
      show p.poolTaint = taintOfInputs (p.inputs ++ [stageOutput p.inputs c])
      rw [ih, taintOfInputs_snoc, stageOutput_taint, joinTaint_idem]
  | merge p q ihp ihq =>
      show joinTaint p.poolTaint q.poolTaint = taintOfInputs (p.inputs ++ q.inputs)
      rw [ihp, ihq, taintOfInputs_append]
  | resubmit p ih =>
      show p.poolTaint = taintOfInputs (p.inputs ++ p.inputs)
      rw [ih, taintOfInputs_append, joinTaint_idem]

/-- 中文说明：污染的归纳传播类 —— 四条生成方式即本族承认的全部传播路径。
表格记的"污染格的全部传播路径未枚举"这一待办，在本族内由该归纳定义闭合。 -/
inductive CarriesTaint : TaintPipeline → Prop where
  | injected (x : FormalInput) (hx : x.taint = .tainted) : CarriesTaint (.input x)
  | viaStage (p : TaintPipeline) (c : String) (hp : CarriesTaint p) :
      CarriesTaint (.stage p c)
  | viaMergeLeft (p q : TaintPipeline) (hp : CarriesTaint p) : CarriesTaint (.merge p q)
  | viaMergeRight (p q : TaintPipeline) (hq : CarriesTaint q) : CarriesTaint (.merge p q)
  | viaResubmit (p : TaintPipeline) (hp : CarriesTaint p) : CarriesTaint (.resubmit p)

/-- 中文说明（界定定理⑥·封闭性主文）：族内任意流水线，只要污染是按本族承认的
四条路径传播进来的，其根污点恒为 `tainted`；stage / merge / resubmit 的**任意有限复合**
由一支族归纳一次覆盖。这是六条中达到真正族封闭的一条：
主干五条引理（`TaintNoninterference.lean:43,56,80,86,95`）只覆盖 join / stage / majority
三个操作，本条覆盖该族的全体组合。
本条只对该归纳族封闭；族外的写法未被排除（例如另写一个把 `Bool false` 读成 clean 的函数）。 -/
theorem closure_boundary6_taint_never_cleaned {p : TaintPipeline} (h : CarriesTaint p) :
    p.poolTaint = .tainted := by
  induction h with
  | injected x hx => exact hx
  | viaStage p' c hp ih => exact ih
  | viaMergeLeft p' q hp ih =>
      show joinTaint p'.poolTaint q.poolTaint = .tainted
      rw [ih]
      exact joinTaint_tainted_left q.poolTaint
  | viaMergeRight p' q hq ih =>
      show joinTaint p'.poolTaint q.poolTaint = .tainted
      rw [ih]
      exact join_with_tainted_is_tainted p'.poolTaint
  | viaResubmit p' hp ih => exact ih

/-- 中文说明：⑥的推论 —— 族内受污流水线的输入池在主干度量下同样是 tainted。 -/
theorem taintOfInputs_of_carriesTaint {p : TaintPipeline} (h : CarriesTaint p) :
    taintOfInputs p.inputs = .tainted := by
  rw [← poolTaint_eq_taintOfInputs]
  exact closure_boundary6_taint_never_cleaned h

/-- 中文说明：受污源一定出现在输入池里（传播类与池的相容性；反向不收录，
因为"池中每个元素都由族内路径引入"需要运行期溯源精化）。 -/
theorem exists_tainted_in_inputs {p : TaintPipeline} (h : CarriesTaint p) :
    ∃ x ∈ p.inputs, x.taint = .tainted := by
  induction h with
  | injected x hx => exact ⟨x, List.mem_cons_self, hx⟩
  | viaStage p' c hp ih =>
      obtain ⟨x, hx, ht⟩ := ih
      exact ⟨x, List.mem_append.mpr (Or.inl hx), ht⟩
  | viaMergeLeft p' q hp ih =>
      obtain ⟨x, hx, ht⟩ := ih
      exact ⟨x, List.mem_append.mpr (Or.inl hx), ht⟩
  | viaMergeRight p' q hq ih =>
      obtain ⟨x, hx, ht⟩ := ih
      exact ⟨x, List.mem_append.mpr (Or.inr hx), ht⟩
  | viaResubmit p' hp ih =>
      obtain ⟨x, hx, ht⟩ := ih
      exact ⟨x, List.mem_append.mpr (Or.inl hx), ht⟩

/-- 中文说明：n 次重复上送同一输入所得的族成员。 -/
def resubmitTimes : Nat → FormalInput → TaintPipeline
  | 0, x => .input x
  | n + 1, x => .resubmit (resubmitTimes n x)

/-- 中文说明：⑥"重复不洗白"的族版 —— 主干 `repetition_does_not_clean`
（`TaintNoninterference.lean:95`）只管一次 cons，本条覆盖任意有限次重复上送。 -/
theorem resubmitTimes_carriesTaint (x : FormalInput) (hx : x.taint = .tainted) (n : Nat) :
    CarriesTaint (resubmitTimes n x) := by
  induction n with
  | zero => exact CarriesTaint.injected x hx
  | succ n ih => exact CarriesTaint.viaResubmit _ ih

/-- 中文说明：⑥的另一面 —— 整池重复提交不改变总污点（对族内任意成员成立的等式）。 -/
theorem resubmit_preserves_total_taint (p : TaintPipeline) :
    taintOfInputs ((TaintPipeline.resubmit p).inputs) = taintOfInputs p.inputs := by
  show taintOfInputs (p.inputs ++ p.inputs) = taintOfInputs p.inputs
  rw [taintOfInputs_append, joinTaint_idem]

/-! ============================================================
    第六节 界定定理不是全调用链主张（本文件的围栏）
    ============================================================ -/

/-- 中文说明：把仓内既有 FAIL 判据正定理化：
`docs/history/evidence-archive/0923_四报告与锤击/法律统一数学模型_四报告与跨仓审查_20260923.md:555`
——"构造子区别或指定 map 不转换，并不禁止另写忽略输入、返回 complete 的函数；
全路径保证需封装及精化"。本条用存在式证成那句话：族外**确实**有这种函数。
因此本文件六条封闭性都是"对声明族封闭"，绝不可读成"六类失真在全部代码中无法表达"。 -/
theorem delimitation_is_not_general :
    ∃ (f : Outcome Nat → Outcome Nat),
      ∀ (e : FailureCore), f (.failure e) = Outcome.complete (42 : Nat) :=
  ⟨fun _ => .complete 42, fun _ => rfl⟩

/-- 中文说明：围栏的另一半 —— 上述洗白函数不等于任何族内成员：
族内成员在任意一个 `failure` 输入上的值都是该 `failure` 本身。 -/
theorem boundary1_family_excludes_launderer {α β : Type} (op : OutcomeMapOp α β)
    (e : FailureCore) (y : β) :
    op.run (.failure e) ≠ (fun _ : Outcome α => Outcome.complete y) (.failure e) := by
  rw [OutcomeMapOp.closure_boundary1_no_failure_upgrade op e]
  exact Outcome.failure_ne_complete e y

end JurisLean.Seams.BoundaryClosure
