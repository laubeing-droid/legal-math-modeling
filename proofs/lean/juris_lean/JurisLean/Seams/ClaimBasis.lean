/-!
P-034 —— 请求权基础链（Anspruchsmethode 四段检验）的法律语义、数学对象与缝合定理。

## 一、法律语义（人话）
一个请求权从被主张到能被强制实现，按检验序要过四段：

1. **成立**（权利形成要件）：主张人所依据规范自身的要件是否成就。例《民法典》第577条把
   "不履行或者履行不符合约定"与"继续履行、采取补救措施或者赔偿损失"连成一条责任规范，
   其要件结构即成立段的检验材料。
2. **障碍**（抗辩权，一时阻却）：请求权已存在，但相对人可拒绝给付。《民法典》第192条第一款
   令时效届满时义务人"可以提出不履行义务的抗辩"，第二款又令同意履行者不得再以时效届满抗辩——
   同一条文里"阻却"与"阻却之除去"并存，而请求权本身并未消灭。第193条规定人民法院不得主动
   适用诉讼时效，说明该段效果须由主张者发动。
3. **消灭**（权利消灭事由）：请求权本身不复存在。《民法典》第557条列举清偿、抵销、提存、免除、
   混同等终止情形。
4. **可行使**（强制实现的障碍）：请求权存续且未被阻却，但不能请求以强制方式实现。
   《民法典》第580条对特定非金钱债务排除继续履行请求。

四段的差异是结构性的而非修辞性的：**障碍除去后请求权复活，消灭是终局**。本件把这一区别做成
类型层事实——`Step` 没有从 `extinguished` 出发到成立的构造子（`extinguished_never_revives`），
而 `suspended`、`unenforceable` 确有除回去的路（`defenseDefused`、`enforceabilityRestored`），
不靠注释约定或运行期检查。

## 二、数学对象
- `Stage`：四段；`Polarity`：该段规范在本节点上是命中（fire）还是除去阻却（defuse）。
- `Node`：链节点 = ⟨段、极性、本案条件是否成就、规范引证⟩。规范引证是字段而非外挂标签，
  结论要能追溯到它。
- `Status`：尚未成立 ∥ 成立 ∥ 被阻却 ∥ 已消灭 ∥ 不可强制实现。
- `fires`/`Step`：单节点转移的自然语义（9 个构造子，每个把输入与输出写成具体状态）。
- `Walk s cs t`：链 `cs` 把起点状态 `s` 推进到 `t`。
- `CitedAt cs b` / `CarriesCreationBasis cs`：链 `cs` 在位置 `b` 含一条成立段命中规范；
  后者声明该链携带引证。引证位置由构造子携带，不是事后贴标签。

## 三、本件证什么、不证什么
**正定理**（`walk_verdict_needs_basis` 与其推论，链上归纳）：从"尚未成立"出发，凡得出任何
非"尚未成立"的法律地位——成立、被阻却、不可强制实现、已消灭——该链都必携带一条成立段命中
规范。也就是"没有成立就没有阻却、没有消灭"，在语义层不能凭空产出结论。
**反向（穷尽性）是条件定理**（`exhaustive_refutation`）："候选表内无一成立 ⇒ 本案无基础"
只在语料被显式声明为封闭（`hclosed`）时成立；`closure_premise_is_not_free` 给出缺该前提时
结论失败的具体见证。一般图可达与 Horn 闭包正确都替代不了本件：
`order_matters_same_node_set_different_verdict` 与 `reachable_but_not_established` 说明同一
无序节点集在不同检验序下结论不同，可达性为真时按序检验的结论可以只是"被阻却"。
本件**不**定义证据标准、不定义制度后果、也不认定任何真实案件的请求权成立与否。

## 四、落点
成立段的规范适用与要件推导 = S1；各段条件在本案中是否成就（事实与证据）= S2；
可行使段的强制实现与救济后果 = S5。

## 五、文献锚与档位
请求权基础方法：Medicus《民法总论》、王泽鉴《法律思维与民法实例》。
请求权基础方法 × Lean 形式化：检索零命中，故本件为 **[代拟稿]**（Owner 2026-09-30 授权
参照文献代拟）。条文编号取自仓内已作规则结构检验并核验过的条文集（第192、193、195、199、557、
558、577、580条，最高人民法院发布文本；见
`docs/history/evidence-archive/0923_四报告与锤击/法律统一数学模型_四报告与跨仓审查_20260923.md:985`，
该处已记录发布文本截断至第1111条的隐患，本件所引均在此范围内）。条文用于规则结构检验，
不构成对任何具体案件的事实认定或胜败判断。
档位：定义为 [构造性定义]；定理在本件内给出完整证明，编译认定待 CI，本地不称 PASS。
-/

namespace JurisLean.Seams.ClaimBasis

/-- 请求权基础检验的四段。 -/
inductive Stage
  | creation     -- 成立：权利形成要件
  | obstacle     -- 障碍：抗辩权（一时阻却）
  | extinction   -- 消灭：权利消灭事由
  | exercisable  -- 可行使：强制实现的条件
  deriving Repr

/-- 节点在该段上的作用方向：使命中该段规范，或除去该段已发生的阻却。 -/
inductive Polarity
  | fire
  | defuse
  deriving Repr

/-- 检验过程中的法律地位。 -/
inductive Status
  | notYet         -- 尚未成立
  | established    -- 成立且未被后续段影响
  | suspended      -- 被抗辩一时阻却（请求权仍存续）
  | extinguished   -- 已消灭（终局）
  | unenforceable  -- 存续但不得请求强制实现
  deriving Repr

/-- 链节点：段、极性、本案条件是否成就、规范引证。 -/
structure Node where
  stage : Stage
  polarity : Polarity
  holds : Bool
  normId : String
  deriving Repr

/-- 裁决表：给定状态下，该段该极性的节点是否触发状态转移。
    条件未成就（`holds = false`）的规范一律不触发；已消灭之后一律不触发。 -/
def fires : Status → Stage → Polarity → Bool → Bool
  | Status.notYet, Stage.creation, Polarity.fire, true => true
  | Status.established, Stage.obstacle, Polarity.fire, true => true
  | Status.established, Stage.extinction, Polarity.fire, true => true
  | Status.established, Stage.exercisable, Polarity.fire, true => true
  | Status.suspended, Stage.extinction, Polarity.fire, true => true
  | Status.suspended, Stage.obstacle, Polarity.defuse, true => true
  | Status.unenforceable, Stage.extinction, Polarity.fire, true => true
  | Status.unenforceable, Stage.exercisable, Polarity.defuse, true => true
  | _, _, _, _ => false

/-- 表行见证：抗辩打在尚未成立的请求上不触发（第193条"不得主动适用"的结构面）。 -/
theorem fires_notYet_obstacle_is_false (pol : Polarity) (hb : Bool) :
    fires Status.notYet Stage.obstacle pol hb = false := rfl

/-- 表行见证：已消灭之后任何段、任何极性都不触发。 -/
theorem fires_extinguished_is_never_true
    (st : Stage) (pol : Polarity) (hb : Bool) :
    fires Status.extinguished st pol hb = false := rfl

/-- 单节点转移语义。每个构造子都把输入与输出写成具体状态，因此"这一结论是从哪一步得到的"
    是可从构造子直接读出的事实，不需要对函数值做反演。 -/
inductive Step : Status → Node → Status → Prop where
  | createFire (cn : Node) (h1 : cn.stage = Stage.creation)
      (h2 : cn.polarity = Polarity.fire) (h3 : cn.holds = true) :
      Step Status.notYet cn Status.established
  | obstacleFire (n : Node) (h1 : n.stage = Stage.obstacle)
      (h2 : n.polarity = Polarity.fire) (h3 : n.holds = true) :
      Step Status.established n Status.suspended
  | extinctionFromEstablished (n : Node) (h1 : n.stage = Stage.extinction)
      (h2 : n.polarity = Polarity.fire) (h3 : n.holds = true) :
      Step Status.established n Status.extinguished
  | enforceabilityBlocked (n : Node) (h1 : n.stage = Stage.exercisable)
      (h2 : n.polarity = Polarity.fire) (h3 : n.holds = true) :
      Step Status.established n Status.unenforceable
  | extinctionFromSuspended (n : Node) (h1 : n.stage = Stage.extinction)
      (h2 : n.polarity = Polarity.fire) (h3 : n.holds = true) :
      Step Status.suspended n Status.extinguished
  | defenseDefused (n : Node) (h1 : n.stage = Stage.obstacle)
      (h2 : n.polarity = Polarity.defuse) (h3 : n.holds = true) :
      Step Status.suspended n Status.established
  | extinctionFromUnenforceable (n : Node) (h1 : n.stage = Stage.extinction)
      (h2 : n.polarity = Polarity.fire) (h3 : n.holds = true) :
      Step Status.unenforceable n Status.extinguished
  | enforceabilityRestored (n : Node) (h1 : n.stage = Stage.exercisable)
      (h2 : n.polarity = Polarity.defuse) (h3 : n.holds = true) :
      Step Status.unenforceable n Status.established
  | pass (s : Status) (n : Node)
      (h : fires s n.stage n.polarity n.holds = false) :
      Step s n s

/-- 链的推导关系：把起点状态按节点依次推进。构造子参数全显式，使归纳时的分支名数固定。 -/
inductive Walk : Status → List Node → Status → Prop where
  | nil (s : Status) : Walk s [] s
  | cons (s s' s'' : Status) (n : Node) (t : List Node) :
      Step s n s' → Walk s' t s'' → Walk s (n :: t) s''

/-- 推进一步（隐式参数版，供见证与后续件使用）。 -/
theorem walkStep {s s' s'' : Status} {n : Node} {t : List Node}
    (h1 : Step s n s') (h2 : Walk s' t s'') : Walk s (n :: t) s'' :=
  Walk.cons s s' s'' n t h1 h2

/-- 链 `cs` 在位置 `b` 携带一条成立段命中规范。 -/
inductive CitedAt : List Node → Node → Prop where
  | here (n : Node) (t : List Node) (h1 : n.stage = Stage.creation)
      (h2 : n.polarity = Polarity.fire) (h3 : n.holds = true) :
      CitedAt (n :: t) n
  | inTail (m : Node) (t : List Node) (b : Node) :
      CitedAt t b → CitedAt (m :: t) b

/-- 链携带成立段引证：存在一个节点处于该链的引证位置。 -/
def CarriesCreationBasis (cs : List Node) : Prop :=
  ∃ b, CitedAt cs b

theorem notYet_ne_established : Status.notYet ≠ Status.established := by
  intro h
  cases h

theorem suspended_ne_established : Status.suspended ≠ Status.established := by
  intro h
  cases h

theorem extinguished_ne_established : Status.extinguished ≠ Status.established := by
  intro h
  cases h

theorem unenforceable_ne_established :
    Status.unenforceable ≠ Status.established := by
  intro h
  cases h

/-- 五个结论标签两两不同：本模型的终局状态不会因构造子混淆而合并。 -/
theorem status_five_labels_pairwise_distinct :
    Status.notYet ≠ Status.established ∧ Status.notYet ≠ Status.suspended ∧
      Status.notYet ≠ Status.extinguished ∧ Status.notYet ≠ Status.unenforceable ∧
      Status.established ≠ Status.suspended ∧ Status.established ≠ Status.extinguished ∧
      Status.established ≠ Status.unenforceable ∧ Status.suspended ≠ Status.extinguished ∧
      Status.suspended ≠ Status.unenforceable ∧
      Status.extinguished ≠ Status.unenforceable := by
  refine ⟨notYet_ne_established, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h

/-- **消灭是终局**：没有任何单步把已消灭带回成立。这是"消灭 ≠ 障碍"的形式面；
    障碍段除去则确有出边（`Step.defenseDefused`）。 -/
theorem extinguished_never_revives {n : Node} :
    Step Status.extinguished n Status.established → False := by
  intro h
  cases h

/-- 链首步分解：任何非空链的推导都先走一步，再走剩下的链。 -/
theorem walk_cons_cases {s s'' : Status} {n : Node} {t : List Node}
    (h : Walk s (n :: t) s'') :
    ∃ s', Step s n s' ∧ Walk s' t s'' := by
  cases h with
  | cons sl sr st nn tl hstep htail => exact ⟨sr, hstep, htail⟩

/-- 引证的位置是结构化的：要么就在链首，要么落在链尾之中。 -/
theorem citedAt_head_or_tail {n : Node} {t : List Node} {b : Node}
    (h : CitedAt (n :: t) b) : b = n ∨ CitedAt t b := by
  cases h with
  | here nn tt c1 c2 c3 => left; rfl
  | inTail m tt bb hrec => right; exact hrec

/-- 单元链的引证直接交出该节点的三字段：段、极性、条件成就。 -/
theorem citedAt_singleton_fields (n : Node) (h : CitedAt [n] n) :
    n.stage = Stage.creation ∧ n.polarity = Polarity.fire ∧ n.holds = true := by
  cases h with
  | here nn tt c1 c2 c3 => exact ⟨c1, c2, c3⟩
  | inTail m tt bb hrec => cases hrec

/-- **正定理（链上归纳）**：链从零起点（尚未成立）出发，凡终局不是"尚未成立"，
    该链必携带一条成立段命中规范。 -/
theorem walk_verdict_needs_basis :
    ∀ (cs : List Node) (s t : Status), Walk s cs t →
      s = Status.notYet → t ≠ Status.notYet → CarriesCreationBasis cs := by
  intro cs
  induction cs with
  | nil =>
      intro s t h hs ht
      cases h with
      | nil sl => exact (ht hs).elim
  | cons n tail ih =>
      intro s t h hs ht
      cases walk_cons_cases h with
      | intro s' hand =>
          cases hand with
          | intro hstep htail =>
              cases hstep with
              | createFire cn c1 c2 c3 =>
                  exact ⟨cn, CitedAt.here cn tail c1 c2 c3⟩
              | pass ps pn pf =>
                  cases ih ps t htail hs ht with
                  | intro b hb => exact ⟨b, CitedAt.inTail pn tail b hb⟩
              | obstacleFire => cases hs
              | extinctionFromEstablished => cases hs
              | enforceabilityBlocked => cases hs
              | extinctionFromSuspended => cases hs
              | defenseDefused => cases hs
              | extinctionFromUnenforceable => cases hs
              | enforceabilityRestored => cases hs

/-- 推论一：终局"成立"必有成立段引证。 -/
theorem established_cites_creation_basis
    {cs : List Node} (h : Walk Status.notYet cs Status.established) :
    CarriesCreationBasis cs :=
  walk_verdict_needs_basis cs Status.notYet Status.established h rfl
    (by intro hh; cases hh)

/-- 推论二：终局"被阻却"同样必须有成立段引证（无成立即无所谓阻却）。 -/
theorem suspended_cites_creation_basis
    {cs : List Node} (h : Walk Status.notYet cs Status.suspended) :
    CarriesCreationBasis cs :=
  walk_verdict_needs_basis cs Status.notYet Status.suspended h rfl
    (by intro hh; cases hh)

/-- 推论三：终局"不可强制实现"同样必须有成立段引证。 -/
theorem unenforceable_cites_creation_basis
    {cs : List Node} (h : Walk Status.notYet cs Status.unenforceable) :
    CarriesCreationBasis cs :=
  walk_verdict_needs_basis cs Status.notYet Status.unenforceable h rfl
    (by intro hh; cases hh)

/-- 推论四：终局"已消灭"同样必须有成立段引证（消灭以请求权存在为前提）。 -/
theorem extinguished_cites_creation_basis
    {cs : List Node} (h : Walk Status.notYet cs Status.extinguished) :
    CarriesCreationBasis cs :=
  walk_verdict_needs_basis cs Status.notYet Status.extinguished h rfl
    (by intro hh; cases hh)

/-- 见证与检验材料：条件成就的成立段规范。 -/
def art577 : Node :=
  { stage := Stage.creation, polarity := Polarity.fire, holds := true,
    normId := "民法典-577" }

/-- 要件不成就的成立段规范。 -/
def art577Unmet : Node :=
  { stage := Stage.creation, polarity := Polarity.fire, holds := false,
    normId := "民法典-577" }

/-- 时效抗辩（第192条第一款）。 -/
def art192Defense : Node :=
  { stage := Stage.obstacle, polarity := Polarity.fire, holds := true,
    normId := "民法典-192一" }

/-- 同意履行致时效抗辩不得再主张（第192条第二款）。 -/
def art192Consent : Node :=
  { stage := Stage.obstacle, polarity := Polarity.defuse, holds := true,
    normId := "民法典-192二" }

/-- 清偿致债权债务终止（第557条第一款第一项）。 -/
def art557Payment : Node :=
  { stage := Stage.extinction, polarity := Polarity.fire, holds := true,
    normId := "民法典-557一款一项" }

/-- 非金钱债务排除继续履行请求（第580条）。 -/
def art580Blocked : Node :=
  { stage := Stage.exercisable, polarity := Polarity.fire, holds := true,
    normId := "民法典-580" }

/-- 见证一：成立段单节点命中得"成立"，故正定理的适用域非空，且该链确实携带引证。 -/
theorem witness_creation_basis_established :
    Walk Status.notYet [art577] Status.established :=
  walkStep (Step.createFire art577 rfl rfl rfl) (Walk.nil Status.established)

theorem witness_established_chain_is_cited :
    CarriesCreationBasis [art577] :=
  established_cites_creation_basis witness_creation_basis_established

/-- 见证二：要件不成就停在"尚未成立"，不得跳到成立。 -/
theorem witness_unmet_elements_stay_notYet :
    Step Status.notYet art577Unmet Status.notYet :=
  Step.pass Status.notYet art577Unmet rfl

/-- 见证三：抗辩打在已成立的请求上得"被阻却"，而非"已消灭"。 -/
theorem witness_defense_suspends_not_extinguishes :
    Walk Status.notYet [art577, art192Defense] Status.suspended :=
  walkStep (Step.createFire art577 rfl rfl rfl)
    (walkStep (Step.obstacleFire art192Defense rfl rfl rfl)
      (Walk.nil Status.suspended))

/-- 见证四：抗辩除去后请求权复活，故障碍与消灭在结构上不同。 -/
theorem witness_defense_defusal_restores :
    Walk Status.notYet [art577, art192Defense, art192Consent] Status.established :=
  walkStep (Step.createFire art577 rfl rfl rfl)
    (walkStep (Step.obstacleFire art192Defense rfl rfl rfl)
      (walkStep (Step.defenseDefused art192Consent rfl rfl rfl)
        (Walk.nil Status.established)))

/-- 复活后的结论仍带引证：除去抗辩不产生"无基础的成立"。 -/
theorem witness_restored_claim_still_cited :
    CarriesCreationBasis [art577, art192Defense, art192Consent] :=
  established_cites_creation_basis witness_defense_defusal_restores

/-- 见证五：消灭事由穿透仍在阻却中的请求权，故消灭优先于障碍。 -/
theorem witness_extinction_reaches_past_defense :
    Walk Status.notYet [art577, art192Defense, art557Payment] Status.extinguished :=
  walkStep (Step.createFire art577 rfl rfl rfl)
    (walkStep (Step.obstacleFire art192Defense rfl rfl rfl)
      (walkStep (Step.extinctionFromSuspended art557Payment rfl rfl rfl)
        (Walk.nil Status.extinguished)))

/-- 见证六：请求权存续但强制实现被排除（第580条式）。 -/
theorem witness_enforceability_blocked :
    Walk Status.notYet [art577, art580Blocked] Status.unenforceable :=
  walkStep (Step.createFire art577 rfl rfl rfl)
    (walkStep (Step.enforceabilityBlocked art580Blocked rfl rfl rfl)
      (Walk.nil Status.unenforceable))

/-- 边界：抗辩不得先于请求权成立而发动（该节点在"尚未成立"上是惰性的）。 -/
theorem defense_on_unestablished_is_inert :
    Step Status.notYet art192Defense Status.notYet :=
  Step.pass Status.notYet art192Defense rfl

/-- **反"图可达"边界定理**：节点集相同、检验序不同，结论不同。
    故"存在一条可成立的基础路径"不等于"按序检验的结论是成立"。 -/
theorem order_matters_same_node_set_different_verdict :
    Walk Status.notYet [art577, art192Defense] Status.suspended ∧
      Walk Status.notYet [art192Defense, art577] Status.established ∧
        Status.suspended ≠ Status.established :=
  ⟨witness_defense_suspends_not_extinguishes,
    walkStep defense_on_unestablished_is_inert
      (walkStep (Step.createFire art577 rfl rfl rfl)
        (Walk.nil Status.established)),
    suspended_ne_established⟩

/-- 可达性谓词：链中存在一条命中的成立段规范即为可达；它对检验序不敏感。 -/
def reachableBySomeBasis : List Node → Bool
  | [] => false
  | n :: t =>
      match n.stage, n.polarity, n.holds with
      | Stage.creation, Polarity.fire, true => true
      | _, _, _ => reachableBySomeBasis t

/-- 可达为真而按序结论为"被阻却"的具体见证：可达性不能充当成立判据。 -/
theorem reachable_but_not_established :
    reachableBySomeBasis [art577, art192Defense] = true ∧
      Walk Status.notYet [art577, art192Defense] Status.suspended :=
  ⟨rfl, witness_defense_suspends_not_extinguishes⟩

/-- 候选基础表的成员关系（语料=声明为封闭的候选链表）。 -/
inductive CorpusMember : List (List Node) → List Node → Prop where
  | here (c : List Node) (rest : List (List Node)) :
      CorpusMember (c :: rest) c
  | there (d c : List Node) (rest : List (List Node)) :
      CorpusMember rest c → CorpusMember (d :: rest) c

/-- **反向（穷尽性）是条件定理**：只有当候选表被显式声明为封闭时，
    "表内无一成立"才等于"本案无可成立基础"。封闭条件是前提，不是本件的定理。 -/
theorem exhaustive_refutation (corpus : List (List Node))
    (hclosed : ∀ cs, Walk Status.notYet cs Status.established → CorpusMember corpus cs)
    (hfail : ∀ cs, CorpusMember corpus cs →
      ¬ Walk Status.notYet cs Status.established) :
    ∀ cs, ¬ Walk Status.notYet cs Status.established := by
  intro cs h
  exact hfail cs (hclosed cs h) h

/-- 封闭前提不可省：空语料下"表内无一成立"平凡为真，但表外确有可成立链。
    故缺封闭条件时，搜索无结果只支持未决，不支持"无请求权基础"。 -/
theorem closure_premise_is_not_free :
    (∀ cs, CorpusMember [] cs → ¬ Walk Status.notYet cs Status.established) ∧
      Walk Status.notYet [art577] Status.established := by
  refine ⟨?_, witness_creation_basis_established⟩
  intro cs h
  cases h

end JurisLean.Seams.ClaimBasis
