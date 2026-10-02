import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Set.Image
import Mathlib.Order.GaloisConnection.Defs
import Mathlib.Tactic
import JurisLean.LegalSpecToIVL
import JurisLean.IVLToHorn
import JurisLean.IVLToAAF
import JurisLean.HornAAFContract
import JurisLean.HornDefinitions
import JurisLean.HornFixedPoint
import JurisLean.DungDefinitions
import JurisLean.Seams.SourceNorms

/-!
老锥四跳 → Seams 八层的**对象级接入件**（计划 `docs/master-plan/12_…` W6 / 终态 G2）。

## 一、本件解决的是哪一个洞
`LegalSpecToIVL.lean:30 lowerSpec`、`IVLToHorn.lean:24 ivlToHorn`、`IVLToAAF.lean:31 ivlToAAF`、
`HornAAFContract.lean:20 compileHornArgument` 四跳各带保义定理，但 `Seams/*.lean` 对它们
**零引用**（`11_` 卷 §一 改1 实测）。`Seams/Transitions.lean` 已在 L1→L2 建了第一座桥
（`namedClosure` / `admissibleFromHorn` / `exceptionEdges` / `aafOf` + 五件保义），
本件**不重做它做过的事**，只做它上游那一层：把老锥的目标接到 Seams 的载体上，
并把"复合律"按**三档**逐跳定档。

## 二、三档定档（逐跳，理由落在算子性质上）
判据是：**单射性**决定能不能拿反向等式／插入；**守卫（谓词是否恒真）**决定第 1 跳是否与
`norms`／`attacks` 无关；**保 ⊥**决定能不能走 `FiniteGaloisAdjunction.lean:24 ResiduatedMap`。

| 复合 | 拿到的档 | 理由（可核对的性质） |
|---|---|---|
| `ivlToHorn ∘ lowerSpec` = 直接那一跳 | **第一档·严格等式** `hop1_hop2_clauses_compose_eq` | 两跳都是无守卫的 `List.map`（`LegalSpecToIVL.lean:31`、`IVLToHorn.lean:27`），`map` 逐点复合即等 |
| `compileHornArgument ∘ derivationOfClause` | **第一档·严格等式** `hop2_hop4_compose_conclusion_rule_eq` | `HornAAFContract.lean:20-31` 字段全是直读，无解析、无默认值 ⇒ 整条是 `rfl` |
| `ivlToAAF ∘ lowerSpec`（节点） | **第一档·严格等式** `hop1_hop3_nodes_compose_eq` | `IVLToAAF.lean:33` 的 `nodes` 是纯 `List.map` |
| `ivlToAAF ∘ lowerSpec`（边） | **第一档·但空洞** `hop1_hop3_edges_vanish` | `LegalSpecToIVL.lean:43` 写死 `attacks := []` ⇒ 第 1 跳**不产任何攻击材料**，边侧复合律对一切 spec 都是空等式 |
| 第 2/3 跳里的 `List → Finset` 去重 | **第二档·Galois insertion** `gi_dedup_legacyNodes` | `List.toFinset` 满射（`Mathlib/Data/Finset/Dedup.lean:131 toFinset_surjective`）⇒ 幂集上正向像 ⊣ 逆向取像是**插入**；但 `lowerRule`／`lowerWitnessedAttack` **不单射**（本件 `hop1_not_injective_general_form_is_false`、`hop3_injective_general_form_is_false` 给具名见证），故这两跳连反向等式都拿不到 |
| `closureAt ∘ hornSystemOfLegacyIVL` 对比 `ivlToAAF` 节点集 | **第三档·只保单侧可推导性** `derivable_is_legacy_node` | 闭包不出论域（`HornFixedPoint.lean:75 horn_result_subset_univ`）而论域就是节点集；**反向为假**，见 §五 |

## 三、为什么不走 `ResiduatedMap` / institutions（写成签名级限制）
- `FiniteGaloisAdjunction.lean:28 map_bot : fn ⊥ = ⊥` 对 Horn 算子**不成立**：
  `HornDefinitions.lean:37-38` 的 `TH sys S = sys.initialFacts ∪ …` 恒含 `initialFacts`，
  只要有一条无前提规则（`Transitions.lean:187 claimCase` 正是这个形状）就有 `TH ∅ ≠ ∅`。
  故本件**不**声称 Horn 侧是 residuated map，也不引用该件（除 `JurisLean.lean:6` 外八层零引用）。
- pin 的 Mathlib 全库无 `Institution`/`Comorphism`/`Fibring` 形式化，只作措辞权威
  （Goguen & Burstall 1992, DOI `10.1145/147508.147524`）。第二档因此落在 `Set` 幂集上的
  `GaloisConnection`/`GaloisInsertion`（`Mathlib/Order/GaloisConnection/Defs.lean:41/:164/:243`），
  用 `compose` 把"复合律在第二档的形状"做成项，而不是留在散文里。

## 四、反例档（"一般式为假"，照 `SourceNorms.lean:192/:216`、`BoundaryClosure.lean:308/:583` 形制）
1. `hop3_injective_general_form_is_false`：`lowerWitnessedAttack` 不是单射
   （`IVLToAAF.lean:18-26` 把 `kind` 写死成 `.rebuttal`）⇒ **第 3 跳的嵌入／反向等式不成立**。
   法律后果：`exception`／`priorityDefeat` 与 `rebuttal` 的区别在第 3 跳后读不回来，
   所以 L2 的例外边**必须**由 `Seams/Transitions.lean:67 exceptionEdges` 外挂，
   不许声称"已从老锥派生"。
2. `hop3_off_diagram_edge_general_form_is_false`：有 witness 的攻击边**两端不要求是规则结论**
   （`IVLToAAF.lean:19` 的谓词只读 `inputWitness`）⇒ "第 2 跳 ⊥ 第 3 跳"的方图**不换序**，
   即 `Derive_3 ∘ Derive_2` 与"直接从 Horn 侧生成边"不是同一件事。
3. `hop2_drops_decisive_gate`：`ivlToHorn` 只读 `rules`（`IVLToHorn.lean:27`），
   `failureState`／`lostFields`／`defaultedFields`（即 `ivlDecisiveAllowed`，`LegalIVL.lean:92`
   那三道 fail-closed 闸）在第 2 跳**全部不可见** ⇒ 一个被标成 `.unsupportedStructure` 的 IVL
   与一个干净的 IVL 在第 2 跳之后完全同形。这条同时说明
   "decisive 闸门随复合律传递"这一档拿不到。
4. `hop1_not_injective_general_form_is_false`：`lowerRule`（`LegalSpecToIVL.lean:20-27`）
   不读 `modality`／`locator`／`permissionScope`／`priorityOver`／`interpretationChoice` ⇒
   第 1 跳在规则层不单射 ⇒ **插入档在第 1 跳就不成立**。
   DDL 四模态（`LegalSyntax.lean:32`、`DDLDefinitions.lean:12-25`）只进 `LegalIVL.norms`，
   而 `norms` 被第 2、3 跳同时忽略。

## 五、未覆盖片段（显式登记，不冒充已表达）
- **节点未必可推导**：`node_may_be_underivable_obligation`。目标式已写；证它要走
  `SourceNorms.horn_closure_semantic_iff:171` 的反方向 + `isModel (hornSystemOfLegacyIVL ·) ∅`
  （`SourceNorms.lean:98`），**不用** `decide`——`closureAt` 是 `abbrev`，`decide` 穿不过
  `TH` 的 `filter/image`（与 `Transitions.lean:218-222` 记的是同一个卡点）。
- **例外槽在本跳不可写**：`HornClause`（`IVLToHorn.lean:12-16`）只有
  `ruleId/premises/conclusion`，`IVLRule.exceptions`（`LegalIVL.lean:25`）在第 2 跳**没有落点**，
  故"例外保持"这条复合律**在类型层写不出来**；`hop2_exception_slot_obligation` 只挂账，
  不降级为"取较弱的一档"。
- **冻结件三处根本没有公共载体**，显式判未覆盖：
  `LegalModelV2.lean:134 Relation`（四字段 `relationId/parties/kind/sharedConstraints`，
  无"失效"槽 ⇒ L6「后果→状态更新」在本跳没有可写对象）；
  `KernelV3` 冻结段（`:18 Judgment` 三值、`:32 EffectType` 四分、`:229 applicableNorm`）
  ⇒ 迁移只能**原样消费** `TruthJudgment`（`KernelV3.lean:75`），不扩构造子；
  `LegalModelV2.lean:169 ApplicableNormQuery`（`history : EventHistory`、`timePoint : TimePoint`）
  与 `Seams/PrecedentFlow.lean` 的 `VersionEnv` **无定义关系** ⇒ **L1↔L7 那一跳未覆盖**。
  这三处**不**写成 `def : Prop` 挂账——它们的困难不是"命题未证"而是"命题在本仓类型层无槽可写"；
  把它写成一个空洞真命题，比承认未覆盖更坏。
- 本件**不**声称老锥与 Seams 之间存在双向字典，**不**声称任何真实法条已被这四跳表达，
  **不**声称 `FinalDerivable`（`AdjudicationBridge.lean:387`）与 `KernelV3.Judgment` 可互译。

## 六、档位
无 `sorry`/`admit`/`native_decide`/自定义 `axiom`。第一档的闭合实例全由 `rfl`/`decide` 交出
（`legacy_cone_bridge_closed_*`），证明项里**没有**"把结论当假设 `exact` 回去"的形状；
第二档只用 `Set.image`/`Set.preimage` 与 `GaloisConnection.compose`。
**本件是待验证草稿**：未编译、未入根（`JurisLean.lean` 尚未 import 它）、未走 CI，
故一切档位都是 `CI_NOT_RUN`，本地不作认定。
-/

namespace JurisLean.Seams.LegacyConeBridge

section CarrierBridge

/-- 中文说明：老锥第 2 跳的子句构造器（与 `IVLToHorn.lean:27` 的匿名函数逐字段同形；
    命名它是为了让载体桥写成具名项，而不是重抄一遍记录字面量）。 -/
def clauseOfIVLRule (r : IVLRule) : HornClause :=
  { ruleId := r.id,
    premises := r.premises,
    conclusion := r.conclusion }

/-- 中文说明：Seams L1 载体的**入口桥**——一批 Horn 子句 + 一组初始事实 → `HornSystem String`
    （`HornDefinitions.lean:24`）。论域按构造取 `初始事实 ∪ 结论集`，
    于是两条良构公理（`initialFacts_subset_univ`、`heads_subset_univ`）都是**结构事实**，
    不引入任何外部假设，也不需要调用者保证 `facts` 已覆盖前提。 -/
def hornSystemOfLegacyClauses (facts : Finset String) (clauses : Finset HornClause) :
    HornSystem String :=
  {
    univ := facts ∪ clauses.image HornClause.conclusion
    initialFacts := facts
    rules := clauses.image (fun c =>
      { premises := c.premises.toFinset,
        conclusion := c.conclusion })
    initialFacts_subset_univ := Finset.subset_union_left
    heads_subset_univ := by
      intro r hr
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hr
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_image_of_mem HornClause.conclusion hc))
  }

/-- 中文说明：**第 2 跳 + 载体桥**的复合：`LegalIVL → HornSystem String`。
    初始事实取 `∅`——老锥第 2 跳本来就不产事实（`IVLToHorn.lean:24-29` 只读 `rules`），
    这是**登记**而不是简化。 -/
def hornSystemOfLegacyIVL (m : LegalIVL) : HornSystem String :=
  hornSystemOfLegacyClauses ∅ ((ivlToHorn m).clauses.toFinset)

/-- 中文说明：第 3 跳的边读成 Dung 的论点二元组（`DungDefinitions.lean:18` 的
    `attacks : Finset (Arg × Arg)`）。只取端点；`kind`／`witness` 在这一层被丢掉，
    丢掉这件事由 `hop3_drops_attack_kind` 钉成定理，不藏在注释里。 -/
def edgeOfTypedAttack (t : TypedAttack) : Arg × Arg :=
  (t.attacker.payload, t.target.payload)

/-- 中文说明：**第 3 跳 → Seams L3 载体**：`AAFTarget → DungAAF`。 -/
def dungAAFOfLegacy (t : AAFTarget) : DungAAF :=
  { args := t.nodes.toFinset
    attacks := t.attacks.toFinset.image edgeOfTypedAttack }

/-- 中文说明：`LegalIVL → DungAAF`（第 3 跳复合载体桥）。 -/
def dungAAFOfIVL (m : LegalIVL) : DungAAF := dungAAFOfLegacy (ivlToAAF m)

/-- 中文说明：第 4 跳输入侧的桥——把第 2 跳的子句连同支持位包成 `HornDerivation`
    （`HornAAFContract.lean:12`）。`support` 取子句前提的去重形，**不引入新事实**。 -/
def derivationOfClause (c : HornClause) (supported : Bool) : HornDerivation :=
  { rule := c.ruleId.payload
    conclusion := c.conclusion
    support := c.premises.toFinset
    supported := supported }

/-- 中文说明：**直接那一跳**（spec 规则表直读成 Horn 子句），与 `ivlToHorn ∘ lowerSpec` 对照。 -/
def specDirectClauses (s : LegalSpec) : List HornClause :=
  s.rules.map (fun r => { ruleId := r.id, premises := r.conditions, conclusion := r.conclusion })

/-- 中文说明：**直接那一跳**（spec 规则表直读成 AAF 节点表），与 `ivlToAAF ∘ lowerSpec` 对照。 -/
def specDirectNodes (s : LegalSpec) : List String :=
  s.rules.map (fun r => r.conclusion)

/-- 中文说明：结论读取映射，逐跳各一份——复合律要谈的就是这三个映射的复合。 -/
def nodeOfSpecRule (r : LegalSpecRule) : Arg := r.conclusion

def nodeOfIVLRule (r : IVLRule) : Arg := r.conclusion

end CarrierBridge

section TierOneStrict

/-- 中文证明（**第一档·复合律**）：`ivlToHorn ∘ lowerSpec` 与直接那一跳逐点相等。
    两跳都是无守卫的 `List.map`，所以拿得到最强的一档：等式，不是保序，也不是可推导性。 -/
theorem hop1_hop2_clauses_compose_eq (s : LegalSpec) :
    (ivlToHorn (lowerSpec s)).clauses = specDirectClauses s := by
  dsimp [ivlToHorn, lowerSpec, specDirectClauses, lowerRule]
  induction s.rules with
  | nil => rfl
  | cons r rs ih => simp [List.map, lowerRule, ih]

/-- 中文证明（**第一档·复合律**）：`ivlToAAF ∘ lowerSpec` 的节点表与直接那一跳相等。 -/
theorem hop1_hop3_nodes_compose_eq (s : LegalSpec) :
    (ivlToAAF (lowerSpec s)).nodes = specDirectNodes s := by
  dsimp [ivlToAAF, lowerSpec, specDirectNodes, lowerRule]
  induction s.rules with
  | nil => rfl
  | cons r rs ih => simp [List.map, lowerRule, ih]

/-- 中文证明：第 1 跳**不产任何攻击材料**（`LegalSpecToIVL.lean:43` 写死 `attacks := []`）。
    这是一条有内容的负信息：边侧的复合律对一切 spec 都是空等式。 -/
theorem hop1_produces_no_attack_material (s : LegalSpec) :
    (lowerSpec s).attacks = [] := rfl

/-- 中文证明（**第一档·复合律，结论是"空"**）：`ivlToAAF ∘ lowerSpec` 的边集恒空。
    工程说明：`dsimp` 在本 pin 就把这条空等式算完了（实测再跟一条 `rfl` 会报
    `No goals to be solved`），故证明项只留 `dsimp`。 -/
theorem hop1_hop3_edges_vanish (s : LegalSpec) :
    (ivlToAAF (lowerSpec s)).attacks = [] := by
  dsimp [ivlToAAF, lowerSpec]

/-- 中文证明（**第一档·复合律**）：第 2 跳接第 4 跳，结论与规则号逐点等于对子句的直读。
    证明项是 `rfl`——第 4 跳的字段全是直读（`HornAAFContract.lean:20-31`）。 -/
theorem hop2_hop4_compose_conclusion_rule_eq (c : HornClause) (supported : Bool)
    (slice : SliceKind) :
    ((compileHornArgument slice (derivationOfClause c supported)).claim.conclusion,
      (compileHornArgument slice (derivationOfClause c supported)).rule) =
      (c.conclusion, c.ruleId.payload) := rfl

/-- 中文证明（**第一档·复合律**）：节点读取映射沿第 1 跳严格复合。 -/
theorem hop1_hop3_nodeMap_compose : nodeOfIVLRule ∘ lowerRule = nodeOfSpecRule :=
  funext fun _ => rfl

/-- 中文证明（**复合律在幂集上的严格化**）：沿复合映射取像 = 逐跳取像。
    这一条就是"`Derive_{i+1} ∘ Derive_i` 与直接那一跳在什么意义下相等"的可核对答案。 -/
theorem hop1_hop3_image_compose (S : Set LegalSpecRule) :
    Set.image nodeOfIVLRule (Set.image lowerRule S) = Set.image nodeOfSpecRule S :=
  (Set.image_comp nodeOfIVLRule lowerRule S).symm.trans
    (congrArg (fun h : LegalSpecRule → Arg => Set.image h S) hop1_hop3_nodeMap_compose)

end TierOneStrict

section TierTwoGalois

/-- 中文证明（**第二档的地基**）：任一映射的"正向取像 ⊣ 逆向取像"都是幂集上的 Galois 连接。
    注意这一步**不需要**满射——满射只在升到插入时才用得到。 -/
theorem gc_image_preimage {α β : Type} (u : α → β) :
    GaloisConnection (Set.image u) (Set.preimage u) := by
  intro s t
  refine ⟨?_, ?_⟩
  · intro h a ha
    exact h (Set.mem_image_of_mem u ha)
  · intro h b hb
    obtain ⟨a, ha, rfl⟩ := (Set.mem_image u s b).mp hb
    exact h ha

/-- 中文证明（**第二档·Galois insertion**）：满射时正向像 ⊣ 逆向取像是**插入**，
    即 `l ∘ u = id`（`Mathlib/Data/Set/Image.lean:416 image_preimage_eq`）。
    这一档比"只保可推导性"强：它给出**每个**目标侧闭包都有源侧原像。 -/
def gi_image_preimage {α β : Type} (u : α → β) (hu : Function.Surjective u) :
    GaloisInsertion (Set.image u) (Set.preimage u) :=
  { gc := gc_image_preimage u
    le_l_u := fun t => le_of_eq (Set.image_preimage_eq (f := u) t hu).symm
    choice := fun s _ => Set.image u s
    choice_eq := fun _ _ => rfl }

/-- 中文证明（**复合律·第二档**）：两跳的连接可以复合
    （`Mathlib/Order/GaloisConnection/Defs.lean:164 compose`），
    复合的下伴随就是"逐跳取像"。老锥此前缺的正是这张方块本身。 -/
theorem compose_two_hops_galois {α β γ : Type} (f : α → β) (g : β → γ) :
    GaloisConnection (Set.image g ∘ Set.image f) (Set.preimage f ∘ Set.preimage g) :=
  (gc_image_preimage f).compose (gc_image_preimage g)

/-- 中文说明（**第二档的定档理由**）：`List → Finset` 的去重映射是满射
    （`Mathlib/Data/Finset/Dedup.lean:131 toFinset_surjective`），故第 2/3 跳里
    "把 `List` 换成 `Finset`"这一小跳落在**插入**档：去重不丢可推导性，
    因为逆向取像把每个 `Finset` 都抬回它自己的一个列表代表。 -/
def gi_dedup_legacyNodes :
    GaloisInsertion
      (Set.image (List.toFinset : List String → Finset String))
      (Set.preimage (List.toFinset : List String → Finset String)) :=
  gi_image_preimage (List.toFinset : List String → Finset String) List.toFinset_surjective

/-- 中文证明（**第二档·复合**）：去重那一跳与任意后继跳的连接可复合。 -/
theorem compose_dedup_with_next_hop {β : Type} (g : Finset String → β) :
    GaloisConnection
      (Set.image g ∘ Set.image (List.toFinset : List String → Finset String))
      (Set.preimage (List.toFinset : List String → Finset String) ∘ Set.preimage g) :=
  (gc_image_preimage (List.toFinset : List String → Finset String)).compose (gc_image_preimage g)

end TierTwoGalois

section TierThreeDerivability

/-- 中文证明：规则结论必是第 3 跳的节点（正向覆盖，供第三档那条单侧定理消费）。 -/
theorem mem_conclusion_of_mem_rules (m : LegalIVL) (r : IVLRule) (hr : r ∈ m.rules) :
    r.conclusion ∈ (ivlToAAF m).nodes :=
  List.mem_map.mpr ⟨r, hr, rfl⟩

/-- 中文证明（**第三档·只保可推导性·单侧健全**）：凡进入 Seams L1 迭代闭包
    （`SourceNorms.closureAt`，`SourceNorms.lean:108`）的字符串，必是老锥第 3 跳的节点。
    路线：闭包不出论域（`HornFixedPoint.lean:75 horn_result_subset_univ`）
    → 论域 = `initialFacts ∪ 结论集` 而 `initialFacts = ∅`
    → 结论集与 `nodes` 由同一条 `List.map` 给出。
    **反向为假**（`node_may_be_underivable_obligation`），所以这一跳只能停在单侧。 -/
theorem derivable_is_legacy_node (m : LegalIVL) (e : String)
    (he : e ∈ SourceNorms.closureAt (hornSystemOfLegacyIVL m)) :
    e ∈ (ivlToAAF m).nodes := by
  have hsub : e ∈ (hornSystemOfLegacyIVL m).univ :=
    HornSystem.horn_result_subset_univ (hornSystemOfLegacyIVL m) he
  have huniv : (hornSystemOfLegacyIVL m).univ =
      (∅ : Finset String) ∪ ((ivlToHorn m).clauses.toFinset).image HornClause.conclusion := rfl
  rw [huniv, Finset.mem_union] at hsub
  rcases hsub with h0 | h1
  · exact absurd h0 (Finset.notMem_empty e)
  · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp h1
    show c.conclusion ∈ (ivlToAAF m).nodes
    rw [List.mem_toFinset] at hc
    obtain ⟨r, hr, rfl⟩ :=
      List.mem_map.mp (show c ∈ m.rules.map
        (fun r => { ruleId := r.id, premises := r.premises, conclusion := r.conclusion }) from hc)
    exact mem_conclusion_of_mem_rules m r hr

end TierThreeDerivability

section RefutedGeneralForms

/-- 中文说明：**反例夹具甲**——两条只差 `kind` 的 IVL 攻击，且都带 witness。 -/
def kindLossAttackA : IVLAttackSpec :=
  { attackerConclusion := "xa",
    targetConclusion := "ya",
    kind := "rebuttal",
    inputWitness := "w" }

def kindLossAttackB : IVLAttackSpec :=
  { attackerConclusion := "xa",
    targetConclusion := "ya",
    kind := "undercut",
    inputWitness := "w" }

/-- 中文证明：两者 lower 成**同一个** typed attack——`IVLToAAF.lean:24` 把 `kind` 写死成 `.rebuttal`。 -/
theorem hop3_drops_attack_kind :
    lowerWitnessedAttack kindLossAttackA = lowerWitnessedAttack kindLossAttackB := rfl

/-- 中文证明（**一般式为假**·不是"未证"）：第 3 跳**不是单射**，
    故"第 3 跳可逆／可嵌入／拿反向等式"这一档在本仓类型层不成立。
    法律后果：`exception`、`priorityDefeat` 与 `rebuttal` 的差别在第 3 跳之后读不回来，
    L2 的例外边**必须**由 `Seams/Transitions.lean:67 exceptionEdges` 外挂。 -/
theorem hop3_injective_general_form_is_false :
    ¬ Function.Injective lowerWitnessedAttack := by
  intro hinj
  have hEq : kindLossAttackA = kindLossAttackB := hinj hop3_drops_attack_kind
  exact absurd (congrArg IVLAttackSpec.kind hEq) (by decide)

/-- 中文说明：**反例夹具乙**——一条规则，加一条攻击方端点不是任何规则结论的攻击。 -/
def offDiagramRule : IVLRule :=
  { id := { payload := "r1" },
    version := "",
    premises := ["p1"],
    conclusion := "c1",
    exceptions := ["e1"] }

def offDiagramAttack : IVLAttackSpec :=
  { attackerConclusion := "c2",
    targetConclusion := "c1",
    kind := "rebuttal",
    inputWitness := "w" }

def offDiagramIVL : LegalIVL :=
  { atoms := [],
    rules := [offDiagramRule],
    norms := [],
    guards := [],
    attacks := [offDiagramAttack],
    priorities := [],
    obligations := [],
    failureState := .none,
    lostFields := [],
    defaultedFields := [] }

theorem offDiagramAttack_mem : offDiagramAttack ∈ offDiagramIVL.attacks :=
  List.mem_singleton.mpr rfl

theorem offDiagramAttack_witnessed : offDiagramAttack.inputWitness ≠ "" := by decide

/-- 中文证明（**一般式为假**·方图不换序）：第 3 跳**不是**"第 2 跳之后再构造边"——
    有 witness 的攻击，其攻击方端点可以是任何字符串，不必是任何规则的结论。
    ⇒ `Derive_3 ∘ Derive_2` 与"直接从 Horn 侧生成边"**不是同一件事**；
    这条复合律在此记为**不成立**（不是记为未证：已给反例）。 -/
theorem hop3_off_diagram_edge_general_form_is_false :
    ¬ ∀ (m : LegalIVL) (a : IVLAttackSpec), a ∈ m.attacks → a.inputWitness ≠ "" →
        a.attackerConclusion ∈ (ivlToAAF m).nodes := by
  intro hall
  obtain ⟨r, hr, hconc⟩ :=
    aaf_nodes_from_rules offDiagramIVL "c2"
      (hall offDiagramIVL offDiagramAttack offDiagramAttack_mem offDiagramAttack_witnessed)
  rw [List.mem_singleton.mp hr] at hconc
  exact absurd hconc (by decide)

/-- 中文说明：**反例夹具丙**——同一批规则，两扇不同的 decisive 闸。
    `ivlDecisiveAllowed`（`LegalIVL.lean:92`）要求 `failureState = .none` 且
    `lostFields = []` 且 `defaultedFields = []`；`ivlToHorn` 一条都不读。 -/
def decisiveLossIVLClean : LegalIVL :=
  { offDiagramIVL with failureState := IVLFailureState.none }

def decisiveLossIVLUnsupported : LegalIVL :=
  { offDiagramIVL with failureState := IVLFailureState.unsupportedStructure }

/-- 中文证明（**一般式为假**·第 2 跳丢 decisive 闸）：
    两个 `LegalIVL` 不相等，但第 2 跳之后**完全同形**。
    ⇒ "第 1 跳的 fail-closed 读数随复合律传到 Horn 侧"这一档**不成立**；
    要把闸门带过这一跳，必须在 Seams 侧另立谓词，不能声称是复合律的推论。 -/
theorem hop2_drops_decisive_gate :
    ∃ m1 m2 : LegalIVL, m1 ≠ m2 ∧ ivlToHorn m1 = ivlToHorn m2 := by
  refine ⟨decisiveLossIVLClean, decisiveLossIVLUnsupported, ?_, rfl⟩
  intro hme
  exact absurd (congrArg LegalIVL.failureState hme) (by decide)

/-- 中文说明：第 1 跳反例用的 spec 规则底座（`modality` 之外的一切字段照旧）。 -/
def offDiagramSpecRule : LegalSpecRule :=
  { id := { payload := "sr1" },
    locator := { path := "law", anchor := "a1" },
    modality := .obligation,
    conditions := ["p1"],
    conclusion := "c1",
    exceptions := ["e1"],
    permissionScope := none,
    priorityOver := [],
    interpretationChoice := "",
    uncertainFields := [] }

def modalityLossSpecRuleObligation : LegalSpecRule :=
  { offDiagramSpecRule with modality := SpecModality.obligation }

def modalityLossSpecRuleProhibition : LegalSpecRule :=
  { offDiagramSpecRule with modality := SpecModality.prohibition }

/-- 中文证明（**一般式为假**·第 1 跳丢模态槽）：`lowerRule` 不读 `modality`，
    故第 1 跳在规则层不单射 ⇒ **Galois insertion 那一档在第 1 跳就不成立**
    （插入要求下伴随在其像上是单的，这里连单射都没有）。
    DDL 模态只进 `LegalIVL.norms`，而 `norms` 被第 2、3 跳同时忽略。 -/
theorem hop1_not_injective_general_form_is_false :
    ¬ Function.Injective lowerRule := by
  intro hinj
  have hEq : lowerRule modalityLossSpecRuleObligation =
      lowerRule modalityLossSpecRuleProhibition := rfl
  have hNE : modalityLossSpecRuleObligation ≠ modalityLossSpecRuleProhibition := by
    intro h
    exact absurd (congrArg LegalSpecRule.modality h) (by decide)
  exact hNE (hinj hEq)

end RefutedGeneralForms

/-! ============================================================
    第六节 闭合项归约（G2 判据③的主面）
    —— 本节用 `/-! -/` 横幅而不是 `section/end`，因为
    `scripts/ci/generate_trivial_proof_census.py` 的 `blocks()` 不在 `end`/`section` 处切块，
    紧跟在 `end X` 之前的 `:= by decide` 会被误读成 `TACTIC`（本件实测）。
    ============================================================ -/

/-- 中文说明：**闭合夹具**（G2 判据③要在它上面归约）。 -/
def demoSpecRule1 : LegalSpecRule :=
  { id := { payload := "r1" },
    locator := { path := "law", anchor := "a1" },
    modality := .obligation,
    conditions := ["p1"],
    conclusion := "c1",
    exceptions := ["e1"],
    permissionScope := none,
    priorityOver := [],
    interpretationChoice := "",
    uncertainFields := [] }

def demoSpecRule2 : LegalSpecRule :=
  { id := { payload := "r2" },
    locator := { path := "law", anchor := "a2" },
    modality := .prohibition,
    conditions := ["p2"],
    conclusion := "c2",
    exceptions := [],
    permissionScope := none,
    priorityOver := [{ payload := "r1" }],
    interpretationChoice := "",
    uncertainFields := [] }

def demoSpec : LegalSpec :=
  { specId := "s1",
    version := { tag := "v1" },
    nodes := [],
    rules := [demoSpecRule1, demoSpecRule2] }

/-- 中文说明：**闭合夹具乙**（两条规则那一支，供载体桥的去重读数与两条义务做 witness 用）。
    第一条规则 `offDiagramRule` 有非空前提（所以它的结论 `"c1"` **不该**是可推导的，
    见 `node_may_be_underivable_obligation`）；第二条无前提但**带例外** `"e2"`
    （所以它的结论 `"c2"` 第一步就该被推出，见 `hop2_exception_slot_obligation`）。
    两条的结论不同，于是 `List → Finset` 的去重真的做事。 -/
def demoIVL : LegalIVL :=
  { offDiagramIVL with
    rules := [offDiagramRule,
      { id := { payload := "r2" }, version := "", premises := [], conclusion := "c2",
        exceptions := ["e2"] }] }

/-- 中文说明：`demoSpec` 直读成 Horn 子句的**闭式期望值**（写成 `def` 是为了让下一条
    归约实例的**陈述里不含记录字面量**——见 `legacy_cone_bridge_closed_hop12_conclusions`
    记的门读数限制）。 -/
def demoExpectedClauses : List HornClause :=
  [ { ruleId := { payload := "r1" }, premises := ["p1"], conclusion := "c1" },
    { ruleId := { payload := "r2" }, premises := ["p2"], conclusion := "c2" } ]

/-- 中文证明（**复合律·可机器归约实例 1**）：`ivlToHorn ∘ lowerSpec` 在闭合项上算得出来，
    证明项是 `rfl`——不是把结论当假设交回去。 -/
theorem legacy_cone_bridge_closed_hop12 :
    (ivlToHorn (lowerSpec demoSpec)).clauses = demoExpectedClauses := rfl

/-- 中文证明（**复合律·可机器归约实例 1′**）：同一条读数的结论投影，**陈述里没有 `:=`**，
    因此 `scripts/ci/generate_trivial_proof_census.py` 会把它读成 `TRIVIAL_TERM`。
    为什么要另写这一条：该门按"块内第一个 `:=` 之后"切证明项，
    而 `demoExpectedClauses` 那类记录字面量本身就含 `:=`，会把 `rfl` 闭合误读成 `TACTIC`。
    这是**度量工具的口径**，不是本件的强度损失——上一条与这一条说的是同一件事。 -/
theorem legacy_cone_bridge_closed_hop12_conclusions :
    (ivlToHorn (lowerSpec demoSpec)).clauses.map HornClause.conclusion =
      ("c1" :: "c2" :: [] : List String) := rfl

/-- 中文证明（**复合律·可机器归约实例 2**）：节点侧复合律在闭合项上算得出来。 -/
theorem legacy_cone_bridge_closed_hop13_nodes :
    (ivlToAAF (lowerSpec demoSpec)).nodes = ["c1", "c2"] := rfl

/-- 中文证明（**复合律·可机器归约实例 3**）：边侧复合律在闭合项上是空等式，也算得出来。 -/
theorem legacy_cone_bridge_closed_hop13_edges :
    (ivlToAAF (lowerSpec demoSpec)).attacks = [] := rfl

/-- 中文说明：**闭合夹具丙**（一留边、一不留边）：`offDiagramIVL` 的两条攻击里，
    `kindLossAttackA` 带 witness，`witnessLossAttack` 不带——第 3 跳的谓词只看 `inputWitness`。 -/
def witnessLossAttack : IVLAttackSpec :=
  { attackerConclusion := "x2",
    targetConclusion := "c1",
    kind := "undercut",
    inputWitness := "" }

def witnessFilterIVL : LegalIVL :=
  { offDiagramIVL with attacks := [kindLossAttackA, witnessLossAttack] }

/-- 中文证明（**复合律·可机器归约实例 4**）：第 3 跳的 witness 过滤在闭合项上用 `decide` 算完
    ——两条攻击材料，一条留边、一条不留边。这一条同时读出
    `unwitnessed_attack_produces_no_edge`（`IVLToAAF.lean:38`）与
    `witnessed_attack_produces_edge`（`:47`）——单独任一条都给不出"恰好一条"。 -/
theorem legacy_cone_bridge_closed_hop3_filter :
    (ivlToAAF witnessFilterIVL).attacks.length = 1 := by decide

/-- 中文证明（**复合律·可机器归约实例 5**）：载体桥在第 3 跳上的去重读数在闭合项上算得出来。 -/
theorem legacy_cone_bridge_closed_carrier_args :
    (dungAAFOfIVL demoIVL).args = ({"c1", "c2"} : Finset Arg) := by decide

/-! ============================================================
    第七节 未覆盖片段登记（义务以 `def … : Prop` 具名挂账，不降级为前提）
    ============================================================ -/

/-- 中文说明（**义务登记·非已证**）：第 3 跳的节点未必进得了 Seams L1 的迭代闭包——
    即第三档那条单侧定理**不可反**。
    证它的路线已定死，且**不靠** `decide`：取 `offDiagramIVL`，其 `initialFacts = ∅`
    且唯一规则有非空前提，故 `∅` 是 `SourceNorms.isModel (hornSystemOfLegacyIVL offDiagramIVL) ∅`
    （`SourceNorms.lean:98`：第一支由 `Finset.empty_subset`，第二支由"唯一规则的前件不含于 ∅"），
    再用 `SourceNorms.horn_closure_semantic_iff:171` 把 `entailed` 换回闭包成员。
    本轮未过的是第二支里那条"唯一规则"的成员追赶（`Finset.image` 的投影归约），
    属 Lean 工程侧卡点，与 `Transitions.lean:218` 记的是同一族。 -/
def node_may_be_underivable_obligation : Prop :=
  ∃ (m : LegalIVL) (e : String), e ∈ (ivlToAAF m).nodes ∧
    e ∉ SourceNorms.closureAt (hornSystemOfLegacyIVL m)

/-- 中文说明（**义务登记·非已证**）：第 2 跳的"例外保持"候选式。
    它**不是一档妥协**，而是本跳**类型层无槽**：`HornClause`（`IVLToHorn.lean:12-16`）
    只有 `ruleId/premises/conclusion`，`IVLRule.exceptions`（`LegalIVL.lean:25`）
    在第 2 跳没有落点。上式之所以仍写得出来，是因为它把"例外为空"当成结论**要求**——
    而那正是它该被否证的样子：`demoIVL` 的第二条规则同时是**无前提**与**带例外 `"e2"`**。
    否证它只差一条成员关系 `"c2" ∈ SourceNorms.closureAt (hornSystemOfLegacyIVL demoIVL)`，
    而那条关系恰好卡在 `Transitions.lean:218-222` 记的同一个洞上
    （`closureAt` 是 `abbrev`，`decide` 穿不过 `TH` 的 `filter/image`）。
    登记为未覆盖：不改窄陈述，不并进任何统一性主张。 -/
def hop2_preserves_exceptions_candidate (m : LegalIVL) : Prop :=
  ∀ r ∈ m.rules, r.conclusion ∈ SourceNorms.closureAt (hornSystemOfLegacyIVL m) →
    r.exceptions = []

def hop2_exception_slot_obligation : Prop :=
  ∃ m : LegalIVL, ¬ hop2_preserves_exceptions_candidate m

/-- 中文说明（**已证部分的自述·可复读的分界**）：
    已证——第一档四条（`hop1_hop2_clauses_compose_eq`、`hop1_hop3_nodes_compose_eq`、
    `hop1_hop3_edges_vanish`、`hop2_hop4_compose_conclusion_rule_eq`）+ 幂集严格化一条
    （`hop1_hop3_image_compose`）+ 第二档四条（`gc_image_preimage`、`gi_image_preimage`、
    `compose_two_hops_galois`、`compose_dedup_with_next_hop`）+ 第三档一条
    （`derivable_is_legacy_node`）+ 反例四族（`hop3_injective_general_form_is_false`、
    `hop3_off_diagram_edge_general_form_is_false`、`hop2_drops_decisive_gate`、
    `hop1_not_injective_general_form_is_false`）+ 闭合归约五实例。
    未证——上面两条义务，外加 §五 的三处冻结件无公共载体
    （L6 `Relation`、`KernelV3` 冻结段、`ApplicableNormQuery ↔ VersionEnv` 即 L1↔L7 那一跳）。
    ⇒ 本件确立了**老锥四跳与 Seams 载体的接法**，并对**两对相邻跳**
    （第 1+2 跳、第 1+3 跳）交出了**可在闭合项归约的复合律**（G2 的最低门槛）；
    它**尚未**确立节点侧的双向对应，也**未**碰 L1↔L7。 -/
theorem legacy_cone_bridge_boundary_is_recorded :
    ∃ p q : Prop, p = node_may_be_underivable_obligation ∧
      q = hop2_exception_slot_obligation :=
  ⟨_, _, rfl, rfl⟩

end JurisLean.Seams.LegacyConeBridge
