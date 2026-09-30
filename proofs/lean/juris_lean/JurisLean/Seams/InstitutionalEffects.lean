import JurisLean.LegalModelV2

/-!
中文说明：S5 缝合件——制度效果（L5→L6）的两条通道：账本投影 π 与非裁判性履行通道。

# 一、法律语义（人话）

法律关系可以因裁判而**产生**，也可以因裁判或其他法律事实而**终止**；债务可以因**履行**而消灭，
但履行不是裁判，它不创设新的法律关系。仓内冻结内核把这件事说得很窄：对象定义 v3 第四条只让
"形成性裁判"转移实体状态，其余事件原样返回；参考实现
`theory/spec/canonical_v2/kernel.py:238` 字面上就是
`return NormState(state.relations + event.formed_relations)`——纯追加，从不删除任何东西。
冻结结构 `JurisLean.Relation`（LegalModelV2.lean:134）只有
`relationId / parties / kind / sharedConstraints` 四个字段，没有任何失效、期限或终止字段；
`JurisLean.RelationalState`（KernelV3.lean:95）的 `relations` 是"当前关系集合"，而冻结的
`transfer`（KernelV3.lean:125 区段）只整体替换 `R_t`，没有"抽取"通道。
于是"**某关系已经不复存在**"在冻结内核里写不出来：追加式投影只记得"曾经成立"。

本件把这条缺失的通道**另外建模**，不改冻结内核、不改冻结条款：

1. **账本 `Ledger`**：成立与终止都以"记录"的形式写进同一条账目序列。终止记录是账本里的
   **数据**，不是对既有记录的原地删除——历史不被涂改。
2. **投影 π（`forms` / `effective`）**：某关系当前是否有效，取决于账本里**最后**一条提及它的
   记录是"成立"还是"终止"。追加式语义因此获得表达消灭的能力。
3. **纯追加投影（`formsEver`）**：某关系是否**曾经**成立——这是冻结内核 `R + formed` 的 Lean 读数。
   它永远不遗忘（`append_is_ideographic`），所以它无法表达消灭；对照定理
   `ledger_can_express_termination` 与 `termination_breaks_projection` 把这一差距做成可检查的事实。
4. **履行通道（Part ②）**：`PerformanceStep` 记录"债务额、已为给付、经抵扣实付、给付后余额"，
   余额用自然数截断减法，因此不可能出现负债务（`overperformance_leaves_zero`）。
   给付事件在关系账本上是**空操作**（`performance_not_creation`、
   `effective_next_nonformative_iff`），但历史成立记录仍被保留（`register_p_side`）——
   **消灭**与**从未成立**是两件不同的事。

# 二、数学对象

- `RecordKind`（formed/terminated）与 `FormationRecord Rel`＝⟨事件引证、类别、所指向关系⟩。
- `Ledger Rel := List (FormationRecord Rel)`；`next : Ledger Rel → SeamEvent Rel → Ledger Rel` 只做追加。
- `formsB / forms`＝π（末次提及决定，折叠机器 `formsFold`）；`formsEverB / formsEver`＝冻结内核的
  纯追加投影（"是否存在成立记录"，折叠机器 `formsEverFold`）；`effective` 是 π 的命题别名。
- `SeamEvent Rel`：四构造子 `formative / terminating / performance / declaratory`，
  `effectKind` 映到 `EffectKind`；构造子互不重合，故"给付不携带成立记录"是类型层事实。
- `Debt`（义务人 + 债务额）、`PerformanceStep`（债务 + 已为给付 + 实付 + 未偿余额）、
  `appliedAmount := min`、`outstandingAfter :=` 截断减法。守恒式 `min a p + (a ∸ p) = a`
  对自然数**无条件**成立（`omega` 直接闭合），不需附加前提。
- `RankedRel`（关系标识 + 位阶数值）、`rankLt`、`routeTwo`、`foldMax`：有限位阶表上的择高路由
  与极大元存在（P-015 的 S5 使用点）。

# 三、本件证什么、不证什么

**证**：π 与单步转移一致（`projection_of_append_matches_step`：
`forms (next L e) r ↔ r = rel ∨ forms L r`，即 π(追加) ≡ 逐步语义；终止片段见
`projection_of_append_matches_step_terminating`，非裁判片段见 `effective_next_nonformative_iff`）；
追加即成立／追加他者不改本题／追加终止即失效（`projection_append_form`、
`projection_append_unrelated`、`projection_append_terminated`）；追加不遗忘
（`append_is_ideographic`）；账本能表达终止而纯追加投影不能（`ledger_can_express_termination`）；
给付 3 抵扣债务 10 实付 3 余 7 的完整见证（`performance_witness_10_3`）与守恒
（`applied_plus_outstanding_eq_amount`、`performStep_conservation`）；超额给付不产生负债务
（`overperformance_leaves_zero`）；给付≠创设（`performance_not_creation`、
`performance_appends_no_record`）；履行后历史成立记录仍在（`register_p_side`）；有限非空位阶表
极大元存在（`exists_maximal_in_ranked`）与二元择高路由保留被投影存续者
（`priority_route_keeps_projected`、`routeTwo_dominates`）。

**不证**（声明片段与未覆盖面，逐条写明；缺失一律 fail-closed）：
1. 不修改、不重定义、也不推翻冻结的 `transfer` 与 `RelationalState`；本件只是**平行**通道。
   π 与冻结 `R_t` 之间的精化定理需要冻结内核先获得失效语义，故属未面。
2. 不含时效、除斥期间、期限届至的时间算术：`terminating` 在这里是抽象终止记录，
   不是任何具体消灭事由的构成要件检验。
3. 不认定任何真实案件的法律关系是否存续、任何真实债务是否清偿；引证号与金额只是结构见证。
4. 不证 P-015 一般位阶定理（有限无环优先关系的整体冲突消解方案属缝合件 S1）。本件末尾只有
   **位阶使用点**：以显式位次表 `List RankedRel` 为数据的二元择高与极大元存在，
   片段相对、可判定，不宣称覆盖 P-015。
5. 不给 `Ledger` 加"同一关系重复成立""终止未成立之关系"之类的良构性前提；关系同一性按
   `DecidableEq Rel` 整体判定，未使用 `relationId` 投影；π 对记录顺序的全部不变性未证明。
6. 不证给付与债权账目的多笔串并（一债多付、多债一付的分配守恒）：P-097
   （`JurisLean/Genealogy/Part5.lean` namespace P097）已证的 `allocateOne` 里 `remainder`
   是**溢缴余额**，不是未偿债务，"债 10 已为 3 余 7"在该处并不可得，故本件自建
   `outstandingAfter` 并把守恒做在本件里。

命名说明：契约把"pure append never forgets"写在 `forms` 上，该句对**末次提及**投影 π 为假
（终止记录就是反例，本件以 `termination_breaks_projection` 做出见证），故本件把该正定理挂在
纯追加投影 `formsEver` 上并保留名字 `append_is_ideographic`；π 侧对应的不变性只在"追加段
完全不提及该关系"的片段成立（`forms_congruent_under_nonmentioning_suffix`）。

合规说明：零 `sorry`、零占位、零新设公理，全部定理在本件内闭合；判定式证明只用于闭式数据
见证，未用任何把闭式判定冒充一般定理的写法。档位：定义 [构造性定义]，定理 [本件内完整证明]，
编译认定待 CI，本地不称 PASS。落点：可行使段的强制实现与救济后果（见
`JurisLean/Seams/ClaimBasis.lean` 第四节）。
-/

namespace JurisLean.Seams.InstitutionalEffects

/-! ## Part ① 账本、投影 π 与纯追加投影 -/

/-- 中文说明：账目记录的两种法律语义类别。终止是一**条记录**，不是删除动作。 -/
inductive RecordKind
  | formed      -- 成立记录：该关系于此刻进入世界
  | terminated  -- 终止记录：该关系于此刻不再有效
  deriving DecidableEq, Repr

/-- 中文说明：单条账目记录＝事件引证 + 类别 + 所指向关系。实例用冻结类型 `JurisLean.Relation`
（LegalModelV2.lean:134）；该结构没有失效字段，正是本件必须另建通道的原因。 -/
structure FormationRecord (Rel : Type) where
  eventId : String
  kind : RecordKind
  rel : Rel
  deriving DecidableEq, Repr

/-- 中文说明：账本类型。序列即历史，没有任何原地修改。 -/
abbrev Ledger (Rel : Type) := List (FormationRecord Rel)

/-- 中文说明：成立记录的构造子。 -/
def formedRecord {Rel : Type} (eventId : String) (rel : Rel) : FormationRecord Rel :=
  { eventId := eventId, kind := RecordKind.formed, rel := rel }

/-- 中文说明：终止记录的构造子（账本里的数据，不是对账本的删除操作）。 -/
def terminatedRecord {Rel : Type} (eventId : String) (rel : Rel) : FormationRecord Rel :=
  { eventId := eventId, kind := RecordKind.terminated, rel := rel }

/-- 中文说明：该记录是否为成立记录。 -/
def recordIsFormation {Rel : Type} (e : FormationRecord Rel) : Bool :=
  match e.kind with
  | RecordKind.formed => true
  | RecordKind.terminated => false

/-- 中文说明：记录是否指向关系 `r`（按关系同一性判定，不比较非同一性属性）。 -/
abbrev recordMentions {Rel : Type} (r : Rel) (e : FormationRecord Rel) : Prop :=
  r = e.rel

/-- 中文说明：提及判定的可计算形式。 -/
def recordMentionsB {Rel : Type} [DecidableEq Rel]
    (r : Rel) (e : FormationRecord Rel) : Bool := decide (r = e.rel)

/-- 中文说明：提及为真则可计算形式取真。 -/
theorem recordMentionsB_true {Rel : Type} [DecidableEq Rel]
    (r : Rel) (e : FormationRecord Rel) (h : recordMentions r e) :
    recordMentionsB r e = true := decide_eq_true h

/-- 中文说明：未提及则可计算形式取假。 -/
theorem recordMentionsB_false {Rel : Type} [DecidableEq Rel]
    (r : Rel) (e : FormationRecord Rel) (h : ¬ recordMentions r e) :
    recordMentionsB r e = false := decide_eq_false h

/-- 中文说明：单条记录对累加器的作用——提及即覆盖，未提及即保持。这是"末次提及决定"的机器。 -/
def formsStep {Rel : Type} [DecidableEq Rel]
    (r : Rel) (e : FormationRecord Rel) (acc : Bool) : Bool :=
  if recordMentions r e then recordIsFormation e else acc

/-- 中文说明：沿账本从左到右折叠；结果由最后一条提及 `r` 的记录决定。 -/
def formsFold {Rel : Type} [DecidableEq Rel]
    (r : Rel) (acc : Bool) : Ledger Rel → Bool
  | [] => acc
  | e :: rest => formsFold r (formsStep r e acc) rest

/-- 中文说明：投影 π 的布尔形式：账本 `L` 下关系 `r` 当前是否有效。 -/
def formsB {Rel : Type} [DecidableEq Rel] (L : Ledger Rel) (r : Rel) : Bool :=
  formsFold r false L

/-- 中文说明：投影 π 的命题形式。 -/
abbrev forms {Rel : Type} [DecidableEq Rel] (L : Ledger Rel) (r : Rel) : Prop :=
  formsB L r = true

/-- 中文说明：空账本上折叠不动累加器。 -/
theorem formsFold_nil {Rel : Type} [DecidableEq Rel]
    (r : Rel) (acc : Bool) : formsFold r acc [] = acc := rfl

/-- 中文说明：单步折叠展开式。 -/
theorem formsFold_cons {Rel : Type} [DecidableEq Rel]
    (r : Rel) (acc : Bool) (e : FormationRecord Rel) (rest : Ledger Rel) :
    formsFold r acc (e :: rest) = formsFold r (formsStep r e acc) rest := rfl

/-- 中文说明：折叠与拼接相容——先折前段再折后段＝折整段。这是"追加"与"逐步"一致的代数内核。 -/
theorem formsFold_append {Rel : Type} [DecidableEq Rel]
    (r : Rel) (acc : Bool) (L s : Ledger Rel) :
    formsFold r acc (L ++ s) = formsFold r (formsFold r acc L) s := by
  induction L generalizing acc with
  | nil => rfl
  | cons a l ih =>
      rw [List.cons_append, formsFold_cons, ih (formsStep r a acc), formsFold_cons]

/-- 中文说明：追加一条记录的展开式。 -/
theorem formsB_append_record {Rel : Type} [DecidableEq Rel]
    (L : Ledger Rel) (r : Rel) (e : FormationRecord Rel) :
    formsB (L ++ [e]) r = formsStep r e (formsB L r) := by
  unfold formsB
  rw [formsFold_append, formsFold_cons, formsFold_nil]

/-- 中文说明：空账本的投影恒为假。 -/
theorem formsB_nil {Rel : Type} [DecidableEq Rel]
    (r : Rel) : formsB ([] : Ledger Rel) r = false := rfl

/-- 中文说明：成立记录对 π 的展开式：被形成者必有效，他者看原账本。 -/
theorem formsB_append_formed {Rel : Type} [DecidableEq Rel]
    (L : Ledger Rel) (eventId : String) (rel r : Rel) :
    formsB (L ++ [formedRecord eventId rel]) r = if r = rel then true else formsB L r := by
  rw [formsB_append_record]
  simp [formsStep, formedRecord, recordIsFormation]

/-- 中文说明：终止记录对 π 的展开式。 -/
theorem formsB_append_terminated {Rel : Type} [DecidableEq Rel]
    (L : Ledger Rel) (eventId : String) (rel r : Rel) :
    formsB (L ++ [terminatedRecord eventId rel]) r = if r = rel then false else formsB L r := by
  rw [formsB_append_record]
  simp [formsStep, terminatedRecord, recordIsFormation]

/-- 中文说明：**追加即成立**：在任意账本后追加 `r` 的成立记录，`r` 在投影下有效。 -/
theorem projection_append_form {Rel : Type} [DecidableEq Rel]
    (L : Ledger Rel) (eventId : String) (r : Rel) :
    formsB (L ++ [formedRecord eventId r]) r = true := by
  rw [formsB_append_formed]
  exact if_pos rfl

/-- 中文说明：**追加他者不改本题**：追加 `r' ≠ r` 的成立记录，`r` 的投影值不动。 -/
theorem projection_append_unrelated {Rel : Type} [DecidableEq Rel]
    (L : Ledger Rel) (eventId : String) {r r' : Rel} (h : r ≠ r') :
    formsB (L ++ [formedRecord eventId r']) r = formsB L r := by
  rw [formsB_append_formed, if_neg h]

/-- 中文说明：**追加终止记录即失效**：末次提及语义让 `r` 在投影中退场。 -/
theorem projection_append_terminated {Rel : Type} [DecidableEq Rel]
    (L : Ledger Rel) (eventId : String) (r : Rel) :
    formsB (L ++ [terminatedRecord eventId r]) r = false := by
  rw [formsB_append_terminated]
  exact if_pos rfl

/-- 中文说明：π 与拼接的展开式。 -/
theorem formsB_append {Rel : Type} [DecidableEq Rel]
    (L s : Ledger Rel) (r : Rel) :
    formsB (L ++ s) r = formsFold r (formsB L r) s := by
  unfold formsB
  rw [formsFold_append]

/-- 中文说明：不提及该关系的记录段在 π 上是"透明"的。 -/
theorem formsFold_nonmentioning {Rel : Type} [DecidableEq Rel]
    (r : Rel) : ∀ (s : Ledger Rel), (∀ e, e ∈ s → ¬ recordMentions r e) →
      ∀ acc : Bool, formsFold r acc s = acc := by
  intro s
  induction s with
  | nil => intro _ acc; rfl
  | cons e rest ih =>
      intro h acc
      rw [formsFold_cons, formsStep, if_neg (h e List.mem_cons_self)]
      exact ih (fun x hx => h x (List.mem_cons_of_mem e hx)) acc

/-- 中文说明：**π 侧的片段不变性**：追加段完全不提及该关系时，投影值不动。
这是契约里"追加不遗忘"在 π 上唯一诚实的版本。 -/
theorem forms_congruent_under_nonmentioning_suffix {Rel : Type} [DecidableEq Rel]
    (L : Ledger Rel) (s : Ledger Rel) (r : Rel)
    (h : ∀ e, e ∈ s → ¬ recordMentions r e) :
    formsB (L ++ s) r = formsB L r := by
  rw [formsB_append, formsFold_nonmentioning r s h]

/-- 中文说明：纯追加折叠的单步累加器：已为真则保持真；本条是指向 `r` 的成立记录则转真。 -/
def everStep {Rel : Type} [DecidableEq Rel]
    (r : Rel) (e : FormationRecord Rel) (acc : Bool) : Bool :=
  match acc, recordMentionsB r e, recordIsFormation e with
  | true, _, _ => true
  | false, true, true => true
  | false, _, _ => false

/-- 中文说明：纯追加投影的折叠机器（对应冻结内核 `R + formed`：只增不减）。 -/
def formsEverFold {Rel : Type} [DecidableEq Rel]
    (r : Rel) (acc : Bool) : Ledger Rel → Bool
  | [] => acc
  | e :: rest => formsEverFold r (everStep r e acc) rest

/-- 中文说明：纯追加投影的布尔形式：`r` 是否**曾**被成立记录引入。 -/
def formsEverB {Rel : Type} [DecidableEq Rel] (L : Ledger Rel) (r : Rel) : Bool :=
  formsEverFold r false L

/-- 中文说明：纯追加投影的命题形式；冻结内核 `R + formed` 能表达的只有这一层。 -/
abbrev formsEver {Rel : Type} [DecidableEq Rel] (L : Ledger Rel) (r : Rel) : Prop :=
  formsEverB L r = true

/-- 中文说明：纯追加折叠的空账本值。 -/
theorem formsEverFold_nil {Rel : Type} [DecidableEq Rel]
    (r : Rel) (acc : Bool) : formsEverFold r acc ([] : Ledger Rel) = acc := rfl

/-- 中文说明：纯追加折叠的单步展开。 -/
theorem formsEverFold_cons {Rel : Type} [DecidableEq Rel]
    (r : Rel) (acc : Bool) (e : FormationRecord Rel) (rest : Ledger Rel) :
    formsEverFold r acc (e :: rest) = formsEverFold r (everStep r e acc) rest := rfl

/-- 中文说明：累加器已为真时纯追加折叠恒为真（"曾经成立"不可被擦除的计算内核）。 -/
theorem everStep_true {Rel : Type} [DecidableEq Rel]
    (r : Rel) (e : FormationRecord Rel) : everStep r e true = true := rfl

/-- 中文说明：一旦取真，之后一切追加都保持真值。 -/
theorem formsEverFold_true {Rel : Type} [DecidableEq Rel]
    (r : Rel) : ∀ (s : Ledger Rel), formsEverFold r true s = true := by
  intro s
  induction s with
  | nil => rfl
  | cons e rest ih => rw [formsEverFold_cons, everStep_true]; exact ih

/-- 中文说明：纯追加折叠与拼接相容。 -/
theorem formsEverFold_append {Rel : Type} [DecidableEq Rel]
    (r : Rel) (acc : Bool) (L s : Ledger Rel) :
    formsEverFold r acc (L ++ s) = formsEverFold r (formsEverFold r acc L) s := by
  induction L generalizing acc with
  | nil => rfl
  | cons a l ih =>
      rw [List.cons_append, formsEverFold_cons, ih (everStep r a acc), formsEverFold_cons]

/-- 中文说明：**追加不遗忘**（纯追加投影）：一旦成立记录入账，任何追加段都抹不去它。
法律读法：冻结内核 `R_{t+1} = R_t + formed`（kernel.py:238）只记得"曾经成立"，
因此"某关系已不存在"在其内不可表达——这正是账本＋投影要补的洞。 -/
theorem append_is_ideographic {Rel : Type} [DecidableEq Rel]
    (L s : Ledger Rel) (r : Rel) :
    formsEver L r → formsEver (L ++ s) r := by
  intro h
  unfold formsEver formsEverB at h ⊢
  rw [formsEverFold_append, h]
  exact formsEverFold_true r s

/-- 中文说明：π 与纯追加投影在同一账本上的比较引理（布尔形式）。 -/
theorem formsEverFold_of_formsFold {Rel : Type} [DecidableEq Rel]
    (r : Rel) :
    ∀ (L : Ledger Rel), formsFold r false L = true → formsEverFold r false L = true := by
  intro L
  induction L with
  | nil => intro h; exact h
  | cons e rest ih =>
      intro h
      rw [formsFold_cons, formsStep] at h
      rw [formsEverFold_cons]
      by_cases hd : recordMentions r e
      · rw [if_pos hd] at h
        by_cases hf : recordIsFormation e = true
        · have he : everStep r e false = true := by
            unfold everStep
            rw [recordMentionsB_true r e hd, hf]
          rw [he]
          exact formsEverFold_true r rest
        · rw [hf] at h
          have he : everStep r e false = false := by
            unfold everStep
            rw [recordMentionsB_true r e hd, hf]
          rw [he]
          exact ih h
      · rw [if_neg hd] at h
        have he : everStep r e false = false := by
          unfold everStep
          rw [recordMentionsB_false r e hd]
        rw [he]
        exact ih h

/-- 中文说明：π 是纯追加投影的**细化**：当前有效蕴含曾经成立（两层不是同一事物）。 -/
theorem formsEver_of_forms {Rel : Type} [DecidableEq Rel]
    (L : Ledger Rel) (r : Rel) : forms L r → formsEver L r :=
  formsEverFold_of_formsFold r L

/-- 中文说明：事件效果类别四分：形成性裁判、终止性裁判、给付（履行）、宣告性裁判。 -/
inductive EffectKind
  | formativeAdjudication
  | terminatingAdjudication
  | performance
  | declaratory
  deriving DecidableEq, Repr

/-- 中文说明：缝合事件。构造子彼此不相交，故"给付不携带成立记录"是类型层事实。 -/
inductive SeamEvent (Rel : Type) where
  | formative (eventId : String) (rel : Rel)
  | terminating (eventId : String) (rel : Rel)
  | performance (eventId : String) (obligor : String) (rel : Rel) (amount : Nat)
  | declaratory (eventId : String)

/-- 中文说明：事件的效果类别。 -/
def effectKind {Rel : Type} : SeamEvent Rel → EffectKind
  | .formative _ _ => .formativeAdjudication
  | .terminating _ _ => .terminatingAdjudication
  | .performance _ _ _ _ => .performance
  | .declaratory _ => .declaratory

/-- 中文说明：单步泛函 `next`：只把新记录追加到账本末尾，从不修改既有记录。
冻结条款四在此被保留为：只有形成性事件写入成立记录。 -/
def next {Rel : Type} : Ledger Rel → SeamEvent Rel → Ledger Rel
  | L, .formative eventId rel => L ++ [formedRecord eventId rel]
  | L, .terminating eventId rel => L ++ [terminatedRecord eventId rel]
  | L, .performance _ _ _ _ => L
  | L, .declaratory _ => L

/-- 中文说明：形成性事件的语义＝追加成立记录。 -/
theorem next_formative_is_append {Rel : Type}
    (L : Ledger Rel) (eventId : String) (rel : Rel) :
    next L (.formative eventId rel) = L ++ [formedRecord eventId rel] := rfl

/-- 中文说明：终止性事件的语义＝追加终止记录（不是删除）。 -/
theorem next_terminating_is_append {Rel : Type}
    (L : Ledger Rel) (eventId : String) (rel : Rel) :
    next L (.terminating eventId rel) = L ++ [terminatedRecord eventId rel] := rfl

/-- 中文说明：给付事件对关系账本是空操作（冻结条款四：非形成性事件不动实体状态）。 -/
theorem next_performance_is_identity {Rel : Type}
    (L : Ledger Rel) (eventId obligor : String) (rel : Rel) (amount : Nat) :
    next L (.performance eventId obligor rel amount) = L := rfl

/-- 中文说明：宣告性事件对关系账本是空操作。 -/
theorem next_declaratory_is_identity {Rel : Type}
    (L : Ledger Rel) (eventId : String) :
    next L (.declaratory eventId) = L := rfl

/-- 中文说明：形成性单步的布尔展开式。 -/
theorem formsB_next_formative {Rel : Type} [DecidableEq Rel]
    (L : Ledger Rel) (eventId : String) (rel r : Rel) :
    formsB (next L (.formative eventId rel)) r =
      if r = rel then true else formsB L r :=
  formsB_append_formed L eventId rel r

/-- 中文说明：**主等价定理** π(追加) ≡ 逐步语义（形成性片段）：
`forms (next L e) r` 当且仅当"被形成者就是 `r`"或"`r` 在 `L` 下已有效"。
片段相对：只覆盖形成性裁判事件；终止与非裁判片段另证。 -/
theorem projection_of_append_matches_step {Rel : Type} [DecidableEq Rel]
    (L : Ledger Rel) (eventId : String) (rel r : Rel) :
    forms (next L (.formative eventId rel)) r ↔ (r = rel ∨ forms L r) := by
  constructor
  · intro h
    rw [formsB_next_formative] at h
    by_cases hd : r = rel
    · exact Or.inl hd
    · rw [if_neg hd] at h
      exact Or.inr h
  · intro h
    rw [formsB_next_formative]
    cases h with
    | inl hd => exact if_pos hd
    | inr hf =>
        by_cases hd : r = rel
        · exact if_pos hd
        · rw [if_neg hd]
          exact hf

/-- 中文说明：终止片段的同类结论：追加终止记录后，该关系在 π 下退场（`nextR` 不含它）。 -/
theorem projection_of_append_matches_step_terminating {Rel : Type} [DecidableEq Rel]
    (L : Ledger Rel) (eventId : String) (rel : Rel) :
    ¬ forms (next L (.terminating eventId rel)) rel := by
  intro h
  rw [next_terminating_is_append, projection_append_terminated] at h
  exact Bool.false_ne_true h

/-- 中文说明：语义谓词 `effective`（契约要求的名字）＝投影 π。 -/
abbrev effective {Rel : Type} [DecidableEq Rel] (L : Ledger Rel) (r : Rel) : Prop :=
  forms L r

/-- 中文说明：`effective (next L e) r ↔ ...`（形成性事件）。 -/
theorem effective_next_formative_iff {Rel : Type} [DecidableEq Rel]
    (L : Ledger Rel) (eventId : String) (rel r : Rel) :
    effective (next L (.formative eventId rel)) r ↔ (r = rel ∨ effective L r) :=
  projection_of_append_matches_step L eventId rel r

/-- 中文说明：非裁判片段：给付与宣告事件下，`r` 的有效性一字不动。 -/
theorem effective_next_nonformative_iff {Rel : Type} [DecidableEq Rel]
    (L : Ledger Rel) (r : Rel) (ev : SeamEvent Rel)
    (hneFormative : effectKind ev ≠ EffectKind.formativeAdjudication)
    (hneTerminating : effectKind ev ≠ EffectKind.terminatingAdjudication) :
    effective (next L ev) r ↔ effective L r := by
  cases ev with
  | formative _ _ => exact absurd rfl hneFormative
  | terminating _ _ => exact absurd rfl hneTerminating
  | performance _ _ _ _ => rw [next_performance_is_identity]; exact Iff.rfl
  | declaratory _ => rw [next_declaratory_is_identity]; exact Iff.rfl

/-- 中文说明：见证用关系对象（仅结构见证，不认定任何真实案件的法律关系）。 -/
def relationDemo : Relation :=
  { relationId := "R-D", parties := ["甲", "乙"], kind := "买卖", sharedConstraints := [] }

/-- 中文说明：第二个见证用关系对象。 -/
def relationOther : Relation :=
  { relationId := "R-E", parties := ["丙"], kind := "租赁", sharedConstraints := [] }

/-- 中文说明：只含成立记录的账本。 -/
def ledgerFormedDemo : Ledger Relation := [formedRecord "J1" relationDemo]

/-- 中文说明：先成立后终止的账本（两条记录并存，历史未被涂改）。 -/
def ledgerTermDemo : Ledger Relation :=
  ledgerFormedDemo ++ [terminatedRecord "J2" relationDemo]

/-- 中文说明：成立账本在 π 下有效（闭式见证）。 -/
theorem ledgerFormedDemo_forms : forms ledgerFormedDemo relationDemo := by
  decide

/-- 中文说明：**对照定理**：同一关系在同一条账本上，π 判定其已不存在，而纯追加投影仍判定其
曾经成立。冻结内核只有后一层（`R + formed`，kernel.py:238；`Relation` 无失效字段，
LegalModelV2.lean:134），故"消灭"在其内没有对应物——本件不动冻结内核，只平行补齐。 -/
theorem ledger_can_express_termination :
    ¬ forms ledgerTermDemo relationDemo ∧ formsEver ledgerTermDemo relationDemo := by
  refine ⟨by decide, by decide⟩

/-- 中文说明：π 对追加**不**单调的闭式见证：追加一条终止记录就把真值翻成假。
故契约把"追加不遗忘"挂在 `forms` 上的那句对本件语义为假，该正定理改挂 `formsEver`。 -/
theorem termination_breaks_projection :
    forms ledgerFormedDemo relationDemo ∧
      ¬ forms (ledgerFormedDemo ++ [terminatedRecord "J2" relationDemo]) relationDemo := by
  refine ⟨by decide, by decide⟩

/-- 中文说明：他关系的终止记录不动本关系的投影（片段：追加段不提及 `r`）。 -/
theorem termination_of_other_leaves_projection {Rel : Type} [DecidableEq Rel]
    (L : Ledger Rel) (eventId : String) {r r' : Rel} (h : r ≠ r') :
    formsB (L ++ [terminatedRecord eventId r']) r = formsB L r := by
  rw [formsB_append_terminated, if_neg h]

/-! ## Part ② 非裁判性履行通道 -/

/-- 中文说明：债务＝义务人 + 债务额。金额用 `Nat`，故"负债务"在本模型里不可表示。 -/
structure Debt where
  obligor : String
  amount : Nat
  deriving DecidableEq, Repr

/-- 中文说明：一步给付的四个字段：所针对债务、已为给付额、经抵扣的实付额、给付后未偿余额。
`applied` 与 `outstanding` 是**计算字段**，由 `performStep` 给出，不是自由输入。 -/
structure PerformanceStep where
  debt : Debt
  performed : Nat
  applied : Nat
  outstanding : Nat
  deriving DecidableEq, Repr

/-- 中文说明：实付额＝债额与已为给付的较小者（超额部分不在本通道内抵扣）。 -/
def appliedAmount (amount performed : Nat) : Nat := min amount performed

/-- 中文说明：未偿余额＝债额的自然数截断减法；`Nat` 减法不可能为负。
注意与 P-097 的 `allocateOne` 之 `remainder`（溢缴余额）方向相反，见模块头未面第 6 条。 -/
def outstandingAfter (amount performed : Nat) : Nat := amount - performed

/-- 中文说明：给付一步的完整计算。 -/
def performStep (d : Debt) (performed : Nat) : PerformanceStep :=
  { debt := d
    performed := performed
    applied := appliedAmount d.amount performed
    outstanding := outstandingAfter d.amount performed }

/-- 中文说明：见证债务：债 10，义务人甲。 -/
def debtDemo : Debt := { obligor := "甲", amount := 10 }

/-- 中文说明：**完整见证**：债 10、已为给付 3 ⇒ 实付 3、未偿 7。 -/
theorem performance_witness_10_3 :
    (performStep debtDemo 3).applied = 3 ∧
      (performStep debtDemo 3).outstanding = 7 := by
  decide

/-- 中文说明：**守恒定理**（无条件）：实付 + 未偿 = 债额。实付用 `min` 卡住，
故超额给付时也不需要任何附加前提（`min a p + (a ∸ p) = a` 对自然数恒成立）。 -/
theorem applied_plus_outstanding_eq_amount (amount performed : Nat) :
    appliedAmount amount performed + outstandingAfter amount performed = amount := by
  omega

/-- 中文说明：守恒定理在 `PerformanceStep` 结构上的读数（非空洞：字段确由计算给出）。 -/
theorem performStep_conservation (d : Debt) (performed : Nat) :
    (performStep d performed).applied + (performStep d performed).outstanding = d.amount :=
  applied_plus_outstanding_eq_amount d.amount performed

/-- 中文说明：守恒的具体读数：3 + 7 = 10。 -/
theorem performStep_conservation_witness :
    (performStep debtDemo 3).applied + (performStep debtDemo 3).outstanding = 10 := by
  decide

/-- 中文说明：**超额给付不产生负义务**：给付不小于债额时未偿余额为 0。 -/
theorem overperformance_leaves_zero (amount performed : Nat) (h : amount ≤ performed) :
    outstandingAfter amount performed = 0 := by
  omega

/-- 中文说明：超额给付的闭式见证：债 10、给付 12 ⇒ 未偿 0、实付 10（溢出 2 不在本通道抵扣）。 -/
theorem overperformance_witness_10_12 :
    (performStep debtDemo 12).outstanding = 0 ∧
      (performStep debtDemo 12).applied = 10 := by
  decide

/-- 中文说明：未偿余额永不为负（`Nat` 类型层事实的本件构造性表达）。 -/
theorem outstanding_never_negative (amount performed : Nat) :
    0 ≤ outstandingAfter amount performed := Nat.zero_le _

/-- 中文说明：实付额既不超过债额，也不超过已为给付。 -/
theorem applied_bounds (amount performed : Nat) :
    appliedAmount amount performed ≤ amount ∧
      appliedAmount amount performed ≤ performed := by
  omega

/-- 中文说明：**给付不是创设**：给付事件下 π 对每个关系的取值一字不变（关系账本上无新记录）。 -/
theorem performance_not_creation {Rel : Type} [DecidableEq Rel]
    (L : Ledger Rel) (eventId obligor : String) (rel : Rel) (amount : Nat) (r : Rel) :
    forms (next L (.performance eventId obligor rel amount)) r ↔ forms L r := by
  rw [next_performance_is_identity]

/-- 中文说明：给付事件的布尔形式：取值相等，而非仅等价。 -/
theorem performance_not_creation_bool {Rel : Type} [DecidableEq Rel]
    (L : Ledger Rel) (eventId obligor : String) (rel : Rel) (amount : Nat) (r : Rel) :
    formsB (next L (.performance eventId obligor rel amount)) r = formsB L r := by
  rw [next_performance_is_identity]

/-- 中文说明：给付事件也从不延长账本——`next` 不追加任何记录。 -/
theorem performance_appends_no_record {Rel : Type}
    (L : Ledger Rel) (eventId obligor : String) (rel : Rel) (amount : Nat) :
    (next L (.performance eventId obligor rel amount)).length = L.length :=
  congrArg List.length (next_performance_is_identity L eventId obligor rel amount)

/-- 中文说明：给付事件的效果类别是 `performance`，与形成性裁判类别不同（构造子不相交）。 -/
theorem performance_effectKind_ne_formative {Rel : Type}
    (eventId obligor : String) (rel : Rel) (amount : Nat) :
    effectKind (SeamEvent.performance eventId obligor rel amount) ≠
      EffectKind.formativeAdjudication := by
  intro hh
  exact absurd hh (by decide)

/-- 中文说明：形成性裁判与给付在同一 `EffectKind` 上互斥（两通道不相交的另一向）。 -/
theorem formative_effectKind_ne_performance {Rel : Type}
    (eventId : String) (rel : Rel) :
    effectKind (SeamEvent.formative eventId rel) ≠ EffectKind.performance := by
  intro hh
  exact absurd hh (by decide)

/-- 中文说明：履行通道的账本类型：给付记录序列（与关系账本 `Ledger` 是两条平行通道）。 -/
abbrev PerformLedger := List PerformanceStep

/-- 中文说明：见证用履行账本：先给付 3，再清偿剩余 7。 -/
def performLedgerDemo : PerformLedger :=
  [performStep debtDemo 3, performStep debtDemo 7]

/-- 中文说明：见证履行账本的两步实付之和为 10，等于债额（多步守恒的最小读数）。 -/
theorem performLedgerDemo_total :
    (performStep debtDemo 3).applied + (performStep debtDemo 7).applied = 10 := by
  decide

/-- 中文说明：见证关系账本：该债权债务关系由裁判"J1"成立。 -/
def relationLedgerDemo : Ledger Relation := [formedRecord "J1" relationDemo]

/-- 中文说明：**消灭不等于从未成立**（P 侧登记）：债务经全额履行后未偿余额为 0（义务消灭），
但关系账本仍保留"J1 成立"的历史记录，π 与纯追加投影都仍判定其有效成立过；而空账本上同一
关系判定为"从未成立"。四个事实一起做见证，故"清偿后关系不存在"绝不可读成"关系从未产生"。 -/
theorem register_p_side :
    forms (next relationLedgerDemo
      (SeamEvent.performance "P1" "甲" relationDemo 10)) relationDemo ∧
      outstandingAfter 10 10 = 0 ∧
      formsEver (next relationLedgerDemo
        (SeamEvent.performance "P1" "甲" relationDemo 10)) relationDemo ∧
      ¬ forms ([] : Ledger Relation) relationDemo := by
  refine ⟨by decide, rfl, by decide, by decide⟩

/-- 中文说明：两通道互不越权的形式表达：给付序列只写债权账本，关系账本的 π 取值不变。 -/
theorem performance_channels_are_disjoint {Rel : Type} [DecidableEq Rel]
    (L : Ledger Rel) (d : Debt) (p : Nat) (r : Rel) :
    formsB (next L (.performance "P" d.obligor r p)) r = formsB L r :=
  performance_not_creation_bool L "P" d.obligor r p r

/-! ## P-015 位阶使用点（S5 片段；一般定理属 S1） -/

/-- 中文说明：位阶表元素＝关系标识 + 位次数值。位次是**声明的数据**，不是推理出来的。 -/
structure RankedRel where
  relId : String
  rank : Nat
  deriving DecidableEq, Repr

/-- 中文说明：声明式位阶：`rankLt a b` 当且仅当 `a` 的位次高于 `b`。 -/
def rankLt (a b : RankedRel) : Prop := b.rank < a.rank

/-- 中文说明：位次严格序反身不成立（无自环）——"有限无环"在本片段的最小可读形式。 -/
theorem rank_lt_irreflexive (a : RankedRel) : ¬ rankLt a a := fun h => Nat.lt_irrefl _ h

/-- 中文说明：位次严格序传递。 -/
theorem rank_lt_transitive (a b c : RankedRel)
    (h1 : rankLt a b) (h2 : rankLt b c) : rankLt a c := by
  omega

/-- 中文说明：二元择高路由：`b` 位次更高时取 `b`，否则取 `a`。
平局保留**声明序中在前者**（`a`），是显式决胜规则，不是任意选择。 -/
def routeTwo (a b : RankedRel) : RankedRel :=
  if a.rank < b.rank then b else a

/-- 中文说明：择高路由的闭式见证：位次 3 对 7 ⇒ 胜者是位次 7 者。 -/
theorem routeTwo_witness_3_7 :
    routeTwo { relId := "R-A", rank := 3 } { relId := "R-B", rank := 7 } =
      { relId := "R-B", rank := 7 } := by
  decide

/-- 中文说明：胜者位次支配两者。 -/
theorem routeTwo_dominates (a b : RankedRel) :
    a.rank ≤ (routeTwo a b).rank ∧ b.rank ≤ (routeTwo a b).rank := by
  by_cases hd : a.rank < b.rank
  · unfold routeTwo
    rw [if_pos hd]
    exact ⟨Nat.le_of_lt hd, Nat.le_refl _⟩
  · unfold routeTwo
    rw [if_neg hd]
    exact ⟨Nat.le_refl _, Nat.le_of_not_lt hd⟩

/-- 中文说明：胜者必是两位候选之一（不引入第三者）。 -/
theorem routeTwo_is_one_of_two (a b : RankedRel) :
    routeTwo a b = a ∨ routeTwo a b = b := by
  by_cases hd : a.rank < b.rank
  · unfold routeTwo
    rw [if_pos hd]
    exact Or.inr rfl
  · unfold routeTwo
    rw [if_neg hd]
    exact Or.inl rfl

/-- 中文说明：有限候选表上的择高折叠（结构递归，平局保留在先者）。 -/
def foldMax (acc : RankedRel) : List RankedRel → RankedRel
  | [] => acc
  | b :: rest => if acc.rank < b.rank then foldMax b rest else foldMax acc rest

/-- 中文说明：折叠的空表值。 -/
theorem foldMax_nil (acc : RankedRel) : foldMax acc [] = acc := rfl

/-- 中文说明：折叠的递归展开式。 -/
theorem foldMax_cons (acc b : RankedRel) (rest : List RankedRel) :
    foldMax acc (b :: rest) =
      if acc.rank < b.rank then foldMax b rest else foldMax acc rest := rfl

/-- 中文说明：折叠结果仍在原表里（不凭空创造候选）。 -/
theorem foldMax_mem (acc : RankedRel) (rest : List RankedRel) :
    foldMax acc rest ∈ acc :: rest := by
  induction rest generalizing acc with
  | nil => exact List.mem_cons_self
  | cons b l ih =>
      rw [foldMax_cons]
      split
      · exact List.mem_cons_of_mem acc (ih b)
      · exact List.mem_cons_of_mem acc (ih acc)

/-- 中文说明：表头位次不超过折叠结果。 -/
theorem acc_le_foldMax (acc : RankedRel) (rest : List RankedRel) :
    acc.rank ≤ (foldMax acc rest).rank := by
  induction rest generalizing acc with
  | nil => exact Nat.le_refl _
  | cons b l ih =>
      rw [foldMax_cons]
      by_cases hd : acc.rank < b.rank
      · rw [if_pos hd]
        exact Nat.le_trans (Nat.le_of_lt hd) (ih b)
      · rw [if_neg hd]
        exact ih acc

/-- 中文说明：表尾任一元素的位次不超过折叠结果。 -/
theorem foldMax_ub_tail (acc : RankedRel) :
    ∀ (rest : List RankedRel), ∀ x, x ∈ rest → x.rank ≤ (foldMax acc rest).rank := by
  intro rest
  induction rest generalizing acc with
  | nil => intro x hx; exact absurd hx (by simp)
  | cons b l ih =>
      intro x hx
      rw [foldMax_cons]
      by_cases hd : acc.rank < b.rank
      · rw [if_pos hd]
        rw [List.mem_cons] at hx
        cases hx with
        | inl heq => rw [heq]; exact acc_le_foldMax b l
        | inr hl => exact ih b x hl
      · rw [if_neg hd]
        rw [List.mem_cons] at hx
        cases hx with
        | inl heq =>
            rw [heq]
            exact Nat.le_trans (Nat.le_of_not_lt hd) (acc_le_foldMax acc l)
        | inr hl => exact ih acc x hl

/-- 中文说明：折叠结果是整表的位次上界。 -/
theorem foldMax_ub (acc : RankedRel) (rest : List RankedRel) :
    ∀ x, x ∈ acc :: rest → x.rank ≤ (foldMax acc rest).rank := by
  intro x hx
  rw [List.mem_cons] at hx
  cases hx with
  | inl heq => rw [heq]; exact acc_le_foldMax acc rest
  | inr hl => exact foldMax_ub_tail acc rest x hl

/-- 中文说明：**有限非空位阶表上极大元存在**（P-015 的 S5 使用点，构造性：由折叠给出 witness）。
片段相对：位次为 `Nat` 的显式表；一般"有限无环优先关系"的极大元与冲突消解属缝合件 S1。 -/
theorem exists_maximal_in_ranked (cs : List RankedRel) (h : cs ≠ []) :
    ∃ m, m ∈ cs ∧ ∀ x, x ∈ cs → x.rank ≤ m.rank := by
  cases cs with
  | nil => exact absurd rfl h
  | cons a rest =>
      refine ⟨foldMax a rest, foldMax_mem a rest, foldMax_ub a rest⟩

/-- 中文说明：**位阶路由保留被投影存续者**：两个竞争关系都在 π 下存续时，
路由胜者也在 π 下存续。本件只把"择高"做成不淘汰存续者的筛选，不宣称解决冲突本身。 -/
theorem priority_route_keeps_projected {L : Ledger RankedRel}
    (a b : RankedRel) (ha : forms L a) (hb : forms L b) : forms L (routeTwo a b) := by
  by_cases hd : a.rank < b.rank
  · unfold routeTwo
    rw [if_pos hd]
    exact hb
  · unfold routeTwo
    rw [if_neg hd]
    exact ha

/-- 中文说明：位阶路由与终止通道的相容片段：被终止者不再存续，故
`priority_route_keeps_projected` 的前提不满足时本件不给任何结论（fail-closed 记录）。 -/
theorem routeTwo_never_invents_survival {L : Ledger RankedRel}
    (eventId : String) (a : RankedRel) :
    ¬ forms (next L (.terminating eventId a)) a :=
  projection_of_append_matches_step_terminating L eventId a

/-- 中文说明：见证位阶表（显式声明的有限位次表）。 -/
def priorityTableDemo : List RankedRel :=
  [{ relId := "R-A", rank := 7 }, { relId := "R-B", rank := 3 }]

/-- 中文说明：见证位阶表非空，故极大元存在可用。 -/
theorem priorityTableDemo_nonempty : priorityTableDemo ≠ [] := by
  decide

/-- 中文说明：位阶表片段上确有极大元（`exists_maximal_in_ranked` 的具体读数）。 -/
theorem priorityTableDemo_has_maximal :
    ∃ m, m ∈ priorityTableDemo ∧ ∀ x, x ∈ priorityTableDemo → x.rank ≤ m.rank :=
  exists_maximal_in_ranked priorityTableDemo priorityTableDemo_nonempty

end JurisLean.Seams.InstitutionalEffects
