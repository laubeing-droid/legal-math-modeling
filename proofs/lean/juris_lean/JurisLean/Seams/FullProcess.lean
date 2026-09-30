import JurisLean.Seams.InstitutionalEffects
import JurisLean.ReceiptAuthority
import Mathlib.Tactic

/-!
中文说明：S6 缝合件——运行闭环（L7）。本件把 S5 的账本投影与履行通道放进一条**有限**轨迹里
走一遍，并且诚实地说出这条链保证了什么、没保证什么。

# §法律语义

日常语言里的"闭环"有两种读法：(1) 每件事都入账、每笔账都对得上；(2) 走完一圈就得到本案的
裁判结论。本件只保证 (1)，并明确拒绝 (2)。

- 账本（S5 的 `Ledger` 与 `next`）只记录**事件写了什么**，不判断该事件是否**有权**被写。
  "谁可以终止一个法律关系"属缝合件 S7（规范回流）与 S2（终局策略）；本件把它们写成显式假设
  `OutOfDomainSemantics`，不解释其内容、不代替其证明。
- 回执（事实确认书、证书、决定书）在真实程序里是**导出之后的产物**。本件把这句话做成定理：
  回执堆 `pile` 不进入任何状态转移（`runTrace_pile_unchanged`）；声明域内被账本准入的回执必带
  语义导出（`receipt_has_semantic_derivation`、`admitted_receipt_has_derivation`）；域外回流的
  回执**只有账本承认、没有导出**（`backflow_admitted_without_derivation`）；层级不足的回执
  **即使记录真在账本里也不被准入**（`seeded_proposal_copy_not_admitted`）。四条一起做 P-123
  "回执账本是果不是因"的形式读数。
- 守恒（实付＋未偿＝债额）、只追加、不遗忘、通道不相交，是**簿记层面**的性质，对任何只追加的
  域外语义都稳健（`invariants_hold_under_any_out_of_domain`）。但"本案有了裁判结论"不是簿记
  性质：全额履行的轨迹每一步都合法，终态形状仍是 `undecidedPerformance`
  （`closure_is_not_uniform_claim`）。

# §数学对象

- `FullEvent Rel`：域内事件（S5 的 `SeamEvent`）＋两个**域外**构造子 `normBackflow`（S7 规范
  回流）与 `historyRewrite`（S2 终止策略缺席时的涂改读数）。
- `State Rel`：⟨关系账本 `ledger : Ledger Rel`、履行账本 `perf : PerformLedger`、登记债务
  `debt : Debt`、回执堆 `pile : List (Receipt Rel)`⟩。
- `DeclaredEventDomain`＋`domainMember`：四类效果类别的**开关表**。`fullDomain` 放开 S5 四类；
  `nonAdjudicativeDomain` 只放开给付与宣告（S5 的"非裁判性"片段）。两个域外构造子在**任何**
  声明域下恒取 `false`。
- `coreStep`／`runTrace`：关系账本一律用 S5 的 `next` 折叠；给付事件另在履行账本追加
  `performStep`；回执堆一字不动。
- `recordOfEvent`／`traceRecords`：事件语义的**产物记录**（给付、宣告与两个域外构造子无产物）。
- `invariantsHeld` 四分量：守恒（引 S5 `applied_plus_outstanding_eq_amount`）、只追加、
  不遗忘（引 S5 `append_is_ideographic`，纯追加投影 `formsEver` 读数）、通道不相交
  （引 S5 `performance_not_creation`）。
- `Receipt Rel`＋`Admitted`＝⟨记录确在账本⟩ ∧ ⟨层级可签发 factAttestation⟩，后者直接取
  `JurisLean.canIssue`（ReceiptAuthority）。`HasDerivation`＝轨迹里存在一个事件，其语义产物
  正是该回执的记录。
- `OutcomeShape`：本件自有的四态裁判形状（**不** import S2）。

# §证与不证

**证**：前缀保全四分量（`finite_trace_preserves_legal_invariants`，含 `take` 读数）；非裁判域内
轨迹对 π 的稳定（`nonadjudicative_trace_stabilizes_projection`）；准入回执必带导出；回执堆不进入
转移；层级门槛五条（逐条引 ReceiptAuthority 原定理名）；域相对性
（`preservation_is_domain_relative`：去掉域假设后只追加、不遗忘、导出性**确实**失效）；对任意
只追加域外语义的稳健性；闭环不是全称主张（`closure_is_not_uniform_claim`）；有限性上界
（`runTrace_length_bound`、`forms_at_end_is_bounded_fold`、`performStep_values_bounded`）。

**不证**：见§未覆盖片段。本件不含任何收敛、真实案件、真实法条断言；`pi_oscillates_witness`
与 `preservation_over_unit_type` 是"不证"的正面见证。

# §未覆盖片段（逐条，缺失一律 fail-closed）

1. **S7 规范回流**：哪个回流事件有权改写关系账本/位阶表，本件不判定；`normBackflow` 在
   `domainMember` 上恒 `false`。其合法性属 S7（`JurisLean.Seams.PrecedentFlow`，本件禁止 import，
   且该件当前为红：`Unknown constant JurisLean.Genealogy.Part1.P019`）。
2. **S2 终局策略**：`OutcomeShape` 只是本件自有的形状记号，与 S2 的 `DecisionStatus` 之间
   **没有**桥接定理；把 `undecidedPerformance` 读成任何法律上的"未决裁判"都超出本件。
3. **S1／S3／S4／XT**：本件未 import；凡需要其一之处都写成显式假设或列为未面。
4. **多笔串并**：一债多付、多债一付的分配守恒未证（S5 未面第 6 条同判）；`debt` 字段在轨迹中
   不滚动，故每步守恒只相对**当时登记的债务**成立。
5. **初始账本非空时**：`receipt_has_semantic_derivation` 需要 `st₀.ledger = []`；初始账本里既有
   记录的准入在本件内**没有**导出（导出只解释轨迹内的事件），该缺口不假装补上。
6. **π 的全局不变性**：只追加与不遗忘说的都是 `formsEver`；末次提及投影 π 可变，
   由 `pi_stability_fails_outside_domain` 与 `pi_oscillates_witness` 做出见证，本件不给收敛。
7. **冻结内核精化**：本件的 `runTrace` 与 `JurisLean.KernelV3.transfer` 之间无精化定理。
8. **回执真实性**：`Receipt.ref` 是字符串引证，不绑定任何真实文书；层级是输入数据，
   不是本件推出的结论。

# §档位

定义 [构造性定义]；定理 [本件内完整证明：零 `sorry`、零 `admit`、零新 `axiom`]；
域外事件语义 [显式假设记录 `OutOfDomainSemantics`，本件不证明其法律正当性]；
上列 8 条 [未覆盖片段，状态 UNPROVED 且不属于本件]。
编译认定待 CI：本地构建只是预备性预检，绝不称 PASS。
-/

namespace JurisLean.Seams.FullProcess

open JurisLean.Seams.InstitutionalEffects

/-! ## Part 1 完整事件语言、状态与声明域 -/

/-- 中文说明：闭环的完整事件语言。`core` 是 S5 声明的四类缝合事件（域内）；`normBackflow` 是
S7 的规范回流、`historyRewrite` 是"S2 终局策略缺席时的涂改"读数，两者都是**域外**：本件拒绝为
它们赋予语义导出，也不允许它们进入保全定理的前提。 -/
inductive FullEvent (Rel : Type) where
  | core (ev : SeamEvent Rel)
  | normBackflow (eventId : String) (rel : Rel)
  | historyRewrite (eventId : String) (keep : Nat)

/-- 中文说明：回执形状＝账本记录的可提交副本＋提交者自报的权威层级。层级取
`JurisLean.AuthorityLevel`（ReceiptAuthority），本件不重新定义层级格。 -/
structure Receipt (Rel : Type) where
  ref : String
  rel : Rel
  kind : RecordKind
  level : AuthorityLevel

/-- 中文说明：闭环状态。`ledger` 与 `perf` 是 S5 的两条平行通道；`debt` 是当前登记债务；
`pile` 是提交上来的回执堆——它在类型上是载荷，在转移上是常量（`coreStep_pile_unchanged`）。 -/
structure State (Rel : Type) where
  ledger : Ledger Rel
  perf : PerformLedger
  debt : Debt
  pile : List (Receipt Rel)

/-- 中文说明：轨迹＝声明事件的有限列表。没有不动点、没有极限、没有迭代算子。 -/
abbrev Trace (Rel : Type) := List (FullEvent Rel)

/-- 中文说明：声明事件域＝四类效果类别的开关表；域外构造子不在此表内，恒被排除。 -/
structure DeclaredEventDomain where
  allowsFormative : Bool
  allowsTerminating : Bool
  allowsPerformance : Bool
  allowsDeclaratory : Bool

/-- 中文说明：S5 全部四类核心事件都放开的域（含裁判性事件）。 -/
def fullDomain : DeclaredEventDomain :=
  { allowsFormative := true, allowsTerminating := true,
    allowsPerformance := true, allowsDeclaratory := true }

/-- 中文说明：S5 的非裁判性片段＝只放开给付与宣告，两个裁判类别关闭。 -/
def nonAdjudicativeDomain : DeclaredEventDomain :=
  { allowsFormative := false, allowsTerminating := false,
    allowsPerformance := true, allowsDeclaratory := true }

/-- 中文说明：类别开关的读取。 -/
def domAllows (dom : DeclaredEventDomain) (k : EffectKind) : Bool :=
  match k with
  | EffectKind.formativeAdjudication => dom.allowsFormative
  | EffectKind.terminatingAdjudication => dom.allowsTerminating
  | EffectKind.performance => dom.allowsPerformance
  | EffectKind.declaratory => dom.allowsDeclaratory

/-- 中文说明：`dom` 是否声明接受事件 `ev`。域外构造子对任何 `dom` 都取 `false`，
故"域"不是宽紧措辞，而是一张可判定的表。 -/
def domainMember (dom : DeclaredEventDomain) {Rel : Type} (ev : FullEvent Rel) : Bool :=
  match ev with
  | FullEvent.core e => domAllows dom (effectKind e)
  | FullEvent.normBackflow _ _ => false
  | FullEvent.historyRewrite _ _ => false

/-- 中文说明：整条轨迹落在声明域内（本件所有保全定理的前提）。 -/
def traceInDomain (dom : DeclaredEventDomain) {Rel : Type} (tr : Trace Rel) : Prop :=
  ∀ ev, ev ∈ tr → domainMember dom ev = true

/-- 中文说明：`fullDomain` 对每个类别都开。 -/
theorem domAllows_full (k : EffectKind) : domAllows fullDomain k = true := by
  cases k <;> rfl

/-- 中文说明：任何声明域允许的构造子，`fullDomain` 也允许（开关表单调）。 -/
theorem domainMember_full_of {Rel : Type} (dom : DeclaredEventDomain) (ev : FullEvent Rel)
    (h : domainMember dom ev = true) : domainMember fullDomain ev = true := by
  cases ev with
  | core e => exact domAllows_full (effectKind e)
  | normBackflow eid rel => exact absurd h Bool.false_ne_true
  | historyRewrite eid keep => exact absurd h Bool.false_ne_true

/-- 中文说明：布尔判定的二择律（本件用 `Bool.cases`，不用排中律）。 -/
theorem domainMember_dichotomy (dom : DeclaredEventDomain) {Rel : Type} (ev : FullEvent Rel) :
    domainMember dom ev = true ∨ domainMember dom ev = false := by
  cases domainMember dom ev
  · exact Or.inr rfl
  · exact Or.inl rfl

/-! ## Part 2 单步泛函与有限折叠 -/

/-- 中文说明：核心单步泛函。关系账本一律用 S5 的 `next`（只追加）；给付事件另在履行账本追加
S5 的 `performStep`（计算字段由 `min` 与截断减法给出）；回执堆 `pile` 一字不动——这正是
"果不是因"的机器读法。域外两个构造子的语义在此**显式给出**，以便本件能对它们证伪，
而不是假装它们不存在。 -/
def coreStep (st : State Rel) : FullEvent Rel → State Rel
  | FullEvent.core (SeamEvent.formative eid rel) =>
      { st with ledger := next st.ledger (SeamEvent.formative eid rel) }
  | FullEvent.core (SeamEvent.terminating eid rel) =>
      { st with ledger := next st.ledger (SeamEvent.terminating eid rel) }
  | FullEvent.core (SeamEvent.performance eid obligor rel amount) =>
      { st with
        ledger := next st.ledger (SeamEvent.performance eid obligor rel amount)
        perf := st.perf ++ [performStep st.debt amount] }
  | FullEvent.core (SeamEvent.declaratory eid) =>
      { st with ledger := next st.ledger (SeamEvent.declaratory eid) }
  | FullEvent.normBackflow eid rel =>
      { st with ledger := next st.ledger (SeamEvent.terminating eid rel) }
  | FullEvent.historyRewrite _ keep =>
      { st with ledger := st.ledger.take keep }

/-- 中文说明：成立事件的账本读数＝S5 `next_formative_is_append`。 -/
theorem coreStep_ledger_formative {Rel : Type} (st : State Rel) (eid : String) (rel : Rel) :
    (coreStep st (FullEvent.core (SeamEvent.formative eid rel))).ledger =
      st.ledger ++ [formedRecord eid rel] :=
  next_formative_is_append st.ledger eid rel

/-- 中文说明：终止事件的账本读数＝S5 `next_terminating_is_append`（追加记录，不是删除）。 -/
theorem coreStep_ledger_terminating {Rel : Type} (st : State Rel) (eid : String) (rel : Rel) :
    (coreStep st (FullEvent.core (SeamEvent.terminating eid rel))).ledger =
      st.ledger ++ [terminatedRecord eid rel] :=
  next_terminating_is_append st.ledger eid rel

/-- 中文说明：给付事件在关系账本上是空操作（S5 `next_performance_is_identity`）。 -/
theorem coreStep_ledger_performance {Rel : Type} (st : State Rel)
    (eid obligor : String) (rel : Rel) (amount : Nat) :
    (coreStep st (FullEvent.core (SeamEvent.performance eid obligor rel amount))).ledger =
      st.ledger :=
  next_performance_is_identity st.ledger eid obligor rel amount

/-- 中文说明：宣告事件在关系账本上是空操作（S5 `next_declaratory_is_identity`）。 -/
theorem coreStep_ledger_declaratory {Rel : Type} (st : State Rel) (eid : String) :
    (coreStep st (FullEvent.core (SeamEvent.declaratory eid))).ledger = st.ledger :=
  next_declaratory_is_identity st.ledger eid

/-- 中文说明：域外回流在账本上追加一条终止记录——它**只是**追加，所以簿记不变式仍成立；
它的**法律正当性**本件不判定（属 S7，见§未覆盖片段第 1 条）。 -/
theorem coreStep_ledger_normBackflow {Rel : Type} (st : State Rel) (eid : String) (rel : Rel) :
    (coreStep st (FullEvent.normBackflow eid rel)).ledger =
      st.ledger ++ [terminatedRecord eid rel] :=
  next_terminating_is_append st.ledger eid rel

/-- 中文说明：域外涂改把账本截短——历史被删，故"只追加"与"不遗忘"都失效（Part 5 做出见证）。 -/
theorem coreStep_ledger_historyRewrite {Rel : Type} (st : State Rel) (eid : String) (keep : Nat) :
    (coreStep st (FullEvent.historyRewrite eid keep)).ledger = st.ledger.take keep := rfl

/-- 中文说明：**回执堆不进入转移**：任何事件都不读它、也不写它。 -/
theorem coreStep_pile_unchanged {Rel : Type} (st : State Rel) (ev : FullEvent Rel) :
    (coreStep st ev).pile = st.pile := by
  cases ev with
  | core e => cases e <;> rfl
  | normBackflow eid rel => rfl
  | historyRewrite eid keep => rfl

/-- 中文说明：给付事件只追加一条履行记录。 -/
theorem coreStep_perf_performance {Rel : Type} (st : State Rel)
    (eid obligor : String) (rel : Rel) (amount : Nat) :
    (coreStep st (FullEvent.core (SeamEvent.performance eid obligor rel amount))).perf =
      st.perf ++ [performStep st.debt amount] := rfl

/-- 中文说明：宣告事件是**真恒等**（任何分量都不动）。 -/
theorem coreStep_declaratory_id {Rel : Type} (st : State Rel) (eid : String) :
    coreStep st (FullEvent.core (SeamEvent.declaratory eid)) = st := rfl

/-- 中文说明：有限折叠 `runTrace`：对列表做结构递归，逐位套用 `coreStep`。 -/
def runTrace {Rel : Type} (st₀ : State Rel) : Trace Rel → State Rel
  | [] => st₀
  | ev :: rest => runTrace (coreStep st₀ ev) rest

/-- 中文说明：空轨迹是恒等。 -/
theorem runTrace_nil {Rel : Type} (st₀ : State Rel) : runTrace st₀ ([] : Trace Rel) = st₀ := rfl

/-- 中文说明：单步展开式。 -/
theorem runTrace_cons {Rel : Type} (st₀ : State Rel) (ev : FullEvent Rel) (rest : Trace Rel) :
    runTrace st₀ (ev :: rest) = runTrace (coreStep st₀ ev) rest := rfl

/-- 中文说明：分段执行＝整体执行（列表折叠的代数事实，不是收敛陈述）。 -/
theorem runTrace_append {Rel : Type} : ∀ (st₀ : State Rel) (a b : Trace Rel),
    runTrace st₀ (a ++ b) = runTrace (runTrace st₀ a) b := by
  intro st₀ a
  induction a generalizing st₀ with
  | nil => intro st₀ b; rw [List.nil_append]
  | cons x l ih =>
      intro st₀ b
      rw [List.cons_append]
      show runTrace (coreStep st₀ x) (l ++ b) = runTrace (runTrace (coreStep st₀ x) l) b
      exact ih (coreStep st₀ x) b

/-- 中文说明：全为宣告事件的轨迹不改变状态（列表层事实，无极限、无收敛）。 -/
theorem runTrace_all_declaratory_is_noop {Rel : Type} (st₀ : State Rel) :
    ∀ (tr : Trace Rel), (∀ ev ∈ tr, ∃ eid, ev = FullEvent.core (SeamEvent.declaratory eid)) →
      runTrace st₀ tr = st₀ := by
  intro tr
  induction tr with
  | nil => intro h; rfl
  | cons a rest ih =>
      intro h
      rw [runTrace_cons]
      obtain ⟨eid, heid⟩ := h a (List.mem_cons_self _ _)
      rw [heid, coreStep_declaratory_id]
      exact ih rest (fun ev hev => h ev (List.mem_cons_of_mem a hev))

/-- 中文说明：事件 `ev` 的语义产物（S5 的 `next` 在该事件上写入的唯一记录）。给付与宣告无产物；
**域外两个构造子也无产物**——本件拒绝为它们赋导出。 -/
def recordOfEvent {Rel : Type} : FullEvent Rel → Option (FormationRecord Rel)
  | FullEvent.core (SeamEvent.formative eid rel) => some (formedRecord eid rel)
  | FullEvent.core (SeamEvent.terminating eid rel) => some (terminatedRecord eid rel)
  | FullEvent.core (SeamEvent.performance _ _ _ _) => none
  | FullEvent.core (SeamEvent.declaratory _) => none
  | FullEvent.normBackflow _ _ => none
  | FullEvent.historyRewrite _ _ => none

/-- 中文说明：有产物则前置该记录，无产物则原样返回。 -/
def appendRecord {Rel : Type} : Option (FormationRecord Rel) → Ledger Rel → Ledger Rel
  | none => fun L => L
  | some rec => fun L => rec :: L

/-- 中文说明：一条轨迹的**导出记录表**（只含域内核心裁判事件的记录）。 -/
def traceRecords {Rel : Type} : Trace Rel → Ledger Rel
  | [] => []
  | ev :: rest => appendRecord (recordOfEvent ev) (traceRecords rest)

/-- 中文说明：列表加一个元素的长度等式（本件有限性上界的算术内核）。 -/
theorem length_append_singleton_eq {α : Type} (l : List α) (x : α) :
    (l ++ [x]).length = l.length + 1 := by
  rw [List.length_append]

/-! ## Part 3 声明不变式与 (A) 前缀保全 -/

/-- 中文说明：单步守恒谓词：实付＋未偿＝该步登记的债额。 -/
def conservedStep (s : PerformanceStep) : Prop :=
  s.applied + s.outstanding = s.debt.amount

/-- 中文说明：状态良构＝履行账本里每一步都守恒。初始状态必须自带这条，本件不假设它免费。 -/
def AdmissibleState {Rel : Type} (st : State Rel) : Prop :=
  ∀ s ∈ st.perf, conservedStep s

/-- 中文说明：守恒的字段层读数。**引用** S5 的 `applied_plus_outstanding_eq_amount`
（自然数上无条件成立的 `min a p + (a ∸ p) = a`），不是本件重证。 -/
theorem performStep_conserved_here (d : Debt) (p : Nat) : conservedStep (performStep d p) := by
  show appliedAmount d.amount p + outstandingAfter d.amount p = d.amount
  exact applied_plus_outstanding_eq_amount d.amount p

/-- 中文说明：单步保持良构。**不需要**域假设：域外事件都不碰履行账本。 -/
theorem coreStep_preserves_admissible {Rel : Type} (st : State Rel) (ev : FullEvent Rel)
    (h : AdmissibleState st) : AdmissibleState (coreStep st ev) := by
  intro s hs
  cases ev with
  | core e =>
      cases e with
      | formative eid rel => exact h s hs
      | terminating eid rel => exact h s hs
      | declaratory eid => exact h s hs
      | performance eid obligor rel amount =>
          rw [coreStep_perf_performance] at hs
          rw [List.mem_append] at hs
          cases hs with
          | inl hold => exact h s hold
          | inr hnew =>
              rw [List.mem_singleton] at hnew
              subst hnew
              exact performStep_conserved_here st.debt amount
  | normBackflow eid rel => exact h s hs
  | historyRewrite eid keep => exact h s hs

/-- 中文说明：**不变式①（守恒）**沿有限轨迹在每个前缀成立。 -/
theorem conservation_along_trace {Rel : Type} :
    ∀ (st₀ : State Rel) (tr : Trace Rel),
      AdmissibleState st₀ → AdmissibleState (runTrace st₀ tr) := by
  intro st₀ tr
  induction tr generalizing st₀ with
  | nil => intro st₀ h₀; exact h₀
  | cons a rest ih =>
      intro st₀ h₀
      rw [runTrace_cons]
      exact ih (coreStep st₀ a) (coreStep_preserves_admissible st₀ a h₀)

/-- 中文说明：**不变式②（只追加）**：终态账本是初态账本的后缀扩张，历史不被涂改。 -/
def appendOnlyOf {Rel : Type} (L₀ : Ledger Rel) (st : State Rel) : Prop :=
  ∃ s, st.ledger = L₀ ++ s

/-- 中文说明：**不变式③（不遗忘）**：纯追加投影 `formsEver` 沿轨迹单调（S5 的读数）。 -/
def ideographOf {Rel : Type} [DecidableEq Rel] (L₀ : Ledger Rel) (st : State Rel) : Prop :=
  ∀ r, formsEver L₀ r → formsEver st.ledger r

/-- 中文说明：**不变式④（通道不相交）**：在任何状态上追加一个给付事件都不改 π。 -/
def channelDisjointnessAt {Rel : Type} [DecidableEq Rel] (st : State Rel) : Prop :=
  ∀ (eid obligor : String) (rel : Rel) (amount : Nat) (r : Rel),
    forms (coreStep st (FullEvent.core (SeamEvent.performance eid obligor rel amount))).ledger r ↔
      forms st.ledger r

/-- 中文说明：不变式④就是 S5 `performance_not_creation` 的逐点读数，**不是**本件新增的假设。 -/
theorem channelDisjointnessAt_any {Rel : Type} [DecidableEq Rel] (st : State Rel) :
    channelDisjointnessAt st :=
  fun eid obligor rel amount r => performance_not_creation st.ledger eid obligor rel amount r

/-- 中文说明：本件声明的四条不变式之合取。未列入的一律不算已保（见§未覆盖片段）。 -/
def invariantsHeld {Rel : Type} [DecidableEq Rel] (L₀ : Ledger Rel) (st : State Rel) : Prop :=
  AdmissibleState st ∧ appendOnlyOf L₀ st ∧ ideographOf L₀ st ∧ channelDisjointnessAt st

/-- 中文说明：域内事件的账本至多加一条记录（故"只追加"成立）。 -/
theorem coreStep_ledger_append {Rel : Type} (st : State Rel) (ev : FullEvent Rel)
    (h : domainMember fullDomain ev = true) : ∃ s, (coreStep st ev).ledger = st.ledger ++ s := by
  cases ev with
  | core e =>
      cases e with
      | formative eid rel =>
          exact ⟨[formedRecord eid rel], coreStep_ledger_formative st eid rel⟩
      | terminating eid rel =>
          exact ⟨[terminatedRecord eid rel], coreStep_ledger_terminating st eid rel⟩
      | performance eid obligor rel amount =>
          exact ⟨[], coreStep_ledger_performance st eid obligor rel amount⟩
      | declaratory eid => exact ⟨[], coreStep_ledger_declaratory st eid⟩
  | normBackflow eid rel => exact absurd h Bool.false_ne_true
  | historyRewrite eid keep => exact absurd h Bool.false_ne_true

/-- 中文说明：域内轨迹的账本**精确等式**：终态账本＝初始账本 ++ 导出记录表。
域外回流不满足它（回流写记录但无产物），故本引理真正把域假设用上。 -/
theorem runTrace_ledger_eq_append {Rel : Type} :
    ∀ (st₀ : State Rel) (tr : Trace Rel), traceInDomain fullDomain tr →
      (runTrace st₀ tr).ledger = st₀.ledger ++ traceRecords tr := by
  intro st₀ tr
  induction tr generalizing st₀ with
  | nil => intro st₀ hdom; exact (List.append_nil st₀.ledger).symm
  | cons a rest ih =>
      intro st₀ hdom
      have hrec := ih (coreStep st₀ a) (fun ev hev => hdom ev (List.mem_cons_of_mem a hev))
      rw [runTrace_cons, hrec]
      have hdomA : domainMember fullDomain a = true := hdom a (List.mem_cons_self _ _)
      cases a with
      | core e =>
          cases e with
          | formative eid rel =>
              rw [coreStep_ledger_formative]
              exact List.append_assoc st₀.ledger [formedRecord eid rel] (traceRecords rest)
          | terminating eid rel =>
              rw [coreStep_ledger_terminating]
              exact List.append_assoc st₀.ledger [terminatedRecord eid rel] (traceRecords rest)
          | performance eid obligor rel amount => rw [coreStep_ledger_performance]
          | declaratory eid => rw [coreStep_ledger_declaratory]
      | normBackflow eid rel => exact absurd hdomA Bool.false_ne_true
      | historyRewrite eid keep => exact absurd hdomA Bool.false_ne_true

/-- 中文说明：**(A) 主定理**：对任何声明域、任何落在域内的轨迹，**每一个前缀**都满足本件声明的
四条不变式。前缀以 `++` 分拆表示（与 `take` 前缀等价，见 `finite_trace_invariants_at_take_prefix`）。
①引用 S5 `applied_plus_outstanding_eq_amount`、③引用 S5 `append_is_ideographic`、
④引用 S5 `performance_not_creation`——都是引用而非重证。π 的单调性、任何收敛、任何裁判结论
都不在本定理内（§未覆盖片段第 6 条）。 -/
theorem finite_trace_preserves_legal_invariants
    {Rel : Type} [DecidableEq Rel] (dom : DeclaredEventDomain) (st₀ : State Rel) (tr : Trace Rel)
    (h₀ : AdmissibleState st₀) (hdom : traceInDomain dom tr) :
    ∀ pre : Trace Rel, (∃ post, tr = pre ++ post) →
      invariantsHeld st₀.ledger (runTrace st₀ pre) := by
  intro pre hpre
  have hfull : traceInDomain fullDomain pre := by
    intro ev hev
    exact domainMember_full_of dom ev
      (hdom ev (by rw [← hpre]; rw [List.mem_append]; exact Or.inl hev))
  have heq := runTrace_ledger_eq_append st₀ pre hfull
  unfold invariantsHeld
  refine ⟨conservation_along_trace st₀ pre h₀, ⟨traceRecords pre, heq⟩, ?_,
    channelDisjointnessAt_any _⟩
  intro r hr
  rw [heq]
  exact append_is_ideographic st₀.ledger (traceRecords pre) r hr

/-- 中文说明：`take` 读数下的同一前缀陈述（前缀＝`tr.take i`）。 -/
theorem finite_trace_invariants_at_take_prefix
    {Rel : Type} [DecidableEq Rel] (dom : DeclaredEventDomain) (st₀ : State Rel) (tr : Trace Rel)
    (h₀ : AdmissibleState st₀) (hdom : traceInDomain dom tr) (i : Nat) :
    invariantsHeld st₀.ledger (runTrace st₀ (tr.take i)) :=
  finite_trace_preserves_legal_invariants dom st₀ tr h₀ hdom (tr.take i)
    ⟨tr.drop i, (List.take_append_drop i tr).symm⟩

/-! ## Part 4 (C) 事件域交接与域相对性 -/

/-- 中文说明：非裁判片段的单步 π 不变性（引 S5 `performance_not_creation`）。 -/
theorem performance_step_preserves_forms {Rel : Type} [DecidableEq Rel]
    (st : State Rel) (eid obligor : String) (rel : Rel) (amount : Nat) (r : Rel) :
    forms (coreStep st (FullEvent.core (SeamEvent.performance eid obligor rel amount))).ledger r ↔
      forms st.ledger r :=
  performance_not_creation st.ledger eid obligor rel amount r

/-- 中文说明：宣告片段的单步 π 不变性（引 S5 `next_declaratory_is_identity`）。 -/
theorem declaratory_step_preserves_forms {Rel : Type} [DecidableEq Rel]
    (st : State Rel) (eid : String) (r : Rel) :
    forms (coreStep st (FullEvent.core (SeamEvent.declaratory eid))).ledger r ↔
      forms st.ledger r := by
  show forms (next st.ledger (SeamEvent.declaratory eid)) r ↔ forms st.ledger r
  rw [next_declaratory_is_identity]
  exact Iff.rfl

/-- 中文说明：**域内稳定定理**：只在 S5 非裁判域（给付＋宣告）上折叠的任意轨迹，π 对每个关系
取值一字不动。这里的域是 `nonAdjudicativeDomain` 而不是 `fullDomain`——换成更大的域该定理即为假
（`pi_stability_fails_outside_domain`）；两个裁判类别与两个域外构造子都在定理之外，
其合法性分别属 S5 的裁判片段、S7 与 S2，本件不代答。 -/
theorem nonadjudicative_trace_stabilizes_projection {Rel : Type} [DecidableEq Rel]
    (st₀ : State Rel) (r : Rel) :
    ∀ (tr : Trace Rel), traceInDomain nonAdjudicativeDomain tr →
      forms (runTrace st₀ tr).ledger r ↔ forms st₀.ledger r := by
  intro tr
  induction tr generalizing st₀ with
  | nil => intro st₀ hdom; exact Iff.rfl
  | cons a rest ih =>
      intro st₀ hdom
      rw [runTrace_cons]
      have hd : domainMember nonAdjudicativeDomain a = true := hdom a (List.mem_cons_self _ _)
      have hrest : traceInDomain nonAdjudicativeDomain rest :=
        fun ev hev => hdom ev (List.mem_cons_of_mem a hev)
      cases a with
      | core e =>
          cases e with
          | formative eid rel => exact absurd hd (by decide)
          | terminating eid rel => exact absurd hd (by decide)
          | performance eid obligor rel amount =>
              exact Iff.trans (ih (coreStep st₀ a) hrest)
                (performance_step_preserves_forms st₀ eid obligor rel amount r)
          | declaratory eid =>
              exact Iff.trans (ih (coreStep st₀ a) hrest)
                (declaratory_step_preserves_forms st₀ eid r)
      | normBackflow eid rel => exact absurd hd (by decide)
      | historyRewrite eid keep => exact absurd hd (by decide)

/-- 中文说明：**交接假设**。域外事件的法律语义由别的缝合件交出，本件把它当**参数**使用；
三个字段就是本件唯一依赖的内容（只追加、不碰履行账本、不碰回执堆）。`step` 的正当性、
回流是否有权终止关系、终局策略内容——全部属 S7 与 S2，本件不证也不假设（§未覆盖片段 1、2）。 -/
structure OutOfDomainSemantics (Rel : Type) where
  step : State Rel → FullEvent Rel → State Rel
  appendsOnly : ∀ st ev, ∃ s, (step st ev).ledger = st.ledger ++ s
  preservesPerf : ∀ st ev, (step st ev).perf = st.perf
  preservesPile : ∀ st ev, (step st ev).pile = st.pile

/-- 中文说明：域内用 `coreStep`，域外用交接假设的语义。 -/
def extStep {Rel : Type} (br : OutOfDomainSemantics Rel) (st : State Rel)
    (ev : FullEvent Rel) : State Rel :=
  match domainMember fullDomain ev with
  | true => coreStep st ev
  | false => br.step st ev

/-- 中文说明：域内事件上外推语义退回核心语义。 -/
theorem extStep_in {Rel : Type} (br : OutOfDomainSemantics Rel) (st : State Rel)
    (ev : FullEvent Rel) (h : domainMember fullDomain ev = true) :
    extStep br st ev = coreStep st ev := by
  unfold extStep
  rw [h]

/-- 中文说明：域外事件上外推语义取交接假设的语义。 -/
theorem extStep_out {Rel : Type} (br : OutOfDomainSemantics Rel) (st : State Rel)
    (ev : FullEvent Rel) (h : domainMember fullDomain ev = false) :
    extStep br st ev = br.step st ev := by
  unfold extStep
  rw [h]

/-- 中文说明：带域外语义的有限折叠。 -/
def runTraceExt {Rel : Type} (br : OutOfDomainSemantics Rel) (st₀ : State Rel) :
    Trace Rel → State Rel
  | [] => st₀
  | ev :: rest => runTraceExt br (extStep br st₀ ev) rest

/-- 中文说明：`runTraceExt` 的单步展开式。 -/
theorem runTraceExt_cons {Rel : Type} (br : OutOfDomainSemantics Rel) (st₀ : State Rel)
    (ev : FullEvent Rel) (rest : Trace Rel) :
    runTraceExt br st₀ (ev :: rest) = runTraceExt br (extStep br st₀ ev) rest := rfl

/-- 中文说明：单步良构对任意域外语义都保持（守恒不变）。 -/
theorem extStep_preserves_admissible {Rel : Type} (br : OutOfDomainSemantics Rel)
    (st : State Rel) (ev : FullEvent Rel) (h : AdmissibleState st) :
    AdmissibleState (extStep br st ev) := by
  intro s hs
  cases domainMember_dichotomy fullDomain ev with
  | inl hd =>
      rw [extStep_in br st ev hd] at hs
      exact coreStep_preserves_admissible st ev h s hs
  | inr hd =>
      rw [extStep_out br st ev hd] at hs
      rw [br.preservesPerf st ev] at hs
      exact h s hs

/-- 中文说明：守恒沿外推轨迹在每个前缀成立（对任意域外语义）。 -/
theorem extConservationAlong {Rel : Type} (br : OutOfDomainSemantics Rel) :
    ∀ (st₀ : State Rel) (tr : Trace Rel),
      AdmissibleState st₀ → AdmissibleState (runTraceExt br st₀ tr) := by
  intro st₀ tr
  induction tr generalizing st₀ with
  | nil => intro st₀ h₀; exact h₀
  | cons a rest ih =>
      intro st₀ h₀
      rw [runTraceExt_cons]
      exact ih (extStep br st₀ a) (extStep_preserves_admissible br st₀ a h₀)

/-- 中文说明：只要域外语义**只追加**，账本就仍只是初态账本的后缀扩张（不依赖其法律内容）。 -/
theorem runTraceExt_ledger_append {Rel : Type} (br : OutOfDomainSemantics Rel) :
    ∀ (st₀ : State Rel) (tr : Trace Rel), ∃ s, (runTraceExt br st₀ tr).ledger = st₀.ledger ++ s := by
  intro st₀ tr
  induction tr generalizing st₀ with
  | nil => intro st₀; exact ⟨[], (List.append_nil st₀.ledger).symm⟩
  | cons a rest ih =>
      intro st₀
      obtain ⟨s1, hs1⟩ := ih (extStep br st₀ a)
      have hstep : ∃ s, (extStep br st₀ a).ledger = st₀.ledger ++ s := by
        cases domainMember_dichotomy fullDomain a with
        | inl hd => rw [extStep_in br st₀ a hd]; exact coreStep_ledger_append st₀ a hd
        | inr hd => rw [extStep_out br st₀ a hd]; exact br.appendsOnly st₀ a
      obtain ⟨s0, hs0⟩ := hstep
      rw [runTraceExt_cons, hs1, hs0]
      exact ⟨s0 ++ s1, List.append_assoc st₀.ledger s0 s1⟩

/-- 中文说明：**稳健性定理**：簿记四不变式对**任何**只追加的域外语义都成立。
这把"本件的保全结论对 S7／S2 的具体内容不敏感"做成正陈述；反过来，导出性与 π 稳定性
**不**稳健（`backflow_admitted_without_derivation`、`pi_stability_fails_outside_domain`）。 -/
theorem invariants_hold_under_any_out_of_domain {Rel : Type} [DecidableEq Rel]
    (br : OutOfDomainSemantics Rel) (st₀ : State Rel) (tr : Trace Rel)
    (h₀ : AdmissibleState st₀) : invariantsHeld st₀.ledger (runTraceExt br st₀ tr) := by
  obtain ⟨s, hs⟩ := runTraceExt_ledger_append br st₀ tr
  unfold invariantsHeld
  refine ⟨extConservationAlong br st₀ tr h₀, ⟨s, hs⟩, ?_, channelDisjointnessAt_any _⟩
  intro r hr
  rw [hs]
  exact append_is_ideographic st₀.ledger s r hr

/-- 中文说明：域内轨迹上外推语义与核心语义**逐字相同**（故 `fullDomain` 是本件的真正落点）。 -/
theorem runTrace_eq_runTraceExt {Rel : Type} (br : OutOfDomainSemantics Rel) :
    ∀ (st₀ : State Rel) (tr : Trace Rel), traceInDomain fullDomain tr →
      runTraceExt br st₀ tr = runTrace st₀ tr := by
  intro st₀ tr
  induction tr generalizing st₀ with
  | nil => intro st₀ hdom; rfl
  | cons a rest ih =>
      intro st₀ hdom
      rw [runTraceExt_cons, runTrace_cons,
        ih (coreStep st₀ a) (fun ev hev => hdom ev (List.mem_cons_of_mem a hev))]
      congr
      exact extStep_in br st₀ a (hdom a (List.mem_cons_self _ _))

/-- 中文说明：本件明确排除的域外构造子清单（交接给 S7 与 S2，不在本件判定范围）。 -/
def outOfDomainTags : List String := ["normBackflow -> S7", "historyRewrite -> S2"]

/-! ## Part 5 见证状态与域外失效 -/

/-- 中文说明：空账本起点（回执导出定理要求它，见§未覆盖片段第 5 条）。 -/
def st₀Empty : State Relation :=
  { ledger := [], perf := [], debt := debtDemo, pile := [] }

/-- 中文说明：已有一条成立记录的起点（"J1 成立 R-D"）。 -/
def st₀Seeded : State Relation :=
  { st₀Empty with ledger := [formedRecord "J1" relationDemo] }

/-- 中文说明：单条给付轨迹：债 10、已为给付 10（与 S5 `register_p_side` 同额读数）。 -/
def performTraceDemo : Trace Relation :=
  [FullEvent.core (SeamEvent.performance "P1" "甲" relationDemo 10)]

/-- 中文说明：单条成立轨迹。 -/
def formedTraceDemo : Trace Relation :=
  [FullEvent.core (SeamEvent.formative "J1" relationDemo)]

/-- 中文说明：域外回流轨迹。 -/
def traceBackflowDemo : Trace Relation := [FullEvent.normBackflow "B1" relationDemo]

/-- 中文说明：域外涂改轨迹（把账本截断到 0 条）。 -/
def rewriteTraceDemo : Trace Relation := [FullEvent.historyRewrite "X1" 0]

/-- 中文说明：成立之后再来一条域外回流。 -/
def backflowAfterFormed : Trace Relation := formedTraceDemo ++ traceBackflowDemo

/-- 中文说明：`st₀Empty` 是良构起点（履行账本为空）。 -/
theorem admissibleState_st₀Empty : AdmissibleState st₀Empty :=
  fun s hs => absurd hs (List.not_mem_nil s)

/-- 中文说明：`performTraceDemo` 落在 `fullDomain` 内。 -/
theorem performTraceDemo_inDomain : traceInDomain fullDomain performTraceDemo := by
  intro ev hev
  rw [List.mem_singleton] at hev
  subst hev
  rfl

/-- 中文说明：回流轨迹不在声明域内（回流恒被排除）。 -/
theorem traceBackflowDemo_notInDomain : ¬ traceInDomain fullDomain traceBackflowDemo :=
  fun h => Bool.false_ne_true (h (FullEvent.normBackflow "B1" relationDemo)
    (List.mem_cons_self _ _))

/-- 中文说明：涂改轨迹不在声明域内。 -/
theorem rewriteTraceDemo_notInDomain : ¬ traceInDomain fullDomain rewriteTraceDemo :=
  fun h => Bool.false_ne_true (h (FullEvent.historyRewrite "X1" 0)
    (List.mem_cons_self _ _))

/-- 中文说明：涂改一步的账本读数：初始唯一的那条记录被删光。 -/
theorem runTrace_rewrite_demo_ledger :
    (runTrace st₀Seeded rewriteTraceDemo).ledger = ([] : Ledger Relation) := rfl

/-- 中文说明：**域假设不是装饰（其一）**：域外涂改使"只追加"失效。 -/
theorem historyRewrite_breaks_appendOnly :
    ¬ appendOnlyOf st₀Seeded.ledger (runTrace st₀Seeded rewriteTraceDemo) := by
  unfold appendOnlyOf
  rintro ⟨s, hs⟩
  rw [runTrace_rewrite_demo_ledger] at hs
  have hlen := congrArg List.length hs
  have h1 : List.length st₀Seeded.ledger = 1 := rfl
  rw [List.length_nil, List.length_append, h1] at hlen
  omega

/-- 中文说明：**域假设不是装饰（其二）**：域外涂改使"不遗忘"失效——`formsEver` 从真被改成假。
这正是 S5 把 `append_is_ideographic` 挂在纯追加投影、而不是挂在 π 上的原因。 -/
theorem historyRewrite_breaks_ideograph :
    ¬ ideographOf st₀Seeded.ledger (runTrace st₀Seeded rewriteTraceDemo) := by
  intro h
  have h2 : ¬ formsEver ([] : Ledger Relation) relationDemo := by decide
  have h3 := h relationDemo (by decide : formsEver st₀Seeded.ledger relationDemo)
  rw [runTrace_rewrite_demo_ledger] at h3
  exact h2 h3

/-- 中文说明：**域假设不是装饰（其三）**：域外回流把 π 从真翻成假，
故 Part 4 的 π 稳定定理只对 `nonAdjudicativeDomain` 成立，不能推广。 -/
theorem pi_stability_fails_outside_domain :
    forms (runTrace st₀Empty formedTraceDemo).ledger relationDemo ∧
      ¬ forms (runTrace st₀Empty backflowAfterFormed).ledger relationDemo :=
  ⟨by decide, by decide⟩

/-! ## Part 6 (B) 回执：果不是因 -/

/-- 中文说明：回执的记录副本（S5 的 `FormationRecord`）。 -/
def receiptRecord {Rel : Type} (rc : Receipt Rel) : FormationRecord Rel :=
  { eventId := rc.ref, kind := rc.kind, rel := rc.rel }

/-- 中文说明：**记账准入**＝记录确在账本 ∧ 层级足以签发事实确认书（`JurisLean.canIssue`）。
两个条件都只是对输入数据的检查；本件不判定它们是否代表真实世界的正当性。 -/
def Admitted {Rel : Type} (st : State Rel) (rc : Receipt Rel) : Prop :=
  receiptRecord rc ∈ st.ledger ∧ canIssue rc.level ArtifactKind.factAttestation

/-- 中文说明：**语义导出**＝轨迹里存在一个事件，其语义产物正是该回执的记录。
域外回流与涂改都无产物，故"账本里有"绝不蕴含"有导出"。 -/
def HasDerivation {Rel : Type} (tr : Trace Rel) (rc : Receipt Rel) : Prop :=
  ∃ ev, ev ∈ tr ∧ recordOfEvent ev = some (receiptRecord rc)

/-- 中文说明：账本承认的记录必来自轨迹里的某个事件（导出方向的机器引理）。 -/
theorem mem_traceRecords_has_event {Rel : Type} :
    ∀ (tr : Trace Rel) (rec : FormationRecord Rel), rec ∈ traceRecords tr →
      ∃ ev, ev ∈ tr ∧ recordOfEvent ev = some rec := by
  intro tr
  induction tr with
  | nil =>
      intro rec h
      exact absurd h (List.not_mem_nil rec)
  | cons a rest ih =>
      intro rec h
      cases a with
      | core e =>
          cases e with
          | formative eid rel =>
              have h' : rec ∈ formedRecord eid rel :: traceRecords rest := h
              rw [List.mem_cons] at h'
              cases h' with
              | inl heq =>
                  exact ⟨FullEvent.core (SeamEvent.formative eid rel),
                    List.mem_cons_self _ _, congrArg some heq⟩
              | inr hrest =>
                  obtain ⟨ev, hev, heq⟩ := ih rec hrest
                  exact ⟨ev, List.mem_cons_of_mem a hev, heq⟩
          | terminating eid rel =>
              have h' : rec ∈ terminatedRecord eid rel :: traceRecords rest := h
              rw [List.mem_cons] at h'
              cases h' with
              | inl heq =>
                  exact ⟨FullEvent.core (SeamEvent.terminating eid rel),
                    List.mem_cons_self _ _, congrArg some heq⟩
              | inr hrest =>
                  obtain ⟨ev, hev, heq⟩ := ih rec hrest
                  exact ⟨ev, List.mem_cons_of_mem a hev, heq⟩
          | performance eid obligor rel amount =>
              have h' : rec ∈ traceRecords rest := h
              obtain ⟨ev, hev, heq⟩ := ih rec h'
              exact ⟨ev, List.mem_cons_of_mem a hev, heq⟩
          | declaratory eid =>
              have h' : rec ∈ traceRecords rest := h
              obtain ⟨ev, hev, heq⟩ := ih rec h'
              exact ⟨ev, List.mem_cons_of_mem a hev, heq⟩
      | normBackflow eid rel =>
          have h' : rec ∈ traceRecords rest := h
          obtain ⟨ev, hev, heq⟩ := ih rec h'
          exact ⟨ev, List.mem_cons_of_mem a hev, heq⟩
      | historyRewrite eid keep =>
          have h' : rec ∈ traceRecords rest := h
          obtain ⟨ev, hev, heq⟩ := ih rec h'
          exact ⟨ev, List.mem_cons_of_mem a hev, heq⟩

/-- 中文说明：**(B) 主定理**：空账本起步、只在声明域内折叠的轨迹上，任何被记账准入的回执都带
语义导出。法律读法：回执是**导出的果**。前提 `st₀.ledger = []` 不是技术装饰——
初始账本里既有的记录在本件内没有导出（§未覆盖片段第 5 条）。 -/
theorem receipt_has_semantic_derivation {Rel : Type} [DecidableEq Rel]
    (st₀ : State Rel) (tr : Trace Rel) (rc : Receipt Rel)
    (hempty : st₀.ledger = []) (hdom : traceInDomain fullDomain tr)
    (hadm : Admitted (runTrace st₀ tr) rc) : HasDerivation tr rc := by
  obtain ⟨hmem, _hlvl⟩ := hadm
  rw [runTrace_ledger_eq_append st₀ tr hdom, hempty, List.nil_append] at hmem
  obtain ⟨ev, hev, heq⟩ := mem_traceRecords_has_event tr (receiptRecord rc) hmem
  exact ⟨ev, hev, heq⟩

/-- 中文说明：**声明片段**：空账本起步＋落在 `fullDomain` 内。本件的回执导出定理只在此片段上陈述。 -/
def declaredFragment {Rel : Type} (st₀ : State Rel) (tr : Trace Rel) : Prop :=
  st₀.ledger = [] ∧ traceInDomain fullDomain tr

/-- 中文说明：片段版本的"准入 ⇒ 导出"。 -/
theorem admitted_receipt_has_derivation {Rel : Type} [DecidableEq Rel]
    (st₀ : State Rel) (tr : Trace Rel) (rc : Receipt Rel)
    (hfr : declaredFragment st₀ tr) (hadm : Admitted (runTrace st₀ tr) rc) :
    HasDerivation tr rc :=
  receipt_has_semantic_derivation st₀ tr rc hfr.1 hfr.2 hadm

/-- 中文说明：**回流回执**：账本承认它（记录确在账本、层级最高），但它没有导出。 -/
def rcBackflow : Receipt Relation :=
  { ref := "B1", rel := relationDemo, kind := RecordKind.terminated,
    level := AuthorityLevel.admittedFormalInput }

/-- 中文说明：回流记录确实进了终态账本。 -/
theorem backflow_record_in_ledger :
    receiptRecord rcBackflow ∈ (runTrace st₀Empty traceBackflowDemo).ledger := by
  show terminatedRecord "B1" relationDemo ∈
    (([] : Ledger Relation) ++ [terminatedRecord "B1" relationDemo])
  rw [List.nil_append]
  exact List.mem_cons_self _ _

/-- 中文说明：回流回执的层级足够（只看层级格，不看正当性）。 -/
theorem rcBackflow_level_ok : canIssue rcBackflow.level ArtifactKind.factAttestation := by
  show canIssue AuthorityLevel.admittedFormalInput ArtifactKind.factAttestation
  decide

/-- 中文说明：**反向不可得（具体见证）**：域外回流的回执被记账准入，却没有语义导出。
故"账本承认"与"已经导出"是两件事；把前者当后者用正是 P-123 反对的读法。 -/
theorem backflow_admitted_without_derivation :
    Admitted (runTrace st₀Empty traceBackflowDemo) rcBackflow ∧
      ¬ HasDerivation traceBackflowDemo rcBackflow := by
  refine ⟨⟨backflow_record_in_ledger, rcBackflow_level_ok⟩, ?_⟩
  intro h
  obtain ⟨ev, hev, heq⟩ := h
  rw [List.mem_singleton] at hev
  rw [← hev] at heq
  exact absurd heq (by decide)

/-- 中文说明：层级不足的回执形状：proposal 层级自报、且记录**确实**已在账本里。 -/
def rcFormedSeeded : Receipt Relation :=
  { ref := "J1", rel := relationDemo, kind := RecordKind.formed,
    level := AuthorityLevel.untrustedProposal }

/-- 中文说明：该回执的记录就是 seeded 账本里的那条。 -/
theorem rcFormedSeeded_record_eq :
    receiptRecord rcFormedSeeded = formedRecord "J1" relationDemo := rfl

/-- 中文说明：该记录确在账本里。 -/
theorem rcFormedSeeded_record_is_in_ledger :
    receiptRecord rcFormedSeeded ∈ st₀Seeded.ledger := by
  show receiptRecord rcFormedSeeded ∈ formedRecord "J1" relationDemo :: ([] : Ledger Relation)
  rw [List.mem_cons]
  exact Or.inl rcFormedSeeded_record_eq

/-- 中文说明：proposal 层级的回执形状在任何状态下都不被准入。
引 ReceiptAuthority 的 `proposal_cannot_issue_attestation`。 -/
theorem proposal_shaped_copy_never_admitted {Rel : Type} (st : State Rel) (rc : Receipt Rel)
    (hlvl : rc.level = AuthorityLevel.untrustedProposal) : ¬ Admitted st rc := by
  intro h
  obtain ⟨_h1, h2⟩ := h
  rw [hlvl] at h2
  exact proposal_cannot_issue_attestation h2

/-- 中文说明：**记账匹配本身不是准入**：记录已在账本、层级却是 proposal ⇒ 仍不被准入。 -/
theorem seeded_proposal_copy_not_admitted : ¬ Admitted st₀Seeded rcFormedSeeded :=
  proposal_shaped_copy_never_admitted st₀Seeded rcFormedSeeded rfl

/-- 中文说明：human-reviewed 候选仍不是正式输入（引 `human_review_not_formal_input`）。 -/
theorem human_reviewed_copy_never_admitted {Rel : Type} (st : State Rel) (rc : Receipt Rel)
    (hlvl : rc.level = AuthorityLevel.humanReviewedCandidate) : ¬ Admitted st rc := by
  intro h
  obtain ⟨_h1, h2⟩ := h
  rw [hlvl] at h2
  exact human_review_not_formal_input
    (by simpa [canIssue, requiredLevel, authorityRank] using h2)

/-- 中文说明：权威链严格有序（引 `authority_strictly_ordered`）：本件据此说明层级只能由
外部凭证逐级抬升，不能由簿记抬升。 -/
theorem level_chain_is_strict :
    authorityRank AuthorityLevel.untrustedProposal <
      authorityRank AuthorityLevel.admittedFormalInput :=
  Nat.lt_trans authority_strictly_ordered.1
    (Nat.lt_trans authority_strictly_ordered.2.1 authority_strictly_ordered.2.2)

/-- 中文说明：同一低层级的任意重复堆叠都到不了确认书所需层级。
引 `consensus_does_not_escalate` 与 `authority_strictly_ordered`。 -/
theorem repeated_proposal_never_reaches_attestation_rank (n : Nat) :
    consensusRank (List.replicate n AuthorityLevel.untrustedProposal) <
      authorityRank (requiredLevel ArtifactKind.factAttestation) := by
  show consensusRank (List.replicate n AuthorityLevel.untrustedProposal) <
    authorityRank AuthorityLevel.admittedFormalInput
  have h1 := consensus_does_not_escalate AuthorityLevel.untrustedProposal n
  obtain ⟨h2, h3, h4⟩ := authority_strictly_ordered
  omega

/-- 中文说明：跳级晋级凭证无效（引 `skipping_receipt_invalid`）：本件的准入不读凭证，
故跳级不可能靠记账混进来。 -/
theorem skipping_authority_receipt_not_valid (r : AuthorityReceipt)
    (h : authorityRank r.toLevel > authorityRank r.fromLevel + 1) : ¬ receiptValid r :=
  skipping_receipt_invalid (Nat.ne_of_gt h)

/-- 中文说明：proposal 层级既发不出证书也发不出 DecisionStatus
（引 `proposal_cannot_issue_certificate`、`proposal_cannot_issue_decision_status`）。 -/
theorem proposal_issues_neither_certificate_nor_status :
    ¬ canIssue AuthorityLevel.untrustedProposal ArtifactKind.certificate ∧
      ¬ canIssue AuthorityLevel.untrustedProposal ArtifactKind.decisionStatus :=
  ⟨proposal_cannot_issue_certificate, proposal_cannot_issue_decision_status⟩

/-- 中文说明：回执堆沿轨迹是常量。 -/
theorem runTrace_pile_unchanged {Rel : Type} :
    ∀ (st₀ : State Rel) (tr : Trace Rel), (runTrace st₀ tr).pile = st₀.pile := by
  intro st₀ tr
  induction tr generalizing st₀ with
  | nil => intro st₀; rfl
  | cons a rest ih =>
      intro st₀
      rw [runTrace_cons, ih (coreStep st₀ a), coreStep_pile_unchanged st₀ a]

/-- 中文说明：**P-123 口号的正定理形式**：回执堆不进入任何转移（果不是因），
且低层级回执永不被准入。两条一起把"账本里有一叠回执"排除出推导依据之外。 -/
theorem receipt_ledger_is_fruit_not_warrant {Rel : Type} (st₀ : State Rel) (tr : Trace Rel) :
    (runTrace st₀ tr).pile = st₀.pile ∧
      ∀ rc : Receipt Rel, rc.level = AuthorityLevel.untrustedProposal → ¬ Admitted st₀ rc :=
  ⟨runTrace_pile_unchanged st₀ tr,
    fun rc hlvl => proposal_shaped_copy_never_admitted st₀ rc hlvl⟩

/-! ## Part 7 (D) 闭包限度 -/

/-- 中文说明：本件自有的裁判形状四态。**不** import S2：与 S2 的 `DecisionStatus` 之间
没有桥接定理（§未覆盖片段第 2 条）。 -/
inductive OutcomeShape
  | decidedAdjudicated
  | undecidedPerformance
  | undecidedEmpty
  | outOfModel
  deriving DecidableEq, Repr

/-- 中文说明：账本里是否存在成立记录（可计算谓词）。 -/
def hasFormationRecord {Rel : Type} : Ledger Rel → Bool
  | [] => false
  | rec :: rest => rec.kind == RecordKind.formed || hasFormationRecord rest

/-- 中文说明：状态到形状的读数：只读关系账本与履行账本，**不读回执堆**（回执是果）。 -/
def outcomeShape {Rel : Type} [DecidableEq Rel] (st : State Rel) : OutcomeShape :=
  if st.ledger = [] then
    if st.perf = [] then OutcomeShape.undecidedEmpty else OutcomeShape.undecidedPerformance
  else if hasFormationRecord st.ledger then OutcomeShape.decidedAdjudicated
    else OutcomeShape.outOfModel

/-- 中文说明：三个非裁判形状都不等于裁判形状。 -/
theorem undecided_shapes_are_not_decided :
    OutcomeShape.undecidedPerformance ≠ OutcomeShape.decidedAdjudicated ∧
      OutcomeShape.undecidedEmpty ≠ OutcomeShape.decidedAdjudicated ∧
        OutcomeShape.outOfModel ≠ OutcomeShape.decidedAdjudicated :=
  ⟨by decide, by decide, by decide⟩

/-- 中文说明：全额履行轨迹的终态形状是 `undecidedPerformance`（闭式计算）。 -/
theorem performTraceDemo_shape_undecided :
    outcomeShape (runTrace st₀Empty performTraceDemo) =
      OutcomeShape.undecidedPerformance := by
  decide

/-- 中文说明：履行通道确实入了账，并按 S5 的守恒式清偿（债 10、未偿 0）。 -/
theorem performTraceDemo_conserves :
    (runTrace st₀Empty performTraceDemo).perf ≠ [] ∧
      ∀ s ∈ (runTrace st₀Empty performTraceDemo).perf, conservedStep s ∧ s.outstanding = 0 := by
  refine ⟨by decide, ?_⟩
  intro s hs
  rw [runTrace_cons, coreStep_perf_performance] at hs
  rw [List.mem_append] at hs
  cases hs with
  | inl hold => exact absurd hold (List.not_mem_nil s)
  | inr hnew =>
      rw [List.mem_singleton] at hnew
      subst hnew
      exact ⟨performStep_conserved_here debtDemo 10, by decide⟩

/-- 中文说明：容易被误读成"闭环已经保证裁判"的**全称主张**。把它写成 Prop，才能证伪它。 -/
def closure_uniform_claim : Prop :=
  ∀ (tr : Trace Relation), traceInDomain fullDomain tr → AdmissibleState st₀Empty →
    (∀ pre : Trace Relation, (∃ post, tr = pre ++ post) →
        invariantsHeld ([] : Ledger Relation) (runTrace st₀Empty pre)) →
      outcomeShape (runTrace st₀Empty tr) = OutcomeShape.decidedAdjudicated

/-- 中文说明：**(D) 诚实门**：闭环**不**是本件声明的全称主张。见证就是那条每一步都合法、
债务按守恒式全额清偿、终态形状却是 `undecidedPerformance` 的轨迹。本件的保全与守恒对
"真实案件／真实法条／循环收敛"不给任何结论。 -/
theorem closure_is_not_uniform_claim : ¬ closure_uniform_claim := by
  intro h
  have hspec := h performTraceDemo performTraceDemo_inDomain admissibleState_st₀Empty
    (finite_trace_preserves_legal_invariants fullDomain st₀Empty performTraceDemo
      admissibleState_st₀Empty performTraceDemo_inDomain)
  rw [performTraceDemo_shape_undecided] at hspec
  exact absurd hspec (by decide)

/-- 中文说明：空账本起步的 `Unit` 状态（`Unit` 不含任何法律内容）。 -/
def st₀Unit : State Unit :=
  { ledger := [], perf := [], debt := debtDemo, pile := [] }

/-- 中文说明：`Unit` 上的给付轨迹（把关系对象换成"无内容的单位值"）。 -/
def performTraceUnit : Trace Unit :=
  [FullEvent.core (SeamEvent.performance "P1" "甲" () 10)]

/-- 中文说明：闭环陈述**不含法律内容**的正面见证：同一条前缀保全定理在类型 `Unit` 上逐字成立。
故"每一步合法"只识别簿记，不识别案件、不识别法条。 -/
theorem preservation_over_unit_type (pre : Trace Unit)
    (hpre : ∃ post, performTraceUnit = pre ++ post) :
    invariantsHeld ([] : Ledger Unit) (runTrace st₀Unit pre) :=
  finite_trace_preserves_legal_invariants fullDomain st₀Unit performTraceUnit
    (fun s hs => absurd hs (List.not_mem_nil s))
    (fun ev hev => by
      rw [List.mem_singleton] at hev
      subst hev
      rfl) pre hpre

/-- 中文说明：本件不给收敛：形成—终止交替让 π 来回摆动（闭式见证）。
任何"循环跑到不动点"的读法都在本件之外。 -/
theorem pi_oscillates_witness :
    forms (runTrace st₀Empty formedTraceDemo).ledger relationDemo ∧
      ¬ forms (runTrace st₀Empty
        (formedTraceDemo ++ [FullEvent.core (SeamEvent.terminating "J2" relationDemo)])).ledger
          relationDemo ∧
      forms (runTrace st₀Empty
        (formedTraceDemo ++ [FullEvent.core (SeamEvent.terminating "J2" relationDemo),
          FullEvent.core (SeamEvent.formative "J3" relationDemo)])).ledger relationDemo :=
  ⟨by decide, by decide, by decide⟩

/-- 中文说明：**域相对性的总结陈述**：把域假设去掉，只追加、不遗忘与导出性都真的失效。 -/
theorem preservation_is_domain_relative :
    ¬ traceInDomain fullDomain rewriteTraceDemo ∧
      ¬ appendOnlyOf st₀Seeded.ledger (runTrace st₀Seeded rewriteTraceDemo) ∧
        ¬ ideographOf st₀Seeded.ledger (runTrace st₀Seeded rewriteTraceDemo) ∧
          ¬ traceInDomain fullDomain traceBackflowDemo ∧
            Admitted (runTrace st₀Empty traceBackflowDemo) rcBackflow ∧
              ¬ HasDerivation traceBackflowDemo rcBackflow :=
  ⟨rewriteTraceDemo_notInDomain, historyRewrite_breaks_appendOnly,
    historyRewrite_breaks_ideograph, traceBackflowDemo_notInDomain,
    backflow_admitted_without_derivation.1, backflow_admitted_without_derivation.2⟩

/-- 中文说明：**域外语义的具体见证**：把回流解释成"追加一条终止记录"。它满足交接假设的三个字段，
因此簿记不变式全部保住；但它没有语义产物，所以回执导出性失效。 -/
def backflowSemantics : OutOfDomainSemantics Relation where
  step st ev := { st with ledger := st.ledger ++ [terminatedRecord "BACKFLOW" relationDemo] }
  appendsOnly := fun st ev => ⟨[terminatedRecord "BACKFLOW" relationDemo], rfl⟩
  preservesPerf := fun _ _ => rfl
  preservesPile := fun _ _ => rfl

/-- 中文说明：该域外语义下不变式仍成立（把 `invariants_hold_under_any_out_of_domain` 落地）。 -/
theorem seeded_invariants_hold_under_backflow_semantics :
    invariantsHeld st₀Seeded.ledger
      (runTraceExt backflowSemantics st₀Seeded traceBackflowDemo) :=
  invariants_hold_under_any_out_of_domain backflowSemantics st₀Seeded traceBackflowDemo
    admissibleState_st₀Empty

/-! ## Part 8 (E) 有限性上界 -/

/-- 中文说明：截断不会把列表变长。 -/
theorem length_take_le {α : Type} : ∀ (l : List α) (k : Nat), (l.take k).length ≤ l.length := by
  intro l
  induction l with
  | nil => intro k; exact Nat.le_refl _
  | cons a rest ih =>
      intro k
      cases k with
      | zero => exact Nat.zero_le _
      | succ k' =>
          show (a :: rest.take k').length ≤ (a :: rest).length
          exact Nat.succ_le_succ (ih k')

/-- 中文说明：单步的账本长度增量至多 1（域外涂改也只是不增）。 -/
theorem coreStep_ledger_length_le {Rel : Type} (st : State Rel) (ev : FullEvent Rel) :
    (coreStep st ev).ledger.length ≤ st.ledger.length + 1 := by
  cases ev with
  | core e =>
      cases e with
      | formative eid rel =>
          rw [coreStep_ledger_formative, length_append_singleton_eq]
      | terminating eid rel =>
          rw [coreStep_ledger_terminating, length_append_singleton_eq]
      | performance eid obligor rel amount => exact Nat.le_succ _
      | declaratory eid => exact Nat.le_succ _
  | normBackflow eid rel =>
      rw [coreStep_ledger_normBackflow, length_append_singleton_eq]
  | historyRewrite eid keep =>
      exact Nat.le_trans (length_take_le st.ledger keep) (Nat.le_succ _)

/-- 中文说明：单步的履行账本长度增量至多 1。 -/
theorem coreStep_perf_length_le {Rel : Type} (st : State Rel) (ev : FullEvent Rel) :
    (coreStep st ev).perf.length ≤ st.perf.length + 1 := by
  cases ev with
  | core e =>
      cases e with
      | performance eid obligor rel amount =>
          rw [coreStep_perf_performance, length_append_singleton_eq]
      | formative eid rel => exact Nat.le_succ _
      | terminating eid rel => exact Nat.le_succ _
      | declaratory eid => exact Nat.le_succ _
  | normBackflow eid rel => exact Nat.le_succ _
  | historyRewrite eid keep => exact Nat.le_succ _

/-- 中文说明：导出记录表长度不超过轨迹长度。 -/
theorem traceRecords_length_le {Rel : Type} :
    ∀ (tr : Trace Rel), (traceRecords tr).length ≤ tr.length := by
  intro tr
  induction tr with
  | nil => exact Nat.le_refl _
  | cons a rest ih =>
      show (appendRecord (recordOfEvent a) (traceRecords rest)).length ≤ rest.length + 1
      have h1 : (appendRecord (recordOfEvent a) (traceRecords rest)).length ≤
        (traceRecords rest).length + 1 := by
        cases recordOfEvent a with
        | none => exact Nat.le_succ _
        | some x => exact Nat.le_refl _
      exact Nat.le_trans h1 (Nat.add_le_add_right ih 1)

/-- 中文说明：履行账本长度沿轨迹的上界＝初长＋步数（每步至多加一条）。 -/
theorem runTrace_perf_length_le {Rel : Type} :
    ∀ (st₀ : State Rel) (tr : Trace Rel),
      (runTrace st₀ tr).perf.length ≤ st₀.perf.length + tr.length := by
  intro st₀ tr
  induction tr generalizing st₀ with
  | nil => intro st₀; exact Nat.le_add_right st₀.perf.length 0
  | cons a rest ih =>
      intro st₀
      have hperf := ih (coreStep st₀ a)
      have hstep := coreStep_perf_length_le st₀ a
      show (runTrace (coreStep st₀ a) rest).perf.length ≤ st₀.perf.length + (rest.length + 1)
      omega

/-- 中文说明：**域内**轨迹的账本长度精确等式（由 `runTrace_ledger_eq_append` 直接得到）。 -/
theorem runTrace_ledger_length_eq {Rel : Type} (st₀ : State Rel) (tr : Trace Rel)
    (hdom : traceInDomain fullDomain tr) :
    (runTrace st₀ tr).ledger.length = st₀.ledger.length + (traceRecords tr).length := by
  rw [runTrace_ledger_eq_append st₀ tr hdom, List.length_append]

/-- 中文说明：**(E) 有限性主定理**：本件的复合是有限折叠而不是渐近过程——每步至多加一条记录，
故关系账本与履行账本的长度上界都是 `|tr|`。这里没有收敛、没有极限、没有不动点假设。
账本一条用的是**域内**上界（域外涂改会缩短账本，仍不超过同一无界）。 -/
theorem runTrace_length_bound {Rel : Type} (st₀ : State Rel) (tr : Trace Rel)
    (hdom : traceInDomain fullDomain tr) :
    (runTrace st₀ tr).ledger.length ≤ st₀.ledger.length + tr.length ∧
      (runTrace st₀ tr).perf.length ≤ st₀.perf.length + tr.length := by
  refine ⟨?_, runTrace_perf_length_le st₀ tr⟩
  rw [runTrace_ledger_length_eq st₀ tr hdom]
  exact Nat.add_le_add_left (traceRecords_length_le tr) st₀.ledger.length

/-- 中文说明：终态 π 的取值＝初态 π 值再对**有限**记录表做一次折叠（引 S5 `formsB_append`）。
折叠步数由 `traceRecords_length_le` 界住，无极限、无迭代收敛。 -/
theorem forms_at_end_is_bounded_fold {Rel : Type} [DecidableEq Rel]
    (st₀ : State Rel) (tr : Trace Rel) (r : Rel) (hdom : traceInDomain fullDomain tr) :
    formsB (runTrace st₀ tr).ledger r = formsFold r (formsB st₀.ledger r) (traceRecords tr) := by
  rw [runTrace_ledger_eq_append st₀ tr hdom]
  exact formsB_append st₀.ledger (traceRecords tr) r

/-- 中文说明：`performStep` 的两个计算值都被债额界住（引 S5 `applied_bounds`）。 -/
theorem performStep_values_bounded (d : Debt) (p : Nat) :
    (performStep d p).applied ≤ d.amount ∧ (performStep d p).outstanding ≤ d.amount := by
  obtain ⟨h1, _h2⟩ := applied_bounds d.amount p
  refine ⟨h1, ?_⟩
  show outstandingAfter d.amount p ≤ d.amount
  unfold outstandingAfter
  omega

/-- 中文说明：履行一步的账本读数：给付 10 抵债 10 ⇒ 实付 10、未偿 0，
而关系账本与"曾成立"读数一字不动（S5 双通道读数的轨迹版本）。 -/
theorem trace_performs_and_keeps_history :
    (runTrace st₀Seeded performTraceDemo).ledger = st₀Seeded.ledger ∧
      (runTrace st₀Seeded performTraceDemo).perf.length = 1 ∧
        formsEver (runTrace st₀Seeded performTraceDemo).ledger relationDemo :=
  ⟨by rw [runTrace_cons, coreStep_ledger_performance], by decide, by decide⟩

end JurisLean.Seams.FullProcess
