import Mathlib.Tactic

/-
Unified finalization, layer E (plan §5.4–§5.5; I.4.7 L07, fragment for U11–U13).

The six-type terminal table as a Lean fragment, mirroring the Python
contract `tools/unified_math_v2/unified/standards.py::finalize_issue`
BRANCH FOR BRANCH (same dispatch order, same premise discipline):

1. not ready                -> PENDING / NOT_READY
2. blockers                 -> NOT_ESTABLISHED / NEG_BLOCKED
3. all elements established -> ESTABLISHED / POS
4. burden ready + unmet     -> NOT_ESTABLISHED / NEG_BURDEN
5. Exhausted4 + Need        -> PENDING / LEGALLY_UNDETERMINED
6. fallthrough              -> PENDING / GAP

A missing Exhausted4 is not allowed to pose as undetermined (that is a
GAP) — witnessed by `witness_gap_is_not_undetermined_pose`.

What this file is NOT (scope, honestly): a single-issue fragment.  The
Γ/k/adjudication-state plumbing of I.4.7 (`caseEvalDomain` over
LawContext/KnowledgeView/AdjudicationState) is not built here; the
existing anchors `EvalDomain`/`stableKernel`/
`unique_verdict_iff_stable_kernel_singletons` in
`Seams/AdjudicationBridge.lean` are NOT imported — per I.4.7 that anchor
is only reusable with its full `collapsesToKernel` premise, which this
fragment does not assume.  The uniqueness statement here is instead the
UNCONDITIONAL allowed-union characterization plus the preserved
intersection-singleton counterexample that blocks the kernel-collapse
shortcut.
-/

namespace JurisLean.Seams.UnifiedFinalization

/-! ## 一、载体：三值裁判与六型终结依据 -/

/-- 裁判三值：成立／不成立／未决（与 Python `Judgment` 同名同义）。 -/
inductive Judgment : Type
  | established -- 成立
  | notEstablished -- 不成立
  | pending -- 未决
  deriving DecidableEq, Repr

/-- 终结依据六型（与 Python `FinalBasis` 同名同序）。 -/
inductive FinalBasis : Type
  | posB -- Ready ∧ ¬阻断 ∧ 要件全立
  | negBlockedB -- Ready ∧ 活的实质反证
  | negBurdenB -- Ready ∧ 负担已就绪 ∧ 有负担性未立要件
  | legallyUndeterminedB -- Exhausted4 ∧ Need（依法未决）
  | notReadyB -- 程序未就绪／中止
  | gapB -- 缺口（未穷尽，或穷尽而无需认定）
  deriving DecidableEq, Repr

/-- 单争点终结输入的七位前提面（§5.4 的机器读数）：
    程序就绪／实质阻断／要件全立／负担已就绪／有负担性未立要件／
    四穷尽（Exhausted4）／需要认定（Need）。 -/
structure IssueInputs where
  /-- 程序就绪（未就绪＝程序门，含中止）。 -/
  ready : Bool
  /-- 有活的实质反证阻断。 -/
  blockers : Bool
  /-- 全部要件已立。 -/
  allEstablished : Bool
  /-- 负担已就绪（可判不利）。 -/
  burdenReady : Bool
  /-- 存在主张方负担且未立的要件。 -/
  unmetBorne : Bool
  /-- 材料四穷尽（Exhausted4）。 -/
  exhausted4 : Bool
  /-- 需要认定（Need）。 -/
  need : Bool
  deriving Repr

/-! ## 二、终结表（与 Python 同一次序的分派） -/

/-- 终结表：模式自上而下＝Python `finalize_issue` 的分支次序。
    分派只读七位前提，不读偏好、不读调用方结论。 -/
def finalizeIssue : IssueInputs → Judgment × FinalBasis
  | ⟨false, _, _, _, _, _, _⟩ => (Judgment.pending, FinalBasis.notReadyB)
  | ⟨true, true, _, _, _, _, _⟩ => (Judgment.notEstablished, FinalBasis.negBlockedB)
  | ⟨true, false, true, _, _, _, _⟩ => (Judgment.established, FinalBasis.posB)
  | ⟨true, false, false, true, true, _, _⟩ =>
      (Judgment.notEstablished, FinalBasis.negBurdenB)
  | ⟨true, false, false, _, _, true, true⟩ =>
      (Judgment.pending, FinalBasis.legallyUndeterminedB)
  | ⟨_, _, _, _, _, _, _⟩ => (Judgment.pending, FinalBasis.gapB)

/-- 合法终结：每个输出型携带自己的语义前提（推导规则）。与前四型不同，
    依法未决要求负担规则未先触发（否则第 4 分支已判不利）；缺口要求
    不满足 Exhausted4 ∧ Need（否则是依法未决，不是缺口）。 -/
inductive LegalFinal : IssueInputs → Judgment × FinalBasis → Prop
  | notReady (inp : IssueInputs) (h : inp.ready = false) :
      LegalFinal inp (Judgment.pending, FinalBasis.notReadyB)
  | negBlocked (inp : IssueInputs) (hr : inp.ready = true)
      (hb : inp.blockers = true) :
      LegalFinal inp (Judgment.notEstablished, FinalBasis.negBlockedB)
  | pos (inp : IssueInputs) (hr : inp.ready = true) (hb : inp.blockers = false)
      (ha : inp.allEstablished = true) :
      LegalFinal inp (Judgment.established, FinalBasis.posB)
  | negBurden (inp : IssueInputs) (hr : inp.ready = true)
      (hb : inp.blockers = false) (ha : inp.allEstablished = false)
      (hbr : inp.burdenReady = true) (hu : inp.unmetBorne = true) :
      LegalFinal inp (Judgment.notEstablished, FinalBasis.negBurdenB)
  | undetermined (inp : IssueInputs) (hr : inp.ready = true)
      (hb : inp.blockers = false) (ha : inp.allEstablished = false)
      (hnf : inp.burdenReady = false ∨ inp.unmetBorne = false)
      (he : inp.exhausted4 = true) (hn : inp.need = true) :
      LegalFinal inp (Judgment.pending, FinalBasis.legallyUndeterminedB)
  | gap (inp : IssueInputs) (hr : inp.ready = true) (hb : inp.blockers = false)
      (ha : inp.allEstablished = false)
      (hnf : inp.burdenReady = false ∨ inp.unmetBorne = false)
      (hnot : ¬ (inp.exhausted4 = true ∧ inp.need = true)) :
      LegalFinal inp (Judgment.pending, FinalBasis.gapB)

/-! ## 三、精确表示（U11）：终结表＝合法终结关系的外延 -/

/-- **健全**：表给出的每个输出都满足自己型别的语义前提。
    证明按 `finalizeIssue` 的同一模式序展开为十个字面量分支（负担未触发的
    依法未决／缺口各按 Or 左右再分），每支的字面前提都是 `rfl`／小 `decide`。 -/
theorem finalize_legal :
    ∀ (inp : IssueInputs), LegalFinal inp (finalizeIssue inp)
  | ⟨false, b, a, br, u, e, n⟩ => LegalFinal.notReady _ rfl
  | ⟨true, true, a, br, u, e, n⟩ => LegalFinal.negBlocked _ rfl rfl
  | ⟨true, false, true, br, u, e, n⟩ => LegalFinal.pos _ rfl rfl rfl
  | ⟨true, false, false, true, true, e, n⟩ => LegalFinal.negBurden _ rfl rfl rfl rfl rfl
  | ⟨true, false, false, false, u, true, true⟩ =>
      LegalFinal.undetermined _ rfl rfl rfl (Or.inl rfl) rfl rfl
  | ⟨true, false, false, br, false, true, true⟩ =>
      LegalFinal.undetermined _ rfl rfl rfl (Or.inr rfl) rfl rfl
  | ⟨true, false, false, false, u, false, n⟩ =>
      LegalFinal.gap _ rfl rfl rfl (Or.inl rfl) (by cases n <;> decide)
  | ⟨true, false, false, false, u, true, false⟩ =>
      LegalFinal.gap _ rfl rfl rfl (Or.inl rfl) (by decide)
  | ⟨true, false, false, br, false, false, n⟩ =>
      LegalFinal.gap _ rfl rfl rfl (Or.inr rfl) (by cases n <;> decide)
  | ⟨true, false, false, br, false, true, false⟩ =>
      LegalFinal.gap _ rfl rfl rfl (Or.inr rfl) (by decide)

/-- **完备**：任何满足语义前提的推导都落在表的同一输出上（对推导分例归纳）。 -/
theorem finalize_complete {inp : IssueInputs} {o : Judgment × FinalBasis}
    (h : LegalFinal inp o) : o = finalizeIssue inp := by
  cases h with
  | notReady h =>
      rcases inp with ⟨r, b, a, br, u, e, n⟩
      subst h
      cases b <;> cases a <;> cases br <;> cases u <;> cases e <;> cases n <;> rfl
  | negBlocked hr hb =>
      rcases inp with ⟨r, b, a, br, u, e, n⟩
      subst hr; subst hb
      cases a <;> cases br <;> cases u <;> cases e <;> cases n <;> rfl
  | pos hr hb ha =>
      rcases inp with ⟨r, b, a, br, u, e, n⟩
      subst hr; subst hb; subst ha
      cases br <;> cases u <;> cases e <;> cases n <;> rfl
  | negBurden hr hb ha hbr hu =>
      rcases inp with ⟨r, b, a, br, u, e, n⟩
      subst hr; subst hb; subst ha; subst hbr; subst hu
      cases e <;> cases n <;> rfl
  | undetermined hr hb ha hnf he hn =>
      rcases inp with ⟨r, b, a, br, u, e, n⟩
      subst hr; subst hb; subst ha; subst he; subst hn
      rcases hnf with h1 | h1
      · subst h1; cases u <;> rfl
      · subst h1; cases br <;> rfl
  | gap hr hb ha hnf hnot =>
      rcases inp with ⟨r, b, a, br, u, e, n⟩
      subst hr; subst hb; subst ha
      rcases hnf with h1 | h1
      · subst h1
        cases u <;> cases e <;> cases n <;>
          first | rfl | (exfalso; exact hnot ⟨rfl, rfl⟩)
      · subst h1
        cases br <;> cases e <;> cases n <;>
          first | rfl | (exfalso; exact hnot ⟨rfl, rfl⟩)

/-- **精确表示**：合法终结关系的外延恰是表输出的单点集
    （`verdict_representation_exact` 的片段读数：枚举结果有推导，推导落回枚举）。 -/
theorem finalize_representation_exact (inp : IssueInputs) (o : Judgment × FinalBasis) :
    LegalFinal inp o ↔ o = finalizeIssue inp :=
  ⟨fun h => finalize_complete h, fun h => by subst h; exact finalize_legal inp⟩

/-! ## 四、程序与实体的分离（U12）与前提互斥 -/

/-- 程序门读数：NOT_READY 当且仅当程序未就绪（其他五型都要求就绪）。 -/
theorem notReady_iff (inp : IssueInputs) :
    (finalizeIssue inp).2 = FinalBasis.notReadyB ↔ inp.ready = false := by
  rcases inp with ⟨r, b, a, br, u, e, n⟩
  cases r <;> cases b <;> cases a <;> cases br <;> cases u <;> cases e <;> cases n <;> decide

/-- **程序结果不供给实体依据**：程序未就绪只给 PENDING/NOT_READY，
    从不产出成立或不成立（I.4.7 `procedural_result_does_not_supply_substantive_basis`
    的片段读数；它不禁止依法证明失败、推定或妨碍规则产生自己的裁判后果——
    那些后果各依其有效法律依据推导）。 -/
theorem not_ready_yields_pending_only (inp : IssueInputs) (h : inp.ready = false) :
    finalizeIssue inp = (Judgment.pending, FinalBasis.notReadyB) := by
  rcases inp with ⟨r, b, a, br, u, e, n⟩
  subst h
  rfl

/-- 依法未决的前提钉死：Exhausted4 ∧ Need 缺一不可。 -/
theorem undetermined_requires_exhausted_need (inp : IssueInputs)
    (h : LegalFinal inp (Judgment.pending, FinalBasis.legallyUndeterminedB)) :
    inp.exhausted4 = true ∧ inp.need = true := by
  cases h with
  | undetermined _ _ _ _ he hn => exact ⟨he, hn⟩

/-- **未穷尽不得冒充未决**：Exhausted4 不满足时输出绝不是 LEGALLY_UNDETERMINED
    （那是 GAP——Python 终结表同一纪律的 Lean 读数）。 -/
theorem gap_is_not_undetermined_pose (inp : IssueInputs) (h : inp.exhausted4 = false) :
    (finalizeIssue inp).2 ≠ FinalBasis.legallyUndeterminedB := by
  rcases inp with ⟨r, b, a, br, u, e, n⟩
  subst h
  cases r <;> cases b <;> cases a <;> cases br <;> cases u <;> cases n <;> decide

/-- 成立与阻断不成立互斥（Pos 与 Neg 前提互斥其一）。 -/
theorem pos_negBlocked_exclusive (inp : IssueInputs)
    (h₁ : LegalFinal inp (Judgment.established, FinalBasis.posB))
    (h₂ : LegalFinal inp (Judgment.notEstablished, FinalBasis.negBlockedB)) : False := by
  cases h₁ with
  | pos _ hb _ =>
      cases h₂ with
      | negBlocked _ hb' => rw [hb] at hb'; exact Bool.noConfusion hb'

/-- 成立与负担不成立互斥（要件全立 vs 有未立负担性要件）。 -/
theorem pos_negBurden_exclusive (inp : IssueInputs)
    (h₁ : LegalFinal inp (Judgment.established, FinalBasis.posB))
    (h₂ : LegalFinal inp (Judgment.notEstablished, FinalBasis.negBurdenB)) : False := by
  cases h₁ with
  | pos _ _ ha =>
      cases h₂ with
      | negBurden _ _ ha' _ _ => rw [ha] at ha'; exact Bool.noConfusion ha'

/-- 程序门与实体判断不相容（ready 同时为假与真）。 -/
theorem procedural_and_substantive_incompatible (inp : IssueInputs)
    (h₁ : LegalFinal inp (Judgment.pending, FinalBasis.notReadyB))
    (h₂ : LegalFinal inp (Judgment.established, FinalBasis.posB)) : False := by
  cases h₁ with
  | notReady hr =>
      cases h₂ with
      | pos hr' _ _ => rw [hr] at hr'; exact Bool.noConfusion hr'

/-! ## 五、允许并的唯一性（U13）与交集单点反例 -/

section Uniqueness

variable {V : Type} [DecidableEq V]

/-- 允许并：一族评价各自给出的结论之并（`allowedSet` 的有限族读数）。 -/
def allowedUnion (dom : List (Finset V)) : Finset V :=
  dom.foldr (fun S acc => S ∪ acc) ∅

/-- 允许并的 cons 读数（foldr 定义展开）。 -/
theorem allowedUnion_cons (T : Finset V) (rest : List (Finset V)) :
    allowedUnion (T :: rest) = T ∪ allowedUnion rest := rfl

/-- 成员评价包含于允许并。 -/
theorem subset_allowedUnion {dom : List (Finset V)} {S : Finset V} (h : S ∈ dom) :
    S ⊆ allowedUnion dom := by
  induction dom with
  | nil => simp at h
  | cons T rest ih =>
      intro x hx
      simp only [allowedUnion, List.foldr_cons]
      rcases List.mem_cons.mp h with rfl | hrest
      · exact Finset.mem_union.mpr (Or.inl hx)
      · exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_of_subset (ih hrest) hx))

/-- 全单点族（非空）的允许并是那个单点。 -/
theorem allowedUnion_eq_singleton_of_all {v : V} :
    ∀ (dom : List (Finset V)), dom ≠ [] → (∀ S ∈ dom, S = {v}) → allowedUnion dom = {v} := by
  intro dom
  induction dom with
  | nil => intro h; exact absurd rfl h
  | cons T rest ih =>
      intro _ hAll
      have hT : T = {v} := hAll T (by simp)
      rw [allowedUnion_cons, hT]
      cases rest with
      | nil => simp [allowedUnion]
      | cons T' rest' =>
          rw [ih (by simp) (fun S hS => hAll S (by simp [hS]))]
          simp

/-- **唯一允许**：允许并为单点 ↔（族非空时）每个评价都是那个单点。
    这是 I.4.7 "UniqueAllowed ↔ (⋃α∈EvalDomain,Out α)={v} 且域非空" 的有限族片段；
    每个"评价产出非空"是前提（空评价不进域）。 -/
theorem unique_allowed_iff_all_singleton {dom : List (Finset V)} {v : V}
    (hne : dom ≠ []) (hnn : ∀ S ∈ dom, S.Nonempty) :
    allowedUnion dom = {v} ↔ ∀ S ∈ dom, S = {v} := by
  constructor
  · intro hU S hS
    have hsub : S ⊆ allowedUnion dom := subset_allowedUnion hS
    rw [hU] at hsub
    obtain ⟨x, hx⟩ := hnn S hS
    have hxv : x = v := Finset.mem_singleton.mp (hsub hx)
    have hvs : ({v} : Finset V) ⊆ S := by
      intro y hy
      have hyv : y = v := Finset.mem_singleton.mp hy
      subst hyv
      subst hxv
      exact hx
    exact Finset.eq_of_subset_of_card_le hsub (Finset.card_le_card hvs)
  · intro hAll
    exact allowedUnion_eq_singleton_of_all dom hne hAll

/-- **交集单点反例（保留）**：两个非单点评价的交可以是单点而允许并不是单点——
    把"稳定核塌缩成单点"当"唯一允许"的捷径在此不通
    （AdjudicationBridge 的 `unique_verdict_iff_stable_kernel_singletons` 需要
    `collapsesToKernel` 全前提，本片段不假设它）。 -/
theorem intersection_singleton_not_unique :
    (List.foldr (· ∩ ·) ({0, 1, 2} : Finset Nat) [{0, 1}, {1, 2}] = {1})
      ∧ allowedUnion [{0, 1}, {1, 2}] ≠ ({1} : Finset Nat) := by
  decide

end Uniqueness

/-! ## 六、见证（Python 测试向量的 Lean 同行） -/

/-- 程序未就绪：其余前提再好也只给 PENDING/NOT_READY。 -/
theorem witness_not_ready :
    finalizeIssue ⟨false, false, true, false, false, true, true⟩
      = (Judgment.pending, FinalBasis.notReadyB) := rfl

/-- 未穷尽＋无需认定：GAP，不冒充 LEGALLY_UNDETERMINED。 -/
theorem witness_gap_is_not_undetermined_pose :
    finalizeIssue ⟨true, false, false, false, false, false, false⟩
      = (Judgment.pending, FinalBasis.gapB) := rfl

/-- 穷尽＋需要认定：依法未决。 -/
theorem witness_undetermined :
    finalizeIssue ⟨true, false, false, false, false, true, true⟩
      = (Judgment.pending, FinalBasis.legallyUndeterminedB) := rfl

end JurisLean.Seams.UnifiedFinalization
