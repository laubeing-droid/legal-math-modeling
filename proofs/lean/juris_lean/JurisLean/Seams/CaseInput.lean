import Mathlib.Data.Finset.Basic
import JurisLean.HornDefinitions
import JurisLean.Seams.SourceNorms

/-! # 案卷输入层（17_ 卷 WBS-5）：把"一份案卷"变成一台 `HornSystem`

**这一层补的是十大缺口的第一条**：此前所有链都跑在手写夹具上
（`UnifiedInstance.lean` 的 `instanceM` 逐字段手填），没有"证据清单/诉请 → 载体"的
构造管道，真实案件喂不进去。本件只做**输入层**：

* `CaseFile`：一份案卷的最小数据——事实位（名字＋是否成立）、规范（前提集＋结论）、
  引注（这份案卷声称依据哪些条文，仅供追溯，不参与计算）。
* `hornOfCase`：把案卷折成一台 `HornSystem`——论域＝出现的所有原子，
  初始事实＝成立的事实位，规则＝案卷的规范逐条照搬。
* 正确性：`case_closure_sound` —— 案卷闭包里的每个原子都是**语义后承**
  （复用 `SourceNorms.horn_closure_semantic_iff`，不另证一遍）；
  `case_facts_in_closure` —— 成立的事实位自己进闭包（无前提规则的退化形，
  复用 `noPremiseRule_in_closure` 同一条通道）。

**本件不做的**：不把案卷变成 `UnifiedModel`（那是下一层的事），不认定任何真实案件，
不验证引注串指向真实条文（引注只是案卷自报的出处）。JSON→Lean 生成器在
`scripts/`，与本件同批交付。

制造日期：2026-10-04（17_ 卷 WBS-5 轮）。
-/

namespace JurisLean.Seams.CaseInput

open JurisLean.Seams.SourceNorms

/-- 一份案卷的最小数据结构。`citations` 是案卷**自报**的条文出处，
    仅供追溯与对账，不参与任何计算，也不验证其指向。 -/
structure CaseFile (α : Type) [DecidableEq α] where
  /-- 案卷声称成立的事实位（名字＋成立与否）。 -/
  facts : List (α × Bool)
  /-- 案卷援引的规范：前提集＋结论。 -/
  rules : List (HornRule α)
  /-- 案卷自报的条文出处（追溯用）。 -/
  citations : List String

/-- 案卷的**论域**：事实位与全部规则头尾出现的原子，去重。 -/
def caseUniv {α : Type} [DecidableEq α] (cf : CaseFile α) : Finset α :=
  (cf.facts.map Prod.fst).toFinset ∪
    (cf.rules.map (·.conclusion)).toFinset ∪
    (cf.rules.flatMap (fun r => r.premises.toList)).toFinset

/-- 案卷的**初始事实**：只取成立为真的那些事实位。 -/
def caseFacts {α : Type} [DecidableEq α] (cf : CaseFile α) : Finset α :=
  (cf.facts.filter (·.2)).map Prod.fst |>.toFinset

/-- 中文证明（技术引理）：初始事实都在论域里——论域本来就含全部事实位的名字。 -/
theorem caseFacts_subset_caseUniv {α : Type} [DecidableEq α] (cf : CaseFile α) :
    caseFacts cf ⊆ caseUniv cf := by
  intro a ha
  simp only [caseFacts, List.mem_toFinset, Finset.mem_map, List.mem_filter] at ha
  obtain ⟨p, hp, rfl⟩ := ha
  simp only [caseUniv, List.mem_toFinset, Finset.mem_map, List.mem_union]
  exact Or.inl ⟨p, hp.1, rfl⟩

/-- 中文证明（技术引理）：每条规则的结论都在论域里——论域并了全部规则头。 -/
theorem caseHeads_subset_caseUniv {α : Type} [DecidableEq α] (cf : CaseFile α) :
    ∀ r ∈ (cf.rules.toFinset : Finset (HornRule α)), r.conclusion ∈ caseUniv cf := by
  intro r hr
  simp only [caseUniv, List.mem_toFinset, Finset.mem_map, List.mem_union]
  exact Or.inr ⟨Or.inl ⟨r, by
    simp only [List.mem_toFinset] at hr
    exact hr, rfl⟩⟩

/-- **主构造**：把一份案卷折成一台 `HornSystem`。 -/
def hornOfCase {α : Type} [DecidableEq α] (cf : CaseFile α) : HornSystem α where
  univ := caseUniv cf
  initialFacts := caseFacts cf
  rules := cf.rules.toFinset
  initialFacts_subset_univ := caseFacts_subset_caseUniv cf
  heads_subset_univ := caseHeads_subset_caseUniv cf

/-- 中文证明（**健全性**）：案卷闭包里的每个原子都是案卷的语义后承。
    复用 `horn_closure_semantic_iff` 的正向，不另证。 -/
theorem case_closure_sound {α : Type} [DecidableEq α] (cf : CaseFile α) (a : α)
    (h : a ∈ closureAt (hornOfCase cf)) : entailed (hornOfCase cf) a :=
  (horn_closure_semantic_iff (hornOfCase cf) a).mp h

/-- 中文证明（**事实进闭包**）：案卷里成立的事实位自己就在闭包里
    ——初始事实无需任何规则即被闭包收纳（`entailed` 对模型取全称，
    初始事实被任何模型包含）。 -/
theorem case_facts_in_closure {α : Type} [DecidableEq α] (cf : CaseFile α) (a : α)
    (h : a ∈ caseFacts cf) : a ∈ closureAt (hornOfCase cf) := by
  refine (horn_closure_semantic_iff (hornOfCase cf) a).mpr ?_
  intro M hM
  exact hM.1 h

/-- 中文见证（**非空案卷**）：一份两条事实、一条规则的最小案卷，
    能跑出"前提 ⇒ 结论"的闭包读数。夹具，不认定任何真实案件。 -/
def sampleFile : CaseFile String :=
  { facts := [("欠款成立", true), ("违约成立", true)],
    rules := [{ premises := {"欠款成立", "违约成立"}, conclusion := "应付违约金" }],
    citations := ["民法典585条2款（案卷自报，未核）"] }

/-- 中文证明：样例案卷的结论确实进闭包（经 `case_closure_sound` 的逆向：
    语义上，含前提的模型必含结论）。 -/
theorem sample_conclusion_in_closure :
    "应付违约金" ∈ closureAt (hornOfCase sampleFile) := by
  refine (horn_closure_semantic_iff (hornOfCase sampleFile) _).mpr ?_
  intro M hM
  have h1 : "欠款成立" ∈ M := hM.1 (by
    simp only [hornOfCase, caseFacts, List.mem_toFinset, Finset.mem_map, List.mem_filter]
    exact ⟨("欠款成立", true), ⟨by decide, by decide⟩, rfl⟩)
  have h2 : "违约成立" ∈ M := hM.1 (by
    simp only [hornOfCase, caseFacts, List.mem_toFinset, Finset.mem_map, List.mem_filter]
    exact ⟨("违约成立", true), ⟨by decide, by decide⟩, rfl⟩)
  have hr := hM.2 { premises := {"欠款成立", "违约成立"}, conclusion := "应付违约金" } (by
    simp only [hornOfCase, List.mem_toFinset]
    exact List.Mem.head _)
  exact hr ⟨h1, h2⟩

end JurisLean.Seams.CaseInput
