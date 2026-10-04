import Mathlib.Data.Finset.Basic
import JurisLean.HornDefinitions
import JurisLean.Seams.SourceNorms

/-! # 案卷输入层（17_ 卷 WBS-5）：把"一份案卷"变成一台 `HornSystem`

**这一层补的是十大缺口的第一条**：此前所有链都跑在手写夹具上
（`UnifiedInstance.lean` 的 `instanceM` 逐字段手填），没有"证据清单/诉请 → 载体"的
构造管道，真实案件喂不进去。本件只做**输入层**：

* `CaseFile`：一份案卷的最小数据——论域（本案出现的全部原子）、成立的事实位、
  规范（前提集＋结论）、引注（案卷自报的出处，仅供追溯，不参与计算）。
  两个前提（事实含于论域、规则头含于论域）由案卷**自己**携带，
  `hornOfCase` 因此不需要现算任何包含关系。
* `hornOfCase`：把案卷照搬成一台 `HornSystem`——逐字段直读。
* 正确性：`case_closure_sound`——案卷闭包里的每个原子都是**语义后承**
  （复用 `SourceNorms.horn_closure_semantic_iff`，不另证）；
  `case_facts_in_closure`——成立的事实位自己进闭包（语义侧：任何模型含初始事实）。

**本件不做的**：不把案卷变成 `UnifiedModel`（那是下一层），不认定任何真实案件，
不验证引注串指向真实条文。JSON→Lean 生成器在 `scripts/gen_case_input.py`，
与本件同批交付；生成器把 JSON 里 `false` 的事实位直接丢弃（不进 `facts`），
因为"不成立的事实"在 Horn 输入里就是"没有这个初始事实"。

制造日期：2026-10-04（17_ 卷 WBS-5 轮）。
-/

namespace JurisLean.Seams.CaseInput

open JurisLean.Seams.SourceNorms

/-- 一份案卷的最小数据结构。`citations` 是案卷**自报**的条文出处，
    仅供追溯与对账，不参与任何计算，也不验证其指向。
    两个前提由案卷自己携带：`hFacts`（成立事实都在论域）、
    `hHeads`（每条规则的结论都在论域）——它们是 `HornSystem` 的入场条件，
    案卷给不出就不该进这台机器。 -/
structure CaseFile (α : Type) [DecidableEq α] where
  /-- 本案出现的全部原子。 -/
  univ : Finset α
  /-- 成立的事实位（JSON 里 `false` 的位由生成器丢弃）。 -/
  facts : Finset α
  /-- 案卷援引的规范：前提集＋结论。 -/
  rules : Finset (HornRule α)
  /-- 案卷自报的条文出处（追溯用）。 -/
  citations : List String
  hFacts : facts ⊆ univ
  hHeads : ∀ r ∈ rules, r.conclusion ∈ univ

/-- **主构造**：把一份案卷照搬成一台 `HornSystem`。逐字段直读，
    不现算任何包含关系——那是案卷自己带来的前提。 -/
def hornOfCase {α : Type} [DecidableEq α] (cf : CaseFile α) : HornSystem α where
  univ := cf.univ
  initialFacts := cf.facts
  rules := cf.rules
  initialFacts_subset_univ := cf.hFacts
  heads_subset_univ := cf.hHeads

/-- 中文证明（**健全性**）：案卷闭包里的每个原子都是案卷的语义后承。
    复用 `horn_closure_semantic_iff` 的正向，不另证。 -/
theorem case_closure_sound {α : Type} [DecidableEq α] (cf : CaseFile α) (a : α)
    (h : a ∈ closureAt (hornOfCase cf)) : entailed (hornOfCase cf) a :=
  (horn_closure_semantic_iff (hornOfCase cf) a).mp h

/-- 中文证明（**事实进闭包**）：案卷里成立的事实位自己就在闭包里
    ——语义侧：`entailed` 对模型取全称，而任何模型都包含初始事实。 -/
theorem case_facts_in_closure {α : Type} [DecidableEq α] (cf : CaseFile α) (a : α)
    (h : a ∈ (hornOfCase cf).initialFacts) : a ∈ closureAt (hornOfCase cf) := by
  refine (horn_closure_semantic_iff (hornOfCase cf) a).mpr ?_
  intro M hM
  exact hM.1 h

/-- 中文见证（**非空案卷**）：两个事实、一条规则的最小案卷，
    能跑出"前提 ⇒ 结论"的闭包读数。夹具，不认定任何真实案件。 -/
def sampleFile : CaseFile String where
  univ := {"欠款成立", "违约成立", "应付违约金"}
  facts := {"欠款成立", "违约成立"}
  rules := {{ premises := {"欠款成立", "违约成立"}, conclusion := "应付违约金" }}
  citations := ["民法典585条2款（案卷自报，未核）"]
  hFacts := by decide
  hHeads := by decide

/-- 中文证明：样例案卷的结论确实进闭包（经语义侧：
    含前提的模型必含结论）。 -/
theorem sample_conclusion_in_closure :
    "应付违约金" ∈ closureAt (hornOfCase sampleFile) := by
  refine (horn_closure_semantic_iff (hornOfCase sampleFile) _).mpr ?_
  intro M hM
  have h1 : "欠款成立" ∈ M := hM.1 (by
    show "欠款成立" ∈ ({"欠款成立", "违约成立"} : Finset String)
    exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl))
  have h2 : "违约成立" ∈ M := hM.1 (by
    show "违约成立" ∈ ({"欠款成立", "违约成立"} : Finset String)
    exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl))
  have hr := hM.2 { premises := {"欠款成立", "违约成立"}, conclusion := "应付违约金" }
    (by show _ ∈ ({{ premises := {"欠款成立", "违约成立"}, conclusion := "应付违约金" }} :
          Finset (HornRule String))
        exact Finset.mem_singleton.mpr rfl)
  refine hr ?_
  intro a ha
  rw [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl
  · exact h1
  · exact h2

end JurisLean.Seams.CaseInput
