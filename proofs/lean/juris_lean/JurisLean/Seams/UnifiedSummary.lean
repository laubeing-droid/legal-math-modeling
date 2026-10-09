import Mathlib.Tactic
import JurisLean.Seams.UnifiedGuards

/-
Unified summary saturation, the Lean reflection of the Python §4
summary layer (main doc §8.2 leftover "Python 摘要饱和的 Lean 反射").

Python contract of record:
`tools/unified_math_v2/unified/argument_grammar.py` —
`last_of` (leaf ∅ / defeasible root {j} / strict root union, §4.2),
`_own_site` + `summarize` (sites = own ∪ children; ordinary leaves
attackable, axiom/exempt not), `_delta` (summary transfer δ_r), and
`saturate_summaries` (least fixed point from leaf productions with a
generating witness per summary).

Reflection design, honestly scoped:

1. CARRIERS — mutual `STree`/`SForest` trees; `Summ` the finite
   observable (conc/mode/rootRule/lastI/leafSrcs/sites; the Python
   `tags` field is constant-empty in this fragment and omitted, noted
   here); `SiteSum.leafS`/`.ruleS` the two site shapes; `SRule`
   reuses `GuardSlot` from `UnifiedGuards`.
2. WELL-FORMEDNESS IS THE FUNCTION — `summarize : STree → Option Summ`
   returns none exactly where Python's constructor validation rejects
   (child conclusions must match premise order).  Determinism of the
   observable is definitional (it IS a function); no separate
   uniqueness proof needed.
3. δ AS A PURE FUNCTION — `deltaS r qs` mirrors `_delta` exactly:
   defeasible root last = {rid}, strict root = union of child lasts;
   sites = own site :: children's sites; the own site carries r's
   guard slots.
4. SATURATION — height-indexed `SaturatedN Γ n` (the indexing repairs
   the no-IH-through-membership trap: step children live at n, the
   parent at n+1), `Saturated` the unheighted wrapper.
   `saturatedN_witness`: every saturated summary has a REALIZING tree
   (no phantom summaries — saturation soundness).
   `saturatedN_into_closed`: Saturated is the LEAST set closed under
   δ from the leaf productions (the least-fixpoint discipline of
   `saturate_summaries`).
   Termination-by-finite-domain is carried by the height index, not
   re-proved here.

STATUS: proved theorems pending their CI compile round (module check
then root then full release); no `sorry`/`admit`/custom `axiom`/
`: True :=`/`native_decide` appears here.
-/

namespace JurisLean.Seams.UnifiedSummary

open JurisLean.Seams.UnifiedGuards (GuardSlot)

/-! ## 一、载体：模式、位点、摘要、规则 -/

/-- 论证模式（Python `ArgMode`）。 -/
inductive SMode where
  | strictS | defeasible

/-- 位点摘要（Python `SiteSummary` 的两形）：普通叶位点（last ∅、
无实例、无守卫）与规则结点位点（带模式/实例/last/守卫槽）。 -/
inductive SiteSum (A : Type) where
  | leafS (conc : A)
  | ruleS (conc : A) (m : SMode) (inst : A) (lastI : List A)
      (guards : List (GuardSlot A))

/-- 有限可观察摘要（Python `Summary`；`tags` 恒空故不设字段）。 -/
structure Summ (A : Type) where
  conc : A
  mode : SMode
  rootRule : Option A
  lastI : List A
  leafSrcs : List A
  sites : List (SiteSum A)

/-- 文法规则（Python `GrammarRule`；守卫槽复用 UnifiedGuards 载体）。 -/
structure SRule (A : Type) where
  rid : A
  premises : List A
  head : A
  mode : SMode
  guards : List (GuardSlot A)

/-- 互斥树/林：叶带 ordinary 位与源；结点带规则与子林。 -/
inductive STree (A : Type) where
  | sLeaf (ordinary : Bool) (atom src : A)
  | sNode (r : SRule A) (fs : SForest A)
with SForest (A : Type) where
  | fNil
  | fCons (t : STree A) (fs : SForest A)

/-- 树的头结论（非递归：只读根）。 -/
def headT {A : Type} : STree A → A
  | .sLeaf _ a _ => a
  | .sNode r _ => r.head

/-! ## 二、δ 传递与叶种子（Python `_delta`/`leaf` 摘要） -/

/-- Last 策略的规则侧（§4.2）：可废止根取 {rid}，严格根取子 last 并。 -/
def lastOfRule {A : Type} (r : SRule A) (qs : List (Summ A)) : List A :=
  match r.mode with
  | .defeasible => [r.rid]
  | .strictS => qs.flatMap Summ.lastI

/-- 结点自身位点（携带 r 的守卫槽）。 -/
def ownSiteOf {A : Type} (r : SRule A) (qs : List (Summ A)) : SiteSum A :=
  .ruleS r.head r.mode r.rid (lastOfRule r qs) r.guards

/-- 摘要传递 δ_r(q₁,…,qₖ)（Python `_delta` 逐字段对应）。 -/
def deltaS {A : Type} (r : SRule A) (qs : List (Summ A)) : Summ A where
  conc := r.head
  mode := r.mode
  rootRule := some r.rid
  lastI := lastOfRule r qs
  leafSrcs := qs.flatMap Summ.leafSrcs
  sites := ownSiteOf r qs :: qs.flatMap Summ.sites

/-- 普通叶的种子摘要（last ∅；位点是叶位点；leafSrcs 记源）。 -/
def leafOrdSum {A : Type} (a src : A) : Summ A where
  conc := a
  mode := .strictS
  rootRule := none
  lastI := []
  leafSrcs := [src]
  sites := [.leafS a]

/-- 豁免叶（axiom/exempt）的种子摘要：不是可攻击位置，无位点。 -/
def leafExemptSum {A : Type} (a src : A) : Summ A where
  conc := a
  mode := .strictS
  rootRule := none
  lastI := []
  leafSrcs := [src]
  sites := []

/-! ## 三、summarize：良构判定内嵌的摘要函数 -/

/-- 摘要函数（互斥结构递归）。`none` 恰落在 Python 构造器拒绝处：
子结论不匹配前提序的树没有摘要（良构判定内嵌，镜像
`ArgTree.__post_init__`）。 -/
mutual
def summarize {A : Type} [DecidableEq A] : STree A → Option (Summ A)
  | .sLeaf true a src => some (leafOrdSum a src)
  | .sLeaf false a src => some (leafExemptSum a src)
  | .sNode r fs =>
      match summs fs with
      | none => none
      | some qs =>
          if qs.map Summ.conc = r.premises then some (deltaS r qs) else none
def summs {A : Type} [DecidableEq A] : SForest A → Option (List (Summ A))
  | .fNil => some []
  | .fCons t fs =>
      match summarize t, summs fs with
      | some q, some qs => some (q :: qs)
      | _, _ => none
end

theorem summarize_leafOrd {A : Type} [DecidableEq A] (a src : A) :
    summarize (.sLeaf true a src) = some (leafOrdSum a src) := by
  simp [summarize]

theorem summarize_leafExempt {A : Type} [DecidableEq A] (a src : A) :
    summarize (.sLeaf false a src) = some (leafExemptSum a src) := by
  simp [summarize]

theorem summs_nil {A : Type} [DecidableEq A] : summs (.fNil : SForest A) = some [] := by
  simp [summs]

/-- 林摘要的逐元素刻画。 -/
theorem summs_cons_iff {A : Type} [DecidableEq A] (t : STree A) (fs : SForest A)
    (qs : List (Summ A)) :
    summs (.fCons t fs) = some qs ↔
      ∃ q qs', summarize t = some q ∧ summs fs = some qs' ∧ qs = q :: qs' := by
  simp only [summs]
  constructor
  · intro h
    cases h1 : summarize t with
    | none => rw [h1] at h; simp at h
    | some q =>
      cases h2 : summs fs with
      | none => rw [h1, h2] at h; simp at h
      | some qs' =>
        simp only [h1, h2] at h
        exact ⟨q, qs', h1, h2, h.symm⟩
  · rintro ⟨q, qs', h1, h2, h3⟩
    simp only [h1, h2]
    exact congrArg some h3.symm

/-- 结点摘要 iff：成功 ⟺ 子摘要齐备且按序匹配前提且结果即 δ。 -/
theorem summarize_node_iff {A : Type} [DecidableEq A] (r : SRule A) (fs : SForest A)
    (q : Summ A) :
    summarize (.sNode r fs) = some q ↔
      ∃ qs, summs fs = some qs ∧ qs.map Summ.conc = r.premises ∧ q = deltaS r qs := by
  simp only [summarize]
  constructor
  · intro h
    cases h1 : summs fs with
    | none => rw [h1] at h; simp at h
    | some qs =>
      simp only [h1] at h
      by_cases hp : qs.map Summ.conc = r.premises
      · rw [if_pos hp] at h
        exact ⟨qs, h1, hp, h.symm⟩
      · rw [if_neg hp] at h; simp at h
  · rintro ⟨qs, h1, hp, hq⟩
    simp only [h1]
    rw [if_pos hp]
    exact congrArg some hq.symm

/-- 头结论一致：摘要的 conc 即树根结论（观察等价只读头部）。 -/
theorem summarize_conc {A : Type} [DecidableEq A] (t : STree A) (q : Summ A)
    (h : summarize t = some q) : q.conc = headT t := by
  cases t with
  | sLeaf b a src =>
      cases b with
      | false =>
          simp only [summarize] at h
          injection h with hq
          rw [← hq]; rfl
      | true =>
          simp only [summarize] at h
          injection h with hq
          rw [← hq]; rfl
  | sNode r fs =>
      obtain ⟨qs, _, _, hq⟩ := (summarize_node_iff r fs q).mp h
      simp [hq, headT]

/-! ## 四、δ 的读数定理（Last 策略与位点累积） -/

/-- 可废止根的 Last 策略：last 恰为单点 {rid}（§4.2）。 -/
theorem delta_last_defeasible {A : Type} (r : SRule A) (qs : List (Summ A))
    (hd : r.mode = .defeasible) (x : A) :
    x ∈ (deltaS r qs).lastI ↔ x = r.rid := by
  simp [deltaS, lastOfRule, hd]

/-- 严格根的 Last 策略：last 为子 last 的并（§4.2）。 -/
theorem delta_last_strict {A : Type} (r : SRule A) (qs : List (Summ A))
    (hs : r.mode = .strictS) (x : A) :
    x ∈ (deltaS r qs).lastI ↔ ∃ q ∈ qs, x ∈ q.lastI := by
  simp [deltaS, lastOfRule, hs]

/-- 位点累积（§4.2）：δ 的位点 = 自身位点 ∪ 子位点。 -/
theorem delta_sites {A : Type} (r : SRule A) (qs : List (Summ A)) (s : SiteSum A) :
    s ∈ (deltaS r qs).sites ↔
      s = ownSiteOf r qs ∨ ∃ q ∈ qs, s ∈ q.sites := by
  simp [deltaS]

/-- 自身位点是规则形，携带 r 的头/模式/实例/守卫槽。 -/
theorem own_site_typed {A : Type} (r : SRule A) (qs : List (Summ A)) :
    ∃ la : List A, ownSiteOf r qs = .ruleS r.head r.mode r.rid la r.guards :=
  ⟨lastOfRule r qs, rfl⟩

/-- δ 的头结论即规则头（读数）。 -/
theorem delta_conc {A : Type} (r : SRule A) (qs : List (Summ A)) :
    (deltaS r qs).conc = r.head := rfl

/-- Last 策略叶侧：普通叶 last 为 ∅（§4.2）。 -/
theorem leaf_last_empty {A : Type} (a src : A) :
    (leafOrdSum a src).lastI = [] := rfl

/-- 普通叶自身是可攻击位点。 -/
theorem leaf_site_mem {A : Type} (a src : A) :
    SiteSum.leafS a ∈ (leafOrdSum a src).sites := by
  simp [leafOrdSum]

/-- 豁免叶不是可攻击位置（axiom/exempt 不产位点）。 -/
theorem exempt_site_free {A : Type} (a src : A) (s : SiteSum A) :
    s ∉ (leafExemptSum a src).sites := by
  simp [leafExemptSum]

/-! ## 五、饱和：高度索引归纳与见证健全性 -/

/-- 高度索引饱和谓词：叶种子在任意层；step 的子摘要住在 n 层、
父摘要住在 n+1 层（高度索引修复"成员假设无 IH"的归纳死结）。 -/
inductive SaturatedN {A : Type} (Γ : List (SRule A)) : ℕ → Summ A → Prop
  | leafOrd (n : ℕ) (a src : A) : SaturatedN Γ n (leafOrdSum a src)
  | leafExempt (n : ℕ) (a src : A) : SaturatedN Γ n (leafExemptSum a src)
  | step (n : ℕ) (r : SRule A) (hr : r ∈ Γ) (qs : List (Summ A))
      (hprem : qs.map Summ.conc = r.premises)
      (hch : ∀ q ∈ qs, SaturatedN Γ n q) :
      SaturatedN Γ (n + 1) (deltaS r qs)

/-- 无高度包装的饱和谓词。 -/
def Saturated {A : Type} (Γ : List (SRule A)) (q : Summ A) : Prop :=
  ∃ n, SaturatedN Γ n q

/-- 选择累积：每个子摘要有实现树 ⟹ 存在林其摘要恰为该列表。 -/
theorem summs_accumulate {A : Type} [DecidableEq A] :
    ∀ (qs : List (Summ A)), (∀ q ∈ qs, ∃ t, summarize t = some q) →
      ∃ fs, summs fs = some qs := by
  intro qs
  induction qs with
  | nil => intro _; exact ⟨.fNil, by simp [summs]⟩
  | cons q qs ih =>
      intro h
      obtain ⟨t, ht⟩ := h q (by simp)
      obtain ⟨fs, hfs⟩ := ih (fun q' hq' => h q' (by simp [hq']))
      exact ⟨.fCons t fs, by simp only [summs, ht, hfs]⟩

/-- 饱和见证健全性（反射核心）：每个饱和摘要都有实现树——
饱和集里没有幻影摘要。 -/
theorem saturatedN_witness {A : Type} [DecidableEq A] (Γ : List (SRule A)) :
    ∀ n q, SaturatedN Γ n q → ∃ t, summarize t = some q := by
  intro n
  induction n with
  | zero =>
      intro q h
      cases h with
      | leafOrd a src => exact ⟨.sLeaf true a src, by simp [summarize]⟩
      | leafExempt a src => exact ⟨.sLeaf false a src, by simp [summarize]⟩
  | succ n ih =>
      intro q h
      cases h with
      | leafOrd a src => exact ⟨.sLeaf true a src, by simp [summarize]⟩
      | leafExempt a src => exact ⟨.sLeaf false a src, by simp [summarize]⟩
      | step r _ qs hprem hch =>
          have hreal : ∀ q ∈ qs, ∃ t, summarize t = some q :=
            fun q hq => ih q (hch q hq)
          obtain ⟨fs, hfs⟩ := summs_accumulate qs hreal
          refine ⟨.sNode r fs, ?_⟩
          rw [summarize_node_iff]
          exact ⟨qs, hfs, hprem, rfl⟩

theorem saturated_witness {A : Type} [DecidableEq A] (Γ : List (SRule A))
    {q : Summ A} (h : Saturated Γ q) : ∃ t, summarize t = some q := by
  obtain ⟨n, hn⟩ := h
  exact saturatedN_witness Γ n q hn

/-- 最小闭包（最小不动点纪律）：任何含叶种子且对 δ 封闭的集合
都包含全部饱和摘要——Saturated 是这样的最小集合
（Python `saturate_summaries` 的 least fixed point 读数）。 -/
theorem saturatedN_into_closed {A : Type} (Γ : List (SRule A)) (S : List (Summ A))
    (hleavesOrd : ∀ a src, leafOrdSum a src ∈ S)
    (hleavesEx : ∀ a src, leafExemptSum a src ∈ S)
    (hstep : ∀ r ∈ Γ, ∀ qs : List (Summ A), qs.map Summ.conc = r.premises →
      (∀ q ∈ qs, q ∈ S) → deltaS r qs ∈ S) :
    ∀ n q, SaturatedN Γ n q → q ∈ S := by
  intro n
  induction n with
  | zero =>
      intro q h
      cases h with
      | leafOrd a src => exact hleavesOrd a src
      | leafExempt a src => exact hleavesEx a src
  | succ n ih =>
      intro q h
      cases h with
      | leafOrd a src => exact hleavesOrd a src
      | leafExempt a src => exact hleavesEx a src
      | step r hr qs hprem hch =>
          exact hstep r hr qs hprem (fun q hq => ih q (hch q hq))

end JurisLean.Seams.UnifiedSummary
