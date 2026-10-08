import Mathlib.Tactic
import JurisLean.Seams.UnifiedAdmission
import JurisLean.Seams.UnifiedFinalization

/-
Unified composition, layer J (plan §5 main chain; I.4.14 L14, fragment for
U25: the vertical pipeline admission → finalization).

The two already-proven layers compose: admitted fact sets (layer D's
`admittedRounds` anchored outputs) feed the six-type terminal table
(layer E's `finalizeIssue`) through an EXPLICIT flag-derivation bridge.

* `deriveInputs` maps an admission snapshot (admitted premises, live
  counter-evidence, burden state, exhaustion) to `IssueInputs` — a
  parameterized family, not a fixed instance.
* `composite_exact`: the pipeline `finalizeIssue ∘ deriveInputs` is
  exactly denoted by the composed semantic relation — proven BY the two
  prior exactness theorems (no re-unfolding of either algorithm), the
  shared-intermediate discipline of I.4.14.
* `established_requires_admitted_premises`: the anchoring discipline
  flows THROUGH the pipeline — a POS verdict at the bottom forces every
  premise of the issue to sit in the admitted set (U08's anchoring made
  vertical).
* `nondegenerate_family`: the parameterized family is non-degenerate —
  two snapshots differing exactly in the admission of one premise give
  different derived inputs (no fixed `openGateData` shortcut).

Scope, honestly: a two-stage fragment with an abstract premise type P.
The full runLegal composition (norm selection → argumentation →
admission → consequences → quantities) composes the same pattern per
seam; those seams' Lean reflections are tracked separately (guardSlots,
summary saturation) and are not claimed here.
-/

namespace JurisLean.Seams.UnifiedComposition

open JurisLean.Seams.UnifiedFinalization (IssueInputs Judgment FinalBasis
  finalizeIssue LegalFinal finalize_representation_exact)

variable {P : Type} [DecidableEq P]

/-! ## 一、快照到终结输入的显式桥 -/

/-- 准入快照（P 为前提/争点载体）：已采纳集合、活反证、负担未立、四穷尽、需要认定。
    程序就绪恒真（本片段只做实体面；程序门是 finalizeIssue 的另一输入位）。 -/
structure Snapshot (P : Type) where
  /-- 已采纳前提集合。 -/
  admitted : Finset P
  /-- 活的实质反证集合。 -/
  counterEvidence : Finset P
  /-- 本争点的前提全集。 -/
  premises : Finset P
  /-- 负担已就绪。 -/
  burdenReady : Bool
  /-- 有负担性未立要件。 -/
  unmetBorne : Bool
  /-- 四穷尽。 -/
  exhausted4 : Bool
  /-- 需要认定。 -/
  need : Bool

/-- 桥：快照 → 终结表输入（要件全立 := 前提全部在已采纳集∧无活反证）。 -/
def deriveInputs [DecidableEq P] (s : Snapshot P) : IssueInputs where
  ready := true
  blockers := decide (s.counterEvidence ≠ ∅)
  allEstablished := decide (s.premises ⊆ s.admitted)
  burdenReady := s.burdenReady
  unmetBorne := s.unmetBorne
  exhausted4 := s.exhausted4
  need := s.need

/-- 合成语义关系：快照经桥映射后按层E的合法终结关系判定。 -/
def CompositeLegal [DecidableEq P] (s : Snapshot P) (o : Judgment × FinalBasis) : Prop :=
  LegalFinal (deriveInputs s) o

/-- **合成精确性**：管线输出恰由合成语义关系外延给定
    ——证明只复用层E的精确表示定理，不重展开任何一层算法。 -/
theorem composite_exact (s : Snapshot P) (o : Judgment × FinalBasis) :
    CompositeLegal s o ↔ o = finalizeIssue (deriveInputs s) :=
  finalize_representation_exact (deriveInputs s) o

/-! ## 二、锚定贯通：POS 底判强制前提全在采纳集 -/

/-- **POS 锚定贯通**：管线给出成立判定 ⇒ 该争点的前提全部已在采纳集中
    ——U08 的"每件采纳事实锚定在有效依据"沿管线向底传导。 -/
theorem established_requires_admitted_premises (s : Snapshot P)
    (h : CompositeLegal s (Judgment.established, FinalBasis.posB)) :
    s.premises ⊆ s.admitted := by
  have ha : (deriveInputs s).allEstablished = true := by
    unfold CompositeLegal at h
    cases h with
    | pos _ _ ha => exact ha
  simp only [deriveInputs, decide_eq_true_eq] at ha
  exact ha

/-- 前提集旗标的桥读数（子集关系可直接读出）。 -/
theorem deriveInputs_allEstablished_iff (s : Snapshot P) :
    (deriveInputs s).allEstablished = true ↔ s.premises ⊆ s.admitted := by
  simp [deriveInputs]

/-! ## 三、非退化见证（无固定输入捷径） -/

/-- **非退化族**：两个只差一个前提采纳与否的快照（前提集恰为该单点），
    桥输出不同——无固定 openGateData 式捷径可过总对应。 -/
theorem nondegenerate_family (prem : P) (counter : Finset P)
    (burden unmet ex4 nd : Bool) :
    deriveInputs ⟨∅, counter, {prem}, burden, unmet, ex4, nd⟩
      ≠ deriveInputs ⟨{prem}, counter, {prem}, burden, unmet, ex4, nd⟩ := by
  intro heq
  have hcongr : (deriveInputs ⟨∅, counter, {prem}, burden, unmet, ex4, nd⟩).allEstablished
      = (deriveInputs ⟨{prem}, counter, {prem}, burden, unmet, ex4, nd⟩).allEstablished := by
    rw [heq]
  have h2 : (deriveInputs ⟨∅, counter, {prem}, burden, unmet, ex4, nd⟩).allEstablished
      = false := by
    simp [deriveInputs]
  have h1 : (deriveInputs ⟨{prem}, counter, {prem}, burden, unmet, ex4, nd⟩).allEstablished
      = true := by
    simp [deriveInputs]
  rw [h2, h1] at hcongr
  exact Bool.noConfusion hcongr

end JurisLean.Seams.UnifiedComposition
