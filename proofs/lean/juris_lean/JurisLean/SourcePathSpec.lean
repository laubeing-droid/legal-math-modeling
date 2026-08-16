import JurisLean.LegalIds

/-!
中文说明：M2 P08 来源路径合同。跨文书 source_path 的每条边都有类型、
方向和 witness；断链和未知边失败关闭。retrieval relevance 不蕴含
source authority 或 legal applicability。允许的引用环与非法依赖环分型。
-/

namespace JurisLean

/-- 中文说明：路径边类型。 -/
inductive SourcePathEdgeKind where
  | derivation
  | citation
  | supersession
  | correction
  | retrieval
deriving DecidableEq, Repr

/-- 中文说明：路径边：有向、带 witness。 -/
structure SourcePathEdge where
  fromSnap : LegalId .snapshot
  toSnap : LegalId .snapshot
  kind : SourcePathEdgeKind
  witness : String
deriving DecidableEq

/-- 中文说明：来源路径。 -/
structure SourcePath where
  edges : List SourcePathEdge
deriving DecidableEq

/-- 中文说明：单边 well-formedness：witness 非空且不得自环。 -/
def edgeWellFormed (e : SourcePathEdge) : Prop :=
  e.witness ≠ "" ∧ e.fromSnap ≠ e.toSnap

/-- 中文说明：路径 well-formedness：每条边都 well-formed。 -/
def pathWellFormed (p : SourcePath) : Prop :=
  ∀ e ∈ p.edges, edgeWellFormed e

/-- 中文说明：断链判定：边的端点必须都在已知快照闭包内。 -/
def pathBroken (p : SourcePath) (known : List (LegalId .snapshot)) : Prop :=
  ∃ e ∈ p.edges, ¬ (e.fromSnap ∈ known) ∨ ¬ (e.toSnap ∈ known)

/-- 中文说明：二边依赖环（方向互为反向）。 -/
def pathHasDependencyCycle (p : SourcePath) : Prop :=
  ∃ e ∈ p.edges, ∃ e' ∈ p.edges,
    e.kind ≠ .citation ∧ e'.kind ≠ .citation ∧
      e.fromSnap = e'.toSnap ∧ e.toSnap = e'.fromSnap

/-- 中文说明：retrieval 相关性（检索命中）。 -/
def edgeRetrievalRelevant (e : SourcePathEdge) : Prop :=
  e.kind = .retrieval

/-- 中文说明：source authority 断言：只有非 retrieval 边可以承载。 -/
def edgeCarriesAuthority (e : SourcePathEdge) : Prop :=
  e.kind ≠ .retrieval

/-- 中文证明：retrieval 相关性不蕴含 source authority。 -/
theorem retrieval_not_applicability {e : SourcePathEdge}
    (hrel : edgeRetrievalRelevant e) : ¬ edgeCarriesAuthority e := by
  dsimp [edgeRetrievalRelevant, edgeCarriesAuthority] at hrel ⊢
  intro hauth
  exact hauth hrel

/-- 中文证明：self-loop 边不满足 well-formedness。 -/
theorem self_loop_not_well_formed {e : SourcePathEdge}
    (hloop : e.fromSnap = e.toSnap) : ¬ edgeWellFormed e := by
  intro hwf
  exact hwf.2 hloop

/-- 中文证明：空 witness 边不满足 well-formedness。 -/
theorem empty_witness_not_well_formed {e : SourcePathEdge}
    (hwit : e.witness = "") : ¬ edgeWellFormed e := by
  intro hwf
  exact hwf.1 hwit

/-- 中文证明：断链路径存在未被闭包覆盖的端点。 -/
theorem broken_path_has_uncovered_endpoint {p : SourcePath}
    {known : List (LegalId .snapshot)} (hbroken : pathBroken p known) :
    ∃ e ∈ p.edges, ¬ (e.fromSnap ∈ known) ∨ ¬ (e.toSnap ∈ known) := hbroken

/-- 中文证明：互为反向的两条非 citation 边构成依赖环。 -/
theorem reversed_noncitation_edges_form_cycle
    (e e' : SourcePathEdge)
    (hkind : e.kind ≠ .citation) (hkind' : e'.kind ≠ .citation)
    (hrev1 : e.fromSnap = e'.toSnap) (hrev2 : e.toSnap = e'.fromSnap) :
    pathHasDependencyCycle { edges := [e, e'] } := by
  refine ⟨e, by simp, e', by simp, hkind, hkind', ?_, ?_⟩
  · exact hrev1
  · exact hrev2

/-- 中文证明：citation 类环不作为依赖环处理（允许引用环分型）。 -/
theorem citation_cycle_not_dependency_cycle (e e' : SourcePathEdge)
    (hcite : e.kind = .citation) (hcite' : e'.kind = .citation) :
    ¬ pathHasDependencyCycle { edges := [e, e'] } := by
  intro hcycle
  rcases hcycle with ⟨a, hamem, b, hbmem, hakind, _, _, _⟩
  simp at hamem hbmem
  rcases hamem with ha | ha <;> rcases hbmem with hb | hb <;>
    simp_all

end JurisLean
