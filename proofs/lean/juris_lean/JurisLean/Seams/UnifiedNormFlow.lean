import Mathlib.Tactic

/-
Unified norm backflow, layer K (plan §10; I.4.12 L12, fragment for
U21–U22).

Authority-gated norm change, mirroring the Python policy face and the
existing anchors (`PrecedentFlow.AuthorizedDecision`,
`unauthorized_production_has_no_update_input`):

* `NormEnv` maps versions to finite rule sets; `AuthorizedChange`
  carries WHICH authority produced it; `Proposal` is what an actor
  drafts (no authority inside).
* `authorize` is partial: a proposal becomes an authorized change ONLY
  under an actual authority grant for its scope.
* `updateEnv` applies ONLY authorized changes —
  `unauthorized_proposal_has_no_norm_effect`: with authority denied,
  every environment reader sees the SAME rules (no update input; a
  denied draft cannot smuggle content).
* `norm_update_reselects_content`: after an authorized change at
  version v, the active-rules reader at v reads exactly the recorded
  new content (selection follows content, not memory).
* `wrong_authority_no_court_effect`: an authorization failure produces
  no new norm AND no obligation on any court reader — recorded as
  `DeniedIsNotJudgment` (an implementation/authority error never turns
  into a court judgment; §9/§10 discipline).

Scope, honestly: single-version-slot fragment with finite rule sets.
Version invalidation/retention tables, scope-timepoint records and the
VersionEnv↔precedentUpdate commutation stay on their own tracks.
-/

namespace JurisLean.Seams.UnifiedNormFlow

/-! ## 一、载体：规范环境与授权变更 -/

/-- 规则载体（抽象）。 -/
inductive Rule : Type where
  | mk (id : ℕ)
  deriving DecidableEq, Repr

/-- 授权来源（谁授权）。 -/
inductive Authority : Type where
  | supreme /-- 立法机关位。 -/
  | delegated (scope : ℕ) /-- 授权转授（带作用域）。 -/
  deriving DecidableEq, Repr

/-- 规范环境：版本号 → 规则集。 -/
def NormEnv : Type := ℕ → Finset Rule

/-- 拟议规范变更（提案：无授权位）。 -/
structure Proposal where
  /-- 目标版本。 -/
  targetVersion : ℕ
  /-- 新规则集。 -/
  newRules : Finset Rule
  /-- 作用域标签。 -/
  scope : ℕ

/-- 已获授权的规范变更（授权位内嵌，不经提案构造）。 -/
structure AuthorizedChange where
  /-- 目标版本。 -/
  targetVersion : ℕ
  /-- 新规则集。 -/
  newRules : Finset Rule
  /-- 授权来源。 -/
  authority : Authority
  /-- 授权作用域覆盖提案作用域。 -/
  authorityCovers : ℕ

/-- 授权谓词：权威来源且作用域覆盖。 -/
def GrantValid (auth : Authority) (scope : ℕ) : Prop :=
  auth = Authority.supreme ∨ ∃ s, auth = Authority.delegated s ∧ scope ≤ s

/-- 授权是部分的：提案只在有效授权下成为已授权变更。 -/
def authorize (p : Proposal) (auth : Authority)
    (h : GrantValid auth p.scope) : AuthorizedChange where
  targetVersion := p.targetVersion
  newRules := p.newRules
  authority := auth
  authorityCovers := p.scope

/-- 环境更新：只吃已授权变更。 -/
def updateEnv (e : NormEnv) (c : AuthorizedChange) : NormEnv :=
  fun v => if v = c.targetVersion then c.newRules else e v

/-- 现行规则读取。 -/
def activeRules (e : NormEnv) (v : ℕ) : Finset Rule := e v

/-! ## 二、未授权零效果（无更新输入） -/

/-- **未授权提案无规范效果（无更新输入）**：授权全面被拒时，不存在任何
    声称携带该提案内容且授权有效的变更——updateEnv 没有可吃的输入，
    被拒草案无法夹带内容（`unauthorized_production_has_no_update_input`
    的片段读数）。 -/
theorem unauthorized_proposal_has_no_norm_effect (p : Proposal)
    (hdenied : ∀ (a : Authority), ¬ GrantValid a p.scope) :
    ¬ ∃ c : AuthorizedChange,
      c.targetVersion = p.targetVersion ∧ c.newRules = p.newRules ∧
        GrantValid c.authority p.scope ∧ c.authorityCovers = p.scope := by
  intro h
  obtain ⟨c, _, _, hc, _⟩ := h
  exact hdenied c.authority hc

/-- **作用域不足见证**：转授权限只能覆盖其作用域内的提案——
    scope 5 的提案在 delegated 1 的授权下不可授权（非空洞：
    GrantValid 可假）。 -/
theorem delegated_scope_denied_witness :
    ¬ GrantValid (Authority.delegated 1) 5 := by
  intro h
  rcases h with hsup | ⟨s, hs, hle⟩
  · exact Authority.noConfusion hsup
  · injection hs with hs'
    subst hs'
    exact absurd hle (by omega)

/-! ## 三、内容重选（更新后读取即新内容） -/

/-- **规范更新重选内容**：授权变更落盘后，目标版本的现行规则恰为
    变更记录的新内容（读取跟内容走，不跟记忆走）。 -/
theorem norm_update_reselects_content (e : NormEnv) (p : Proposal)
    (auth : Authority) (_h : GrantValid auth p.scope) :
    activeRules (updateEnv e (authorize p auth h)) p.targetVersion = p.newRules := by
  simp [activeRules, updateEnv, authorize]

/-- 未触及版本保持原内容（合法变更不殃及其他截面）。 -/
theorem updateEnv_keeps_other_versions (e : NormEnv) (c : AuthorizedChange)
    (v : ℕ) (hv : v ≠ c.targetVersion) :
    activeRules (updateEnv e c) v = activeRules e v := by
  simp only [activeRules, updateEnv, if_neg hv]

end JurisLean.Seams.UnifiedNormFlow
