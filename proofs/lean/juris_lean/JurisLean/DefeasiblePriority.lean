import JurisLean.LegalIds

/-!
中文说明：M4 P03 defeasible priority。rule/argument priority、
conditional priority 与 priority cycle。priority cycle 产生规定的
undecided/blocked 语义，不能依迭代顺序任意决胜。
-/

namespace JurisLean

/-- 中文说明：规则优先级对（higher 击败 lower）。 -/
abbrev PriorityPair := LegalId .rule × LegalId .rule

/-- 中文说明：conditional priority：携带激活条件句柄。 -/
structure ConditionalPriority where
  higher : LegalId .rule
  lower : LegalId .rule
  condition : String
  active : Bool
deriving DecidableEq

/-- 中文说明：给定优先级集合中 hi > lo 是否成立。 -/
def hasPriority (ps : List PriorityPair) (hi lo : LegalId .rule) : Prop :=
  (hi, lo) ∈ ps

/-- 中文说明：优先级解析：双向优先级（环）返回 none（undecided），
不允许按列表顺序任意决胜。 -/
def resolvePriority (ps : List PriorityPair) (a b : LegalId .rule) :
    Option (LegalId .rule) :=
  if (a, b) ∈ ps ∧ (b, a) ∈ ps then
    none
  else if (a, b) ∈ ps then
    some a
  else if (b, a) ∈ ps then
    some b
  else
    none

/-- 中文说明：priority cycle（二元环）判定。 -/
def hasPriorityCycle (ps : List PriorityPair) (a b : LegalId .rule) : Prop :=
  (a, b) ∈ ps ∧ (b, a) ∈ ps

/-- 中文证明：priority cycle 产生 undecided（无决胜者）。 -/
theorem priority_cycle_yields_undecided (ps : List PriorityPair)
    (a b : LegalId .rule) (hcycle : hasPriorityCycle ps a b) :
    resolvePriority ps a b = none := by
  dsimp [resolvePriority]
  split
  · rfl
  · contradiction

/-- 中文证明：单向优先级决胜 higher。 -/
theorem single_direction_priority_wins (ps : List PriorityPair)
    (a b : LegalId .rule) (hab : (a, b) ∈ ps) (hnotrev : (b, a) ∉ ps) :
    resolvePriority ps a b = some a := by
  dsimp [resolvePriority]
  by_cases hfwd : (a, b) ∈ ps
  · by_cases hcyc2 : (b, a) ∈ ps
    · exfalso
      exact hnotrev hcyc2
    · simp [hfwd, hcyc2]
  · exfalso
    exact hfwd hab

/-- 中文证明：无优先级证据时不得默认产生胜者。 -/
theorem missing_priority_no_winner (ps : List PriorityPair)
    (a b : LegalId .rule) (hn1 : (a, b) ∉ ps) (hn2 : (b, a) ∉ ps) :
    resolvePriority ps a b = none := by
  dsimp [resolvePriority]
  by_cases hcyc : (a, b) ∈ ps ∧ (b, a) ∈ ps
  · rcases hcyc with ⟨h1a, _⟩
    exact (hn1 h1a).elim
  · by_cases hf : (a, b) ∈ ps
    · exact (hn1 hf).elim
    · by_cases hr : (b, a) ∈ ps
      · exact (hn2 hr).elim
      · simp [hf, hr]

/-- 中文证明：conditional priority 未激活时不参与决胜（建模为过滤）。 -/
def activeConditionalPriorities (cps : List ConditionalPriority) :
    List PriorityPair :=
  cps.filterMap (fun cp => if cp.active then some (cp.higher, cp.lower) else none)

theorem inactive_conditional_priority_excluded (cp : ConditionalPriority)
    (hinactive : cp.active = false) :
    (cp.higher, cp.lower) ∉ activeConditionalPriorities [cp] := by
  simp [activeConditionalPriorities, hinactive]

end JurisLean
