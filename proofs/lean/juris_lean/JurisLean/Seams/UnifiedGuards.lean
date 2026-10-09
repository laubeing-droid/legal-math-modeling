import Mathlib.Tactic

/-
Unified guard slots, the full field structure (plan §4.3; main doc
§8.2 leftover "guardSlots 完整字段 Lean 化").

Python contract of record:
`tools/unified_math_v2/unified/argument_grammar.py` —
`GUARD_KINDS = {exception, authority, scope, procedure}`,
`GuardSlot(rule_instance, kind, slot, scope)`, the two
`GrammarRule.__post_init__` checks (own-instance, known-kind), and
`GuardSlot.atom() = gate_blocked:{inst}:{kind}:{slot}`.

Layer C (`UnifiedArgumentation.lean`) already factorized gate defeats
over an ENV-CARRIED opaque perimeter `GatePerimeter A = Rul A → List A`;
what it deliberately did not carry is the field structure of the guards
themselves.  This module Lean-izes exactly that structure with the
kind / slot / scope distinction:

1. KIND — the four-element `GuardKind` whitelist (a Lean constructor
   can name no other kind: the Python `unknown guard kind` rejection
   becomes the type itself); `attackOfGuardKind` maps each guard kind
   to its gate attack kind injectively, so a slot fires exactly one
   kind and never another (§4.3 typed-edge discipline).
2. SLOT — atom identity reads (ruleInst, kind, slot): any two of the
   three differing forces distinct atoms (`atom_ne_of_kind_ne`,
   `atom_ne_of_slot_ne`, `atom_ne_of_inst_ne`).
3. SCOPE — the declared scope fields are carried (`scopeFields`) but
   NEVER enter atom identity (`atom_eq_of_scope_change`,
   `atom_scope_free`): in Python `atom()` reads no scope; scope is
   declared metadata for downstream policy, not attack identity.

Own-instance well-formedness (`GuardsOwnInstance`, the Python
"guard slot must name its own rule instance" check) is load-bearing:
`foreign_guard_not_in_perimeter` — a slot naming a foreign instance
never lands in a rule's own perimeter, so proving its gate-block atom
blocks no guarded use of that rule.

Relation to Layer C: `GuardedRule.perimeter` is the concrete,
field-structured instance of Layer C's abstract env-carried
`GatePerimeter`; once rules are typed so that the perimeter is read at
`GateAtom I`, the Layer C biconditional `gateDefeat_iff_summaryDefeat`
governs the defeats these guards license.  That lifting itself is not
re-proved here and not claimed.

STATUS: proved theorems pending their CI compile round (module check
then root then full release); no `sorry`/`admit`/custom `axiom`/
`: True :=`/`native_decide` appears here.
-/

namespace JurisLean.Seams.UnifiedGuards

/-! ## 一、守卫类白名单（GUARD_KINDS 的类型化） -/

/-- 四守卫类（§4.3 gate 攻击的 exception/authority/scope/procedure）。
Lean 构造子即白名单——Python 侧的 unknown guard kind 拒绝在类型层成立。 -/
inductive GuardKind where
  | exception | authority | gscope | procedure
deriving DecidableEq

/-- Python 的 `GUARD_KINDS` 字符串集，按 `guardKindName` 命中。 -/
def guardKindsList : List String :=
  ["exception", "authority", "scope", "procedure"]

/-- 守卫类的 Python 字符串名。 -/
def guardKindName : GuardKind → String
  | .exception => "exception"
  | .authority => "authority"
  | .gscope => "scope"
  | .procedure => "procedure"

/-- 每个守卫类的名字都在 GUARD_KINDS 白名单内。 -/
theorem guardKindName_mem (k : GuardKind) :
    guardKindName k ∈ guardKindsList := by
  cases k <;> simp [guardKindName, guardKindsList]

/-- 守卫类名字互异：不同的类不共享同一个 Python 字符串名。 -/
theorem guardKindName_injective : Function.Injective guardKindName := by
  intro a b h
  cases a <;> cases b
  all_goals simp only [guardKindName] at h
  all_goals first
    | rfl
    | exact absurd h (by decide)

/-! ## 二、守卫槽与门原子的完整字段结构 -/

/-- 守卫槽 g = (Inst, kind, slot) 连同其声明的 scope 字段——
Python `GuardSlot` 的完整四字段结构（§4.3 表）。 -/
structure GuardSlot (I : Type) where
  ruleInst : I
  kind : GuardKind
  slot : String
  scopeFields : List String
deriving DecidableEq

/-- 门原子的身份三元组：ruleInst/kind/slot——正是 Python
`atom()` 读的三个字段；scope 刻意不在其中。 -/
structure GateAtom (I : Type) where
  ruleInst : I
  kind : GuardKind
  slot : String
deriving DecidableEq

/-- `GuardSlot.atom()`：槽到其门原子的投影（scope 被丢弃）。 -/
def GuardSlot.atom (g : GuardSlot I) : GateAtom I :=
  ⟨g.ruleInst, g.kind, g.slot⟩

/-- 原子身份 iff：两槽同原子 ⟺ ruleInst、kind、slot 逐字段相等。
右端刻意不含 scopeFields——原子相等对 scope 无任何约束。 -/
theorem atom_eq_iff {I : Type} [DecidableEq I] (g₁ g₂ : GuardSlot I) :
    g₁.atom = g₂.atom ↔
      g₁.ruleInst = g₂.ruleInst ∧ g₁.kind = g₂.kind ∧ g₁.slot = g₂.slot := by
  simp only [GuardSlot.atom, GateAtom.mk.injEq]

/-- kind 区分：同实例同槽名、守卫类不同 ⟹ 原子必不同
（authority 阻断与 exception 阻断是不同的攻击，不共享原子）。 -/
theorem atom_ne_of_kind_ne {I : Type} [DecidableEq I] {i : I} {s : String}
    {k₁ k₂ : GuardKind} {σ₁ σ₂ : List String} (hne : k₁ ≠ k₂) :
    (⟨i, k₁, s, σ₁⟩ : GuardSlot I).atom ≠ (⟨i, k₂, s, σ₂⟩ : GuardSlot I).atom := by
  intro h
  have h3 := (atom_eq_iff _ _).mp h
  exact hne h3.2.1

/-- slot 区分：同实例同类、槽名不同 ⟹ 原子必不同
（exception"上诉审"与 exception"管辖异议"是不同槽）。 -/
theorem atom_ne_of_slot_ne {I : Type} [DecidableEq I] {i : I} {k : GuardKind}
    {s₁ s₂ : String} {σ₁ σ₂ : List String} (hne : s₁ ≠ s₂) :
    (⟨i, k, s₁, σ₁⟩ : GuardSlot I).atom ≠ (⟨i, k, s₂, σ₂⟩ : GuardSlot I).atom :=
  fun h => hne ((atom_eq_iff _ _).mp h).2.2

/-- 实例区分：守卫类与槽名相同、规则实例不同 ⟹ 原子必不同
（他规则的同名守卫不是本规则的守卫）。 -/
theorem atom_ne_of_inst_ne {I : Type} [DecidableEq I] {i₁ i₂ : I} {k : GuardKind}
    {s : String} {σ₁ σ₂ : List String} (hne : i₁ ≠ i₂) :
    (⟨i₁, k, s, σ₁⟩ : GuardSlot I).atom ≠ (⟨i₂, k, s, σ₂⟩ : GuardSlot I).atom :=
  fun h => hne ((atom_eq_iff _ _).mp h).1

/-- scope 不进身份（方向一）：scope 字段任意改写，原子分毫不动。 -/
theorem atom_eq_of_scope_change {I : Type} [DecidableEq I] (i : I) (k : GuardKind)
    (s : String) (σ₁ σ₂ : List String) :
    (⟨i, k, s, σ₁⟩ : GuardSlot I).atom = (⟨i, k, s, σ₂⟩ : GuardSlot I).atom :=
  rfl

/-- scope 不进身份（方向二）：既有原子相等后，再改任一槽的 scope
原子仍相等——scope 对阻断身份零约束（它是给下游政策读的声明性元数据）。 -/
theorem atom_scope_free {I : Type} [DecidableEq I] {g₁ g₂ : GuardSlot I}
    (h : g₁.atom = g₂.atom) (σ : List String) :
    g₁.atom = ({ g₂ with scopeFields := σ } : GuardSlot I).atom := by
  rw [h]
  rfl

/-! ## 三、守卫类到攻击类的单射（typed-edge 纪律） -/

/-- 四类 gate 攻击（Python AttackKind 的 EXCEPTION/AUTHORITY/SCOPE/PROCEDURE）。 -/
inductive GateAttackKind where
  | gException | gAuthority | gScope | gProcedure
deriving DecidableEq

/-- §4.3 的 kind→攻击类映射（Python 的字典
exception→EXCEPTION 等四行）。 -/
def attackOfGuardKind : GuardKind → GateAttackKind
  | .exception => .gException
  | .authority => .gAuthority
  | .gscope => .gScope
  | .procedure => .gProcedure

/-- 映射单射：不同守卫类永不落到同一攻击类。 -/
theorem attackOfGuardKind_injective : Function.Injective attackOfGuardKind := by
  intro a b h
  cases a <;> cases b
  all_goals simp only [attackOfGuardKind] at h
  all_goals first
    | rfl
    | exact absurd h (by decide)

/-- 一个守卫槽只发自己那一类的 gate 攻击，绝不冒充另一类。 -/
theorem guard_fires_only_own_kind {k₁ k₂ : GuardKind} (hne : k₁ ≠ k₂) :
    attackOfGuardKind k₁ ≠ attackOfGuardKind k₂ :=
  fun h => hne (attackOfGuardKind_injective h)

/-! ## 四、守卫规则的 own-instance 良构与周界 -/

/-- 带守卫的规则（Python `GrammarRule` 的守卫面：实例名、头、守卫槽表）。 -/
structure GuardedRule (I : Type) where
  ruleId : I
  head : I
  guardSlots : List (GuardSlot I)

/-- Python `__post_init__` 检查一：槽必须指名自己所在规则的实例。 -/
def GuardsOwnInstance (r : GuardedRule I) : Prop :=
  ∀ g ∈ r.guardSlots, g.ruleInst = r.ruleId

/-- 规则的门周界：其守卫槽原子的有限列表——层C 抽象 GatePerimeter
在本字段结构载体的具体实例。 -/
def GuardedRule.perimeter (r : GuardedRule I) : List (GateAtom I) :=
  r.guardSlots.map GuardSlot.atom

/-- 周界成员资格的逐槽刻画。 -/
theorem atom_mem_perimeter_iff {I : Type} (r : GuardedRule I) (a : GateAtom I) :
    a ∈ r.perimeter ↔ ∃ g ∈ r.guardSlots, g.atom = a := by
  simp [GuardedRule.perimeter, List.mem_map]

/-- 自家守卫的原子必在自家周界内。 -/
theorem own_guard_atom_mem_perimeter {I : Type} (r : GuardedRule I)
    {g : GuardSlot I} (hg : g ∈ r.guardSlots) :
    g.atom ∈ r.perimeter :=
  (atom_mem_perimeter_iff r g.atom).mpr ⟨g, hg, rfl⟩

/-- own-instance 检查是承重的：指名外国实例的守卫永不落入本规则的
周界——证明它的门原子阻断不了本规则的任何受守卫使用。 -/
theorem foreign_guard_not_in_perimeter {I : Type} [DecidableEq I]
    {r : GuardedRule I} (hval : GuardsOwnInstance r) {g : GuardSlot I}
    (hforeign : g.ruleInst ≠ r.ruleId) :
    g.atom ∉ r.perimeter := by
  intro hmem
  obtain ⟨g', hg', hatom⟩ := (atom_mem_perimeter_iff r g.atom).mp hmem
  have h1 := ((atom_eq_iff g' g).mp hatom).1
  rw [hval g' hg'] at h1
  exact hforeign h1.symm

/-! ## 五、字面量钉死（kind / slot / scope 三分各有可判读数） -/

/-- kind 区分的字面量钉死：同规则同槽名，exception 与 authority
的原子可判定地不相等。 -/
theorem exception_vs_authority_atoms_differ :
    (⟨"r1", GuardKind.exception, "appeal", ["civil"]⟩ : GuardSlot String).atom ≠
      (⟨"r1", GuardKind.authority, "appeal", ["civil"]⟩ : GuardSlot String).atom := by
  apply atom_ne_of_kind_ne
  intro h
  cases h

/-- slot 区分的字面量钉死：同规则同类，槽名 appeal 与
counterclaim 的原子可判定地不相等。 -/
theorem slot_names_distinguish_atoms :
    (⟨"r1", GuardKind.exception, "appeal", []⟩ : GuardSlot String).atom ≠
      (⟨"r1", GuardKind.exception, "counterclaim", []⟩ : GuardSlot String).atom := by
  apply atom_ne_of_slot_ne
  decide

/-- scope 零约束的字面量钉死：scope 从 ["civil"] 换成
["criminal", "administrative"]，原子逐字节相等。 -/
theorem scope_change_keeps_concrete_atom :
    (⟨"r1", GuardKind.exception, "appeal", ["civil"]⟩ : GuardSlot String).atom =
      (⟨"r1", GuardKind.exception, "appeal",
        ["criminal", "administrative"]⟩ : GuardSlot String).atom :=
  rfl

/-- own-instance 检查非空洞的字面量钉死：指名 art32 的守卫挂在
art31 规则上，良构检查可判定地拒绝。 -/
theorem foreign_slot_fails_own_instance :
    ¬ GuardsOwnInstance
      ({ ruleId := ("art31" : String), head := "damage",
         guardSlots := [⟨"art32", GuardKind.authority, "tribunal", []⟩] } :
        GuardedRule String) := by
  intro h
  have h1 := h _ List.mem_cons_self
  exact absurd h1 (by decide)

end JurisLean.Seams.UnifiedGuards
