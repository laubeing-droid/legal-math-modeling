import JurisLean.LegalIds
import JurisLean.TypedAttack

/-!
中文说明：M4 P03 argument compiler 合同。expected attack 不遗漏、
spurious attack 不产生、方向不反转。checker 只依赖声明的 expected
集合与输入 witness，不调用编译器实现。
-/

namespace JurisLean

/-- 中文说明：编译产物：arguments 与 typed attacks。 -/
structure CompiledAAF where
  arguments : List (LegalId .argument)
  attacks : List TypedAttack
deriving DecidableEq

/-- 中文说明：无遗漏：每个 expected attack 都出现在产物中。 -/
def noOmittedAttacks (expected : List TypedAttack) (out : CompiledAAF) : Prop :=
  ∀ e ∈ expected, e ∈ out.attacks

/-- 中文说明：无伪造：产物的每个 attack 都在 expected 中。 -/
def noSpuriousAttacks (expected : List TypedAttack) (out : CompiledAAF) : Prop :=
  ∀ a ∈ out.attacks, a ∈ expected

/-- 中文说明：方向保持：产物中与 expected 反向且同 witness 的 attack
必须就是 expected 中的同一 attack（否则即为方向反转）。 -/
def directionPreserved (expected : List TypedAttack) (out : CompiledAAF) : Prop :=
  ∀ a ∈ out.attacks, ∀ e ∈ expected,
    a.attacker = e.target ∧ a.target = e.attacker ∧ a.witness = e.witness →
      a = e

/-- 中文说明：expected 集合自身不含反向重复对。 -/
def reversalFree (expected : List TypedAttack) : Prop :=
  ∀ a ∈ expected, ∀ e ∈ expected,
    a.attacker = e.target ∧ a.target = e.attacker ∧ a.witness = e.witness →
      a = e

/-- 中文说明：编译合同同时满足三项。 -/
def compilationContractOk (expected : List TypedAttack) (out : CompiledAAF) : Prop :=
  noOmittedAttacks expected out ∧
    noSpuriousAttacks expected out ∧
      directionPreserved expected out

/-- 中文证明：遗漏一个 expected attack 违反合同。 -/
theorem omitted_attack_breaks_contract {expected : List TypedAttack}
    {out : CompiledAAF} (e : TypedAttack) (hexp : e ∈ expected)
    (habsent : e ∉ out.attacks) :
    ¬ noOmittedAttacks expected out := by
  intro hno
  exact habsent (hno e hexp)

/-- 中文证明：伪造 attack 违反合同。 -/
theorem spurious_attack_breaks_contract {expected : List TypedAttack}
    {out : CompiledAAF} (a : TypedAttack) (hout : a ∈ out.attacks)
    (hunknown : a ∉ expected) :
    ¬ noSpuriousAttacks expected out := by
  intro hns
  exact hunknown (hns a hout)

/-- 中文证明：方向反转的 attack 违反方向保持。 -/
theorem reversed_edge_breaks_direction {expected : List TypedAttack}
    {out : CompiledAAF} (a e : TypedAttack) (ha : a ∈ out.attacks)
    (he : e ∈ expected) (hrev1 : a.attacker = e.target)
    (hrev2 : a.target = e.attacker) (hwit : a.witness = e.witness)
    (hne : a ≠ e) :
    ¬ directionPreserved expected out := by
  intro hdp
  exact hne (hdp a ha e he ⟨hrev1, hrev2, hwit⟩)

/-- 中文证明：expected 无反向重复时，恒等产物满足完整合同。 -/
theorem identity_translation_satisfies_contract (expected : List TypedAttack)
    (hfree : reversalFree expected) :
    compilationContractOk expected { arguments := [], attacks := expected } := by
  dsimp [compilationContractOk]
  refine ⟨fun _ h => h, fun _ h => h, ?_⟩
  intro a ha e he hrev
  exact hfree a ha e he hrev

/-- 中文证明：产物 attacks 为空而 expected 非空时合同失败。 -/
theorem empty_output_with_expectations_fails
    (expected : List TypedAttack) (e : TypedAttack) (hexp : e ∈ expected) :
    ¬ noOmittedAttacks expected { arguments := [], attacks := [] } := by
  intro hno
  have hmem : e ∈ ([] : List TypedAttack) := hno e hexp
  cases hmem

end JurisLean
