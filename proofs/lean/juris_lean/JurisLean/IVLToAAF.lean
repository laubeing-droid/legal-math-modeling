import JurisLean.LegalIVL
import JurisLean.TypedAttack

/-!
中文说明：M6 IVL -> AAF target。argument 以规则结论为节点，attack 从
IVL attack 规格派生；每个 attack 保留输入 witness，无 witness 不产边。
-/

namespace JurisLean

/-- 中文说明：AAF target：节点（结论）与 typed attacks。 -/
structure AAFTarget where
  nodes : List String
  attacks : List TypedAttack
deriving DecidableEq

/-- 中文说明：witnessed attack lowering：只保留有 witness 的 attack。 -/
def lowerWitnessedAttack (a : IVLAttackSpec) : Option TypedAttack :=
  if a.inputWitness ≠ "" then
    some
      {
        attacker := { payload := a.attackerConclusion },
        target := { payload := a.targetConclusion },
        kind := .rebuttal,
        witness := a.inputWitness
      }
  else
    none

/-- 中文说明：IVL -> AAF lowering。 -/
def ivlToAAF (m : LegalIVL) : AAFTarget :=
  {
    nodes := m.rules.map (fun r => r.conclusion),
    attacks := m.attacks.filterMap lowerWitnessedAttack
  }

/-- 中文证明：无 witness 的 IVL attack 不产生 AAF 边（no-spurious）。 -/
theorem unwitnessed_attack_produces_no_edge (a : IVLAttackSpec)
    (hempty : a.inputWitness = "") :
    lowerWitnessedAttack a = none := by
  dsimp [lowerWitnessedAttack]
  split
  · contradiction
  · rfl

/-- 中文证明：有 witness 的 IVL attack 产生保留 witness 的边。 -/
theorem witnessed_attack_produces_edge (a : IVLAttackSpec)
    (hwit : a.inputWitness ≠ "") :
    ∃ t : TypedAttack, lowerWitnessedAttack a = some t ∧
      t.witness = a.inputWitness := by
  dsimp [lowerWitnessedAttack]
  split
  · exact ⟨_, rfl, rfl⟩
  · contradiction

/-- 中文证明：AAF 节点全部来自 IVL 规则结论（no-spurious 节点）。 -/
theorem aaf_nodes_from_rules (m : LegalIVL) (n : String)
    (hmem : n ∈ (ivlToAAF m).nodes) :
    ∃ r ∈ m.rules, r.conclusion = n := by
  dsimp [ivlToAAF] at hmem
  rcases List.mem_map.mp hmem with ⟨r, hr, heq⟩
  exact ⟨r, hr, heq.symm⟩

end JurisLean
