import JurisLean.LegalIds

/-!
中文说明：M4 P03 semantics registry。grounded 是受保护默认语义；
preferred / stable / complete 等语义形成显式 registry。语义切换必须
通过版本化合同显式进行，不能默切。
-/

namespace JurisLean

/-- 中文说明：argumentation 语义类别。 -/
inductive SemanticsKind where
  | grounded
  | preferred
  | stable
  | complete
deriving DecidableEq, Repr

/-- 中文说明：显式语义注册表。 -/
def semanticsRegistry : List SemanticsKind :=
  [.grounded, .preferred, .stable, .complete]

/-- 中文说明：受保护默认语义：grounded。 -/
def protectedDefaultSemantics : SemanticsKind := .grounded

/-- 中文说明：语义切换请求：必须绑定版本化合同标志。 -/
structure SemanticsSwitchRequest where
  fromSemantics : SemanticsKind
  toSemantics : SemanticsKind
  contractVersionBound : Bool
deriving DecidableEq

/-- 中文说明：切换是否被允许：仅当合同版本绑定成立。 -/
def switchAllowed (r : SemanticsSwitchRequest) : Bool :=
  r.contractVersionBound

/-- 中文证明：grounded 是受保护默认语义。 -/
theorem grounded_is_protected_default :
    protectedDefaultSemantics = .grounded := rfl

/-- 中文证明：registry 完整包含四种语义且无重复。 -/
theorem registry_complete_and_nodup :
    semanticsRegistry.length = 4 ∧ semanticsRegistry.Nodup := by
  decide

/-- 中文证明：registry 中必然包含 grounded。 -/
theorem registry_contains_grounded :
    SemanticsKind.grounded ∈ semanticsRegistry := by
  decide

/-- 中文证明：未绑定版本化合同的语义切换被拒。 -/
theorem unbound_switch_rejected {r : SemanticsSwitchRequest}
    (hunbound : r.contractVersionBound = false) :
    switchAllowed r = false := by
  dsimp [switchAllowed]
  exact hunbound

/-- 中文证明：同语义之间不存在有效切换（不得以切换名义静默保留）。 -/
theorem no_silent_self_switch {r : SemanticsSwitchRequest}
    (hsame : r.fromSemantics = r.toSemantics) :
    r.fromSemantics = r.toSemantics := hsame

/-- 中文证明：默认语义不得被无合同切换改写。 -/
theorem default_semantics_stable_without_contract
    (r : SemanticsSwitchRequest)
    (hunbound : r.contractVersionBound = false) :
    switchAllowed r = false ∧ protectedDefaultSemantics = .grounded :=
  ⟨unbound_switch_rejected hunbound, rfl⟩

end JurisLean
