import JurisLean.CertificateChecker

/-!
中文说明：本文件表达 Horn closure 到 AAF arguments/attacks 的最小 contract。
它不声称完整 Python runtime 已被 Lean 证明，只刻画四个竖切必须保持的
可审计边界。
-/

namespace JurisLean

/-- 中文说明：Horn derivation 只记录规则、结论和支持事实是否已闭包支持。 -/
structure HornDerivation where
  rule : RuleId
  conclusion : FactId
  support : Finset FactId
  supported : Bool
deriving DecidableEq

/-- 中文说明：把一个 Horn derivation 编译成支持同一结论的 argument。 -/
def compileHornArgument (slice : SliceKind) (d : HornDerivation) : Argument :=
  {
    id := "arg::" ++ d.rule,
    claim := {
      id := "claim::" ++ d.conclusion,
      conclusion := d.conclusion,
      slice := slice
    },
    support := d.support,
    rule := d.rule,
    supported := d.supported
  }

/-- 中文说明：把一个 exception fact 编译成 directed attack。 -/
def compileExceptionAttack (exceptionFact : FactId)
    (attacker target : Argument) : Attack :=
  {
    id := "attack::exception::" ++ exceptionFact,
    source := attacker.id,
    target := target.id,
    kind := AttackKind.exception
  }

/-- 中文说明：把 priority relation 编译成 directed priority defeat。 -/
def compilePriorityDefeat (p : Priority) : Attack :=
  {
    id := "attack::priority::" ++ p.id,
    source := p.higher,
    target := p.lower,
    kind := AttackKind.priorityDefeat
  }

/-- 中文说明：checker 层只允许 supported argument 和 accepted certificate 同时成立。 -/
def checkerAcceptsArgument (a : Argument) (c : Certificate) : Prop :=
  a.supported = true ∧ checkCertificate c = CheckVerdict.accept

/-- 中文证明：Horn derivation 编译出的 argument 保留同一结论。 -/
theorem horn_derivation_to_argument_conclusion
    (slice : SliceKind) (d : HornDerivation) :
    (compileHornArgument slice d).claim.conclusion = d.conclusion := rfl

/-- 中文证明：Horn derivation 编译出的 argument 保留 supported 标记。 -/
theorem horn_derivation_to_argument_supported
    (slice : SliceKind) (d : HornDerivation) :
    (compileHornArgument slice d).supported = d.supported := rfl

/-- 中文证明：exception fact 编译结果必须是 exception attack。 -/
theorem exception_fact_to_attack_kind
    (exceptionFact : FactId) (attacker target : Argument) :
    (compileExceptionAttack exceptionFact attacker target).kind =
      AttackKind.exception := rfl

/-- 中文证明：priority relation 编译结果必须是 priority defeat。 -/
theorem priority_defeat_to_attack_kind (p : Priority) :
    (compilePriorityDefeat p).kind = AttackKind.priorityDefeat := rfl

/-- 中文证明：unsupported argument 不能被 checker 接受。 -/
theorem no_unsupported_argument_accepted
    {a : Argument} {c : Certificate}
    (hUnsupported : a.supported = false) :
    ¬ checkerAcceptsArgument a c := by
  intro h
  rcases h with ⟨hSupported, _hCertificate⟩
  rw [hUnsupported] at hSupported
  contradiction

end JurisLean
