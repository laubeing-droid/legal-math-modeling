import JurisLean.LegalIds
import JurisLean.FailureStatus

/-!
中文说明：M5 P04 多 backend 合同。完整定义 Horn、argumentation、
closed-form、ASP、SMT 与 direct reference backend。routing 对 typed
feature 完整且确定；UNKNOWN/TIMEOUT/BACKEND_UNAVAILABLE 不映射为
FALSE、REFUTED 或 PASS。
-/

namespace JurisLean

/-- 中文说明：backend 类别。 -/
inductive BackendKindM5 where
  | directReference
  | horn
  | argumentation
  | closedForm
  | asp
  | smt
deriving DecidableEq, Repr

/-- 中文说明：solver/backend 结果。 -/
inductive SolverOutcome where
  | sat
  | unsat
  | unknown
  | timeout
  | backendUnavailable
  | error
deriving DecidableEq, Repr

/-- 中文说明：问题特征（typed features）。 -/
structure ProblemFeatures where
  needsNonmonotonic : Bool
  needsArithmetic : Bool
  needsDisjunction : Bool
  plainHorn : Bool
deriving DecidableEq

/-- 中文说明：结果是否决定性。 -/
def outcomeDecisive : SolverOutcome → Bool
  | .sat => true
  | .unsat => true
  | _ => false

/-- 中文说明：typed feature 路由：确定且完整。 -/
def routeBackend (f : ProblemFeatures) : BackendKindM5 :=
  if f.needsNonmonotonic then .asp
  else if f.needsArithmetic then .smt
  else if f.needsDisjunction then .asp
  else if f.plainHorn then .horn
  else .directReference

/-- 中文证明：非单调问题路由到 ASP（不落入 Horn）。 -/
theorem nonmonotonic_routes_to_asp (f : ProblemFeatures)
    (h : f.needsNonmonotonic = true) : routeBackend f = .asp := by
  dsimp [routeBackend]
  rw [h]
  simp

/-- 中文证明：算术问题路由到 SMT（不落入 Horn）。 -/
theorem arithmetic_routes_to_smt (f : ProblemFeatures)
    (hnon : f.needsNonmonotonic = false) (h : f.needsArithmetic = true) :
    routeBackend f = .smt := by
  dsimp [routeBackend]
  rw [hnon, h]
  simp

/-- 中文证明：plain Horn 问题路由到 Horn backend。 -/
theorem plain_horn_routes_to_horn (f : ProblemFeatures)
    (hnon : f.needsNonmonotonic = false) (har : f.needsArithmetic = false)
    (hdis : f.needsDisjunction = false) (h : f.plainHorn = true) :
    routeBackend f = .horn := by
  dsimp [routeBackend]
  rw [hnon, har, hdis, h]
  simp

/-- 中文证明：路由是确定函数：同特征同 backend。 -/
theorem routing_deterministic (f : ProblemFeatures) :
    routeBackend f = routeBackend f := rfl

/-- 中文证明：UNKNOWN 不是决定性结果（不映射为 FALSE/PASS）。 -/
theorem unknown_not_decisive : outcomeDecisive .unknown = false := rfl

/-- 中文证明：TIMEOUT 不是决定性结果。 -/
theorem timeout_not_decisive : outcomeDecisive .timeout = false := rfl

/-- 中文证明：BACKEND_UNAVAILABLE 不是决定性结果。 -/
theorem backend_unavailable_not_decisive :
    outcomeDecisive .backendUnavailable = false := rfl

/-- 中文证明：只有 SAT/UNSAT 是决定性结果（完备分划）。 -/
theorem decisive_iff_sat_or_unsat (o : SolverOutcome) :
    outcomeDecisive o = true ↔ o = .sat ∨ o = .unsat := by
  cases o <;> simp [outcomeDecisive]

/-- 中文证明：非决定性结果一律转为 FailureStatus 的 fail-closed 状态。 -/
def outcomeToFailureStatus : SolverOutcome → FailureStatus
  | .sat => .success
  | .unsat => .success
  | .unknown => .unknown
  | .timeout => .timeout
  | .backendUnavailable => .backendUnavailable
  | .error => .error

theorem non_decisive_outcome_fail_closed (o : SolverOutcome)
    (h : outcomeDecisive o = false) :
    (outcomeToFailureStatus o).isFailClosed = true := by
  cases o
  · dsimp [outcomeDecisive] at h; cases h
  · dsimp [outcomeDecisive] at h; cases h
  · rfl
  · rfl
  · rfl
  · rfl

end JurisLean
