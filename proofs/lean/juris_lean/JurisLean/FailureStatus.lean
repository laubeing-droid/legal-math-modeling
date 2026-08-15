/-!
中文说明：M1 失败状态层。所有非确定结果统一 fail-closed：UNKNOWN、
TIMEOUT、SKIP、NOT_RUN、BACKEND_UNAVAILABLE、ERROR、CI_NOT_RUN 都不得
映射为 PASS、FALSE 或 REFUTED。
-/

namespace JurisLean

/-- 中文说明：执行与证据状态；只有 success 是正向结果。 -/
inductive FailureStatus where
  | success
  | unknown
  | timeout
  | skip
  | notRun
  | backendUnavailable
  | error
  | ciNotRun
deriving DecidableEq, Repr

/-- 中文说明：是否允许把状态升级为决定性通过。 -/
def FailureStatus.isDecisivePass : FailureStatus -> Bool
  | .success => true
  | _ => false

/-- 中文说明：状态是否属于 fail-closed 阻塞类。 -/
def FailureStatus.isFailClosed : FailureStatus -> Bool
  | .success => false
  | _ => true

/-- 中文证明：只有 success 才能作为决定性通过。 -/
theorem only_success_is_decisive_pass (s : FailureStatus) :
    s.isDecisivePass = true ↔ s = .success := by
  cases s <;> simp [FailureStatus.isDecisivePass]

/-- 中文证明：UNKNOWN 永远不是决定性通过。 -/
theorem unknown_never_decisive :
    FailureStatus.isDecisivePass .unknown = false := rfl

/-- 中文证明：TIMEOUT 永远不是决定性通过。 -/
theorem timeout_never_decisive :
    FailureStatus.isDecisivePass .timeout = false := rfl

/-- 中文证明：CI_NOT_RUN 属于 fail-closed，不允许发布。 -/
theorem ci_not_run_is_fail_closed :
    FailureStatus.isFailClosed .ciNotRun = true := rfl

/-- 中文证明：除 success 外所有状态都是 fail-closed。 -/
theorem non_success_is_fail_closed (s : FailureStatus) :
    s ≠ .success → s.isFailClosed = true := by
  cases s <;> simp [FailureStatus.isFailClosed]

/-- 中文说明：发布判定：任何 fail-closed 状态阻塞发布。 -/
def releaseAllowed (statuses : List FailureStatus) : Bool :=
  statuses.all (fun s => s.isDecisivePass)

/-- 中文证明：含任一 fail-closed 状态的列表不允许发布。 -/
theorem release_blocked_by_fail_closed (s : FailureStatus) (rest : List FailureStatus)
    (hblocked : s.isFailClosed = true) :
    releaseAllowed (s :: rest) = false := by
  cases s <;> first
    | cases hblocked
    | simp [releaseAllowed, FailureStatus.isDecisivePass]

end JurisLean
