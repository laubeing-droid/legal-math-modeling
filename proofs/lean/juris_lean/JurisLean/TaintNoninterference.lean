import JurisLean.LegalIds

/-!
中文说明：M3 taint noninterference。tainted 输入对正式证书
noninterference：不能通过后续 Horn、AAF、solver 或多 Agent 共识转成
正式事实。taint 沿任何推导阶段单调传播；只有全 clean 输入才产生
clean 输出。
-/

namespace JurisLean

/-- 中文说明：污点标签。 -/
inductive Taint where
  | clean
  | tainted
deriving DecidableEq, Repr

/-- 中文说明：形式输入携带污点标签与内容标识。 -/
structure FormalInput where
  subject : String
  taint : Taint
deriving DecidableEq

/-- 中文说明：污点合并：任一 tainted 即 tainted。 -/
def joinTaint : Taint → Taint → Taint
  | .clean, .clean => .clean
  | _, _ => .tainted

/-- 中文说明：输入列表的总体污点。 -/
def taintOfInputs : List FormalInput → Taint
  | [] => .clean
  | x :: xs => joinTaint x.taint (taintOfInputs xs)

/-- 中文说明：任一推导阶段（Horn / AAF / solver）的输出污点。
建模为对输入污点的上界保持：输出不优于输入的最坏污点。 -/
def stageOutput (inputs : List FormalInput) (conclusion : String) : FormalInput :=
  { subject := conclusion, taint := taintOfInputs inputs }

/-- 中文证明：clean 与 clean 合并仍为 clean。 -/
theorem join_clean_clean : joinTaint .clean .clean = .clean := rfl

/-- 中文证明：任何与 tainted 的合并都是 tainted。 -/
theorem join_with_tainted_is_tainted (t : Taint) :
    joinTaint t .tainted = .tainted := by
  cases t <;> rfl

/-- 中文证明：首位 tainted 输入使整个输入集合为 tainted。 -/
theorem tainted_input_taints_collection (x : FormalInput) (xs : List FormalInput)
    (ht : x.taint = .tainted) :
    taintOfInputs (x :: xs) = .tainted := by
  dsimp [taintOfInputs]
  rw [ht]
  cases (taintOfInputs xs) <;> rfl

/-- 中文证明：任一推导阶段保持污点上界：tainted 输入产生 tainted 输出。 -/
theorem stage_preserves_taint (x : FormalInput) (rest : List FormalInput)
    (conclusion : String) (ht : x.taint = .tainted) :
    (stageOutput (x :: rest) conclusion).taint = .tainted := by
  dsimp [stageOutput, taintOfInputs]
  rw [ht]
  cases (taintOfInputs rest) <;> rfl

/-- 中文证明：全 clean 输入产生 clean 输出（noninterference 正向）。 -/
theorem all_clean_inputs_clean_output (inputs : List FormalInput)
    (hall : ∀ x ∈ inputs, x.taint = .clean) (conclusion : String) :
    (stageOutput inputs conclusion).taint = .clean := by
  dsimp [stageOutput]
  revert hall
  induction inputs with
  | nil => intro _; rfl
  | cons y ys ih =>
    intro hall
    dsimp [taintOfInputs]
    have hy : y ∈ y :: ys := List.mem_cons.mpr (Or.inl rfl)
    rw [hall y hy]
    rw [ih (fun z hz => hall z (List.mem_cons.mpr (Or.inr hz)))]
    rfl

/-- 中文证明：多数 Agent 共识不能洗白污点（consensus laundering 无效）。 -/
theorem majority_cannot_clean (x : FormalInput) (copies : List FormalInput)
    (ht : x.taint = .tainted) :
    taintOfInputs (x :: copies) = .tainted :=
  tainted_input_taints_collection x copies ht

/-- 中文证明：tainted 输入不能成为 clean 推导结论（noninterference 核心）。 -/
theorem tainted_not_promoted_to_clean (x : FormalInput) (rest : List FormalInput)
    (conclusion : String) (ht : x.taint = .tainted) :
    (stageOutput (x :: rest) conclusion).taint ≠ .clean := by
  have htainted := stage_preserves_taint x rest conclusion ht
  intro hclean
  rw [htainted] at hclean
  cases hclean

/-- 中文证明：重复运行同一 tainted proposal 不改变污点（重复不洗白）。 -/
theorem repetition_does_not_clean (x : FormalInput) (n : List FormalInput)
    (ht : x.taint = .tainted) :
    taintOfInputs (x :: n) = taintOfInputs (x :: x :: n) := by
  rw [tainted_input_taints_collection x n ht,
      tainted_input_taints_collection x (x :: n) ht]

end JurisLean
