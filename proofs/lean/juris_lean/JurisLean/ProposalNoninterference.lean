import JurisLean.TaintNoninterference
import JurisLean.ProposalEnvelopeSpec

/-!
中文说明：M7 proposal noninterference 组合定理。LLM/Agent proposal
携带 UNTRUSTED_PROPOSAL 污点；经过 Horn/AAF/solver/多数 Agent 阶段后
污点保留，不能进入正式前提集（与 M3 taint 定理组合）。
-/

namespace JurisLean

/-- 中文说明：把 proposal 视为一个带污点的形式输入。 -/
def proposalAsInput (p : ProposalEnvelope) : FormalInput :=
  { subject := p.subject, taint := .tainted }

/-- 中文证明：LLM/Agent proposal 作为输入必然携带污点。 -/
theorem proposal_is_tainted_input (p : ProposalEnvelope)
    (horigin : p.origin = .llm ∨ p.origin = .agent) :
    (proposalAsInput p).taint = .tainted := by
  dsimp [proposalAsInput]
  cases horigin <;> rfl

/-- 中文证明：proposal 进入推导阶段后输出仍为 tainted（noninterference
与 TaintNoninterference.stage_preserves_taint 组合）。 -/
theorem proposal_taint_survives_stage (p : ProposalEnvelope)
    (rest : List FormalInput) (conclusion : String) :
    (stageOutput (proposalAsInput p :: rest) conclusion).taint = .tainted :=
  stage_preserves_taint (proposalAsInput p) rest conclusion rfl

/-- 中文证明：tainted proposal 输出永远不是 clean（不能成为正式事实）。 -/
theorem proposal_never_clean_after_stage (p : ProposalEnvelope)
    (rest : List FormalInput) (conclusion : String) :
    (stageOutput (proposalAsInput p :: rest) conclusion).taint ≠ .clean := by
  have h := proposal_taint_survives_stage p rest conclusion
  intro hclean
  rw [h] at hclean
  cases hclean

/-- 中文证明：多数 proposal 复制不改变污点（共识不洗白）。 -/
theorem proposal_majority_stays_tainted (p : ProposalEnvelope)
    (copies : List FormalInput) :
    taintOfInputs (proposalAsInput p :: copies) = .tainted :=
  tainted_input_taints_collection (proposalAsInput p) copies rfl

end JurisLean
