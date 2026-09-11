import JurisLean.BusinessRoot.SevenAxis

/- Generated from actual parsed Python fixture bytes. Not an independent legal
source or a verified byte-to-Lean compiler. Never generated from checker PASS
labels. Regenerate and diff in CI before this module is compiled. -/
set_option maxRecDepth 100000
namespace JurisLean.BusinessRoot.SevenAxis.Cases
open JurisLean.BusinessRoot.SevenAxis

def observedDoc : DocValue :=
  { metaData := { caseId := "DEMO-PRINCIPAL-01", issue := "principal-balance", creditor := "甲公司", debtor := "乙公司", debtId := "DEBT-1", sourceIds := ["SYNTHETIC-BASIS"], dueDay := "2026-08-01", asOfDay := "2026-09-09", assumptions := ["仅付款认定作为分支", "债权成立与到期已作为示例前提", "非真实法律案件"], context := { assumptions := ["仅付款认定作为分支", "债权成立与到期已作为示例前提", "非真实法律案件"], decision_time := "2026-09-09", engine_version := "reference-2.1", event_time := "2026-08-01", evidence_version := "test-evidence-1", interpretation := "explicit-reference", issue := "principal-balance", jurisdiction := "TEST", law_version := "source-snapshot-example", max_depth := 2, model_version := "synthetic-model-1", party := "claimant", procedure := "conditional_analysis", profile := "grounded", request := "DEMO-PRINCIPAL-01", rulepack_version := "test-1", scenario := "finite-conditional-completions", semantic_scope := "height_bounded", stage := "analysis", target := "award_at_least_threshold" } }
    mode := "EXACT_FINITE_SCENARIOS", rows := [([("payment_recognized", true)], (700 : ℚ), (0 : ℚ)), ([("payment_recognized", false)], (1000 : ℚ), (0 : ℚ))], pending := [] }

def observedCalculation : CalculationValue :=
  { metaData := { schema := "br/reference-two-file-delivery/1", requirement := "SYNTHETIC_EXACT_PRINCIPAL_ANALYTICS_TWO_FILES/1", scope := "SYNTHETIC_CONDITIONAL_MODEL_NOT_LITIGATION_FORECAST", warning := "本文件只核对已选合成模型的条件本金、概率和行动格；不构成事实认定、机构批准、真实胜率校准或任意法律业务验收。", principalDocument := "conditional_principal.txt", context := { assumptions := ["仅付款认定作为分支", "债权成立与到期已作为示例前提", "非真实法律案件"], decision_time := "2026-09-09", engine_version := "reference-2.1", event_time := "2026-08-01", evidence_version := "test-evidence-1", interpretation := "explicit-reference", issue := "principal-balance", jurisdiction := "TEST", law_version := "source-snapshot-example", max_depth := 2, model_version := "synthetic-model-1", party := "claimant", procedure := "conditional_analysis", profile := "grounded", request := "DEMO-PRINCIPAL-01", rulepack_version := "test-1", scenario := "finite-conditional-completions", semantic_scope := "height_bounded", stage := "analysis", target := "award_at_least_threshold" }, sources := [⟨"SYNTHETIC-BASIS", "1", 0, 35, "合成示例：已到期本金1000元；争议清偿300元；只计算条件本金余额。"⟩], relation := ⟨"principal-claim", "甲公司", "乙公司", "DEBT-1", (1000 : ℚ), "2026-08-01", "2026-09-09"⟩, modelVersion := "synthetic-model-1", modelBasis := "SYNTHETIC-SETTLEMENT-GRID/1", weights := [([("payment_recognized", true)], { num := 2, den := 5 }), ([("payment_recognized", false)], { num := 3, den := 5 })], threshold := (800 : ℚ), costs := [(100 : ℚ), (60 : ℚ), (10 : ℚ), (10 : ℚ)], options := [(600 : ℚ), (850 : ℚ), (1100 : ℚ)] }
    mode := "EXACT_FINITE_SCENARIOS", values := { requirement := "SYNTHETIC_EXACT_PRINCIPAL_ANALYTICS_TWO_FILES/1", principal := (1000 : ℚ), rows := [([("payment_recognized", true)], (700 : ℚ), (0 : ℚ)), ([("payment_recognized", false)], (1000 : ℚ), (0 : ℚ))], pending := [], weights := [([("payment_recognized", true)], { num := 2, den := 5 }), ([("payment_recognized", false)], { num := 3, den := 5 })], expectedC := (880 : ℚ), expectedU := (0 : ℚ), eventProbability := { num := 3, den := 5 }, lower := (790 : ℚ), upper := (930 : ℚ), eligible := [(850 : ℚ)], selected := some (850 : ℚ), notice := "SYNTHETIC_CONDITIONAL_MODEL_NOT_LITIGATION_FORECAST" } }

theorem actual_doc_normalization_matches : observedDoc = expectedDoc := rfl
theorem actual_json_normalization_matches : observedCalculation = expectedCalculation := rfl
theorem actual_bytes_typed_observations_accepted :
    checkSevenAxisBundle selectedInput selectedInput
      (writeDoc observedDoc) (writeCalculation observedCalculation) = true := by
  rw [actual_doc_normalization_matches, actual_json_normalization_matches]
  exact full_projection_accepts_normal

theorem reject_doc_caseId :
    checkSevenAxisBundle selectedInput selectedInput
      (writeDoc { expectedDoc with metaData := { expectedDoc.metaData with caseId := "OTHER-CASE" } })
      (writeCalculation expectedCalculation) = false := by
  apply changed_doc_metadata_rejected
  intro h
  have hf := congrArg DocMeta.caseId h
  simp [expectedDoc, expectedDocMeta, selectedInput, selectedContext] at hf

theorem reject_doc_issue :
    checkSevenAxisBundle selectedInput selectedInput
      (writeDoc { expectedDoc with metaData := { expectedDoc.metaData with issue := "OTHER-ISSUE" } })
      (writeCalculation expectedCalculation) = false := by
  apply changed_doc_metadata_rejected
  intro h
  have hf := congrArg DocMeta.issue h
  simp [expectedDoc, expectedDocMeta, selectedInput, selectedContext] at hf

theorem reject_doc_creditor :
    checkSevenAxisBundle selectedInput selectedInput
      (writeDoc { expectedDoc with metaData := { expectedDoc.metaData with creditor := "其他权利人" } })
      (writeCalculation expectedCalculation) = false := by
  apply changed_doc_metadata_rejected
  intro h
  have hf := congrArg DocMeta.creditor h
  simp [expectedDoc, expectedDocMeta, selectedInput, selectedContext] at hf

theorem reject_doc_debtor :
    checkSevenAxisBundle selectedInput selectedInput
      (writeDoc { expectedDoc with metaData := { expectedDoc.metaData with debtor := "丙公司" } })
      (writeCalculation expectedCalculation) = false := by
  apply changed_doc_metadata_rejected
  intro h
  have hf := congrArg DocMeta.debtor h
  simp [expectedDoc, expectedDocMeta, selectedInput, selectedContext] at hf

theorem reject_doc_debtId :
    checkSevenAxisBundle selectedInput selectedInput
      (writeDoc { expectedDoc with metaData := { expectedDoc.metaData with debtId := "OTHER-DEBT" } })
      (writeCalculation expectedCalculation) = false := by
  apply changed_doc_metadata_rejected
  intro h
  have hf := congrArg DocMeta.debtId h
  simp [expectedDoc, expectedDocMeta, selectedInput, selectedContext] at hf

theorem reject_doc_sourceIds :
    checkSevenAxisBundle selectedInput selectedInput
      (writeDoc { expectedDoc with metaData := { expectedDoc.metaData with sourceIds := ["OTHER-SOURCE"] } })
      (writeCalculation expectedCalculation) = false := by
  apply changed_doc_metadata_rejected
  intro h
  have hf := congrArg DocMeta.sourceIds h
  simp [expectedDoc, expectedDocMeta, selectedInput, selectedContext] at hf

theorem reject_doc_dueDay :
    checkSevenAxisBundle selectedInput selectedInput
      (writeDoc { expectedDoc with metaData := { expectedDoc.metaData with dueDay := "2099-01-01" } })
      (writeCalculation expectedCalculation) = false := by
  apply changed_doc_metadata_rejected
  intro h
  have hf := congrArg DocMeta.dueDay h
  simp [expectedDoc, expectedDocMeta, selectedInput, selectedContext] at hf

theorem reject_doc_asOfDay :
    checkSevenAxisBundle selectedInput selectedInput
      (writeDoc { expectedDoc with metaData := { expectedDoc.metaData with asOfDay := "2099-01-02" } })
      (writeCalculation expectedCalculation) = false := by
  apply changed_doc_metadata_rejected
  intro h
  have hf := congrArg DocMeta.asOfDay h
  simp [expectedDoc, expectedDocMeta, selectedInput, selectedContext] at hf

theorem reject_doc_assumptions :
    checkSevenAxisBundle selectedInput selectedInput
      (writeDoc { expectedDoc with metaData := { expectedDoc.metaData with assumptions := ["UNSUPPORTED-ASSUMPTION"] } })
      (writeCalculation expectedCalculation) = false := by
  apply changed_doc_metadata_rejected
  intro h
  have hf := congrArg DocMeta.assumptions h
  simp [expectedDoc, expectedDocMeta, selectedInput, selectedContext] at hf

theorem reject_context_assumptions :
    checkSevenAxisBundle selectedInput selectedInput
      (writeDoc { expectedDoc with metaData := { expectedDoc.metaData with
        context := { selectedContext with assumptions := ["OTHER-ASSUMPTION"] } } })
      (writeCalculation expectedCalculation) = false := by
  apply changed_doc_metadata_rejected
  intro h
  have hf := congrArg (fun m : DocMeta => m.context.assumptions) h
  simp [expectedDoc, expectedDocMeta, selectedInput, selectedContext] at hf

theorem reject_context_decision_time :
    checkSevenAxisBundle selectedInput selectedInput
      (writeDoc { expectedDoc with metaData := { expectedDoc.metaData with
        context := { selectedContext with decision_time := "OTHER-VALUE" } } })
      (writeCalculation expectedCalculation) = false := by
  apply changed_doc_metadata_rejected
  intro h
  have hf := congrArg (fun m : DocMeta => m.context.decision_time) h
  simp [expectedDoc, expectedDocMeta, selectedInput, selectedContext] at hf

theorem reject_context_engine_version :
    checkSevenAxisBundle selectedInput selectedInput
      (writeDoc { expectedDoc with metaData := { expectedDoc.metaData with
        context := { selectedContext with engine_version := "OTHER-VALUE" } } })
      (writeCalculation expectedCalculation) = false := by
  apply changed_doc_metadata_rejected
  intro h
  have hf := congrArg (fun m : DocMeta => m.context.engine_version) h
  simp [expectedDoc, expectedDocMeta, selectedInput, selectedContext] at hf

theorem reject_context_event_time :
    checkSevenAxisBundle selectedInput selectedInput
      (writeDoc { expectedDoc with metaData := { expectedDoc.metaData with
        context := { selectedContext with event_time := "OTHER-VALUE" } } })
      (writeCalculation expectedCalculation) = false := by
  apply changed_doc_metadata_rejected
  intro h
  have hf := congrArg (fun m : DocMeta => m.context.event_time) h
  simp [expectedDoc, expectedDocMeta, selectedInput, selectedContext] at hf

theorem reject_context_evidence_version :
    checkSevenAxisBundle selectedInput selectedInput
      (writeDoc { expectedDoc with metaData := { expectedDoc.metaData with
        context := { selectedContext with evidence_version := "OTHER-VALUE" } } })
      (writeCalculation expectedCalculation) = false := by
  apply changed_doc_metadata_rejected
  intro h
  have hf := congrArg (fun m : DocMeta => m.context.evidence_version) h
  simp [expectedDoc, expectedDocMeta, selectedInput, selectedContext] at hf

theorem reject_context_interpretation :
    checkSevenAxisBundle selectedInput selectedInput
      (writeDoc { expectedDoc with metaData := { expectedDoc.metaData with
        context := { selectedContext with interpretation := "OTHER-VALUE" } } })
      (writeCalculation expectedCalculation) = false := by
  apply changed_doc_metadata_rejected
  intro h
  have hf := congrArg (fun m : DocMeta => m.context.interpretation) h
  simp [expectedDoc, expectedDocMeta, selectedInput, selectedContext] at hf

theorem reject_context_issue :
    checkSevenAxisBundle selectedInput selectedInput
      (writeDoc { expectedDoc with metaData := { expectedDoc.metaData with
        context := { selectedContext with issue := "OTHER-VALUE" } } })
      (writeCalculation expectedCalculation) = false := by
  apply changed_doc_metadata_rejected
  intro h
  have hf := congrArg (fun m : DocMeta => m.context.issue) h
  simp [expectedDoc, expectedDocMeta, selectedInput, selectedContext] at hf

theorem reject_context_jurisdiction :
    checkSevenAxisBundle selectedInput selectedInput
      (writeDoc { expectedDoc with metaData := { expectedDoc.metaData with
        context := { selectedContext with jurisdiction := "OTHER-VALUE" } } })
      (writeCalculation expectedCalculation) = false := by
  apply changed_doc_metadata_rejected
  intro h
  have hf := congrArg (fun m : DocMeta => m.context.jurisdiction) h
  simp [expectedDoc, expectedDocMeta, selectedInput, selectedContext] at hf

theorem reject_context_law_version :
    checkSevenAxisBundle selectedInput selectedInput
      (writeDoc { expectedDoc with metaData := { expectedDoc.metaData with
        context := { selectedContext with law_version := "OTHER-VALUE" } } })
      (writeCalculation expectedCalculation) = false := by
  apply changed_doc_metadata_rejected
  intro h
  have hf := congrArg (fun m : DocMeta => m.context.law_version) h
  simp [expectedDoc, expectedDocMeta, selectedInput, selectedContext] at hf

theorem reject_context_max_depth :
    checkSevenAxisBundle selectedInput selectedInput
      (writeDoc { expectedDoc with metaData := { expectedDoc.metaData with
        context := { selectedContext with max_depth := 999 } } })
      (writeCalculation expectedCalculation) = false := by
  apply changed_doc_metadata_rejected
  intro h
  have hf := congrArg (fun m : DocMeta => m.context.max_depth) h
  simp [expectedDoc, expectedDocMeta, selectedInput, selectedContext] at hf

theorem reject_context_model_version :
    checkSevenAxisBundle selectedInput selectedInput
      (writeDoc { expectedDoc with metaData := { expectedDoc.metaData with
        context := { selectedContext with model_version := "OTHER-VALUE" } } })
      (writeCalculation expectedCalculation) = false := by
  apply changed_doc_metadata_rejected
  intro h
  have hf := congrArg (fun m : DocMeta => m.context.model_version) h
  simp [expectedDoc, expectedDocMeta, selectedInput, selectedContext] at hf

theorem reject_context_party :
    checkSevenAxisBundle selectedInput selectedInput
      (writeDoc { expectedDoc with metaData := { expectedDoc.metaData with
        context := { selectedContext with party := "OTHER-VALUE" } } })
      (writeCalculation expectedCalculation) = false := by
  apply changed_doc_metadata_rejected
  intro h
  have hf := congrArg (fun m : DocMeta => m.context.party) h
  simp [expectedDoc, expectedDocMeta, selectedInput, selectedContext] at hf

theorem reject_context_procedure :
    checkSevenAxisBundle selectedInput selectedInput
      (writeDoc { expectedDoc with metaData := { expectedDoc.metaData with
        context := { selectedContext with procedure := "OTHER-VALUE" } } })
      (writeCalculation expectedCalculation) = false := by
  apply changed_doc_metadata_rejected
  intro h
  have hf := congrArg (fun m : DocMeta => m.context.procedure) h
  simp [expectedDoc, expectedDocMeta, selectedInput, selectedContext] at hf

theorem reject_context_profile :
    checkSevenAxisBundle selectedInput selectedInput
      (writeDoc { expectedDoc with metaData := { expectedDoc.metaData with
        context := { selectedContext with profile := "OTHER-VALUE" } } })
      (writeCalculation expectedCalculation) = false := by
  apply changed_doc_metadata_rejected
  intro h
  have hf := congrArg (fun m : DocMeta => m.context.profile) h
  simp [expectedDoc, expectedDocMeta, selectedInput, selectedContext] at hf

theorem reject_context_request :
    checkSevenAxisBundle selectedInput selectedInput
      (writeDoc { expectedDoc with metaData := { expectedDoc.metaData with
        context := { selectedContext with request := "OTHER-VALUE" } } })
      (writeCalculation expectedCalculation) = false := by
  apply changed_doc_metadata_rejected
  intro h
  have hf := congrArg (fun m : DocMeta => m.context.request) h
  simp [expectedDoc, expectedDocMeta, selectedInput, selectedContext] at hf

theorem reject_context_rulepack_version :
    checkSevenAxisBundle selectedInput selectedInput
      (writeDoc { expectedDoc with metaData := { expectedDoc.metaData with
        context := { selectedContext with rulepack_version := "OTHER-VALUE" } } })
      (writeCalculation expectedCalculation) = false := by
  apply changed_doc_metadata_rejected
  intro h
  have hf := congrArg (fun m : DocMeta => m.context.rulepack_version) h
  simp [expectedDoc, expectedDocMeta, selectedInput, selectedContext] at hf

theorem reject_context_scenario :
    checkSevenAxisBundle selectedInput selectedInput
      (writeDoc { expectedDoc with metaData := { expectedDoc.metaData with
        context := { selectedContext with scenario := "OTHER-VALUE" } } })
      (writeCalculation expectedCalculation) = false := by
  apply changed_doc_metadata_rejected
  intro h
  have hf := congrArg (fun m : DocMeta => m.context.scenario) h
  simp [expectedDoc, expectedDocMeta, selectedInput, selectedContext] at hf

theorem reject_context_semantic_scope :
    checkSevenAxisBundle selectedInput selectedInput
      (writeDoc { expectedDoc with metaData := { expectedDoc.metaData with
        context := { selectedContext with semantic_scope := "OTHER-VALUE" } } })
      (writeCalculation expectedCalculation) = false := by
  apply changed_doc_metadata_rejected
  intro h
  have hf := congrArg (fun m : DocMeta => m.context.semantic_scope) h
  simp [expectedDoc, expectedDocMeta, selectedInput, selectedContext] at hf

theorem reject_context_stage :
    checkSevenAxisBundle selectedInput selectedInput
      (writeDoc { expectedDoc with metaData := { expectedDoc.metaData with
        context := { selectedContext with stage := "OTHER-VALUE" } } })
      (writeCalculation expectedCalculation) = false := by
  apply changed_doc_metadata_rejected
  intro h
  have hf := congrArg (fun m : DocMeta => m.context.stage) h
  simp [expectedDoc, expectedDocMeta, selectedInput, selectedContext] at hf

theorem reject_context_target :
    checkSevenAxisBundle selectedInput selectedInput
      (writeDoc { expectedDoc with metaData := { expectedDoc.metaData with
        context := { selectedContext with target := "OTHER-VALUE" } } })
      (writeCalculation expectedCalculation) = false := by
  apply changed_doc_metadata_rejected
  intro h
  have hf := congrArg (fun m : DocMeta => m.context.target) h
  simp [expectedDoc, expectedDocMeta, selectedInput, selectedContext] at hf

end JurisLean.BusinessRoot.SevenAxis.Cases
