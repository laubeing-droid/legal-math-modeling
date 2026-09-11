import JurisLean.BusinessRoot.Root
import JurisLean.UnifiedV21.Context

/-!
Audit-delta candidate: full observed input binding around the EXISTING numeric
root. No replacement numerical engine and no assertion about an arbitrary I0.
The old `business_root_two_files` remains a historical numeric-projection lemma.
The release claim must use `seven_axis_business_root` below.

`DocRow` and `CalculationRow` are typed observations of ACTUAL parsed files,
not producer-supplied attestations. UTF-8/JSON lexing, date parsing, normalization
and Python-to-this-token mapping remain the declared cross-check/TCB boundary.
The statement protects every field declared in the observation types. It does
not prove a source true, a legal interpretation applicable, or a forecast valid.
All new declarations: SOURCE_DRAFT_CI_NOT_RUN until this checkout's GitHub build.
-/
set_option maxRecDepth 100000

namespace JurisLean.BusinessRoot.SevenAxis

abbrev ContextKey := JurisLean.ULM.UnifiedV21.ContextKey
abbrev ScenarioRow := List (String × Bool) × ℚ × ℚ

structure SourceBinding where
  sourceId : String
  version : String
  text : String
  start : Nat
  stop : Nat
  quoted : String
  deriving DecidableEq

structure SourceView where
  sourceId : String
  version : String
  start : Nat
  stop : Nat
  quoted : String
  deriving DecidableEq

def SourceBinding.view (s : SourceBinding) : SourceView :=
  ⟨s.sourceId, s.version, s.start, s.stop, s.quoted⟩

structure RelationBinding where
  relationId : String
  creditor : String
  debtor : String
  debtId : String
  principal : ℚ
  dueDay : String
  asOfDay : String
  deriving DecidableEq

structure PaymentBinding where
  paymentId : String
  amount : ℚ
  paidDay : String
  payer : String
  payee : String
  debtId : String
  recognitionAtom : String
  sourceId : String
  deriving DecidableEq

/-- Complete selected input at this finite reference boundary. The inherited
context is reused; no approval ID, signature, key, or alternative registry. -/
structure FullInput where
  context : ContextKey
  requirement : String
  sources : List SourceBinding
  relation : RelationBinding
  paymentDetails : List PaymentBinding
  specification : PrincipalSpec
  decisionWeights : List (List (String × Bool) × ℚ)
  parameters : ExactInput
  modelBasis : String
  deriving DecidableEq

def CheckFullBinding (expected submitted : FullInput) : Bool :=
  decide (expected = submitted)

theorem full_binding_exact (a b : FullInput)
    (h : CheckFullBinding a b = true) : a = b := by
  exact of_decide_eq_true h

theorem full_binding_refuses_change (a b : FullInput) (h : a ≠ b) :
    CheckFullBinding a b = false := by
  simp [CheckFullBinding, h]

/-- Typing is not byte serialization. This roundtrip only concerns the displayed
complete structured carrier and cannot certify Python JSON serialization. -/
def toCarrier (x : FullInput) : FullInput := x

theorem carrier_retains_input (x : FullInput) : toCarrier x = x := rfl

structure DocMeta where
  caseId : String
  issue : String
  creditor : String
  debtor : String
  debtId : String
  sourceIds : List String
  dueDay : String
  asOfDay : String
  assumptions : List String
  context : ContextKey
  deriving DecidableEq

structure JsonMeta where
  schema : String
  requirement : String
  scope : String
  warning : String
  principalDocument : String
  context : ContextKey
  sources : List SourceView
  relation : RelationBinding
  modelVersion : String
  modelBasis : String
  weights : List (List (String × Bool) × ℚ)
  threshold : ℚ
  costs : List ℚ
  options : List ℚ
  deriving DecidableEq

def notice : String :=
  "本文件只核对已选合成模型的条件本金、概率和行动格；不构成事实认定、机构批准、真实胜率校准或任意法律业务验收。"
def textWarning : String :=
  "本文件为明确假设下的条件计算，不表示法院认定、真实胜率或最终返还请求已经成立。"
def textFooter : String :=
  "范围仅限本输入指定的本金余额；利息、其他抗辩、法律审核和实际裁判另行处理。"

def expectedDocMeta (i : FullInput) : DocMeta :=
  { caseId := i.context.request, issue := i.context.issue
    creditor := i.relation.creditor, debtor := i.relation.debtor
    debtId := i.relation.debtId, sourceIds := i.sources.map (·.sourceId)
    dueDay := i.relation.dueDay, asOfDay := i.relation.asOfDay
    assumptions := i.context.assumptions, context := i.context }

def expectedJsonMeta (i : FullInput) : JsonMeta :=
  { schema := "br/reference-two-file-delivery/1", requirement := i.requirement
    scope := "SYNTHETIC_CONDITIONAL_MODEL_NOT_LITIGATION_FORECAST"
    warning := notice, principalDocument := "conditional_principal.txt"
    context := i.context, sources := i.sources.map SourceBinding.view
    relation := i.relation, modelVersion := i.context.model_version
    modelBasis := i.modelBasis, weights := i.decisionWeights
    threshold := i.parameters.threshold
    costs := [i.parameters.costP, i.parameters.costD,
              i.parameters.settleP, i.parameters.settleD]
    options := i.parameters.options }

structure DocValue where
  meta : DocMeta
  mode : String
  rows : List ScenarioRow
  pending : List (List (String × Bool))
  deriving DecidableEq

structure CalculationValue where
  meta : JsonMeta
  mode : String
  values : Protected
  deriving DecidableEq

/-- Named, closed token grammar AFTER real byte decoding. Header metadata are
one canonical decoded aggregate of the actual header lines, not an invisible
sidecar supplied by the producer. -/
inductive DocRow where
  | title (s : String)
  | warning (s : String)
  | metadata (m : DocMeta)
  | mode (s : String)
  | scenarios (xs : List ScenarioRow)
  | pending (xs : List (List (String × Bool)))
  | footer (s : String)

inductive CalculationRow where
  | metadata (m : JsonMeta)
  | mode (s : String)
  | values (p : Protected)

def readDoc : List DocRow → Option DocValue
  | [.title t, .warning n, .metadata m, .mode k, .scenarios xs, .pending u, .footer f] =>
    if t = "# 条件性本金分析" ∧ n = textWarning ∧ f = textFooter
    then some ⟨m, k, xs, u⟩ else none
  | _ => none

def readCalculation : List CalculationRow → Option CalculationValue
  | [.metadata m, .mode k, .values p] => some ⟨m,k,p⟩
  | _ => none

def writeDoc (v : DocValue) : List DocRow :=
  [.title "# 条件性本金分析", .warning textWarning, .metadata v.meta,
   .mode v.mode, .scenarios v.rows, .pending v.pending, .footer textFooter]

def writeCalculation (v : CalculationValue) : List CalculationRow :=
  [.metadata v.meta, .mode v.mode, .values v.values]

theorem read_write_doc (v : DocValue) : readDoc (writeDoc v) = some v := by
  cases v
  simp [readDoc, writeDoc]

theorem read_write_calculation (v : CalculationValue) :
    readCalculation (writeCalculation v) = some v := by
  cases v
  rfl

/-- Selected context corresponds to the retained Python `demo_spec` fixture.
The field-level vector tests must validate this mapping in CI. -/
def selectedContext : ContextKey :=
  { request := "DEMO-PRINCIPAL-01", jurisdiction := "TEST"
    event_time := "2026-08-01", decision_time := "2026-09-09"
    procedure := "conditional_analysis", stage := "analysis", party := "claimant"
    issue := "principal-balance", scenario := "finite-conditional-completions"
    profile := "grounded", law_version := "source-snapshot-example"
    interpretation := "explicit-reference", rulepack_version := "test-1"
    engine_version := "reference-2.1", model_version := "synthetic-model-1"
    evidence_version := "test-evidence-1", target := "award_at_least_threshold"
    semantic_scope := "height_bounded"
    assumptions := ["仅付款认定作为分支", "债权成立与到期已作为示例前提", "非真实法律案件"]
    max_depth := 2 }

def sourceText : String :=
  "合成示例：已到期本金1000元；争议清偿300元；只计算条件本金余额。"

def selectedInput : FullInput :=
  { context := selectedContext, requirement := requirementQ
    sources := [⟨"SYNTHETIC-BASIS", "1", sourceText, 0, sourceText.length, sourceText⟩]
    relation := ⟨"principal-claim", "甲公司", "乙公司", "DEBT-1", 1000,
                  "2026-08-01", "2026-09-09"⟩
    paymentDetails := [⟨"P1",300,"2026-08-20","乙公司","甲公司","DEBT-1",
                         rootAtom,"SYNTHETIC-BASIS"⟩]
    specification := rootSpec
    decisionWeights := [([(rootAtom,true)],qTwoFifths),
                        ([(rootAtom,false)],qThreeFifths)]
    parameters := rootInput, modelBasis := "SYNTHETIC-SETTLEMENT-GRID/1" }

/-- Expected protected observations are derived from selected input and the
already independently proved numerical witness, NEVER from producer files. -/
def expectedDoc : DocValue :=
  ⟨expectedDocMeta selectedInput, "EXACT_FINITE_SCENARIOS", rootRowsCond, []⟩

def expectedCalculation : CalculationValue :=
  ⟨expectedJsonMeta selectedInput, "EXACT_FINITE_SCENARIOS", rootProtected⟩

/-- This is a fixed-profile check, not an arbitrary-parameter solver. A new input
may run through ordinary reference checking, but does not inherit this theorem. -/
def checkSevenAxisBundle (hostSelected submitted : FullInput)
    (d : List DocRow) (j : List CalculationRow) : Bool :=
  match readDoc d, readCalculation j with
  | some dv, some jv =>
    decide (hostSelected = selectedInput ∧ submitted = hostSelected ∧
            dv = expectedDoc ∧ jv = expectedCalculation)
  | _, _ => false

/-- A genuine semantic conclusion: same original input, complete witness
semantics, and actual parsed observations equal their independent requirement.
No `check = true` occurs in this business-satisfaction definition. -/
def SevenTaskSat (hostSelected submitted : FullInput) (W : List Witness)
    (d : List DocRow) (j : List CalculationRow) : Prop :=
  hostSelected = selectedInput ∧ submitted = hostSelected ∧
  RootObligations W ∧
  readDoc d = some expectedDoc ∧
  readCalculation j = some expectedCalculation

theorem seven_axis_business_root (hostSelected submitted : FullInput)
    (d : List DocRow) (j : List CalculationRow)
    (h : checkSevenAxisBundle hostSelected submitted d j = true) :
    ∃ W, SevenTaskSat hostSelected submitted W d j := by
  unfold checkSevenAxisBundle at h
  cases hd : readDoc d with
  | none => simp [hd] at h
  | some dv =>
    cases hj : readCalculation j with
    | none => simp [hd, hj] at h
    | some jv =>
      simp only [hd, hj] at h
      have hparts : hostSelected = selectedInput ∧ submitted = hostSelected ∧
          dv = expectedDoc ∧ jv = expectedCalculation := of_decide_eq_true h
      refine ⟨rootRows, hparts.1, hparts.2.1,
        ⟨root_worlds_match, root_joint_sem, root_task_sat⟩, ?_, ?_⟩
      · simpa only [hparts.2.2.1] using hd
      · simpa only [hparts.2.2.2] using hj

theorem full_projection_accepts_normal :
    checkSevenAxisBundle selectedInput selectedInput
      (writeDoc expectedDoc) (writeCalculation expectedCalculation) = true := by
  simp [checkSevenAxisBundle, read_write_doc, read_write_calculation]

/-- Required top-level regression: changed input cannot inherit the old task. -/
theorem wrong_selected_input_rejected (x : FullInput) (hne : x ≠ selectedInput)
    (d : List DocRow) (j : List CalculationRow) :
    checkSevenAxisBundle x x d j = false := by
  unfold checkSevenAxisBundle
  cases hd : readDoc d <;> cases hj : readCalculation j <;> simp [hne]

/-- Any metadata mutation, not merely one hand-picked debtor, is rejected. -/
theorem changed_doc_metadata_rejected (m : DocMeta)
    (hne : m ≠ expectedDoc.meta) :
    checkSevenAxisBundle selectedInput selectedInput
      (writeDoc { expectedDoc with meta := m })
      (writeCalculation expectedCalculation) = false := by
  have hd : ({ expectedDoc with meta := m } : DocValue) ≠ expectedDoc := by
    intro he
    exact hne (congrArg DocValue.meta he)
  simp [checkSevenAxisBundle, read_write_doc, read_write_calculation, hd]

theorem changed_json_metadata_rejected (m : JsonMeta)
    (hne : m ≠ expectedCalculation.meta) :
    checkSevenAxisBundle selectedInput selectedInput
      (writeDoc expectedDoc)
      (writeCalculation { expectedCalculation with meta := m }) = false := by
  have hj : ({ expectedCalculation with meta := m } : CalculationValue) ≠
      expectedCalculation := by
    intro he
    exact hne (congrArg CalculationValue.meta he)
  simp [checkSevenAxisBundle, read_write_doc, read_write_calculation, hj]

/-- Selected input contents, protected metadata, and outputs remain distinct:
the equality proof does not certify truth or legal approval of the input. -/
theorem input_model_preserved (i j : FullInput) (h : CheckFullBinding i j = true) :
    i.context.model_version = j.context.model_version := by
  exact congrArg (fun x : FullInput => x.context.model_version) (full_binding_exact i j h)

theorem input_sources_preserved (i j : FullInput) (h : CheckFullBinding i j = true) :
    i.sources = j.sources := by
  exact congrArg FullInput.sources (full_binding_exact i j h)

/-- Explicit parameterized prerequisites needed BEFORE generalizing the root.
`Nodup` concerns list positions, not merely equal values of duplicate rows. -/
def ScenarioTableWF (s : PrincipalSpec) (rows : List Witness) : Prop :=
  WorldsMatch s.keys s.facts s.constraint rows ∧ (rows.map (·.world)).Nodup

def WeightTableWF (rows : List Witness) (ws : List (ℚ × World)) : Prop :=
  (ws.map Prod.snd).Nodup ∧
  (∀ w, w ∈ ws.map Prod.snd ↔ w ∈ rows.map (·.world)) ∧
  (∀ p ∈ ws, 0 ≤ p.1) ∧ (ws.map Prod.fst).sum = 1


/-- Explicit regressions for the audit's concrete counterexamples. -/
theorem wrong_debtor_rejected :
    checkSevenAxisBundle selectedInput selectedInput
      (writeDoc { expectedDoc with meta := { expectedDoc.meta with debtor := "丙公司" } })
      (writeCalculation expectedCalculation) = false := by
  apply changed_doc_metadata_rejected
  intro h
  have hfield := congrArg DocMeta.debtor h
  simp [expectedDoc, expectedDocMeta, selectedInput] at hfield

theorem wrong_threshold_rejected :
    checkSevenAxisBundle selectedInput selectedInput
      (writeDoc expectedDoc)
      (writeCalculation { expectedCalculation with
        meta := { expectedCalculation.meta with threshold := 9999 } }) = false := by
  apply changed_json_metadata_rejected
  intro h
  have hfield := congrArg JsonMeta.threshold h
  norm_num [expectedCalculation, expectedJsonMeta, selectedInput, rootInput] at hfield

theorem wrong_action_grid_rejected :
    checkSevenAxisBundle selectedInput selectedInput
      (writeDoc expectedDoc)
      (writeCalculation { expectedCalculation with
        meta := { expectedCalculation.meta with options := [860] } }) = false := by
  apply changed_json_metadata_rejected
  intro h
  have hfield := congrArg JsonMeta.options h
  norm_num [expectedCalculation, expectedJsonMeta, selectedInput, rootInput] at hfield

theorem wrong_case_rejected :
    checkSevenAxisBundle selectedInput selectedInput
      (writeDoc { expectedDoc with meta := { expectedDoc.meta with caseId := "OTHER-CASE" } })
      (writeCalculation expectedCalculation) = false := by
  apply changed_doc_metadata_rejected
  intro h
  have hfield := congrArg DocMeta.caseId h
  simp [expectedDoc, expectedDocMeta, selectedInput, selectedContext] at hfield

theorem selected_numerical_correspondence :
    selectedInput.specification = rootSpec ∧
    selectedInput.parameters = rootInput ∧
    selectedInput.relation.principal = rootSpec.principal ∧
    selectedInput.decisionWeights = rootProtected.weights := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  rfl

theorem accepted_root_has_original_input (i s : FullInput)
    (d : List DocRow) (j : List CalculationRow)
    (h : checkSevenAxisBundle i s d j = true) : s = i := by
  obtain ⟨w, hw⟩ := seven_axis_business_root i s d j h
  exact hw.2.1

theorem duplicate_world_positions_rejected (w : World) :
    ¬ ([w,w] : List World).Nodup := by
  simp

end JurisLean.BusinessRoot.SevenAxis
