import JurisLean.Candidates.SourceCompilation20261027

#check JurisLean.Candidates.SourceCompilation20261027.extracted_view_is_exact_selected_payload
#print axioms JurisLean.Candidates.SourceCompilation20261027.extracted_view_is_exact_selected_payload
#check JurisLean.Candidates.SourceCompilation20261027.actual_record_observations
#print axioms JurisLean.Candidates.SourceCompilation20261027.actual_record_observations
#check JurisLean.Candidates.SourceCompilation20261027.extracted_observed_reference_resolves
#print axioms JurisLean.Candidates.SourceCompilation20261027.extracted_observed_reference_resolves
#check JurisLean.Candidates.SourceCompilation20261027.accepted_leaf_has_actual_source
#print axioms JurisLean.Candidates.SourceCompilation20261027.accepted_leaf_has_actual_source
#check JurisLean.Candidates.SourceCompilation20261027.compiler_reads_actual_extracted_output
#print axioms JurisLean.Candidates.SourceCompilation20261027.compiler_reads_actual_extracted_output
#check JurisLean.Candidates.SourceCompilation20261027.actual_compilation_enters_finite_closure
#print axioms JurisLean.Candidates.SourceCompilation20261027.actual_compilation_enters_finite_closure
#check JurisLean.Candidates.SourceCompilation20261027.interpreted_material_to_query
#print axioms JurisLean.Candidates.SourceCompilation20261027.interpreted_material_to_query
#check JurisLean.Candidates.SourceCompilation20261027.robust_compilation_retains_every_branch
#print axioms JurisLean.Candidates.SourceCompilation20261027.robust_compilation_retains_every_branch
#check JurisLean.Candidates.SourceCompilation20261027.successful_family_does_not_drop_unknown
#print axioms JurisLean.Candidates.SourceCompilation20261027.successful_family_does_not_drop_unknown

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.SourceCompilation20261027
open JurisLean.Candidates.CompilerProvenance20261027

def sourceCompileGamma : Gamma :=
  ⟨⟨1⟩, 1, 1, "synthetic", 3, 7, 8, ⟨10⟩, ⟨20⟩, ⟨20⟩, 1, 1, 1⟩
def sourceCompileTag : AmountTag := ⟨"CNY", "yuan", 8⟩
def sourceCompileMaterial : MaterialSnapshot :=
  ⟨sourceCompileGamma, 2, 3, [⟨⟨1⟩, 0, 0, "debt 10; A pays 7; relation 9"⟩]⟩
def quotedSource {A : Type} (a : A) : Quoted A := ⟨⟨⟨1⟩, 0, 2, 3⟩, a⟩
def sourceCompilePayment : FullPayment :=
  ⟨⟨10⟩, 20, ⟨⟨1⟩, 1, ⟨9⟩, ⟨1⟩, ⟨2⟩, ⟨7, sourceCompileTag⟩, ⟨1⟩, ⟨100⟩, 8, ⟨5⟩⟩⟩
def sourceCompileView : ConsumedView :=
  { record := quotedSource ⟨⟨0, 1, 2, 1, .normScope⟩, 3, true⟩
    relations := [quotedSource ⟨⟨9⟩, ⟨1⟩, ⟨2⟩, ⟨10, sourceCompileTag⟩, "terms retained"⟩]
    ledger := [quotedSource ⟨⟨20, .principal, .contractStip, 2, .supported, 10⟩,
      ⟨9⟩, ⟨1⟩, sourceCompileTag⟩]
    payments := [quotedSource sourceCompilePayment]
    initialHistory := []
    historyEvents := [quotedSource (.formation ⟨1⟩ ⟨9⟩), quotedSource (.payment ⟨1⟩ ⟨10⟩)]
    objects := [quotedSource (⟨1⟩, .relation ⟨9⟩), quotedSource (⟨2⟩, .debt 20),
      quotedSource (⟨3⟩, .payment ⟨10⟩)]
    observed := quotedSource (⟨1⟩, ⟨9⟩)
    atoms := [quotedSource 1] }
def sourceCompileCatalog : List InterpretationRow := [⟨sourceCompileMaterial, 0, sourceCompileView⟩]
def sourceCompileRule : RuleUse := ⟨50, 8, ⟨[1], 2⟩⟩
def sourceCompileNodes : List Node :=
  [.leaf ⟨⟨1⟩, 0, 7, 1⟩, .fire sourceCompileRule [0]]
def sourceCompileRun (material : MaterialSnapshot) (catalog : List InterpretationRow) : Result CompiledView :=
  compileView material 0 catalog [sourceCompileRule] (fun _ _ => true) sourceCompileNodes 1 2
def extractionKnown (result : Result ExtractedView) : Bool :=
  match result with
  | .known _ => true
  | _ => false

/-- info: true -/
#guard_msgs in
#eval match sourceCompileRun sourceCompileMaterial sourceCompileCatalog with
  | .known out => decide (out.evidence.atom = 2 ∧ 2 ∈ out.closure ∧
      out.evidence.leaves = [(⟨⟨1⟩, 0, 7, 1⟩ : Leaf)] ∧
      (recordOf out.source).claimedAmount = 3 ∧ (recordOf out.source).registered = true ∧
      out.source.decoded.payments.map (fun (p : Quoted FullPayment) => p.value.payload.amount.value) = [7] ∧
      out.source.decoded.ledger.map (fun (d : Quoted FullDebt) => d.value.item.amount) = [10] ∧
      out.source.decoded.historyEvents.map Quoted.value =
        [SourceHistory.formation ⟨1⟩ ⟨9⟩, SourceHistory.payment ⟨1⟩ ⟨10⟩])
  | _ => false

/-- info: true -/
#guard_msgs in
#eval !extractionKnown (extractView sourceCompileMaterial 0 [])

/-- info: true -/
#guard_msgs in
#eval !extractionKnown (extractView sourceCompileMaterial 0 (sourceCompileCatalog ++ sourceCompileCatalog))

/-- info: true -/
#guard_msgs in
#eval !compiled (sourceCompileRun { sourceCompileMaterial with
  fragments := [⟨⟨1⟩, 0, 0, "debt 10; B pays 9; relation 9"⟩] } sourceCompileCatalog)

/-- info: true -/
#guard_msgs in
#eval !compiled (sourceCompileRun { sourceCompileMaterial with parseVersion := 99 } sourceCompileCatalog)

/-- info: true -/
#guard_msgs in
#eval !compiled (sourceCompileRun { sourceCompileMaterial with unitVersion := 99 } sourceCompileCatalog)

/-- info: true -/
#guard_msgs in
#eval
  let bad := { sourceCompileView with observed := quotedSource (⟨1⟩, ⟨99⟩) }
  !extractionKnown (extractView sourceCompileMaterial 0 [⟨sourceCompileMaterial, 0, bad⟩])

/-- info: true -/
#guard_msgs in
#eval
  let bad := { sourceCompileView with atoms := [⟨⟨⟨99⟩, 0, 2, 3⟩, 1⟩] }
  !extractionKnown (extractView sourceCompileMaterial 0 [⟨sourceCompileMaterial, 0, bad⟩])

/-- info: true -/
#guard_msgs in
#eval !compiled (compileView sourceCompileMaterial 0 sourceCompileCatalog [sourceCompileRule]
  (fun _ _ => true) [.leaf ⟨⟨1⟩, 0, 7, 99⟩] 0 99)

/-- info: true -/
#guard_msgs in
#eval
  let bad := { sourceCompileView with payments := [quotedSource
    { sourceCompilePayment with payload := { sourceCompilePayment.payload with caseRevision := 99 } }] }
  !extractionKnown (extractView sourceCompileMaterial 0 [⟨sourceCompileMaterial, 0, bad⟩])

/-- info: true -/
#guard_msgs in
#eval !robustCompiled []

/-- info: true -/
#guard_msgs in
#eval robustCompiled (compileBranches sourceCompileMaterial [0] sourceCompileCatalog
  [sourceCompileRule] (fun _ _ => true) (fun _ => sourceCompileNodes) (fun _ => 1) 2)

/-- info: true -/
#guard_msgs in
#eval !robustCompiled (compileBranches sourceCompileMaterial [0, 1] sourceCompileCatalog
  [sourceCompileRule] (fun _ _ => true) (fun _ => sourceCompileNodes) (fun _ => 1) 2)

/-- info: true -/
#guard_msgs in
#eval
  let duplicate := { sourceCompileMaterial with fragments :=
    sourceCompileMaterial.fragments ++ sourceCompileMaterial.fragments }
  !extractionKnown (extractView duplicate 0 [⟨duplicate, 0, sourceCompileView⟩])

/-- The same record alone does not identify the consumed payment view. Both
alternative tables can bind internally, but they cannot both mean the stated
primitive raw sentence. The primitive interpretation has no discharge claim. -/
def primitivePaymentMeaning (s : MaterialSnapshot) (v : ConsumedView) : Bool :=
  decide (s.fragments.map Fragment.raw = ["debt 10; A pays 7; relation 9"] ∧
    v.payments.map (fun p => (p.value.payload.payer, p.value.payload.amount.value)) = [(⟨1⟩, 7)])

/-- info: true -/
#guard_msgs in
#eval
  let changed := { sourceCompileView with payments := [quotedSource
    { sourceCompilePayment with payload := { sourceCompilePayment.payload with
      payer := ⟨2⟩, amount := ⟨9, sourceCompileTag⟩ } }] }
  extractionKnown (extractView sourceCompileMaterial 0 [⟨sourceCompileMaterial, 0, changed⟩]) &&
    primitivePaymentMeaning sourceCompileMaterial sourceCompileView &&
    !primitivePaymentMeaning sourceCompileMaterial changed &&
    decide (changed.record.value.claimedAmount = sourceCompileView.record.value.claimedAmount ∧
      changed.record.value.registered = sourceCompileView.record.value.registered)

/-- info: true -/
#guard_msgs in
#eval !compiled (compileView sourceCompileMaterial 0 sourceCompileCatalog [sourceCompileRule]
  (fun _ _ => true) [.leaf ⟨⟨1⟩, 99, 7, 1⟩] 0 1)
