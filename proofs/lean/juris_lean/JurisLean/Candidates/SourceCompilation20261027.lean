import JurisLean.Candidates.CompilerProvenance20261027
import JurisLean.Seams.UnifiedNeedlesS0S1
import JurisLean.Seams.UnifiedQuantLedger

/-!
Original 03.1/03.5 and 07.2/07.3: a finite fixed-template extractor retaining
the complete consumed view. It selects an interpretation of the exact raw
snapshot, and feeds that selected output into the existing provenance checker.
Catalog membership establishes a binding, not source truth or legal effects.
The semantic theorem states the primitive interpretation/rule premises openly.
-/

namespace JurisLean.Candidates.SourceCompilation20261027

open JurisLean.Candidates.Final20261021

inductive LegalObject where
  | party (id : PartyId)
  | debt (id : Nat)
  | payment (id : PaymentId)
  | document (id : Nat)
  | relation (id : RelationId)
  deriving DecidableEq, Repr

structure Fragment where
  source : SourceRef
  position : Nat
  sourceOrder : Nat
  raw : String
  deriving DecidableEq, Repr

structure MaterialSnapshot where
  gamma : Gamma
  parseVersion : Nat
  unitVersion : Nat
  fragments : List Fragment
  deriving DecidableEq, Repr

structure Citation where
  source : SourceRef
  position : Nat
  parseVersion : Nat
  unitVersion : Nat
  deriving DecidableEq, Repr

structure Quoted (A : Type) where
  citation : Citation
  value : A

structure FullDebt where
  item : JurisLean.Seams.UnifiedQuantLedger.LedgerItem
  debtRel : RelationId
  obligor : PartyId
  unit : AmountTag

structure FullPayment where
  key : PaymentId
  targetDebt : Nat
  payload : PaymentPayload
  deriving DecidableEq, Repr

inductive SourceHistory where
  | formation (source : SourceRef) (relation : RelationId)
  | payment (source : SourceRef) (key : PaymentId)
  deriving DecidableEq, Repr

-- The existing CaseRecord and LedgerItem are retained whole, not recreated
-- from their keys. History positions are the actual list positions.
structure ConsumedView where
  record : Quoted JurisLean.Seams.UnifiedNeedlesS0S1.CaseRecord
  relations : List (Quoted DebtRecord)
  ledger : List (Quoted FullDebt)
  payments : List (Quoted FullPayment)
  initialHistory : List (Quoted SourceHistory)
  historyEvents : List (Quoted SourceHistory)
  objects : List (Quoted (SourceRef × LegalObject))
  observed : Quoted (SourceRef × RelationId)
  atoms : List (Quoted Nat)

def citations (v : ConsumedView) : List Citation :=
  [v.record.citation, v.observed.citation] ++ v.relations.map Quoted.citation ++
  v.ledger.map Quoted.citation ++ v.payments.map Quoted.citation ++
  v.initialHistory.map Quoted.citation ++ v.historyEvents.map Quoted.citation ++
  v.objects.map Quoted.citation ++ v.atoms.map Quoted.citation

def citationPresent (s : MaterialSnapshot) (c : Citation) : Bool :=
  decide (c.parseVersion = s.parseVersion ∧ c.unitVersion = s.unitVersion) &&
  s.fragments.any (fun f => decide (f.source = c.source ∧ f.position = c.position))

def resolve (v : ConsumedView) (ref : SourceRef) : Result LegalObject :=
  match (v.objects.filter fun x => decide (x.value.1 = ref)).map (fun x => x.value.2) with
  | [obj] => .known obj
  | [] => .unknown .identityUnknown
  | _ => .conflict ref.value 2

def viewChecks (s : MaterialSnapshot) (v : ConsumedView) : Bool :=
  (citations v).all (citationPresent s) &&
  decide (resolve v v.observed.value.1 = .known (.relation v.observed.value.2)) &&
  v.payments.all (fun p => decide (p.value.payload.caseId = s.gamma.caseId ∧
    p.value.payload.caseRevision = s.gamma.caseRevision ∧
    p.value.payload.source = p.citation.source))

structure InterpretationRow where
  material : MaterialSnapshot
  branch : Nat
  decoded : ConsumedView

structure ExtractedView where
  material : MaterialSnapshot
  branch : Nat
  decoded : ConsumedView

-- A finite decoder table is fixed for this call. Neither an independent
-- candidate payload nor a separate compiler fact list is accepted here.
def matchingRows (s : MaterialSnapshot) (branch : Nat)
    (catalog : List InterpretationRow) : List InterpretationRow :=
  catalog.filter fun row => decide (row.material = s ∧ row.branch = branch)

def extractView (s : MaterialSnapshot) (branch : Nat)
    (catalog : List InterpretationRow) : Result ExtractedView :=
  if (s.fragments.map fun f => (f.source, f.position)).Nodup then
    match matchingRows s branch catalog with
    | [row] =>
        if viewChecks s row.decoded then .known ⟨s, branch, row.decoded⟩
        else .rejected .observationBindingMismatch
    | [] => .unknown .missingEvidence
    | _ => .conflict branch 2
  else .rejected .observationBindingMismatch

theorem extracted_view_is_exact_selected_payload (s : MaterialSnapshot) (branch : Nat)
    (catalog : List InterpretationRow) (out : ExtractedView)
    (accepted : extractView s branch catalog = .known out) :
    out.material = s ∧ out.branch = branch ∧ viewChecks s out.decoded = true ∧
    ∃ row ∈ catalog, row.material = s ∧ row.branch = branch ∧ row.decoded = out.decoded := by
  unfold extractView at accepted
  split at accepted
  next unique =>
    cases rows : matchingRows s branch catalog with
    | nil => simp [rows] at accepted
    | cons row tail =>
        cases tail with
        | cons second rest => simp [rows] at accepted
        | nil =>
            simp only [rows] at accepted
            split at accepted
            next valid =>
              cases accepted
              have member : row ∈ matchingRows s branch catalog := by simp [rows]
              have selected := List.mem_filter.mp member
              have matches : row.material = s ∧ row.branch = branch := of_decide_eq_true selected.2
              exact ⟨rfl, rfl, valid, row, selected.1, matches.1, matches.2, rfl⟩
            next invalid => cases accepted
  next duplicate => cases accepted

def recordOf (v : ExtractedView) : JurisLean.Seams.UnifiedNeedlesS0S1.CaseRecord := v.decoded.record.value

theorem actual_record_observations (v : ExtractedView) :
    (recordOf v).key = v.decoded.record.value.key ∧
    (recordOf v).claimedAmount = v.decoded.record.value.claimedAmount ∧
    (recordOf v).registered = v.decoded.record.value.registered := by
  exact ⟨rfl, rfl, rfl⟩

theorem extracted_observed_reference_resolves (s : MaterialSnapshot) (branch : Nat)
    (catalog : List InterpretationRow) (out : ExtractedView)
    (accepted : extractView s branch catalog = .known out) :
    resolve out.decoded out.decoded.observed.value.1 =
      .known (.relation out.decoded.observed.value.2) := by
  have valid := (extracted_view_is_exact_selected_payload s branch catalog out accepted).2.2.1
  simp only [viewChecks, Bool.and_eq_true, decide_eq_true_eq] at valid
  exact valid.1.2

def leafOf (v : ExtractedView) (fact : Quoted Nat) : CompilerProvenance20261027.Leaf :=
  ⟨fact.citation.source, fact.citation.position, v.material.gamma.interpretation, fact.value⟩

def extractedLeaves (v : ExtractedView) : List CompilerProvenance20261027.Leaf := v.decoded.atoms.map (leafOf v)

def leafCheck (v : ExtractedView) (ctx : Gamma) (leaf : CompilerProvenance20261027.Leaf) : Bool :=
  decide (ctx = v.material.gamma ∧ leaf ∈ extractedLeaves v)

theorem accepted_leaf_has_actual_source (v : ExtractedView) (ctx : Gamma) (leaf : CompilerProvenance20261027.Leaf)
    (checked : leafCheck v ctx leaf = true) :
    ctx = v.material.gamma ∧ ∃ fact ∈ v.decoded.atoms,
      leaf = leafOf v fact := by
  have valid : ctx = v.material.gamma ∧ leaf ∈ extractedLeaves v := of_decide_eq_true checked
  obtain ⟨fact, member, equal⟩ := List.mem_map.mp valid.2
  exact ⟨valid.1, fact, member, equal.symm⟩

structure CompiledView where
  source : ExtractedView
  evidence : CompilerProvenance20261027.Evidence
  closure : List Nat

def compileView (s : MaterialSnapshot) (branch : Nat) (catalog : List InterpretationRow)
    (rules : List CompilerProvenance20261027.RuleUse) (ruleGate : Gamma → CompilerProvenance20261027.RuleUse → Bool)
    (nodes : List CompilerProvenance20261027.Node) (root query : Nat) : Result CompiledView :=
  match extractView s branch catalog with
  | .known view =>
      match CompilerProvenance20261027.proposed_provenance_input view.material.gamma rules (leafCheck view)
          ruleGate nodes root query with
      | .known evidence => .known ⟨view, evidence,
          CompilerProvenance20261027.closureFromEvidence view.material.gamma rules ruleGate evidence⟩
      | .unknown e => .unknown e
      | .rejected e => .rejected e
      | .conflict l r => .conflict l r
  | .unknown e => .unknown e
  | .rejected e => .rejected e
  | .conflict l r => .conflict l r

theorem compiler_reads_actual_extracted_output (s : MaterialSnapshot) (branch : Nat)
    (catalog : List InterpretationRow) (rules : List CompilerProvenance20261027.RuleUse)
    (ruleGate : Gamma → CompilerProvenance20261027.RuleUse → Bool) (nodes : List CompilerProvenance20261027.Node) (root query : Nat)
    (out : CompiledView) (accepted : compileView s branch catalog rules ruleGate nodes root query =
      .known out) :
    extractView s branch catalog = .known out.source ∧
    CompilerProvenance20261027.proposed_provenance_input out.source.material.gamma rules (leafCheck out.source)
      ruleGate nodes root query = .known out.evidence ∧
    out.closure = CompilerProvenance20261027.closureFromEvidence out.source.material.gamma rules ruleGate out.evidence := by
  cases extracted : extractView s branch catalog with
  | unknown e => simp [compileView, extracted] at accepted
  | rejected e => simp [compileView, extracted] at accepted
  | conflict l r => simp [compileView, extracted] at accepted
  | known view =>
      cases compiled : CompilerProvenance20261027.proposed_provenance_input view.material.gamma rules (leafCheck view)
          ruleGate nodes root query with
      | unknown e => simp [compileView, extracted, compiled] at accepted
      | rejected e => simp [compileView, extracted, compiled] at accepted
      | conflict l r => simp [compileView, extracted, compiled] at accepted
      | known evidence =>
          simp only [compileView, extracted, compiled, Result.known.injEq] at accepted
          cases accepted
          exact ⟨extracted, compiled, rfl⟩

theorem actual_compilation_enters_finite_closure (s : MaterialSnapshot) (branch : Nat)
    (catalog : List InterpretationRow) (rules : List CompilerProvenance20261027.RuleUse)
    (ruleGate : Gamma → CompilerProvenance20261027.RuleUse → Bool) (nodes : List CompilerProvenance20261027.Node) (root query : Nat)
    (out : CompiledView) (accepted : compileView s branch catalog rules ruleGate nodes root query =
      .known out) : query ∈ out.closure ∧ CompilerProvenance20261027.BackwardFrom 0 nodes := by
  have flow := compiler_reads_actual_extracted_output s branch catalog rules ruleGate nodes root query out accepted
  rw [flow.2.2]
  exact ⟨CompilerProvenance20261027.u03_1_provenance_consumed_by_finite_closure _ _ _ _ _ _ _ _ flow.2.1,
    (CompilerProvenance20261027.u03_1_checked_provenance_sound _ _ _ _ _ _ _ _ flow.2.1).2.2⟩

-- Interpret relates raw material to primitive typed objects/amounts/actions.
-- Its atom consequence concerns only source atoms, never the final query.
theorem interpreted_material_to_query (s : MaterialSnapshot) (branch : Nat)
    (catalog : List InterpretationRow) (rules : List CompilerProvenance20261027.RuleUse)
    (ruleGate : Gamma → CompilerProvenance20261027.RuleUse → Bool) (nodes : List CompilerProvenance20261027.Node) (root query : Nat)
    (out : CompiledView) (Interpret : MaterialSnapshot → ConsumedView → Prop)
    (truth : Nat → Prop)
    (catalogFaithful : ∀ row ∈ catalog, row.material = s → row.branch = branch →
      Interpret s row.decoded)
    (primitiveMeaning : ∀ decoded, Interpret s decoded → ∀ f ∈ decoded.atoms, truth f.value)
    (rulesSound : ∀ r ∈ CompilerProvenance20261027.activeRules s.gamma rules ruleGate,
      (∀ a ∈ r.premises, truth a) → truth r.conclusion)
    (accepted : compileView s branch catalog rules ruleGate nodes root query = .known out) :
    truth query := by
  have flow := compiler_reads_actual_extracted_output s branch catalog rules ruleGate nodes root query out accepted
  have selected := extracted_view_is_exact_selected_payload s branch catalog out.source flow.1
  obtain ⟨row, member, materialEq, branchEq, decodedEq⟩ := selected.2.2.2
  have interpreted : Interpret s out.source.decoded := by
    rw [← decodedEq]
    exact catalogFaithful row member materialEq branchEq
  apply CompilerProvenance20261027.u03_1_provenance_semantic_composition _ rules (leafCheck out.source)
    ruleGate nodes root query out.evidence truth _ _ flow.2.1
  · intro leaf version valid
    obtain ⟨_, fact, factMember, leafEq⟩ := accepted_leaf_has_actual_source _ _ _ valid
    rw [leafEq]
    exact primitiveMeaning _ interpreted fact factMember
  · simpa only [selected.1] using rulesSound

def compiled (r : Result CompiledView) : Bool :=
  match r with
  | .known _ => true
  | _ => false

def robustCompiled (results : List (Result CompiledView)) : Bool :=
  !results.isEmpty && results.all compiled

theorem robust_compilation_retains_every_branch (results : List (Result CompiledView))
    (accepted : robustCompiled results = true) :
    results ≠ [] ∧ ∀ r ∈ results, ∃ out, r = .known out := by
  have allKnown : ∀ r ∈ results, compiled r = true := by
    exact List.all_eq_true.mp (Bool.and_eq_true.mp accepted).2
  constructor
  · intro empty
    simp [robustCompiled, empty] at accepted
  · intro r member
    have good := allKnown r member
    cases r with
    | known out => exact ⟨out, rfl⟩
    | unknown e => simp [compiled] at good
    | rejected e => simp [compiled] at good
    | conflict l r => simp [compiled] at good

def compileBranches (s : MaterialSnapshot) (branches : List Nat)
    (catalog : List InterpretationRow) (rules : List CompilerProvenance20261027.RuleUse)
    (ruleGate : Gamma → CompilerProvenance20261027.RuleUse → Bool) (nodes : Nat → List CompilerProvenance20261027.Node)
    (root : Nat → Nat) (query : Nat) : List (Result CompiledView) :=
  branches.map fun b => compileView s b catalog rules ruleGate (nodes b) (root b) query

theorem successful_family_does_not_drop_unknown (s : MaterialSnapshot) (branches : List Nat)
    (catalog : List InterpretationRow) (rules : List CompilerProvenance20261027.RuleUse)
    (ruleGate : Gamma → CompilerProvenance20261027.RuleUse → Bool) (nodes : Nat → List CompilerProvenance20261027.Node)
    (root : Nat → Nat) (query branch : Nat) (member : branch ∈ branches)
    (accepted : robustCompiled (compileBranches s branches catalog rules ruleGate nodes root query) = true) :
    ∃ out, compileView s branch catalog rules ruleGate (nodes branch) (root branch) query = .known out := by
  apply (robust_compilation_retains_every_branch _ accepted).2
  exact List.mem_map.mpr ⟨branch, member, rfl⟩

end JurisLean.Candidates.SourceCompilation20261027
