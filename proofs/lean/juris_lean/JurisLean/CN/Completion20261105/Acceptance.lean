import JurisLean.CN.Completion20261105.Checkpoint2

/-!
Remaining concrete obligations: C2 executes all nine operators; C3 proves
different charges for two participants of one event in one shared case; C5
propagates each agreed unknown cause and unresolved statutory conflict. These
synthetic configurations are not assertions about any person's real conduct.
-/
namespace JurisLean.CN.Completion20261105.Acceptance
open JurisLean.KernelV3
open JurisLean.CN.Revision20261101
open InstitutionRules Examples

def opParams : OperatorParams :=
  ⟨[⟨⟨10⟩,⟨61⟩,toyScope,1⟩],
    [⟨toyScope,toyNorm,[.advance,.extend,.restart,.cap,.suspend,.resume],.decide⟩],
    [⟨grant .otherBind .administrator,toyScope.question⟩]⟩
def opStart : Situation :=
  let s := readyCase confirmation .interpretation
  let st := {s.core.state with
    F := [⟨⟨61⟩,⟨12⟩,toyAtom,0⟩]
    clocks := [⟨toyScope,⟨61⟩,1,⟨2⟩,⟨3⟩⟩]}
  s.withCore (s.core.putState st rfl)
def advanced : Situation := advance opStart
  (.operator opParams (.adjust (request .decide) .human ⟨.advance,⟨1⟩,⟨61⟩⟩))

theorem actual_anchor :
    (executeCommand opStart (.operator opParams (.anchor ⟨toyScope,⟨10⟩,1⟩))).answer = .success [⟨61⟩] := by decide
theorem actual_measure :
    (executeCommand opStart (.operator opParams (.measure .day toyScope))).answer = .success ⟨2⟩ := by decide
theorem actual_exclude :
    (executeCommand opStart (.operator opParams (.exclude [1,2,2,3] [2]))).answer = .success [1,3] := by decide

theorem actual_witness :
    (executeCommand opStart (.operator opParams (.witness ⟨⟨9⟩,toyScope,⟨5⟩⟩))).answer = .success ⟨11⟩ := by decide
theorem actual_count :
    (executeCommand opStart (.operator opParams (.count toyScope))).answer = .success 1 := by decide
theorem actual_project :
    (executeCommand opStart (.operator opParams (.project ⟨⟨12⟩,toyScope,toyScope.question,0⟩))).answer =
      .success [⟨61⟩] := by decide

def qscope (n : Nat) : Scope := {toyScope with question := ⟨n⟩}
def qnorm (n : Nat) : NormRef := {toyNorm with id := ⟨n⟩}
def qatom (n p : Nat) : Atom := ⟨qscope n,⟨p⟩⟩
def qrule (n : Nat) : Rule :=
  ⟨qnorm n,qscope n,.both (.atom (qatom n 4)) (.atom (qatom n 5)),
    [⟨10*n⟩,⟨10*n+1⟩],.confirmatory,none⟩
def qrequest (n : Nat) (act : Act) : Request :=
  {request act with scope := qscope n,rule := ⟨n⟩}
def qgrants (n : Nat) : List Grant := grants.map (fun g => {g with scope := qscope n,rule := ⟨n⟩})
def qpolicy (n : Nat) : ProofPolicy := ⟨qnorm n,qscope n,support⟩
def qcall (n : Nat) : Law.Call := ⟨qrequest n .decide,qpolicy n,.human,toyWorld⟩
def qtemplate (n : Nat) : ProofTemplate :=
  ⟨qnorm n,qscope n,.criminal,.prosecution,
    [(qatom n 4,.document ⟨10*n⟩ ⟨10*n⟩ (qatom n 4)),
     (qatom n 5,.document ⟨10*n+1⟩ ⟨10*n+1⟩ (qatom n 5))],⟨12⟩,⟨n⟩⟩
def dualBase : Situation :=
  let st := {initial with
    N := ⟨1,[qrule 100,qrule 101,qrule 102],qgrants 100 ++ qgrants 101 ++ qgrants 102⟩
    F := [⟨ev1,aJia,toyAtom,0⟩,⟨ev2,aJia,toyAtom,0⟩]}
  {Situation.initial with
    core := initialCase.putState st rfl
    participations := jiaParts ++ yiParts
    uses := [⟨qnorm 100,qscope 100,.offense⟩,⟨qnorm 101,qscope 101,.offense⟩,⟨qnorm 102,qscope 102,.offense⟩]
    offenseSlots := [⟨qnorm 100,qscope 100,aJia,ev1,q1,⟨100⟩⟩,
      ⟨qnorm 101,qscope 101,aYi,ev1,q1,⟨101⟩⟩,⟨qnorm 102,qscope 102,aYi,ev2,q1,⟨101⟩⟩]}
def qAdmit (s : Situation) (n offset pred : Nat) : Situation :=
  let id : Ref .material := ⟨10*n+offset⟩
  let raw : Raw id := ⟨qatom n pred,true,⟨id.value⟩,0⟩
  let rc : Receipt raw := ⟨⟨id.value⟩,⟨12⟩,qnorm n,true,true,true,by decide⟩
  advance (advance s (.record id raw)) (.admitEvidence (qrequest n .admitEvidence) .human id raw rc)
def qPrepare (s : Situation) (n : Nat) : Situation :=
  qAdmit (qAdmit (advance s (.addTemplate (qrequest n .addTemplate) (qtemplate n))) n 0 4) n 1 5
def dualCase : Situation := qPrepare (qPrepare (qPrepare dualBase 100) 101) 102

set_option maxRecDepth 4096 in
theorem actual_shared_event_different_charges :
    (executeCommand dualCase (.offenseEvidence (qcall 100) aJia ev1 q1 (qatom 100 4) (qatom 100 5))).answer =
      .success ⟨100⟩ ∧
    (executeCommand dualCase (.offenseEvidence (qcall 101) aYi ev1 q1 (qatom 101 4) (qatom 101 5))).answer =
      .success ⟨101⟩ ∧
    (executeCommand dualCase (.offenseEvidence (qcall 102) aYi ev2 q1 (qatom 102 4) (qatom 102 5))).answer =
      .rejected .prerequisites := by decide

def bScope : Scope := {toyScope with object := ⟨300⟩}
def bRequest : Request := {request .decide with scope := bScope}
def exchangeStart : Situation :=
  let n := {opStart.core.state.N with
    rules := {confirmation with scope := bScope} :: opStart.core.state.N.rules
    grants := {grant .decide .court with scope := bScope} :: opStart.core.state.N.grants}
  let st := {opStart.core.state with N := n}
  {opStart.withCore (opStart.core.putState st rfl) with
    uses := ⟨toyNorm,bScope,.interpretation⟩ :: opStart.uses}
def aAssignment : MeaningAssignment := ⟨toyScope.object,.literal (some (.atom toyAtom))⟩
def bAssignment : MeaningAssignment := ⟨bScope.object,.literal (some (.neg (.atom toyAtom)))⟩
theorem actual_commute :
    (executeCommand exchangeStart (.operator opParams
      (.commute aAssignment bAssignment (request .decide) bRequest))).answer = .success true ∧
    (advance (advance exchangeStart (.assignment aAssignment (request .decide)))
      (.assignment bAssignment bRequest)).meanings toyScope.object = some (.atom toyAtom) ∧
    (advance (advance exchangeStart (.assignment bAssignment bRequest))
      (.assignment aAssignment (request .decide))).meanings toyScope.object = some (.atom toyAtom) := by decide

def unknownState (k : UnknownKind) : Situation := advance (configured toyRule .lifecycle)
  (.addTemplate (request .addTemplate) {template with clauses := [(toyAtom,.unresolved k)]})
theorem three_unknown_exits_are_actual (k : UnknownKind) :
    (executeCommand (unknownState k) (.legal (call .constitute))).answer = .unknown k ∧
    (executeCommand (unknownState k) (.legal (call .constitute))).after.core.state.L = [] := by
  cases k <;> decide

theorem actual_conflict_is_suspended (kind : ConflictKind) :
    (executeCommand {normal with disputes := [(toyScope,kind)]} (.legal (call .decide))).answer =
      .conflict (pendingRoute kind) := by cases kind <;> decide

theorem actual_hohfeld_projection :
    legalPositions formedCase toyScope = hohfeld toyRelation := by decide

inductive OtherTag
  | persuasive | referential | credit | publicValidity
  deriving DecidableEq

def bindingTags (s : Situation) : List (Option OtherTag) := s.core.state.bindings.map (fun b =>
  match b with
  | .decide _ => none
  | .other other => some (match other.source with
      | .persuasive _ => .persuasive | .referential _ _ => .referential
      | .credit _ _ => .credit | .publicValidity _ _ => .publicValidity))

def otherIndex : BindingIndex := ⟨[⟨12⟩],toyScope,0,10⟩
def otherB (source : OtherSource) : OtherBinding := ⟨source,otherIndex,request .otherBind,rfl⟩
def otherStart : Situation := admitOne normal ⟨71⟩ toyAtom true

theorem three_other_sources_stay_separate :
    bindingTags (advance otherStart (.bindOther (otherB (.publicValidity ⟨71⟩ toyNorm)) .human)) =
      [some .publicValidity] ∧
    bindingTags (advance otherStart (.bindOther (otherB (.referential ⟨71⟩ toyNorm)) .human)) =
      [some .referential] ∧
    bindingTags (advance otherStart (.bindOther (otherB (.credit ⟨71⟩ toyNorm)) .human)) =
      [some .credit] := by decide

theorem missing_other_document_not_created :
    (executeCommand normal (.bindOther (otherB (.credit ⟨71⟩ toyNorm)) .human)).answer =
      .unknown .inputUnchecked := by decide


def newlyFound : ExecProc := ⟨⟨900⟩,aD,⟨901⟩⟩
theorem newly_observed_execution_uses_stay_gate :
    (advance accepted (.observeExecution (request .admitEvidence) ⟨9⟩ newlyFound)).stayed.contains newlyFound.id = true ∧
    (advance accepted (.observeExecution (request .admitEvidence) ⟨9⟩ {newlyFound with debtor := aO})).stayed.contains newlyFound.id = false := by decide

def ioChecks : IO Unit := do
  unless decide ((clockAt advanced toyScope).map (fun c => c.elapsed.value) = some 3 ∧
    (executeCommand advanced (.operator opParams (.expire toyScope))).answer = .success true ∧
    advanced.core.state.L = opStart.core.state.L) do throw (IO.userError "actual clock adjustment/expiry failed")
  let actual ← Runtime.serveLine Runtime.testCatalog opStart "operator:2"
  match actual.value with
  | some (.natural 1) => pure ()
  | _ => throw (IO.userError "runtime value did not come from the actual count call")
  IO.println "CN_SCOPE_ACCEPTANCE_PASS"

#eval ioChecks
#print axioms newly_observed_execution_uses_stay_gate
#print axioms three_other_sources_stay_separate
#print axioms missing_other_document_not_created
#print axioms actual_anchor
#print axioms actual_measure
#print axioms actual_exclude
#print axioms actual_witness
#print axioms actual_count
#print axioms actual_project
#print axioms actual_commute
#print axioms actual_shared_event_different_charges
#print axioms three_unknown_exits_are_actual
#print axioms actual_conflict_is_suspended
#print axioms actual_hohfeld_projection
end JurisLean.CN.Completion20261105.Acceptance
