import JurisLean.CN.Revision20261101.World

/-!
F07/A10/S2/D2: the legal proof-policy language is distinct from natural truth.
These clauses express a scoped, source-bound method of evaluating admitted
materials. They neither assert that a witness is truthful nor change F.
The three method families and burden allocation have separate types.
-/
namespace JurisLean.CN.Completion20261105
open JurisLean.KernelV3
open JurisLean.CN.Revision20261101

def containsAtom (target : Atom) : Formula → Bool
  | .atom a => a == target
  | .both a b | .either a b => containsAtom target a || containsAtom target b
  | .neg a => containsAtom target a


inductive ProofStandard
  | criminal | civil | administrative
  deriving DecidableEq, Repr

inductive BurdenBearer
  | claimant | defendant | administrativeDefendant | prosecution
  | statutory (question : Ref .query)
  deriving DecidableEq, Repr

inductive ProofCriterion
  | support (claim : Atom)
  | document (material : Ref .material) (source : Ref .document) (claim : Atom)
  | both (left right : ProofCriterion)
  | either (left right : ProofCriterion)
  | neg (body : ProofCriterion)
  | unresolved (reason : UnknownKind)
  deriving DecidableEq, Repr

structure ProofTemplate where
  source : NormRef
  scope : Scope
  standard : ProofStandard
  burden : BurdenBearer
  clauses : List (Atom × ProofCriterion)
  issuer : Ref .actor
  document : Ref .document

def ProofCriterion.scoped (scope : Scope) : ProofCriterion → Bool
  | .support a | .document _ _ a => a.scope == scope
  | .both a b | .either a b => a.scoped scope && b.scoped scope
  | .neg a => a.scoped scope
  | .unresolved _ => true

def ProofTemplate.scoped (t : ProofTemplate) : Bool :=
  t.clauses.all (fun entry => entry.1.scope == t.scope && entry.2.scoped t.scope)

def combineAnd : Check Judgment → Check Judgment → Check Judgment
  | .known .notEstablished, _ => .known .notEstablished
  | _, .known .notEstablished => .known .notEstablished
  | .known a, .known b => .known (andJ a b)
  | .unknown k, _ => .unknown k
  | _, .unknown k => .unknown k

def combineOr : Check Judgment → Check Judgment → Check Judgment
  | .known .established, _ => .known .established
  | _, .known .established => .known .established
  | .known a, .known b => .known (orJ a b)
  | .unknown k, _ => .unknown k
  | _, .unknown k => .unknown k

def criterionSupport (items : List AdmittedItem) (a : Atom) : Check Judgment :=
  let matching := items.filter (fun item => item.raw.atom == a)
  if matching.isEmpty then .unknown .inputUnchecked
  else .known (support matching a)

def criterionDocument (items : List AdmittedItem) (i : Ref .material)
    (source : Ref .document) (a : Atom) : Check Judgment :=
  match items.find? (fun item =>
      item.id == i && item.raw.source == source && item.raw.atom == a) with
  | none => .unknown .inputUnchecked
  | some item =>
    .known (if item.raw.asserted then .established else .notEstablished)

def evalCriterion (items : List AdmittedItem) : ProofCriterion → Check Judgment
  | .support a => criterionSupport items a
  | .document i source a => criterionDocument items i source a
  | .both left right => combineAnd (evalCriterion items left) (evalCriterion items right)
  | .either left right => combineOr (evalCriterion items left) (evalCriterion items right)
  | .neg body =>
    match evalCriterion items body with
    | .known j => .known (notJ j)
    | .unknown k => .unknown k
  | .unresolved k => .unknown k

def templateAtom (template : ProofTemplate) (items : List AdmittedItem)
    (a : Atom) : Check Judgment :=
  match template.clauses.filter (fun entry => entry.1 == a) with
  | [entry] => evalCriterion items entry.2
  | _ => .unknown .inputUnchecked

def evalProofFormula (template : ProofTemplate) (items : List AdmittedItem) :
    Formula → Check Judgment
  | .atom a => templateAtom template items a
  | .both a b => combineAnd (evalProofFormula template items a) (evalProofFormula template items b)
  | .either a b => combineOr (evalProofFormula template items a) (evalProofFormula template items b)
  | .neg a =>
    match evalProofFormula template items a with
    | .known j => .known (notJ j)
    | .unknown k => .unknown k

/- Proof obligations: unknown is not false; proven bad faith is decisive;
   lack of admitted material cannot become a positive criterion. -/
theorem criterion_no_admission (a : Atom) :
    evalCriterion [] (.support a) = .unknown .inputUnchecked := by
  simp [evalCriterion, criterionSupport]

theorem criterion_document_no_admission (i : Ref .material) (source : Ref .document) (a : Atom) :
    evalCriterion [] (.document i source a) = .unknown .inputUnchecked := rfl

theorem criterion_unknown_propagates (reason : UnknownKind) :
    evalCriterion [] (.neg (.unresolved reason)) = .unknown reason := rfl

theorem known_bad_faith_decisive (other : Check Judgment) :
    combineAnd (.known .notEstablished) other = .known .notEstablished := rfl

theorem three_methods_separate :
    ProofStandard.criminal ≠ ProofStandard.civil ∧
    ProofStandard.criminal ≠ ProofStandard.administrative ∧
    ProofStandard.civil ≠ ProofStandard.administrative := by decide

/- Both policies consume the same admitted view. A qualified document rule can
   yield a different assessment from unqualified support; neither changes F. -/
def qualifiedExample : ProofCriterion :=
  .document ⟨9⟩ ⟨10⟩ toyAtom

theorem qualified_pending_is_unchecked :
    evalCriterion (admittedView recorded.E [⟨9⟩]) qualifiedExample =
      .unknown .inputUnchecked := by decide

theorem qualified_admitted_is_assessed :
    evalCriterion (admittedView prepared.E [⟨9⟩]) qualifiedExample =
      .known .established := by decide

#print axioms criterion_no_admission
#print axioms criterion_document_no_admission
#print axioms criterion_unknown_propagates
#print axioms known_bad_faith_decisive
#print axioms three_methods_separate
#print axioms qualified_pending_is_unchecked
#print axioms qualified_admitted_is_assessed
end JurisLean.CN.Completion20261105

