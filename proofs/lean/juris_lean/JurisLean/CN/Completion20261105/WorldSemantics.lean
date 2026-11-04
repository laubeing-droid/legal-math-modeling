import JurisLean.CN.Completion20261105.OperationalReady
import JurisLean.CN.Completion20261105.Execution

/-!
C1/C5/P5: K includes supported legal assessments, not truth-pinned testimony.
The world has one natural/relational projection and a legal-assessment function
indexed by the actual rule and approved method. Compatibility constrains that
function from the same admitted view used by the executable checker. The
all-world guard theorem below reuses Foundation.formula_refines; it does not
assume ProofPolicy soundness or a Ready conclusion in an input ticket.
-/
namespace JurisLean.CN.Completion20261105
open JurisLean.KernelV3
open JurisLean.CN.Revision20261101

def collapse : Check Judgment → Judgment
  | .known j => j
  | .unknown _ => .undetermined

theorem collapse_and (a b : Check Judgment) :
    collapse (combineAnd a b) = andJ (collapse a) (collapse b) := by
  cases a with
  | known ja =>
    cases b with
    | known jb => cases ja <;> cases jb <;> rfl
    | unknown k => cases ja <;> rfl
  | unknown k =>
    cases b with
    | known jb => cases jb <;> rfl
    | unknown l => rfl

theorem collapse_or (a b : Check Judgment) :
    collapse (combineOr a b) = orJ (collapse a) (collapse b) := by
  cases a with
  | known ja =>
    cases b with
    | known jb => cases ja <;> cases jb <;> rfl
    | unknown k => cases ja <;> rfl
  | unknown k =>
    cases b with
    | known jb => cases jb <;> rfl
    | unknown l => rfl

theorem collapse_formula (t : ProofTemplate) (items : List AdmittedItem) (f : Formula) :
    collapse (evalProofFormula t items f) =
      evalFormula (fun a => collapse (templateAtom t items a)) f := by
  induction f with
  | atom a => rfl
  | both a b ha hb => simp only [evalProofFormula,evalFormula,collapse_and,ha,hb]
  | either a b ha hb => simp only [evalProofFormula,evalFormula,collapse_or,ha,hb]
  | neg a ha =>
    simp only [evalProofFormula,evalFormula]
    rw [←ha]
    cases evalProofFormula t items a <;> rfl

def atomAssessment (s : Situation) (law : Rule) (t : IssuedTemplate) (a : Atom) : Judgment :=
  collapse (templateAtom t.body (admittedView s.core.state.E law.materials) a)

structure SemanticWorld where
  nature : PossibleWorld
  assessment : Rule → IssuedTemplate → Atom → Judgment

def semanticCompatible (s : Situation) (world : SemanticWorld) : Prop :=
  legalCompatible s world.nature ∧
  ∀ law ∈ s.core.state.N.rules, ∀ t ∈ selectedTemplates s law, ∀ a,
    Refines (atomAssessment s law t a) (world.assessment law t a)

def semanticKernel (s : Situation) : KernelState (List LegalRelation) SemanticWorld :=
  ⟨s.core.state.L,semanticCompatible s⟩

def canonicalWorld (s : Situation) (nature : PossibleWorld) : SemanticWorld :=
  ⟨nature,atomAssessment s⟩

theorem canonicalWorld_compatible (s : Situation) (w : PossibleWorld)
    (h : legalCompatible s w) : semanticCompatible s (canonicalWorld s w) := by
  refine ⟨h,?_⟩
  intro law hl t ht a
  exact Or.inr rfl

def WorldReady (s : Situation) (law : Rule) (t : IssuedTemplate) : Prop :=
  (∃ z, semanticCompatible s z) ∧
  ∀ z, semanticCompatible s z → evalFormula (z.assessment law t) law.guard = .established

theorem ready_refines_all_supported_worlds (s : Situation) (law : Rule) (t : IssuedTemplate)
    (p : ProofPolicy) (hl : law ∈ s.core.state.N.rules) (h : Ready s law t p) :
    WorldReady s law t := by
  obtain ⟨w,hw⟩ := h.1
  refine ⟨⟨canonicalWorld s w,canonicalWorld_compatible s w hw⟩,?_⟩
  intro z hz
  have href := formula_refines (atomAssessment s law t) (z.assessment law t) law.guard
    (hz.2 law hl t h.2.1)
  have hc : evalFormula (atomAssessment s law t) law.guard = .established := by
    rw [←collapse_formula t.body (admittedView s.core.state.E law.materials) law.guard]
    change collapse (assessed s law t.body) = .established
    rw [h.2.2.1]
    rfl
  rw [hc] at href
  rcases href with bad | good
  · cases bad
  · exact good.symm

theorem actual_legal_step_semantic_ready (s : Situation) (r : Request) (p : ProofPolicy)
    (m : Mode) (w : PossibleWorld)
    (h : (legalDispatch s r p m w).answer = .success ()) :
    ∃ law t, law ∈ s.core.state.N.rules ∧ WorldReady s law t := by
  obtain ⟨law,t,hl,hr⟩ := legalDispatch_success_ready s r p m w h
  exact ⟨law,t,hl,ready_refines_all_supported_worlds s law t p hl hr⟩

/- A fixed trustworthy additional constraint narrows K. This elementary set
   proof does not turn arbitrary admission into natural truth. Actual methods
   with conflicting/withdrawn inputs are recomputed and may be nonmonotone. -/
def addTrustedConstraint (s : Situation) (phi : SemanticWorld → Prop) : Set SemanticWorld :=
  fun z => semanticCompatible s z ∧ phi z

theorem trusted_constraint_narrows (s : Situation) (phi : SemanticWorld → Prop) :
    addTrustedConstraint s phi ⊆ (semanticKernel s).K_et := by
  intro z hz
  exact hz.1

/- Admission changes E, not the independent natural/relational projection.
   It may nevertheless change semanticCompatible through atomAssessment. -/
theorem admission_preserves_natural_K (s : Situation) (r : Request) (m : Mode)
    (i : Ref .material) (raw : Raw i) (receipt : Receipt raw) (w : PossibleWorld) :
    legalCompatible (admission s r m i raw receipt).after w ↔ legalCompatible s w := by
  unfold admission
  repeat' first | rfl | split

#print axioms collapse_formula
#print axioms canonicalWorld_compatible
#print axioms ready_refines_all_supported_worlds
#print axioms actual_legal_step_semantic_ready
#print axioms trusted_constraint_narrows
#print axioms admission_preserves_natural_K
end JurisLean.CN.Completion20261105
