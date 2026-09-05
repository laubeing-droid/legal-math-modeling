import JurisLean.ULM06FactEvidence
import JurisLean.HornFixedPoint

/-! Request-bound tagged Horn support closure and position-candidate separation. -/

namespace JurisLean.ULM

/-- The existing proved `HornSystem` is reused as the executable fixed-point
kernel. This wrapper adds the request identity that the generic kernel does not
know about. -/
structure TaggedHornSystem where
  request : RequestKey
  system : HornSystem TaggedAtom
  universeRequestBound : ∀ atom ∈ system.univ, atom.request = request

/-- Exact finite least fixed point from the existing proved Horn kernel. -/
def supportClosure (sys : TaggedHornSystem) : Finset TaggedAtom :=
  FiniteMonotoneSystem.iter
    (HornSystem.toFiniteMonotoneSystem sys.system) sys.system.univ.card

@[simp] theorem supportClosure_fixed (sys : TaggedHornSystem) :
    HornSystem.TH sys.system (supportClosure sys) = supportClosure sys := by
  exact HornSystem.horn_result_fixed_point sys.system

theorem supportClosure_least (sys : TaggedHornSystem)
    (s : Finset TaggedAtom) (hs : HornSystem.TH sys.system s = s) :
    supportClosure sys ⊆ s := by
  exact HornSystem.horn_result_least_fixed_point sys.system s hs

theorem supportClosure_request_bound
    (sys : TaggedHornSystem) {atom : TaggedAtom}
    (h : atom ∈ supportClosure sys) : atom.request = sys.request := by
  have huniv : atom ∈ sys.system.univ :=
    FiniteMonotoneSystem.iter_subset_univ
      (HornSystem.toFiniteMonotoneSystem sys.system)
      sys.system.univ.card h
  exact sys.universeRequestBound atom huniv

structure PositionCandidate where
  claim : JurisLean.LegalId .claim
  request : RequestKey
  support : Finset TaggedAtom
deriving DecidableEq

def CandidateWF (sys : TaggedHornSystem) (c : PositionCandidate) : Prop :=
  c.request = sys.request ∧ c.support ⊆ supportClosure sys

noncomputable def generateCandidates
    (sys : TaggedHornSystem) (pool : Finset PositionCandidate) :
    Finset PositionCandidate := by
  classical
  exact pool.filter (CandidateWF sys)

theorem generated_candidate_sound
    {sys : TaggedHornSystem} {pool : Finset PositionCandidate}
    {c : PositionCandidate} (h : c ∈ generateCandidates sys pool) :
    CandidateWF sys c := by
  classical
  exact (Finset.mem_filter.mp h).2

theorem generated_candidate_request_bound
    {sys : TaggedHornSystem} {pool : Finset PositionCandidate}
    {c : PositionCandidate} (h : c ∈ generateCandidates sys pool) :
    c.request = sys.request :=
  (generated_candidate_sound h).1

end JurisLean.ULM
