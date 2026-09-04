import JurisLean.ULM07HornSupport

/-! Finite structural argument carrier and construction coverage checker. -/

namespace JurisLean.ULM

/-- One labelled AND-support hyperedge. Alternative edges with the same
conclusion remain distinct OR-support routes. -/
structure SupportHyperedge where
  request : RequestKey
  rule : JurisLean.LegalId .rule
  premises : Finset TaggedAtom
  conclusion : TaggedAtom
deriving DecidableEq

/-- Mathematical argument identity is the full labelled support hypergraph, not
an uninterpreted digest, a premise set, or a run-local counter. Finsets already
quotient traversal order and duplicate storage. -/
structure CanonicalArgument where
  request : RequestKey
  conclusion : TaggedAtom
  basePremises : Finset TaggedAtom
  supportEdges : Finset SupportHyperedge
deriving DecidableEq

/-- Direct support dependency. `premise` is strictly below `conclusion` in a
well-founded argument. -/
def SupportDependsOn (a : CanonicalArgument)
    (premise conclusion : TaggedAtom) : Prop :=
  ∃ edge ∈ a.supportEdges,
    premise ∈ edge.premises ∧ edge.conclusion = conclusion

/-- A concrete node reaches the argument root through one or more real support
edges, or is the root itself. -/
def SupportReachesRoot (a : CanonicalArgument) (node : TaggedAtom) : Prop :=
  node = a.conclusion ∨
    Relation.TransGen (SupportDependsOn a) node a.conclusion

/-- A premise is available only as a declared base premise or as the conclusion
of another actual support edge. This excludes dangling, invented subproofs. -/
def SupportNodeAvailable (a : CanonicalArgument) (node : TaggedAtom) : Prop :=
  node ∈ a.basePremises ∨
    ∃ edge ∈ a.supportEdges, edge.conclusion = node

/-- Cyclic rule graphs may exist globally; one concrete argument derivation must
still be finite and well founded. -/
def SupportWellFounded (a : CanonicalArgument) : Prop :=
  WellFounded (SupportDependsOn a)

/-- Named fields avoid a brittle conjunction-projection API and make the carrier
contract explicit: no dangling nodes, request mixing, dependency erasure, or
cyclic concrete derivations. -/
structure ArgumentWF (a : CanonicalArgument) : Prop where
  conclusionRequest : a.conclusion.request = a.request
  rootAvailable : SupportNodeAvailable a a.conclusion
  baseRequest : ∀ p ∈ a.basePremises,
    p.request = a.request ∧ p.dependencies ⊆ a.conclusion.dependencies
  edgeRequest : ∀ e ∈ a.supportEdges,
    e.request = a.request ∧ e.conclusion.request = a.request
  edgePremisesNonempty : ∀ e ∈ a.supportEdges, e.premises.Nonempty
  edgePremisesAvailable : ∀ e ∈ a.supportEdges, ∀ p ∈ e.premises,
    SupportNodeAvailable a p
  edgePremiseRequest : ∀ e ∈ a.supportEdges, ∀ p ∈ e.premises,
    p.request = a.request ∧
      p.dependencies ⊆ e.conclusion.dependencies
  baseReachesRoot : ∀ p ∈ a.basePremises, SupportReachesRoot a p
  edgeReachesRoot : ∀ e ∈ a.supportEdges,
    SupportReachesRoot a e.conclusion
  wellFounded : SupportWellFounded a

structure ArgumentConstructionResult where
  request : RequestKey
  arguments : Finset CanonicalArgument
deriving DecidableEq

/-- Relative completeness is equality with the finite frozen expected carrier. -/
def ArgumentCoverage
    (expected actual : Finset CanonicalArgument) : Prop :=
  actual = expected

/-- Executable finite equality checker for the declared carrier. It is not yet
a refinement proof for the production argument generator. -/
def checkArgumentCoverage
    (expected actual : Finset CanonicalArgument) : Bool :=
  if actual = expected then true else false

theorem checkArgumentCoverage_sound
    {expected actual : Finset CanonicalArgument}
    (h : checkArgumentCoverage expected actual = true) :
    ArgumentCoverage expected actual := by
  unfold checkArgumentCoverage at h
  split at h
  · assumption
  · simp at h

theorem checkArgumentCoverage_complete
    {expected actual : Finset CanonicalArgument}
    (h : ArgumentCoverage expected actual) :
    checkArgumentCoverage expected actual = true := by
  unfold ArgumentCoverage at h
  unfold checkArgumentCoverage
  simp [h]

/-- Equality with a frozen expected carrier transfers its independently proved
well-formedness to every actual argument. The Boolean coverage checker does not
attempt to decide `WellFounded`. -/
theorem covered_argument_is_well_formed
    {expected actual : Finset CanonicalArgument}
    (hCoverage : ArgumentCoverage expected actual)
    (hExpectedWF : ∀ a ∈ expected, ArgumentWF a)
    {a : CanonicalArgument} (hActual : a ∈ actual) :
    ArgumentWF a := by
  rw [hCoverage] at hActual
  exact hExpectedWF a hActual

structure ArgumentSupportedPosition where
  candidate : PositionCandidate
  argument : CanonicalArgument
  sameRequest : argument.request = candidate.request
  sameClaim : argument.conclusion.atom = candidate.claim.payload

/-- Query projection from a structural argument. -/
def CanonicalArgument.claim (a : CanonicalArgument) :
    JurisLean.LegalId .claim :=
  { payload := a.conclusion.atom }

theorem argument_supported_position_preserves_request
    (p : ArgumentSupportedPosition) :
    p.argument.request = p.candidate.request := p.sameRequest

theorem argument_supported_position_preserves_claim
    (p : ArgumentSupportedPosition) :
    p.argument.claim = p.candidate.claim := by
  apply JurisLean.LegalId.ext
  exact p.sameClaim

theorem argument_wf_has_well_founded_support
    {a : CanonicalArgument} (h : ArgumentWF a) :
    SupportWellFounded a := h.wellFounded

theorem argument_wf_has_no_dangling_edge
    {a : CanonicalArgument} (h : ArgumentWF a)
    {e : SupportHyperedge} (he : e ∈ a.supportEdges) :
    SupportReachesRoot a e.conclusion :=
  h.edgeReachesRoot e he

end JurisLean.ULM
