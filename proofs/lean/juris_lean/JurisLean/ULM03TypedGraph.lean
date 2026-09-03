import JurisLean.ULM02Outcome

/-! Finite kind-indexed incidence graph and request-preserving local relation. -/

namespace JurisLean.ULM

/-- Node identity carries an explicit kind.  Full dependent payload refinement is
an implementation-refinement obligation, not silently claimed by this skeleton. -/
structure NFNode where
  kind : NodeKind
  ident : String
deriving DecidableEq, Repr

structure NFEdge where
  ident : String
  kind : EdgeKind
  request : RequestKey
  src : Finset NFNode
  tgt : Finset NFNode
  claims : Finset ClaimKind
deriving DecidableEq, Repr

structure TypedGraph where
  request : RequestKey
  nodes : Finset NFNode
  edges : Finset NFEdge
deriving DecidableEq, Repr

/-- Incidence, request identity, and carrier membership are explicit. -/
def EdgeWF (g : TypedGraph) (e : NFEdge) : Prop :=
  g.request.WellFormed ∧
  e ∈ g.edges ∧
  e.request = g.request ∧
  e.src ⊆ g.nodes ∧
  e.tgt ⊆ g.nodes

structure ConnectWitness (left right : NFEdge) where
  sameRequest : left.request = right.request
  node : NFNode
  leftTarget : node ∈ left.tgt
  rightSource : node ∈ right.src

structure LocalState where
  request : RequestKey
  active : Finset NFNode
deriving DecidableEq, Repr

/-- An edge is enabled only on its own request and when every source is active. -/
def Enabled (e : NFEdge) (s : LocalState) : Prop :=
  e.request = s.request ∧ e.src ⊆ s.active

/-- The minimal executable edge effect adds only declared target nodes and keeps
request identity. -/
def applyEdge (e : NFEdge) (s : LocalState) : LocalState :=
  { request := s.request, active := s.active ∪ e.tgt }

@[simp] theorem applyEdge_request (e : NFEdge) (s : LocalState) :
    (applyEdge e s).request = s.request := rfl

theorem target_subset_applyEdge (e : NFEdge) (s : LocalState) :
    e.tgt ⊆ (applyEdge e s).active := by
  intro x hx
  exact Finset.mem_union_right _ hx

/-- The graph-local relation is generated only by a well-formed graph edge. -/
def LocalTransition (g : TypedGraph) (s t : LocalState) : Prop :=
  ∃ e, EdgeWF g e ∧ Enabled e s ∧ t = applyEdge e s

theorem localTransition_preserves_request {g : TypedGraph} {s t : LocalState}
    (h : LocalTransition g s t) : t.request = s.request := by
  rcases h with ⟨e, _, _, rfl⟩
  rfl

theorem localTransition_has_declared_edge {g : TypedGraph}
    {s t : LocalState} (h : LocalTransition g s t) :
    ∃ e ∈ g.edges, e.tgt ⊆ t.active := by
  rcases h with ⟨e, hwf, _, rfl⟩
  exact ⟨e, hwf.2.1, target_subset_applyEdge e s⟩

end JurisLean.ULM
