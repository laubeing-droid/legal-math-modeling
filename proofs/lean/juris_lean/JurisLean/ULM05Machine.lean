import JurisLean.ULM04Obligations

/-! Homogeneous machine, proof-relevant step constructors, and finite progress. -/

namespace JurisLean.ULM

structure RunConfig where
  request : RequestKey
  active : Finset NFNode
  completedEdges : Finset NFEdge
  phase : Nat
deriving DecidableEq, Repr

inductive SemResult where
  | settled (request : RequestKey) (active : Finset NFNode)
  | incomplete (request : RequestKey) (open : Finset OpenObligation)
  | failed (request : RequestKey) (failure : FailureCore)

inductive Machine where
  | running (config : RunConfig)
  | halted (result : SemResult)

namespace Machine

def request : Machine → RequestKey
  | .running c => c.request
  | .halted (.settled r _) => r
  | .halted (.incomplete r _) => r
  | .halted (.failed r _) => r

end Machine

/-- An edge is run-enabled only once in a finite run configuration. -/
def runEnabled (e : NFEdge) (c : RunConfig) : Prop :=
  e.request = c.request ∧
  e.src ⊆ c.active ∧
  e ∉ c.completedEdges

def applyRunEdge (e : NFEdge) (c : RunConfig) : RunConfig :=
  { request := c.request
    active := c.active ∪ e.tgt
    completedEdges := insert e c.completedEdges
    phase := c.phase + 1 }

def Quiescent (g : TypedGraph) (c : RunConfig) : Prop :=
  ∀ e, EdgeWF g e → ¬ runEnabled e c

inductive Step (g : TypedGraph) : Machine → Machine → Prop where
  | edge (c : RunConfig) (e : NFEdge)
      (hwf : EdgeWF g e) (hen : runEnabled e c) :
      Step g (.running c) (.running (applyRunEdge e c))
  | finalize (c : RunConfig) (hq : Quiescent g c) :
      Step g (.running c) (.halted (.settled c.request c.active))

inductive Run (g : TypedGraph) : Machine → Machine → Prop where
  | refl (x : Machine) : Run g x x
  | tail {x y z : Machine} : Run g x y → Step g y z → Run g x z

@[simp] theorem applyRunEdge_request (e : NFEdge) (c : RunConfig) :
    (applyRunEdge e c).request = c.request := rfl

@[simp] theorem applyRunEdge_marks_completed (e : NFEdge) (c : RunConfig) :
    e ∈ (applyRunEdge e c).completedEdges := by
  simp [applyRunEdge]

theorem applied_edge_not_reenabled (e : NFEdge) (c : RunConfig) :
    ¬ runEnabled e (applyRunEdge e c) := by
  intro h
  exact h.2.2 (applyRunEdge_marks_completed e c)

theorem step_preserves_request {g : TypedGraph} {x y : Machine}
    (h : Step g x y) : x.request = y.request := by
  cases h <;> rfl

theorem run_preserves_request {g : TypedGraph} {x y : Machine}
    (h : Run g x y) : x.request = y.request := by
  induction h with
  | refl => rfl
  | tail hrun hstep ih => exact ih.trans (step_preserves_request hstep)

theorem halted_has_no_step {g : TypedGraph} {r : SemResult} {y : Machine} :
    ¬ Step g (.halted r) y := by
  intro h
  cases h


theorem all_graph_edges_completed_quiescent
    {g : TypedGraph} {c : RunConfig}
    (hall : g.edges ⊆ c.completedEdges) : Quiescent g c := by
  intro e he hen
  exact hen.2.2 (hall he.2.1)

end JurisLean.ULM
