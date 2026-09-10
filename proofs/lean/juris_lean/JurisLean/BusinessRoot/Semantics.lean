import Mathlib

/-!
ROOT01 — Independent finite-principal business semantics for the frozen task Q
`SYNTHETIC_EXACT_PRINCIPAL_ANALYTICS_TWO_FILES/1`.

These definitions never mention a checker boolean, a renderer output or a
stored "expected" result: the scenario domain Ω, the joint semantics JointSem,
the task satisfaction TaskSat and the protected record Protected are stated
over the mathematical objects themselves. A scenario (world) is a total
assignment over the declared atom keys only, mirroring the Python reference's
`World = tuple[(key, bool), ...]` shape.

Scope: the fixed synthetic two-file principal task only. This file proves no
legal statement, no real-case claim and no empirical property.
-/

namespace JurisLean.BusinessRoot

/-- Requirement identity of the frozen task Q. -/
def requirementQ : String := "SYNTHETIC_EXACT_PRINCIPAL_ANALYTICS_TWO_FILES/1"

/-- Propositional guard over string atoms; structural, closed syntax. -/
inductive Guard where
  | truthy
  | falsey
  | atom (name : String)
  | neg (a : Guard)
  | both (a b : Guard)
  | either (a b : Guard)
  deriving DecidableEq

/-- A scenario is a total assignment over the declared keys, given positionally. -/
abbrev World := List Bool

/-- Positional atom lookup; undeclared atoms read as `false` by convention and
never occur in well-formed inputs because every referenced atom is declared. -/
def lookupVal : List String → List Bool → String → Bool
  | [], _, _ => false
  | _, [], _ => false
  | k :: ks, v :: vs, a => if k = a then v else lookupVal ks vs a

def Guard.denote (keys : List String) (vals : World) : Guard → Bool
  | .truthy => true
  | .falsey => false
  | .atom a => lookupVal keys vals a
  | .neg a => ! a.denote keys vals
  | .both a b => a.denote keys vals && b.denote keys vals
  | .either a b => a.denote keys vals || b.denote keys vals

/-- Declared facts `F`; `none` marks an atom whose truth is a scenario branch. -/
abbrev Facts := List (String × Option Bool)

def factsExtend (F : Facts) (keys : List String) (vals : World) : Prop :=
  ∀ p ∈ F, match p.2 with
    | none => True
    | some b => lookupVal keys vals p.1 = b

/-- A payment whose recognition in a scenario is conditional on an atom. -/
structure Payment where
  paymentId : String
  amount : ℚ
  recognitionAtom : String
  deriving DecidableEq, Repr

/-- Sum of payment amounts whose recognition atom holds in the scenario.
Structurally recursive definition: every branch reduces cleanly under simp
and the kernel, so the frozen numeric facts decide directly. -/
def recognizedSum : List String → List Payment → World → ℚ
  | _, [], _ => 0
  | keys, p :: rest, vals =>
      (if lookupVal keys vals p.recognitionAtom then p.amount else 0)
        + recognizedSum keys rest vals

/-- R_ξ = P − Σ_j q_j·1_{A_j(ξ)}. -/
def residualOf (principal : ℚ) (keys : List String) (payments : List Payment)
    (vals : World) : ℚ :=
  principal - recognizedSum keys payments vals

/-- Nonnegative clipped principal balance C_ξ. -/
def clipC (r : ℚ) : ℚ := if r ≤ 0 then 0 else r

/-- Nonnegative overpayment residual U_ξ. -/
def clipU (r : ℚ) : ℚ := if r < 0 then -r else 0

/-- The frozen input I0 = (spec, model binding, Q); the requirement identity is
part of the object, not an external claim. -/
structure PrincipalSpec where
  keys : List String
  principal : ℚ
  payments : List Payment
  facts : Facts
  constraint : Guard
  deriving DecidableEq

/-- Ω(I0) membership: the scenario has the declared shape, extends F and
satisfies the joint constraint Γ. Defined independently of any solver. Stated
over the explicit fields so that structural reasoning never needs projections. -/
def DomainOf (keys : List String) (F : Facts) (Γ : Guard) (vals : World) : Prop :=
  vals.length = keys.length ∧ factsExtend F keys vals ∧ Γ.denote keys vals = true

def InOmega (s : PrincipalSpec) (vals : World) : Prop :=
  DomainOf s.keys s.facts s.constraint vals

/-- One business outcome row: its scenario plus the C/U decomposition. -/
structure Witness where
  world : World
  principalBalance : ℚ
  overpaymentResidual : ℚ
  deriving Repr

/-- Worlds(W) = Ω(I0): every Ω member appears exactly once as a row world, and
no row world lies outside Ω. Stated without reference to any algorithm. -/
def WorldsMatch (keys : List String) (F : Facts) (Γ : Guard) (W : List Witness) : Prop :=
  (∀ o ∈ W, DomainOf keys F Γ o.world) ∧
  (∀ vals, DomainOf keys F Γ vals → ∃ o ∈ W, o.world = vals) ∧
  (∀ a ∈ W, ∀ b ∈ W, a.world = b.world → a = b)

/-- Independent joint semantics: each row carries the conservation-plus-
complementarity decomposition of its own scenario. The clipping identities are
NOT part of the definition; they are derived in `PrincipalChecker`. -/
def JointSem (principal : ℚ) (keys : List String) (payments : List Payment)
    (W : List Witness) : Prop :=
  ∀ o ∈ W,
    0 ≤ o.principalBalance ∧ 0 ≤ o.overpaymentResidual ∧
    o.principalBalance * o.overpaymentResidual = 0 ∧
    o.principalBalance - o.overpaymentResidual =
      residualOf principal keys payments o.world

/-- Model inputs of the frozen task: scenario weights over the same Ω, one
threshold, four costs, the declared legal grid and the claimed analytics.
The claimed fields are the submission under test, not their own evidence. -/
structure ModelInputs where
  weights : List (ℚ × World)
  threshold : ℚ
  costP : ℚ
  costD : ℚ
  settleP : ℚ
  settleD : ℚ
  legalOptions : List ℚ
  expectedC : ℚ
  expectedU : ℚ
  eventProbability : ℚ
  lower : ℚ
  upper : ℚ
  eligible : List ℚ
  selected : Option ℚ
  deriving DecidableEq

/-- Weighted value of a per-scenario quantity under the model weights. -/
def weighted (ws : List (ℚ × World)) (f : World → ℚ) : ℚ :=
  (ws.map (fun p => p.1 * f p.2)).sum

/-- Probability mass of the threshold event {C_ξ ≥ t} under the model weights. -/
def eventMass (ws : List (ℚ × World)) (f : World → ℚ) (t : ℚ) : ℚ :=
  (ws.map (fun p => if t ≤ f p.2 then p.1 else 0)).sum

/-- Independent task satisfaction for the frozen Q. The task demands exact
all-scenario analytics over the same Ω, so every claimed analytics field must
equal its independent weighted definition; partial scenario tables cannot
satisfy this because the weights must cover exactly the rows of W. -/
def TaskSat (principal : ℚ) (keys : List String) (payments : List Payment)
    (m : ModelInputs) (W : List Witness) : Prop :=
  (∀ p ∈ m.weights, 0 ≤ p.1) ∧
  (m.weights.map Prod.fst).sum = 1 ∧
  (∀ o ∈ W, ∀ p ∈ m.weights, o.world = p.2 →
      o.principalBalance = clipC (residualOf principal keys payments o.world)) ∧
  (∀ o ∈ W, ∀ p ∈ m.weights, o.world = p.2 →
      o.overpaymentResidual = clipU (residualOf principal keys payments o.world)) ∧
  weighted m.weights
      (fun w => clipC (residualOf principal keys payments w)) = m.expectedC ∧
  weighted m.weights
      (fun w => clipU (residualOf principal keys payments w)) = m.expectedU ∧
  eventMass m.weights
      (fun w => clipC (residualOf principal keys payments w)) m.threshold =
        m.eventProbability ∧
  m.lower = m.expectedC - m.costP + m.settleP ∧
  m.upper = m.expectedC + m.costD - m.settleD ∧
  m.eligible = m.legalOptions.filter
      (fun x => decide (m.lower ≤ x ∧ x ≤ m.upper)) ∧
  (m.selected = none ∨ ∃ x ∈ m.eligible, m.selected = some x)

/-- Abstract protected record of the frozen two-file delivery: requirement
identity, principal, per-scenario rows (condition map with balance and
overpayment), pending scenarios, the analytics block and the delivery notice.
This is the joint read-back target of both actual files. -/
structure Protected where
  requirement : String
  principal : ℚ
  rows : List (List (String × Bool) × ℚ × ℚ)
  pending : List (List (String × Bool))
  expectedC : ℚ
  expectedU : ℚ
  eventProbability : ℚ
  lower : ℚ
  upper : ℚ
  eligible : List ℚ
  selected : Option ℚ
  notice : String
  deriving DecidableEq

/-- The protected record generated from independent objects (principal,
per-scenario condition rows, pending scenarios, analytics) — not from any
renderer output. -/
def protectedOf (principal : ℚ)
    (rows : List (List (String × Bool) × ℚ × ℚ))
    (pending : List (List (String × Bool))) (m : ModelInputs) : Protected :=
  { requirement := requirementQ
    principal := principal
    rows := rows
    pending := pending
    expectedC := m.expectedC
    expectedU := m.expectedU
    eventProbability := m.eventProbability
    lower := m.lower
    upper := m.upper
    eligible := m.eligible
    selected := m.selected
    notice := "SYNTHETIC_CONDITIONAL_MODEL_NOT_LITIGATION_FORECAST" }

/-- Guard for the frozen requirement identity inside any claimed record. -/
def requirementBound (p : Protected) : Prop := p.requirement = requirementQ

end JurisLean.BusinessRoot
