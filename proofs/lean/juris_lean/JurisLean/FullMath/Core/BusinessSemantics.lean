import JurisLean.FullMath.Core.Foundations

/-!
F01 — Independent joint-witness semantics.

`Phi I w` is defined only from the environment's declared component
predicates and the witness itself; it never consults a solver, a stored
status or a rendered report. Every output view is a denotation of declared
observations over witnesses.
-/

namespace JurisLean.FullMath.Core

/-- Joint witness `w = (facts, arguments, extensions, claims, quantities,
probabilities, actions, burdens, documentView)`. -/
structure Witness where
  facts : List (String × FactStatus)
  arguments : List String
  extensions : List String
  claims : List String
  quantities : List (String × Quantity)
  probabilities : List (String × ℚ)
  actions : List String
  burdens : List (String × String)
  documentView : List (String × String)

/-- Environment `I = (κ, Σ, F, R, Γ, Q, U)`: indexed scope, declared facts and
rules, declared requirement and legal-action sets, per-component admission
predicates and the joint constraint Γ. -/
structure Env where
  scope : Scope
  declaredFacts : List (String × FactStatus)
  rules : List (List String × String)
  requirements : List String
  legalActions : List String
  factAdmissible : String × FactStatus → Prop
  quantityAdmissible : String × Quantity → Prop
  probabilityAdmissible : String × ℚ → Prop
  gamma : Witness → Prop

/-! Independent component predicates. -/

/-- Every fact of the witness is admitted by the environment. -/
def PhiF (I : Env) (w : Witness) : Prop := ∀ p ∈ w.facts, I.factAdmissible p

/-- Burden records exist for every disputed fact. -/
def PhiB (I : Env) (w : Witness) : Prop :=
  ∀ p ∈ w.facts, p.2 = FactStatus.disputed → ∃ b ∈ w.burdens, b.1 = p.1

/-- Every claim of the witness links to a declared requirement. -/
def PhiQ (I : Env) (w : Witness) : Prop := ∀ c ∈ w.claims, c ∈ I.requirements

/-- Every quantity is admissible for its key. -/
def PhiN (I : Env) (w : Witness) : Prop :=
  ∀ p ∈ w.quantities, I.quantityAdmissible p

/-- Every probability entry is admissible for its key. -/
def PhiP (I : Env) (w : Witness) : Prop :=
  ∀ p ∈ w.probabilities, I.probabilityAdmissible p

/-- Every action of the witness is a declared legal action. -/
def PhiA (I : Env) (w : Witness) : Prop := ∀ a ∈ w.actions, a ∈ I.legalActions

/-- The total independent semantics: conjunction of all components and Γ. -/
def Phi (I : Env) (w : Witness) : Prop :=
  PhiF I w ∧ PhiN I w ∧ PhiB I w ∧ PhiQ I w ∧ PhiP I w ∧ PhiA I w ∧ I.gamma w

/-- Solutions of an environment: exactly the witnesses satisfying Φ. -/
def Sol (I : Env) : Set Witness := {w | Phi I w}

/-! Observation views. -/

/-- Kinds of declared observations. -/
inductive ObsKind where
  | factObs
  | argumentObs
  | extensionObs
  | claimObs
  | quantityObs
  | probabilityObs
  | actionObs
  | burdenObs
  | documentObs
  deriving DecidableEq

/-- A named observation reads one projection of the witness. -/
def observe (k : ObsKind) (w : Witness) : List String :=
  match k with
  | .factObs => w.facts.map Prod.fst
  | .argumentObs => w.arguments
  | .extensionObs => w.extensions
  | .claimObs => w.claims
  | .quantityObs => w.quantities.map Prod.fst
  | .probabilityObs => w.probabilities.map Prod.fst
  | .actionObs => w.actions
  | .burdenObs => w.burdens.map Prod.fst
  | .documentObs => w.documentView.map Prod.fst

/-- The protected output of a run is exactly the denotation of the declared
observation kinds; it reads nothing else. -/
def protectedView (w : Witness) : ObsKind → List String :=
  observe · w

/-- F01(a): membership in `Sol` is by definition Φ, never by a status bit. -/
theorem sol_membership (I : Env) (w : Witness) : w ∈ Sol I ↔ Phi I w := Iff.rfl

/-- F01(b): Φ decomposes into exactly the independent component predicates. -/
theorem phi_iff_components (I : Env) (w : Witness) :
    Phi I w ↔ (PhiF I w ∧ PhiN I w ∧ PhiB I w ∧ PhiQ I w ∧ PhiP I w ∧ PhiA I w ∧ I.gamma w) :=
  Iff.rfl

/-- F01(c): outputs are denotations — witnesses agreeing on all declared
observations have identical protected views. -/
theorem protectedView_congr (w w' : Witness)
    (h : ∀ k, observe k w = observe k w') :
    protectedView w = protectedView w' := by
  funext k
  exact h k

/-- Environment extension: every component predicate of `I'` is implied by the
corresponding predicate of `I` (requirements and legal actions only grow). -/
def EnvExtends (I I' : Env) : Prop :=
  I.scope = I'.scope ∧
  (∀ p, I.factAdmissible p → I'.factAdmissible p) ∧
  (∀ p, I.quantityAdmissible p → I'.quantityAdmissible p) ∧
  (∀ p, I.probabilityAdmissible p → I'.probabilityAdmissible p) ∧
  (∀ w, I.gamma w → I'.gamma w) ∧
  I.requirements ⊆ I'.requirements ∧ I.legalActions ⊆ I'.legalActions

/-- F01(d): semantics monotonicity — relaxing the environment keeps solutions. -/
theorem sol_mono (I I' : Env) (h : EnvExtends I I') : Sol I ⊆ Sol I' := by
  intro w hw
  have hw' : Phi I w := hw
  have hF : PhiF I w → PhiF I' w := fun hf p hp => h.2.1 p (hf p hp)
  have hN : PhiN I w → PhiN I' w := fun hn p hp => h.2.2.1 p (hn p hp)
  have hP : PhiP I w → PhiP I' w := fun hp p hp' => h.2.2.2.1 p (hp p hp')
  have hG : I.gamma w → I'.gamma w := h.2.2.2.2.1
  have hQ : PhiQ I w → PhiQ I' w := fun hq c hc => h.2.2.2.2.2.1 (hq c hc)
  have hA : PhiA I w → PhiA I' w := fun ha a ha' => h.2.2.2.2.2.2 (ha a ha')
  exact ⟨hF hw'.1, hN hw'.2.1, hw'.2.2.1, hQ hw'.2.2.2.1, hP hw'.2.2.2.2.1,
    hA hw'.2.2.2.2.2.1, hG hw'.2.2.2.2.2.2⟩

end JurisLean.FullMath.Core
