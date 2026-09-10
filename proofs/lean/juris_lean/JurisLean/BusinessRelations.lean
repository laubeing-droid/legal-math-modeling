import Mathlib

/-!
Business-relations additive proof draft. No local Lean execution has occurred.
This file proves statements about explicit finite/typed models, not source-language
interpretation, institutional truth, Python refinement, or unrestricted DOCX.
It takes the canonical case key as a type parameter; it does not create a second key registry.
-/
namespace JurisLean.BusinessRelations

inductive Formula (α : Type) where
  | top | bottom | atom (name : α)
  | neg (a : Formula α)
  | both (a b : Formula α)
  | either (a b : Formula α)

def Formula.eval (v : α → Bool) : Formula α → Bool
  | .top => true
  | .bottom => false
  | .atom x => v x
  | .neg a => !(a.eval v)
  | .both a b => a.eval v && b.eval v
  | .either a b => a.eval v || b.eval v

def Formula.holds (v : α → Bool) : Formula α → Prop
  | .top => True
  | .bottom => False
  | .atom x => v x = true
  | .neg a => ¬ a.holds v
  | .both a b => a.holds v ∧ b.holds v
  | .either a b => a.holds v ∨ b.holds v

theorem guard_reflection (f : Formula α) (v : α → Bool) :
    f.eval v = true ↔ f.holds v := by
  induction f with
  | top => simp [Formula.eval, Formula.holds]
  | bottom => simp [Formula.eval, Formula.holds]
  | atom x => simp [Formula.eval, Formula.holds]
  | neg a ih =>
      simp only [Formula.eval, Formula.holds]
      rw [show (!a.eval v) = true ↔ ¬(a.eval v = true) from by simp, ih]
  | both a b iha ihb =>
      simp only [Formula.eval, Formula.holds]
      rw [show (a.eval v && b.eval v) = true
            ↔ (a.eval v = true ∧ b.eval v = true) from by simp, iha, ihb]
  | either a b iha ihb =>
      simp only [Formula.eval, Formula.holds]
      rw [show (a.eval v || b.eval v) = true
            ↔ (a.eval v = true ∨ b.eval v = true) from by simp, iha, ihb]

def inner {W : Type} (s : Finset W) (p : W → Prop) [DecidablePred p] : Set W :=
  {w | w ∈ s.filter p}

theorem finite_inner_sound {W : Type} (s : Finset W) (p : W → Prop)
    [DecidablePred p] : inner s p ⊆ {w | p w} := by
  intro w hw
  exact (Finset.mem_filter.mp hw).2

theorem finite_exact_of_independent_cover {W : Type} (s : Finset W) (p : W → Prop)
    [DecidablePred p] (cover : ∀ w, p w → w ∈ s) :
    inner s p = {w | p w} := by
  ext w
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr ⟨cover w h, h⟩

/-- The typed base-and-step property, not hash collision resistance. -/
def RelComp (r : A → B → Prop) (s : B → C → Prop) (a : A) (c : C) : Prop :=
  ∃ b, r a b ∧ s b c

theorem composition_sound
    {r r' : A → B → Prop} {s s' : B → C → Prop}
    (hr : ∀ a b, r' a b → r a b) (hs : ∀ b c, s' b c → s b c) :
    ∀ a c, RelComp r' s' a c → RelComp r s a c := by
  intro a c h
  obtain ⟨b, hb, hc⟩ := h
  exact ⟨b, hr a b hb, hs b c hc⟩

/-- Joint constraints are lifted with inverse images, not point embeddings. -/
def joint {ι W : Type} {V : ι → Type}
    (Γ : W → Prop) (project : (i : ι) → W → V i)
    (domains : (i : ι) → Set (V i)) : Set W :=
  {w | Γ w ∧ ∀ i, project i w ∈ domains i}

def reduce {ι W : Type} {V : ι → Type}
    (Γ : W → Prop) (project : (i : ι) → W → V i)
    (domains : (i : ι) → Set (V i)) (i : ι) : Set (V i) :=
  domains i ∩ project i '' joint Γ project domains

theorem concrete_reduction_preserves {ι W : Type} {V : ι → Type}
    (Γ : W → Prop) (project : (i : ι) → W → V i)
    (domains : (i : ι) → Set (V i)) :
    joint Γ project (reduce Γ project domains) = joint Γ project domains := by
  ext w
  constructor
  · intro h
    exact ⟨h.1, fun i => (h.2 i).1⟩
  · intro h
    exact ⟨h.1, fun i => ⟨h.2 i, ⟨w, h, rfl⟩⟩⟩

/-- A ledger checker need not duplicate the solver's clipping algorithm. -/
theorem ledger_complementarity_unique (balance excess residual : ℚ)
    (hb : 0 ≤ balance) (he : 0 ≤ excess)
    (hd : balance - excess = residual) (hc : balance * excess = 0) :
    balance = max residual 0 ∧ excess = max (-residual) 0 := by
  rcases mul_eq_zero.mp hc with h | h
  · subst balance
    have hr : residual ≤ 0 := by linarith
    constructor
    · simp [max_eq_right hr]
    · rw [max_eq_left (by linarith : (0 : ℚ) ≤ -residual)]
      linarith
  · subst excess
    have hr : 0 ≤ residual := by linarith
    constructor
    · rw [max_eq_left hr]
      linarith
    · simp [max_eq_right (by linarith : -residual ≤ (0 : ℚ))]

def rawBalance (principal payment : ℚ) (recognized : Bool) : ℚ :=
  if recognized then principal - payment else principal

def branchSem (principal payment : ℚ) (w : Bool × ℚ) : Prop :=
  (w.1 = false ∧ w.2 = principal) ∨
  (w.1 = true ∧ w.2 = principal - payment)

def branchCandidates (principal payment : ℚ) : Finset (Bool × ℚ) :=
  {(false, principal), (true, principal - payment)}

theorem two_scenarios_exact (principal payment : ℚ) :
    {w | w ∈ branchCandidates principal payment} = {w | branchSem principal payment w} := by
  ext w
  rcases w with ⟨b, y⟩
  cases b <;> simp [branchCandidates, branchSem]

def conditionalExpectation (principal payment p : ℚ) : ℚ :=
  p * rawBalance principal payment true + (1-p) * rawBalance principal payment false

theorem expectation_conservation (principal payment p : ℚ) :
    conditionalExpectation principal payment p = principal - p * payment := by
  dsimp [conditionalExpectation, rawBalance]
  ring

def thresholdProbability (principal payment p threshold : ℚ) : ℚ :=
  p * (if threshold ≤ principal-payment then 1 else 0) +
  (1-p) * (if threshold ≤ principal then 1 else 0)

theorem probability_between_branches (principal payment p threshold : ℚ)
    (low : principal-payment < threshold) (high : threshold ≤ principal) :
    thresholdProbability principal payment p threshold = 1-p := by
  simp [thresholdProbability, not_le.mpr low, high]

def acceptable (legal : Finset ℚ) (lo hi : ℚ) : Finset ℚ :=
  legal.filter (fun s => lo ≤ s ∧ s ≤ hi)

theorem acceptable_membership (legal : Finset ℚ) (lo hi s : ℚ) :
    s ∈ acceptable legal lo hi ↔ s ∈ legal ∧ lo ≤ s ∧ s ≤ hi := by
  simp [acceptable]

/-- lo/hi are derived inside the statement, not provided as unrelated witnesses. -/
theorem same_case_settlement (principal payment p cp cd sp sd chosen : ℚ)
    (legal : Finset ℚ)
    (h : chosen ∈ acceptable legal
       (conditionalExpectation principal payment p - cp + sp)
       (conditionalExpectation principal payment p + cd - sd)) :
    chosen ∈ legal ∧ principal-p*payment-cp+sp ≤ chosen ∧
      chosen ≤ principal-p*payment+cd-sd := by
  simpa only [expectation_conservation] using (acceptable_membership legal _ _ chosen).mp h

/-- A full grammar row: no arbitrary prose constructor is present. -/
structure Observation (K : Type) where
  key : K
  holder : String
  respondent : String
  basis : List String
  asOf : Nat
  assumptions : List String
  recognized : Bool
  amount : ℚ

deriving DecidableEq

inductive Token (K : Type) where
  | subject (key : K)
  | holder (value : String)
  | respondent (value : String)
  | basis (value : List String)
  | asOf (value : Nat)
  | assumptions (value : List String)
  | recognized (value : Bool)
  | amount (value : ℚ)

def encodeRow (r : Observation K) : List (Token K) :=
  [.subject r.key, .holder r.holder, .respondent r.respondent,
   .basis r.basis, .asOf r.asOf, .assumptions r.assumptions,
   .recognized r.recognized, .amount r.amount]

def decodeRow : List (Token K) → Option (Observation K)
  | [.subject key, .holder holder, .respondent respondent,
     .basis basis, .asOf asOf, .assumptions assumptions,
     .recognized recognized, .amount amount] =>
       some ⟨key,holder,respondent,basis,asOf,assumptions,recognized,amount⟩
  | _ => none

theorem protected_roundtrip (r : Observation K) : decodeRow (encodeRow r) = some r := by
  cases r
  rfl

/-- The same decoded object participates in semantics and business requirements. -/
theorem delivered_business_sat
    (sem : Observation K → Prop) (req : Observation K → Prop)
    (adequate : ∀ x, sem x → req x)
    (tokens : List (Token K)) (x : Observation K)
    (parsed : decodeRow tokens = some x) (valid : sem x) :
    ∃ actual, decodeRow tokens = some actual ∧ req actual := by
  exact ⟨x, parsed, adequate x valid⟩

theorem frame_for_unaffected_field
    (old fresh : A) (obs : A → B) (unchanged : obs fresh = obs old)
    (p : B → Prop) : p (obs fresh) ↔ p (obs old) := by
  rw [unchanged]

/-- Model removal, not arbitrary changes to legal semantics. -/
def mayOut (models : Set X) (outputs : X → Set Y) : Set Y :=
  {y | ∃ x ∈ models, y ∈ outputs x}

theorem evidence_refinement_may_shrinks {small large : Set X}
    (h : small ⊆ large) (outputs : X → Set Y) :
    mayOut small outputs ⊆ mayOut large outputs := by
  intro y hy
  obtain ⟨x,hx,hy⟩ := hy
  exact ⟨x,h hx,hy⟩

/-- Avoid empty-world universal "certainty" by requiring a witness explicitly. -/
theorem universal_answer_has_world (models : Set X) (p : X → Prop)
    (nonempty : models.Nonempty) (all : ∀ x ∈ models, p x) :
    ∃ x ∈ models, p x := by
  obtain ⟨x,hx⟩ := nonempty
  exact ⟨x,hx,all x hx⟩

end JurisLean.BusinessRelations
