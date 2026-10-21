import JurisLean.Candidates.Final20261021.Interfaces
import JurisLean.HornFixedPoint

namespace JurisLean.Candidates.Final20261021.Compiler

structure Rule (Atom : Type) where
  premises : List Atom
  conclusion : Atom
  deriving DecidableEq, Repr

inductive Derives {Atom : Type} (facts : Atom → Prop) (rules : Rule Atom → Prop) :
    Atom → Prop where
  | fact (a : Atom) : facts a → Derives facts rules a
  | fire (r : Rule Atom) : rules r →
      (∀ a ∈ r.premises, Derives facts rules a) → Derives facts rules r.conclusion

def Models {Atom : Type} (facts : Atom → Prop) (rules : Rule Atom → Prop)
    (truth : Atom → Prop) : Prop :=
  (∀ a, facts a → truth a) ∧
  (∀ r, rules r → (∀ a ∈ r.premises, truth a) → truth r.conclusion)

theorem u03_1_relative_soundness {Atom : Type} {facts : Atom → Prop}
    {rules : Rule Atom → Prop} {truth : Atom → Prop}
    (model : Models facts rules truth) {a : Atom} (h : Derives facts rules a) : truth a := by
  induction h with
  | fact a ha => exact model.1 a ha
  | fire r hr hp ih => exact model.2 r hr ih

theorem derivable_model {Atom : Type} (facts : Atom → Prop) (rules : Rule Atom → Prop) :
    Models facts rules (Derives facts rules) := by
  exact ⟨fun a h => .fact a h, fun r hr hp => .fire r hr hp⟩

theorem u03_2_relative_completeness {Atom : Type} (facts : Atom → Prop)
    (rules : Rule Atom → Prop) (a : Atom) :
    Derives facts rules a ↔ ∀ truth, Models facts rules truth → truth a := by
  constructor
  · intro h truth model
    exact u03_1_relative_soundness model h
  · intro h
    exact h (Derives facts rules) (derivable_model facts rules)

def advance (rules : List (Rule Nat)) (known : List Nat) : List Nat :=
  known ++ rules.flatMap (fun r =>
    if r.premises.all (fun a => decide (a ∈ known)) then [r.conclusion] else [])

def proposed_rule_input (rules : List (Rule Nat)) : Nat → List Nat → List Nat
  | 0, known => known
  | n + 1, known => proposed_rule_input rules n (advance rules known)

theorem advance_sound (rules : List (Rule Nat)) (facts known : List Nat)
    (sound : ∀ a ∈ known, Derives (· ∈ facts) (· ∈ rules) a) :
    ∀ a ∈ advance rules known, Derives (· ∈ facts) (· ∈ rules) a := by
  intro a ha
  rcases List.mem_append.mp ha with old | added
  · exact sound a old
  · obtain ⟨r, hr, ha⟩ := List.mem_flatMap.mp added
    split at ha
    next fired =>
      simp only [List.mem_singleton] at ha
      subst a
      apply Derives.fire r hr
      intro x hx
      have enabled : ∀ b ∈ r.premises, b ∈ known := by
        simpa only [List.all_eq_true, decide_eq_true_eq] using fired
      exact sound x (enabled x hx)
    next stopped => simp at ha

theorem u03_1_computed_sound (rules : List (Rule Nat)) (facts : List Nat) (fuel : Nat) :
    ∀ a ∈ proposed_rule_input rules fuel facts, Derives (· ∈ facts) (· ∈ rules) a := by
  have run : ∀ n known, (∀ a ∈ known, Derives (· ∈ facts) (· ∈ rules) a) →
      ∀ a ∈ proposed_rule_input rules n known, Derives (· ∈ facts) (· ∈ rules) a := by
    intro n
    induction n with
    | zero => intro known h; exact h
    | succ n ih => intro known h; exact ih _ (advance_sound rules facts known h)
  exact run fuel facts (fun a h => .fact a h)

theorem advance_contains (rules : List (Rule Nat)) (known : List Nat) :
    ∀ a ∈ known, a ∈ advance rules known := by
  intro a ha
  exact List.mem_append.mpr (Or.inl ha)

theorem computed_contains_facts (rules : List (Rule Nat)) (fuel : Nat) (facts : List Nat) :
    ∀ a ∈ facts, a ∈ proposed_rule_input rules fuel facts := by
  induction fuel generalizing facts with
  | zero => exact fun _ h => h
  | succ n ih =>
      intro a ha
      exact ih (advance rules facts) a (advance_contains rules facts a ha)

-- The runtime checks closure under every enabled rule. Fuel exhaustion alone
-- never asserts saturation, and duplicate list entries do not prevent closure.
def closed (rules : List (Rule Nat)) (known : List Nat) : Bool :=
  rules.all fun r =>
    if r.premises.all (fun a => decide (a ∈ known)) then decide (r.conclusion ∈ known)
    else true

theorem closed_reflects (rules : List (Rule Nat)) (known : List Nat) :
    closed rules known = true ↔
      ∀ r ∈ rules, (∀ a ∈ r.premises, a ∈ known) → r.conclusion ∈ known := by
  unfold closed
  rw [List.all_eq_true]
  constructor
  · intro h r hr premises
    have enabled : r.premises.all (fun a => decide (a ∈ known)) = true := by
      simpa only [List.all_eq_true, decide_eq_true_eq] using premises
    simpa only [enabled, if_true, decide_eq_true_eq] using h r hr
  · intro h r hr
    by_cases enabled : r.premises.all (fun a => decide (a ∈ known)) = true
    · have premises : ∀ a ∈ r.premises, a ∈ known := by
        simpa only [List.all_eq_true, decide_eq_true_eq] using enabled
      simp [enabled, h r hr premises]
    · simp [enabled]

def proposed_checked_rule_input (rules : List (Rule Nat)) (fuel : Nat)
    (facts : List Nat) : Result (List Nat) :=
  let known := proposed_rule_input rules fuel facts
  if closed rules known then .known known else .unknown .checkIncomplete

theorem u03_2_checked_closure_complete (rules : List (Rule Nat))
    (facts : List Nat) (fuel : Nat) (known : List Nat)
    (checked : proposed_checked_rule_input rules fuel facts = .known known) (a : Nat) :
    a ∈ known ↔ Derives (· ∈ facts) (· ∈ rules) a := by
  unfold proposed_checked_rule_input at checked
  dsimp only at checked
  split at checked
  next stable =>
    cases checked
    constructor
    · exact u03_1_computed_sound rules facts fuel a
    · intro derived
      apply u03_1_relative_soundness (truth := (· ∈ proposed_rule_input rules fuel facts)) _ derived
      exact ⟨computed_contains_facts rules fuel facts,
        (closed_reflects rules _).mp stable⟩
  next incomplete => cases checked

-- The baseline finite fixed-point kernel is reused at its exact type.
-- No claim that its fixed-point completeness alone is semantic completeness.
theorem u03_finite_kernel_termination (sys : HornSystem Nat) :
    ∃ k, k ≤ sys.univ.card ∧
      FiniteMonotoneSystem.iter sys.toFiniteMonotoneSystem k =
      FiniteMonotoneSystem.iter sys.toFiniteMonotoneSystem (k + 1) :=
  HornSystem.horn_finite_termination sys

structure SupportedAtom where
  atom : Nat
  source : SourceRef
  interpretationVersion : Nat
  deriving DecidableEq, Repr

-- Input support is supplied by an independent interpretation relation.
def proposed_fact_checker (support : SourceRef → Nat → Prop)
    [∀ source atom, Decidable (support source atom)] (a : SupportedAtom) : Result Nat :=
  if support a.source a.atom then .known a.atom else .unknown .missingEvidence

end JurisLean.Candidates.Final20261021.Compiler
