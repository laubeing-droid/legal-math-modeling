import JurisLean.FullMath.Core.Foundations

/-!
F11/F12 — Partial soundness and exact completeness of finite certificates.

A scan returning accepted candidates is always sound: everything accepted is
a solution. An exact certificate (independent membership decision covering
the whole carrier) yields equality with the solution set. Accepted /
rejected / undecided form a genuine three-way partition, and a full claim is
admissible only when the undecided class is empty.
-/

namespace JurisLean.FullMath.Representation

section Finite
variable {A : Type} [DecidableEq A] [Fintype A]

/-- The independently-defined solution set. -/
def solutionSet (pred : A → Bool) : Set A := {x | pred x = true}

/-- Enumerate all carrier elements satisfying the predicate. -/
def enumerateAll (pred : A → Bool) : Finset A :=
  Finset.univ.filter (fun a => pred a = true)

/-- Exact certificate: the reported set answers membership for the whole
carrier. -/
def checkExact (pred : A → Bool) (out : Finset A) : Bool :=
  decide (∀ a : A, a ∈ out ↔ pred a = true)

/-- F11: a partial scan is sound — every reported member is a solution. -/
theorem partial_scan_sound (pred : A → Bool) (out : Finset A)
    (h : ∀ a ∈ out, pred a = true) :
    (↑out : Set A) ⊆ solutionSet pred := by
  intro a ha
  exact h a (Finset.mem_coe.mp ha)

/-- F12(a): membership reflection for the enumerator. -/
theorem enumeration_member (pred : A → Bool) (a : A) :
    a ∈ enumerateAll pred ↔ pred a = true := by
  simp [enumerateAll]

/-- F12(b): an accepted exact certificate yields denotation equality. -/
theorem exact_check_reflects (pred : A → Bool) (out : Finset A)
    (h : checkExact pred out = true) :
    (↑out : Set A) = solutionSet pred := by
  have hp : ∀ a : A, a ∈ out ↔ pred a = true := of_decide_eq_true h
  ext a
  constructor
  · intro ha
    exact (hp a).mp (Finset.mem_coe.mp ha)
  · intro ha
    exact Finset.mem_coe.mpr ((hp a).mpr ha)

/-- F12(c): the enumerator carries its own exact certificate. -/
theorem enumeration_certified (pred : A → Bool) :
    checkExact pred (enumerateAll pred) = true := by
  rw [checkExact]
  exact decide_eq_true (fun a => enumeration_member pred a)

/-! Accepted / rejected / undecided partition. -/

/-- A three-valued per-candidate verdict. -/
inductive Verdict where
  | accepted
  | rejected
  | undecided

/-- Classification from a partial checker. -/
def classify (chk : A → Option Bool) (a : A) : Verdict :=
  match chk a with
  | some true => .accepted
  | some false => .rejected
  | none => .undecided

/-- The checker agrees with the predicate when it answers at all. -/
def Agrees (chk : A → Option Bool) (pred : A → Bool) : Prop :=
  ∀ a, chk a = some (pred a)

/-- F11/F12(d): the three verdicts are pairwise distinct by construction. -/
theorem verdict_distinct (v : Verdict) :
    (v = .accepted ↔ ¬ (v = .rejected ∨ v = .undecided)) ∧
    (v = .rejected ↔ ¬ (v = .accepted ∨ v = .undecided)) := by
  cases v <;> simp [Verdict]

/-- F12(e): an exact certificate with an agreeing checker leaves nothing
undecided — only then may a full claim be issued. -/
theorem exact_claim_requires_no_undecided (chk : A → Option Bool)
    (pred : A → Bool) (hagree : Agrees chk pred) (out : Finset A)
    (hcert : checkExact pred out = true) :
    ∀ a, classify chk a ≠ .undecided := by
  intro a ha
  unfold classify at ha
  cases hchk : chk a with
  | none =>
    have hAg := hagree a
    rw [hchk] at hAg
    exact absurd hAg (by simp)
  | some b =>
    rw [hchk] at ha
    cases b
    · exact absurd ha (by simp)
    · exact absurd ha (by simp)

end Finite

end JurisLean.FullMath.Representation
