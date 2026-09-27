import Mathlib

/-!
# Mandate upgrade — disclosure and hallucination gates that read their input

Two of the audit's degenerate definitions (P2-14) sat in the delivery layer:
`Part6.lean:167` defined `compliant (r) := r.disclosed`, so the theorems built on
it read a flag back and never looked at what was disclosed; `Part6.lean:189`
defined the fabricated-identifier blocker as `| [] => false | _ :: _ => true`,
which never inspects the registry it is handed. Both are formally true and
informationally empty.

Replaced here by predicates that consume their arguments: occurrence over a
registry, coverage of a recorded-data list checked item by item, and compliance
requiring both the flag *and* coverage. Membership is defined locally rather than
mixing `List.mem` with `decide (· ∈ ·)`, which is the two-representation trap that
cost this repository CI rounds before.

Status: imported by the release root and named by `AxiomAudit.lean`; built green
in CI run 36297146468 (subject 304194cc5). Commits after that subject do not
inherit the verdict.
-/

namespace JurisLean.Mandate.Disclosure

/-- Occurrence over codes: one notion of membership, used everywhere below. -/
def occurs : Nat → List Nat → Bool
  | _, [] => false
  | d, y :: ys => decide (y = d) || occurs d ys

/-- Conjunction over a Bool list, so coverage needs no library `all` lemma. -/
def allp : List Bool → Bool
  | [] => true
  | b :: bs => b && allp bs

/-- Every recorded datum must occur in the disclosed set. -/
def covers (disclosed recorded : List Nat) : Bool :=
  allp (recorded.map (fun d => occurs d disclosed))

/-- A disclosure is compliant only if flagged *and* covering the record. -/
def compliant (flag : Bool) (disclosed recorded : List Nat) : Bool :=
  flag && covers disclosed recorded

/-- Occurrence distributes over append: registry growth is conservative. -/
theorem occurs_append (d : Nat) : ∀ xs ys : List Nat,
    occurs d (xs ++ ys) = (occurs d xs || occurs d ys) := by
  intro xs
  induction xs with
  | nil => intro ys; simp [occurs]
  | cons a as ih =>
      intro ys
      by_cases h : a = d
      · simp [occurs, h, ih ys]
      · simp [occurs, h, ih ys]

/-- A registry mentions its own head. -/
theorem occurs_head (d : Nat) (l : List Nat) : occurs d (d :: l) = true := by
  simp [occurs]

/-- Growing a registry cannot lose a recorded datum. -/
theorem occurs_monotone (d : Nat) (xs ys : List Nat) (h : occurs d xs = true) :
    occurs d (xs ++ ys) = true := by
  rw [occurs_append]
  rw [h]
  simp

theorem covers_nil_recorded (disclosed : List Nat) : covers disclosed [] = true := rfl

/-- An empty registry covers a non-empty record: the gate says no. -/
theorem not_covers_empty_registry (d : Nat) : covers [] [d] = false := by
  simp [covers, occurs, allp]

/-- Compliance reduces to coverage once the flag is set, so the flag alone is
never sufficient — the property the released `compliant` projection lacked. -/
theorem compliant_true_iff_covers (disclosed recorded : List Nat) :
    compliant true disclosed recorded = true ↔ covers disclosed recorded = true := by
  simp [compliant]

/-- A covering registry with the flag set is compliant; a short one is not. -/
theorem compliant_concrete :
    compliant true [1, 2] [1, 2] = true ∧ compliant true [1] [1, 2] = false :=
  ⟨by decide, by decide⟩

end JurisLean.Mandate.Disclosure
