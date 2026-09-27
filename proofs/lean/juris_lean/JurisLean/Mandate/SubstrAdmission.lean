import Mathlib

/-!
# Mandate upgrade — verbatim citation admission, on both sides of the bridge

The audit found a bilateral mismatch under P-127: the shipped Python contract
tests *containment* (`delivery_contracts.py:127`, `self.cited_text in
self.snapshot_text`), while the Lean side proved facts about *prefixes*
(`General.lean` `P127_isPrefixChars_*`), and the paper registered the downgrade as
“前缀而非任意子串” without ever stating how the two relations stand.

This module puts both relations in one place over a code list: the direction that
holds (prefix ⇒ containment), the direction that provably fails, the length
obstruction that makes a fabricated citation detectable, and reflexivity of
containment — which is the property the Python gate relies on and never states.

Status: NOT in `JurisLean.lean`, NOT in `AxiomAudit.lean`; CI_NOT_RUN.
-/

namespace JurisLean.Mandate.SubstrAdmission

/-- Prefix over codes: the relation the Lean side already used. -/
def isPrefix : List Nat → List Nat → Bool
  | [], _ => true
  | _, [] => false
  | x :: xs, y :: ys => decide (x = y) && isPrefix xs ys

/-- Containment over codes: what the Python contract's `in` actually asserts. -/
def isSubstr : List Nat → List Nat → Bool
  | [], _ => true
  | _, [] => false
  | pat, y :: rest => isPrefix pat (y :: rest) || isSubstr pat rest

/-- A list is a prefix of itself. -/
theorem isPrefix_refl (l : List Nat) : isPrefix l l = true := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [isPrefix, ih]

/-- A pattern longer than its target cannot be a prefix — the detection workhorse. -/
theorem isPrefix_false_of_longer (pat : List Nat) :
    ∀ src : List Nat, pat.length > src.length → isPrefix pat src = false := by
  induction pat with
  | nil =>
      intro src h
      simp at h
  | cons p ps ih =>
      intro src h
      cases src with
      | nil => simp [isPrefix]
      | cons q qs =>
          have hlen : ps.length > qs.length := by
            simpa using h
          have htail := ih qs hlen
          simp [isPrefix, htail]

/-- The empty citation is contained everywhere; nothing is asserted about it. -/
theorem isSubstr_nil_pat (src : List Nat) : isSubstr [] src = true := by
  simp [isSubstr]

/-- Prefix implies containment: the one direction between the two relations. -/
theorem isSubstr_of_isPrefix (pat src : List Nat) (h : isPrefix pat src = true) :
    isSubstr pat src = true := by
  cases pat with
  | nil => rfl
  | cons p ps =>
      cases src with
      | nil => simp [isPrefix] at h
      | cons q qs => simp [isSubstr, h]

/-- Any list contains itself, since containment includes the prefix case. -/
theorem isSubstr_self (src : List Nat) : isSubstr src src = true :=
  isSubstr_of_isPrefix src src (isPrefix_refl src)

/--
Containment does not imply prefix, exhibited. A witness is legitimate here
because the claim is negative: it refutes a universal, it does not assert a law.
-/
theorem substr_strictly_weaker :
    isSubstr [2] [1, 2, 3] = true ∧ isPrefix [2] [1, 2, 3] = false :=
  ⟨by decide, by decide⟩

/--
Consequence for the ledger: the Python gate and the Lean prefix facts are not
the same proposition. Whichever one is intended must be stated on both sides;
this file is where the containment relation first exists in Lean at all.
-/
theorem prefix_adequate_for_admission (pat src : List Nat) (h : isPrefix pat src = true) :
    isSubstr pat src = true :=
  isSubstr_of_isPrefix pat src h

end JurisLean.Mandate.SubstrAdmission
