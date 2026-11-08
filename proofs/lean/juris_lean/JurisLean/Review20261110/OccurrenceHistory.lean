import Mathlib

namespace LegalMath20261110.OccurrenceHistory

structure Occurrence (A O : Type*) where
  token : Nat
  action : A
  outcome : O

abbrev History (A O : Type*) := List (Occurrence A O)

variable {A O : Type*}

def maxToken : History A O → Nat
  | [] => 0
  | e :: rest => max e.token (maxToken rest)

def fresh (h : History A O) : Nat := maxToken h + 1

theorem token_le_max (h : History A O) (e : Occurrence A O) (he : e ∈ h) :
    e.token ≤ maxToken h := by
  induction h with
  | nil => simp at he
  | cons x xs ih =>
      rcases List.mem_cons.mp he with rfl | he
      · exact le_max_left _ _
      · exact le_trans (ih he) (le_max_right _ _)

theorem fresh_not_mem (h : History A O) : fresh h ∉ h.map Occurrence.token := by
  intro hm
  obtain ⟨e, he, eq⟩ := List.mem_map.mp hm
  have bound := token_le_max h e he
  dsimp [fresh] at eq
  omega

def append (h : History A O) (a : A) (o : O) : History A O :=
  h ++ [⟨fresh h, a, o⟩]

theorem append_prefix (h : History A O) (a : A) (o : O) : h <+: append h a o :=
  List.prefix_append _ _

/-- Cancellation of finite sequences, independent of a globally injective token generator. -/
theorem append_injective (h h' : History A O) (a a' : A) (o o' : O)
    (same : append h a o = append h' a' o') : h = h' ∧ a = a' ∧ o = o' := by
  have rev := congrArg List.reverse same
  simp only [append, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append] at rev
  have head := (List.cons.inj rev).1
  have tail := (List.cons.inj rev).2
  refine ⟨?_, congrArg Occurrence.action head, congrArg Occurrence.outcome head⟩
  simpa using congrArg List.reverse tail

def WellFormed (h : History A O) : Prop := (h.map Occurrence.token).Nodup

theorem append_wellFormed (h : History A O) (a : A) (o : O) (valid : WellFormed h) :
    WellFormed (append h a o) := by
  have fresh := fresh_not_mem h
  have hv : (h.map Occurrence.token).Nodup := valid
  simpa [WellFormed, append, List.map_append, List.nodup_append, hv] using fresh

def recordCount {R K : Type*} [DecidableEq R] [DecidableEq K]
    (token : R → K) (records : Finset R) : Nat := (records.image token).card

theorem record_count_once {R K : Type*} [DecidableEq R] [DecidableEq K]
    (token : R → K) (records : Finset R) (r : R) (seen : token r ∈ records.image token) :
    recordCount token (insert r records) = recordCount token records := by
  simp [recordCount, Finset.image_insert, seen]

theorem empty_records_count {R K : Type*} [DecidableEq R] [DecidableEq K] (token : R → K) :
    recordCount token ∅ = 0 := by simp [recordCount]

#print axioms append_injective
#print axioms append_prefix
#print axioms fresh_not_mem
#print axioms append_wellFormed
#print axioms record_count_once

end LegalMath20261110.OccurrenceHistory
