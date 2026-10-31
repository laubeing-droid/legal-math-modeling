import JurisLean.Candidates.CompilerClosure20261026
import JurisLean.Candidates.Final20261021.Decision
import JurisLean.Candidates.EvidenceWorlds20261027

namespace JurisLean.Candidates.CompilerOriginalBoundaries20261031

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.Final20261021.Compiler
open JurisLean.Candidates.EvidenceWorlds20261027

/-!
Original 03.2/03.5/03.6 finite boundary instances only.
The compatible interpretation family and literal semantics below are the
declared finite models, not a claim about arbitrary natural-language parsing.
The finite fingerprint is exact on two represented contents; it is not a
claim of collision resistance for a cryptographic algorithm.
-/

private def interpretationScore (facts : List Nat) : ℚ :=
  if facts = [1] then 2 else 1

private def highestScoreFamily : List (List Nat) :=
  match Decision.best interpretationScore [[1], [2]] with
  | some facts => [facts]
  | none => []

/-- Original 03.2: the existing actual maximum selector drops a compatible
interpretation. Query 1 then appears robust only in the incorrectly reduced
family; the full-family exact evaluator does not return it. -/
theorem highest_score_selection_can_create_nonrobust_fact :
    interpretationScore [2] < interpretationScore [1] ∧
      Decision.best interpretationScore [[1], [2]] = some [1] ∧
      highestScoreFamily = [[1]] ∧
      proposed_robust_queries [] [[1], [2]] [1] = .known [] ∧
      proposed_robust_queries [] highestScoreFamily [1] = .known [1] := by
  decide

private def literalWords (positive : Bool) : List String :=
  if positive then ["paid"] else ["not", "paid"]

private def finiteFingerprint (words : List String) : Option Nat :=
  if words = ["paid"] then some 1
  else if words = ["not", "paid"] then some 0
  else none

private def literalHolds (actualPaid claimedPaid : Bool) : Prop :=
  actualPaid = claimedPaid

/-- Original 03.5: even an exact finite fingerprint only identifies content.
Two distinct references contain the same positive statement in a world where
that statement is false. Source truth does not follow from unchanged content. -/
theorem identical_fingerprints_do_not_supply_source_truth :
    (∀ a b : Bool,
      finiteFingerprint (literalWords a) = finiteFingerprint (literalWords b) ↔
        literalWords a = literalWords b) ∧
      (∀ a : Bool, finiteFingerprint (literalWords a) ≠ none) ∧
      (let first : Nat × Bool := (0, true)
       let second : Nat × Bool := (1, true)
       first.1 ≠ second.1 ∧
         literalWords first.2 = literalWords second.2 ∧
         finiteFingerprint (literalWords first.2) =
           finiteFingerprint (literalWords second.2) ∧
         ¬ literalHolds false first.2 ∧ ¬ literalHolds false second.2) := by
  decide

private def literalInterpretations (words : List String) : Result (List Bool) :=
  if words = ["paid"] then .known [true]
  else if words = ["not", "paid"] then .known [false]
  else if words = ["paid", "?"] then .known [true, false]
  else .rejected .unsupported

private def literalQuery (words : List String) : Result Judgment :=
  match literalInterpretations words with
  | .known worlds => .known (worldJudgment worlds (fun w (_ : Nat) => w) 0)
  | .unknown e => .unknown e
  | .rejected e => .rejected e
  | .conflict a b => .conflict a b

/-- Original 03.6: one inserted negation changes the literal interpretation,
so this pair is not a meaning-preserving transformation. The same finite
interpretation table includes two alternatives, an accepted query and refusal. -/
theorem negation_changes_meaning_and_finite_interface_keeps_ambiguity :
    literalWords false = "not" :: literalWords true ∧
      literalInterpretations (literalWords true) = .known [true] ∧
      literalInterpretations (literalWords false) = .known [false] ∧
      literalQuery (literalWords true) = .known .supported ∧
      literalQuery (literalWords false) = .known .opposed ∧
      literalInterpretations ["paid", "?"] = .known [true, false] ∧
      literalQuery ["paid", "?"] = .known .insufficient ∧
      literalQuery ["unknown"] = .rejected .unsupported := by
  decide

end JurisLean.Candidates.CompilerOriginalBoundaries20261031
