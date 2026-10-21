import JurisLean.Candidates.Final20261021.RSI

namespace JurisLean.Candidates.Final20261021.Feedback

structure Scope where
  task : Nat
  target : Nat
  feature : Nat
  mechanism : Nat
  ruleVersion : Nat
  principal : PartyId
  protectedDomains : List Nat
  deriving DecidableEq, Repr

structure Assessed where
  scope : Scope
  model : RSI.Checkpoint
  lower : ℚ
  upper : ℚ
  validationSnapshot : Nat
  protocol : Nat
  delta : ℚ
  deriving DecidableEq, Repr

inductive Verdict where
  | accepted | insufficientBound | scopeMismatch
  deriving DecidableEq, Repr

def consider (old candidate : Assessed) (tolerance : ℚ) : Verdict × Assessed :=
  if candidate.scope = old.scope then
    if candidate.upper ≤ old.lower + tolerance then (.accepted, candidate)
    else (.insufficientBound, old)
  else (.scopeMismatch, old)

theorem mismatched_scope_keeps (old candidate : Assessed) (tolerance : ℚ)
    (mismatch : candidate.scope ≠ old.scope) :
    consider old candidate tolerance = (.scopeMismatch, old) := by simp [consider, mismatch]

theorem accepted_evidence (old candidate : Assessed) (tolerance : ℚ)
    (accepted : (consider old candidate tolerance).1 = .accepted) :
    candidate.scope = old.scope ∧ candidate.upper ≤ old.lower+tolerance ∧
    (consider old candidate tolerance).2 = candidate := by
  by_cases hs : candidate.scope = old.scope
  · by_cases hg : candidate.upper ≤ old.lower+tolerance
    · exact ⟨hs, hg, by simp [consider, hs, hg]⟩
    · simp [consider, hs, hg] at accepted
  · simp [consider, hs] at accepted

theorem u14_1_conservative_accept (old candidate : Assessed) (tolerance oldRisk newRisk : ℚ)
    (oldBound : old.lower ≤ oldRisk) (newBound : newRisk ≤ candidate.upper)
    (accepted : (consider old candidate tolerance).1 = .accepted) :
    newRisk ≤ oldRisk + tolerance := by
  have gate := (accepted_evidence old candidate tolerance accepted).2.1
  linarith

inductive Lifecycle where
  | candidate (model : RSI.Checkpoint)
  | evaluated (certificate : Assessed)
  | accepted (certificate : Assessed)
  | loaded (model : RSI.Checkpoint) (readbackReceipt : SourceRef)
  deriving DecidableEq, Repr

-- Exact checkpoint bytes and all semantic metadata must match the readback.
-- The registry is external; the pure candidate cannot grant itself access.
def loadAccepted (g : Gamma) (grants : List Authorization.Grant)
    (old candidate : Assessed) (tolerance : ℚ)
    (readback : RSI.Checkpoint) (receipt : SourceRef) : Result Lifecycle :=
  if (consider old candidate tolerance).1 ≠ .accepted then .rejected .missingEvidence
  else if readback ≠ candidate.model then .rejected .scopeMismatch
  else if Authorization.authorized grants g candidate.scope.principal 2
      candidate.model.version (.party candidate.scope.principal) = false then .unknown .authorityUnresolved
  else .known (.loaded readback receipt)

inductive LabelOrigin where
  | external | suggestion
  deriving DecidableEq, Repr

structure Label where
  unit : MeasurementId
  target : Nat
  outcome : Bool
  source : SourceRef
  origin : LabelOrigin
  deriving DecidableEq, Repr

structure LabelStore where
  history : List Label
  training : List Label
  conflicts : List (Label × Label)
  deriving DecidableEq, Repr

def addLabel (s : LabelStore) (row : Label) : Result LabelStore :=
  if row.origin = .suggestion then .rejected .missingEvidence
  else if s.conflicts.any (fun pair => decide (pair.1.unit = row.unit ∧ pair.1.target = row.target))
    then .known { s with history := s.history ++ [row] }
  else match s.training.find? (fun old => decide (old.unit = row.unit ∧ old.target = row.target)) with
  | none => .known { s with history := s.history ++ [row], training := s.training ++ [row] }
  | some old =>
      if old.outcome = row.outcome then .known { s with history := s.history ++ [row] }
      else .known { s with history := s.history ++ [row],
        training := s.training.filter (fun x => decide (x.unit ≠ row.unit ∨ x.target ≠ row.target)),
        conflicts := s.conflicts ++ [(old, row)] }

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

theorem u14_2_independent_cluster_upper_tail {Ω I : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (clusterSum : I → Ω → ℝ)
    (sizes : I → Nat) (clusters : Finset I) (independent : iIndepFun clusterSum μ)
    (measurable : ∀ i ∈ clusters, AEMeasurable (clusterSum i) μ)
    (bounded : ∀ i ∈ clusters, ∀ᵐ w ∂μ, clusterSum i w ∈ Set.Icc 0 (sizes i : ℝ))
    (deviation : ℝ) (positive : 0 ≤ deviation) :
    μ.real {w | deviation ≤ ∑ i ∈ clusters, (clusterSum i w - ∫ z, clusterSum i z ∂μ)} ≤
      exp (-deviation^2 / (2 * ∑ i ∈ clusters, (((‖(sizes i : ℝ)-0‖₊/2)^2 : ℝ≥0) : ℝ))) :=
  Learning.u01_0_independent_bounded_upper_tail μ clusterSum (fun _ => 0)
    (fun i => (sizes i : ℝ)) clusters independent measurable bounded deviation positive

theorem u14_2_independent_cluster_two_tail {Ω I : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (clusterSum : I → Ω → ℝ)
    (sizes : I → Nat) (clusters : Finset I) (independent : iIndepFun clusterSum μ)
    (measurable : ∀ i ∈ clusters, AEMeasurable (clusterSum i) μ)
    (bounded : ∀ i ∈ clusters, ∀ᵐ w ∂μ, clusterSum i w ∈ Set.Icc 0 (sizes i : ℝ))
    (N : ℝ) (total : N = ∑ i ∈ clusters, (sizes i : ℝ)) (positiveN : 0 < N)
    (ε : ℝ) (positive : 0 < ε) :
    μ.real {w | ε ≤ |(∑ i ∈ clusters, (clusterSum i w - ∫ z, clusterSum i z ∂μ))/N|} ≤
      2 * exp (-2*N^2*ε^2 / (∑ i ∈ clusters, (sizes i : ℝ)^2)) := by
  have positiveSquares : 0 < ∑ i ∈ clusters, (sizes i : ℝ)^2 := by
    have nonneg : 0 ≤ ∑ i ∈ clusters, (sizes i : ℝ)^2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg (sizes i : ℝ))
    by_contra notPositive
    have zero : (∑ i ∈ clusters, (sizes i : ℝ)^2) = 0 := by linarith
    have every := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ clusters) => sq_nonneg (sizes i : ℝ))).mp zero
    have totalZero : N = 0 := by
      rw [total]
      apply Finset.sum_eq_zero
      intro i hi
      have squareZero := every i hi
      nlinarith
    linarith
  have bound := Learning.u01_0_independent_bounded_two_tail μ clusterSum (fun _ => 0)
    (fun i => (sizes i : ℝ)) clusters independent measurable bounded
    (by simpa using positiveSquares) (N*ε) (mul_pos positiveN positive)
  have events : {w | ε ≤ |(∑ i ∈ clusters,
        (clusterSum i w - ∫ z, clusterSum i z ∂μ))/N|} =
      {w | N*ε ≤ |∑ i ∈ clusters, (clusterSum i w - ∫ z, clusterSum i z ∂μ)|} := by
    ext w
    simp only [Set.mem_setOf_eq, abs_div, abs_of_pos positiveN]
    rw [le_div_iff₀ positiveN, mul_comm ε N]
  rw [events]
  simpa only [sub_zero, mul_pow, mul_assoc] using bound

theorem u14_2_unequal_cluster_effective_size :
    ((99+1 : ℚ)^2 / (99^2+1^2)) = 5000/4901 ∧ (5000/4901 : ℚ) ≠ 2 := by norm_num

end JurisLean.Candidates.Final20261021.Feedback
