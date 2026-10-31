import JurisLean.Candidates.ExchangeableRank20261031

noncomputable section

open MeasureTheory ProbabilityTheory

namespace JurisLean.Candidates.GroupedConformalInstance20261031

open JurisLean.Candidates.ExchangeableRank20261031

/-!
Original 05.4: a sufficient group-conditional split-conformal version.
The training output and score are fixed. For this fixed group, n is its own
calibration count, and the conditional law is the actual test-group conditional
measure. Group membership alone does not establish the permutation-law premise.
-/

/-- Apply the existing split-conformal theorem under the actual positive-mass
test-group conditional law, using this group's own calibration threshold. -/
theorem group_conditional_split_conformal_coverage
    {Ω E G : Type*} [MeasurableSpace Ω] [MeasurableSpace E] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin (n + 1) → E) (hX : Measurable X)
    (group : E → G) (g : G)
    (hgroup : MeasurableSet {ω | group (X ω (Fin.last n)) = g})
    (hpos : 0 < μ {ω | group (X ω (Fin.last n)) = g})
    (hcal : ∀ᵐ ω ∂(ProbabilityTheory.cond μ
        {ω | group (X ω (Fin.last n)) = g}),
      ∀ i : Fin n, group (X ω i.castSucc) = g)
    (score : E → ℝ) (hscore : Measurable score)
    (hex : ∀ σ : Equiv.Perm (Fin (n + 1)),
      IdentDistrib (fun ω i => X ω (σ i)) X
        (ProbabilityTheory.cond μ {ω | group (X ω (Fin.last n)) = g})
        (ProbabilityTheory.cond μ {ω | group (X ω (Fin.last n)) = g}))
    (hn : 1 ≤ n) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    ENNReal.ofReal (1 - α) ≤
      ProbabilityTheory.cond μ {ω | group (X ω (Fin.last n)) = g}
        {ω | (score (X ω (Fin.last n)) : WithTop ℝ) ≤
          conformalThreshold
            (fun i : Fin n => score (X ω i.castSucc)) α hα1} := by
  letI : IsProbabilityMeasure
      (ProbabilityTheory.cond μ {ω | group (X ω (Fin.last n)) = g}) :=
    ProbabilityTheory.cond_isProbabilityMeasure (ne_of_gt hpos)
  exact scored_sample_split_conformal_coverage
    (ProbabilityTheory.cond μ {ω | group (X ω (Fin.last n)) = g})
    X hX score hscore hex hn α hα0 hα1

end JurisLean.Candidates.GroupedConformalInstance20261031