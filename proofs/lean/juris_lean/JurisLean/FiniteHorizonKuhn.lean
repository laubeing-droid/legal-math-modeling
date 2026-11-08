import JurisLean.FiniteHorizonGame

/-!
Concrete full-support signatures and both Kuhn directions for the bounded
history machine. Each strategy witness works simultaneously at every horizon.
-/

namespace LegalMath.FiniteHorizon
namespace Game

open Math.ParameterizedChain Math.PMFProduct

variable {T : Nat} {ι State : Type} {Obs Action : ι → Type}
variable (G : Game T ι State Obs Action)

/-- One supported edge records exactly the additional personal action requirement. -/
theorem req_step (i : ι) (h t : History T ι State Action)
    (a : G.core.JointActionAt h) (hpos : G.core.step h a t ≠ 0)
    (π : LocalPlan T (Obs i) (Action i)) :
    Req (G.observe i t) π ↔
      Req (G.observe i h) π ∧ π (G.observe i h) = a i := by
  by_cases ht : h.val.length < T
  · obtain ⟨s, _, rfl⟩ := (G.step_active_support h ht a t).mp hpos
    rw [G.observe_advance, Req_append]
    simp only [rawAction, ofAction_toAction]
  · rw [G.step_terminal h ht a] at hpos
    have heq : t = h := by
      by_contra hne
      exact hpos (by simp [PMF.pure_apply, hne])
    subst t
    letI := terminal_action_subsingleton (G.observe i h) (by simpa using ht)
    simp only [Subsingleton.elim (π (G.observe i h)) (a i), and_true]

section Runs

variable [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Action i)]

theorem req_pureStep (i : ι) (π₀ : G.core.PureProfile)
    (ss : List (History T ι State Action)) (t : History T ι State Action)
    (hpos : G.core.pureStep π₀ ss t ≠ 0) (πᵢ : G.core.LocalStrategy i) :
    Req (G.observe i t) πᵢ ↔
      Req (G.core.projectStates i ss) πᵢ ∧
        πᵢ (G.core.projectStates i ss) = π₀ i (G.core.projectStates i ss) := by
  rw [G.pureStep_eq] at hpos
  have heq := congrArg
    (fun r : PersonalRecord T (Obs i) (Action i) => Req r πᵢ ∧ πᵢ r = π₀ i r)
    (G.projectStates_eq i ss)
  exact (G.req_step i (G.core.lastState ss) t
    (fun j => π₀ j (G.observe j (G.core.lastState ss))) hpos πᵢ).trans
      ⟨fun hp => heq.symm ▸ hp, fun hp => heq ▸ hp⟩

/-- A one-player replacement changes one coordinate of the required joint action. -/
theorem update_action_iff (i : ι) (π₀ : G.core.PureProfile)
    (πᵢ : G.core.LocalStrategy i) (ss : List (History T ι State Action)) :
    (∀ j, (Function.update π₀ i πᵢ) j (G.core.projectStates j ss) =
      π₀ j (G.core.projectStates j ss)) ↔
      πᵢ (G.core.projectStates i ss) = π₀ i (G.core.projectStates i ss) := by
  constructor
  · intro h
    simpa using h i
  · intro h j
    by_cases hj : j = i
    · subst j
      simpa using h
    · simp [Function.update_of_ne hj]

/-- Endpoint recall exactly determines support under any one-player replacement,
including terminal endpoints and arbitrarily many absorbing steps. -/
theorem support_iff_req (i : ι) (n : Nat) (π₀ : G.core.PureProfile)
    (ss : List (History T ι State Action))
    (hpos : pureRun G.core.pureStep G.core.init n π₀ ss ≠ 0)
    (πᵢ : G.core.LocalStrategy i) :
    pureRun G.core.pureStep G.core.init n (Function.update π₀ i πᵢ) ss ≠ 0 ↔
      Req (G.core.projectStates i ss) πᵢ := by
  induction n generalizing ss with
  | zero =>
      have heq : ss = [G.core.init] := by
        by_contra hne
        exact hpos (by simp [pureRun, Math.TraceRun.traceRun, PMF.pure_apply, hne])
      subst ss
      constructor
      · intro _
        simpa [projectStates_eq, ObsModelCore.lastState, core, initialHistory,
          observe, initialRecord] using Req_initial (T := T) (G.signal i [] G.initial) πᵢ
      · intro _
        simpa only [pureRun, Math.TraceRun.traceRun] using hpos
  | succ n ih =>
      rcases List.eq_nil_or_concat ss with rfl | ⟨p, t, rfl⟩
      · exact False.elim (hpos (pureRun_succ_nil _ _ _ _))
      · rw [List.concat_eq_append] at hpos ⊢
        have hfactor := pureRun_succ_append G.core.pureStep G.core.init n π₀ p t
        have hp := left_ne_zero_of_mul (hfactor ▸ hpos)
        have ht := right_ne_zero_of_mul (hfactor ▸ hpos)
        rw [ObsModelCore.pureRun_succ_nonzero_iff (O := G.core) G.stepActionDeterminism n hpos,
          G.update_action_iff, ih p hp, G.projectStates_append]
        exact (G.req_pureStep i π₀ p t ht πᵢ).symm

def localSupportSignatureFull (i : ι) : G.core.LocalSupportSignatureFull i where
  Req := Req
  support_iff := G.support_iff_req i

theorem obsLocalFeasibilityFull (i : ι) : G.core.ObsLocalFeasibilityFull i :=
  ObsModelCore.obsLocalFeasibilityFull_of_localSupportSignatureFull
    (O := G.core) i (G.localSupportSignatureFull i)

section FiniteRecords

variable [∀ i, Fintype (Obs i)]

noncomputable instance coreInfoStateFintype (i : ι) : Fintype (G.core.InfoState i) :=
  inferInstanceAs (Fintype (PersonalRecord T (Obs i) (Action i)))

/-- The same independently sampled complete plan realizes every finite run. -/
theorem behavioral_to_mixed (β : G.core.BehavioralProfile) :
    ∀ n, G.core.runDist n β =
      (G.core.behavioralToMixedJoint β).bind (G.core.runDistPure n) := by
  intro n
  exact ObsModelCore.kuhn_behavioral_to_mixed (O := G.core)
    G.noNontrivialInfoStateRepeat β n

/-- The behavioral-to-mixed equality also preserves every endpoint readout. -/
theorem behavioral_to_mixed_readout {Outcome : Type}
    (β : G.core.BehavioralProfile) (readout : History T ι State Action → Outcome)
    (n : Nat) :
    (G.core.runDist n β).map (fun ss => readout (G.core.lastState ss)) =
      ((G.core.behavioralToMixedJoint β).bind (G.core.runDistPure n)).map
        (fun ss => readout (G.core.lastState ss)) :=
  congrArg (fun d => d.map (fun ss => readout (G.core.lastState ss)))
    (G.behavioral_to_mixed β n)

variable [∀ i, Nonempty (Action i)]

/-- A single player-local behavioral profile realizes the independent mixed
prior at every horizon, rather than choosing a new witness for each horizon. -/
theorem mixed_to_behavioral (μ : ∀ i, PMF (G.core.LocalStrategy i)) :
    ∃ β : G.core.BehavioralProfile, ∀ n,
      G.core.runDist n β = (pmfPi μ).bind (G.core.runDistPure n) := by
  classical
  let fallback : G.core.BehavioralProfile :=
    fun i r => PMF.pure (Classical.arbitrary _)
  refine ⟨ObsModelCore.mixedToBehavioralProfileWithFallback (O := G.core) μ fallback, ?_⟩
  intro n
  apply ObsModelCore.mixedToBehavioralProfileWithFallback_runDist (O := G.core)
    G.stepMassInvariant G.stepSupportFactorization
  intro i
  apply ObsModelCore.actionPosteriorLocal_of_obsLocalFeasibility (O := G.core)
    G.stepMassInvariant i
  intro n₁ n₂ π₀ π₀' ss₁ ss₂ hobs h₁ h₂ _
  exact G.obsLocalFeasibilityFull i n₁ n₂ π₀ π₀' ss₁ ss₂ hobs h₁ h₂

/-- Arbitrary endpoint readouts, including terminal outcomes and payoffs,
have the same pushforward law under this one behavioral witness. -/
theorem mixed_to_behavioral_readout {Outcome : Type}
    (μ : ∀ i, PMF (G.core.LocalStrategy i))
    (readout : History T ι State Action → Outcome) :
    ∃ β : G.core.BehavioralProfile, ∀ n,
      (G.core.runDist n β).map (fun ss => readout (G.core.lastState ss)) =
        ((pmfPi μ).bind (G.core.runDistPure n)).map
          (fun ss => readout (G.core.lastState ss)) := by
  obtain ⟨β, hβ⟩ := G.mixed_to_behavioral μ
  exact ⟨β, fun n => congrArg
    (fun d => d.map (fun ss => readout (G.core.lastState ss))) (hβ n)⟩

end FiniteRecords
end Runs
end Game
end LegalMath.FiniteHorizon

