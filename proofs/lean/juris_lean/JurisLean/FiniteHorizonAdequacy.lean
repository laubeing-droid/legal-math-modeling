import JurisLean.FiniteHorizonKuhn

/-!
The original game's direct finite-horizon recursion and its transport to the
Kuhn core. The direct law samples actions from personal records and executes
the supplied game transition; its definition does not use the core runner.
Its state is the complete bounded game history, so arbitrary history and
terminal-payoff readouts are preserved, including absorbing extensions.
-/

namespace LegalMath.FiniteHorizon

open Math.PMFProduct

abbrev BehavioralPlan (T : Nat) (ι : Type) (Obs Action : ι → Type) :=
  (i : ι) → (r : PersonalRecord T (Obs i) (Action i)) → PMF (ActionAt r)

namespace Game

variable {T : Nat} {ι State : Type} {Obs Action : ι → Type}
variable (G : Game T ι State Obs Action)

/-- Both strategy interfaces have exactly the same personal-record domain. -/
def localPlanEquiv (i : ι) :
    LocalPlan T (Obs i) (Action i) ≃ G.core.LocalStrategy i := Equiv.refl _

def behavioralPlanEquiv :
    BehavioralPlan T ι Obs Action ≃ G.core.BehavioralProfile := Equiv.refl _

variable [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Action i)]

/-- The original independent-action equation, evaluated at a complete history. -/
noncomputable def nativeStep (β : BehavioralPlan T ι Obs Action)
    (h : History T ι State Action) : PMF (History T ι State Action) :=
  (pmfPi (fun i => β i (G.observe i h))).bind (G.step h)

/-- Direct iteration of the given game, without a core state-trace runner. -/
noncomputable def nativeLaw (β : BehavioralPlan T ι Obs Action) :
    Nat → PMF (History T ι State Action)
  | 0 => PMF.pure G.initialHistory
  | n + 1 => (G.nativeLaw β n).bind (G.nativeStep β)

noncomputable def nativeLawPure
    (π : (i : ι) → LocalPlan T (Obs i) (Action i)) (n : Nat) :
    PMF (History T ι State Action) :=
  G.nativeLaw (fun i r => PMF.pure (π i r)) n

/-- Identity information states erase the core's bookkeeping transports. -/
theorem stepDist_nativeStep (β : BehavioralPlan T ι Obs Action)
    (ss : List (History T ι State Action)) :
    G.core.stepDist β ss = G.nativeStep β (G.core.lastState ss) := by
  have transport
      (v w : (i : ι) → PersonalRecord T (Obs i) (Action i)) (e : v = w)
      (k : ((i : ι) → ActionAt (w i)) → PMF (History T ι State Action)) :
      (pmfPi (fun i => β i (v i))).bind
          (fun a => k (fun i => (congrFun e i) ▸ a i)) =
        (pmfPi (fun i => β i (w i))).bind k := by
    cases e
    rfl
  exact transport (fun i => G.core.projectStates i ss)
    (fun i => G.observe i (G.core.lastState ss))
    (funext (fun i => G.projectStates_eq i ss)) (G.step (G.core.lastState ss))

/-- The absorbing extension retains the entire history in the direct semantics. -/
theorem nativeStep_terminal (β : BehavioralPlan T ι Obs Action)
    (h : History T ι State Action) (ht : ¬h.val.length < T) :
    G.nativeStep β h = PMF.pure h := by
  unfold nativeStep
  simp only [step, dif_neg ht]
  exact PMF.bind_const _ _

/-- The endpoint of the core trace has exactly the directly iterated history law.
The endpoint itself contains every original action and environment result. -/
theorem runDist_nativeLaw (β : BehavioralPlan T ι Obs Action) (n : Nat) :
    (G.core.runDist n β).map G.core.lastState = G.nativeLaw β n := by
  induction n with
  | zero =>
      simp [ObsModelCore.runDist, Math.TraceRun.traceRun, nativeLaw,
        ObsModelCore.lastState, core]
  | succ n ih =>
      change ((G.core.runDist n β).bind (fun ss =>
        (G.core.stepDist β ss).map (fun t => ss ++ [t]))).map G.core.lastState =
        (G.nativeLaw β n).bind (G.nativeStep β)
      rw [PMF.map_bind, ← ih, PMF.bind_map]
      congr 1
      funext ss
      simp only [PMF.map_comp, Function.comp_def,
        ObsModelCore.lastState_append_singleton, PMF.map_id]
      exact G.stepDist_nativeStep β ss

theorem runDistPure_nativeLaw
    (π : (i : ι) → LocalPlan T (Obs i) (Action i)) (n : Nat) :
    (G.core.runDistPure n π).map G.core.lastState = G.nativeLawPure π n :=
  G.runDist_nativeLaw (fun i r => PMF.pure (π i r)) n

/-- Any original history readout is preserved by the independent semantics bridge. -/
theorem native_readout_adequacy {Outcome : Type}
    (β : BehavioralPlan T ι Obs Action)
    (readout : History T ι State Action → Outcome) (n : Nat) :
    (G.core.runDist n β).map (fun ss => readout (G.core.lastState ss)) =
      (G.nativeLaw β n).map readout := by
  rw [← G.runDist_nativeLaw β n, PMF.map_comp]
  rfl

variable [∀ i, Fintype (Obs i)]

/-- Behavioral-to-mixed equivalence in the original direct game equations. -/
theorem native_behavioral_to_mixed (β : BehavioralPlan T ι Obs Action) :
    ∀ n, G.nativeLaw β n =
      (G.core.behavioralToMixedJoint β).bind (fun π => G.nativeLawPure π n) := by
  intro n
  rw [← G.runDist_nativeLaw β n, G.behavioral_to_mixed β n, PMF.map_bind]
  congr 1
  funext π
  exact G.runDistPure_nativeLaw π n

theorem native_behavioral_to_mixed_readout {Outcome : Type}
    (β : BehavioralPlan T ι Obs Action)
    (readout : History T ι State Action → Outcome) (n : Nat) :
    (G.nativeLaw β n).map readout =
      ((G.core.behavioralToMixedJoint β).bind
        (fun π => G.nativeLawPure π n)).map readout :=
  congrArg (fun d => d.map readout) (G.native_behavioral_to_mixed β n)

variable [∀ i, Nonempty (Action i)]

/-- One direct-game behavioral strategy realizes the independent mixed prior
at every horizon, with no reconstruction of the witness after choosing n. -/
theorem native_mixed_to_behavioral
    (μ : (i : ι) → PMF (LocalPlan T (Obs i) (Action i))) :
    ∃ β : BehavioralPlan T ι Obs Action, ∀ n,
      G.nativeLaw β n = (pmfPi μ).bind (fun π => G.nativeLawPure π n) := by
  obtain ⟨β, hβ⟩ := G.mixed_to_behavioral μ
  refine ⟨β, fun n => ?_⟩
  rw [← G.runDist_nativeLaw β n, hβ n, PMF.map_bind]
  congr 1
  funext π
  exact G.runDistPure_nativeLaw π n

theorem native_mixed_to_behavioral_readout {Outcome : Type}
    (μ : (i : ι) → PMF (LocalPlan T (Obs i) (Action i)))
    (readout : History T ι State Action → Outcome) :
    ∃ β : BehavioralPlan T ι Obs Action, ∀ n,
      (G.nativeLaw β n).map readout =
        ((pmfPi μ).bind (fun π => G.nativeLawPure π n)).map readout := by
  obtain ⟨β, hβ⟩ := G.native_mixed_to_behavioral μ
  exact ⟨β, fun n => congrArg (fun d => d.map readout) (hβ n)⟩

end Game

namespace Examples

/-- Two players receive independently sampled private bits before the last move. -/
noncomputable def privateBits : Game 2 (Fin 2) (Fin 2 → Bool)
    (fun _ => Bool) (fun _ => Bool) where
  initial := fun _ => false
  signal := fun i _ s => s i
  transition := fun h a =>
    if h.val.isEmpty then
      pmfPi (fun _ : Fin 2 => PMF.bernoulli (1 / 2) (by norm_num))
    else PMF.pure a

def quietAction : JointAction (Fin 2) (fun _ => Bool) := fun _ => false

def bits (b : Bool) : Fin 2 → Bool := fun i => if i = 0 then false else b

def afterPrivateBit (b : Bool) : History 2 (Fin 2) (Fin 2 → Bool) (fun _ => Bool) :=
  ⟨[(quietAction, bits b)], by decide⟩

def terminalPrivateBit (b : Bool) : History 2 (Fin 2) (Fin 2 → Bool) (fun _ => Bool) :=
  ⟨[(quietAction, bits b), (quietAction, quietAction)], by decide⟩

/-- The first player cannot see the other player's bit. -/
theorem private_information_hidden :
    privateBits.observe 0 (afterPrivateBit false) =
      privateBits.observe 0 (afterPrivateBit true) := rfl

/-- The bit is not lost from the other player's full terminal record. -/
theorem terminal_private_record_retained :
    privateBits.observe 1 (terminalPrivateBit false) ≠
      privateBits.observe 1 (terminalPrivateBit true) := by
  intro heq
  have hlog := congrArg (fun r => r.2.val) heq
  simp [Game.observe, Game.localLog, privateBits, terminalPrivateBit, bits] at hlog

/-- Both private-bit alternatives are genuine positive-probability environment outcomes. -/
theorem private_bits_supported (s : Fin 2 → Bool) :
    privateBits.transition privateBits.initialHistory quietAction s ≠ 0 := by
  change (pmfPi (fun _ : Fin 2 => PMF.bernoulli (1 / 2) (by norm_num))) s ≠ 0
  rw [pmfPi_apply]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  cases s i <;> norm_num [PMF.bernoulli_apply]

/-- The nontrivial two-player example consumes the same all-horizons theorem. -/
theorem private_bits_kuhn
    (μ : (i : Fin 2) → PMF (LocalPlan 2 Bool Bool)) :
    ∃ β : BehavioralPlan 2 (Fin 2) (fun _ => Bool) (fun _ => Bool), ∀ n,
      privateBits.nativeLaw β n =
        (pmfPi μ).bind (fun π => privateBits.nativeLawPure π n) :=
  privateBits.native_mixed_to_behavioral μ

end Examples
end LegalMath.FiniteHorizon

#print axioms LegalMath.FiniteHorizon.Game.stepActionDeterminism
#print axioms LegalMath.FiniteHorizon.Game.noNontrivialInfoStateRepeat
#print axioms LegalMath.FiniteHorizon.Game.support_iff_req
#print axioms LegalMath.FiniteHorizon.Game.localSupportSignatureFull
#print axioms LegalMath.FiniteHorizon.Game.behavioral_to_mixed
#print axioms LegalMath.FiniteHorizon.Game.mixed_to_behavioral
#print axioms LegalMath.FiniteHorizon.Game.runDist_nativeLaw
#print axioms LegalMath.FiniteHorizon.Game.native_behavioral_to_mixed
#print axioms LegalMath.FiniteHorizon.Game.native_mixed_to_behavioral
#print axioms LegalMath.FiniteHorizon.Examples.private_information_hidden
#print axioms LegalMath.FiniteHorizon.Examples.terminal_private_record_retained
#print axioms LegalMath.FiniteHorizon.Examples.private_bits_supported
#print axioms LegalMath.FiniteHorizon.Examples.private_bits_kuhn
