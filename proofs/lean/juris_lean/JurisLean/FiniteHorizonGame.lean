import JurisLean.FiniteHorizonRecords
import JurisLean.External.GameTheory.Theorems.Kuhn.MixedToBehavioralCore
import JurisLean.External.GameTheory.Theorems.Kuhn.BehavioralToMixedCore

/-!
A finite-horizon, synchronous, perfect-recall stochastic game.
The environment may be infinite. Only personal observations and actions need
be finite. A successor records the actual joint action and next environment
state. The terminal state absorbs without erasing anyone's personal record.
-/

namespace LegalMath.FiniteHorizon

open Math.ParameterizedChain Math.PMFProduct

abbrev JointAction (ι : Type) (Action : ι → Type) := (i : ι) → Action i

abbrev History (T : Nat) (ι State : Type) (Action : ι → Type) :=
  BoundedHistory T (JointAction ι Action × State)

/-- The given transition law can depend on the complete bounded history. -/
structure Game (T : Nat) (ι State : Type) (Obs Action : ι → Type) where
  initial : State
  signal : (i : ι) → State → Obs i
  transition : History T ι State Action → JointAction ι Action → PMF State

namespace Game

variable {T : Nat} {ι State : Type} {Obs Action : ι → Type}
variable (G : Game T ι State Obs Action)

def initialHistory (G : Game T ι State Obs Action) : History T ι State Action := ⟨[], by simp⟩

def observe (i : ι) (h : History T ι State Action) :
    PersonalRecord T (Obs i) (Action i) :=
  (G.signal i G.initial, ⟨h.val.map (fun x => (x.1 i, G.signal i x.2)), by
    simpa using h.property⟩)

@[simp] theorem observe_stage (i : ι) (h : History T ι State Action) :
    stage (G.observe i h) = h.val.length := by simp [observe, stage]

@[simp] theorem observe_initial (i : ι) :
    G.observe i G.initialHistory = initialRecord T (G.signal i G.initial) := rfl

def advance (G : Game T ι State Obs Action) (h : History T ι State Action) (ht : h.val.length < T)
    (a : JointAction ι Action) (s : State) : History T ι State Action :=
  ⟨h.val ++ [(a, s)], by simp only [List.length_append, List.length_singleton]; omega⟩

@[simp] theorem advance_length (h : History T ι State Action) (ht : h.val.length < T)
    (a : JointAction ι Action) (s : State) :
    (G.advance h ht a s).val.length = h.val.length + 1 := by simp [advance]

theorem observe_advance (i : ι) (h : History T ι State Action) (ht : h.val.length < T)
    (a : JointAction ι Action) (s : State) :
    G.observe i (G.advance h ht a s) =
      append (G.observe i h) (by simpa using ht) (a i) (G.signal i s) := by
  apply Prod.ext rfl
  apply Subtype.ext
  simp [observe, advance, append]

def rawAction (h : History T ι State Action) (ht : h.val.length < T)
    (a : (i : ι) → ActionAt (G.observe i h)) : JointAction ι Action :=
  fun i => toAction (G.observe i h) (by simpa using ht) (a i)

theorem rawAction_injective (h : History T ι State Action) (ht : h.val.length < T) :
    Function.Injective (G.rawAction h ht) := by
  intro a b hab
  funext i
  exact toAction_injective (G.observe i h) (by simpa using ht) (congrFun hab i)

noncomputable def step (h : History T ι State Action)
    (a : (i : ι) → ActionAt (G.observe i h)) : PMF (History T ι State Action) :=
  if ht : h.val.length < T then
    (G.transition h (G.rawAction h ht a)).map (G.advance h ht (G.rawAction h ht a))
  else PMF.pure h

noncomputable def core : ObsModelCore ι (History T ι State Action)
    (fun i => PersonalRecord T (Obs i) (Action i)) (fun _ r => ActionAt r) where
  infoState := fun _ => InfoStateCore.identity _
  observe := G.observe
  machine := { init := G.initialHistory, step := G.step }

@[simp] theorem projectStates_eq (i : ι) (ss : List (History T ι State Action)) :
    G.core.projectStates i ss = G.observe i (G.core.lastState ss) :=
  G.core.currentObs_projectStates i ss

@[simp] theorem projectStates_append (i : ι) (ss : List (History T ι State Action))
    (h : History T ι State Action) :
    G.core.projectStates i (ss ++ [h]) = G.observe i h := by
  rw [projectStates_eq, ObsModelCore.lastState_append_singleton]

theorem step_terminal (h : History T ι State Action) (ht : ¬h.val.length < T)
    (a : G.core.JointActionAt h) : G.core.step h a = PMF.pure h := by
  change G.step h a = _
  simp [step, ht]

theorem step_active_support (h : History T ι State Action) (ht : h.val.length < T)
    (a : G.core.JointActionAt h) (t : History T ι State Action) :
    G.core.step h a t ≠ 0 ↔ ∃ s,
      G.transition h (G.rawAction h ht a) s ≠ 0 ∧
        G.advance h ht (G.rawAction h ht a) s = t := by
  change G.step h a t ≠ 0 ↔ _
  simp only [step, dif_pos ht]
  exact PMF.mem_support_map_iff

/-- The recorded joint action is forced by any supported source/target pair. -/
theorem stepActionDeterminism : G.core.StepActionDeterminism := by
  intro h t a b ha hb
  by_cases ht : h.val.length < T
  · obtain ⟨s, _, hs⟩ := (G.step_active_support h ht a t).mp ha
    obtain ⟨s', _, hs'⟩ := (G.step_active_support h ht b t).mp hb
    have heq := congrArg Subtype.val (hs.trans hs'.symm)
    have hp := (Math.TraceRun.append_singleton_inj heq).2
    apply G.rawAction_injective h ht
    exact congrArg Prod.fst hp
  · funext i
    letI := terminal_action_subsingleton (G.observe i h) (by simpa using ht)
    exact Subsingleton.elim _ _

/-- Forget only the recorded action; the next environment law is unchanged. -/
def current (h : History T ι State Action) : State :=
  ((h.val.getLast?).map Prod.snd).getD G.initial

@[simp] theorem current_advance (h : History T ι State Action) (ht : h.val.length < T)
    (a : JointAction ι Action) (s : State) : G.current (G.advance h ht a s) = s := by
  simp [current, advance, List.getLast?_append]

theorem step_environment (h : History T ι State Action) (ht : h.val.length < T)
    (a : G.core.JointActionAt h) :
    (G.core.step h a).map G.current = G.transition h (G.rawAction h ht a) := by
  change (G.step h a).map G.current = _
  simp only [step, dif_pos ht, PMF.map_map]
  simpa only [Function.comp_def, current_advance] using
    (PMF.map_id (G.transition h (G.rawAction h ht a)))

section Runs

variable [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Action i)]

theorem stepMassInvariant : G.core.StepMassInvariant :=
  G.stepActionDeterminism.toMassInvariant

theorem stepSupportFactorization : G.core.StepSupportFactorization :=
  G.stepActionDeterminism.toSupportFactorization

/-- Erase the core's transports by selecting actions at the actual personal record. -/
theorem pureStep_eq (π : G.core.PureProfile) (ss : List (History T ι State Action)) :
    G.core.pureStep π ss = G.step (G.core.lastState ss)
      (fun i => π i (G.observe i (G.core.lastState ss))) := by
  rw [ObsModelCore.pureStep_eq]
  congr 1
  funext i
  simp only [projectStates_eq]
  rfl

/-- Every supported step advances the clock until T and then absorbs. -/
theorem step_time (h t : History T ι State Action) (a : G.core.JointActionAt h)
    (hpos : G.core.step h a t ≠ 0) :
    t.val.length = min (h.val.length + 1) T := by
  by_cases ht : h.val.length < T
  · obtain ⟨s, _, rfl⟩ := (G.step_active_support h ht a t).mp hpos
    rw [advance_length, Nat.min_eq_left (by omega)]
  · rw [G.step_terminal h ht a] at hpos
    have heq : t = h := by
      by_contra hne
      exact hpos (by simp [PMF.pure_apply, hne])
    subst t
    have := h.property
    omega

theorem run_time (n : Nat) (π : G.core.PureProfile) (ss : List (History T ι State Action))
    (hpos : pureRun G.core.pureStep G.core.init n π ss ≠ 0) :
    (G.core.lastState ss).val.length = min n T := by
  induction n generalizing ss with
  | zero =>
      have heq : ss = [G.core.init] := by
        by_contra hne
        exact hpos (by simp [pureRun, Math.TraceRun.traceRun, PMF.pure_apply, hne])
      subst ss
      simp [ObsModelCore.lastState, core, initialHistory]
  | succ n ih =>
      rcases List.eq_nil_or_concat ss with rfl | ⟨p, t, rfl⟩
      · exact False.elim (hpos (pureRun_succ_nil _ _ _ _))
      · simp only [List.concat_eq_append, pureRun_succ_append] at hpos
        have hp := left_ne_zero_of_mul hpos
        have ht := right_ne_zero_of_mul hpos
        rw [ObsModelCore.pureStep_eq] at ht
        have htime := G.step_time _ _ _ ht
        rw [ih p hp] at htime
        rw [List.concat_eq_append, ObsModelCore.lastState_append_singleton]
        omega

/-- Repeated information states occur only after absorption, where actions are unique. -/
theorem noNontrivialInfoStateRepeat : G.core.NoNontrivialInfoStateRepeat := by
  intro i π k ss hpos j₁ j₂ hj hj₂ heq
  rw [G.core.runDistPure_eq_pureRun] at hpos
  have hlen := pureRun_length G.core.pureStep G.core.init k π ss hpos
  have h₁ := pureRun_take_nonzero G.core.pureStep G.core.init k π ss hpos j₁ (by omega)
  have h₂ := pureRun_take_nonzero G.core.pureStep G.core.init k π ss hpos j₂ (by omega)
  have ht₁ := G.run_time j₁ π _ h₁
  have ht₂ := G.run_time j₂ π _ h₂
  have he := congrArg stage heq
  simp only [projectStates_eq, observe_stage] at he
  rw [ht₁, ht₂] at he
  apply terminal_action_subsingleton
  change ¬stage (G.core.projectStates i (ss.take (j₂ + 1))) < T
  rw [projectStates_eq, observe_stage, ht₂]
  omega

end Runs
end Game
end LegalMath.FiniteHorizon
