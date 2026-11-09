import JurisLean.FiniteHorizonAdequacy
import JurisLean.External.GameTheory.Theorems.NashExistenceMixed
import JurisLean.External.GameTheory.Core.GameProperties
import JurisLean.Candidates.FormalTail20261024

/-!
Finite-horizon multiplayer learning on the original complete game history.
Every private parameter is reconstructed from that player's complete personal
record, then used by its next decision. The old general Kuhn and direct-law
adequacy theorems are consumers of this policy, not replaced by a new game.
Source only; CI_NOT_RUN until subject-bound build and axiom artifacts exist.
-/
set_option autoImplicit false

namespace LegalMath20261110.RemainingClosure.MultiAgentFeedback

open LegalMath.FiniteHorizon
open Math.PMFProduct
open scoped ENNReal NNReal BigOperators

noncomputable section

structure PrivateLearning (Obs Action Parameter : Type) where
  initial : Obs → Parameter
  update : Parameter → Action → Obs → Parameter

variable {T : Nat} {ι State : Type} {Obs Action Parameter : ι → Type}

/-- No hidden environment input is accepted by the private learner. -/
def privateParameter {O A P : Type} (L : PrivateLearning O A P)
    (r : PersonalRecord T O A) : P :=
  r.2.val.foldl (fun θ observed => L.update θ observed.1 observed.2) (L.initial r.1)

lemma privateParameter_append {O A P : Type} (L : PrivateLearning O A P)
    (r : PersonalRecord T O A) (ht : stage r < T) (a : A) (o : O) :
    privateParameter L (append r ht a o) = L.update (privateParameter L r) a o := by
  simp [privateParameter, append, List.foldl_append]

def privateParameters (G : Game T ι State Obs Action)
    (L : (i : ι) → PrivateLearning (Obs i) (Action i) (Parameter i))
    (h : History T ι State Action) : (i : ι) → Parameter i :=
  fun i => privateParameter (L i) (G.observe i h)

theorem private_parameters_advance (G : Game T ι State Obs Action)
    (L : (i : ι) → PrivateLearning (Obs i) (Action i) (Parameter i))
    (h : History T ι State Action) (ht : h.val.length < T)
    (a : JointAction ι Action) (next : State) (i : ι) :
    privateParameters G L (G.advance h ht a next) i =
      (L i).update (privateParameters G L h i) (a i)
        (G.signal i (h.val ++ [(a,next)]) next) := by
  unfold privateParameters
  rw [G.observe_advance,privateParameter_append]

def learningPolicy
    (L : (i : ι) → PrivateLearning (Obs i) (Action i) (Parameter i))
    (choose : (i : ι) → PersonalRecord T (Obs i) (Action i) → Parameter i → PMF (Action i)) :
    BehavioralPlan T ι Obs Action :=
  fun i r => if ht : stage r < T then
    (choose i r (privateParameter (L i) r)).map (ofAction r ht)
  else PMF.pure (by simpa [ActionAt,ht] using ())

theorem learningPolicy_raw
    (L : (i : ι) → PrivateLearning (Obs i) (Action i) (Parameter i))
    (choose : (i : ι) → PersonalRecord T (Obs i) (Action i) → Parameter i → PMF (Action i))
    (i : ι) (r : PersonalRecord T (Obs i) (Action i)) (ht : stage r < T) :
    ((learningPolicy L choose) i r).map (toAction r ht) =
      choose i r (privateParameter (L i) r) := by
  simp only [learningPolicy,dif_pos ht,PMF.map_comp]
  simpa only [Function.comp_def,toAction_ofAction] using
    PMF.map_id (choose i r (privateParameter (L i) r))

/-- This is the actual next decision, after the same environment result has
updated each player's own observation and private parameter. -/
theorem next_decision_uses_actual_personal_update (G : Game T ι State Obs Action)
    (L : (i : ι) → PrivateLearning (Obs i) (Action i) (Parameter i))
    (choose : (i : ι) → PersonalRecord T (Obs i) (Action i) → Parameter i → PMF (Action i))
    (h : History T ι State Action) (ht : h.val.length < T)
    (a : JointAction ι Action) (next : State) (i : ι)
    (active : stage (G.observe i (G.advance h ht a next)) < T) :
    ((learningPolicy L choose) i (G.observe i (G.advance h ht a next))).map
        (toAction (G.observe i (G.advance h ht a next)) active) =
      choose i (G.observe i (G.advance h ht a next))
        ((L i).update (privateParameters G L h i) (a i)
          (G.signal i (h.val ++ [(a,next)]) next)) := by
  rw [learningPolicy_raw]
  change choose i _ (privateParameters G L (G.advance h ht a next) i) = _
  rw [private_parameters_advance]

theorem equal_personal_records_no_leak (G : Game T ι State Obs Action)
    (L : (i : ι) → PrivateLearning (Obs i) (Action i) (Parameter i))
    (choose : (i : ι) → PersonalRecord T (Obs i) (Action i) → Parameter i → PMF (Action i))
    (i : ι) (h t : History T ι State Action) (same : G.observe i h = G.observe i t) :
    privateParameters G L h i = privateParameters G L t i ∧
      choose i (G.observe i h) (privateParameters G L h i) =
        choose i (G.observe i t) (privateParameters G L t i) := by
  simp [privateParameters,same]

def unifiedReadout (G : Game T ι State Obs Action)
    (L : (i : ι) → PrivateLearning (Obs i) (Action i) (Parameter i))
    (payoff : History T ι State Action → ι → ℝ) (h : History T ι State Action) :=
  (h,(privateParameters G L h,payoff h))

def learnedPost (G : Game T ι State Obs Action)
    (L : (i : ι) → PrivateLearning (Obs i) (Action i) (Parameter i))
    (payoff : History T ι State Action → ι → ℝ)
    (h : History T ι State Action) (ht : h.val.length < T)
    (a : JointAction ι Action) (next : State) :=
  (G.advance h ht a next,
    ((fun i => (L i).update (privateParameters G L h i) (a i)
      (G.signal i (h.val ++ [(a,next)]) next)), payoff (G.advance h ht a next)))

lemma same_actual_joint_post (G : Game T ι State Obs Action)
    (L : (i : ι) → PrivateLearning (Obs i) (Action i) (Parameter i))
    (payoff : History T ι State Action → ι → ℝ)
    (h : History T ι State Action) (ht : h.val.length < T)
    (a : JointAction ι Action) (next : State) :
    unifiedReadout G L payoff (G.advance h ht a next) = learnedPost G L payoff h ht a next := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · funext i
      exact private_parameters_advance G L h ht a next i
    · rfl

section FinitePlayers
variable [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Action i)]

/-- One joint environment result supplies every player's next parameter and
all payoffs; it is not replaced by independently resampled player outcomes. -/
theorem native_step_joint_learning (G : Game T ι State Obs Action)
    (L : (i : ι) → PrivateLearning (Obs i) (Action i) (Parameter i))
    (choose : (i : ι) → PersonalRecord T (Obs i) (Action i) → Parameter i → PMF (Action i))
    (payoff : History T ι State Action → ι → ℝ)
    (h : History T ι State Action) (ht : h.val.length < T) :
    (G.nativeStep (learningPolicy L choose) h).map (unifiedReadout G L payoff) =
      (pmfPi (fun i => (learningPolicy L choose) i (G.observe i h))).bind (fun a =>
        (G.transition h (G.rawAction h ht a)).map
          (learnedPost G L payoff h ht (G.rawAction h ht a))) := by
  rw [Game.nativeStep,PMF.map_bind]
  congr 1
  funext a
  simp only [Game.step,dif_pos ht,PMF.map_comp]
  congr 1
  funext next
  exact same_actual_joint_post G L payoff h ht (G.rawAction h ht a) next

theorem core_direct_learning_adequacy (G : Game T ι State Obs Action)
    (L : (i : ι) → PrivateLearning (Obs i) (Action i) (Parameter i))
    (choose : (i : ι) → PersonalRecord T (Obs i) (Action i) → Parameter i → PMF (Action i))
    (payoff : History T ι State Action → ι → ℝ) (n : Nat) (_hn : n ≤ T) :
    (G.core.runDist n (learningPolicy L choose)).map
        (fun histories => unifiedReadout G L payoff (G.core.lastState histories)) =
      (G.nativeLaw (learningPolicy L choose) n).map (unifiedReadout G L payoff) :=
  G.native_readout_adequacy (learningPolicy L choose) (unifiedReadout G L payoff) n

variable [∀ i, Fintype (Obs i)]

/-- The original general multiplayer Kuhn theorem is consumed by the policy
that actually reconstructs and uses each private learning parameter. -/
theorem kuhn_preserves_joint_history_learning_payoff (G : Game T ι State Obs Action)
    (L : (i : ι) → PrivateLearning (Obs i) (Action i) (Parameter i))
    (choose : (i : ι) → PersonalRecord T (Obs i) (Action i) → Parameter i → PMF (Action i))
    (payoff : History T ι State Action → ι → ℝ) :
    ∀ n, n ≤ T →
      (G.nativeLaw (learningPolicy L choose) n).map (unifiedReadout G L payoff) =
      ((G.core.behavioralToMixedJoint (learningPolicy L choose)).bind
        (fun plans => G.nativeLawPure plans n)).map (unifiedReadout G L payoff) := by
  intro n hn
  exact G.native_behavioral_to_mixed_readout (learningPolicy L choose) (unifiedReadout G L payoff) n

/-- A deterministic candidate still performs private updates from its record. -/
def localLearningPlan {O A P : Type} (L : PrivateLearning O A P)
    (choose : PersonalRecord T O A → P → A) : LocalPlan T O A :=
  fun r => if ht : stage r < T then ofAction r ht (choose r (privateParameter L r))
  else by simpa [ActionAt,ht] using ()

/-- The strategic outcome of a candidate profile is the original learning
history law, with the original single payoff vector as utility. -/
def candidateGame (G : Game T ι State Obs Action)
    (L : (i : ι) → PrivateLearning (Obs i) (Action i) (Parameter i))
    (K : ι → Nat)
    (choose : (i : ι) → Fin (K i) → PersonalRecord T (Obs i) (Action i) → Parameter i → Action i)
    (payoff : History T ι State Action → ι → ℝ) : GameTheory.KernelGame ι where
  Strategy := fun i => Fin (K i)
  Outcome := History T ι State Action
  utility := payoff
  outcomeKernel := fun candidates =>
    G.nativeLawPure (fun i => localLearningPlan (L i) (choose i (candidates i))) T

/-- Finite nonempty candidate learning programs have a mixed equilibrium under
bounded actual utility. The very same candidate law has a Kuhn behavioral
realization preserving full history, private parameters and actual payoffs.
This is not a convergence theorem for arbitrary learning dynamics. -/
theorem finite_learning_equilibrium_and_kuhn (G : Game T ι State Obs Action)
    (L : (i : ι) → PrivateLearning (Obs i) (Action i) (Parameter i))
    (K : ι → Nat) (positive : ∀ i, 0 < K i)
    (choose : (i : ι) → Fin (K i) → PersonalRecord T (Obs i) (Action i) → Parameter i → Action i)
    (payoff : History T ι State Action → ι → ℝ) (C : ι → ℝ)
    (bounded : ∀ i h, |payoff h i| ≤ C i) [∀ i, Nonempty (Action i)] :
    ∃ μ : (i : ι) → PMF (Fin (K i)),
      (candidateGame G L K choose payoff).mixedExtension.IsNash μ ∧
      ∃ β : BehavioralPlan T ι Obs Action, ∀ n, n ≤ T →
        (G.nativeLaw β n).map (unifiedReadout G L payoff) =
          ((pmfPi μ).bind (fun candidates =>
            G.nativeLawPure (fun i => localLearningPlan (L i) (choose i (candidates i))) n)).map
              (unifiedReadout G L payoff) := by
  letI : ∀ i, Nonempty (Fin (K i)) := fun i => ⟨⟨0,positive i⟩⟩
  letI : ∀ i, Finite ((candidateGame G L K choose payoff).Strategy i) := fun i => by
    change Finite (Fin (K i))
    infer_instance
  letI : ∀ i, Nonempty ((candidateGame G L K choose payoff).Strategy i) := fun i => by
    change Nonempty (Fin (K i))
    infer_instance
  obtain ⟨μ,hNash⟩ := (candidateGame G L K choose payoff).mixed_nash_exists_of_bounded bounded
  obtain ⟨β,hβ⟩ := G.native_mixed_to_behavioral
    (fun i => (μ i).map (fun candidate => localLearningPlan (L i) (choose i candidate)))
  refine ⟨μ,hNash,β,?_⟩
  intro n hn
  have law := hβ n
  rw [pmfPi_map_bind] at law
  exact congrArg (fun distribution => distribution.map (unifiedReadout G L payoff)) law

end FinitePlayers

def bitLearning : PrivateLearning Bool Bool Bool where
  initial := fun _ => false
  update := fun _ _ observed => observed

def privateBitChoice (_ : Fin 2) (_ : PersonalRecord 2 Bool Bool) (parameter : Bool) : PMF Bool :=
  PMF.pure parameter

/-- The existing two-player private-information game supplies a nontrivial
consumer: player 1 changes its next decision after its private bit; player 0
cannot see that bit and keeps the same parameter and decision. -/
theorem two_player_learning_instance :
    privateParameters Examples.privateBits (fun _ : Fin 2 => bitLearning)
      (Examples.afterPrivateBit false) 1 = false ∧
    privateParameters Examples.privateBits (fun _ : Fin 2 => bitLearning)
      (Examples.afterPrivateBit true) 1 = true ∧
    privateParameters Examples.privateBits (fun _ : Fin 2 => bitLearning)
      (Examples.afterPrivateBit true) 0 = false ∧
    ((learningPolicy (fun _ : Fin 2 => bitLearning) privateBitChoice) 1
      (Examples.privateBits.observe 1 (Examples.afterPrivateBit true))).map
        (toAction (Examples.privateBits.observe 1 (Examples.afterPrivateBit true))
          (by simp [Examples.afterPrivateBit])) = PMF.pure true ∧
    Examples.privateBits.observe 0 (Examples.afterPrivateBit false) =
      Examples.privateBits.observe 0 (Examples.afterPrivateBit true) := by
  refine ⟨?_,?_,?_,?_,Examples.private_information_hidden⟩
  · simp [privateParameters,privateParameter,bitLearning,Examples.privateBits,
      Examples.afterPrivateBit,Examples.bits,Game.observe,Game.localLog]
  · simp [privateParameters,privateParameter,bitLearning,Examples.privateBits,
      Examples.afterPrivateBit,Examples.bits,Game.observe,Game.localLog]
  · simp [privateParameters,privateParameter,bitLearning,Examples.privateBits,
      Examples.afterPrivateBit,Examples.bits,Game.observe,Game.localLog]
  · rw [learningPolicy_raw (fun _ : Fin 2 => bitLearning) privateBitChoice (1 : Fin 2)
      (Examples.privateBits.observe 1 (Examples.afterPrivateBit true)) (by simp [Examples.afterPrivateBit])]
    simp [privateBitChoice,privateParameter,bitLearning,Examples.privateBits,
      Examples.afterPrivateBit,Examples.bits,Game.observe,Game.localLog]

theorem two_player_learning_kuhn
    (payoff : History 2 (Fin 2) (Fin 2 → Bool) (fun _ => Bool) → Fin 2 → ℝ) :
    ∀ n, n ≤ 2 →
      (Examples.privateBits.nativeLaw
        (learningPolicy (fun _ : Fin 2 => bitLearning) privateBitChoice) n).map
          (unifiedReadout Examples.privateBits (fun _ : Fin 2 => bitLearning) payoff) =
      ((Examples.privateBits.core.behavioralToMixedJoint
        (learningPolicy (fun _ : Fin 2 => bitLearning) privateBitChoice)).bind
        (fun plans => Examples.privateBits.nativeLawPure plans n)).map
          (unifiedReadout Examples.privateBits (fun _ : Fin 2 => bitLearning) payoff) :=
  kuhn_preserves_joint_history_learning_payoff Examples.privateBits
    (fun _ : Fin 2 => bitLearning) privateBitChoice payoff

/-- A nonempty legal menu is an explicit domain input, not supplied by a
statistical forecast. Every sampled menu index maps to a real allowed action. -/
def menuChoice {A : Type} (menu : List A) (indices : PMF (Fin menu.length)) : PMF A :=
  indices.map (fun i => menu.get i)

theorem menuChoice_support {A : Type} (menu : List A) (indices : PMF (Fin menu.length))
    (a : A) (member : a ∈ (menuChoice menu indices).support) : a ∈ menu := by
  obtain ⟨i,_,same⟩ := (PMF.mem_support_map_iff _ _ _).mp member
  rw [← same]
  exact List.get_mem _ _

theorem menuChoice_permitted {A : Type} (menu : List A) (indices : PMF (Fin menu.length))
    (allowed : A → Prop) (sound : ∀ a ∈ menu, allowed a)
    (a : A) (member : a ∈ (menuChoice menu indices).support) : allowed a :=
  sound a (menuChoice_support menu indices a member)

/-- The private learning policy can consume only indexed members of its
actual record-dependent legal menu. Empty menus cannot supply a PMF of indices
and use the explicit NoAllowedAction branch of InterpretationChoice. -/
def menuLearningPolicy
    (L : (i : ι) → PrivateLearning (Obs i) (Action i) (Parameter i))
    (menus : (i : ι) → PersonalRecord T (Obs i) (Action i) → List (Action i))
    (draw : (i : ι) → (r : PersonalRecord T (Obs i) (Action i)) →
      Parameter i → PMF (Fin (menus i r).length)) : BehavioralPlan T ι Obs Action :=
  learningPolicy L (fun i r θ => menuChoice (menus i r) (draw i r θ))

theorem actual_private_policy_is_permitted
    (L : (i : ι) → PrivateLearning (Obs i) (Action i) (Parameter i))
    (menus : (i : ι) → PersonalRecord T (Obs i) (Action i) → List (Action i))
    (draw : (i : ι) → (r : PersonalRecord T (Obs i) (Action i)) →
      Parameter i → PMF (Fin (menus i r).length))
    (allowed : (i : ι) → PersonalRecord T (Obs i) (Action i) → Action i → Prop)
    (sound : ∀ i r a, a ∈ menus i r → allowed i r a)
    (i : ι) (r : PersonalRecord T (Obs i) (Action i)) (ht : stage r < T)
    (a : Action i) (member : a ∈
      (((menuLearningPolicy L menus draw) i r).map (toAction r ht)).support) :
    allowed i r a := by
  have raw := learningPolicy_raw L
    (fun i r θ => menuChoice (menus i r) (draw i r θ)) i r ht
  change a ∈ (((learningPolicy L
    (fun i r θ => menuChoice (menus i r) (draw i r θ))) i r).map (toAction r ht)).support at member
  rw [raw] at member
  exact menuChoice_permitted (menus i r) (draw i r (privateParameter (L i) r))
    (allowed i r) (sound i r) a member

/-- A shared signal is a single joint draw, distinct from independent marginals. -/
def fairBit : PMF Bool := PMF.bernoulli (1/2) (by norm_num)
def sharedSignal : PMF (Bool × Bool) := fairBit.map (fun b => (b,b))
def independentSignals : PMF (Bool × Bool) :=
  fairBit.bind (fun a => fairBit.map (fun b => (a,b)))

theorem correlation_is_not_independent_product :
    sharedSignal.map Prod.fst = fairBit ∧ sharedSignal.map Prod.snd = fairBit ∧
    independentSignals.map Prod.fst = fairBit ∧ independentSignals.map Prod.snd = fairBit ∧
    sharedSignal (false,true) = 0 ∧ independentSignals (false,true) = (1/4 : ℝ≥0∞) ∧
    sharedSignal ≠ independentSignals := by
  have univ : (Finset.univ : Finset Bool) = {false,true} := by decide
  have correlated : sharedSignal (false,true) = 0 := by
    norm_num [sharedSignal,fairBit,PMF.map_apply,tsum_fintype,univ,PMF.bernoulli_apply]
  have separate : independentSignals (false,true) = (1/4 : ℝ≥0∞) := by
    norm_num [independentSignals,fairBit,PMF.bind_apply,PMF.map_apply,
      tsum_fintype,univ,PMF.bernoulli_apply]
    rw [← ENNReal.mul_inv (a := (2:ℝ≥0∞)) (b := 2)
      (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    norm_num
  refine ⟨?_,?_,?_,?_,correlated,separate,?_⟩
  · rw [sharedSignal,PMF.map_comp]
    change fairBit.map id = fairBit
    exact PMF.map_id fairBit
  · rw [sharedSignal,PMF.map_comp]
    change fairBit.map id = fairBit
    exact PMF.map_id fairBit
  · ext b
    cases b <;> norm_num [independentSignals,fairBit,PMF.map_bind,PMF.map_comp,
      PMF.bind_apply,PMF.map_apply,tsum_fintype,univ,PMF.bernoulli_apply]
  · ext b
    cases b <;> norm_num [independentSignals,fairBit,PMF.map_bind,PMF.map_comp,
      PMF.bind_apply,PMF.map_apply,tsum_fintype,univ,PMF.bernoulli_apply]
  · intro same
    have atOffDiagonal := congrArg (fun distribution : PMF (Bool × Bool) => distribution (false,true)) same
    change sharedSignal (false,true) = independentSignals (false,true) at atOffDiagonal
    rw [correlated,separate] at atOffDiagonal
    exact (ENNReal.inv_ne_zero.mpr (by norm_num : (4:ℝ≥0∞) ≠ ∞))
      (by simpa only [one_div] using atOffDiagonal.symm)

#print axioms private_parameters_advance
#print axioms next_decision_uses_actual_personal_update
#print axioms native_step_joint_learning
#print axioms core_direct_learning_adequacy
#print axioms kuhn_preserves_joint_history_learning_payoff
#print axioms finite_learning_equilibrium_and_kuhn
#print axioms menuChoice_permitted
#print axioms correlation_is_not_independent_product

end

noncomputable section

section GuardedLearningSelection

variable {I : Type} [Fintype I] [DecidableEq I]
  {S : I → Type} [∀ i, Fintype (S i)]

/-- The conclusion of Nash, used with the original game's exact expected utility. -/
def HasNoGain (u : ((i : I) → S i) → I → ℝ) (σ : (i : I) → S i) : Prop :=
  ∀ i a, u (Function.update σ i a) i ≤ u σ i

def EstimatedGain (v : ((i : I) → S i) → I → ℝ) (η : ℝ)
    (σ : (i : I) → S i) : Prop :=
  ∃ move : Sigma S, 2*η < v (Function.update σ move.1 move.2) move.1 - v σ move.1

/-- One player changes only when its estimated gain exceeds the two-error guard. -/
def guardedStep (v : ((i : I) → S i) → I → ℝ) (η : ℝ)
    (σ : (i : I) → S i) : (i : I) → S i := by
  classical
  exact if h : EstimatedGain v η σ then
    Function.update σ (Classical.choose h).1 (Classical.choose h).2 else σ

def guardedPath (v : ℕ → ((i : I) → S i) → I → ℝ) (η : ℝ)
    (initial : (i : I) → S i) : ℕ → (i : I) → S i
  | 0 => initial
  | n+1 => guardedStep (v n) η (guardedPath v η initial n)

lemma guarded_gain_is_real (u v : ((i : I) → S i) → I → ℝ) (η : ℝ)
    (accurate : ∀ σ i, |u σ i - v σ i| ≤ η)
    (σ : (i : I) → S i) (move : Sigma S)
    (gain : 2*η < v (Function.update σ move.1 move.2) move.1 - v σ move.1) :
    u σ move.1 < u (Function.update σ move.1 move.2) move.1 := by
  have ha := (abs_le.mp (accurate (Function.update σ move.1 move.2) move.1)).1
  have hb := (abs_le.mp (accurate σ move.1)).2
  linarith

lemma profitable_move_is_detected (u v : ((i : I) → S i) → I → ℝ) (η δ : ℝ)
    (accurate : ∀ σ i, |u σ i - v σ i| ≤ η)
    (gap : ∀ σ i a, u σ i < u (Function.update σ i a) i →
      δ ≤ u (Function.update σ i a) i - u σ i)
    (separated : 4*η < δ) (σ : (i : I) → S i) (notNash : ¬ HasNoGain u σ) :
    EstimatedGain v η σ := by
  classical
  have profitable : ∃ i a, u σ i < u (Function.update σ i a) i := by
    simpa only [HasNoGain,not_forall,not_le] using notNash
  obtain ⟨i,a,ha⟩ := profitable
  refine ⟨⟨i,a⟩,?_⟩
  have hd := gap σ i a ha
  have hc := (abs_le.mp (accurate σ i)).1
  have ht := (abs_le.mp (accurate (Function.update σ i a) i)).2
  linarith

lemma guardedStep_of_nash (u v : ((i : I) → S i) → I → ℝ) (η : ℝ)
    (accurate : ∀ σ i, |u σ i - v σ i| ≤ η)
    (σ : (i : I) → S i) (nash : HasNoGain u σ) : guardedStep v η σ = σ := by
  classical
  have absent : ¬ EstimatedGain v η σ := by
    rintro ⟨move,gain⟩
    exact not_lt_of_ge (nash move.1 move.2) (guarded_gain_is_real u v η accurate σ move gain)
  simp only [guardedStep,dif_neg absent]

/-- Finite potential values induce a natural rank without assuming termination. -/
def potentialRank (Φ : ((i : I) → S i) → ℝ) (σ : (i : I) → S i) : ℕ := by
  classical
  exact (Finset.univ.filter (fun τ => Φ σ < Φ τ)).card

lemma potentialRank_decreases (Φ : ((i : I) → S i) → ℝ)
    (σ τ : (i : I) → S i) (improves : Φ σ < Φ τ) :
    potentialRank Φ τ < potentialRank Φ σ := by
  classical
  unfold potentialRank
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_,?_⟩
  · intro x hx
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hx ⊢
    exact lt_trans improves hx
  · intro same
    have member : τ ∈ Finset.univ.filter (fun x => Φ σ < Φ x) := by simp [improves]
    rw [← same] at member
    simpa using member

lemma guardedStep_decreases_rank (u : ((i : I) → S i) → I → ℝ)
    (v : ((i : I) → S i) → I → ℝ) (η δ : ℝ)
    (accurate : ∀ σ i, |u σ i - v σ i| ≤ η)
    (gap : ∀ σ i a, u σ i < u (Function.update σ i a) i →
      δ ≤ u (Function.update σ i a) i - u σ i)
    (separated : 4*η < δ)
    (Φ : ((i : I) → S i) → ℝ)
    (potential : ∀ σ i a, u σ i < u (Function.update σ i a) i →
      Φ σ < Φ (Function.update σ i a))
    (σ : (i : I) → S i) (notNash : ¬ HasNoGain u σ) :
    potentialRank Φ (guardedStep v η σ) < potentialRank Φ σ := by
  classical
  have available := profitable_move_is_detected u v η δ accurate gap separated σ notNash
  have actual := guarded_gain_is_real u v η accurate σ (Classical.choose available)
    (Classical.choose_spec available)
  rw [guardedStep,dif_pos available]
  exact potentialRank_decreases Φ σ _ (potential σ _ _ actual)

/-- Consume the pre-existing finite strict-improvement trace, not a new
axiomatized termination principle. -/
lemma strict_rank_trace {P : Type} (rank : P → ℕ) (path : ℕ → P) (start len : ℕ)
    (drop : ∀ j, j < len → rank (path (start+j+1)) < rank (path (start+j))) :
    JurisLean.Candidates.FormalTail20261024.FinStrictImprove rank
      (path start) len (path (start+len)) := by
  induction len generalizing start with
  | zero => simpa using JurisLean.Candidates.FormalTail20261024.FinStrictImprove.nil (rank := rank) (path start)
  | succ len ih =>
      have first := drop 0 (Nat.zero_lt_succ len)
      have tail := ih (start+1) (fun j hj => by
        have h := drop (j+1) (by omega)
        simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h)
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        JurisLean.Candidates.FormalTail20261024.FinStrictImprove.cons
          (by simpa using first) tail

/-- Uniformly accurate private estimates, a positive true gain gap and an
ordinal potential force this defined asynchronous selection to terminate at
Nash. Neither convergence nor Nash is a premise. -/
theorem guarded_learning_selection_converges
    (u : ((i : I) → S i) → I → ℝ) (v : ℕ → ((i : I) → S i) → I → ℝ) (η δ : ℝ)
    (accurate : ∀ n σ i, |u σ i - v n σ i| ≤ η)
    (gap : ∀ σ i a, u σ i < u (Function.update σ i a) i →
      δ ≤ u (Function.update σ i a) i - u σ i)
    (separated : 4*η < δ)
    (Φ : ((i : I) → S i) → ℝ)
    (potential : ∀ σ i a, u σ i < u (Function.update σ i a) i →
      Φ σ < Φ (Function.update σ i a)) (initial : (i : I) → S i) :
    ∃ N, N ≤ potentialRank Φ initial ∧ HasNoGain u (guardedPath v η initial N) ∧
      ∀ n, N ≤ n → guardedPath v η initial n = guardedPath v η initial N := by
  classical
  have reaches : ∃ N, N ≤ potentialRank Φ initial ∧ HasNoGain u (guardedPath v η initial N) := by
    by_contra never
    push_neg at never
    have trace := strict_rank_trace (potentialRank Φ) (guardedPath v η initial) 0
      (potentialRank Φ initial + 1) (fun j hj => by
        have non := never j (by omega)
        simpa [guardedPath] using guardedStep_decreases_rank u (v j) η δ
          (accurate j) gap separated Φ potential (guardedPath v η initial j) non)
    have length := JurisLean.Candidates.FormalTail20261024.u15_1_finite_state_strict_improve_length_bound
      (potentialRank Φ) trace
    change potentialRank Φ initial + 1 ≤ potentialRank Φ initial at length
    omega
  obtain ⟨N,bound,nash⟩ := reaches
  refine ⟨N,bound,nash,?_⟩
  intro n hn
  induction n,hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
      change guardedStep (v n) η (guardedPath v η initial n) = _
      rw [ih]
      exact guardedStep_of_nash u (v n) η (accurate n) _ nash

end GuardedLearningSelection

section PrivateLearningSelectionConsumer

variable {T : Nat} {ι State : Type} {Obs Action Parameter : ι → Type}
  [Fintype ι] [DecidableEq ι] [∀ i, Fintype (Obs i)] [∀ i, Fintype (Action i)]

/-- The fixed evaluation game is the same original finite-horizon experiment:
its candidate programs retain private updates and its readout retains history,
all private parameters and the same actual payoff. Stabilizing its candidate
profile never resets the continuing legal system or freezes private parameters. -/
theorem private_learning_selection_joint_converges
    (G : Game T ι State Obs Action)
    (L : (i : ι) → PrivateLearning (Obs i) (Action i) (Parameter i))
    (K : ι → ℕ)
    (choose : (i : ι) → Fin (K i) → PersonalRecord T (Obs i) (Action i) → Parameter i → Action i)
    (payoff : History T ι State Action → ι → ℝ)
    (C : ι → ℝ) (bounded : ∀ i h, |payoff h i| ≤ C i)
    (completed : ℕ → History T ι State Action)
    (estimate : (i : ι) → Parameter i → ((j : ι) → Fin (K j)) → ℝ)
    (η δ : ℝ) (Φ : ((i : ι) → Fin (K i)) → ℝ)
    (accurate : ∀ n σ i,
      |(candidateGame G L K choose payoff).eu σ i -
        estimate i (privateParameters G L (completed n) i) σ| ≤ η)
    (gap : ∀ σ i a,
      (candidateGame G L K choose payoff).eu σ i <
        (candidateGame G L K choose payoff).eu (Function.update σ i a) i →
      δ ≤ (candidateGame G L K choose payoff).eu (Function.update σ i a) i -
        (candidateGame G L K choose payoff).eu σ i)
    (separated : 4*η < δ)
    (potential : (candidateGame G L K choose payoff).IsOrdinalPotential Φ)
    (permitted : (i : ι) → PersonalRecord T (Obs i) (Action i) → Action i → Prop)
    (legalPrograms : ∀ i k r, stage r < T →
      permitted i r (choose i k r (privateParameter (L i) r)))
    (initial : (i : ι) → Fin (K i)) :
    let v := fun n σ i => estimate i (privateParameters G L (completed n) i) σ
    ∃ N, N ≤ potentialRank Φ initial ∧
      (∀ (σ : (i : ι) → Fin (K i)) i, Summable (fun h =>
        (G.nativeLawPure (fun j => localLearningPlan (L j) (choose j (σ j))) T h).toReal * payoff h i)) ∧
      (candidateGame G L K choose payoff).IsNash (guardedPath v η initial N) ∧
      (∀ i r, stage r < T → permitted i r (choose i (guardedPath v η initial N i) r
        (privateParameter (L i) r))) ∧
      ∀ n, N ≤ n → ∀ t, t ≤ T →
        (G.nativeLawPure (fun i => localLearningPlan (L i)
          (choose i (guardedPath v η initial n i))) t).map (unifiedReadout G L payoff) =
        (G.nativeLawPure (fun i => localLearningPlan (L i)
          (choose i (guardedPath v η initial N i))) t).map (unifiedReadout G L payoff) := by
  let v := fun n σ i => estimate i (privateParameters G L (completed n) i) σ
  have hp : ∀ σ i a,
      (candidateGame G L K choose payoff).eu σ i <
        (candidateGame G L K choose payoff).eu (Function.update σ i a) i →
      Φ σ < Φ (Function.update σ i a) := fun σ i a h => (potential i σ a).mp h
  obtain ⟨N,bound,nash,stable⟩ := guarded_learning_selection_converges
    (I := ι) (S := fun i => Fin (K i))
    (fun σ i => (candidateGame G L K choose payoff).eu σ i) v η δ accurate gap
      separated Φ hp initial
  refine ⟨N,bound,?_,nash,?_,?_⟩
  · intro σ i
    exact Math.Probability.expect_summable_of_bounded _ _ (bounded i)
  · intro i r active
    exact legalPrograms i _ r active
  · intro n hn t ht
    rw [stable n hn]

/-- A minimal two-player coordination counterexample: simultaneous current
best replies cycle. Strict potential descent requires the stated asynchronous
one-player revision, not arbitrary learning dynamics. -/
def simultaneousReply (s : Bool × Bool) : Bool × Bool := (s.2,s.1)

def coordinationPayoff (s : Bool × Bool) : ℝ := if s.1 = s.2 then 1 else 0

theorem simultaneous_best_replies_can_cycle :
    simultaneousReply (false,true) = (true,false) ∧
    simultaneousReply (true,false) = (false,true) ∧
    (false,true) ≠ (true,false) ∧
    (∀ s : Bool × Bool, ∀ a : Bool,
      coordinationPayoff (a,s.2) ≤ coordinationPayoff ((simultaneousReply s).1,s.2)) ∧
    (∀ s : Bool × Bool, ∀ a : Bool,
      coordinationPayoff (s.1,a) ≤ coordinationPayoff (s.1,(simultaneousReply s).2)) := by
  refine ⟨rfl,rfl,by decide,?_,?_⟩
  · rintro ⟨x,y⟩ a
    cases x <;> cases y <;> cases a <;> norm_num [simultaneousReply,coordinationPayoff]
  · rintro ⟨x,y⟩ a
    cases x <;> cases y <;> cases a <;> norm_num [simultaneousReply,coordinationPayoff]

end PrivateLearningSelectionConsumer

end

#print axioms guarded_learning_selection_converges
#print axioms private_learning_selection_joint_converges
#print axioms simultaneous_best_replies_can_cycle

end LegalMath20261110.RemainingClosure.MultiAgentFeedback
