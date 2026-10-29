/-
CI_NOT_RUN. Mechanically combined from the two reviewed U06.2 drafts.
-/

import JurisLean.Candidates.Final20261021.Decision
import JurisLean.Seams.UnifiedEquilExist
import JurisLean.Seams.UnifiedW4Games

open scoped BigOperators

namespace JurisLean.Candidates.U06_2EquilibriumTransfer20261030


/-!
U06.2:
* Finite pure-action carriers; independent mixed profiles use the existing pmfPi.
* The 2η estimate is reused from Decision.
* A change of strategy carrier requires an actual Equiv and an iff covering
  every allowed deviation.
* The equivalence assumption does not certify that any particular migration
  preserves its action tree, information structure, or chance mechanism.
-/

theorem finite_expect_disturbance
    {Ω : Type*} [Fintype Ω]
    (d : PMF Ω) (f g : Ω → ℝ) (η : ℝ)
    (disturbance : ∀ ω, |f ω - g ω| ≤ η) :
    |Math.Probability.expect d f -
      Math.Probability.expect d g| ≤ η := by
  have hsum := Math.Probability.pmf_toReal_sum_one d
  have hdiff :
      Math.Probability.expect d f -
        Math.Probability.expect d g =
      ∑ ω, (d ω).toReal * (f ω - g ω) := by
    rw [Math.Probability.expect_eq_sum,
      Math.Probability.expect_eq_sum,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro ω _
    ring
  rw [hdiff]
  apply abs_le.mpr
  constructor
  · calc
      -η = (∑ ω, (d ω).toReal) * (-η) := by
        rw [hsum, one_mul]
      _ = ∑ ω, (d ω).toReal * (-η) := by
        rw [Finset.sum_mul]
      _ ≤ ∑ ω, (d ω).toReal * (f ω - g ω) := by
        exact Finset.sum_le_sum (fun ω _ =>
          mul_le_mul_of_nonneg_left
            (abs_le.mp (disturbance ω)).1
            ENNReal.toReal_nonneg)
  · calc
      (∑ ω, (d ω).toReal * (f ω - g ω)) ≤
          ∑ ω, (d ω).toReal * η := by
        exact Finset.sum_le_sum (fun ω _ =>
          mul_le_mul_of_nonneg_left
            (abs_le.mp (disturbance ω)).2
            ENNReal.toReal_nonneg)
      _ = (∑ ω, (d ω).toReal) * η := by
        rw [Finset.sum_mul]
      _ = η := by
        rw [hsum, one_mul]

theorem finite_expect_affine
    {Ω : Type*} [Fintype Ω]
    (d : PMF Ω) (f : Ω → ℝ) (scale shift : ℝ) :
    Math.Probability.expect d (fun ω => scale * f ω + shift) =
      scale * Math.Probability.expect d f + shift := by
  rw [Math.Probability.expect_eq_sum,
    Math.Probability.expect_eq_sum]
  calc
    (∑ ω, (d ω).toReal * (scale * f ω + shift)) =
        ∑ ω, (scale * ((d ω).toReal * f ω) +
          shift * (d ω).toReal) := by
      apply Finset.sum_congr rfl
      intro ω _
      ring
    _ = scale * (∑ ω, (d ω).toReal * f ω) +
        shift * (∑ ω, (d ω).toReal) := by
      rw [Finset.sum_add_distrib,
        Finset.mul_sum, Finset.mul_sum]
    _ = scale * (∑ ω, (d ω).toReal * f ω) + shift := by
      rw [Math.Probability.pmf_toReal_sum_one d, mul_one]

theorem finite_expect_positiveAffine_preference
    {Ω : Type*} [Fintype Ω]
    (d q : PMF Ω) (f g : Ω → ℝ)
    (scale shift : ℝ) (positive : 0 < scale) :
    (Math.Probability.expect d (fun ω => scale * f ω + shift) ≤
      Math.Probability.expect q (fun ω => scale * g ω + shift)) ↔
    (Math.Probability.expect d f ≤
      Math.Probability.expect q g) := by
  rw [finite_expect_affine, finite_expect_affine]
  constructor
  · intro h
    exact (mul_le_mul_left positive).mp
      ((add_le_add_iff_right shift).mp h)
  · intro h
    exact (add_le_add_iff_right shift).mpr
      ((mul_le_mul_left positive).mpr h)

/-- The mixed transfer also permits different finite action types by player. -/
theorem product_pmf_equilibrium_transfer
    {I : Type*} [Fintype I] [DecidableEq I]
    {A : I → Type*} [∀ i, Fintype (A i)]
    (u v : (∀ i, A i) → I → ℝ)
    (chosen : ∀ i, PMF (A i))
    (ε η : I → ℝ)
    (disturbance : ∀ i a, |u a i - v a i| ≤ η i)
    (approximate :
      ∀ i (τ : PMF (A i)),
        Math.Probability.expect
            (Math.PMFProduct.pmfPi
              (A := A) (Function.update chosen i τ))
            (fun a => v a i) -
          Math.Probability.expect
            (Math.PMFProduct.pmfPi (A := A) chosen)
            (fun a => v a i) ≤ ε i) :
    ∀ i (τ : PMF (A i)),
      Math.Probability.expect
          (Math.PMFProduct.pmfPi
            (A := A) (Function.update chosen i τ))
          (fun a => u a i) -
        Math.Probability.expect
          (Math.PMFProduct.pmfPi (A := A) chosen)
          (fun a => u a i) ≤ ε i + 2 * η i := by
  have transfer :=
    JurisLean.Candidates.Final20261021.Decision.u06_2_approx_equilibrium_transfer
      (u := fun i σ =>
        Math.Probability.expect
          (Math.PMFProduct.pmfPi (A := A) σ)
          (fun a => u a i))
      (v := fun i σ =>
        Math.Probability.expect
          (Math.PMFProduct.pmfPi (A := A) σ)
          (fun a => v a i))
      (deviation := fun i σ σ' =>
        ∃ τ : PMF (A i), σ' = Function.update σ i τ)
      (chosen := chosen)
      (ε := ε) (η := η)
      (disturbance := by
        intro i σ
        exact finite_expect_disturbance
          (Math.PMFProduct.pmfPi (A := A) σ)
          (fun a => u a i) (fun a => v a i)
          (η i) (disturbance i))
      (approximate := by
        rintro i σ' ⟨τ, rfl⟩
        exact approximate i τ)
  intro i τ
  exact transfer i (Function.update chosen i τ) ⟨τ, rfl⟩

/--
An actual equivalence and a two-way deviation correspondence cover every target
deviation. The target equilibrium is a conclusion, never an assumption.
-/
theorem equiv_deviation_equilibrium_transfer
    {Player Source Target : Type*}
    [Fintype Player] [Fintype Source] [Fintype Target]
    (e : Source ≃ Target)
    (u : Player → Target → ℝ)
    (v : Player → Source → ℝ)
    (sourceDeviation : Player → Source → Source → Prop)
    (targetDeviation : Player → Target → Target → Prop)
    (chosen : Source) (ε η : Player → ℝ)
    (deviationCorrespondence :
      ∀ i a b,
        targetDeviation i (e a) (e b) ↔
          sourceDeviation i a b)
    (disturbance : ∀ i a, |u i (e a) - v i a| ≤ η i)
    (approximate :
      ∀ i a, sourceDeviation i chosen a →
        v i a - v i chosen ≤ ε i) :
    ∀ i b, targetDeviation i (e chosen) b →
      u i b - u i (e chosen) ≤ ε i + 2 * η i := by
  have transfer :=
    JurisLean.Candidates.Final20261021.Decision.u06_2_approx_equilibrium_transfer
      (u := fun i a => u i (e a))
      (v := v)
      (deviation := sourceDeviation)
      (chosen := chosen)
      (ε := ε) (η := η)
      disturbance approximate
  intro i b hb
  have hb' :
      targetDeviation i (e chosen) (e (e.symm b)) := by
    simpa using hb
  have sourceAllowed :
      sourceDeviation i chosen (e.symm b) :=
    (deviationCorrespondence i chosen (e.symm b)).mp hb'
  simpa using transfer i (e.symm b) sourceAllowed

section ActualLegalGame

open JurisLean.Seams.UnifiedEquilExist

variable {I : Type} [Fintype I] [DecidableEq I]
variable {Act : Type} [Fintype Act] [DecidableEq Act]

/-- Connection to the existing KernelGame mixed extension and product PMF. -/
theorem legalGame_mixedExtension_expect
    (u : (I → Act) → I → ℝ)
    (σ : ∀ _ : I, PMF Act) (i : I) :
    (legalGame u).mixedExtension.eu σ i =
      Math.Probability.expect
        (Math.PMFProduct.pmfPi (A := fun _ : I => Act) σ)
        (fun a => u a i) := by
  rw [legalGame_mixedExtension_eu,
    Math.Probability.expect_eq_sum]
  simp only [Math.PMFProduct.pmfPi_apply, ENNReal.toReal_prod]
  rfl

/-- Every mixed unilateral replacement row is included. -/
theorem legalGame_mixed_equilibrium_transfer
    (u v : (I → Act) → I → ℝ)
    (chosen : ∀ _ : I, PMF Act)
    (ε η : I → ℝ)
    (disturbance : ∀ i a, |u a i - v a i| ≤ η i)
    (approximate :
      ∀ i (τ : PMF Act),
        (legalGame v).mixedExtension.eu
            (Function.update chosen i τ) i -
          (legalGame v).mixedExtension.eu chosen i ≤ ε i) :
    ∀ i (τ : PMF Act),
      (legalGame u).mixedExtension.eu
          (Function.update chosen i τ) i -
        (legalGame u).mixedExtension.eu chosen i ≤
          ε i + 2 * η i := by
  have transfer :=
    product_pmf_equilibrium_transfer
      (A := fun _ : I => Act)
      u v chosen ε η disturbance
      (by
        intro i τ
        simpa only [legalGame_mixedExtension_expect]
          using approximate i τ)
  intro i τ
  simpa only [legalGame_mixedExtension_expect]
    using transfer i τ

theorem legalGame_mixedExtension_affine
    (u : (I → Act) → I → ℝ)
    (scale shift : I → ℝ)
    (σ : ∀ _ : I, PMF Act) (i : I) :
    (legalGame (fun a j => scale j * u a j + shift j))
        .mixedExtension.eu σ i =
      scale i * (legalGame u).mixedExtension.eu σ i + shift i := by
  simpa only [legalGame_mixedExtension_expect] using
    finite_expect_affine
      (Math.PMFProduct.pmfPi (A := fun _ : I => Act) σ)
      (fun a => u a i) (scale i) (shift i)

/-- Positive affine transformations preserve every player's mixed best response. -/
theorem legalGame_positiveAffine_bestResponse
    (u : (I → Act) → I → ℝ)
    (scale shift : I → ℝ)
    (positive : ∀ i, 0 < scale i)
    (chosen : ∀ _ : I, PMF Act) (i : I) :
    (∀ τ : PMF Act,
      (legalGame (fun a j => scale j * u a j + shift j))
          .mixedExtension.eu (Function.update chosen i τ) i ≤
        (legalGame (fun a j => scale j * u a j + shift j))
          .mixedExtension.eu chosen i) ↔
    (∀ τ : PMF Act,
      (legalGame u).mixedExtension.eu
          (Function.update chosen i τ) i ≤
        (legalGame u).mixedExtension.eu chosen i) := by
  constructor
  · intro h τ
    have hτ := h τ
    rw [legalGame_mixedExtension_affine,
      legalGame_mixedExtension_affine] at hτ
    exact (mul_le_mul_left (positive i)).mp
      ((add_le_add_iff_right (shift i)).mp hτ)
  · intro h τ
    rw [legalGame_mixedExtension_affine,
      legalGame_mixedExtension_affine]
    exact (add_le_add_iff_right (shift i)).mpr
      ((mul_le_mul_left (positive i)).mpr (h τ))

end ActualLegalGame

/--
A one-player finite game: all old actions have payoff 0, the embedding has
zero payoff error, but the added action has payoff 1 and breaks equilibrium.
-/
theorem added_action_counterexample :
    ∃ (embed : Fin 1 → Fin 2)
      (oldPayoff : Fin 1 → ℝ) (newPayoff : Fin 2 → ℝ),
      Function.Injective embed ∧
      (∀ a, |newPayoff (embed a) - oldPayoff a| ≤ (0 : ℝ)) ∧
      (∀ a, oldPayoff a - oldPayoff 0 ≤ 0) ∧
      ¬ (∀ a, newPayoff a - newPayoff (embed 0) ≤ 0) := by
  refine ⟨(fun _ => 0), (fun _ => 0),
    (fun a => if a = 0 then 0 else 1), ?_, ?_, ?_, ?_⟩
  · intro a b _
    exact Subsingleton.elim a b
  · intro a
    norm_num
  · intro a
    norm_num
  · intro h
    have hbad := h (1 : Fin 2)
    norm_num at hbad

/--
The transform is globally strictly increasing.
Certain payoff 2 beats the fair 0/3 lottery before transformation;
after transformation the expectations are 2 and 5/2.
-/
theorem strictMono_expected_preference_reversal :
    ∃ (φ : ℝ → ℝ) (d : PMF (Fin 2)),
      StrictMono φ ∧
      (Math.Probability.expect d (fun _ : Fin 2 => (2 : ℝ)) >
        Math.Probability.expect d
          (fun a => if a = 0 then (0 : ℝ) else 3)) ∧
      (Math.Probability.expect d (fun _ : Fin 2 => φ 2) <
        Math.Probability.expect d
          (fun a => φ (if a = 0 then (0 : ℝ) else 3))) := by
  classical
  let φ : ℝ → ℝ := fun x =>
    if x ≤ 2 then x else 3 * x - 4
  have monotone : StrictMono φ := by
    intro x y hxy
    by_cases hx : x ≤ 2
    · by_cases hy : y ≤ 2
      · simpa only [φ, if_pos hx, if_pos hy] using hxy
      · simp only [φ, if_pos hx, if_neg hy]
        have hy' : (2 : ℝ) < y := lt_of_not_ge hy
        linarith
    · by_cases hy : y ≤ 2
      · exact (hx (le_trans (le_of_lt hxy) hy)).elim
      · simp only [φ, if_neg hx, if_neg hy]
        linarith
  let d : PMF (Fin 2) :=
    PMF.ofFintype
      (fun _ : Fin 2 => (1 / 2 : ℝ≥0∞))
      (by norm_num [Fin.sum_univ_succ])
  have mass (a : Fin 2) :
      (d a).toReal = (1 / 2 : ℝ) := by
    norm_num [d, PMF.ofFintype_apply]
  refine ⟨φ, d, monotone, ?_, ?_⟩
  · rw [Math.Probability.expect_eq_sum,
      Math.Probability.expect_eq_sum]
    simp only [mass]
    norm_num [Fin.sum_univ_succ]
  · rw [Math.Probability.expect_eq_sum,
      Math.Probability.expect_eq_sum]
    simp only [mass]
    norm_num [Fin.sum_univ_succ, φ]


open JurisLean.Seams.UnifiedW4Games

/- false is player A / menu entry 1; true is player B / menu entry 2. -/
abbrev BargainAStrategy := Bool × (Bool → Bool → Bool)
abbrev BargainBStrategy := (Bool → Bool) × (Bool → Bool)
abbrev BargainSourceProfile := BargainAStrategy × BargainBStrategy

def BargainStrategy : Bool → Type
  | false => BargainAStrategy
  | true => BargainBStrategy

instance bargainStrategyFintype (i : Bool) : Fintype (BargainStrategy i) := by
  cases i <;> infer_instance

instance bargainStrategyDecidableEq (i : Bool) : DecidableEq (BargainStrategy i) := by
  cases i <;> infer_instance

abbrev BargainTargetProfile := ∀ i : Bool, BargainStrategy i

def bargainProfileEquiv : BargainSourceProfile ≃ BargainTargetProfile where
  toFun s := fun
    | false => s.1
    | true => s.2
  invFun σ := (σ false, σ true)
  left_inv s := by cases s; rfl
  right_inv σ := by
    funext i
    cases i <;> rfl

def bargainSourceUpdate (s : BargainSourceProfile) :
    (i : Bool) → BargainStrategy i → BargainSourceProfile
  | false, τ => (τ, s.2)
  | true, τ => (s.1, τ)

theorem bargainProfileEquiv_update
    (s : BargainSourceProfile) (i : Bool) (τ : BargainStrategy i) :
    bargainProfileEquiv (bargainSourceUpdate s i τ) =
      Function.update (bargainProfileEquiv s) i τ := by
  funext j
  cases i <;> cases j <;>
    simp [bargainProfileEquiv, bargainSourceUpdate, Function.update]

def bargainSourceDeviation
    (i : Bool) (s t : BargainSourceProfile) : Prop :=
  ∃ τ : BargainStrategy i, t = bargainSourceUpdate s i τ

def bargainTargetDeviation
    (i : Bool) (σ ρ : BargainTargetProfile) : Prop :=
  ∃ τ : BargainStrategy i, ρ = Function.update σ i τ

theorem bargain_allowedDeviation_iff
    (i : Bool) (s t : BargainSourceProfile) :
    bargainTargetDeviation i (bargainProfileEquiv s) (bargainProfileEquiv t) ↔
      bargainSourceDeviation i s t := by
  constructor
  · rintro ⟨τ, hτ⟩
    refine ⟨τ, ?_⟩
    apply bargainProfileEquiv.injective
    exact hτ.trans (bargainProfileEquiv_update s i τ).symm
  · rintro ⟨τ, rfl⟩
    exact ⟨τ, bargainProfileEquiv_update s i τ⟩

inductive BargainTerminal where
  | accept0 (first : Bool)
  | accept1 (first second : Bool)
  | failure (first second : Bool)
  deriving DecidableEq, Fintype

inductive BargainHistory where
  | root
  | offered0 (first : Bool)
  | rejected0 (first : Bool)
  | offered1 (first second : Bool)
  | terminal (z : BargainTerminal)
  deriving DecidableEq, Fintype

def bargainActor : BargainHistory → Option Bool
  | .root => some false
  | .offered0 _ => some true
  | .rejected0 _ => some true
  | .offered1 _ _ => some false
  | .terminal _ => none

def BargainAction : BargainHistory → Type
  | .root => Bool
  | .offered0 _ => Bool
  | .rejected0 _ => Bool
  | .offered1 _ _ => Bool
  | .terminal _ => PEmpty

def bargainStep : (h : BargainHistory) → BargainAction h → BargainHistory
  | .root, q => .offered0 q
  | .offered0 q, accept =>
      if accept then .terminal (.accept0 q) else .rejected0 q
  | .rejected0 q, r => .offered1 q r
  | .offered1 q r, accept =>
      if accept then .terminal (.accept1 q r) else .terminal (.failure q r)
  | .terminal _, a => nomatch a

/- The policy specifies an action at every nonterminal history, including off-path ones. -/
def bargainMove (s : BargainSourceProfile) : BargainHistory → Option Bool
  | .root => some s.1.1
  | .offered0 q => some (s.2.1 q)
  | .rejected0 q => some (s.2.2 q)
  | .offered1 q r => some (s.1.2 q r)
  | .terminal _ => none

def bargainTargetMove (σ : BargainTargetProfile) : BargainHistory → Option Bool
  | .root => some (σ false).1
  | .offered0 q => some ((σ true).1 q)
  | .rejected0 q => some ((σ true).2 q)
  | .offered1 q r => some ((σ false).2 q r)
  | .terminal _ => none

theorem bargain_actions_preserved (s : BargainSourceProfile) (h : BargainHistory) :
    bargainTargetMove (bargainProfileEquiv s) h = bargainMove s h := by
  cases h <;> rfl

def bargainRun (s : BargainSourceProfile) : BargainTerminal :=
  let q := s.1.1
  if s.2.1 q then .accept0 q
  else
    let r := s.2.2 q
    if s.1.2 q r then .accept1 q r else .failure q r

def bargainTargetRun (σ : BargainTargetProfile) : BargainTerminal :=
  let q := (σ false).1
  if (σ true).1 q then .accept0 q
  else
    let r := (σ true).2 q
    if (σ false).2 q r then .accept1 q r else .failure q r

def bargainTrace (s : BargainSourceProfile) : List BargainHistory :=
  let q := s.1.1
  if s.2.1 q then
    [.root, bargainStep .root q, bargainStep (.offered0 q) true]
  else
    let r := s.2.2 q
    [.root, bargainStep .root q, bargainStep (.offered0 q) false,
      bargainStep (.rejected0 q) r, bargainStep (.offered1 q r) (s.1.2 q r)]

def bargainTargetTrace (σ : BargainTargetProfile) : List BargainHistory :=
  bargainTrace (σ false, σ true)

theorem bargain_trace_terminal (s : BargainSourceProfile) :
    (bargainTrace s).getLast? = some (.terminal (bargainRun s)) := by
  cases hb : s.2.1 s.1.1
  · cases ha : s.1.2 s.1.1 (s.2.2 s.1.1) <;>
      simp [bargainTrace, bargainRun, bargainStep, hb, ha]
  · simp [bargainTrace, bargainRun, bargainStep, hb]

theorem bargain_trace_preserved (s : BargainSourceProfile) :
    bargainTargetTrace (bargainProfileEquiv s) = bargainTrace s := rfl

/- This specific synthetic tree is public and fully observed by construction. -/
def bargainPublicHistory (h : BargainHistory) : BargainHistory := h

theorem bargain_perfect_information (h k : BargainHistory) :
    bargainPublicHistory h = bargainPublicHistory k ↔ h = k := Iff.rfl

theorem bargain_publicInfo_preserved (s : BargainSourceProfile) :
    (bargainTargetTrace (bargainProfileEquiv s)).map bargainPublicHistory =
      (bargainTrace s).map bargainPublicHistory := rfl

noncomputable def bargainTreeKernel (s : BargainSourceProfile) : PMF BargainTerminal :=
  PMF.pure (bargainRun s)

noncomputable def bargainTargetKernel (σ : BargainTargetProfile) : PMF BargainTerminal :=
  PMF.pure (bargainTargetRun σ)

theorem bargain_deterministic_kernel_preserved (s : BargainSourceProfile) :
    bargainTargetKernel (bargainProfileEquiv s) = bargainTreeKernel s := rfl

def bargainX (q : Bool) : ℚ := if q then bParamsDemo.x2 else bParamsDemo.x1
def bargainY (r : Bool) : ℚ := if r then bParamsDemo.y2 else bParamsDemo.y1

structure BargainTerminalLedger where
  grossA : ℚ
  grossB : ℚ
  delayLossA : ℚ
  delayLossB : ℚ
  failed : Bool
  deriving DecidableEq

/-
The delay losses below are utility-unit opportunity losses implementing this
example's delta. They are not real monetary charges and are not attributed to
an independent pre-existing cost model. Failure has the given outside payoff
zero, hence gross payoff and discount loss zero for both players.
-/
def bargainLedger : BargainTerminal → BargainTerminalLedger
  | .accept0 q =>
      ⟨bParamsDemo.cake - bargainX q, bargainX q, 0, 0, false⟩
  | .accept1 _ r =>
      ⟨bargainY r, bParamsDemo.cake - bargainY r,
        (1 - bParamsDemo.delta) * bargainY r,
        (1 - bParamsDemo.delta) * (bParamsDemo.cake - bargainY r), false⟩
  | .failure _ _ => ⟨0, 0, 0, 0, true⟩

def bargainLedgerPay (z : BargainTerminal) (i : Bool) : ℝ :=
  if i then
    (((bargainLedger z).grossB - (bargainLedger z).delayLossB : ℚ) : ℝ)
  else
    (((bargainLedger z).grossA - (bargainLedger z).delayLossA : ℚ) : ℝ)

theorem bargain_delay_loss_formula (share : ℚ) :
    share - (1 - bParamsDemo.delta) * share = bParamsDemo.delta * share := by
  ring

theorem bargain_ledger_values :
    bargainLedger (.accept0 false) = ⟨60, 40, 0, 0, false⟩ ∧
    bargainLedger (.accept0 true) = ⟨40, 60, 0, 0, false⟩ ∧
    (∀ q, bargainLedger (.accept1 q false) = ⟨20, 80, 10, 40, false⟩) ∧
    (∀ q, bargainLedger (.accept1 q true) = ⟨50, 50, 25, 25, false⟩) ∧
    (∀ q r, bargainLedger (.failure q r) = ⟨0, 0, 0, 0, true⟩) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · norm_num [bargainLedger, bargainX, bParamsDemo]
  · norm_num [bargainLedger, bargainX, bParamsDemo]
  · intro q
    norm_num [bargainLedger, bargainY, bParamsDemo]
  · intro q
    norm_num [bargainLedger, bargainY, bParamsDemo]
  · intro q r
    rfl

/- The abstract terminal utility is read from the existing W4 payoff functions. -/
def bargainAbstractTerminalPayQ : BargainTerminal → Bool → ℚ
  | .accept0 q, false => (r0Pay bParamsDemo (bargainX q)).1
  | .accept0 q, true => (r0Pay bParamsDemo (bargainX q)).2
  | .accept1 _ r, false => (r1Pay bParamsDemo (bargainY r)).1
  | .accept1 _ r, true => (r1Pay bParamsDemo (bargainY r)).2
  | .failure _ _, _ => 0

def bargainAbstractTerminalPay (z : BargainTerminal) (i : Bool) : ℝ :=
  (bargainAbstractTerminalPayQ z i : ℝ)

theorem bargain_ledger_payoff_eq (z : BargainTerminal) (i : Bool) :
    bargainLedgerPay z i = bargainAbstractTerminalPay z i := by
  cases z with
  | accept0 q =>
      cases q <;> cases i <;>
        norm_num [bargainLedgerPay, bargainLedger, bargainAbstractTerminalPay,
          bargainAbstractTerminalPayQ, bargainX, bargainY, bParamsDemo,
          r0Pay, accR0, biR1, b1Choice, r1Pay, accR1]
  | accept1 q r =>
      cases r <;> cases i <;>
        norm_num [bargainLedgerPay, bargainLedger, bargainAbstractTerminalPay,
          bargainAbstractTerminalPayQ, bargainX, bargainY, bParamsDemo,
          r1Pay, accR1]
  | failure q r =>
      cases i <;>
        norm_num [bargainLedgerPay, bargainLedger, bargainAbstractTerminalPay,
          bargainAbstractTerminalPayQ]

def bargainConcretePayoff (i : Bool) (s : BargainSourceProfile) : ℝ :=
  bargainLedgerPay (bargainRun s) i

theorem bargain_profile_payoff_eq (s : BargainSourceProfile) (i : Bool) :
    bargainConcretePayoff i s =
      bargainAbstractTerminalPay (bargainTargetRun (bargainProfileEquiv s)) i := by
  change bargainLedgerPay (bargainRun s) i =
    bargainAbstractTerminalPay (bargainRun s) i
  exact bargain_ledger_payoff_eq _ _

/- Both are actual KernelGame instances with dependent complete-strategy carriers. -/
noncomputable def bargain_treeGame : GameTheory.KernelGame Bool where
  Strategy := BargainStrategy
  Outcome := BargainTerminal
  utility := bargainLedgerPay
  outcomeKernel := fun σ => bargainTreeKernel (σ false, σ true)

noncomputable def bargain_abstractGame : GameTheory.KernelGame Bool where
  Strategy := BargainStrategy
  Outcome := BargainTerminal
  utility := bargainAbstractTerminalPay
  outcomeKernel := bargainTargetKernel

theorem bargain_games_eq : bargain_treeGame = bargain_abstractGame := by
  have hu : bargainLedgerPay = bargainAbstractTerminalPay := by
    funext z i
    exact bargain_ledger_payoff_eq z i
  unfold bargain_treeGame bargain_abstractGame
  rw [hu]
  rfl

theorem bargain_treeGame_eu (σ : BargainTargetProfile) (i : Bool) :
    bargain_treeGame.eu σ i = bargainConcretePayoff i (σ false, σ true) := by
  change Math.Probability.expect
      (PMF.pure (bargainRun (σ false, σ true)))
      (fun z => bargainLedgerPay z i) = _
  simp only [Math.Probability.expect_pure, bargainConcretePayoff]

theorem bargain_abstractGame_eu (σ : BargainTargetProfile) (i : Bool) :
    bargain_abstractGame.eu σ i =
      bargainAbstractTerminalPay (bargainTargetRun σ) i := by
  change Math.Probability.expect (PMF.pure (bargainTargetRun σ))
      (fun z => bargainAbstractTerminalPay z i) = _
  simp only [Math.Probability.expect_pure]

def bargainBIProfile : BargainSourceProfile :=
  ((false, fun _ _ => true), (fun _ => true, fun _ => false))

theorem bargain_bi_profile_payoff :
    bargainRun bargainBIProfile = .accept0 false ∧
    (bargainConcretePayoff false bargainBIProfile,
      bargainConcretePayoff true bargainBIProfile) =
      (((biOutcome bParamsDemo).1 : ℝ), ((biOutcome bParamsDemo).2 : ℝ)) := by
  constructor
  · rfl
  · rw [witness_bargain_bi.2]
    norm_num [bargainConcretePayoff, bargainBIProfile, bargainRun,
      bargainLedgerPay, bargainLedger, bargainX, bParamsDemo]

/-
These are all complete unilateral strategies, not merely one-step changes.
The fixed menus have root offers 40/60 and B's actual delayed continuation 40.
No general claim about accR0 or the external T113 statement is inferred.
-/
theorem bargain_bi_all_deviations_nonpositive
    (i : Bool) (τ : BargainStrategy i) :
    bargainConcretePayoff i (bargainSourceUpdate bargainBIProfile i τ) -
      bargainConcretePayoff i bargainBIProfile ≤ 0 := by
  cases i with
  | false =>
      cases hq : τ.1 <;>
        norm_num [bargainConcretePayoff, bargainSourceUpdate,
          bargainBIProfile, bargainRun, bargainLedgerPay, bargainLedger,
          bargainX, bargainY, bParamsDemo, hq]
  | true =>
      cases hr : τ.1 false <;> cases hq : τ.2 false <;>
        norm_num [bargainConcretePayoff, bargainSourceUpdate,
          bargainBIProfile, bargainRun, bargainLedgerPay, bargainLedger,
          bargainX, bargainY, bParamsDemo, hr, hq]

/- Requires equiv_deviation_equilibrium_transfer from the preceding core draft. -/
theorem bargain_equilibrium_transfer_instance :
    ∀ i ρ,
      bargainTargetDeviation i (bargainProfileEquiv bargainBIProfile) ρ →
        bargain_abstractGame.eu ρ i -
          bargain_abstractGame.eu (bargainProfileEquiv bargainBIProfile) i ≤ 0 := by
  have transfer := equiv_deviation_equilibrium_transfer
    (e := bargainProfileEquiv)
    (u := fun i σ => bargainAbstractTerminalPay (bargainTargetRun σ) i)
    (v := bargainConcretePayoff)
    (sourceDeviation := bargainSourceDeviation)
    (targetDeviation := bargainTargetDeviation)
    (chosen := bargainBIProfile)
    (ε := fun _ => 0) (η := fun _ => 0)
    (deviationCorrespondence := bargain_allowedDeviation_iff)
    (disturbance := by
      intro i s
      rw [← bargain_profile_payoff_eq s i]
      norm_num)
    (approximate := by
      rintro i t ⟨τ, rfl⟩
      exact bargain_bi_all_deviations_nonpositive i τ)
  intro i ρ hρ
  simpa only [bargain_abstractGame_eu, mul_zero, add_zero]
    using transfer i ρ hρ

/-
Actual mixed KernelGame transfer for this instance. Only the source approximate
equilibrium is an input. Structural/game equality supplies the zero disturbance;
the target equilibrium or any structural preservation is not assumed.
-/
theorem bargain_mixed_transfer_instance
    (chosen : ∀ i : Bool, PMF (BargainStrategy i)) (ε : Bool → ℝ)
    (approximate :
      ∀ i (τ : PMF (BargainStrategy i)),
        bargain_treeGame.mixedExtension.eu (Function.update chosen i τ) i -
          bargain_treeGame.mixedExtension.eu chosen i ≤ ε i) :
    ∀ i (τ : PMF (BargainStrategy i)),
      bargain_abstractGame.mixedExtension.eu (Function.update chosen i τ) i -
        bargain_abstractGame.mixedExtension.eu chosen i ≤ ε i := by
  have transfer :=
    JurisLean.Candidates.Final20261021.Decision.u06_2_approx_equilibrium_transfer
      (u := fun i σ => bargain_abstractGame.mixedExtension.eu σ i)
      (v := fun i σ => bargain_treeGame.mixedExtension.eu σ i)
      (deviation := fun i σ ρ =>
        ∃ τ : PMF (BargainStrategy i), ρ = Function.update σ i τ)
      (chosen := chosen) (ε := ε) (η := fun _ => 0)
      (disturbance := by
        intro i σ
        rw [bargain_games_eq]
        norm_num)
      (approximate := by
        rintro i ρ ⟨τ, rfl⟩
        exact approximate i τ)
  intro i τ
  simpa only [mul_zero, add_zero] using
    transfer i (Function.update chosen i τ) ⟨τ, rfl⟩

end JurisLean.Candidates.U06_2EquilibriumTransfer20261030

#check JurisLean.Candidates.U06_2EquilibriumTransfer20261030.finite_expect_disturbance
#print axioms JurisLean.Candidates.U06_2EquilibriumTransfer20261030.finite_expect_disturbance
#check JurisLean.Candidates.U06_2EquilibriumTransfer20261030.finite_expect_affine
#print axioms JurisLean.Candidates.U06_2EquilibriumTransfer20261030.finite_expect_affine
#check JurisLean.Candidates.U06_2EquilibriumTransfer20261030.finite_expect_positiveAffine_preference
#print axioms JurisLean.Candidates.U06_2EquilibriumTransfer20261030.finite_expect_positiveAffine_preference
#check JurisLean.Candidates.U06_2EquilibriumTransfer20261030.product_pmf_equilibrium_transfer
#print axioms JurisLean.Candidates.U06_2EquilibriumTransfer20261030.product_pmf_equilibrium_transfer
#check JurisLean.Candidates.U06_2EquilibriumTransfer20261030.equiv_deviation_equilibrium_transfer
#print axioms JurisLean.Candidates.U06_2EquilibriumTransfer20261030.equiv_deviation_equilibrium_transfer
#check JurisLean.Candidates.U06_2EquilibriumTransfer20261030.legalGame_mixedExtension_expect
#print axioms JurisLean.Candidates.U06_2EquilibriumTransfer20261030.legalGame_mixedExtension_expect
#check JurisLean.Candidates.U06_2EquilibriumTransfer20261030.legalGame_mixed_equilibrium_transfer
#print axioms JurisLean.Candidates.U06_2EquilibriumTransfer20261030.legalGame_mixed_equilibrium_transfer
#check JurisLean.Candidates.U06_2EquilibriumTransfer20261030.legalGame_mixedExtension_affine
#print axioms JurisLean.Candidates.U06_2EquilibriumTransfer20261030.legalGame_mixedExtension_affine
#check JurisLean.Candidates.U06_2EquilibriumTransfer20261030.legalGame_positiveAffine_bestResponse
#print axioms JurisLean.Candidates.U06_2EquilibriumTransfer20261030.legalGame_positiveAffine_bestResponse
#check JurisLean.Candidates.U06_2EquilibriumTransfer20261030.added_action_counterexample
#print axioms JurisLean.Candidates.U06_2EquilibriumTransfer20261030.added_action_counterexample
#check JurisLean.Candidates.U06_2EquilibriumTransfer20261030.strictMono_expected_preference_reversal
#print axioms JurisLean.Candidates.U06_2EquilibriumTransfer20261030.strictMono_expected_preference_reversal
#check JurisLean.Candidates.Final20261021.Decision.u06_2_approx_equilibrium_transfer
#print axioms JurisLean.Candidates.Final20261021.Decision.u06_2_approx_equilibrium_transfer
#check JurisLean.Seams.UnifiedEquilExist.legalGame_mixedExtension_eu
#print axioms JurisLean.Seams.UnifiedEquilExist.legalGame_mixedExtension_eu
#check JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargainProfileEquiv_update
#print axioms JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargainProfileEquiv_update
#check JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_allowedDeviation_iff
#print axioms JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_allowedDeviation_iff
#check JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_actions_preserved
#print axioms JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_actions_preserved
#check JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_trace_terminal
#print axioms JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_trace_terminal
#check JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_trace_preserved
#print axioms JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_trace_preserved
#check JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_perfect_information
#print axioms JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_perfect_information
#check JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_publicInfo_preserved
#print axioms JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_publicInfo_preserved
#check JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_deterministic_kernel_preserved
#print axioms JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_deterministic_kernel_preserved
#check JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_delay_loss_formula
#print axioms JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_delay_loss_formula
#check JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_ledger_values
#print axioms JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_ledger_values
#check JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_ledger_payoff_eq
#print axioms JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_ledger_payoff_eq
#check JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_profile_payoff_eq
#print axioms JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_profile_payoff_eq
#check JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_games_eq
#print axioms JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_games_eq
#check JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_treeGame_eu
#print axioms JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_treeGame_eu
#check JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_abstractGame_eu
#print axioms JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_abstractGame_eu
#check JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_bi_profile_payoff
#print axioms JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_bi_profile_payoff
#check JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_bi_all_deviations_nonpositive
#print axioms JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_bi_all_deviations_nonpositive
#check JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_equilibrium_transfer_instance
#print axioms JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_equilibrium_transfer_instance
#check JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_mixed_transfer_instance
#print axioms JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_mixed_transfer_instance
