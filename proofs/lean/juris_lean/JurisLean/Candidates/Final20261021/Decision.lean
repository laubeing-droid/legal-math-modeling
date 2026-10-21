import JurisLean.Candidates.Final20261021.Interfaces
import JurisLean.Candidates.Final20261021.Probability

namespace JurisLean.Candidates.Final20261021.Decision
open Probability

variable {A : Type}

def best (score : A → ℚ) : List A → Option A
  | [] => none
  | a :: rest => match best score rest with
    | none => some a
    | some b => if score a ≤ score b then some b else some a

theorem best_none (score : A → ℚ) (options : List A) :
    best score options = none ↔ options = [] := by
  cases options with
  | nil => simp [best]
  | cons a rest =>
    simp only [best, List.cons_ne_nil, iff_false]
    cases h : best score rest <;> simp
    split <;> simp

theorem best_mem (score : A → ℚ) {options : List A} {a : A}
    (selected : best score options = some a) : a ∈ options := by
  induction options generalizing a with
  | nil => simp [best] at selected
  | cons x xs ih =>
    simp only [best] at selected
    cases hb : best score xs with
    | none => simp [hb] at selected; subst a; simp
    | some b =>
      simp only [hb] at selected
      split at selected
      · cases selected; exact List.mem_cons_of_mem _ (ih hb)
      · cases selected; simp

theorem best_dominates (score : A → ℚ) {options : List A} {a : A}
    (selected : best score options = some a) : ∀ b ∈ options, score b ≤ score a := by
  induction options generalizing a with
  | nil => simp [best] at selected
  | cons x xs ih =>
    simp only [best] at selected
    cases hb : best score xs with
    | none =>
      have hx := (best_none score xs).mp hb
      subst xs
      simp [best] at selected
      subst a
      simp
    | some winner =>
      simp only [hb] at selected
      have hw := ih hb
      split at selected
      · cases selected
        intro b hm
        rcases List.mem_cons.mp hm with he | he
        · subst b; assumption
        · exact hw b he
      · cases selected
        intro b hm
        rcases List.mem_cons.mp hm with he | he
        · subst b; exact le_rfl
        · exact le_trans (hw b he) (le_of_not_ge (by assumption))

def legalBest (score : A → ℚ) (permitted : A → Bool) (options : List A) : Option A :=
  best score (options.filter permitted)

theorem legal_best_sound (score : A → ℚ) (permitted : A → Bool)
    (options : List A) (a : A) (selected : legalBest score permitted options = some a) :
    a ∈ options ∧ permitted a = true ∧
      ∀ b ∈ options, permitted b = true → score b ≤ score a := by
  have hm := List.mem_filter.mp (best_mem score selected)
  refine ⟨hm.1, hm.2, ?_⟩
  intro b hb hp
  exact best_dominates score selected b (List.mem_filter.mpr ⟨hb,hp⟩)

inductive ExactExpr where
  | rational (q : ℚ)
  | add (a b : ExactExpr)
  | mul (a b : ExactExpr)
  deriving DecidableEq, Repr

def evalExact : ExactExpr → ℚ
  | .rational q => q
  | .add a b => evalExact a + evalExact b
  | .mul a b => evalExact a * evalExact b

inductive Evaluates : ExactExpr → ℚ → Prop where
  | rational (q : ℚ) : Evaluates (.rational q) q
  | add {a b : ExactExpr} {x y : ℚ} :
      Evaluates a x → Evaluates b y → Evaluates (.add a b) (x+y)
  | mul {a b : ExactExpr} {x y : ℚ} :
      Evaluates a x → Evaluates b y → Evaluates (.mul a b) (x*y)

theorem u06_3_eval_exists (e : ExactExpr) : Evaluates e (evalExact e) := by
  induction e with
  | rational q => exact .rational q
  | add a b ha hb => exact .add ha hb
  | mul a b ha hb => exact .mul ha hb

theorem u06_3_eval_unique {e : ExactExpr} {q : ℚ} (h : Evaluates e q) : q = evalExact e := by
  induction h with
  | rational q => rfl
  | add ha hb iha ihb => simp [evalExact, iha, ihb]
  | mul ha hb iha ihb => simp [evalExact, iha, ihb]

structure TypedValue where
  expr : ExactExpr
  -- none means a dimensionless coefficient, never a money amount.
  dimension : Option AmountTag
  deriving DecidableEq, Repr

def addValues (a b : TypedValue) : Result TypedValue :=
  if a.dimension = b.dimension then .known ⟨.add a.expr b.expr, a.dimension⟩
  else .rejected .mixedCurrency

def mulValues (a b : TypedValue) : Result TypedValue :=
  match a.dimension, b.dimension with
  | some _, some _ => .rejected .unsupported
  | none, d => .known ⟨.mul a.expr b.expr, d⟩
  | d, none => .known ⟨.mul a.expr b.expr, d⟩

def ledgerAmount (a : Amount) : TypedValue := ⟨.rational a.value, some a.tag⟩

theorem exact_ledger_bridge (a : Amount) : evalExact (ledgerAmount a).expr = a.value := rfl

theorem half_not_truncated : evalExact (.rational (1/2)) = (1/2 : ℚ) ∧
    evalExact (.rational (1/2)) ≠ (0 : ℚ) := by norm_num [evalExact]

structure OutcomeValue where
  probability : ℚ
  payoff : TypedValue
  cashIds : List EventId
  deriving DecidableEq, Repr

structure Alternative where
  id : Nat
  conditions : List SourceRef
  causalBridge : Option SourceRef
  outcomes : List OutcomeValue
  cost : Amount
  execution : List PaymentPayload
  deriving DecidableEq, Repr

structure DecisionIR where
  gamma : Gamma
  action : Alternative
  expectedNet : Amount
  expectedUtility : ℚ
  probabilityOfLoss : ℚ
  utilityVersion : Nat
  riskLimit : ℚ
  informationCutoff : Instant
  deriving DecidableEq, Repr

def evaluate (g : Gamma) (utility : ℚ → ℚ) (utilityVersion : Nat)
    (riskLimit : ℚ) (a : Alternative) : Result DecisionIR :=
  if a.causalBridge.isNone then .unknown .notIdentified
  else if a.outcomes.any (fun o => decide (o.probability < 0)) ∨
      (a.outcomes.map (·.probability)).sum ≠ 1 then .rejected .unsupported
  else if a.outcomes.any (fun o => decide (o.payoff.dimension ≠ some a.cost.tag)) then
    .rejected .mixedCurrency
  else if a.outcomes.any (fun o => decide (¬ o.cashIds.Nodup)) then .rejected .duplicateCash
  else if a.execution.any (fun p => decide (p.caseId ≠ g.caseId ∨
    p.caseRevision ≠ g.caseRevision ∨ p.amount.tag ≠ a.cost.tag)) then .rejected .scopeMismatch
  else
    let net := (a.outcomes.map fun o => o.probability * evalExact o.payoff.expr).sum - a.cost.value
    let eu := (a.outcomes.map fun o =>
      o.probability * utility (evalExact o.payoff.expr - a.cost.value)).sum
    let risk := (a.outcomes.map fun o =>
      if evalExact o.payoff.expr - a.cost.value < 0 then o.probability else 0).sum
    .known ⟨g, a, ⟨net, a.cost.tag⟩, eu, risk, utilityVersion, riskLimit, g.knowledgeCutoff⟩

def proposed_feasible_policy (allowed : List Nat) (values : List DecisionIR) : List DecisionIR :=
  values.filter fun v => decide (v.action.id ∈ allowed ∧ v.probabilityOfLoss ≤ v.riskLimit)

def proposed_decision (allowed : List Nat) (values : List DecisionIR) : Option DecisionIR :=
  best (·.expectedUtility) (proposed_feasible_policy allowed values)

theorem u06_3_decision_respects_allowed (allowed : List Nat) (values : List DecisionIR)
    (selected : DecisionIR) (h : proposed_decision allowed values = some selected) :
    selected.action.id ∈ allowed ∧ selected.probabilityOfLoss ≤ selected.riskLimit := by
  have hm := best_mem (fun x : DecisionIR => x.expectedUtility) h
  have hp := (List.mem_filter.mp hm).2
  simpa only [decide_eq_true_eq] using hp

def net (q b l k : ℝ) : ℝ := q*b + (1-q)*l - k

theorem u06_4_threshold_increasing (q b l k target : ℝ) (h : l < b) :
    target ≤ net q b l k ↔ (target+k-l)/(b-l) ≤ q := by
  rw [div_le_iff₀ (sub_pos.mpr h)]
  unfold net
  constructor <;> intro hx <;> nlinarith

theorem u06_4_threshold_decreasing (q b l k target : ℝ) (h : b < l) :
    target ≤ net q b l k ↔ q ≤ (target+k-l)/(b-l) := by
  rw [le_div_iff_of_neg (sub_neg.mpr h)]
  unfold net
  constructor <;> intro hx <;> nlinarith

theorem u06_4_threshold_equal (q l k target : ℝ) :
    target ≤ net q l l k ↔ target ≤ l-k := by unfold net; ring_nf

theorem u06_2_approx_equilibrium_transfer {Player Profile : Type}
    (u v : Player → Profile → ℝ) (deviation : Player → Profile → Profile → Prop)
    (chosen : Profile) (ε η : Player → ℝ)
    (disturbance : ∀ i a, |u i a - v i a| ≤ η i)
    (approximate : ∀ i a, deviation i chosen a → v i a - v i chosen ≤ ε i) :
    ∀ i a, deviation i chosen a → u i a - u i chosen ≤ ε i + 2 * η i := by
  intro i a allowed
  have hd := (abs_le.mp (disturbance i a)).2
  have hh := (abs_le.mp (disturbance i chosen)).1
  have he := approximate i a allowed
  linarith

def policyScore {Ω A Y : Type} [Fintype Ω] (P : Probability.FiniteLaw Ω)
    (observation : Ω → Y) (utility : A → Ω → ℚ) (policy : Y → A) : ℚ :=
  Probability.expectation P (fun w => utility (policy (observation w)) w)

theorem u06_1_value_of_free_information {Ω A Y : Type} [Fintype Ω]
    (P : Probability.FiniteLaw Ω) (observation : Ω → Y) (utility : A → Ω → ℚ)
    (actions : List A) (policies : List (Y → A)) (old : A)
    (chosen : Y → A) (oracle : Ω → A)
    (ignore : (fun _ : Y => old) ∈ policies)
    (feasible : ∀ pi ∈ policies, ∀ y, pi y ∈ actions)
    (signalChoice : best (policyScore P observation utility) policies = some chosen)
    (perfectChoice : ∀ w, best (fun a => utility a w) actions = some (oracle w)) :
    Probability.expectation P (utility old) ≤ policyScore P observation utility chosen ∧
    policyScore P observation utility chosen ≤ Probability.expectation P (fun w => utility (oracle w) w) := by
  constructor
  · exact best_dominates (policyScore P observation utility) signalChoice _ ignore
  · have hm := best_mem (policyScore P observation utility) signalChoice
    apply Probability.expectation_mono
    intro w
    exact best_dominates (fun a => utility a w) (perfectChoice w) _
      (feasible chosen hm (observation w))

end JurisLean.Candidates.Final20261021.Decision
