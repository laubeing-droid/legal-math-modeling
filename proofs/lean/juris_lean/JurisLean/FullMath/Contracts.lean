import JurisLean.FullMath.Tranche1
import JurisLean.FullMath.Tranche2
import JurisLean.FullMath.Tranche3
import JurisLean.FullMath.Tranche4
import JurisLean.FullMath.Tranche5
import JurisLean.FullMath.Tranche6
import JurisLean.FullMath.Tranche7

/-! Generated from the module signatures: each contract is the real
statement of its mapped theorem. This file contains no proofs. -/

open JurisLean.FullMath.Core
open JurisLean.FullMath.Logic
open JurisLean.FullMath.Evidence
open JurisLean.FullMath.Probability
open JurisLean.FullMath.Numeric
open JurisLean.FullMath.Burden
open JurisLean.FullMath.Action
open JurisLean.FullMath.Composition
open JurisLean.FullMath.Representation
open JurisLean.FullMath.Causal
open JurisLean.FullMath.Document
open JurisLean.FullMath.Roots
open JurisLean.FullMath.Gaps
open JurisLean.FullMath.Numeric.Iv

namespace JurisLean.FullMath.Contracts

def root_GENERIC_FINITE : Prop := ∀ {A : Type} [DecidableEq A] [Fintype A]
    (pred : A → Bool) (out : Finset A)
    (hcert : Representation.checkExact pred out = true), (↑out : Set A) = {x | pred x = true}

def root_SYMBOLIC_EXACT : Prop := ∀ (d : ℕ) (b : Box d), ModeCorrect (Asgn d) (Box d) boxDen b (boxDen b) .exact

def root_STATISTICAL_COMPOSITION : Prop := ∀ {Ω : Type} (P : Set Ω → ℚ)
    (events : List (Set Ω)) (budgets : List ℚ)
    (hlen : events.length = budgets.length)
    (hsub : ∀ e f : Set Ω, P (e ∪ f) ≤ P e + P f)
    (hempty : P ∅ = 0)
    (hch : ∀ i (_hi : i < events.length), P events[i]! ≤ budgets[i]!), P (events.foldr (· ∪ ·) ∅) ≤ budgets.sum

def root_CIVIL : Prop := ∀ (c : CivilClaim), CivilConserved c

def root_CRIMINAL : Prop := ∀ {Person : Type} (cc : CriminalCase Person)
    (convicted : Person → Prop)
    (hrule : ∀ p, convicted p → cc.elements p ≠ [] ∧ cc.evidenceLawful p ∧ cc.standardMet p), ∀ p, convicted p → cc.elements p ≠ [] ∧ cc.evidenceLawful p ∧ cc.standardMet p

def root_ADMINISTRATIVE : Prop := ∀ (ac : AdminCase)
    (enforceable : Prop)
    (hrule : enforceable → ac.authorityHeld ∧ ac.dutyImposed ∧ ac.procedureFollowed), enforceable → ac.authorityHeld ∧ ac.dutyImposed ∧ ac.procedureFollowed

def root_DOCUMENT_DELIVERY : Prop := ∀ (cs : List Char)
    (hplain : Document.Plain cs), Document.parseL (Document.renderL cs) = some (cs, [])

def target_F01 : Prop := ∀ (I : Env) (w : Witness), Phi I w ↔ (PhiF I w ∧ PhiN I w ∧ PhiB I w ∧ PhiQ I w ∧ PhiP I w ∧ PhiA I w ∧ I.gamma w)

def target_F02 : Prop := ∀ (c : CompId) (s : String), (migrate c s).domain = c.domain ∧ (migrate c s).model = c.model ∧ (migrate c s).scenario = c.scenario ∧ (migrate c s).semScope = s

def target_F03 : Prop := ∀ (a b : CompId) (h : composable a b = true), a.domain = b.domain ∧ a.issue = b.issue ∧ a.stage = b.stage ∧ a.version = b.version ∧ a.model = b.model ∧ a.scenario = b.scenario ∧ a.semScope = b.semScope

def target_F04 : Prop := ∀ (d : Deriv), ∀ a, Deriv.origin a ∈ d.subtrees → a ∈ d.deps

def target_F05 : Prop := ∀ {A : Type} [DecidableEq A] [Fintype A] (R : Finset (Finset A × A)) (F : Finset A), ∀ n m, m ≤ n → cl R F m ⊆ cl R F n

def target_F06 : Prop := ∀ {A : Type} [DecidableEq A] (facts : List A) (rules : List (Rul A)), ∀ d a, WellFormed facts rules a → Arg.height a ≤ d → a ∈ Generate facts rules d

def target_F07 : Prop := ∃ a b, a ∈ Generate [0] cyclicRules 0 ∧ b ∈ Generate [0] cyclicRules 2 ∧ Arg.concl a = Arg.concl b ∧ Arg.height a ≠ Arg.height b

def target_F08 : Prop := ∀ {A : Type} [DecidableEq A] (con : Contrary A) (rc : RuleContra A) (a : Arg A), ∀ (k : ℕ) (b : Arg A), Arg.height b ≤ k → (edgeFuel con rc a b k = true ↔ Defeat A con rc a b)

def target_F09 : Prop := ∀ {A : Type} [DecidableEq A] (edges : List (Arg A × Arg A))
    (policy : Arg A → Arg A → Option Bool), (pendingEdges edges policy).length ≤ edges.length

def target_F10 : Prop := ∀ {A : Type} [DecidableEq A] [Fintype A] (af : AF A) (P : Finset A) (hP : charF af P = P), grounded af ⊆ P

def target_F11 : Prop := ∀ {A : Type} [DecidableEq A] [Fintype A], evalUniversal (A := A) .incomplete = .unknown

def target_F12 : Prop := ∀ (a : Admission)
    (h : a.status = FactStatus.verified), ∃ source authority, a = Admission.verifiedPremise source authority

def target_F13 : Prop := ∀ {A : Type} [DecidableEq A] [Fintype A] (R R' : Finset (Finset A × A)) (hR : R ⊆ R') (F Δ : Finset A), closure R' (F ∪ Δ) = closure R' (closure R F ∪ Δ)

def target_F14 : Prop := ∀ {A : Type} [DecidableEq A] [Fintype A] (R R' : Finset (Finset A × A)) (hR : R ⊆ R')
    (F Δ : Finset A), incrementalUpdate R F (.addOnly Δ R') = closure R' (F ∪ Δ)

def target_P01 : Prop := ∀ {n : ℕ} (c : Chain n), Finset.sum Finset.univ (fun s : State n => joint c s) = 1

def target_P02 : Prop := ∀ {S : Type} [Fintype S] [DecidableEq S] (p : S → ℚ) (hp : ∀ s, 0 ≤ p s) (e : S → Bool)
    (hZ : 0 < evMass p e), ∑ s, posterior p e hZ s = 1

def target_P03 : Prop := ∀ {n : ℕ} (fs gs : List ((Fin n → Bool) → ℚ)) (i : Fin n)
    (h : ∀ f ∈ fs, IndepAt f i) (w : Fin n → Bool), Finset.sum Finset.univ (fun _v : Bool => prodAt (fs ++ gs) (upd w i _v)) = prodAt fs w * Finset.sum Finset.univ (fun v : Bool => prodAt gs (upd w i v))

def target_P04 : Prop := ∀ (o : Obs) (l : List Obs), obsTotal (o :: o :: l) = obsTotal (o :: l)

def target_P05 : Prop := ∀ {k : ℕ} (α n m : Fin k → ℚ), dirWeights (fun i => α i + n i) m = dirWeights α (fun i => n i + m i)

def target_P06 : Prop := ∃ (π : Bool → ℚ) (r1 r2 : ℚ), hyperWeights π (fun b => if b then r1 else r2) true ≠ hyperWeights (fun b => if b then 2 else 1) (fun b => if b then 3 else 5) true

def target_P07 : Prop := ∀ {m : ℕ} (ws ps : Fin m → ℚ) (lo hi : ℚ)
    (hw : ∀ j, 0 ≤ ws j)
    (hw1 : Finset.sum Finset.univ (fun j : Fin m => ws j) = 1)
    (hlo : ∀ j, lo ≤ ps j) (hhi : ∀ j, ps j ≤ hi), lo ≤ mix ws ps ∧ mix ws ps ≤ hi

def target_P08 : Prop := ∀ (eps p q l u : ℝ)
    (he0 : 0 ≤ eps) (he1 : eps ≤ 1)
    (hpl : l ≤ p) (hpu : p ≤ u) (hq0 : 0 ≤ q) (hq1 : q ≤ 1), (1 - eps) * l ≤ (1 - eps) * p + eps * q ∧ (1 - eps) * p + eps * q ≤ (1 - eps) * u + eps

def target_P09 : Prop := ∀ (a b u v r : ℚ)
    (ha : 0 < a) (hb : 0 ≤ b) (hu : 0 ≤ u) (hv : 0 ≤ v) (hr : 0 ≤ r)
    (huv : u + v ≤ r), a / (a + b + r) ≤ (a + u) / (a + b + u + v) ∧ (a + u) / (a + b + u + v) ≤ (a + r) / (a + b + r)

def target_P10 : Prop := ∀ (a1 b1 a2 b2 : ℕ) (w delta : ℚ) (l u : ℚ)
    (hw : 0 ≤ w) (hw1 : w ≤ 1)
    (h1 : 1 - delta ≤ betaMass a1 b1 l u)
    (h2 : 1 - delta ≤ betaMass a2 b2 l u), 1 - delta ≤ w * betaMass a1 b1 l u + (1 - w) * betaMass a2 b2 l u

def target_P11 : Prop := ∀ (data : List Row) (r : Row)
    (h : r ∈ legalRows data), r.featT < r.labelT

def target_P12 : Prop := ∀ (p q : ℝ), expBern p (fun y => (q - (if y then 1 else 0)) ^ 2) - expBern p (fun y => (p - (if y then 1 else 0)) ^ 2) = (q - p) ^ 2

def target_P13 : Prop := ∀ (w1 w2 y1 y2 : ℚ) (hw1 : 0 < w1) (hw2 : 0 < w2)
    (hviol : y2 < y1), ∀ c1 c2 : ℚ, c1 ≤ c2 → w1 * (y1 - c1) ^ 2 + w2 * (y2 - c2) ^ 2 ≥ w1 * (y1 - ((w1 * y1 + w2 * y2) / (w1 + w2))) ^ 2 + w2 * (y2 - ((w1 * y1 + w2 * y2) / (w1 + w2))) ^ 2

def target_E01 : Prop := ∀ (calibrationScore threshold : ℚ)
    (nCalibration minN : ℕ), e01Decide calibrationScore threshold nCalibration minN = .withinDeclaredRisk ↔ (minN ≤ nCalibration ∧ calibrationScore ≤ threshold)

def target_N01 : Prop := ∀ (r : ℚ), covered r - uncovered r = r

def target_N02 : Prop := ∀ (i j : Iv) (x y : ℚ) (hx : mem x i) (hy : mem y j), mem (x * y) (mul i j)

def target_N03 : Prop := ∀ {n : ℕ} (A : Fin n → Fin n → ℚ) (b c : Fin n → ℚ)
    (x lam : Fin n → ℚ)
    (hP : PrimalFeasible A b x) (hD : DualFeasible A b c lam), dualObj b lam ≤ primalObj c x

def target_N04 : Prop := ¬ ∀ d ∈ [0, 20, 30, 100], Iv.mem d ⟨20, 30, by norm_num⟩

def target_N05 : Prop := ∀ {n : ℕ} (A : Fin n → Fin n → ℚ) (b c : Fin n → ℚ)
    (xstar lam : Fin n → ℚ)
    (hPstar : PrimalFeasible A b xstar) (hDstar : DualFeasible A b c lam)
    (heq : primalObj c xstar = dualObj b lam), ∀ x, PrimalFeasible A b x → primalObj c xstar ≤ primalObj c x

def target_N06 : Prop := ∀ (k : KKT1), ∀ x, k.l ≤ x → quad1 k.h k.g k.xstar ≤ quad1 k.h k.g x

def target_N07 : Prop := ∀ (lo k hi : ℤ) (x : ℤ)
    (hx : lo ≤ x ∧ x ≤ hi), (lo ≤ x ∧ x ≤ k) ∨ (k + 1 ≤ x ∧ x ≤ hi)

def target_N08 : Prop := ∀ (l u a b η x y : ℝ) (h : l ≤ u), |T l u a b η x - T l u a b η y| ≤ |1 - η * a| * |x - y|

def target_N09 : Prop := ∀ (l u a b η : ℝ) (ha : 0 < a) (hlu : l ≤ u) (hη : 0 < η), T l u a b η (clip l u (-(b / a))) = clip l u (-(b / a))

def target_N10 : Prop := ∀ (l u a b η : ℝ) (ha : 0 < a)
    (hlu : l ≤ -(b / a)) (hbu : -(b / a) ≤ u), T l u a b η (-(b / a)) = -(b / a)

def target_B01 : Prop := ∀ (p q : String) (hpq : p ≠ q)
    (s : BurdenSlot), resolveList [p, q] s = BurdenState.pending

def target_B02 : Prop := ∀ (g : Gate) (h : terminal g = true), g.stageReady = true ∧ g.assessmentComplete = true ∧ g.authorityValid = true

def target_B03 : Prop := ∀ (std : Standard) (w : Weight), gate std w = FactOutcome.established ↔ std.threshold ≤ w

def target_B04 : Prop := completeAssignment civilSlots civilPolicies

def target_B05 : Prop := completeAssignment criminalSlots criminalPolicies

def target_B06 : Prop := completeAssignment adminSlots adminPolicies

def target_B07 : Prop := ∀ (v v' : SourceVersion)
    (h : cacheKey v ≠ cacheKey v'), cacheHit v v' = false

def target_G01 : Prop := ∀ {S A : Type} [Fintype S] [DecidableEq S] [DecidableEq A] (legal : S → Finset A) (hne : ∀ s, (legal s).Nonempty)
    (r : S → A → ℚ) (p : S → A → S → ℚ) (β : ℚ) (t : ℕ) (s : S) (a : A)
    (ha : a ∈ legal s), qval r p β (vf legal hne r p β t) s a ≤ vf legal hne r p β (t + 1) s

def target_G02 : Prop := ∀ {C : Type} [Fintype C] [DecidableEq C] {K : Type} [Fintype K] [DecidableEq K] (w : C → ℚ) (hw : ∀ c, 0 ≤ w c)
    (u : C → K → ℚ) (arg : C → K) (k₀ : K)
    (hatt : ∀ c k, u c k ≤ u c (arg c)), (∑ c, w c * u c k₀) ≤ ∑ c, w c * u c (arg c)

def target_G03 : Prop := ∀ (legal : Set ℚ) (P D : PartyParams) (s : ℚ)
    (h : s ∈ admissibleSettlements legal P D), s ∈ legal ∧ plaintiffL P ≤ s ∧ s ≤ defendantU D

def target_G04 : Prop := ∀ {T : Type} [Fintype T] [DecidableEq T] (u : T → T → ℚ) (h : dsicCheck u = true), dsicProp u

def target_G05 : Prop := ∀ {Θ : Type} [Nonempty Θ]
    (r₁ r₂ : Θ → ℚ)
    (m₁ : ℚ) (hm₁ : ∀ θ, m₁ ≤ r₁ θ)
    (m₂ : ℚ) (hm₂ : ∀ θ, m₂ ≤ r₂ θ), m₁ + m₂ ≤ r₁ (Classical.arbitrary Θ) + r₂ (Classical.arbitrary Θ)

def target_C01 : Prop := ∀ {X Y Z W : Type} (r : X → Y → Prop) (s : Y → Z → Prop) (t : Z → W → Prop)
    (x : X) (w : W), relComp (relComp r s) t x w ↔ relComp r (relComp s t) x w

def target_C02 : Prop := ∀ {S : Type} (T1 T2 : OuterStep S) (c0 c1 c2 : Set S)
    (h1 : T1.step c0 ⊆ c1) (h2 : T2.step c1 ⊆ c2), T2.step (T1.step c0) ⊆ c2

def target_C03 : Prop := ∀ (p0 p1 : ℚ) (hp0 : 0 ≤ p0) (hp1 : 0 ≤ p1)
    (S0 S1 : Set Bool) (ev : Bool → Bool) (y0 y1 : Bool)
    (hy0 : y0 ∈ S0) (hy1 : y1 ∈ S1), p0 * ind (ev y0) + p1 * ind (ev y1) ≤ p0 * maxInd S0 ev + p1 * maxInd S1 ev

def target_C04 : Prop := ∀ (D C p : ℚ) (hC : 0 ≤ C) (hp : 0 ≤ p) (hp1 : p ≤ 1), (p * (D - C) + (1 - p) * D = D - p * C) ∧ ((1 - p) * 1 + p * 0 = 1 - p) ∧ (D - p * C ≤ D ∧ D ≤ D)

def target_C05 : Prop := ∀ (policy : String) (ids : List ℕ), ∀ r ∈ runChain policy ids, ∃ i ∈ ids, r = CondRuling.conditional i policy

def target_C06 : Prop := ∀ (spec : List ℚ → Bool) (w : List ℚ)
    (h : checkerAccepts spec w = true), w ∈ solutionsOf spec

def target_C07 : Prop := (∀ (computed solutions : Set ℚ)
    (h : allowedClaim .completeMode computed solutions), computed = solutions) ∧ (∀ {A : Type} [DecidableEq A] [Fintype A]
    (pred : A → Bool) (out : Finset A)
    (hcert : Representation.checkExact pred out = true), (↑out : Set A) = {x | pred x = true}) ∧ (∀ (d : ℕ) (b : Box d), ModeCorrect (Asgn d) (Box d) boxDen b (boxDen b) .exact) ∧ (∀ {Ω : Type} (P : Set Ω → ℚ)
    (events : List (Set Ω)) (budgets : List ℚ)
    (hlen : events.length = budgets.length)
    (hsub : ∀ e f : Set Ω, P (e ∪ f) ≤ P e + P f)
    (hempty : P ∅ = 0)
    (hch : ∀ i (_hi : i < events.length), P events[i]! ≤ budgets[i]!), P (events.foldr (· ∪ ·) ∅) ≤ budgets.sum) ∧ (∀ (c : CivilClaim), CivilConserved c) ∧ (∀ {Person : Type} (cc : CriminalCase Person)
    (convicted : Person → Prop)
    (hrule : ∀ p, convicted p → cc.elements p ≠ [] ∧ cc.evidenceLawful p ∧ cc.standardMet p), ∀ p, convicted p → cc.elements p ≠ [] ∧ cc.evidenceLawful p ∧ cc.standardMet p) ∧ (∀ (ac : AdminCase)
    (enforceable : Prop)
    (hrule : enforceable → ac.authorityHeld ∧ ac.dutyImposed ∧ ac.procedureFollowed), enforceable → ac.authorityHeld ∧ ac.dutyImposed ∧ ac.procedureFollowed) ∧ (∀ (cs : List Char)
    (hplain : Document.Plain cs), Document.parseL (Document.renderL cs) = some (cs, []))

def target_EXT01 : Prop := ∀ {W R : Type} (sem : R → Set W)
    (rep : R) (sol : Set W) (m : Mode)
    (h : ModeCorrect W R sem rep sol m), match m with | .exact => sem rep = sol | .inner => sem rep ⊆ sol | .outer => sol ⊆ sem rep

def target_EXT02 : Prop := ∀ (claims : List InputClaim) (c : InputClaim) (i j : CompId)
    (h : carries claims c i) (hcarried : carries claims c j), i = j

def target_EXT03 : Prop := ∀ {A : Type} [DecidableEq A] [Fintype A] (af : AF A), charF af (grounded af) = grounded af

def target_EXT04 : Prop := ∀ {d : ℕ} (b : Box (d + 1)) (k : ℚ) (hk : b.lo 0 ≤ k) (hk2 : k ≤ b.hi 0), boxDen (splitBox b k hk hk2).1 ∪ boxDen (splitBox b k hk hk2).2 = boxDen b

def target_EXT05 : Prop := ∀ (retired : List Assume) (d : Deriv)
    (a : Assume) (ha : a ∈ d.deps) (hr : a ∈ retired), invalidated retired d = true

def target_EXT06 : Prop := ∀ (data : List Row) (r : Row) (hr : r ∈ legalRows data), r ∈ partRows (tagOf r) data

def target_EXT07 : Prop := sSup (Set.Ico (0 : ℝ) 1) = 1 ∧ (1 : ℝ) ∉ Set.Ico (0 : ℝ) 1

def target_EXT08 : Prop := ∀ (θ : Bool), rInd θ + rCon θ = 1

def target_EXT09 : Prop := (∀ (Person : Type)
    (cc : CriminalCase Person) (convicted : Person → Prop)
    (crule : ∀ p, convicted p → cc.elements p ≠ [] ∧ cc.evidenceLawful p ∧ cc.standardMet p)
    (ac : AdminCase) (enforceable : Prop)
    (arule : enforceable → ac.authorityHeld ∧ ac.dutyImposed ∧ ac.procedureFollowed)
    (civil : CivilClaim), (∀ p, convicted p → cc.elements p ≠ [] ∧ cc.evidenceLawful p ∧ cc.standardMet p) ∧ (enforceable → ac.authorityHeld ∧ ac.dutyImposed ∧ ac.procedureFollowed) ∧ CivilConserved civil) ∧ (∀ (c : CivilClaim), CivilConserved c) ∧ (∀ {Person : Type} (cc : CriminalCase Person)
    (convicted : Person → Prop)
    (hrule : ∀ p, convicted p → cc.elements p ≠ [] ∧ cc.evidenceLawful p ∧ cc.standardMet p), ∀ p, convicted p → cc.elements p ≠ [] ∧ cc.evidenceLawful p ∧ cc.standardMet p) ∧ (∀ (ac : AdminCase)
    (enforceable : Prop)
    (hrule : enforceable → ac.authorityHeld ∧ ac.dutyImposed ∧ ac.procedureFollowed), enforceable → ac.authorityHeld ∧ ac.dutyImposed ∧ ac.procedureFollowed)

/-! D001-D008 (group 01 接案、问题与主体识别, W2-A batch B01): each def is
that demand's own contract, translated from ALL_134_MATH_CONTRACTS.md.
The first conjunct is the group-registered locator/identity separation
component (a locator collision never merges two records); the remaining
conjuncts are the demand's operational semantics with its adverse case. -/

/-- D001 咨询主题与并列争点：topics(out) ⊆ Topics_scope；每个已确认并列
争点拿到自己的规范需求对象（不因主主题只报一个）；未分类段落进入 residual
且 residual 不含已确认段落。 -/
def demand_D001 : Prop :=
  (∃ a b : List String, locator a = locator b ∧ a ≠ b) ∧
  ∀ (scope : Finset String) (paras : List String),
    (∀ t ∈ paras.filter (fun p => decide (p ∈ scope)), t ∈ scope) ∧
    (∀ t ∈ scope, decide (t ∈ paras) = true →
        t ∈ paras.filter (fun p => decide (p ∈ scope))) ∧
    (∀ p ∈ paras, decide (p ∈ scope) = false →
        p ∈ paras.filter (fun p => decide (¬(p ∈ scope)))) ∧
    (∀ p ∈ paras.filter (fun p => decide (¬(p ∈ scope))), ¬(p ∈ scope))

/-- D002 民刑性质路由：route(s) 允许民事、刑事、并行或待定（并行
(true,true) 被政策声明即原样返回，不拆成二选一）；分类不得自动改变
准入事实（事实层无论路由结果如何逐条原样保留）。 -/
def demand_D002 : Prop :=
  (∃ a b : List String, locator a = locator b ∧ a ≠ b) ∧
  ∀ (table : List (String × Bool × Bool)) (s : String) (facts : List String),
    (∀ e, table.find? (fun p => decide (p.1 = s)) = some e → e ∈ table) ∧
    (∀ e, table.find? (fun p => decide (p.1 = s)) = some e → e = (s, true, true) →
        (e.2.1, e.2.2) = (true, true)) ∧
    (∀ r : Option (String × Bool × Bool),
        (match r with | some _ => facts | none => facts) = facts)

/-- D003 主体与角色：Role(person,matter,stage) 的每个绑定都有出处
（解析只返回表内绑定）；主体、角色、名称为不同类型字段——角色不同或
主体不同都不因其余字段同名而合并。 -/
def demand_D003 : Prop :=
  (∃ a b : List String, locator a = locator b ∧ a ≠ b) ∧
  ∀ (bindings : List (String × String × String × String))
      (person matter stage : String),
    (∀ e, bindings.find?
            (fun b => decide (b.1 = person ∧ b.2.1 = matter ∧ b.2.2.1 = stage)) = some e →
        e ∈ bindings) ∧
    (∀ (p r₁ r₂ : String), r₁ ≠ r₂ → (p, matter, stage, r₁) ≠ (p, matter, stage, r₂)) ∧
    (∀ (n₁ n₂ r : String), n₁ ≠ n₂ → (n₁, matter, stage, r) ≠ (n₂, matter, stage, r))

/-- D004 逐被告结果图：整案正确 = 所有必查被告的逐人映射全部正确；
交换两被告处分而总量（平均）不变，逐被告检查仍然失败。 -/
def demand_D004 : Prop :=
  (∃ a b : List String, locator a = locator b ∧ a ≠ b) ∧
  (∀ (ok : String → Bool) (required : List String),
      required.all ok = true ↔ ∀ d ∈ required, ok d = true) ∧
  (∀ (u v : String) (x y : ℕ), u ≠ v → x ≠ y →
      ((fun d => if d = u then x else if d = v then y else 0) u
          ≠ (fun d => if d = u then y else if d = v then x else 0) u) ∧
      ((fun d => if d = u then x else if d = v then y else 0) u
          + (fun d => if d = u then x else if d = v then y else 0) v
        = (fun d => if d = u then y else if d = v then x else 0) u
          + (fun d => if d = u then y else if d = v then x else 0) v))

/-- D005 登记快照一致解析：同名异码按规范主体键（登记代码）各自解析
不合并；按名称的别名解析命中的条目就是独立查表语义下的表内条目。 -/
def demand_D005 : Prop :=
  (∃ a b : List String, locator a = locator b ∧ a ≠ b) ∧
  ∀ (c₁ c₂ : ℕ) (nm : String) (rest : List (ℕ × String × ℕ)), c₁ ≠ c₂ →
    ((⟨c₁, nm, 0⟩ :: ⟨c₂, nm, 0⟩ :: rest).find? (fun r => decide (r.1 = c₁))
        = some (c₁, nm, 0)) ∧
    ((⟨c₁, nm, 0⟩ :: ⟨c₂, nm, 0⟩ :: rest).find? (fun r => decide (r.1 = c₂))
        = some (c₂, nm, 0)) ∧
    (∀ e, (⟨c₁, nm, 0⟩ :: ⟨c₂, nm, 0⟩ :: rest).find? (fun r => decide (r.2.1 = nm))
            = some e →
        e ∈ (⟨c₁, nm, 0⟩ :: ⟨c₂, nm, 0⟩ :: rest))

/-- D006 混同防线：同地址不传播身份（等号不把两实体合并为同一主体）；
责任边只由明确规则生成（每条生成边都有规则出处）；无规则声明则无边。 -/
def demand_D006 : Prop :=
  (∃ a b : List String, locator a = locator b ∧ a ≠ b) ∧
  ∀ (c₁ c₂ : ℕ) (k₁ k₂ addr : String) (rules : List (ℕ × (ℕ × String))), c₁ ≠ c₂ →
    ((c₁, k₁, addr) ≠ (c₂, k₂, addr)) ∧
    (∀ e ∈ rules.map (fun r => (r.1, r.2.1)), ∃ r ∈ rules, e = (r.1, r.2.1)) ∧
    (rules = [] → rules.map (fun r => (r.1, r.2.1)) = [])

/-- D007 法院代字与管辖：代字到机构与级别的查表结果有出处且字段原样；
管辖判断走另外的适用规则（无适用法源且无排除事由 = 待定，不因代字
解析成功而获得管辖）；同级别不同代字仍是两个机关。 -/
def demand_D007 : Prop :=
  (∃ a b : List String, locator a = locator b ∧ a ≠ b) ∧
  ∀ (courts : List (String × String × String))
      (sources : List SourceVersion) (t : ℕ) (exclusions : List String)
      (cd inst lv : String),
    (∀ e, courts.find? (fun c => decide (c.1 = cd)) = some e → e ∈ courts) ∧
    (applicableSources sources t = [] → ¬(cd ∈ exclusions) →
        decideSlot sources t exclusions cd = SlotStatus.pending) ∧
    (∀ (d₂ i₁ i₂ l : String), cd ≠ d₂ → (cd, inst, l) ≠ (d₂, i₂, l))

/-- D008 请求结构：Claim=(claimant,respondent,basis,object,remedy,scope)；
每个金额字段都挂在具名主体对上（无主体的金额槽位不存在）；任一字段
不同即不同请求；claimant 与 respondent 互换即不同请求。 -/
def demand_D008 : Prop :=
  (∃ a b : List String, locator a = locator b ∧ a ≠ b) ∧
  ∀ claims : List (String × String × String × String × String × String),
    (∀ e ∈ claims.map (fun c => (c.1, c.2.1)), ∃ c ∈ claims, (c.1, c.2.1) = e) ∧
    (∀ (a r bs bj₁ bj₂ rm sc : String), bj₁ ≠ bj₂ →
        (a, r, bs, bj₁, rm, sc) ≠ (a, r, bs, bj₂, rm, sc)) ∧
    (∀ a r : String, a ≠ r → (a, r) ≠ (r, a))

/-! D009-D018 (group 02 法源、解释与类案研究, W2-A batch B02): each def is
that demand's own contract, translated from ALL_134_MATH_CONTRACTS.md.
The first conjunct is the group-registered fail-closed source component
(a slot with no applicable source and no exclusion ground stays pending,
never inapplicable); the remaining conjuncts are the demand's own
operational semantics with its adverse case. -/

/-- D012 helper: bounded citation chase — resolve a term through the
declared definition table, following declared cross-references with at
most `fuel` hops; `none` is the explicit rejection path (fuel exhausted,
or neither a registered meaning nor a declared reference exists). -/
def citeChase (defs : List (String × String × Bool))
    (cites : List (String × String)) : ℕ → String → Option (String × Bool)
  | 0, _ => none
  | fuel + 1, x =>
    match defs.find? (fun d => decide (d.1 = x)) with
    | some d => some (d.2.1, d.2.2)
    | none =>
      match cites.find? (fun c => decide (c.1 = x)) with
      | some c => citeChase defs cites fuel c.2
      | none => none

/-- D009 引文回读与版本拒绝（反例：真实引文但引用错版本，版本检查须
拒绝）：quoted_span 就是 source 的 [st,en) 切片——按出处坐标从原文重取
逐字还原该引文、长度恰为 en-st；整段重读引文自身亦逐字还原（受保护
命题的可回读出处）；版本检查按缓存键三元组判定，键不同即拒绝，
引文内容为真也不放行。 -/
def demand_D009 : Prop :=
  (∀ (sources : List SourceVersion) (t : ℕ) (exclusions : List String)
      (s : String), applicableSources sources t = [] → ¬(s ∈ exclusions) →
      decideSlot sources t exclusions s = SlotStatus.pending) ∧
  ∀ (source : List Char) (st en : ℕ) (span : List Char)
      (v q : SourceVersion) (hkey : cacheKey v ≠ cacheKey q),
    en ≤ source.length →
    span = (source.take en).drop st →
    ((source.take en).drop st = span ∧
      span.length = en - st ∧
      (span.take span.length).drop 0 = span ∧
      cacheHit v q = false)

/-- D010 适用法条（反例：只召回相似法条不能签全部适用法条证书）：结果
= 冻结规则库中满足适用谓词的成员——每条结果既在库内又满足谓词；
"全部适用"声称要求独立候选覆盖：库内每条满足谓词的规则都必须在结果
里（结果=filter 全库）；谓词为假的相似法条记录永不进入适用结果。 -/
def demand_D010 : Prop :=
  (∀ (sources : List SourceVersion) (t : ℕ) (exclusions : List String)
      (s : String), applicableSources sources t = [] → ¬(s ∈ exclusions) →
      decideSlot sources t exclusions s = SlotStatus.pending) ∧
  ∀ (rules : List (String × Bool)) (hits : List String),
    hits = (rules.filter (fun r => r.2)).map (fun r => r.1) →
    ((∀ s ∈ hits, ∃ e ∈ rules, e.1 = s ∧ e.2 = true) ∧
     (∀ e ∈ rules, e.2 = true → e.1 ∈ hits) ∧
     (∀ e ∈ rules, e.2 = false → e ∉ rules.filter (fun r => r.2)))

/-- D011 历史版本与法效时间（反例：后上传旧文本不得按新上传日期当新
法）：Applicable(v,eventTime) 只按法效时间判定——事件时点早于 effective
即不适用，与其登记（published）先后无关；登记时间与法效时间是分别
保存的两个字段；旧文本在其自身 effective 之后照常适用（考查的是历史
版本）。 -/
def demand_D011 : Prop :=
  (∀ (sources : List SourceVersion) (t : ℕ) (exclusions : List String)
      (s : String), applicableSources sources t = [] → ¬(s ∈ exclusions) →
      decideSlot sources t exclusions s = SlotStatus.pending) ∧
  ∀ (old new : SourceVersion) (t p e r : ℕ),
    new.published < old.published → t < new.effective →
    (appliesAt new t = false ∧
      (⟨p, e, r⟩ : SourceVersion).published = p ∧
      (⟨p, e, r⟩ : SourceVersion).effective = e ∧
      (old.effective ≤ t → (∀ rr, old.repealed = some rr → t < rr) →
        appliesAt old t = true))

/-- D012 定义作用域与引用图解释器（反例：定义中排除关联方，主文不得
重新无条件纳入）：有界引用追踪在注册含义处停机并原样返回含义与限定
词——被定义排除的词元解析结果仍带排除标记；燃料耗尽给出明确拒绝
路径（none），不发明未注册含义。 -/
def demand_D012 : Prop :=
  (∀ (sources : List SourceVersion) (t : ℕ) (exclusions : List String)
      (s : String), applicableSources sources t = [] → ¬(s ∈ exclusions) →
      decideSlot sources t exclusions s = SlotStatus.pending) ∧
  ∀ (defs : List (String × String × Bool)) (cites : List (String × String))
      (x m : String) (fuel : ℕ),
    (defs.find? (fun d => decide (d.1 = x)) = some (x, m, false) →
        citeChase defs cites (fuel + 1) x = some (m, false)) ∧
    (citeChase defs cites 0 x = none) ∧
    (∀ (x' m' : String),
        defs.find? (fun d => decide (d.1 = x')) = some (x', m', true) →
        citeChase defs cites (fuel + 1) x' = some (m', true))

/-- D013 类案相关性与迁移（反例：程序上相关但实体事实不同，不复制
实体结论）：排序键就是指定 score——序关系与 score 的序一致且反对称；
类案迁移须持有相关特征保留见证——relevant 特征全部保留于目标案才可
复制实体结论，缺任一相关特征即不得复制。 -/
def demand_D013 : Prop :=
  (∀ (sources : List SourceVersion) (t : ℕ) (exclusions : List String)
      (s : String), applicableSources sources t = [] → ¬(s ∈ exclusions) →
      decideSlot sources t exclusions s = SlotStatus.pending) ∧
  ∀ (score : String → ℚ) (a b : String)
      (tgtFeats relevant : List String) (copied : Bool),
    (decide (score a > score b) = true ↔ score a > score b) ∧
    (score a > score b → score b > score a → False) ∧
    (copied = decide (relevant.all (fun f => decide (f ∈ tgtFeats))) →
      (∃ f ∈ relevant, f ∉ tgtFeats) → copied = false)

/-- D014 固定候选池重排与全库检索（反例：100项pool全命中不能改写成
全库无遗漏）：返回集 ⊆ Relevant_D——返回成员逐项来自池内且满足独立
相关性定义；池内满足谓词者全部被返回（无漏池内）；等号声称（全库
无遗漏）需要覆盖 D：语料中有池外真相关条目时，全库无遗漏声称即被
拒绝。 -/
def demand_D014 : Prop :=
  (∀ (sources : List SourceVersion) (t : ℕ) (exclusions : List String)
      (s : String), applicableSources sources t = [] → ¬(s ∈ exclusions) →
      decideSlot sources t exclusions s = SlotStatus.pending) ∧
  ∀ (corpus pool returned : List String) (relevant : String → Bool),
    returned = pool.filter relevant →
    ((∀ s ∈ returned, s ∈ pool ∧ relevant s = true) ∧
     (∀ s ∈ pool, relevant s = true → s ∈ returned) ∧
     ((∃ s ∈ corpus, s ∉ pool ∧ relevant s = true) →
        ¬ (∀ s ∈ corpus, relevant s = true → s ∈ returned)))

/-- D015 引用支持与声明升级（反例：案号真实但只支持相反观点，不准当
正向依据）：核准支持边只由正向 stance 的引用生成——每条边的来源都是
一条正向引用；反方 stance 的引用记录永不进入核准边来源；每个引用
命题的 span 原样保留在登记中。 -/
def demand_D015 : Prop :=
  (∀ (sources : List SourceVersion) (t : ℕ) (exclusions : List String)
      (s : String), applicableSources sources t = [] → ¬(s ∈ exclusions) →
      decideSlot sources t exclusions s = SlotStatus.pending) ∧
  ∀ (cites : List (String × List Char × Bool)) (edges : List (String × String))
      (propId : String),
    edges = (cites.filter (fun c => c.2.2)).map (fun c => (c.1, propId)) →
    ((∀ e ∈ edges, ∃ c ∈ cites, c.1 = e.1 ∧ c.2.2 = true) ∧
     (∀ c ∈ cites, c.2.2 = false → c ∉ cites.filter (fun c => c.2.2)) ∧
     (∀ c ∈ cites, ∃ span, (c.1, span, c.2.2) ∈ cites ∧ span = c.2.1))

/-- D016 先例效力图与引用时点（反例：推翻一个争点不得删除该案所有
无关论点，亦不得保留被推翻点）：推翻按 (判例, 争点) 逐点登记生效日，
效力随引用时点判定——生效日后该点失效；无关争点（其推翻记录在引用
时点之前均未生效）照常有效；两争点切片互不串扰。 -/
def demand_D016 : Prop :=
  (∀ (sources : List SourceVersion) (t : ℕ) (exclusions : List String)
      (s : String), applicableSources sources t = [] → ¬(s ∈ exclusions) →
      decideSlot sources t exclusions s = SlotStatus.pending) ∧
  ∀ (overruled : List (String × String × ℕ)) (c i j : String) (t d : ℕ),
    (c, i, d) ∈ overruled → d ≤ t →
    ((overruled.filter (fun o => decide (o.1 = c ∧ o.2.1 = i))).all
        (fun o => decide (t < o.2.2)) = false ∧
      ((∀ o ∈ overruled, o.1 = c ∧ o.2.1 = j → t < o.2.2) →
        (overruled.filter (fun o => decide (o.1 = c ∧ o.2.1 = j))).all
          (fun o => decide (t < o.2.2)) = true))

/-- D017 法律框架候选筛选（反例：不能按英文合同或美国当事人自动选
UCC）：候选按四项适用条件（管辖、标的、冲突法、适用条件）合取筛选，
全真才选中、任一为假即未选中；单一条件为真而其余为假时仍不选中
（未决分支保留在候选表中，不丢弃）。 -/
def demand_D017 : Prop :=
  (∀ (sources : List SourceVersion) (t : ℕ) (exclusions : List String)
      (s : String), applicableSources sources t = [] → ¬(s ∈ exclusions) →
      decideSlot sources t exclusions s = SlotStatus.pending) ∧
  ∀ (cands : List (String × Bool × Bool × Bool × Bool)) (name : String)
      (b₁ b₂ b₃ b₄ : Bool),
    cands.find? (fun c => decide (c.1 = name)) = some (name, b₁, b₂, b₃, b₄) →
    (((b₁ && b₂ && b₃ && b₄) = true ↔
        b₁ = true ∧ b₂ = true ∧ b₃ = true ∧ b₄ = true) ∧
     ((b₁ && b₂ && b₃ && b₄) = false ↔
        b₁ = false ∨ b₂ = false ∨ b₃ = false ∨ b₄ = false) ∧
     (b₁ = true → b₂ = false → (b₁ && b₂ && b₃ && b₄) = false) ∧
     (name, b₁, b₂, b₃, b₄) ∈ cands)

/-- D018 跨法域申报规则比较（反例：将申报门槛相同误当申报后果相同须
被区分）：比较保持每个域的主体/门槛/时间/效果四维——恒等比较下四维
逐维一致；门槛相同而后果不同的两个制度必须被区分（不同一），并返回
具名差异见证（"effect"维），不得判为等同。 -/
def demand_D018 : Prop :=
  (∀ (sources : List SourceVersion) (t : ℕ) (exclusions : List String)
      (s : String), applicableSources sources t = [] → ¬(s ∈ exclusions) →
      decideSlot sources t exclusions s = SlotStatus.pending) ∧
  ∀ (a b : List String × ℚ × ℕ × String)
      (m : List String × ℚ × ℕ × String),
    (m = a → m.1 = a.1 ∧ m.2.1 = a.2.1 ∧ m.2.2.1 = a.2.2.1 ∧ m.2.2.2 = a.2.2.2) ∧
    (a.2.1 = b.2.1 → a.2.2.2 ≠ b.2.2.2 → a ≠ b) ∧
    (a.2.1 = b.2.1 → a.2.2.2 ≠ b.2.2.2 →
      (if a.2.2.2 = b.2.2.2 then ([] : List String) else ["effect"]) ≠ [])

/-! D019-D028 (group 03 证据内容、事件与冲突, W2-A batch B03): each def is
that demand's own contract, translated from ALL_134_MATH_CONTRACTS.md.
The first conjunct is the group-registered evidence-identity component
(a conflicting resubmission under an already-accepted id never overwrites
the first acceptance and never double-counts); the remaining conjuncts
are the demand's own operational semantics with its adverse case. -/

/-- D019 事件抽取与触发范围（反例：触发词来自引述假设，不得变成已发生
事件）：每个登记事件行 (type, actors, object, quoted, st, en) 的跨度坐标
都切在原文内——[st,en) 切片长度恰为 en-st（回指原文可读回）；带引述
标记的触发词行永不进入已发生事件结果（结果只收 quoted=false 的行）；
标签映射无碰撞——同一触发词在两行挂不同类型标签仍是两行分立，不合并。 -/
def demand_D019 : Prop :=
  (∀ (k : ℕ) (v v' : ℚ) (l : List Obs),
      (dedup (⟨k, v'⟩ :: ⟨k, v⟩ :: l)).map Obs.id = (dedup (⟨k, v⟩ :: l)).map Obs.id) ∧
  ∀ (source : List String)
      (tags : List (String × List String × String × Bool × ℕ × ℕ)),
    ((∀ (ty : String) (acs : List String) (ob : String) (q : Bool) (st en : ℕ),
        (ty, acs, ob, q, st, en) ∈ tags → en ≤ source.length) →
     ((∀ (ty : String) (acs : List String) (ob : String) (q : Bool) (st en : ℕ),
          q = true →
          (ty, acs, ob, q, st, en) ∉
            tags.filter (fun r => decide (r.2.2.2.1 = false))) ∧
      (∀ (ty : String) (acs : List String) (ob : String) (q : Bool) (st en : ℕ),
          (ty, acs, ob, q, st, en) ∈ tags → en ≤ source.length →
          ((source.take en).drop st).length = en - st) ∧
      (∀ (ty ty' ob : String) (acs₁ acs₂ : List String) (q : Bool) (st en : ℕ),
          ty ≠ ty' → (ty, acs₁, ob, q, st, en) ≠ (ty', acs₂, ob, q, st, en))))

/-- D020 事件参与人、对象、法律阶段与证据地位逐边绑定（反例：前案
被害人不得由位置默认绑定到本案）：绑定按 caseId 显式键过滤——本案边
逐条携带其自己的 caseId（位置不默认填充）；非本案 caseId 的行永不进入
本案绑定结果；person 不同即不同绑定行，不因其余字段同名而合并。 -/
def demand_D020 : Prop :=
  (∀ (k : ℕ) (v v' : ℚ) (l : List Obs),
      (dedup (⟨k, v'⟩ :: ⟨k, v⟩ :: l)).map Obs.id = (dedup (⟨k, v⟩ :: l)).map Obs.id) ∧
  ∀ (edges : List (String × String × String × String × String)) (c : String),
    ((∀ e ∈ edges.filter (fun e => decide (e.1 = c)), e.1 = c) ∧
     (∀ (p o s g : String), (c, p, o, s, g) ∈ edges →
        (c, p, o, s, g) ∈ edges.filter (fun e => decide (e.1 = c))) ∧
     (∀ (c' p o s g : String), c' ≠ c →
        (c', p, o, s, g) ∉ edges.filter (fun e => decide (e.1 = c))) ∧
     (∀ (p₁ p₂ o s g : String), p₁ ≠ p₂ →
        (c, p₁, o, s, g) ≠ (c, p₂, o, s, g)))

/-- D021 多份材料组成有出处的时间线（反例：没有时间的事件不凭叙述顺序
补造精确日期）：有明确日期的事件按日期严格序进入时间线（序传递、反自
反）；无日期的事件保持 unknown（none），既不补造日期也不从时间线清单
静默消失——每条源事件要么在已定日期载体里要么显式无日期（二分完备）。 -/
def demand_D021 : Prop :=
  (∀ (k : ℕ) (v v' : ℚ) (l : List Obs),
      (dedup (⟨k, v'⟩ :: ⟨k, v⟩ :: l)).map Obs.id = (dedup (⟨k, v⟩ :: l)).map Obs.id) ∧
  ∀ (evts : List (String × Option ℕ)),
    ((∀ (e : String × Option ℕ), e ∈ evts → e.2 = none →
        e ∉ evts.filter (fun x => x.2.isSome)) ∧
     (∀ (e : String × Option ℕ) (d : ℕ), e ∈ evts → e.2 = some d →
        e ∈ evts.filter (fun x => x.2.isSome)) ∧
     (∀ (e : String × Option ℕ), e ∈ evts →
        e ∈ evts.filter (fun x => x.2.isSome) ∨ e.2 = none) ∧
     (∀ (a b c : ℕ), a < b → b < c → a < c) ∧
     (∀ a : ℕ, ¬ (a < a)))

/-- D022 实质矛盾与含混（反例：两个不同时点地址不能自动判为同一时点
矛盾）：矛盾登记要求同一主体、同一时点、内容对在声明相反表内且见证
非空，四者齐备才报告；不同时点的候选行与未声明相反的内容对永不成为
矛盾；无论是否矛盾，双方原读法都保留在多解释清单里（含混不消解）。 -/
def demand_D022 : Prop :=
  (∀ (k : ℕ) (v v' : ℚ) (l : List Obs),
      (dedup (⟨k, v'⟩ :: ⟨k, v⟩ :: l)).map Obs.id = (dedup (⟨k, v⟩ :: l)).map Obs.id) ∧
  ∀ (cands : List ((String × ℕ × String) × (String × ℕ × String) × String))
      (ctres : List (String × String)),
    ((∀ r ∈ cands.filter (fun r =>
          decide (r.1.1 = r.2.1.1 ∧ r.1.2.1 = r.2.1.2.1 ∧
            (r.1.2.2, r.2.1.2.2) ∈ ctres ∧ r.2.2 ≠ "")),
        r.1.1 = r.2.1.1 ∧ r.1.2.1 = r.2.1.2.1 ∧
          (r.1.2.2, r.2.1.2.2) ∈ ctres ∧ r.2.2 ≠ "") ∧
     (∀ r ∈ cands, r.1.2.1 ≠ r.2.1.2.1 →
        r ∉ cands.filter (fun r =>
          decide (r.1.1 = r.2.1.1 ∧ r.1.2.1 = r.2.1.2.1 ∧
            (r.1.2.2, r.2.1.2.2) ∈ ctres ∧ r.2.2 ≠ ""))) ∧
     (∀ r ∈ cands, (r.1.2.2, r.2.1.2.2) ∉ ctres →
        r ∉ cands.filter (fun r =>
          decide (r.1.1 = r.2.1.1 ∧ r.1.2.1 = r.2.1.2.1 ∧
            (r.1.2.2, r.2.1.2.2) ∈ ctres ∧ r.2.2 ≠ ""))) ∧
     (∀ r ∈ cands, (r.1.2.2, r.2.1.2.2) ∈
        cands.map (fun r => (r.1.2.2, r.2.1.2.2))))

/-- D023 缺直接材料与否定证据分开（反例：材料未附付款凭证不得推出
肯定未付款）：q 无记录不推出 q 的否定证据构造——缺记录时不存在
polarity=false 的显式记录条目；负查询只在声明的完整记录范围内开放
（范围外查询不获准）；无记录标记（none）与否定证据记录（some false）
是两个不同载体，不互相顶替。 -/
def demand_D023 : Prop :=
  (∀ (k : ℕ) (v v' : ℚ) (l : List Obs),
      (dedup (⟨k, v'⟩ :: ⟨k, v⟩ :: l)).map Obs.id = (dedup (⟨k, v⟩ :: l)).map Obs.id) ∧
  ∀ (rec : List (String × Bool)) (scope : List String) (q : String),
    ((q ∉ rec.map (fun r => r.1) →
        ¬ (∃ r ∈ rec, r.1 = q ∧ r.2 = false)) ∧
     (q ∉ scope → decide (q ∈ scope) = false) ∧
     ((none : Option Bool) ≠ some false))

/-- D024 答案支持定位（反例：给正确答案但引用无关原句，不通过支持
检查）：支持片段以 (answer, span, st, en) 登记，边界合法（st ≤ en）
才进入通过集；同一答案的两条不同片段都在通过集内（冗余支持可保留）；
边界非法（en < st）的片段永不进入支持集。 -/
def demand_D024 : Prop :=
  (∀ (k : ℕ) (v v' : ℚ) (l : List Obs),
      (dedup (⟨k, v'⟩ :: ⟨k, v⟩ :: l)).map Obs.id = (dedup (⟨k, v⟩ :: l)).map Obs.id) ∧
  ∀ (links : List (String × String × ℕ × ℕ)) (a s₁ s₂ : String) (st en : ℕ),
    (a, s₁, st, en) ∈ links → (a, s₂, st, en) ∈ links → st ≤ en → s₁ ≠ s₂ →
    (((a, s₁, st, en) ∈ links.filter (fun l => decide (l.2.2.1 ≤ l.2.2.2)) ∧
      (a, s₂, st, en) ∈ links.filter (fun l => decide (l.2.2.1 ≤ l.2.2.2))) ∧
     ((∀ l ∈ links.filter (fun l => decide (l.2.2.1 ≤ l.2.2.2)),
          l.2.2.1 ≤ l.2.2.2) ∧
      (∀ l ∈ links, l.2.2.2 < l.2.2.1 →
          l ∉ links.filter (fun l => decide (l.2.2.1 ≤ l.2.2.2)))))

/-- D025 “是”“否”“不知道”保持区别（反例：unknown 进 if 分支当 False
产生否定结论须拦截）：四值状态编码为 some (some Bool)（是/否）、none
（不知道）、some none（冲突），任一状态必居其一且两两不同一不互转；
条件分支只能取出 definite Bool——非 definite 状态落到显式默认值分支，
永不凭空产出否定结论。 -/
def demand_D025 : Prop :=
  (∀ (k : ℕ) (v v' : ℚ) (l : List Obs),
      (dedup (⟨k, v'⟩ :: ⟨k, v⟩ :: l)).map Obs.id = (dedup (⟨k, v⟩ :: l)).map Obs.id) ∧
  ∀ (s : Option (Option Bool)) (fb : Bool),
    ((s = none ∨ s = some none ∨ (∃ b, s = some (some b))) ∧
     (¬ (none = some (some false)) ∧ ¬ (some none = some (some true))) ∧
     ((match s with
         | some (some b) => b
         | _ => fb) = fb ∨ (∃ b, s = some (some b))))

/-- D026 主张、证据内容与法院认定分立（反例：原告诉称不得经摘要变成
法院查明）：每条记录的 source 与 use 是各自独立保存的字段；asserted
类记录永不进入 adjudicated 过滤结果（升格必须显式登记，无隐式升格）；
adjudicated 过滤结果的每条都在原记录表内且 kind 逐字为 adjudicated；
种类不同的两条记录即使其余字段全同也仍不同一。 -/
def demand_D026 : Prop :=
  (∀ (k : ℕ) (v v' : ℚ) (l : List Obs),
      (dedup (⟨k, v'⟩ :: ⟨k, v⟩ :: l)).map Obs.id = (dedup (⟨k, v⟩ :: l)).map Obs.id) ∧
  ∀ (recs : List (String × String × String × String)),
    ((∀ (kd c s u : String),
        (kd, c, s, u).2.2.1 = s ∧ (kd, c, s, u).2.2.2 = u) ∧
     (∀ (c s u : String),
        ("asserted", c, s, u) ∉
          recs.filter (fun r => decide (r.1 = "adjudicated"))) ∧
     (∀ r ∈ recs.filter (fun r => decide (r.1 = "adjudicated")),
        r ∈ recs ∧ r.1 = "adjudicated") ∧
     (∀ (c s u : String), ("asserted", c, s, u) ≠ ("adjudicated", c, s, u)))

/-- D027 拟写审理事实段的支持检查（反例：把未确认行为改写为既成事实
应使语义差量失败）：事实段只收声明的准入事实或明确条件语义里的受保护
命题（段内 ⊆ 准入∪条件）；不在两清单内的拟写命题不进段、作为未决项
保留在 pending 载体（二分完备）；未决命题被改写标记为既成事实时，语义
差量载体非空（篡改被检出）。 -/
def demand_D027 : Prop :=
  (∀ (k : ℕ) (v v' : ℚ) (l : List Obs),
      (dedup (⟨k, v'⟩ :: ⟨k, v⟩ :: l)).map Obs.id = (dedup (⟨k, v⟩ :: l)).map Obs.id) ∧
  ∀ (draft admitted conditional tamper : List String),
    ((∀ d ∈ draft.filter (fun x => decide (x ∈ admitted ∨ x ∈ conditional)),
        d ∈ admitted ∨ d ∈ conditional) ∧
     (∀ d ∈ draft, d ∉ admitted → d ∉ conditional →
        d ∉ draft.filter (fun x => decide (x ∈ admitted ∨ x ∈ conditional))) ∧
     (∀ d ∈ draft,
        d ∈ draft.filter (fun x => decide (x ∈ admitted ∨ x ∈ conditional)) ∨
        d ∈ draft.filter (fun x => decide (¬ (x ∈ admitted ∨ x ∈ conditional)))) ∧
     (∀ d ∈ draft, d ∈ tamper → ¬ (d ∈ admitted ∨ d ∈ conditional) →
        1 ≤ (draft.filter (fun x =>
            decide (x ∈ tamper ∧ ¬ (x ∈ admitted ∨ x ∈ conditional)))).length))

/-- D028 前科、其他案件与本案分作用域（反例：过去抢劫经历不能直接加入
本次危险驾驶罪名清单）：行为行 (caseId, eventId, act, historical) 逐条
携带案件与事件作用域——进入本次罪名的行为逐条 caseId 为本案；带历史
标记的行为永不直接进入本次罪名结果；历史经历只能经指定规则通道进入
（通道条目都在规则表内，且声明为 true 的规则条目都在通道内）；案件或
事件不同即行为不同，不合并。 -/
def demand_D028 : Prop :=
  (∀ (k : ℕ) (v v' : ℚ) (l : List Obs),
      (dedup (⟨k, v'⟩ :: ⟨k, v⟩ :: l)).map Obs.id = (dedup (⟨k, v⟩ :: l)).map Obs.id) ∧
  ∀ (acts : List (String × String × String × Bool)) (rules : List (String × Bool))
      (c : String),
    ((∀ a ∈ acts.filter (fun a => decide (a.1 = c ∧ ¬ a.2.2.2)), a.1 = c) ∧
     (∀ (e x : String), (c, e, x, true) ∉
        acts.filter (fun a => decide (a.1 = c ∧ ¬ a.2.2.2))) ∧
     (∀ r ∈ rules.filter (fun r => r.2), r ∈ rules) ∧
     (∀ r ∈ rules, r.2 = true → r ∈ rules.filter (fun r => r.2)) ∧
     (∀ (c₁ c₂ e x : String), c₁ ≠ c₂ →
        (c₁, e, x, false) ≠ (c₂, e, x, false)) ∧
     (∀ (e₁ e₂ x : String), e₁ ≠ e₂ → (c, e₁, x, false) ≠ (c, e₂, x, false)))

/-! D029-D036 (group 04 请求权、抗辩及争点处理, W2-A batch B04): each def is
that demand's own contract, translated from ALL_134_MATH_CONTRACTS.md.
The first conjunct is the group-registered argument-construction component
(bounded generation is sound: every generated argument is well-formed with
height at most the budget); the remaining conjuncts are the demand's own
operational semantics with its adverse case. -/

/-- D029 请求候选与主给付/附随费独立（反例：互斥备位请求不能默认同时
全额受偿）：候选=给定事实下规则表允许的 remedy 组合——每条候选都在表
内且前提为真，表内前提为真的行全部进入候选（结果=filter 全表）；
主给付与附随费是两个独立债项（种类不同即不同，不合并为一个数目）；
备位请求的受偿以主请求未受偿为前提——主请求受偿时备位行不在受偿结果。 -/
def demand_D029 : Prop :=
  (∀ {A : Type} [DecidableEq A] (facts : List A) (rules : List (Rul A)),
      ∀ d a, a ∈ Generate facts rules d → WellFormed facts rules a ∧ Arg.height a ≤ d) ∧
  ∀ (table : List (String × Bool × String)) (p i : String) (pr alt : Bool)
      (awards : List String),
    p ≠ i → pr = true →
    awards = (if pr then [p] else []) ++ (if !pr && alt then [i] else []) →
    ((∀ c ∈ (table.filter (fun r => r.2.1)).map (fun r => r.1),
        ∃ e ∈ table, e.1 = c ∧ e.2.1 = true) ∧
     (∀ e ∈ table, e.2.1 = true → e.1 ∈ (table.filter (fun r => r.2.1)).map (fun r => r.1)) ∧
     (∀ (d : String) (x y : ℚ), (d, "principal", x) ≠ (d, "incidental", y)) ∧
     i ∉ awards)

/-- D030 诉请四阶段分立（反例：生成与原告诉请相同不获得全部合法请求
证书）：Filed/Allowed/Supported/Awarded 是四个不同载体（标签两两不同）
并显式连接——受偿 ⊆ 支持 ⊆ 已提（逐行携带支持/受偿标记）；仅仅回声
已提清单不等于全部可获支持清单：允许表中有已提清单之外的行时，回声
清单与全部允许清单必不相同。 -/
def demand_D030 : Prop :=
  (∀ {A : Type} [DecidableEq A] (facts : List A) (rules : List (Rul A)),
      ∀ d a, a ∈ Generate facts rules d → WellFormed facts rules a ∧ Arg.height a ≤ d) ∧
  ((("filed" : String) ≠ "allowed" ∧ "filed" ≠ "supported" ∧ "filed" ≠ "awarded") ∧
    ("allowed" ≠ "supported" ∧ "allowed" ≠ "awarded") ∧ "supported" ≠ "awarded") ∧
  ∀ (filed sup awd : List (String × Bool × Bool)) (echo : List String)
      (table : List (String × Bool)),
    sup = filed.filter (fun r => r.2.1) →
    awd = sup.filter (fun r => r.2.2) →
    echo = filed.map (fun r => r.1) →
    ((∀ r ∈ awd, r ∈ sup) ∧ (∀ r ∈ awd, r ∈ filed) ∧ (∀ r ∈ sup, r ∈ filed) ∧
     (∀ r ∈ awd, r.2.1 = true ∧ r.2.2 = true) ∧
     (∀ e ∈ table, e.2 = true → e.1 ∉ echo →
        echo ≠ (table.filter (fun r => r.2)).map (fun r => r.1)))

/-- D031 备选法律关系情景（反例：不得把被告的投资抗辩既当承认借款又作
相反事实）：借贷与投资是两张不同情景行——关系不同即行不同，各自的前
提/结果从各自登记行导出（查表带出处）；答辩命题的"承认借款"与"相反
事实"是互斥载体——双标记行不进任何载体，承认载体行不同时是相反事实，
相反事实载体行不同时是承认。 -/
def demand_D031 : Prop :=
  (∀ {A : Type} [DecidableEq A] (facts : List A) (rules : List (Rul A)),
      ∀ d a, a ∈ Generate facts rules d → WellFormed facts rules a ∧ Arg.height a ≤ d) ∧
  ∀ (rows : List (String × String × String))
      (defs : List (String × Bool × Bool))
      (r₁ r₂ p₁ c₁ p₂ c₂ : String) (adm contra : List (String × Bool × Bool)),
    r₁ ≠ r₂ →
    rows.find? (fun d => decide (d.1 = r₁)) = some (r₁, p₁, c₁) →
    rows.find? (fun d => decide (d.1 = r₂)) = some (r₂, p₂, c₂) →
    adm = defs.filter (fun d => d.2.1 && !d.2.2) →
    contra = defs.filter (fun d => d.2.2 && !d.2.1) →
    (((r₁, p₁, c₁) ≠ (r₂, p₂, c₂)) ∧
     ((r₁, p₁, c₁) ∈ rows ∧ (r₂, p₂, c₂) ∈ rows) ∧
     (∀ d ∈ defs, d.2.1 = true → d.2.2 = true → d ∉ adm ∧ d ∉ contra) ∧
     (∀ d ∈ adm, d.2.2 = false) ∧
     (∀ d ∈ contra, d.2.1 = false))

/-- D032 分支共享与相容约束（反例：在有效分支取本金规则、无效分支取
收益规则拼接不合法结果）：从同一主张与输入版本分出的各支共享身份与
版本（身份/版本字段逐支相同、分支不同即行不同），但规则适用表按支内
regime 闭合声明——有效支配本金规则、无效支配收益规则，跨支拼接对
(valid, yield) 与 (invalid, principal) 都不在适用表内。 -/
def demand_D032 : Prop :=
  (∀ {A : Type} [DecidableEq A] (facts : List A) (rules : List (Rul A)),
      ∀ d a, a ∈ Generate facts rules d → WellFormed facts rules a ∧ Arg.height a ≤ d) ∧
  ∀ bV bI : String × String × String × String,
    bV.1 ≠ bI.1 →
    bV.2.1 = bI.2.1 →
    bV.2.2.1 = bI.2.2.1 →
    (((("valid", "principal") : String × String) ∈
        [("valid", "principal"), ("invalid", "yield")] ∧
      (("invalid", "yield") : String × String) ∈
        [("valid", "principal"), ("invalid", "yield")]) ∧
     (("valid", "yield") : String × String) ∉
        [("valid", "principal"), ("invalid", "yield")] ∧
     (("invalid", "principal") : String × String) ∉
        [("valid", "principal"), ("invalid", "yield")]) ∧
    bV ≠ bI ∧
    ((bV.2.1, bV.2.2.1) = (bI.2.1, bI.2.2.1))

/-- D033 时效各要素分别计算（反例：只有到期、无抗辩提出，不自动按时效
驳回）：驳回须同时具备"期间届满"与"被告提出抗辩"两个独立开关——仅
到期而未抗辩时债权照常存活（到期不自动删债权）；中断后的重新起算是
另一本独立的账（自承诺日起算的加法），承诺开关不并入到期判定。 -/
def demand_D033 : Prop :=
  (∀ {A : Type} [DecidableEq A] (facts : List A) (rules : List (Rul A)),
      ∀ d a, a ∈ Generate facts rules d → WellFormed facts rules a ∧ Arg.height a ≤ d) ∧
  ∀ (due raised ack : Bool) (ackDay restart : ℕ) (dismissed alive : Bool),
    dismissed = decide (due && raised) →
    alive = !(decide (due && raised)) →
    restart = ackDay + 1095 →
    ((due = true → raised = false → dismissed = false ∧ alive = true) ∧
     (due = true → raised = true → dismissed = true) ∧
     (ack = true → restart = ackDay + 1095) ∧
     (∀ ack' : Bool, dismissed = decide (due && raised)))

/-- D034 Issue 图五链与拒绝跳步（反例：把反驳未成立当作对方主张已证明
须拒绝）：每行分别携带争点、主张、反驳、责任主体与攻击靶点五个链位；
主张的证明状态只由其自身支持集导出——支持集未立时主张不证明，反驳
成立或未成立都不代行证明。 -/
def demand_D034 : Prop :=
  (∀ {A : Type} [DecidableEq A] (facts : List A) (rules : List (Rul A)),
      ∀ d a, a ∈ Generate facts rules d → WellFormed facts rules a ∧ Arg.height a ≤ d) ∧
  ∀ (row : String × String × String × String × String)
      (issues : List (String × String × String × String × String))
      (supOk proved : Bool),
    row ∈ issues →
    proved = decide supOk →
    (((row.1, row.2.1, row.2.2.1, row.2.2.2.1, row.2.2.2.2) ∈
        issues.map (fun x => (x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2))) ∧
     (∀ (c₁ c₂ i r p a : String), c₁ ≠ c₂ →
        (i, c₁, r, p, a) ≠ (i, c₂, r, p, a)) ∧
     (supOk = false → proved = false) ∧
     (∀ rebOk : Bool, proved = decide supOk))

/-- D035 答辩链接与承认授权（反例：模板中无来源的债务承认应触发审查
而非静默写入）：每条承认进入记录载体都带自身授权来源（写入的承认都
有来源为真的行）；无来源的承认行进入审查清单，绝不静默写入记录。 -/
def demand_D035 : Prop :=
  (∀ {A : Type} [DecidableEq A] (facts : List A) (rules : List (Rul A)),
      ∀ d a, a ∈ Generate facts rules d → WellFormed facts rules a ∧ Arg.height a ≤ d) ∧
  ∀ (defs : List (String × String × String × Bool × Bool))
      (admissions reviewed : List String),
    admissions = (defs.filter (fun d => d.2.2.2.1 && d.2.2.2.2)).map (fun d => d.1) →
    reviewed = (defs.filter (fun d => d.2.2.2.1 && !d.2.2.2.2)).map (fun d => d.1) →
    ((∀ p ∈ admissions, ∃ d ∈ defs, d.1 = p ∧ d.2.2.2.2 = true) ∧
     (∀ d ∈ defs, d.2.2.2.1 = true → d.2.2.2.2 = false → d.1 ∈ reviewed))

/-- D036 同一责任模型联算（反例：连带责任外部给付与内部份额不得混为
每人比例给付）：主体、方式、份额与金额由同一模型逐人联合计算——
内部份额行 = (主体, 份额×总额)，两行主体不同即行不同，份额账守恒
（Σ 份额×总额 = 总额）；外部给付是另一本逐人账，外部给付额与内部
比例额不同时，两本账的清单必不相同。 -/
def demand_D036 : Prop :=
  (∀ {A : Type} [DecidableEq A] (facts : List A) (rules : List (Rul A)),
      ∀ d a, a ∈ Generate facts rules d → WellFormed facts rules a ∧ Arg.height a ≤ d) ∧
  ∀ (p₁ p₂ : String) (s₁ s₂ e₁ e₂ total : ℚ),
    p₁ ≠ p₂ → s₁ + s₂ = 1 → e₁ + e₂ = total →
    (((p₁, s₁ * total) ≠ (p₂, s₂ * total)) ∧
     (s₁ * total + s₂ * total = total) ∧
     (e₁ ≠ s₁ * total →
        ([(p₁, s₁ * total), (p₂, s₂ * total)] : List (String × ℚ)) ≠
          [(p₁, e₁), (p₂, e₂)]))

/-! D037-D046 (group 05 刑事定罪、量刑与多被告, W2-A batch B05): each def is
that demand's own contract, translated from ALL_134_MATH_CONTRACTS.md.
The first conjunct is the group-registered per-person component (conviction
slot keys are indexed by the person, so two defendants never share one
elements slot); the remaining conjuncts are the demand's own operational
semantics with its adverse case. -/

/-- D039 helper: the numeric aggregate over a penalty-kind ledger exists
    only when every row is a term row (kind 1) carrying its month count;
    life (kind 2) and death (kind 3) rows are non-numeric kinds — they
    poison the aggregate instead of entering ordinary addition, so no
    sentinel number can be mixed into a sentence average. -/
def penTotal (rows : List (ℕ × Option ℕ)) : Option ℕ :=
  if rows.all (fun r => r.1 = 1 && r.2.isSome) then
    some (rows.map (fun r => r.2.getD 0)).sum
  else none

/-- D043 helper: field-by-field read-back of a rendered main text against
    the verified structured record — each mismatched field (kind, period,
    fine) is reported by name, so a mis-written fine is found on read-back. -/
def readBack (rec txt : String × ℕ × ℚ) : List String :=
  (if txt.1 = rec.1 then [] else ["kind"]) ++
    (if txt.2.1 = rec.2.1 then [] else ["months"]) ++
    (if txt.2.2 = rec.2.2 then [] else ["fine"])

/-- D045 helper: an amount item enters the criminal total only when its
    three attribution axes (property / act / subject) are all verified. -/
def crimOK (it : ℕ × Bool × Bool × Bool × ℚ) : Bool :=
  it.2.1 && it.2.2.1 && it.2.2.2.1

/-- D045 helper: count each verified item once — a source already seen is
    skipped, so the same loot appearing in two records is never added
    twice. -/
def countOnce : List (ℕ × Bool × Bool × Bool × ℚ) → List ℕ → ℚ
  | [], _ => 0
  | it :: rest, seen =>
    if crimOK it = true ∧ ¬(it.1 ∈ seen) then
      it.2.2.2.2 + countOnce rest (it.1 :: seen)
    else countOnce rest seen

/-- D037 多罪标签与要件/阻却/竞合政策（反例：单标签接口不得悄悄丢掉第二项
合法罪名候选）：输出标签集 = 冻结候选表中同时满足选定要件、阻却排除与竞合
政策的行——输出标签逐项回指表内全真行，表内全真行全部进入输出（标签与
语义双向映射）；两个不同的全真候选同时在输出里，只保留首个的单标签载体
因此不等于输出（丢掉第二项被检出）。 -/
def demand_D037 : Prop :=
  (∀ (i j : ℕ) (h : personSlot i = personSlot j), i = j) ∧
  ∀ (cands : List (String × Bool × Bool × Bool)) (outs : List String),
    outs = (cands.filter (fun c => c.2.1 && c.2.2.1 && c.2.2.2)).map (fun c => c.1) →
    ((∀ l ∈ outs, ∃ e ∈ cands, e.1 = l ∧ e.2.1 = true ∧ e.2.2.1 = true ∧ e.2.2.2 = true) ∧
     (∀ e ∈ cands, e.2.1 = true → e.2.2.1 = true → e.2.2.2 = true → e.1 ∈ outs) ∧
     (∀ c₁ c₂ : String × Bool × Bool × Bool,
        c₁ ∈ cands → c₂ ∈ cands → c₁.1 ≠ c₂.1 →
        c₁.2.1 = true → c₁.2.2.1 = true → c₁.2.2.2 = true →
        c₂.2.1 = true → c₂.2.2.1 = true → c₂.2.2.2 = true →
        c₁.1 ∈ outs ∧ c₂.1 ∈ outs ∧ [c₁.1] ≠ outs))

/-- D038 法条类别编码往返与类型分立（反例：law.txt 第1项不自动打印为刑法
第1条）：冻结词典按标签ID与（法条编号、款项）双向可查——（编号、款项）
命中唯一时，按ID查得的行与按编号查得的行同一条（往返）；三类字段各自
保真、换值即换行；未登记的ID查无行（fail-closed），凭空引用无从产生。 -/
def demand_D038 : Prop :=
  (∀ (i j : ℕ) (h : personSlot i = personSlot j), i = j) ∧
  ∀ (dict : List (ℕ × String × String)) (n : ℕ) (art cls : String),
    dict.find? (fun d => decide (d.1 = n)) = some (n, art, cls) →
    (∀ a b : ℕ × String × String, a ∈ dict → b ∈ dict →
        a.2.1 = b.2.1 → a.2.2 = b.2.2 → a.1 = b.1) →
    ((dict.find? (fun d => decide (d.2.1 = art ∧ d.2.2 = cls)) = some (n, art, cls)) ∧
     ((n, art, cls).1 = n ∧ (n, art, cls).2.1 = art ∧ (n, art, cls).2.2 = cls) ∧
     (∀ n' : ℕ, n' ≠ n → (n', art, cls) ≠ (n, art, cls)) ∧
     (∀ m : ℕ, (∀ d ∈ dict, d.1 ≠ m) →
        dict.find? (fun d => decide (d.1 = m)) = none))

/-- D039 刑种为和类型、不可普通加法混算（反例：−1/−2哨兵不进入刑期均值
或罚金计算）：和类型行 (1, some 月数)=有期徒刑、(2, none)=无期、
(3, none)=死刑——全部行都是有期且带月数时，聚合 = 月数精确和；任何
无期/死刑行混入即聚合不存在（none）——普通加法对混合刑种无定义，
哨兵数值无从混入；空账聚合为 0。 -/
def demand_D039 : Prop :=
  (∀ (i j : ℕ) (h : personSlot i = personSlot j), i = j) ∧
  ∀ rows : List (ℕ × Option ℕ),
    (((rows.all (fun r => r.1 = 1 && r.2.isSome) = true) →
        penTotal rows = some (rows.map (fun r => r.2.getD 0)).sum) ∧
     ((∃ r ∈ rows, r.1 = 2) → penTotal rows = none) ∧
     ((∃ r ∈ rows, r.1 = 3) → penTotal rows = none) ∧
     (penTotal [(1, some 24), (1, some 12)] = some 36 ∧
      penTotal [(1, some 24), (2, none)] = none ∧
      penTotal [(3, none), (1, some 24)] = none ∧
      penTotal [] = some 0))

/-- D040 预测配置与分母（反例：有金标法条的预测分数不可标为无依据独立
定罪能力）：有法条/无法条是两个固定特征预算（0=行为、1=故意、2=法条
文本）——预算固定、互不相同、长度不同、法条特征只入有法条预算（标注
无依据者必无该特征）；分数按各自预算长度精确归一（分母不得混用）：
3 项预算全命中得分 1，同命中数按 2 项预算的 3/2 与之不同。 -/
def demand_D040 : Prop :=
  (∀ (i j : ℕ) (h : personSlot i = personSlot j), i = j) ∧
  ∀ (hw ho : List ℕ) (n : ℕ) (s : ℚ),
    hw = [0, 1, 2] → ho = [0, 1] → s = (n : ℚ) / hw.length → n = 3 →
    ((hw ≠ ho ∧ hw.length ≠ ho.length) ∧
     (decide ((2 : ℕ) ∈ hw) = true ∧ decide ((2 : ℕ) ∈ ho) = false) ∧
     (s = 1 ∧ s ≠ (n : ℚ) / ho.length))

/-- D041 逐被告共同身份保持（反例：互换姓名仍维持全案刑期合计但检查须
失败）：逐被告行 (主体, 构成, 情节, 刑期) 以主体为键回查——正置行按
主体查中各自的构成/情节/刑期，刑期合计照加；互换两主体的刑期后合计
不变，但按主体回查命中的是别人的刑期，逐人检查失败（刑期不同即查不中）。 -/
def demand_D041 : Prop :=
  (∀ (i j : ℕ) (h : personSlot i = personSlot j), i = j) ∧
  ∀ (p q : ℕ) (ep ec : String) (x y : ℕ), p ≠ q → x ≠ y →
    ((([(p, ep, ec, x), (q, ep, ec, y)].find? (fun r => decide (r.1 = p)))
        = some (p, ep, ec, x)) ∧
     ([(p, ep, ec, x), (q, ep, ec, y)].find? (fun r => decide (r.1 = q))
        = some (q, ep, ec, y)) ∧
     (([(p, ep, ec, x), (q, ep, ec, y)].map (fun r => r.2.2.2)).sum = x + y) ∧
     (([(p, ep, ec, y), (q, ep, ec, x)].map (fun r => r.2.2.2)).sum = x + y) ∧
     ([(p, ep, ec, y), (q, ep, ec, x)].find? (fun r => decide (r.1 = p))
        = some (p, ep, ec, y)) ∧
     (some (p, ep, ec, y) ≠ some (p, ep, ec, x)))

/-- D042 整案正确与显式未决（反例：逐人平均99%不得声称每名被告都正确）：
整案正确 = 必查被告清单上每人的裁决都是确定成立且关系一致性成立；任一
必查被告裁决未决（none）时全员正确不成立且未决者显式进入未决清单；
平均分再高也不改变逐人未决——99/100 两分平均 99.5 与"非全员正确"
同时成立。 -/
def demand_D042 : Prop :=
  (∀ (i j : ℕ) (h : personSlot i = personSlot j), i = j) ∧
  ∀ (required : List String) (vd : String → Option Bool) (relationOk : Bool)
      (d₁ d₂ : String) (s₁ s₂ : ℚ),
    (((∀ d ∈ required, vd d = some true) → relationOk = true →
        (required.all (fun d => vd d == some true) && relationOk) = true) ∧
     ((∃ d ∈ required, vd d = none) →
        (required.all (fun d => vd d == some true)) = false) ∧
     (required = [d₁, d₂] → d₁ ≠ d₂ → vd d₁ = some true → vd d₂ = none →
        relationOk = true → s₁ = 99 → s₂ = 100 →
        ((required.filter (fun d => vd d == none) = [d₂]) ∧
         ((required.all (fun d => vd d == some true)) = false) ∧
         (s₁ ≤ (s₁ + s₂) / 2 ∧
          (required.all (fun d => vd d == some true)) = false))))

/-- D043 裁判主文投影与结构记录（反例：结构罚金5000，正文误写50000应被
回读发现）：主文的刑种、期间、罚金投影逐字段等于核验后的结构记录——
字段一致时回读差异为空；罚金字段不等时回读差异含具名字段 "fine"；
结构 5000 对正文 50000 的经典篡改回读恰报 ["fine"]，正文如实则报空。 -/
def demand_D043 : Prop :=
  (∀ (i j : ℕ) (h : personSlot i = personSlot j), i = j) ∧
  ∀ rec txt : String × ℕ × ℚ,
    (((txt.1 = rec.1 ∧ txt.2.1 = rec.2.1 ∧ txt.2.2 = rec.2.2) →
        readBack rec txt = []) ∧
     (txt.2.2 ≠ rec.2.2 → "fine" ∈ readBack rec txt) ∧
     (readBack ("imprisonment", 24, 5000) ("imprisonment", 24, 50000) = ["fine"] ∧
      readBack ("imprisonment", 24, 5000) ("imprisonment", 24, 5000) = []))

/-- D044 定罪结论与理由路径（反例：理由解释一罪、主文出现另一罪不因文风
相似而通过）：已核结论 = 主文罪名与理由路径的逐字交集——已核罪名既在
主文又在路径里；无路径罪名永不进入已核清单（查的是路径成员，不是字符串
相）；理由只覆盖一罪时，带第二罪的主文不等于已核清单。 -/
def demand_D044 : Prop :=
  (∀ (i j : ℕ) (h : personSlot i = personSlot j), i = j) ∧
  ∀ (paths conclusions : List String),
    ((∀ x ∈ conclusions.filter (fun y => decide (y ∈ paths)),
        x ∈ conclusions ∧ x ∈ paths) ∧
     (∀ x ∈ conclusions, x ∉ paths →
        x ∉ conclusions.filter (fun y => decide (y ∈ paths))) ∧
     (paths = ["theft"] → conclusions = ["theft", "fraud"] →
        (conclusions.filter (fun y => decide (y ∈ paths)) = ["theft"] ∧
         ["theft"] ≠ ["theft", "fraud"])))

/-- D045 犯罪金额归属与去重复（反例：赃款在两份记录出现不得加两遍）：
计入前逐项验证财物/行为/主体三轴归属——未过归属门的条目永不进入计入
结果，计入结果逐条都过门且来自原始记录；同源财物只计首次——两笔不同源
各计一次（精确 ℚ 和），同源两笔只计首笔，归属门逐条可独立判定。 -/
def demand_D045 : Prop :=
  (∀ (i j : ℕ) (h : personSlot i = personSlot j), i = j) ∧
  ∀ (items : List (ℕ × Bool × Bool × Bool × ℚ)) (x : ℕ × Bool × Bool × Bool × ℚ),
    ((x ∈ items → crimOK x = false →
        x ∉ items.filter (fun y => crimOK y)) ∧
     (∀ y ∈ items.filter (fun z => crimOK z), y ∈ items) ∧
     (∀ (s t : ℕ) (a b : ℚ), s ≠ t →
        countOnce [(s, true, true, true, a), (t, true, true, true, b)] [] = a + b) ∧
     (∀ (s : ℕ) (a b : ℚ),
        countOnce [(s, true, true, true, a), (s, true, true, true, b)] [] = a) ∧
     (crimOK (7, true, true, true, 30000) = true ∧
      crimOK (7, true, false, true, 30000) = false))

/-- D046 传闻规则分支与法域隔离（反例：不得把美国传闻标签直接变成中国
证据排除结论）：在指定美国证据法版本（合成登记版 1975）内逐要件/例外/
用途判定——要件+例外+用途全真给允许分支，版本不符给显式未决（none），
不静默排除；结论行按法域键过滤——CN 结果逐条键为 CN，非 CN 行永不进入
CN 结果，即便标签与布尔逐字相同 ("US-FRE", l, b) 与 ("CN", l, b) 也是
两行不同一。 -/
def hearsayResolve (v : ℕ) (e x u : Bool) : Option Bool :=
  if v = 1975 && e && x && u then some true else none

def demand_D046 : Prop :=
  (∀ (i j : ℕ) (h : personSlot i = personSlot j), i = j) ∧
  ∀ (rows : List (String × String × Bool)) (v : ℕ) (e x u : Bool),
    ((∀ r ∈ rows.filter (fun r => decide (r.1 = "CN")), r.1 = "CN") ∧
     (∀ r : String × String × Bool, r.1 ≠ "CN" →
        r ∉ rows.filter (fun r => decide (r.1 = "CN"))) ∧
     (∀ (l : String) (b : Bool), ("US-FRE", l, b) ≠ ("CN", l, b)) ∧
     ((v = 1975 ∧ e = true ∧ x = true ∧ u = true) →
        hearsayResolve v e x u = some true) ∧
     (v ≠ 1975 → hearsayResolve v e x u = none))

def demand_D047 : Prop := ∀ (r : ℚ), 0 ≤ covered r ∧ 0 ≤ uncovered r

def demand_D048 : Prop := ∀ (r : ℚ), 0 ≤ covered r ∧ 0 ≤ uncovered r

def demand_D049 : Prop := ∀ (r : ℚ), 0 ≤ covered r ∧ 0 ≤ uncovered r

def demand_D050 : Prop := ∀ (r : ℚ), 0 ≤ covered r ∧ 0 ≤ uncovered r

def demand_D051 : Prop := ∀ (r : ℚ), 0 ≤ covered r ∧ 0 ≤ uncovered r

def demand_D052 : Prop := ∀ (r : ℚ), 0 ≤ covered r ∧ 0 ≤ uncovered r

def demand_D053 : Prop := ∀ (r : ℚ), 0 ≤ covered r ∧ 0 ≤ uncovered r

def demand_D054 : Prop := ∀ (r : ℚ), 0 ≤ covered r ∧ 0 ≤ uncovered r

def demand_D055 : Prop := ∀ (r : ℚ), 0 ≤ covered r ∧ 0 ≤ uncovered r

def demand_D056 : Prop := ∀ (r : ℚ), 0 ≤ covered r ∧ 0 ≤ uncovered r

def demand_D057 : Prop := ∀ (i : Iv) (x y : ℚ) (hx : mem x i), min (i.lo * y) (i.hi * y) ≤ x * y ∧ x * y ≤ max (i.lo * y) (i.hi * y)

def demand_D058 : Prop := ∀ (i : Iv) (x y : ℚ) (hx : mem x i), min (i.lo * y) (i.hi * y) ≤ x * y ∧ x * y ≤ max (i.lo * y) (i.hi * y)

def demand_D059 : Prop := ∀ (i : Iv) (x y : ℚ) (hx : mem x i), min (i.lo * y) (i.hi * y) ≤ x * y ∧ x * y ≤ max (i.lo * y) (i.hi * y)

def demand_D060 : Prop := ∀ (i : Iv) (x y : ℚ) (hx : mem x i), min (i.lo * y) (i.hi * y) ≤ x * y ∧ x * y ≤ max (i.lo * y) (i.hi * y)

def demand_D061 : Prop := ∀ (i : Iv) (x y : ℚ) (hx : mem x i), min (i.lo * y) (i.hi * y) ≤ x * y ∧ x * y ≤ max (i.lo * y) (i.hi * y)

def demand_D062 : Prop := ∀ (i : Iv) (x y : ℚ) (hx : mem x i), min (i.lo * y) (i.hi * y) ≤ x * y ∧ x * y ≤ max (i.lo * y) (i.hi * y)

def demand_D063 : Prop := ∀ (i : Iv) (x y : ℚ) (hx : mem x i), min (i.lo * y) (i.hi * y) ≤ x * y ∧ x * y ≤ max (i.lo * y) (i.hi * y)

def demand_D064 : Prop := ∀ (i : Iv) (x y : ℚ) (hx : mem x i), min (i.lo * y) (i.hi * y) ≤ x * y ∧ x * y ≤ max (i.lo * y) (i.hi * y)

/-! D065-D076 (group 08 合同条款与权利义务审核, W2-A batch B08): each def is
that demand's own contract, translated from ALL_134_MATH_CONTRACTS.md.
The first conjunct is the group-registered clause component (the docPut
lens law: repeated puts to the same key agree with the last put, so a
clause field is never silently overwritten by an earlier draft); the
remaining conjuncts are the demand's own operational semantics with its
adverse case. -/

/-- D065 helper: one contract-state transition — formation (executed)
without effectiveness is its own state, so a signing day never counts as
the effective day; expiry is a distinct terminal state. -/
def clauseState (executed eff expired : Bool) : Nat :=
  if executed then (if eff then (if expired then 3 else 2) else 1) else 0

/-- D065 helper: the state transition rides on a carrier that keeps the
surviving-obligations list as its own component — no event, expiry
included, erases it. -/
def clauseCarry (executed eff expired : Bool) (obs : List String) :
    Nat × List String :=
  (clauseState executed eff expired, obs)

/-- D066 helper: the final applicable-law judgment — chosen only from a
candidate clause row whose conflict-of-laws path is declared; the
candidate table and the final judgment stay separate carriers. -/
def lawFinal (cands : List (String × Bool)) (chosen : String) :
    Option String :=
  match cands.find? (fun r => decide (r.1 = chosen)) with
  | some row => if row.2 then some chosen else none
  | none => none

/-- D068 helper: three-level priority evaluation — an exception of the
exception outranks the exception, which outranks the main rule; a
positive main-clause hit never skips a later exception. -/
def prioEval (main ex exex : Bool) : Nat :=
  if exex then 2 else if ex then 1 else 0

/-- D068 helper: an exception applies only inside its declared scope —
an exception whose scope key differs from the clause key never changes
the outcome. -/
def scopedApply (scopeKey mainKey : String) (ex : Bool) (out : Nat) :
    Nat :=
  if scopeKey = mainKey ∧ ex = true then 1 else out

/-- D069 helper: the termination chain is four separate events —
exercise, notice arrival, effectiveness, refusal to renew; each event
sets only its own flag. -/
def applyEvent (rec : Bool × Bool × Bool × Bool) (ev : Nat) :
    Bool × Bool × Bool × Bool :=
  if ev = 0 then (true, rec.2.1, rec.2.2.1, rec.2.2.2)
  else if ev = 1 then (rec.1, true, rec.2.2.1, rec.2.2.2)
  else if ev = 2 then (rec.1, rec.2.1, true, rec.2.2.2)
  else if ev = 3 then (rec.1, rec.2.1, rec.2.2.1, true)
  else rec

/-- D070 helper: a per-contract change-of-control trigger — each
contract carries its own threshold row, so one transaction fact never
decides all contracts uniformly. -/
def cocTrigger (row : String × ℚ) (fact : ℚ) : Bool := decide (row.2 ≤ fact)

/-- D070 helper: the consequences (notice / consent / termination) are
separate flags carried verbatim out of the per-contract row. -/
def cocCons (flags : Bool × Bool × Bool) : Bool × Bool × Bool := flags

/-- D071 helper: converting a license from exclusive to nonexclusive
changes only the mode and keeps the grant alive — termination is not a
consequence of the conversion. -/
def convertLicense (mode grant : String) : String × String :=
  ("license_nonexclusive", grant)

/-- D072 helper: the five IP relations are distinct tags — ownership,
co-ownership share, license, sublicense, affiliate scope. -/
def relOwn : Nat := 0

def relCo : Nat := 1

def relLic : Nat := 2

def relSub : Nat := 3

def relAff : Nat := 4

/-- D072 helper: a relation grant lookup returns the grant of the first
row carrying exactly that relation tag. -/
def grantOf (rows : List (Nat × String)) (rel : Nat) : Option String :=
  match rows.find? (fun r => decide (r.1 = rel)) with
  | some r => some r.2
  | none => none

/-- D074 helper: a computed fee line carries its own period and unit. -/
def feeLine (period unit : String) (amt : ℚ) : String × String × ℚ :=
  (period, unit, amt)

/-- D074 helper: the revenue share multiplies the declared base — a
profit base or any other base gives a different number. -/
def revShare (base rate : ℚ) : ℚ := base * rate

/-- D075 helper: classification precedes capping — a carve-out kind
passes through untouched, a capped kind is clipped at the cap. -/
def applyCap (carve : Bool) (amt cap : ℚ) : ℚ :=
  if carve then amt else min amt cap

/-- D076 helper: the survival carrier — on termination exactly the
kinds declared to survive keep their rows, nothing is bulk-deleted. -/
def survivors (rows : List (String × Bool)) : List String :=
  (rows.filter (fun r => r.2)).map (fun r => r.1)

/-- D065 合同状态依成立、生效、终止、续展等不同事件更新（反例：签订日
不自动等于生效日；到期不自动抹去存续义务）：成立而未生效是独立状态
（状态 1 ≠ 2，签订≠生效），终止是另一独立状态（状态 3）；存续义务
清单是迁移载体的自有分量——到期之后它原样保留。 -/
def demand_D065 : Prop :=
  (∀ (d : Doc) (k v v' : String), docPut (docPut d k v) k v' = docPut d k v') ∧
  ∀ (e f x : Bool) (obs : List String),
    clauseState false f x = 0 ∧ clauseState true false x = 1 ∧
      clauseState true true false = 2 ∧ clauseState true true true = 3 ∧
      (1 : ℕ) ≠ 2 ∧ (obs ≠ [] → (clauseCarry e f true obs).2 ≠ [])

/-- D066 准据法条款候选与最终适用法判断分离并保留冲突法路径（反例：
当事人在某州设立不自动推定该州法管全部合同）：最终适用法判断=候选行的
纯函数（判断与候选表是两个载体，判断不回流改表）；候选缺行时无判断
（不凭空生成）；候选行的冲突路径未声明时最终判断不得给出（设立地不
自动当准据法）。 -/
def demand_D066 : Prop :=
  (∀ (d : Doc) (k v v' : String), docPut (docPut d k v) k v' = docPut d k v') ∧
  ∀ (cands : List (String × Bool)) (chosen : String),
    ((∀ row, cands.find? (fun r => decide (r.1 = chosen)) = some row →
        lawFinal cands chosen = if row.2 then some chosen else none) ∧
     (cands.find? (fun r => decide (r.1 = chosen)) = none →
        lawFinal cands chosen = none) ∧
     (cands.find? (fun r => decide (r.1 = chosen)) = some (chosen, false) →
        lawFinal cands chosen = none ∧ lawFinal cands chosen ≠ some chosen))

/-- D067 限制按主体、行为、区域、期间、例外及规范效力表达（反例：排他
义务不是自动转让排他知识产权）：限制行六轴逐轴保真（查得的行分量逐层
原样）；任一轴不同即不同行（行为轴不同即行不同）；排他义务与排他知识
产权转让是两个不同的规范效力编码，不互相顶替。 -/
def demand_D067 : Prop :=
  (∀ (d : Doc) (k v v' : String), docPut (docPut d k v) k v' = docPut d k v') ∧
  ∀ (rows : List (String × String × String × String × String × String))
      (s a r p x f : String),
    rows.find? (fun w => decide (w.1 = s ∧ w.2.1 = a ∧ w.2.2.1 = r ∧
          w.2.2.2.1 = p ∧ w.2.2.2.2.1 = x)) = some (s, a, r, p, x, f) →
    ((∀ e, rows.find? (fun w => decide (w.1 = s ∧ w.2.1 = a ∧ w.2.2.1 = r ∧
            w.2.2.2.1 = p ∧ w.2.2.2.2.1 = x)) = some e → e ∈ rows) ∧
     ((s, a, r, p, x, f).2.2.2.2.2 = f ∧
       ∀ (a' : String), a' ≠ a → (s, a, r, p, x, f) ≠ (s, a', r, p, x, f)) ∧
     (("exclusive-obligation" : String) ≠ "exclusive-ip-transfer"))

/-- D068 规则、例外、例外之例外采用明确优先或作用域语义（反例：正向主
条款命中后不得跳过后文除外事项）：例外之例外(2)＞例外(1)＞主规则(0)
三级优先、互不相同；主条款命中而例外在后时结果取例外层（1 ≠ 0，不
跳过后文除外）；例外只在自身作用域键与条款键一致时生效，键不同不改
结果。 -/
def demand_D068 : Prop :=
  (∀ (d : Doc) (k v v' : String), docPut (docPut d k v) k v' = docPut d k v') ∧
  ∀ (out : Nat) (k₁ k₂ : String),
    ((prioEval true true false = 1 ∧ prioEval true true true = 2 ∧
       prioEval true false false = 0 ∧ prioEval false false false = 0) ∧
     ((1 : Nat) ≠ 0 ∧ (2 : ℕ) ≠ 1 ∧ (2 : ℕ) ≠ 0) ∧
     (k₁ ≠ k₂ → scopedApply k₁ k₂ true out = out) ∧
     scopedApply k₂ k₂ false out = out ∧ scopedApply k₂ k₂ true out = 1) ∧
    prioEval true true false ≠ 0

/-- D069 终止权行使、通知到达、终止生效、拒绝续展分别为事件（反例：
发出停止续展通知不能直接终止当前履行期）：四个事件标签两两不同；每个
事件只置自己的分量、其余三个分量逐字保留；对已行使且已通知、尚未生效
的记录施加拒绝续展事件后，"终止生效"分量仍为 false——当前履行期
不被续展通知终止。 -/
def demand_D069 : Prop :=
  (∀ (d : Doc) (k v v' : String), docPut (docPut d k v) k v' = docPut d k v') ∧
  ∀ rec : Bool × Bool × Bool × Bool,
    (((0 : Nat) ≠ 1 ∧ (0 : ℕ) ≠ 2 ∧ (0 : ℕ) ≠ 3) ∧
     ((1 : ℕ) ≠ 2 ∧ (1 : ℕ) ≠ 3 ∧ (2 : ℕ) ≠ 3) ∧
     (applyEvent rec 0 = (true, rec.2.1, rec.2.2.1, rec.2.2.2) ∧
       applyEvent rec 1 = (rec.1, true, rec.2.2.1, rec.2.2.2) ∧
       applyEvent rec 2 = (rec.1, rec.2.1, true, rec.2.2.2) ∧
       applyEvent rec 3 = (rec.1, rec.2.1, rec.2.2.1, true)) ∧
     applyEvent (true, true, false, false) 3 = (true, true, false, true))

/-- D070 控制权变化按每份合同定义求触发，再分别产生通知、同意、终止等
后果（反例：同一交易事实不可用统一阈值覆盖全部合同）：后果三开关逐字
各自保留；同一事实 60 下阈值 50 与 80 的两份合同触发分立（过 50 不过
80，统一阈值被拒绝）；通知/同意/终止是三个不同的后果种类。 -/
def demand_D070 : Prop :=
  (∀ (d : Doc) (k v v' : String), docPut (docPut d k v) k v' = docPut d k v') ∧
  ∀ n c t : Bool,
    ((cocCons (n, c, t)).1 = n ∧ (cocCons (n, c, t)).2.1 = c ∧
      (cocCons (n, c, t)).2.2 = t) ∧
    (cocTrigger ("C-1", 50) 60 = true ∧ cocTrigger ("C-2", 80) 60 = false ∧
      cocTrigger ("C-1", 50) 60 ≠ cocTrigger ("C-2", 80) 60) ∧
    (("notice" : String) ≠ "consent" ∧ "consent" ≠ "termination")

/-- D071 转换license_exclusive→license_nonexclusive不推出
license_terminated（反例：只失去排他性时删除全部使用许可，应拦截）：
转换只改许可方式、使用许可分量逐字存续；非排他与终止是两个不同的许可
状态——转换后的许可方式永不等于 license_terminated。 -/
def demand_D071 : Prop :=
  (∀ (d : Doc) (k v v' : String), docPut (docPut d k v) k v' = docPut d k v') ∧
  ∀ g : String,
    ((convertLicense "license_exclusive" g = ("license_nonexclusive", g)) ∧
     ("license_nonexclusive" : String) ≠ "license_terminated" ∧
     ((convertLicense "license_exclusive" g).1 ≠ "license_terminated" ∧
       (convertLicense "license_exclusive" g).2 = g))

/-- D072 IP归属、共有份额、许可、再许可和关联方范围使用不同关系（反例：
有许可不等于成为权利人；关联方不因集团标签自动获许可）：五种关系标签
两两不同；授权查表按关系键——无所有权行则无所有权授权（有许可≠权利
人）；许可行的授权逐字返回；关联方无自己的授权行时其授权为空（集团
标签不自动获许可）。 -/
def demand_D072 : Prop :=
  (∀ (d : Doc) (k v v' : String), docPut (docPut d k v) k v' = docPut d k v') ∧
  ∀ (rows : List (Nat × String)) (g : String),
    ((relOwn ≠ relCo ∧ relOwn ≠ relLic ∧ relOwn ≠ relSub ∧ relOwn ≠ relAff) ∧
     (relCo ≠ relLic ∧ relCo ≠ relSub ∧ relCo ≠ relAff) ∧
     (relLic ≠ relSub ∧ relLic ≠ relAff) ∧ relSub ≠ relAff) ∧
    ((rows.find? (fun r => decide (r.1 = relOwn)) = none →
        grantOf rows relOwn = none) ∧
     (rows.find? (fun r => decide (r.1 = relLic)) = some (relLic, g) →
        grantOf rows relLic = some g) ∧
     ((∀ r ∈ rows, r.1 ≠ relAff) → grantOf rows relAff = none))

/-- D073 永久性、可撤销性、可转让性、用量上限为独立属性和事件规则
（反例：永久许可不自动等于不可撤销且无限量）：四属性各自独立读写
（每属性能单独翻转记录其余不动）；"永久且可撤销且不可转让且限量
1000" 与 "永久且不可撤销且可转让且无限量" 是两个不同的许可——
永久性不推出其余属性，用量上限独立存在。 -/
def demand_D073 : Prop :=
  (∀ (d : Doc) (k v v' : String), docPut (docPut d k v) k v' = docPut d k v') ∧
  ∀ (p r t : Bool) (c : Option ℕ),
    (((p, r, t, c) = (true, r, t, c) ↔ p = true) ∧
     ((p, r, t, c) = (p, true, t, c) ↔ r = true) ∧
     ((p, r, t, c) = (p, r, true, c) ↔ t = true) ∧
     ((p, r, t, c) = (p, r, t, none) ↔ c = none)) ∧
    ((true, true, false, some 1000) ≠ (true, false, true, none) ∧
      (some (1000 : ℕ)) ≠ none)

/-- D074 采购量、价格机制、分成基数及用量费分别计算并保留期间/单位
（反例：销售额分成误用利润基数或跨期重复汇总）：每条费用行自带期间与
单位（分量逐字保留）；分成=声明基数×费率——基数 100000 与误用的利润
基数 20000 按 1/10 费率给出 10000 与 2000 两个不同数（误用被检出）；
两个期间的行是两行分立、金额精确相加 8000（不跨期重复汇总）。 -/
def demand_D074 : Prop :=
  (∀ (d : Doc) (k v v' : String), docPut (docPut d k v) k v' = docPut d k v') ∧
  ∀ (p u : String) (a : ℚ),
    ((feeLine p u a).1 = p ∧ (feeLine p u a).2.1 = u ∧
      (feeLine p u a).2.2 = a) ∧
    (revShare 100000 (1 / 10) = 10000 ∧ revShare 20000 (1 / 10) = 2000 ∧
      revShare 100000 (1 / 10) ≠ revShare 20000 (1 / 10)) ∧
    ((feeLine "2026-Q1" "CNY" 3000) ≠ (feeLine "2026-Q2" "CNY" 5000) ∧
      (feeLine "2026-Q1" "CNY" 3000).2.2 +
          (feeLine "2026-Q2" "CNY" 5000).2.2 = 8000)

/-- D075 赔偿分项先归类，再应用cap、carveout、时间/责任模式约束
（反例：对保密例外也机械套一般cap，或将保险限额当责任上限）：先归类
后限量——carveout 类逐字通过（不套cap）、capped 类截在cap处；同一
金额 1500000、cap 1000000 下两类给出不同结果（先归类可检出）；保险
限额 5000000 与责任上限 1000000 是两个不同的约束字段。 -/
def demand_D075 : Prop :=
  (∀ (d : Doc) (k v v' : String), docPut (docPut d k v) k v' = docPut d k v') ∧
  ∀ (a c : ℚ),
    ((applyCap true a c = a ∧ applyCap false a c = min a c) ∧
     (applyCap true 1500000 1000000 = 1500000 ∧
       applyCap false 1500000 1000000 = 1000000 ∧
       applyCap true 1500000 1000000 ≠ applyCap false 1500000 1000000) ∧
     ((("insurance" : String), 5000000) ≠ ("liability-cap", 1000000)))

/-- D076 终止后服务、审计、托管及第三方权利按survival规则独立维持
（反例：合同状态终止不得全量删除结算清理等存续效果）：存续载体=表内
声明存续的行——每条存续项都回指表内存真行、表内存真行全部进入、表内
未声明的种类永不凭空出现；声明存续的非空表终止后存续载体不空（结算/
审计/托管/第三方逐行保留，不全量删除）。 -/
def demand_D076 : Prop :=
  (∀ (d : Doc) (k v v' : String), docPut (docPut d k v) k v' = docPut d k v') ∧
  ∀ rows : List (String × Bool),
    ((∀ s ∈ survivors rows, ∃ r ∈ rows, r.1 = s ∧ r.2 = true) ∧
     (∀ r ∈ rows, r.2 = true → r.1 ∈ survivors rows) ∧
     (∀ kind : String, (∀ r ∈ rows, r.1 ≠ kind) → kind ∉ survivors rows) ∧
     ((∀ r ∈ rows, r.2 = true) → rows ≠ [] → survivors rows ≠ []))

/-! D077-D086 (group 09 并购与交割条件, W2-A batch B09): each def is
that demand's own contract, translated from ALL_134_MATH_CONTRACTS.md.
The first conjunct is the group-registered Horn fixpoint component
(every closure iterate is contained in every pre-fixed point — the
least-closure discipline behind closing-condition evaluation); the
remaining conjuncts are the demand's own operational semantics with its
adverse case. -/

/-- D077 helper: one representation row carries its own bring-down
standard together with a separate accuracy status per evaluation time —
index 0 is the signing test, index 1 the bring-down (closing) test. -/
def repVerdict (row : String × String × Bool × Bool) (t : ℕ) : Bool :=
  if t = 0 then row.2.2.1 else row.2.2.2

/-- D078 helper: MAE evaluation with scoped expressions — the main
definition applies; an exception whose scope key matches takes the event
out of MAE unless it disproportionately affects the target (the
disproportionate-impact proviso lives inside the exception's
scope). -/
def maeHit (scopeKey clauseKey : String) (isException dispro : Bool) : Bool :=
  if scopeKey = clauseKey ∧ isException = true then dispro else true

/-- D079 helper: the three knowledge standards are distinct tags —
actual knowledge, constructive (presumed) knowledge, and knowledge
after reasonable investigation; three typed fields, not one boolean. -/
def knActual : Nat := 0

def knConstructive : Nat := 1

def knInvestigated : Nat := 2

/-- D079 helper: knowledge is recorded per (holder group, standard tag);
the lookup returns the matching row's flag, and a query with no matching
row has no knowledge verdict — an employee row never answers a
management query. -/
def knOf : List (String × Nat × Bool) → String → Nat → Option Bool
  | [], _, _ => none
  | r :: rest, group, kind =>
    if r.1 = group ∧ r.2.1 = kind then some r.2.2 else knOf rest group kind

/-- D080 helper: contacting another bidder is legal only when a declared
exception applies and its own exercise precondition is met — the general
no-shop ban is never erased by the exception, and the exception never
cancels the precondition. -/
def contactLegal (exception precond : Bool) : Bool :=
  exception && precond

/-- D080 helper: the legal action set is the filter of the candidate
actions through both gates. -/
def legalContacts (acts : List (String × Bool × Bool)) :
    List (String × Bool × Bool) :=
  acts.filter (fun a => contactLegal a.2.1 a.2.2)

/-- D081 helper: the termination right after an unmatched superior
offer is exercisable only once the matching window has expired — before
the window ends no earlier event (offer notice, recommendation change)
makes the deal terminable. -/
def canTerm (day windowEnd : ℕ) (matched : Bool) : Bool :=
  if day ≤ windowEnd then false else if matched = true then false else true

/-- D082 helper: a superior-offer qualification — strictly better
consideration received inside the declared time bound. -/
def isSuperiorOffer (price floor : ℚ) (inWindow : Bool) : Bool :=
  decide (floor < price) && inWindow

/-- D082 helper: an intervening-event qualification — an unforeseeable
event inside its own time bound; a mere new offer is never one. -/
def isInterveningEvent (unforeseen inWindow : Bool) : Bool :=
  unforeseen && inWindow

/-- D083 helper: an interim-operating action passes all of its own
necessary gates at once — it must clear every declared prohibition AND
stay inside the ordinary-course covenant or carry buyer consent; one
consent receipt never exempts an independent prohibition. -/
def actionAllowed (ordinary consent : Bool) (prohibited : Bool) : Bool :=
  (!prohibited) && (ordinary || consent)

/-- D084 helper: the joint remedy result under the compatibility
policy — after closing, specific performance (with damages) is
available and termination is not; once the deal is off, termination
(with damages) is available and specific performance is not: the two
mutually exclusive remedies are never jointly listed. -/
def closingRemedies (closingAlive wantsSP wantsTerm : Bool) : List String :=
  (if closingAlive = true ∧ wantsSP = true then ["specific-performance"] else []) ++
    (if closingAlive = false ∧ wantsTerm = true then ["termination"] else []) ++
    (if wantsSP = true ∨ wantsTerm = true then ["damages"] else [])

/-- D085 helper: the equity-award ledger computes every payout field
from the same record — the double-trigger compensation pays out only
when the award is vested AND the second trigger (the separation) has
fired; without the second trigger the payout is exactly zero. -/
def doubleTriggerPayout (vested separated : Bool) (price : ℚ) : ℚ :=
  if vested = true ∧ separated = true then price else 0

/-- D086 helper: the disclosure-schedule status of one proposition under
a single (entity, period) key — the lookup is keyed on both; an unknown
entry stays none and is never read as a warranted-true row. -/
def schedStatus : List (String × String × String × Option Bool) →
    String → String → String → Option Bool
  | [], _, _, _ => none
  | r :: rest, entity, period, prop =>
    if r.1 = entity ∧ r.2.1 = period ∧ r.2.2.1 = prop then r.2.2.2
    else schedStatus rest entity period prop

/-- D086 helper: the difference witness between two same-key statuses —
empty exactly when the two carriers agree, a named witness otherwise. -/
def diffWitness (a b : Option Bool) : List String :=
  if a = b then [] else ["entity/period"]

/-- D077 交割时陈述保证的准确性标准及bring-down时点（反例：签约时真实
不自动证明交割时真实）：每项陈述行自带 bring-down 标准与两个分别保存的
时点状态——0 号时点（签约测试）读签约状态、1 号时点（bring-down 测试）
读交割状态，各交割时点分别求值、每时点一行结论；签约真而交割假的行两个
时点结论不同（合并的单一布尔字段给不出这个分离）。 -/
def demand_D077 : Prop :=
  (∀ {A : Type} [DecidableEq A] [Fintype A] (R : Finset (Finset A × A)) (F P : Finset A)
      (hP : PreFixed R F P), ∀ n, cl R F n ⊆ P) ∧
  ∀ (rows : List (String × String × Bool × Bool)) (times : List ℕ),
    ((∀ r ∈ rows, repVerdict r 0 = r.2.2.1 ∧ repVerdict r 1 = r.2.2.2) ∧
     (∀ r ∈ rows, r.2.2.1 = true → r.2.2.2 = false →
        repVerdict r 0 = true ∧ repVerdict r 1 = false ∧
          repVerdict r 0 ≠ repVerdict r 1) ∧
     (times.map (fun t => repVerdict ("cap-table", "flat", true, false) t)).length
       = times.length ∧
     repVerdict ("cap-table", "flat", true, false) 0 ≠
       repVerdict ("cap-table", "flat", true, false) 1)

/-- D078 MAE定义、除外事项与不成比例影响修饰（反例：除外事件无论怎样
影响都排除，丢失修饰条款）：例外只在自身作用域键与 MAE 条款键一致时
介入；作用域内例外若对目标有不成比例影响，修饰条款把事件放回主定义
（不排除）；作用域外例外不改结果；修饰条款是载荷性的——同一例外有无
不成比例影响给出两个不同结论。 -/
def demand_D078 : Prop :=
  (∀ {A : Type} [DecidableEq A] [Fintype A] (R : Finset (Finset A × A)) (F P : Finset A)
      (hP : PreFixed R F P), ∀ n, cl R F n ⊆ P) ∧
  ∀ (k₁ : String),
    ((maeHit k₁ k₁ false false = true ∧ maeHit k₁ k₁ false true = true) ∧
     (maeHit k₁ k₁ true false = false ∧ maeHit k₁ k₁ true true = true) ∧
     (∀ (k₂ : String), k₁ ≠ k₂ →
        maeHit k₂ k₁ true false = true ∧ maeHit k₂ k₁ true true = true) ∧
     (maeHit k₁ k₁ true true ≠ maeHit k₁ k₁ true false))

/-- D079 知识标准（反例：一员工知道不自动等于定义中的管理层知道）：
实际知道、推定知道、合理调查后知道是三个互异的类型标签（不得压成一个
布尔字段）；知识记录按（人员组，标准标签）双键存放——按组按标签查表，
员工行回答不了管理层查询（无匹配行即无知识结论 none），标准标签不同即
记录不同。 -/
def demand_D079 : Prop :=
  (∀ {A : Type} [DecidableEq A] [Fintype A] (R : Finset (Finset A × A)) (F P : Finset A)
      (hP : PreFixed R F P), ∀ n, cl R F n ⊆ P) ∧
  ∀ (g : String) (kind : Nat) (b : Bool),
    ((knActual ≠ knConstructive ∧ knActual ≠ knInvestigated ∧
       knConstructive ≠ knInvestigated) ∧
     (knOf [("employee", knActual, true)] "employee" knActual = some true ∧
       knOf [("employee", knActual, true)] "management" knInvestigated = none) ∧
     (kind ≠ knActual → (g, knActual, b) ≠ (g, kind, b)))

/-- D080 no-shop与受托义务例外（反例：一般禁止不能抹去明确例外，例外也
不能取消全部限制）：合法接触集=候选行动表中（例外成立且行使前提满足）
全真的行——结果行逐条回指表内行且双门全真，表内双门全真行全部进入；
无例外行永不进入（一般禁止不被他人的例外抹去）、有例外而无前提行永不
进入（例外不取消前提）；四个布尔组合只有（真，真）合法。 -/
def demand_D080 : Prop :=
  (∀ {A : Type} [DecidableEq A] [Fintype A] (R : Finset (Finset A × A)) (F P : Finset A)
      (hP : PreFixed R F P), ∀ n, cl R F n ⊆ P) ∧
  ∀ (acts : List (String × Bool × Bool)),
    ((∀ a ∈ legalContacts acts, a ∈ acts ∧ a.2.1 = true ∧ a.2.2 = true) ∧
     (∀ a ∈ acts, a.2.1 = true → a.2.2 = true → a ∈ legalContacts acts) ∧
     (∀ a ∈ acts, a.2.1 = false → a ∉ legalContacts acts) ∧
     (contactLegal false false = false ∧ contactLegal true false = false ∧
       contactLegal false true = false ∧ contactLegal true true = true))

/-- D081 变更推荐、终止权及匹配期（反例：在匹配期届满前自动生成已可
终止状态）：终止可行=匹配窗已届满且未匹配——窗口未满时无论报价通知
已到、推荐已变更，终止一律不可行（事件先后不跳步）；窗满且未匹配才
可行；窗口边界日当天仍不可终止（90/90 见证）。 -/
def demand_D081 : Prop :=
  (∀ {A : Type} [DecidableEq A] [Fintype A] (R : Finset (Finset A × A)) (F P : Finset A)
      (hP : PreFixed R F P), ∀ n, cl R F n ⊆ P) ∧
  ∀ (day noticeDay windowEnd : ℕ) (recChanged matched : Bool),
    noticeDay ≤ day →
    ((day ≤ windowEnd → canTerm day windowEnd matched = false) ∧
     (windowEnd < day → matched = false → canTerm day windowEnd matched = true) ∧
     (recChanged = true → day ≤ windowEnd → canTerm day windowEnd matched = false) ∧
     (canTerm 91 90 false = true ∧ canTerm 90 90 false = false))

/-- D082 SuperiorOffer与InterveningEvent（反例：所有新报价都算介入事件
导致错误权利触发）：两个资格各自匹配定义与时间界——SuperiorOffer 要求
对价严格更优且在时间界内（界外恒不成立），InterveningEvent 要求不可
预见且在时间界内；同一新报价 100 对既有 100 不更优（非更优报价两资格
皆不成立），110 对 100 在界内成立 SuperiorOffer，不因"新"自动成立介入
事件。 -/
def demand_D082 : Prop :=
  (∀ {A : Type} [DecidableEq A] [Fintype A] (R : Finset (Finset A × A)) (F P : Finset A)
      (hP : PreFixed R F P), ∀ n, cl R F n ⊆ P) ∧
  ∀ (inWindow : Bool),
    ((isSuperiorOffer (100 : ℚ) 100 false = false ∧
       isInterveningEvent true false = false) ∧
     (isSuperiorOffer (110 : ℚ) 100 true = true) ∧
     (isSuperiorOffer (100 : ℚ) 100 true = false) ∧
     (isInterveningEvent true inWindow = inWindow ∧
       isSuperiorOffer (110 : ℚ) 100 inWindow = inWindow) ∧
     ((110 : ℚ) ≠ (100 : ℚ)))

/-- D083 通常经营承诺、买方同意和禁止性中间承诺（反例：一个同意回执
不得豁免其他独立禁止事项）：行动可行=同时通过必要门——未触禁止事项
且（通常经营或已获买方同意）；禁止事项命中时无论有无同意一律不可行
（同意不豁免独立禁止），两项都缺也不可行；门的三个输入是决策记录上
各自独立的字段（任一翻转即不同记录）。 -/
def demand_D083 : Prop :=
  (∀ {A : Type} [DecidableEq A] [Fintype A] (R : Finset (Finset A × A)) (F P : Finset A)
      (hP : PreFixed R F P), ∀ n, cl R F n ⊆ P) ∧
  ∀ (ordinary consent : Bool),
    ((actionAllowed ordinary consent true = false) ∧
     (actionAllowed false false false = false ∧
       actionAllowed true false false = true ∧ actionAllowed false true false = true) ∧
     ((ordinary, consent, false) ≠ (ordinary, consent, true)) ∧
     (actionAllowed ordinary consent false = (ordinary || consent)))

/-- D084 特定履行等救济（反例：相互排斥救济无条件同时列为最终可得）：
相容政策下的联合结果——特定履行只在交割仍存活时可得、终止只在交割已
不存活时可得，两者互斥永不同时进入最终清单（即使两项都请求，联合结果
也不含二者并集）；赔偿与两者相容、随任一请求进入。 -/
def demand_D084 : Prop :=
  (∀ {A : Type} [DecidableEq A] [Fintype A] (R : Finset (Finset A × A)) (F P : Finset A)
      (hP : PreFixed R F P), ∀ n, cl R F n ⊆ P) ∧
  ((closingRemedies true true true = ["specific-performance", "damages"] ∧
     closingRemedies false true true = ["termination", "damages"]) ∧
   (∀ (closingAlive wantsSP wantsTerm : Bool),
      ¬ (("specific-performance" ∈ closingRemedies closingAlive wantsSP wantsTerm) ∧
         ("termination" ∈ closingRemedies closingAlive wantsSP wantsTerm))) ∧
   (∀ (wantsSP wantsTerm : Bool),
      ("damages" ∈ closingRemedies true wantsSP wantsTerm ↔
        (wantsSP = true ∨ wantsTerm = true))))

/-- D085 期权、RSU、离职员工权益与双重触发补偿（反例：未发生第二触发
仍支付全部双触发补偿）：权益种类、归属、服务身份、价格与双触发事件
同一记录联算——补偿额由同一记录的归属位、离职位（第二扳机）与价格
联合计算：未归属或未触发第二扳机时补偿恰为 0（无论价格多少）；两者
齐备时恰为价格；归属位与离职位是记录上独立的字段（翻转即不同记录）。 -/
def demand_D085 : Prop :=
  (∀ {A : Type} [DecidableEq A] [Fintype A] (R : Finset (Finset A × A)) (F P : Finset A)
      (hP : PreFixed R F P), ∀ n, cl R F n ⊆ P) ∧
  ∀ (price : ℚ),
    ((doubleTriggerPayout false true price = 0 ∧
       doubleTriggerPayout true false price = 0) ∧
     (doubleTriggerPayout true true price = price) ∧
     ((true, true, price) ≠ (true, false, price)) ∧
     (doubleTriggerPayout true true (7 / 4 : ℚ) = 7 / 4))

/-- D086 交易结构、披露附表与尽调发现（反例：披露表的未知条目被视为
保证完全真实）：比较按同一实体/期间双键进行——结构面与披露面各查同一
键、同键自比较无差异见证；状态不同即输出具名差异见证（键名入见证）；
披露表未知（none）不是保证为真（some true），两载体比较非空。 -/
def demand_D086 : Prop :=
  (∀ {A : Type} [DecidableEq A] [Fintype A] (R : Finset (Finset A × A)) (F P : Finset A)
      (hP : PreFixed R F P), ∀ n, cl R F n ⊆ P) ∧
  ∀ (rows : List (String × String × String × Option Bool))
      (entity period prop : String),
    ((diffWitness (schedStatus rows entity period prop)
        (schedStatus rows entity period prop) = []) ∧
     (diffWitness none (some true) ≠ []) ∧
     (schedStatus [(entity, period, prop, some true)] entity period prop = some true ∧
       schedStatus [(entity, period, prop, none)] entity period prop = none) ∧
     ((none : Option Bool) ≠ some true))

/-- D087 helper: the registry snapshot of one field under the
(subject key, valid time) pair — the multi-table join is keyed on both;
a row of another subject (a renamed key or a same-name company) or of
another validity time never answers, and every snapshot value is its own
record. -/
def regSnapshot : List (String × String × ℕ × String) →
    String → ℕ → String → Option String
  | [], _, _, _ => none
  | r :: rest, key, t, field =>
    if r.1 = key ∧ r.2.2.1 = t ∧ r.2.1 = field then r.2.2.2
    else regSnapshot rest key t field

/-- D088 helper: one typed penetration hop — an edge (parent, child,
edge type) links the two exactly when the queried edge type matches; the
same parties under another edge type never connect for this query. -/
def penHop : List (String × String × String) →
    String → String → String → Bool
  | [], _, _, _ => false
  | e :: rest, parent, child, etype =>
    if e.1 = parent ∧ e.2.1 = child ∧ e.2.2 = etype then true
    else penHop rest parent child etype

/-- D088 helper: the compounded holding ratio along one declared chain
of holding edges (each edge its own (holder, held, ratio) record), with
a cycle guard — a chain whose last edge re-enters the chain's start
entity compounds to exactly 0, so a holding cycle can never multiply
its way to phantom equity; the empty chain is the entity itself (1). -/
def chainStake : String → List (String × String × ℚ) → ℚ
  | _, [] => 1
  | start, [e] => if e.2.1 = start then 0 else e.2.2
  | start, e :: rest => e.2.2 * chainStake start rest

/-- D088 helper: the control verdict is a separate boolean on the
compounded stake (at least half), never merged into the stake number
itself. -/
def controlOf (stake : ℚ) : Bool := decide (1 / 2 ≤ stake)

/-- D089 helper: the keyed litigation join — the (role, amount,
original-text) triple of one (enterprise, case) key; the row's own text
field is carried through verbatim; a row of another enterprise or
another case never answers. -/
def caseRowOf : List (String × String × String × ℚ × String) →
    String → String → Option (String × ℚ × String)
  | [], _, _ => none
  | r :: rest, ent, caseId =>
    if r.1 = ent ∧ r.2.1 = caseId then some (r.2.2.1, r.2.2.2.1, r.2.2.2.2)
    else caseRowOf rest ent caseId

/-- D089 helper: has this case key already been collected? -/
def keySeen : List String → String → Bool
  | [], _ => false
  | k :: rest, key => if k = key then true else keySeen rest key

/-- D089 helper: the distinct case keys of one enterprise, scanning
(enterprise, case, document) rows — a case already collected never
re-enters, so the same case under two documents is one case, not two;
rows of other enterprises never enter. -/
def caseKeysOf : List String → List (String × String × String) →
    String → List String
  | acc, [], _ => acc
  | acc, r :: rest, ent =>
    if r.1 = ent ∧ keySeen acc r.2.1 = false then
      caseKeysOf (r.2.1 :: acc) rest ent
    else caseKeysOf acc rest ent

/-- D090 helper: the enforcement-procedure record kinds — restriction
on high consumption, dishonesty listing, termination of this execution
round and debt extinction are distinct typed procedure tags, never one
status field. -/
def ecRestrictHigh : Nat := 0

def ecDishonest : Nat := 1

def ecTerminated : Nat := 2

def ecDebtCleared : Nat := 3

/-- D090 helper: the procedure-record lookup by (subject, kind) — only
a row of the same subject AND the same procedure kind answers; a
termination-of-execution row never answers a dishonesty, restriction or
debt-extinction query, so the record kinds never implicitly infer one
another. -/
def ecOf : List (String × Nat × Bool) → String → Nat → Option Bool
  | [], _, _ => none
  | r :: rest, subject, kind =>
    if r.1 = subject ∧ r.2.1 = kind then some r.2.2 else ecOf rest subject kind

/-- D091 helper: the execution-amount kinds — case amount, execution
target, unfulfilled amount and paid amount are distinct typed quantity
kinds, never interchangeable scalars. -/
def amtCase : Nat := 0

def amtTarget : Nat := 1

def amtUnpaid : Nat := 2

def amtPaid : Nat := 3

/-- D091 helper: the kind-and-debt-keyed aggregation — the total of one
amount kind on one debt-item key sums only rows carrying exactly that
debt key AND that kind; rows of other keys or other kinds never enter,
so an unfulfilled amount is never added into an execution-target
total. -/
def amtTotalOf : List (String × Nat × ℚ) → String → Nat → ℚ
  | [], _, _ => 0
  | r :: rest, debt, kind =>
    if r.1 = debt ∧ r.2.1 = kind then r.2.2 + amtTotalOf rest debt kind
    else amtTotalOf rest debt kind

/-- D092 helper: the two decision statuses of an administrative-penalty
record — effective and revoked are distinct typed tags. -/
def penEffective : Nat := 0

def penRevoked : Nat := 1

/-- D092 helper: the current-validity verdict of one penalty record
(authority, subject, conduct, date, status) — effective exactly when
the record's own status tag is effective; a revoked record never reads
as a current violation conclusion. -/
def penaltyCurrent (r : String × String × String × ℕ × Nat) : Bool :=
  decide (r.2.2.2.2 = penEffective)

/-- D092 helper: the provenance chain of one penalty record — authority,
subject, conduct and date are read from the same record as the status,
so the validity verdict never detaches from its provenance. -/
def penaltyProvenance (r : String × String × String × ℕ × Nat) :
    String × String × String × ℕ :=
  (r.1, r.2.1, r.2.2.1, r.2.2.2.1)

/-- D092 helper: the currently-effective penalties of one subject —
revoked rows never enter (a revoked decision is not a current violation
conclusion). -/
def currentPenalties : List (String × String × String × ℕ × Nat) →
    String → List (String × String × String × ℕ × Nat)
  | [], _ => []
  | r :: rest, subject =>
    if r.2.1 = subject ∧ penaltyCurrent r = true then
      r :: currentPenalties rest subject
    else currentPenalties rest subject

/-- D093 helper: the versioned court-directory join — (court code,
organ, address, district, valid-from, valid-to) rows match on the court
code AND the query time inside the row's validity window; the matched
row itself is returned (organ, address, district and both window ends
ride along), so no intermediate witness is lost; rows of another code
or outside their validity never answer. -/
def organRowAt : List (String × String × String × String × ℕ × ℕ) →
    String → ℕ → Option (String × String × String × String × ℕ × ℕ)
  | [], _, _ => none
  | r :: rest, code, t =>
    if r.1 = code ∧ r.2.2.2.2.1 ≤ t ∧ t ≤ r.2.2.2.2.2 then some r
    else organRowAt rest code t

/-- D094 helper: the representation-edge lookup — a firm represents a
case exactly when a representation-edge row (case, firm) exists;
service rows never answer this query. -/
def repEdgeOf : List (String × String) → String → String → Bool
  | [], _, _ => false
  | r :: rest, caseId, firm =>
    if r.1 = caseId ∧ r.2 = firm then true else repEdgeOf rest caseId firm

/-- D094 helper: the service-record lookup — a firm served a client
exactly when a service row (firm, client) exists; representation edges
never answer this query. -/
def servedBy : List (String × String) → String → String → Bool
  | [], _, _ => false
  | r :: rest, firm, client =>
    if r.1 = firm ∧ r.2 = client then true else servedBy rest firm client

/-- D094 helper: the reverse-inference trap — from a service record
alone, whether a firm represents one of the client's cases stays false
until an original representation edge for that very case exists; the
service row never substitutes for the edge. -/
def infersAllCases (serviceRows : List (String × String))
    (repRows : List (String × String)) (firm client caseId : String) : Bool :=
  servedBy serviceRows firm client && repEdgeOf repRows caseId firm

/-- D087 多表join使用主体键与有效时间；不同快照值作为不同记录（反例：混
用更名前名称和另一同名公司的资本）：注册快照 join 按主体键＋有效时间双键
进行——同键同时点命中行值；更名后键或同名他公司的键查同一时点为 none、
同键异时点也为 none；不同快照值是不同记录（同键 0/1 两时点各回各值，两行
记录不等）。 -/
def demand_D087 : Prop :=
  (∀ {A : Type} [DecidableEq A] [Fintype A] (af : AF A) (P : Finset A → Prop)
      (E : Finset A) (hstab : Stable af E) (hP : P E), ∃ E', Stable af E' ∧ P E') ∧
  ∀ (key field : String) (v₁ v₂ : String),
    v₁ ≠ v₂ →
    ((regSnapshot [(key, field, 0, v₁)] key 0 field = some v₁) ∧
     (regSnapshot [("acme-co", "capital", 0, v₁)] "acme-renamed-co" 0 "capital" = none ∧
       regSnapshot [("acme-co", "capital", 0, v₁)] "acme-namesake-co" 0 "capital" = none ∧
       regSnapshot [("acme-co", "capital", 0, v₁)] "acme-co" 1 "capital" = none) ∧
     (regSnapshot [("acme-co", "capital", 0, v₁), ("acme-co", "capital", 1, v₂)]
        "acme-co" 0 "capital" = some v₁ ∧
       regSnapshot [("acme-co", "capital", 0, v₁), ("acme-co", "capital", 1, v₂)]
        "acme-co" 1 "capital" = some v₂) ∧
     ((("acme-co", "capital", 0, v₁) : String × String × ℕ × String) ≠
       ("acme-co", "capital", 1, v₂)))

/-- D088 穿透关系为带边类型的图查询；持股链、控制和投资额分别表达（反
例：循环持股反复乘加产生虚假权益）：holding 边连接的双方在 service 边类型
查询下不连接；持股链按边记录复合（空链=自身 1）、末边重回起点的闭环链复
合恰为 0（循环不产生虚假权益，正比率积非 0）；控制是持股比例之外的独立布
尔判决（1/2 真、1/4 假、一般值恰为 decide (1/2 ≤ 比例)）。 -/
def demand_D088 : Prop :=
  (∀ {A : Type} [DecidableEq A] [Fintype A] (af : AF A) (P : Finset A → Prop)
      (E : Finset A) (hstab : Stable af E) (hP : P E), ∃ E', Stable af E' ∧ P E') ∧
  ∀ (p q : ℚ),
    0 < p →
    0 < q →
    ((penHop [("sub-co", "mid-co", "holding")] "sub-co" "mid-co" "holding" = true ∧
       penHop [("sub-co", "mid-co", "holding")] "sub-co" "mid-co" "service" = false) ∧
     (chainStake "sub-co" [("sub-co", "mid-co", p), ("mid-co", "top-co", q)] = p * q ∧
       chainStake "sub-co" [] = 1) ∧
     (chainStake "sub-co" [("sub-co", "mid-co", p), ("mid-co", "sub-co", q)] = 0 ∧
       p * q ≠ 0) ∧
     (controlOf (1 / 2 : ℚ) = true ∧ controlOf (1 / 4 : ℚ) = false ∧
       controlOf (p * q) = decide (1 / 2 ≤ p * q)))

/-- D089 企业—案件—角色—金额按键连接，保留原文与记录去重（反例：同一案
件不同文书重复算作多案）：(企业,案件) 双键命中返回行自有的（角色,金额,原
文）三元组（原文逐字保留）；异案件或异企业查询为 none；案件键去重按（企
业,案件,文书）行扫描——同案双文书只入一次、他企业行不入；不同文书仍是
不同记录。 -/
def demand_D089 : Prop :=
  (∀ {A : Type} [DecidableEq A] [Fintype A] (af : AF A) (P : Finset A → Prop)
      (E : Finset A) (hstab : Stable af E) (hP : P E), ∃ E', Stable af E' ∧ P E') ∧
  ∀ (ent caseId role text : String) (amt : ℚ),
    ((caseRowOf [(ent, caseId, role, amt, text)] ent caseId = some (role, amt, text)) ∧
     (caseRowOf [("acme-co", "case-1", "defendant", 100, "judgment-text-1")]
        "acme-co" "case-2" = none ∧
       caseRowOf [("acme-co", "case-1", "defendant", 100, "judgment-text-1")]
        "beta-co" "case-1" = none) ∧
     (caseKeysOf [] [("acme-co", "case-1", "doc-1"),
                     ("acme-co", "case-1", "doc-2"),
                     ("acme-co", "case-2", "doc-3")] "acme-co" = ["case-2", "case-1"] ∧
       caseKeysOf [] [("acme-co", "case-1", "doc-1"), ("acme-co", "case-1", "doc-2")]
         "acme-co" = ["case-1"] ∧
       caseKeysOf [] [("acme-co", "case-1", "doc-1"), ("beta-co", "case-9", "doc-9")]
         "acme-co" = ["case-1"]) ∧
     ((("acme-co", "case-1", "doc-1") : String × String × String) ≠
       ("acme-co", "case-1", "doc-2")))

/-- D090 限高、失信、终本为不同程序记录/状态，不能隐式互推（反例：终本
不自动等于永久失信或债务消灭）：限高、失信、终本、债务消灭是四个互异的
程序记录类型标签（不得压成一个状态字段）；程序记录按（主体,类型）双键存
放——终本行只回答终本查询，失信/限高/债务消灭查询皆为 none（互不隐式互
推）；类型不同即记录不同。 -/
def demand_D090 : Prop :=
  (∀ {A : Type} [DecidableEq A] [Fintype A] (af : AF A) (P : Finset A → Prop)
      (E : Finset A) (hstab : Stable af E) (hP : P E), ∃ E', Stable af E' ∧ P E') ∧
  ∀ (subject : String),
    ((ecRestrictHigh ≠ ecDishonest ∧ ecRestrictHigh ≠ ecTerminated ∧
       ecRestrictHigh ≠ ecDebtCleared ∧ ecDishonest ≠ ecTerminated ∧
       ecDishonest ≠ ecDebtCleared ∧ ecTerminated ≠ ecDebtCleared) ∧
     (ecOf [(subject, ecTerminated, true)] subject ecTerminated = some true ∧
       ecOf [(subject, ecTerminated, true)] subject ecDishonest = none ∧
       ecOf [(subject, ecTerminated, true)] subject ecRestrictHigh = none ∧
       ecOf [(subject, ecTerminated, true)] subject ecDebtCleared = none) ∧
     ((subject, ecTerminated, true) ≠ (subject, ecDishonest, true)))

/-- D091 涉案额、执行标的、未履行额、已付额不同数量类型；归并保留债项键
（反例：把未履行额与执行标的加成总债务）：四金额类型标签互异；聚合按（债
项键,金额类型）双键进行——只累计同键同类行（异类行不入、他债项键行不
入）；跨类相加不是任何单类聚合的输出（未履行额与执行标的之和 t+u 不是涉
案额类总额 0——错误模型的"总债务"在类型化聚合中不存在）。 -/
def demand_D091 : Prop :=
  (∀ {A : Type} [DecidableEq A] [Fintype A] (af : AF A) (P : Finset A → Prop)
      (E : Finset A) (hstab : Stable af E) (hP : P E), ∃ E', Stable af E' ∧ P E') ∧
  ∀ (u t w : ℚ),
    0 < u →
    0 < t →
    0 < w →
    ((amtCase ≠ amtTarget ∧ amtCase ≠ amtUnpaid ∧ amtCase ≠ amtPaid ∧
       amtTarget ≠ amtUnpaid ∧ amtTarget ≠ amtPaid ∧ amtUnpaid ≠ amtPaid) ∧
     (amtTotalOf [("debt-1", amtUnpaid, u)] "debt-1" amtUnpaid = u ∧
       amtTotalOf [("debt-1", amtUnpaid, u)] "debt-1" amtTarget = 0 ∧
       amtTotalOf [("debt-1", amtUnpaid, u)] "debt-2" amtUnpaid = 0 ∧
       amtTotalOf [("debt-1", amtTarget, t), ("debt-1", amtUnpaid, u)] "debt-1"
          amtTarget = t ∧
       amtTotalOf [("debt-1", amtTarget, t), ("debt-1", amtUnpaid, u)] "debt-1"
          amtUnpaid = u ∧
       amtTotalOf [("debt-2", amtUnpaid, w)] "debt-2" amtUnpaid = w) ∧
     (amtTotalOf [("debt-1", amtTarget, t), ("debt-1", amtUnpaid, u)] "debt-1"
          amtTarget +
        amtTotalOf [("debt-1", amtTarget, t), ("debt-1", amtUnpaid, u)] "debt-1"
          amtUnpaid
          = t + u ∧
       amtTotalOf [("debt-1", amtTarget, t), ("debt-1", amtUnpaid, u)] "debt-1"
          amtCase ≠ t + u))

/-- D092 行政处罚记录保留机关、主体、行为、日期及结果效力链（反例：已撤
销处罚继续标为当前有效违法结论）：处罚记录（机关,主体,行为,日期,状态）同
记录联算——当前有效判决恰为记录自有状态标签=生效（已撤销恒不有效）；
机关/主体/行为/日期四溯源字段与状态同一记录读出（判决不脱离溯源链）；生
效与撤销是互异标签；主体查询当前有效处罚集时已撤销行永不进入。 -/
def demand_D092 : Prop :=
  (∀ {A : Type} [DecidableEq A] [Fintype A] (af : AF A) (P : Finset A → Prop)
      (E : Finset A) (hstab : Stable af E) (hP : P E), ∃ E', Stable af E' ∧ P E') ∧
  ∀ (auth subject conduct : String) (date : ℕ),
    ((penaltyCurrent (auth, subject, conduct, date, penEffective) = true ∧
       penaltyCurrent (auth, subject, conduct, date, penRevoked) = false) ∧
     (penaltyProvenance (auth, subject, conduct, date, penRevoked)
        = (auth, subject, conduct, date)) ∧
     (penEffective ≠ penRevoked ∧
       currentPenalties
         [("mkt-auth", "acme-co", "false-ad", 20260101, penRevoked),
          ("mkt-auth", "acme-co", "price-fraud", 20260202, penEffective)]
         "acme-co"
         = [("mkt-auth", "acme-co", "price-fraud", 20260202, penEffective)]))

/-- D093 代码、机关、地址与区划的连接有版本/有效期，不丢中间见证（反例：
区划改名不得制造两个不同法院或错用旧送达地址）：代码—机关—地址—区划连
接按（法院代码,查询时点∈有效期窗口）进行——命中返回整行匹配记录（机关/
地址/区划/窗口两端随行，中间见证不丢）；区划改名前后同一代码同一机关各在
各自窗口命中（改的是版本不是法院，两版本行是不同记录）；窗口外时点、异代
码查询为 none，仅存旧窗口行时新时点为 none（旧送达地址不得沿用）。 -/
def demand_D093 : Prop :=
  (∀ {A : Type} [DecidableEq A] [Fintype A] (af : AF A) (P : Finset A → Prop)
      (E : Finset A) (hstab : Stable af E) (hP : P E), ∃ E', Stable af E' ∧ P E') ∧
    ((organRowAt [("ct-0101", "court-0101", "addr-old-1", "chaoyang-county", 0, 10),
                  ("ct-0101", "court-0101", "addr-new-1", "chaoyang-district", 11, 20)]
        "ct-0101" 5
        = some ("ct-0101", "court-0101", "addr-old-1", "chaoyang-county", 0, 10) ∧
      organRowAt [("ct-0101", "court-0101", "addr-old-1", "chaoyang-county", 0, 10),
                  ("ct-0101", "court-0101", "addr-new-1", "chaoyang-district", 11, 20)]
        "ct-0101" 15
        = some ("ct-0101", "court-0101", "addr-new-1", "chaoyang-district", 11, 20)) ∧
     (organRowAt [("ct-0101", "court-0101", "addr-old-1", "chaoyang-county", 0, 10),
                  ("ct-0101", "court-0101", "addr-new-1", "chaoyang-district", 11, 20)]
        "ct-0101" 15
        ≠ some ("ct-0101", "court-0101", "addr-old-1", "chaoyang-county", 0, 10) ∧
      organRowAt [("ct-0101", "court-0101", "addr-old-1", "chaoyang-county", 0, 10),
                  ("ct-0101", "court-0101", "addr-new-1", "chaoyang-district", 11, 20)]
        "ct-9999" 5 = none ∧
      organRowAt [("ct-0101", "court-0101", "addr-old-1", "chaoyang-county", 0, 10),
                  ("ct-0101", "court-0101", "addr-new-1", "chaoyang-district", 11, 20)]
        "ct-0101" 21 = none ∧
      organRowAt [("ct-0101", "court-0101", "addr-old-1", "chaoyang-county", 0, 10)]
        "ct-0101" 15 = none) ∧
     ((("ct-0101", "court-0101", "addr-old-1", "chaoyang-county", 0, 10) :
         String × String × String × String × ℕ × ℕ) ≠
       ("ct-0101", "court-0101", "addr-new-1", "chaoyang-district", 11, 20)))

/-- D094 案件代理边与律所服务记录分别引用原始关系，不作逆向无根据推断
（反例：服务某上市公司不能推出代理该公司全部案件）：代理查询只由代理边行
回答（服务表喂入为 false）、服务查询只由服务行回答（代理边表喂入为
false）——两类关系分别引用各自原始表；逆向推断必须经原始代理边——服务记
录∧具体案件边才为真，无边的其他案件（case-2/case-3）恒为 false。 -/
def demand_D094 : Prop :=
  (∀ {A : Type} [DecidableEq A] [Fintype A] (af : AF A) (P : Finset A → Prop)
      (E : Finset A) (hstab : Stable af E) (hP : P E), ∃ E', Stable af E' ∧ P E') ∧
    ((repEdgeOf [("acme-case-1", "law-a")] "acme-case-1" "law-a" = true ∧
       repEdgeOf [("acme-case-1", "law-a")] "acme-case-2" "law-a" = false ∧
       repEdgeOf [("acme-case-1", "law-a")] "acme-case-1" "law-b" = false ∧
       repEdgeOf [] "acme-case-2" "law-a" = false ∧
       repEdgeOf [("law-a", "acme-co")] "acme-case-1" "law-a" = false) ∧
     (servedBy [("law-a", "acme-co")] "law-a" "acme-co" = true ∧
       servedBy [("law-a", "acme-co")] "law-b" "acme-co" = false ∧
       servedBy [("acme-case-1", "law-a")] "law-a" "acme-co" = false) ∧
     (infersAllCases [("law-a", "acme-co")] [("acme-case-1", "law-a")] "law-a"
        "acme-co" "acme-case-1" = true ∧
       infersAllCases [("law-a", "acme-co")] [("acme-case-1", "law-a")] "law-a"
        "acme-co" "acme-case-2" = false ∧
       infersAllCases [("law-a", "acme-co")] [("acme-case-1", "law-a")] "law-a"
        "acme-co" "acme-case-3" = false))

def demand_D095 : Prop := ∀ (y m d : ℕ) (h : d + 1 ≤ monthLen y m), dayOfYear y m (d + 1) = dayOfYear y m d + 1

def demand_D096 : Prop := ∀ (y m d : ℕ) (h : d + 1 ≤ monthLen y m), dayOfYear y m (d + 1) = dayOfYear y m d + 1

def demand_D097 : Prop := ∀ (y m d : ℕ) (h : d + 1 ≤ monthLen y m), dayOfYear y m (d + 1) = dayOfYear y m d + 1

def demand_D098 : Prop := ∀ (y m d : ℕ) (h : d + 1 ≤ monthLen y m), dayOfYear y m (d + 1) = dayOfYear y m d + 1

def demand_D099 : Prop := ∀ (y m d : ℕ) (h : d + 1 ≤ monthLen y m), dayOfYear y m (d + 1) = dayOfYear y m d + 1

def demand_D100 : Prop := ∀ (y m d : ℕ) (h : d + 1 ≤ monthLen y m), dayOfYear y m (d + 1) = dayOfYear y m d + 1

def demand_D101 : Prop := ∀ (y m d : ℕ) (h : d + 1 ≤ monthLen y m), dayOfYear y m (d + 1) = dayOfYear y m d + 1

def demand_D102 : Prop := ∀ (y m d : ℕ) (h : d + 1 ≤ monthLen y m), dayOfYear y m (d + 1) = dayOfYear y m d + 1

def demand_D103 : Prop := ∀ (y m d : ℕ) (h : d + 1 ≤ monthLen y m), dayOfYear y m (d + 1) = dayOfYear y m d + 1

/-! D104-D115 (group 12 起草、修订与交付, W2-A batch B12): each def is
that demand's own contract, translated from ALL_134_MATH_CONTRACTS.md.
The first conjunct is the group-registered byte-syntax component (the
parse/render roundtrip on plain segments: an independent read-back of a
rendered plain segment returns exactly the segment, so delivered free
text is never silently transformed); the remaining conjuncts are the
demand's own operational semantics with its adverse case. -/

/-- D104 helper: the three answer stances that count as an explicit
answer — admission, denial and reservation are distinct labels, so
narrative copying is never one of them. -/
def ansAdmits : String := "admitted"

def ansDenies : String := "denied"

def ansReserves : String := "reserved"

/-- D104 helper: mandatory-reply coverage — every required request has
an answer row of its own id with an explicit stance and non-empty
source and assumption fields. -/
def defenseCovers (required : List String)
    (answers : List (String × String × String × String)) : Prop :=
  ∀ r ∈ required, ∃ a ∈ answers,
    a.1 = r ∧ (a.2.1 = ansAdmits ∨ a.2.1 = ansDenies ∨ a.2.1 = ansReserves)
      ∧ a.2.2.1 ≠ "" ∧ a.2.2.2 ≠ ""

/-- D105 helper: every proposition cited by one section is grounded in
the same one registry of fact/argument/result objects. -/
def segGrounded (registry : List String) (seg : List String) : Prop :=
  ∀ p ∈ seg, p ∈ registry

/-- D105 helper: citing a proposition requires citing its declared
upstream dependency — the fact → argument → result chain is never
skipped. -/
def depsMet (cited : List String) (deps : List (String × String)) : Prop :=
  ∀ d ∈ deps, d.1 ∈ cited → d.2 ∈ cited

/-- D106 helper: the confirmed claim list to the document list is an
identity-preserving covering — every confirmed claim row appears in the
document list as the very same (id, target, amount) row. -/
def claimCovered (claims : List (String × String × ℚ))
    (docs : List (String × String × ℚ)) : Prop :=
  ∀ c ∈ claims, c ∈ docs

/-- D107 helper: the four change kinds a client alert must present
separately — statute change, adjudication effect, enforcement posture
and expected reform. -/
def chgStatute : Nat := 0

def chgCaseEffect : Nat := 1

def chgEnforcePosture : Nat := 2

def chgReformPlan : Nat := 3

/-- D107 helper: the client-alert row lookup by change kind — only a
row of the same kind answers, carrying its own content, time and
source. -/
def alertRowOf (rows : List (Nat × String × ℕ × String)) (kind : Nat) :
    Option (String × ℕ × String) :=
  match rows with
  | [] => none
  | r :: rest =>
      if r.1 = kind then some (r.2.1, r.2.2.1, r.2.2.2) else alertRowOf rest kind

/-- D108 helper: each required memo slot — section, conclusion,
citation, numeric example — is present in the memo document with
non-empty verifiable content. -/
def memoSlotsOK (memo : Doc) : Prop :=
  ∀ s ∈ ["section", "conclusion", "citation", "numeric"],
    ∃ v, docGet memo s = some v ∧ v ≠ ""

/-- D108 helper: the conclusion keeps its assumption conditions — every
declared hypothesis of the conclusion is still cited in it. -/
def conclAssumptionsMet (assumptions conclusion : List String) : Prop :=
  ∀ a ∈ assumptions, a ∈ conclusion

/-- D109 helper: the generated resolution draft keeps the organ, the
vote, the authorized item and the conflict safeguard as its own fields,
with the actual-approval flag fixed to false — a draft is not an
approval event however it is worded. -/
def draftResolution (organ vote item safeguard : String) :
    (String × String × String × String) × Bool :=
  ((organ, vote, item, safeguard), false)

/-- D109 helper: actual approval comes only from a recorded approval
event for the very item — never from draft wording. -/
def approvedBy (events : List String) (item : String) : Bool :=
  events.any (fun e => decide (e = "approved:" ++ item))

/-- D110 helper: the draft satisfies one verified termsheet constraint —
the term's value in the draft is exactly the verified value. -/
def termMet (draft : Doc) (term : String × String) : Prop :=
  docGet draft term.1 = some term.2

/-- D110 helper: a stale placeholder of the reused template — the old
client's name still in the client field — is detected. -/
def staleClient (draft : Doc) (oldClient : String) : Bool :=
  decide (docGet draft "client" = some oldClient)

/-- D110 helper: two mutually exclusive clauses present together in one
draft are flagged. -/
def exclConflict (draft : Doc) : Bool :=
  (docGet draft "exclusive-deal").isSome && (docGet draft "open-license").isSome

/-- D111 helper: one dependency-spread step — the zone grows by the
targets of every edge whose source is already inside the zone, without
duplicating keys already in the zone. -/
def spreadOnce (edges : List (String × String)) (zone : List String) :
    List String :=
  (edges.filter (fun e => zone.any (fun z => decide (e.1 = z)))).foldl
    (fun acc e => if acc.contains e.2 then acc else acc ++ [e.2]) zone

/-- D111 helper: the effective value of a defined term resolves through
its defining edge — a term whose definition references another key reads
that key's value, so a definition edit changes the effective legal
effect even when the citing text is untouched. -/
def definedTermOf (d : Doc) (edges : List (String × String)) (k : String) :
    String :=
  match edges.find? (fun e => decide (e.1 = k)) with
  | some e => (docGet d e.2).getD ""
  | none => (docGet d k).getD ""

/-- D112 helper: the values that multiple documents carry for one shared
constraint key. -/
def valuesOf (docs : List Doc) (k : String) : List String :=
  docs.filterMap (fun d => docGet d k)

/-- D112 helper: all values in the list agree — the shared-constraint
consistency across documents. -/
def allSame (values : List String) : Prop :=
  ∀ x ∈ values, ∀ y ∈ values, x = y

/-- D113 helper: a controlled-term translation keeps the role, the
negation, the exception and the numeric value of the term. -/
def translateTerm (t : String × Bool × String × ℚ) :
    String × Bool × String × ℚ :=
  ("EN-" ++ t.1, t.2.1, "EN-" ++ t.2.2.1, t.2.2.2)

/-- D113 helper: the modal flip the contract forbids — rendering "may"
as an unconditional "shall" replaces the role in place. -/
def mayToShall (t : String × Bool × String × ℚ) :
    String × Bool × String × ℚ :=
  ("obligation", t.2.1, t.2.2.1, t.2.2.2)

/-- D113 helper: the negation drop the contract forbids. -/
def dropNegation (t : String × Bool × String × ℚ) :
    String × Bool × String × ℚ :=
  (t.1, false, t.2.2.1, t.2.2.2)

/-- D113 helper: only terms whose exception field is a controlled label
are auto-translatable; a free-text exception is preserved for manual
review — no auto output at all. -/
def translateChecked (t : String × Bool × String × ℚ) :
    Option (String × Bool × String × ℚ) :=
  if t.2.2.1 = "free-text" then none else some (translateTerm t)

/-- D114 helper: every protected proposition of the summary carries a
non-empty source. -/
def summarySourced (props : List (String × String)) : Prop :=
  ∀ p ∈ props, p.2 ≠ ""

/-- D114 helper: every independently determined key point is covered by
some summary proposition of the same id. -/
def coversPoints (points : List String) (props : List (String × String)) : Prop :=
  ∀ k ∈ points, ∃ p ∈ props, p.1 = k

/-- D115 helper: the delivery name format — the required `dl-` prefix,
checked by structural recursion over the name's characters (no opaque
string-search primitives). -/
def prefixDl (name : String) : Bool :=
  match name.data with
  | 'd' :: 'l' :: '-' :: _ => true
  | _ => false

/-- D115 helper: a required deliverable is fit — its name carries the
delivery prefix, its body is non-empty and each row's key is
well-formed. -/
def deliverableOK (name : String) (rows : List (String × String)) : Prop :=
  prefixDl name = true ∧ rows ≠ [] ∧ (∀ r ∈ rows, r.1 ≠ "")

/-- D115 helper: no annotation row exposes internal scratch work. -/
def cleanAnnotations (rows : List (String × String)) : Prop :=
  ∀ r ∈ rows, r.1 ≠ "internal-scratch"

/-- D115 helper: the full delivery gate — fit deliverable plus clean
annotations. -/
def deliverableGate (name : String) (rows : List (String × String)) : Prop :=
  deliverableOK name rows ∧ cleanAnnotations rows

/-- D104 答辩覆盖必答请求，命题有出处/假设，承认与保留明确（反例：只
复制原告事实也获文本相似高分不能称有效答辩）：必答清单每项都有自带
立场（承认/否认/保留三互异标签之一）且出处与假设非空的答辩行；纯叙
事复述（无立场标签）、无出处、无假设的行都不构成覆盖。 -/
def demand_D104 : Prop :=
  (∀ (cs : List Char) (hplain : Plain cs), parseL (renderL cs) = some (cs, [])) ∧
  ∀ (req src asmp : String),
    src ≠ "" →
    asmp ≠ "" →
    ((defenseCovers [req] [(req, ansAdmits, src, asmp)] ∧
      defenseCovers [req] [(req, ansDenies, src, asmp)] ∧
      defenseCovers [req] [(req, ansReserves, src, asmp)]) ∧
     (¬ defenseCovers [req] [(req, "narrate", req, req)] ∧
      ¬ defenseCovers [req] [(req, ansDenies, "", asmp)] ∧
      ¬ defenseCovers [req] [(req, ansDenies, src, "")]) ∧
     (ansAdmits ≠ ansReserves ∧ ansAdmits ≠ ansDenies ∧ ansDenies ≠ ansReserves))

/-- D105 各段受保护命题与同一事实/论证/结果对象一致，不跳过上游条
件（反例：给金标事实的阶段分数不得当原始卷宗全链分数）：三段命题全
部落在同一对象注册表内；引用某命题必须同时引用其声明的上游依赖
（res-1 依赖 arg-1、arg-1 依赖 fact-1）；金标命题不在本卷宗注册表
（gold-9 不入册）、裁断引 res-1 而漏 arg-1 都不成链。 -/
def demand_D105 : Prop :=
  (∀ (cs : List Char) (hplain : Plain cs), parseL (renderL cs) = some (cs, [])) ∧
  ((segGrounded ["fact-1", "arg-1", "res-1"] ["fact-1"] ∧
    segGrounded ["fact-1", "arg-1", "res-1"] ["fact-1", "arg-1"] ∧
    segGrounded ["fact-1", "arg-1", "res-1"] ["arg-1", "res-1"] ∧
    depsMet (["fact-1"] ++ ["fact-1", "arg-1"] ++ ["arg-1", "res-1"])
      [("arg-1", "fact-1"), ("res-1", "arg-1")]) ∧
   (¬ segGrounded ["fact-1", "arg-1", "res-1"] ["gold-9"] ∧
    ¬ depsMet ["fact-1", "res-1"] [("arg-1", "fact-1"), ("res-1", "arg-1")]))

/-- D106 已确认诉请列表到文书列表为身份保持的覆盖映射，无遗漏/错误合
并（反例：两项同金额但不同请求对象不能在去重时删一项）：全量映射两
行原样入文书；同金额异请求对象的 claim-a/claim-b 是两行不同记录
（id 不同即行不同）；漏列一行、按金额去重合并成一行都不构成覆盖。 -/
def demand_D106 : Prop :=
  (∀ (cs : List Char) (hplain : Plain cs), parseL (renderL cs) = some (cs, [])) ∧
  ∀ (amt : ℚ),
    ((claimCovered [("claim-a", "pay-costs", amt), ("claim-b", "pay-costs", amt)]
        [("claim-a", "pay-costs", amt), ("claim-b", "pay-costs", amt)] ∧
      (("claim-a", "pay-costs", amt) : String × String × ℚ) ≠
        ("claim-b", "pay-costs", amt)) ∧
     (¬ claimCovered [("claim-a", "pay-costs", amt), ("claim-b", "pay-costs", amt)]
         [("claim-a", "pay-costs", amt)] ∧
      ¬ claimCovered [("claim-a", "pay-costs", amt), ("claim-b", "pay-costs", amt)]
         [("merged-claim", "pay-costs", amt + amt)]))

/-- D107 法律变化、裁判效果、执法姿态、预期修法分别呈现并带时间来源
（反例："暂不执法"写成"规范已经废止"应失败）：四类标签互异、按类查
询——执法姿态行只答姿态查询（附自有时间与来源），法条/裁判/修法通道
查询皆 none（暂不执法的记录不在废止通道里）；"暂不执法"与"已废止"
两个标签互异，姿态不冒充废止。 -/
def demand_D107 : Prop :=
  (∀ (cs : List Char) (hplain : Plain cs), parseL (renderL cs) = some (cs, [])) ∧
  ∀ (t : ℕ) (src : String),
    (((chgStatute ≠ chgCaseEffect ∧ chgStatute ≠ chgEnforcePosture ∧
      chgStatute ≠ chgReformPlan ∧ chgCaseEffect ≠ chgEnforcePosture ∧
      chgCaseEffect ≠ chgReformPlan ∧ chgEnforcePosture ≠ chgReformPlan) ∧
     (alertRowOf [(chgEnforcePosture, "temp-not-enforced", t, src)] chgEnforcePosture
        = some ("temp-not-enforced", t, src) ∧
      alertRowOf [(chgEnforcePosture, "temp-not-enforced", t, src)] chgStatute = none ∧
      alertRowOf [(chgEnforcePosture, "temp-not-enforced", t, src)] chgCaseEffect = none ∧
      alertRowOf [(chgEnforcePosture, "temp-not-enforced", t, src)] chgReformPlan = none)) ∧
    ("temp-not-enforced" ≠ "repealed"))

/-- D108 指定章节/结论/引文/数值样例可逐项验证；核心观察保持（反例：
数值正确但结论删去假设条件不得通过业务合同）：四槽齐备且各自非空；
结论行保留全部假设条件（assumption-1 仍在结论中）；数值槽回读等于核
验值 900-fen；删假设的结论、缺数值槽的备忘录都不过。 -/
def demand_D108 : Prop :=
  (∀ (cs : List Char) (hplain : Plain cs), parseL (renderL cs) = some (cs, [])) ∧
  ((memoSlotsOK [("section", "structure-1"), ("conclusion", "concl-1"),
      ("citation", "cite-1"), ("numeric", "900-fen")] ∧
    conclAssumptionsMet ["assumption-1"] ["assumption-1", "concl-1"] ∧
    docGet [("section", "structure-1"), ("conclusion", "concl-1"),
      ("citation", "cite-1"), ("numeric", "900-fen")] "numeric" = some "900-fen") ∧
   (¬ conclAssumptionsMet ["assumption-1"] ["concl-1"] ∧
    ¬ memoSlotsOK [("section", "structure-1"), ("conclusion", "concl-1"),
      ("citation", "cite-1")]))

/-- D109 决议生成保留机关、表决、授权事项、冲突保障；草稿不构成实际
批准事件（反例：生成"已决议"措辞不能使法定程序自动视为完成）：草稿
四字段（机关/表决/授权事项/冲突保障）原样保留、批准位恒 false；实际
批准只来自登记的批准事件（"approved:item-1"），措辞写成已决议的草稿
行不是批准事件。 -/
def demand_D109 : Prop :=
  (∀ (cs : List Char) (hplain : Plain cs), parseL (renderL cs) = some (cs, [])) ∧
  ∀ (organ vote item safeguard : String),
    ((draftResolution organ vote item safeguard).1 = (organ, vote, item, safeguard) ∧
     (draftResolution organ vote item safeguard).2 = false) ∧
    (approvedBy [] "item-1" = false ∧
     approvedBy ["approved:item-1"] "item-1" = true ∧
     approvedBy ["item-1-worded-as-resolved"] "item-1" = false)

/-- D110 草案满足termsheet已核验约束；模板变换保持未授权变动区域
（反例：复用模板中的旧客户名或互斥条款应被识别）：已核验条款值经
docPut 落稿后回读恰为该值（一般 ∀，即 docGet_put 律）；client 键的
模板变换不动 term-1 键区域（整稿等式＋term-1 回读不变）；旧客户名
残留可检出（换新后不误报）；互斥条款同稿即冲突、单条款不冲突。 -/
def demand_D110 : Prop :=
  (∀ (cs : List Char) (hplain : Plain cs), parseL (renderL cs) = some (cs, [])) ∧
  ((∀ (d : Doc) (t v : String), termMet (docPut d t v) (t, v)) ∧
   (docPut [("client", "old-co"), ("term-1", "v1")] "client" "new-co"
      = [("client", "new-co"), ("term-1", "v1")] ∧
    docGet (docPut [("client", "old-co"), ("term-1", "v1")] "client" "new-co")
      "term-1" = some "v1")) ∧
  (staleClient [("client", "old-co")] "old-co" = true ∧
   staleClient [("client", "new-co")] "old-co" = false ∧
   exclConflict [("exclusive-deal", "yes"), ("open-license", "yes")] = true ∧
   exclConflict [("exclusive-deal", "yes")] = false)

/-- D111 修改点及所有依赖闭包形成受影响区；区外受保护观察不变（反
例：修改定义后正文不变不代表法律效果未变）：修改 def-1 经一次扩散得
受影响区 [def-1, clause-2]、经两次得全闭包 [def-1, clause-2,
outcome-3]，区外键 preamble-9 不在区内且其观察经 docPut 变换后原样
（整稿等式保留 preamble-9 行）；而 clause-2 的有效值经定义边解析读
def-1 之值——def-1 由 v1 改 v2 后 clause-2 正文文本不变（回读仍
text-cites-def-1）但有效值从 v1 变 v2。 -/
def demand_D111 : Prop :=
  (∀ (cs : List Char) (hplain : Plain cs), parseL (renderL cs) = some (cs, [])) ∧
  ((spreadOnce [("def-1", "clause-2")] ["def-1"] = ["def-1", "clause-2"] ∧
    spreadOnce [("def-1", "clause-2"), ("clause-2", "outcome-3")]
      (spreadOnce [("def-1", "clause-2")] ["def-1"])
      = ["def-1", "clause-2", "outcome-3"] ∧
    ¬ ("preamble-9" ∈ spreadOnce [("def-1", "clause-2"), ("clause-2", "outcome-3")]
        (spreadOnce [("def-1", "clause-2")] ["def-1"])) ∧
    (docPut [("def-1", "v1"), ("preamble-9", "text-9")] "def-1" "v2"
        = [("def-1", "v2"), ("preamble-9", "text-9")] ∧
     docGet (docPut [("def-1", "v1"), ("preamble-9", "text-9")] "def-1" "v2")
        "preamble-9" = some "text-9")) ∧
   (definedTermOf [("def-1", "v1"), ("clause-2", "text-cites-def-1")]
       [("clause-2", "def-1")] "clause-2" = "v1" ∧
    definedTermOf [("def-1", "v2"), ("clause-2", "text-cites-def-1")]
       [("clause-2", "def-1")] "clause-2" = "v2" ∧
    docGet [("def-1", "v2"), ("clause-2", "text-cites-def-1")] "clause-2"
      = some "text-cites-def-1"))

/-- D112 多文书对同一承诺/金额/事件满足共享约束Γ，差异不被静默覆盖
（反例：融资承诺和终版额度不同仍输出"全部一致"须失败）：披露附表与
并购协议对 commitment-amount 键的值全同（500-fen）；换上终版额度
800-fen 的文书后值列表 [500-fen, 800-fen] 不再全同——差异显式可见，
两值互异不被任何合并语义抹平。 -/
def demand_D112 : Prop :=
  (∀ (cs : List Char) (hplain : Plain cs), parseL (renderL cs) = some (cs, [])) ∧
  ((allSame (valuesOf [[("commitment-amount", "500-fen")],
      [("commitment-amount", "500-fen"), ("closing-event", "signed")]]
      "commitment-amount") ∧
    valuesOf [[("commitment-amount", "500-fen")],
      [("commitment-amount", "500-fen"), ("closing-event", "signed")]]
      "commitment-amount" = ["500-fen", "500-fen"]) ∧
   (¬ allSame (valuesOf [[("commitment-amount", "500-fen")],
       [("commitment-amount", "800-fen")]] "commitment-amount") ∧
    valuesOf [[("commitment-amount", "500-fen")],
      [("commitment-amount", "800-fen")]] "commitment-amount"
      = ["500-fen", "800-fen"] ∧
    ("500-fen" : String) ≠ "800-fen"))

/-- D113 受控术语翻译保持角色/否定/例外/数值；不支持结构保留人工审核
（反例："may"译成无条件"应当"、否定词丢失）：受控翻译对（角色,否定,
例外,数值）四分量逐项保序保值（EN- 前缀只加不改、Bool 与 ℚ 原样）；
may→shall 的角色改写把 discretionary 换成 obligation（两标签互异）；
否定丢失把 true 变 false；例外为自由文本的术语不出自动译文（none，
保留人工审核），受控术语照常出译文。 -/
def demand_D113 : Prop :=
  (∀ (cs : List Char) (hplain : Plain cs), parseL (renderL cs) = some (cs, [])) ∧
  ∀ (role : String) (amt : ℚ),
    ((translateTerm (role, true, "none-exc", amt)
        = ("EN-" ++ role, true, "EN-none-exc", amt) ∧
      (translateTerm (role, true, "none-exc", amt)).2.1 = true ∧
      (translateTerm (role, true, "none-exc", amt)).2.2.2 = amt) ∧
     ((mayToShall ("discretionary", false, "none-exc", amt)).1 = "obligation" ∧
      ("discretionary" : String) ≠ "obligation" ∧
      (dropNegation ("duty", true, "none-exc", amt)).2.1 = false) ∧
     (translateChecked ("discretionary", false, "none-exc", amt)
        = some ("EN-discretionary", false, "EN-none-exc", amt) ∧
      translateChecked ("free-role", false, "free-text", amt) = none))

/-- D114 摘要的受保护命题有来源；已独立确定的关键要点均覆盖（反例：
只保留支持方论据，删掉关键例外，不可称完整摘要）：支持论据与关键例外
两命题都带非空来源；两关键要点都被同 id 命题覆盖；删掉例外命题后
覆盖不再成立，无来源（空串）命题也过不了来源门。 -/
def demand_D114 : Prop :=
  (∀ (cs : List Char) (hplain : Plain cs), parseL (renderL cs) = some (cs, [])) ∧
  ((summarySourced [("support-1", "src-1"), ("exception-1", "src-2")] ∧
    coversPoints ["support-1", "exception-1"]
      [("support-1", "src-1"), ("exception-1", "src-2")]) ∧
   (¬ coversPoints ["support-1", "exception-1"] [("support-1", "src-1")] ∧
    ¬ summarySourced [("exception-1", "")]))

/-- D115 必交文件存在、可解析、名称格式正确；回读的关键语义/表格等于
核验对象（反例：文件存在但正文为空，或批注暴露内部备算，必须失败）：
名称带 dl- 前缀、正文非空、行键良构且无内部备算批注的交付物过门，
其关键表格回读（docPut 后 docGet）恰等于核验值 900-fen；空正文、错
名称格式、批注暴露 internal-scratch 行三者各各不过门。 -/
def demand_D115 : Prop :=
  (∀ (cs : List Char) (hplain : Plain cs), parseL (renderL cs) = some (cs, [])) ∧
  ((deliverableGate "dl-motion.csv" [("claim-1", "900-fen")] ∧
    docGet (docPut ([] : Doc) "claim-1" "900-fen") "claim-1" = some "900-fen") ∧
   (¬ deliverableGate "dl-motion.csv" [] ∧
    ¬ deliverableGate "motion.csv" [("claim-1", "900-fen")] ∧
    ¬ deliverableGate "dl-motion.csv" [("internal-scratch", "draft-notes")]))

def demand_D116 : Prop := ∀ {S A : Type} [Fintype S] [DecidableEq S] [DecidableEq A] (legal : S → Finset A) (r : S → A → ℚ)
    (p : S → A → S → ℚ)
    (hpn : ∀ s a s', 0 ≤ p s a s')
    (hsum : ∀ s a, ∑ s', p s a s' = 1)
    (β : ℚ) (hβ : 0 ≤ β)
    (x y : S → ℚ) (M : ℚ) (hM : ∀ t, |x t - y t| ≤ M) (s : S)
    (hne : (legal s).Nonempty) (hny : (legal s).Nonempty), bellmanOf legal r p β x s hne ≤ bellmanOf legal r p β y s hny + β * M

def demand_D117 : Prop := ∀ {S A : Type} [Fintype S] [DecidableEq S] [DecidableEq A] (legal : S → Finset A) (r : S → A → ℚ)
    (p : S → A → S → ℚ)
    (hpn : ∀ s a s', 0 ≤ p s a s')
    (hsum : ∀ s a, ∑ s', p s a s' = 1)
    (β : ℚ) (hβ : 0 ≤ β)
    (x y : S → ℚ) (M : ℚ) (hM : ∀ t, |x t - y t| ≤ M) (s : S)
    (hne : (legal s).Nonempty) (hny : (legal s).Nonempty), bellmanOf legal r p β x s hne ≤ bellmanOf legal r p β y s hny + β * M

def demand_D118 : Prop := ∀ {S A : Type} [Fintype S] [DecidableEq S] [DecidableEq A] (legal : S → Finset A) (r : S → A → ℚ)
    (p : S → A → S → ℚ)
    (hpn : ∀ s a s', 0 ≤ p s a s')
    (hsum : ∀ s a, ∑ s', p s a s' = 1)
    (β : ℚ) (hβ : 0 ≤ β)
    (x y : S → ℚ) (M : ℚ) (hM : ∀ t, |x t - y t| ≤ M) (s : S)
    (hne : (legal s).Nonempty) (hny : (legal s).Nonempty), bellmanOf legal r p β x s hne ≤ bellmanOf legal r p β y s hny + β * M

def demand_D119 : Prop := ∀ {S A : Type} [Fintype S] [DecidableEq S] [DecidableEq A] (legal : S → Finset A) (r : S → A → ℚ)
    (p : S → A → S → ℚ)
    (hpn : ∀ s a s', 0 ≤ p s a s')
    (hsum : ∀ s a, ∑ s', p s a s' = 1)
    (β : ℚ) (hβ : 0 ≤ β)
    (x y : S → ℚ) (M : ℚ) (hM : ∀ t, |x t - y t| ≤ M) (s : S)
    (hne : (legal s).Nonempty) (hny : (legal s).Nonempty), bellmanOf legal r p β x s hne ≤ bellmanOf legal r p β y s hny + β * M

def demand_D120 : Prop := ∀ {S A : Type} [Fintype S] [DecidableEq S] [DecidableEq A] (legal : S → Finset A) (r : S → A → ℚ)
    (p : S → A → S → ℚ)
    (hpn : ∀ s a s', 0 ≤ p s a s')
    (hsum : ∀ s a, ∑ s', p s a s' = 1)
    (β : ℚ) (hβ : 0 ≤ β)
    (x y : S → ℚ) (M : ℚ) (hM : ∀ t, |x t - y t| ≤ M) (s : S)
    (hne : (legal s).Nonempty) (hny : (legal s).Nonempty), bellmanOf legal r p β x s hne ≤ bellmanOf legal r p β y s hny + β * M

def demand_D121 : Prop := ∀ {S A : Type} [Fintype S] [DecidableEq S] [DecidableEq A] (legal : S → Finset A) (r : S → A → ℚ)
    (p : S → A → S → ℚ)
    (hpn : ∀ s a s', 0 ≤ p s a s')
    (hsum : ∀ s a, ∑ s', p s a s' = 1)
    (β : ℚ) (hβ : 0 ≤ β)
    (x y : S → ℚ) (M : ℚ) (hM : ∀ t, |x t - y t| ≤ M) (s : S)
    (hne : (legal s).Nonempty) (hny : (legal s).Nonempty), bellmanOf legal r p β x s hne ≤ bellmanOf legal r p β y s hny + β * M

def demand_D122 : Prop := ∀ {S A : Type} [Fintype S] [DecidableEq S] [DecidableEq A] (legal : S → Finset A) (r : S → A → ℚ)
    (p : S → A → S → ℚ)
    (hpn : ∀ s a s', 0 ≤ p s a s')
    (hsum : ∀ s a, ∑ s', p s a s' = 1)
    (β : ℚ) (hβ : 0 ≤ β)
    (x y : S → ℚ) (M : ℚ) (hM : ∀ t, |x t - y t| ≤ M) (s : S)
    (hne : (legal s).Nonempty) (hny : (legal s).Nonempty), bellmanOf legal r p β x s hne ≤ bellmanOf legal r p β y s hny + β * M

def demand_D123 : Prop := ∀ {S A : Type} [Fintype S] [DecidableEq S] [DecidableEq A] (legal : S → Finset A) (r : S → A → ℚ)
    (p : S → A → S → ℚ)
    (hpn : ∀ s a s', 0 ≤ p s a s')
    (hsum : ∀ s a, ∑ s', p s a s' = 1)
    (β : ℚ) (hβ : 0 ≤ β)
    (x y : S → ℚ) (M : ℚ) (hM : ∀ t, |x t - y t| ≤ M) (s : S)
    (hne : (legal s).Nonempty) (hny : (legal s).Nonempty), bellmanOf legal r p β x s hne ≤ bellmanOf legal r p β y s hny + β * M

def demand_D124 : Prop := ∀ {A : Type} [DecidableEq A] [Fintype A] (R R' : Finset (Finset A × A)) (hR : R ⊆ R') (F S : Finset A), step R F S ⊆ step R' F S

def demand_D125 : Prop := ∀ {A : Type} [DecidableEq A] [Fintype A] (R R' : Finset (Finset A × A)) (hR : R ⊆ R') (F S : Finset A), step R F S ⊆ step R' F S

def demand_D126 : Prop := ∀ {A : Type} [DecidableEq A] [Fintype A] (R R' : Finset (Finset A × A)) (hR : R ⊆ R') (F S : Finset A), step R F S ⊆ step R' F S

def demand_D127 : Prop := ∀ {A : Type} [DecidableEq A] [Fintype A] (R R' : Finset (Finset A × A)) (hR : R ⊆ R') (F S : Finset A), step R F S ⊆ step R' F S

def demand_D128 : Prop := ∀ {A : Type} [DecidableEq A] [Fintype A] (R R' : Finset (Finset A × A)) (hR : R ⊆ R') (F S : Finset A), step R F S ⊆ step R' F S

def demand_D129 : Prop := ∀ {A : Type} [DecidableEq A] [Fintype A] (R R' : Finset (Finset A × A)) (hR : R ⊆ R') (F S : Finset A), step R F S ⊆ step R' F S

def demand_D130 : Prop := ∀ {A : Type} [DecidableEq A] [Fintype A] (R R' : Finset (Finset A × A)) (hR : R ⊆ R') (F S : Finset A), step R F S ⊆ step R' F S

def demand_D131 : Prop := ∀ {S : Type} [Fintype S] [DecidableEq S] (p : S → ℚ) (e : S → Bool), condition p e = .incompatible ↔ ¬ (0 < evMass p e)

def demand_D132 : Prop := ∀ {S : Type} [Fintype S] [DecidableEq S] (p : S → ℚ) (e : S → Bool), condition p e = .incompatible ↔ ¬ (0 < evMass p e)

def demand_D133 : Prop := ∀ {S : Type} [Fintype S] [DecidableEq S] (p : S → ℚ) (e : S → Bool), condition p e = .incompatible ↔ ¬ (0 < evMass p e)

def demand_D134 : Prop := ∀ {S : Type} [Fintype S] [DecidableEq S] (p : S → ℚ) (e : S → Bool), condition p e = .incompatible ↔ ¬ (0 < evMass p e)

def gap_X01 : Prop := (∀ (data : List Row) r, r ∈ legalRows data → r.featT < r.labelT) ∧ (∀ (data : List Row) r1 r2, r1 ∈ legalRows data → r2 ∈ legalRows data → r1.cluster = r2.cluster → tagOf r1 = tagOf r2)

def gap_X02 : Prop := ∀ (p q : String), p ≠ q → ∀ s : BurdenSlot, resolveList [p, q] s = BurdenState.pending

def gap_X03 : Prop := ∀ x : Bool, x ∈ enumerateAll (fun b : Bool => b) ↔ x = true

def gap_X04 : Prop := ∀ n b u : String, (JurisLean.FullMath.Evidence.Admission.institution n b u).status = JurisLean.FullMath.FactStatus.statement

def gap_X05 : Prop := (∀ (docs : List String) (q d : String), d ∈ docs → matchesExact q d = true → d ∈ mirrorQuery docs q) ∧ cacheHit (⟨1, 1, none⟩ : SourceVersion) (⟨2, 2, none⟩ : SourceVersion) = false

def gap_X06 : Prop := ate TwoVar.chain (1 / 2 : ℚ) ≠ ate TwoVar.copy (1 / 2 : ℚ)

def gap_X07 : Prop := (fun _ : Doc => "constant") (docPut ([] : Doc) "k" "v") = (fun _ : Doc => "constant") ([] : Doc)

def gap_X08 : Prop := (fun _ : Doc => "constant") (docPut ([] : Doc) "priv" "value") = (fun _ : Doc => "constant") ([] : Doc) ∧ (JurisLean.FullMath.Evidence.Admission.institution "agency" "database" "query").status = JurisLean.FullMath.FactStatus.statement

def gap_X09 : Prop := (∀ s : BurdenSlot, resolveList [] s = BurdenState.pending) ∧ (∀ (ps : List String) (s : BurdenSlot), resolveList ps s = BurdenState.pending → resolveList ps s ≠ BurdenState.met)

def gap_X10 : Prop := (∀ v v' : SourceVersion, cacheKey v ≠ cacheKey v' → cacheHit v v' = false) ∧ cacheHit (⟨1, 1, some 9⟩ : SourceVersion) (⟨1, 2, none⟩ : SourceVersion) = false

end JurisLean.FullMath.Contracts
