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
      (sources : List SourceVersion) (t : ℕ) (exclusions cd inst lv : String),
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

def demand_D009 : Prop := ∀ (sources : List SourceVersion) (t : ℕ)
    (exclusions : List String) (s : String)
    (hnone : applicableSources sources t = []) (hnot : ¬ (s ∈ exclusions)), decideSlot sources t exclusions s = SlotStatus.pending

def demand_D010 : Prop := ∀ (sources : List SourceVersion) (t : ℕ)
    (exclusions : List String) (s : String)
    (hnone : applicableSources sources t = []) (hnot : ¬ (s ∈ exclusions)), decideSlot sources t exclusions s = SlotStatus.pending

def demand_D011 : Prop := ∀ (sources : List SourceVersion) (t : ℕ)
    (exclusions : List String) (s : String)
    (hnone : applicableSources sources t = []) (hnot : ¬ (s ∈ exclusions)), decideSlot sources t exclusions s = SlotStatus.pending

def demand_D012 : Prop := ∀ (sources : List SourceVersion) (t : ℕ)
    (exclusions : List String) (s : String)
    (hnone : applicableSources sources t = []) (hnot : ¬ (s ∈ exclusions)), decideSlot sources t exclusions s = SlotStatus.pending

def demand_D013 : Prop := ∀ (sources : List SourceVersion) (t : ℕ)
    (exclusions : List String) (s : String)
    (hnone : applicableSources sources t = []) (hnot : ¬ (s ∈ exclusions)), decideSlot sources t exclusions s = SlotStatus.pending

def demand_D014 : Prop := ∀ (sources : List SourceVersion) (t : ℕ)
    (exclusions : List String) (s : String)
    (hnone : applicableSources sources t = []) (hnot : ¬ (s ∈ exclusions)), decideSlot sources t exclusions s = SlotStatus.pending

def demand_D015 : Prop := ∀ (sources : List SourceVersion) (t : ℕ)
    (exclusions : List String) (s : String)
    (hnone : applicableSources sources t = []) (hnot : ¬ (s ∈ exclusions)), decideSlot sources t exclusions s = SlotStatus.pending

def demand_D016 : Prop := ∀ (sources : List SourceVersion) (t : ℕ)
    (exclusions : List String) (s : String)
    (hnone : applicableSources sources t = []) (hnot : ¬ (s ∈ exclusions)), decideSlot sources t exclusions s = SlotStatus.pending

def demand_D017 : Prop := ∀ (sources : List SourceVersion) (t : ℕ)
    (exclusions : List String) (s : String)
    (hnone : applicableSources sources t = []) (hnot : ¬ (s ∈ exclusions)), decideSlot sources t exclusions s = SlotStatus.pending

def demand_D018 : Prop := ∀ (sources : List SourceVersion) (t : ℕ)
    (exclusions : List String) (s : String)
    (hnone : applicableSources sources t = []) (hnot : ¬ (s ∈ exclusions)), decideSlot sources t exclusions s = SlotStatus.pending

def demand_D019 : Prop := ∀ (k : ℕ) (v v' : ℚ) (l : List Obs), (dedup (⟨k, v'⟩ :: ⟨k, v⟩ :: l)).map Obs.id = (dedup (⟨k, v⟩ :: l)).map Obs.id

def demand_D020 : Prop := ∀ (k : ℕ) (v v' : ℚ) (l : List Obs), (dedup (⟨k, v'⟩ :: ⟨k, v⟩ :: l)).map Obs.id = (dedup (⟨k, v⟩ :: l)).map Obs.id

def demand_D021 : Prop := ∀ (k : ℕ) (v v' : ℚ) (l : List Obs), (dedup (⟨k, v'⟩ :: ⟨k, v⟩ :: l)).map Obs.id = (dedup (⟨k, v⟩ :: l)).map Obs.id

def demand_D022 : Prop := ∀ (k : ℕ) (v v' : ℚ) (l : List Obs), (dedup (⟨k, v'⟩ :: ⟨k, v⟩ :: l)).map Obs.id = (dedup (⟨k, v⟩ :: l)).map Obs.id

def demand_D023 : Prop := ∀ (k : ℕ) (v v' : ℚ) (l : List Obs), (dedup (⟨k, v'⟩ :: ⟨k, v⟩ :: l)).map Obs.id = (dedup (⟨k, v⟩ :: l)).map Obs.id

def demand_D024 : Prop := ∀ (k : ℕ) (v v' : ℚ) (l : List Obs), (dedup (⟨k, v'⟩ :: ⟨k, v⟩ :: l)).map Obs.id = (dedup (⟨k, v⟩ :: l)).map Obs.id

def demand_D025 : Prop := ∀ (k : ℕ) (v v' : ℚ) (l : List Obs), (dedup (⟨k, v'⟩ :: ⟨k, v⟩ :: l)).map Obs.id = (dedup (⟨k, v⟩ :: l)).map Obs.id

def demand_D026 : Prop := ∀ (k : ℕ) (v v' : ℚ) (l : List Obs), (dedup (⟨k, v'⟩ :: ⟨k, v⟩ :: l)).map Obs.id = (dedup (⟨k, v⟩ :: l)).map Obs.id

def demand_D027 : Prop := ∀ (k : ℕ) (v v' : ℚ) (l : List Obs), (dedup (⟨k, v'⟩ :: ⟨k, v⟩ :: l)).map Obs.id = (dedup (⟨k, v⟩ :: l)).map Obs.id

def demand_D028 : Prop := ∀ (k : ℕ) (v v' : ℚ) (l : List Obs), (dedup (⟨k, v'⟩ :: ⟨k, v⟩ :: l)).map Obs.id = (dedup (⟨k, v⟩ :: l)).map Obs.id

def demand_D029 : Prop := ∀ {A : Type} [DecidableEq A] (facts : List A) (rules : List (Rul A)), ∀ d a, a ∈ Generate facts rules d → WellFormed facts rules a ∧ Arg.height a ≤ d

def demand_D030 : Prop := ∀ {A : Type} [DecidableEq A] (facts : List A) (rules : List (Rul A)), ∀ d a, a ∈ Generate facts rules d → WellFormed facts rules a ∧ Arg.height a ≤ d

def demand_D031 : Prop := ∀ {A : Type} [DecidableEq A] (facts : List A) (rules : List (Rul A)), ∀ d a, a ∈ Generate facts rules d → WellFormed facts rules a ∧ Arg.height a ≤ d

def demand_D032 : Prop := ∀ {A : Type} [DecidableEq A] (facts : List A) (rules : List (Rul A)), ∀ d a, a ∈ Generate facts rules d → WellFormed facts rules a ∧ Arg.height a ≤ d

def demand_D033 : Prop := ∀ {A : Type} [DecidableEq A] (facts : List A) (rules : List (Rul A)), ∀ d a, a ∈ Generate facts rules d → WellFormed facts rules a ∧ Arg.height a ≤ d

def demand_D034 : Prop := ∀ {A : Type} [DecidableEq A] (facts : List A) (rules : List (Rul A)), ∀ d a, a ∈ Generate facts rules d → WellFormed facts rules a ∧ Arg.height a ≤ d

def demand_D035 : Prop := ∀ {A : Type} [DecidableEq A] (facts : List A) (rules : List (Rul A)), ∀ d a, a ∈ Generate facts rules d → WellFormed facts rules a ∧ Arg.height a ≤ d

def demand_D036 : Prop := ∀ {A : Type} [DecidableEq A] (facts : List A) (rules : List (Rul A)), ∀ d a, a ∈ Generate facts rules d → WellFormed facts rules a ∧ Arg.height a ≤ d

def demand_D037 : Prop := ∀ (i j : ℕ) (h : personSlot i = personSlot j), i = j

def demand_D038 : Prop := ∀ (i j : ℕ) (h : personSlot i = personSlot j), i = j

def demand_D039 : Prop := ∀ (i j : ℕ) (h : personSlot i = personSlot j), i = j

def demand_D040 : Prop := ∀ (i j : ℕ) (h : personSlot i = personSlot j), i = j

def demand_D041 : Prop := ∀ (i j : ℕ) (h : personSlot i = personSlot j), i = j

def demand_D042 : Prop := ∀ (i j : ℕ) (h : personSlot i = personSlot j), i = j

def demand_D043 : Prop := ∀ (i j : ℕ) (h : personSlot i = personSlot j), i = j

def demand_D044 : Prop := ∀ (i j : ℕ) (h : personSlot i = personSlot j), i = j

def demand_D045 : Prop := ∀ (i j : ℕ) (h : personSlot i = personSlot j), i = j

def demand_D046 : Prop := ∀ (i j : ℕ) (h : personSlot i = personSlot j), i = j

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

def demand_D065 : Prop := ∀ (d : Doc) (k v v' : String), docPut (docPut d k v) k v' = docPut d k v'

def demand_D066 : Prop := ∀ (d : Doc) (k v v' : String), docPut (docPut d k v) k v' = docPut d k v'

def demand_D067 : Prop := ∀ (d : Doc) (k v v' : String), docPut (docPut d k v) k v' = docPut d k v'

def demand_D068 : Prop := ∀ (d : Doc) (k v v' : String), docPut (docPut d k v) k v' = docPut d k v'

def demand_D069 : Prop := ∀ (d : Doc) (k v v' : String), docPut (docPut d k v) k v' = docPut d k v'

def demand_D070 : Prop := ∀ (d : Doc) (k v v' : String), docPut (docPut d k v) k v' = docPut d k v'

def demand_D071 : Prop := ∀ (d : Doc) (k v v' : String), docPut (docPut d k v) k v' = docPut d k v'

def demand_D072 : Prop := ∀ (d : Doc) (k v v' : String), docPut (docPut d k v) k v' = docPut d k v'

def demand_D073 : Prop := ∀ (d : Doc) (k v v' : String), docPut (docPut d k v) k v' = docPut d k v'

def demand_D074 : Prop := ∀ (d : Doc) (k v v' : String), docPut (docPut d k v) k v' = docPut d k v'

def demand_D075 : Prop := ∀ (d : Doc) (k v v' : String), docPut (docPut d k v) k v' = docPut d k v'

def demand_D076 : Prop := ∀ (d : Doc) (k v v' : String), docPut (docPut d k v) k v' = docPut d k v'

def demand_D077 : Prop := ∀ {A : Type} [DecidableEq A] [Fintype A] (R : Finset (Finset A × A)) (F P : Finset A)
    (hP : PreFixed R F P), ∀ n, cl R F n ⊆ P

def demand_D078 : Prop := ∀ {A : Type} [DecidableEq A] [Fintype A] (R : Finset (Finset A × A)) (F P : Finset A)
    (hP : PreFixed R F P), ∀ n, cl R F n ⊆ P

def demand_D079 : Prop := ∀ {A : Type} [DecidableEq A] [Fintype A] (R : Finset (Finset A × A)) (F P : Finset A)
    (hP : PreFixed R F P), ∀ n, cl R F n ⊆ P

def demand_D080 : Prop := ∀ {A : Type} [DecidableEq A] [Fintype A] (R : Finset (Finset A × A)) (F P : Finset A)
    (hP : PreFixed R F P), ∀ n, cl R F n ⊆ P

def demand_D081 : Prop := ∀ {A : Type} [DecidableEq A] [Fintype A] (R : Finset (Finset A × A)) (F P : Finset A)
    (hP : PreFixed R F P), ∀ n, cl R F n ⊆ P

def demand_D082 : Prop := ∀ {A : Type} [DecidableEq A] [Fintype A] (R : Finset (Finset A × A)) (F P : Finset A)
    (hP : PreFixed R F P), ∀ n, cl R F n ⊆ P

def demand_D083 : Prop := ∀ {A : Type} [DecidableEq A] [Fintype A] (R : Finset (Finset A × A)) (F P : Finset A)
    (hP : PreFixed R F P), ∀ n, cl R F n ⊆ P

def demand_D084 : Prop := ∀ {A : Type} [DecidableEq A] [Fintype A] (R : Finset (Finset A × A)) (F P : Finset A)
    (hP : PreFixed R F P), ∀ n, cl R F n ⊆ P

def demand_D085 : Prop := ∀ {A : Type} [DecidableEq A] [Fintype A] (R : Finset (Finset A × A)) (F P : Finset A)
    (hP : PreFixed R F P), ∀ n, cl R F n ⊆ P

def demand_D086 : Prop := ∀ {A : Type} [DecidableEq A] [Fintype A] (R : Finset (Finset A × A)) (F P : Finset A)
    (hP : PreFixed R F P), ∀ n, cl R F n ⊆ P

def demand_D087 : Prop := ∀ {A : Type} [DecidableEq A] [Fintype A] (af : AF A) (P : Finset A → Prop)
    (E : Finset A) (hstab : Stable af E) (hP : P E), ∃ E', Stable af E' ∧ P E'

def demand_D088 : Prop := ∀ {A : Type} [DecidableEq A] [Fintype A] (af : AF A) (P : Finset A → Prop)
    (E : Finset A) (hstab : Stable af E) (hP : P E), ∃ E', Stable af E' ∧ P E'

def demand_D089 : Prop := ∀ {A : Type} [DecidableEq A] [Fintype A] (af : AF A) (P : Finset A → Prop)
    (E : Finset A) (hstab : Stable af E) (hP : P E), ∃ E', Stable af E' ∧ P E'

def demand_D090 : Prop := ∀ {A : Type} [DecidableEq A] [Fintype A] (af : AF A) (P : Finset A → Prop)
    (E : Finset A) (hstab : Stable af E) (hP : P E), ∃ E', Stable af E' ∧ P E'

def demand_D091 : Prop := ∀ {A : Type} [DecidableEq A] [Fintype A] (af : AF A) (P : Finset A → Prop)
    (E : Finset A) (hstab : Stable af E) (hP : P E), ∃ E', Stable af E' ∧ P E'

def demand_D092 : Prop := ∀ {A : Type} [DecidableEq A] [Fintype A] (af : AF A) (P : Finset A → Prop)
    (E : Finset A) (hstab : Stable af E) (hP : P E), ∃ E', Stable af E' ∧ P E'

def demand_D093 : Prop := ∀ {A : Type} [DecidableEq A] [Fintype A] (af : AF A) (P : Finset A → Prop)
    (E : Finset A) (hstab : Stable af E) (hP : P E), ∃ E', Stable af E' ∧ P E'

def demand_D094 : Prop := ∀ {A : Type} [DecidableEq A] [Fintype A] (af : AF A) (P : Finset A → Prop)
    (E : Finset A) (hstab : Stable af E) (hP : P E), ∃ E', Stable af E' ∧ P E'

def demand_D095 : Prop := ∀ (y m d : ℕ) (h : d + 1 ≤ monthLen y m), dayOfYear y m (d + 1) = dayOfYear y m d + 1

def demand_D096 : Prop := ∀ (y m d : ℕ) (h : d + 1 ≤ monthLen y m), dayOfYear y m (d + 1) = dayOfYear y m d + 1

def demand_D097 : Prop := ∀ (y m d : ℕ) (h : d + 1 ≤ monthLen y m), dayOfYear y m (d + 1) = dayOfYear y m d + 1

def demand_D098 : Prop := ∀ (y m d : ℕ) (h : d + 1 ≤ monthLen y m), dayOfYear y m (d + 1) = dayOfYear y m d + 1

def demand_D099 : Prop := ∀ (y m d : ℕ) (h : d + 1 ≤ monthLen y m), dayOfYear y m (d + 1) = dayOfYear y m d + 1

def demand_D100 : Prop := ∀ (y m d : ℕ) (h : d + 1 ≤ monthLen y m), dayOfYear y m (d + 1) = dayOfYear y m d + 1

def demand_D101 : Prop := ∀ (y m d : ℕ) (h : d + 1 ≤ monthLen y m), dayOfYear y m (d + 1) = dayOfYear y m d + 1

def demand_D102 : Prop := ∀ (y m d : ℕ) (h : d + 1 ≤ monthLen y m), dayOfYear y m (d + 1) = dayOfYear y m d + 1

def demand_D103 : Prop := ∀ (y m d : ℕ) (h : d + 1 ≤ monthLen y m), dayOfYear y m (d + 1) = dayOfYear y m d + 1

def demand_D104 : Prop := ∀ (cs : List Char) (hplain : Plain cs), parseL (renderL cs) = some (cs, [])

def demand_D105 : Prop := ∀ (cs : List Char) (hplain : Plain cs), parseL (renderL cs) = some (cs, [])

def demand_D106 : Prop := ∀ (cs : List Char) (hplain : Plain cs), parseL (renderL cs) = some (cs, [])

def demand_D107 : Prop := ∀ (cs : List Char) (hplain : Plain cs), parseL (renderL cs) = some (cs, [])

def demand_D108 : Prop := ∀ (cs : List Char) (hplain : Plain cs), parseL (renderL cs) = some (cs, [])

def demand_D109 : Prop := ∀ (cs : List Char) (hplain : Plain cs), parseL (renderL cs) = some (cs, [])

def demand_D110 : Prop := ∀ (cs : List Char) (hplain : Plain cs), parseL (renderL cs) = some (cs, [])

def demand_D111 : Prop := ∀ (cs : List Char) (hplain : Plain cs), parseL (renderL cs) = some (cs, [])

def demand_D112 : Prop := ∀ (cs : List Char) (hplain : Plain cs), parseL (renderL cs) = some (cs, [])

def demand_D113 : Prop := ∀ (cs : List Char) (hplain : Plain cs), parseL (renderL cs) = some (cs, [])

def demand_D114 : Prop := ∀ (cs : List Char) (hplain : Plain cs), parseL (renderL cs) = some (cs, [])

def demand_D115 : Prop := ∀ (cs : List Char) (hplain : Plain cs), parseL (renderL cs) = some (cs, [])

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
