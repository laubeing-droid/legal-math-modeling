import JurisLean.FullMath.Tranche1
import JurisLean.FullMath.Tranche2
import JurisLean.FullMath.Tranche3
import JurisLean.FullMath.Tranche4
import JurisLean.FullMath.Tranche5
import JurisLean.FullMath.Tranche6
import JurisLean.FullMath.Tranche7
import JurisLean.Seams.UnifiedCalendar
import JurisLean.Seams.UnifiedQuantLedger

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
open JurisLean.Seams.UnifiedCalendar (CalDate daysDiff toEpochDay PeriodSpec
  nextBiz backSchedule addCalDays addCalMonths syntheticWeekend)
open JurisLean.Seams.UnifiedQuantLedger (LedgerItem DebtKind FeeBasis
  ClaimStatus outstanding loanLedger afterStream afterPay allocsOf demoLedger
  StreamLegal InterestSeg LoanCharges termInterest segInterest ChargesWithin
  totalCharges sampleAll sampleNoPenalty SecKind SecEvent requiredEvent
  secEstablished corpSuretyEstablished distributeProceeds FactCand admittedFact
  CashRule CashFact statusConsistent)
open JurisLean.Seams.UnifiedQuantities (remainingAfter)

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

/-! D047-D056 (group 06 借贷、担保与共同债务, W2-A batch B06): each def is
that demand's own contract, translated from ALL_134_MATH_CONTRACTS.md.
The first conjunct is the group-registered quantity component (both parts
of the covered/uncovered split stay nonnegative — amounts never go below
zero through any decomposition); the remaining conjuncts are the demand's
own operational semantics with its adverse case, consumed from the shared
quantity-ledger carrier `Seams/UnifiedQuantLedger.lean` (B06 prerequisite,
module round green) plus the group-local qualitative encodings below. -/

/-- D048/D056 helper: a supported contract-stipulated ledger row owed to
beneficiary 0 — the seven-field debt identity (ident/kind/basis/
beneficiary/status/amount) of the shared carrier, spelled short for the
witness ledgers. -/
def loanRow (id : ℕ) (k : DebtKind) (amt : ℚ) : LedgerItem :=
  { ident := id, kind := k, basis := FeeBasis.contractStip, beneficiary := 0,
    status := ClaimStatus.supported, amount := amt }

/-- D047 交付事实与清偿事实分别进入责任链（反例：出借记录不能自动证明
后来未清偿）：借款已实际交付才入账——未交付的借条余额恒为零；清偿判定
与付足等价（余额为零 ⇔ 总支付覆盖全部到期额）；交付 200、还款流 150 ⇒
余额 50，仅有交付记录（无还款）余额 200——两事实分别读出；而仅有出借
记录不蕴含未清偿：同一账本补一条 200 的还款流后余额恰为零。 -/
def demand_D047 : Prop :=
  (∀ (r : ℚ), 0 ≤ covered r ∧ 0 ≤ uncovered r) ∧
  ((∀ (id : ℕ) (p : ℚ), outstanding (loanLedger false id p) = 0) ∧
   (∀ (items : List LedgerItem), (∀ it ∈ items, 0 ≤ it.amount) →
      ∀ (ps : List ℚ), (∀ p ∈ ps, 0 ≤ p) →
        (outstanding (afterStream ps items) = 0 ↔ outstanding items ≤ ps.sum)) ∧
   (outstanding (afterStream [150] (loanLedger true 1 200)) = 50 ∧
    outstanding (loanLedger true 1 200) = 200) ∧
   outstanding (afterStream [200] (loanLedger true 1 200)) = 0)

/-- D048 抵充账本按准入顺序更新（反例：同一还款同时全额扣本金、又全额扣
利息应拒绝）：每笔分配逐项非负、分配总额不超过该笔付款，支付后债项身份
逐笔保持（余额可追踪）；同一支付 ID 出现两次的支付流非法；准入顺序见证
——费用 10→利息 100→本金 200 的账本支付 150 逐项抵充恰为 (10, 100, 40)；
对利息 100＋本金 200 的账本，真实抵充是 [100, 50]——"同时全额扣本金又全
额扣利息"的 [100, 200] 永不成立。 -/
def demand_D048 : Prop :=
  (∀ (r : ℚ), 0 ≤ covered r ∧ 0 ≤ uncovered r) ∧
  ((∀ (items : List LedgerItem) (p : ℚ), (∀ it ∈ items, 0 ≤ it.amount) →
      0 ≤ p → (∀ a ∈ allocsOf p items, 0 ≤ a) ∧ (allocsOf p items).sum ≤ p ∧
        (afterPay p items).map LedgerItem.ident = items.map LedgerItem.ident) ∧
   ¬ StreamLegal [(7, 100), (7, 50)] ∧
   allocsOf 150 demoLedger = [10, 100, 40] ∧
   (allocsOf 150 [loanRow 2 DebtKind.interest 100, loanRow 3 DebtKind.principal 200]
        = [100, 50] ∧
    ¬ allocsOf 150 [loanRow 2 DebtKind.interest 100,
        loanRow 3 DebtKind.principal 200] = [100, 200]))

/-- D049 借期利息、逾期利息、违约金分别形成计算组件，组合受适用政策限制
（反例：相似百分比不能默认三项全叠加）：组件独立——借期利息不随逾期参数
（利率/天数）变化；分段可加——任意天数处切两段之和等于整段（整数天，不换
月）；政策上限谓词之上组合总额受上限约束——本金 100、三组件各 10 的全叠加
30 超上限 24 被拒，去掉违约金组件后 20 在限内。 -/
def demand_D049 : Prop :=
  (∀ (r : ℚ), 0 ≤ covered r ∧ 0 ≤ uncovered r) ∧
  ((∀ (c : LoanCharges) (r : ℚ) (d : ℕ),
      termInterest { c with overdueRate := r, overdueDays := d } = termInterest c) ∧
   (∀ (s : InterestSeg) (d1 d2 : ℕ), s.denom ≠ 0 → s.days = d1 + d2 →
      segInterest { s with days := d1 } + segInterest { s with days := d2 }
        = segInterest s) ∧
   (∀ (cap : ℚ) (c : LoanCharges), ChargesWithin cap c → totalCharges c ≤ cap) ∧
   (¬ ChargesWithin 24 sampleAll ∧ ChargesWithin 24 sampleNoPenalty))

/-- D050 保证/抵押/质押以不同法律关系、设立事件、效力与救济表示（反例：
签担保文件不自动证明登记完成或财产已交付）：三类型的设立要件事件互不相
同——保证以签署、抵押以登记、质押以交付设立，抵押要件与质押要件是两个
不同事件；要件事件不在事实集中即不设立——仅有签署的记录既不设立抵押也
不设立质押，而同一签署即设立保证，登记齐备的抵押设立；担保物价款按顺位
优先分配：各顺位受偿和＋剩余＝价款，后顺位得正 ⇒ 前顺位债权全清。 -/
def demand_D050 : Prop :=
  (∀ (r : ℚ), 0 ≤ covered r ∧ 0 ≤ uncovered r) ∧
  ((requiredEvent SecKind.suretyship = SecEvent.signed ∧
    requiredEvent SecKind.mortgage = SecEvent.registered ∧
    requiredEvent SecKind.pledge = SecEvent.delivered ∧
    requiredEvent SecKind.mortgage ≠ requiredEvent SecKind.pledge) ∧
   (¬ secEstablished SecKind.mortgage [SecEvent.signed] ∧
    ¬ secEstablished SecKind.pledge [SecEvent.signed] ∧
    secEstablished SecKind.suretyship [SecEvent.signed] ∧
    secEstablished SecKind.mortgage [SecEvent.signed, SecEvent.registered]) ∧
   ((∀ (claims : List ℚ) (proceeds : ℚ),
       (distributeProceeds claims proceeds).sum + remainingAfter claims proceeds
         = proceeds) ∧
    (∀ (claims : List ℚ), (∀ c ∈ claims, 0 ≤ c) → ∀ (proceeds : ℚ) (k : ℕ),
       0 < (List.drop k (distributeProceeds claims proceeds)).sum →
         List.take k (distributeProceeds claims proceeds) = List.take k claims)))

/-- D051 决议存在、程序、代表权限及担保效力分别建谓词并按规则连接（反
例：仅无决议字段不得由一条统一规则宣布所有担保无效）：公司保证的设立是
决议存在＋签署两要件的合取——要件谓词分别可判、按规则连接（缺一即不设
立）；同一"仅有签署"事件集下公司保证未设立而自然人保证设立——无效力判
定走类型化要件，不是一条统一无效规则；决议与签署齐备的公司保证设立。 -/
def demand_D051 : Prop :=
  (∀ (r : ℚ), 0 ≤ covered r ∧ 0 ≤ uncovered r) ∧
  ((∀ (evs : List SecEvent),
      corpSuretyEstablished evs ↔
        (SecEvent.boardResolution ∈ evs ∧ SecEvent.signed ∈ evs)) ∧
   (¬ corpSuretyEstablished [SecEvent.signed] ∧
    secEstablished SecKind.suretyship [SecEvent.signed]) ∧
   corpSuretyEstablished [SecEvent.boardResolution, SecEvent.signed])

/-- D052 helper: signing capacity — own name, or on behalf of a principal
(the representation relation). -/
inductive SigningCapacity : Type
  | ownName | onBehalfOf (principal : ℕ)
  deriving DecidableEq

/-- D052 helper: the responsible subject of a signature — the represented
principal when the representation relation points at one, otherwise the
signer; signer, nominal capacity, contract party and responsible person
are separately encoded fields. -/
def respOf (signer : ℕ) (cap : SigningCapacity) : ℕ :=
  match cap with
  | .ownName => signer
  | .onBehalfOf p => p

/-- D052 签字人、名义、代表关系、合同当事人和责任人分别编码（反例：签名
文本为自然人名不自动由其个人承担全部合同义务）：责任人按代表关系连接——
代表关系指向公司时责任人是被代表主体而非签字自然人（签名文本为自然人名
不改变责任人），以自己名义签署时责任人即签字人；账本侧受益人字段独立于
金额字段，支付抵充逐笔保持受益人（当事人身份不随抵充漂移）。 -/
def demand_D052 : Prop :=
  (∀ (r : ℚ), 0 ≤ covered r ∧ 0 ≤ uncovered r) ∧
  ((∀ (signer p : ℕ), respOf signer (.onBehalfOf p) = p) ∧
   (∀ signer : ℕ, respOf signer .ownName = signer) ∧
   respOf 3 (.onBehalfOf 7) ≠ 3 ∧
   (∀ (p : ℚ) (items : List LedgerItem),
      (afterPay p items).map LedgerItem.beneficiary
        = items.map LedgerItem.beneficiary))

/-- D053 helper: the spousal-debt issues as independent fields — marriage
period, spouse signature, common intent, household/business use. -/
structure SpousalDebt where
  inMarriage : Bool
  spouseSigned : Bool
  commonIntent : Bool
  householdUse : Bool

/-- D053 helper: joint attribution requires the spouse signature or the
common-intent + household-use pair — never the marriage period alone. -/
def jointDebt (d : SpousalDebt) : Bool :=
  d.spouseSigned || (d.commonIntent && d.householdUse)

/-- D053 婚姻期间、签字、共同意思、用途和债务归属为独立争点（反例：婚内
借款不自动推出夫妻共同债务）：共同债务归属由"配偶签字"或"共同意思＋共同
生活/经营用途"判定，与婚姻期间字段无关（翻转婚姻期间不改变归属判定——
期间是独立争点，不是归属规则）；婚内（期间真）而无签字、无共同意思、无
共同用途的借款不是共同债务；配偶签字成立归属，共同意思＋共同用途同样成
立。 -/
def demand_D053 : Prop :=
  (∀ (r : ℚ), 0 ≤ covered r ∧ 0 ≤ uncovered r) ∧
  ((∀ d : SpousalDebt,
      jointDebt { d with inMarriage := true }
        = jointDebt { d with inMarriage := false }) ∧
   jointDebt ⟨true, false, false, false⟩ = false ∧
   (jointDebt ⟨true, true, false, false⟩ = true ∧
    jointDebt ⟨true, false, true, true⟩ = true))

/-- D054 helper: company-relation evidence edges — shared resources (a
phone number, an address) are light edges; commingled funds and one-way
control are heavy edges. -/
inductive CorpEdge : Type
  | sharedPhone | sharedAddress | commingledFunds | underControl
  deriving DecidableEq

/-- D054 helper: the separate evaluation rule — personality mixing is
reached only through the heavy edges (commingled funds or one-way
control); light edges never reach it by themselves. -/
def personalityMix (edges : List CorpEdge) : Prop :=
  CorpEdge.commingledFunds ∈ edges ∨ CorpEdge.underControl ∈ edges

/-- D054 helper: the joint-liability consequence attaches only through
the evaluation rule — never directly from an evidence edge. -/
def corpJointDue (edges : List CorpEdge) : Prop := personalityMix edges

/-- D054 公司关系证据形成支持图；人格混同等评价与连带后果单独规则连接
（反例：共用电话不直接生成无限连带责任边）：连带后果恰好由人格混同评价
规则给出（评价与后果是单独一层，不与证据边混写）；仅有共用电话/地址的
证据图既不达人格混同评价、也不生成连带后果；出现资金混同或单向控制的
证据图两项皆达。 -/
def demand_D054 : Prop :=
  (∀ (r : ℚ), 0 ≤ covered r ∧ 0 ≤ uncovered r) ∧
  ((∀ edges : List CorpEdge, corpJointDue edges ↔ personalityMix edges) ∧
   (¬ personalityMix [CorpEdge.sharedPhone] ∧
    ¬ corpJointDue [CorpEdge.sharedPhone, CorpEdge.sharedAddress]) ∧
   (personalityMix [CorpEdge.commingledFunds] ∧
    corpJointDue [CorpEdge.underControl]))

/-- D055 资金来源和现金能力是有来源的事实候选；不足即未证而非虚构负事
实（反例：收入低不自动证明不可能现金出借）：无来源候选不进事实（未证），
有来源候选照常准入；从"收入低"到"不可能现金出借"没有任何获准规则（空
规则基——收入再低也不生成负事实）；同一标识的有源/无源两候选准入判定不
同（来源字段真实参与判定）。 -/
def demand_D055 : Prop :=
  (∀ (r : ℚ), 0 ≤ covered r ∧ 0 ≤ uncovered r) ∧
  ((∀ id : ℕ, ¬ (admittedFact (FactCand.unsourced id) = true)) ∧
   (∀ id : ℕ, admittedFact (FactCand.sourced id) = true) ∧
   ¬ CashRule CashFact.incomeLow CashFact.cashImpossible ∧
   admittedFact (FactCand.sourced 3) ≠ admittedFact (FactCand.unsourced 3))

/-- D056 律师费、诉讼费、保全费等使用独立债项/基础/受益人/请求状态（反
例：自身工时报价不能自动作为对方应赔律师费）：三费用分型互异且与本金分
型不同（各自是独立的债项种类）；请求状态与基础的一致性要求 supported
状态须有可支撑基础——自身工时报价的律师费行不自动 supported，合同约定
基础的行可 supported；按 Bool 谓词分组的分组和相加＝总额（分组聚合不丢
不重）。 -/
def demand_D056 : Prop :=
  (∀ (r : ℚ), 0 ≤ covered r ∧ 0 ≤ uncovered r) ∧
  ((DebtKind.attorneyFee ≠ DebtKind.courtFee ∧
    DebtKind.attorneyFee ≠ DebtKind.preservationFee ∧
    DebtKind.courtFee ≠ DebtKind.preservationFee ∧
    DebtKind.attorneyFee ≠ DebtKind.principal) ∧
   (¬ statusConsistent
      { ident := 5, kind := DebtKind.attorneyFee, basis := FeeBasis.selfQuoted,
        beneficiary := 2, status := ClaimStatus.supported, amount := 3000 } ∧
    statusConsistent
      { ident := 6, kind := DebtKind.attorneyFee, basis := FeeBasis.contractStip,
        beneficiary := 2, status := ClaimStatus.supported, amount := 3000 }) ∧
   (∀ (f : LedgerItem → Bool) (items : List LedgerItem),
      ((items.filter f).map LedgerItem.amount).sum
        + ((items.filter (fun it => !f it)).map LedgerItem.amount).sum
        = (items.map LedgerItem.amount).sum))

/-! D057-D064 (group 07 侵权责任与损害, W2-A batch B07): each def is
that demand's own contract, translated from ALL_134_MATH_CONTRACTS.md.
The first conjunct is the group-registered interval component (for a
fixed second factor every product with a member of the interval lies
between the two endpoint products — the ratio-times-loss kernel of
every sharing/computation figure); the remaining conjuncts are the
demand's own operational semantics with its adverse case, consumed from
the shared quantity-ledger carrier `Seams/UnifiedQuantLedger.lean`
(B07 prerequisite, module round green: the interval constructions QIv
and TIv, tort kinds, gates/shares, liability modes, the loss ledger,
remedies and scenario witnesses). -/

open JurisLean.Seams.UnifiedQuantLedger (TortKind TortCand
  selectByElements toResidual
  IvTag TIv tMem tScale FaultOK causeTimesLoss imputed ivStrongCause
  ivCause ivLossC ivLossA ivLossB ivInter
  Shares LegalShares badShares goodShares
  RespMode externalDue JointRecoveryOK recourseOf deficitOf suppDistribution
  pays_sum_base
  LossEntry lossTotal dedupFirst invoiceEntry appraisalEntry
  Remedy amountOf monetaryTotal
  ScenarioWitness SummaryRecord FromSameWitness wA wB mixedRecord)

open JurisLean.Seams.UnifiedQuantLedger.QIv

/-- D057 侵权类型候选按要件选择，开放残余不强制塞既有类别（反例：分类器
不认识的新情形不能返回无任何请求权）：要件满足与否决定入选/入残余——
要件未满足的候选必落入残余桶且不入选择；每个候选必落入选择或残余之一
（双向 filter 覆盖全部候选）；分类器不认识的残余情形与可归类的既有情形
并存——残余桶恰一、选择桶恰一，新情形保留请求权载体而非返回空账。 -/
def demand_D057 : Prop :=
  (∀ (i : Iv) (x y : ℚ) (hx : mem x i),
      min (i.lo * y) (i.hi * y) ≤ x * y ∧ x * y ≤ max (i.lo * y) (i.hi * y)) ∧
  ((∀ (cands : List TortCand) (c : TortCand), c ∈ cands →
      c.elementsMet = false → c ∈ toResidual cands ∧ c ∉ selectByElements cands) ∧
   (∀ (cands : List TortCand) (c : TortCand), c ∈ cands →
      c ∈ selectByElements cands ∨ c ∈ toResidual cands) ∧
   (toResidual [⟨TortKind.openResidual, false⟩,
       ⟨TortKind.general, true⟩]).length = 1 ∧
   (selectByElements [⟨TortKind.openResidual, false⟩,
       ⟨TortKind.general, true⟩]).length = 1)

/-- D058 行为—损害—因果—过错是类型化关系；统计因果与法律归责分层（反
例：相关性显著不直接推出法律上的相当因果或责任）：损失/因果度量/过错比
例三区间标签互异（跨标签运算在类型层被拒）；因果度量区间×损失区间的四
端点乘积健全（统计因果度量的分担乘积仍是损失区间）；过错比例区间的
[0,1] 良构在 [0,1] 缩放下保持；法律归责门与统计度量分层——归责任须门开
且因果度量下界为正（等价刻画），因果度量再强 [9/10,1] 而归责门关则不归
责；因果度量 [1/3,2/3] 乘损失 [90,120] 恰得 [30,80]。 -/
def demand_D058 : Prop :=
  (∀ (i : Iv) (x y : ℚ) (hx : mem x i),
      min (i.lo * y) (i.hi * y) ≤ x * y ∧ x * y ≤ max (i.lo * y) (i.hi * y)) ∧
  ((IvTag.cause ≠ IvTag.loss ∧ IvTag.loss ≠ IvTag.fault ∧
      IvTag.cause ≠ IvTag.fault) ∧
   (∀ (ci : TIv IvTag.cause) (li : TIv IvTag.loss) (x y : ℚ),
      tMem x ci → tMem y li → tMem (x * y) (causeTimesLoss ci li)) ∧
   (∀ (a : TIv IvTag.fault) (c : ℚ) (ha : FaultOK a) (hc0 : 0 ≤ c) (hc1 : c ≤ 1),
      FaultOK (tScale c hc0 a)) ∧
   ((∀ (g : Bool) (ci : TIv IvTag.cause),
       imputed g ci ↔ (g = true ∧ 0 < ci.iv.lo)) ∧
    ¬ imputed false ivStrongCause) ∧
   (causeTimesLoss ivCause ivLossC).iv.lo = 30 ∧
   (causeTimesLoss ivCause ivLossC).iv.hi = 80)

/-- D059 成立门和份额选择分开；无责任不得被赋正赔偿份额（反例：用小比
例掩盖根本不承担该责任的主体）：份额配置的成立门（gate）与份额（share）
是分立字段，合法性谓词只做连接——门关 ⇒ 份额恰为零；门关却赋 1/10 份额
的配置非法（小比例不能掩盖无责任）；门全开、份额 1/4＋3/4 的配置合法。 -/
def demand_D059 : Prop :=
  (∀ (i : Iv) (x y : ℚ) (hx : mem x i),
      min (i.lo * y) (i.hi * y) ≤ x * y ∧ x * y ≤ max (i.lo * y) (i.hi * y)) ∧
  ((∀ {ι : Type} [Fintype ι] (s : Shares ι), LegalShares s →
      ∀ i, s.gate i = false → s.share i = 0) ∧
   ¬ LegalShares badShares ∧
   LegalShares goodShares)

/-- D060 分别建按份、连带、补充等外部给付义务与内部追偿关系（反例：同
一损害多个连带债务全额相加造成超额受偿）：三种责任方式的外部给付义务分
别给出——按份＝内部份额、连带＝全额损失、补充＝损失超出主责清偿部分与
补充责任额的较小者；连带外部偿付总约束——受偿总额不超过损失，两笔全额
100 相加成 200 违反约束；内部追偿池平衡——总付款＝总内部份额时多付总额
＝缺额总额（追偿池＝缺额池，无中生有的追偿不可能）；补充责任顺序语义
——主责任人足额清偿 ⇒ 补充方分配恰为零。 -/
def demand_D060 : Prop :=
  (∀ (i : Iv) (x y : ℚ) (hx : mem x i),
      min (i.lo * y) (i.hi * y) ≤ x * y ∧ x * y ≤ max (i.lo * y) (i.hi * y)) ∧
  ((∀ (loss share p d : ℚ), externalDue RespMode.several loss share p d = share) ∧
   (∀ (loss share p d : ℚ), externalDue RespMode.joint loss share p d = loss) ∧
   (∀ (loss share p d : ℚ),
      externalDue RespMode.supplementary loss share p d = min (max (loss - p) 0) d) ∧
   ¬ JointRecoveryOK 100 [100, 100] ∧
   (∀ {ι : Type} [Fintype ι] (paid internalShare : ι → ℚ),
      ∑ i, paid i = ∑ i, internalShare i →
      ∑ i, recourseOf (paid i) (internalShare i)
        = ∑ i, deficitOf (paid i) (internalShare i)) ∧
   (∀ (p d loss : ℚ), loss ≤ p → 0 ≤ d → suppDistribution p d loss = [loss, 0]))

/-- D061 损失账本按损害事件、受益人、项目和时间去重，再执行明确聚合
（反例：发票额和同一损失评估额不得无条件双计）：去重后键（损害事件，受
益人，项目，时间）无重复；非负账项下去重不虚增（去重后总额不超过原总
额）；键本无重复时去重是恒等（无重复账目不被误删）；发票额 1000 与同一
损失键的评估额 800 双计成 1800 被首见去重压回 1000。 -/
def demand_D061 : Prop :=
  (∀ (i : Iv) (x y : ℚ) (hx : mem x i),
      min (i.lo * y) (i.hi * y) ≤ x * y ∧ x * y ≤ max (i.lo * y) (i.hi * y)) ∧
  ((∀ (l : List LossEntry), ((dedupFirst l).map LossEntry.key).Nodup) ∧
   (∀ (l : List LossEntry), (∀ e ∈ l, 0 ≤ e.amount) →
      lossTotal (dedupFirst l) ≤ lossTotal l) ∧
   (∀ (l : List LossEntry), (l.map LossEntry.key).Nodup → dedupFirst l = l) ∧
   lossTotal (dedupFirst [invoiceEntry, appraisalEntry]) = 1000 ∧
   lossTotal [invoiceEntry, appraisalEntry] = 1800)

/-- D062 逐方给付满足外部偿付总约束及内部规则；共享损失基数一致（反例：
把外部连带金额按内部份额削减，须发现语义不符）：份额和为一 ⇒ 逐方按份
给付之和恰等于共享损失基数（1/4＋3/4 份额乘基数 100 恰得 100）；连带方外
部义务是全额损失，份额小于损失时两者必不相等；外部偿付总约束谓词恰是
受偿总额不超损失（等价刻画，单笔全额 100 的受偿合法）；内部追偿池平衡
——总付款＝总内部份额时追偿池＝缺额池；区间端点代数——加法结合/交换、
非负缩放对加法分配、缩放结合，份额×损失的区间计算与逐方加总一致（损失
区间 [100,200] 与 [150,300] 求交得 [150,200]——共同基数带）。 -/
def demand_D062 : Prop :=
  (∀ (i : Iv) (x y : ℚ) (hx : mem x i),
      min (i.lo * y) (i.hi * y) ≤ x * y ∧ x * y ≤ max (i.lo * y) (i.hi * y)) ∧
  ((∀ {ι : Type} [Fintype ι] (base : ℚ) (share : ι → ℚ), ∑ i, share i = 1 →
      ∑ i, share i * base = base) ∧
   (∀ (loss share : ℚ), 0 < loss → share < loss →
      externalDue RespMode.joint loss share 0 0 ≠ share) ∧
   ((∀ (loss : ℚ) (recoveries : List ℚ),
       JointRecoveryOK loss recoveries ↔ recoveries.sum ≤ loss) ∧
    JointRecoveryOK 100 [100]) ∧
   (∀ {ι : Type} [Fintype ι] (paid internalShare : ι → ℚ),
      ∑ i, paid i = ∑ i, internalShare i →
      ∑ i, recourseOf (paid i) (internalShare i)
        = ∑ i, deficitOf (paid i) (internalShare i)) ∧
   (∀ (i j k : Iv), Iv.add (Iv.add i j) k = Iv.add i (Iv.add j k)) ∧
   (∀ (i j : Iv), Iv.add i j = Iv.add j i) ∧
   (∀ (c : ℚ) (hc : 0 ≤ c) (i j : Iv),
      vscale c hc (Iv.add i j) = Iv.add (vscale c hc i) (vscale c hc j)) ∧
   (∀ (c1 c2 : ℚ) (h1 : 0 ≤ c1) (h2 : 0 ≤ c2) (i : Iv),
      vscale c1 h1 (vscale c2 h2 i) = vscale (c1 * c2) (mul_nonneg h1 h2) i) ∧
   vinter ivLossA ivLossB = some ivInter ∧
   (∑ i : Fin 2, goodShares.share i * 100) = 100)

/-- D063 恢复原状、停止侵害等非金钱救济为动作/状态目标，不强转人民币
（反例：道歉或禁令不能当赔偿金额零而消失）：非金钱救济没有金额视图——
恢复原状/停止侵害/赔礼道歉的金额视图皆为 none（不伪装成 0）；金钱赔偿的
金额视图恰为该金额；金钱投影是盲区——两份清单金钱总额同为 100 而非金钱
义务不同（清单身份仍区分，道歉不因金额为零而消失）。 -/
def demand_D063 : Prop :=
  (∀ (i : Iv) (x y : ℚ) (hx : mem x i),
      min (i.lo * y) (i.hi * y) ≤ x * y ∧ x * y ≤ max (i.lo * y) (i.hi * y)) ∧
  ((amountOf Remedy.restitution = none ∧
    amountOf Remedy.cessation = none ∧
    amountOf Remedy.apology = none) ∧
   (∀ (q : ℚ), amountOf (Remedy.moneyAmt q) = some q) ∧
   (monetaryTotal [Remedy.moneyAmt 100, Remedy.apology] = 100 ∧
    monetaryTotal [Remedy.moneyAmt 100] = 100 ∧
    [Remedy.moneyAmt 100, Remedy.apology] ≠ [Remedy.moneyAmt 100]))

/-- D064 总结中每项责任、比例、数值和限制来自同一场景见证（反例：不同
情景各取最有利结果拼成无条件总结）：来自同一见证的记录恰以该见证的场景
号/比例/数值三投影为其字段（FromSameWitness 的展开刻画——字段不来自别
处）；同一见证 ⇒ 总结继承见证的比例守恒（见证比例和为一 ⇒ 记录比例和为
一）；跨场景拼接的记录——场景 1 的身份配场景 2 的数值——不是任何单一场
景见证的总结。 -/
def demand_D064 : Prop :=
  (∀ (i : Iv) (x y : ℚ) (hx : mem x i),
      min (i.lo * y) (i.hi * y) ≤ x * y ∧ x * y ≤ max (i.lo * y) (i.hi * y)) ∧
  ((∀ (r : SummaryRecord) (w : ScenarioWitness), FromSameWitness r w →
      r.scenId = w.scenId ∧ r.ratios = w.ratios ∧ r.values = w.values) ∧
   (∀ (r : SummaryRecord) (w : ScenarioWitness), FromSameWitness r w →
      w.ratios.sum = 1 → r.ratios.sum = 1) ∧
   (¬ FromSameWitness mixedRecord wA ∧ ¬ FromSameWitness mixedRecord wB))

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

/-! D095-D103 (group 11 金额、时间和经济敞口, W2-A batch B11): each def is
that demand's own contract, translated from ALL_134_MATH_CONTRACTS.md.
The first conjunct of every demand is the group-registered calendar
component inlined as `succDay_ordinal_mono` (month-ordinal monotonicity
under same-month succession — integer day order, leap years and month
lengths from the unified calendar); the remaining conjuncts are the
demand's own operational semantics with its adverse case. The calendar
surface (CalDate, toEpochDay, daysDiff, addCalDays, addCalMonths,
PeriodSpec, nextBiz, backSchedule, syntheticWeekend) is consumed from
`Seams/UnifiedCalendar.lean`, never redefined here; amounts are ℚ and
day counts are exact ℤ. -/

/-- D095 helper: interest accrued on one segment — base × daily rate ×
the exact ℤ day count from the unified calendar (independent base,
independent period, exact days; no 30-day averaging). -/
def taInterestSeg (base rate : ℚ) (a b : CalDate) : ℚ :=
  base * rate * ((daysDiff a b : ℤ) : ℚ)

/-- D095 helper: waterfall imputation of one payment across a list of
debt components (fees, interest, penalty, principal …) — each component
is covered only from what remains after the previous ones (守恒抵充:
a payment is never double-spent, never lost). -/
def taImputeAll (pay : ℚ) : List ℚ → List ℚ
  | [] => []
  | b :: rest => min pay b :: taImputeAll (pay - min pay b) rest

/-- D096 helper: the applicable benchmark at one epoch day under a
one-step policy — from the event day on, the new benchmark applies;
before it, the old one (the event date and the legal policy decide,
not the current date). -/
def taStepRate (eventDay : ℤ) (oldRate newRate : ℚ) (day : ℤ) : ℚ :=
  if eventDay ≤ day then newRate else oldRate

/-- D096 helper: the interest-rate multiple acts only on a confirmed
benchmark — an unconfirmed base passes through unchanged. -/
def taCappedMult (mult : ℚ) (confirmed : Bool) (base : ℚ) : ℚ :=
  if confirmed then mult * base else base

/-- D097 helper: total consideration of one cash + stock leg — cash
plus share count × per-share price (share count and per-share price
are different dimensions; their product is the money amount). -/
def taConsideration (cash shares price : ℚ) : ℚ := cash + shares * price

/-- D097 helper: explicit rounding to whole currency units — applied
once, at the declared stage of the derivation. -/
def taRound (x : ℚ) : ℚ := ((⌊x⌋ : ℤ) : ℚ)

/-- D098 helper: has the prepayment date reached the trigger date (the
month-arithmetic deadline, month-end clamped)? -/
def taTriggered (trigger prepay : CalDate) : Bool :=
  decide (toEpochDay trigger ≤ toEpochDay prepay)

/-- D098 helper: the make-whole premium due — only when the trigger
date is reached AND the ratio is positive (trigger day and applicable
ratio verified jointly). -/
def taMakeWhole (triggered : Bool) (balance ratio : ℚ) : ℚ :=
  if triggered && decide (0 < ratio) then balance * ratio else 0

/-- D099 helper: has this period's (business-day-rolled) deadline
arrived by the given epoch day? -/
def taDeadlineArrived (p : PeriodSpec) (day : ℤ) : Bool :=
  decide (p.deadline ≤ day)

/-- D099 helper: the termination right on one period arises only when
the deadline has arrived AND the arrival is evidenced — either missing
blocks it (the 30-day notice expiring never substitutes for the
60-day cure period). -/
def taRightArises (arrived evidenced : Bool) : Bool := arrived && evidenced

/-- D100 helper: back-scheduling one item from its deadline by the lead
days; a start that falls before the floor date (for example today) is
reported as a conflict (none), never silently clamped into an
executable plan. -/
def taBackItem (floor deadline : CalDate) (lead : ℕ) : Option CalDate :=
  match backSchedule deadline lead with
  | some s => if toEpochDay floor ≤ toEpochDay s then some s else none
  | none => none

/-- D101 helper: the four exposure kinds — debt principal (a balance),
accrued cost, income risk (a contingent, scenario-valued exposure)
and contingent compensation; distinct labels, so a risk figure can
never pose as a realized amount. -/
def taExpDebt : ℕ := 0

def taExpCost : ℕ := 1

def taExpRisk : ℕ := 2

def taExpContingent : ℕ := 3

/-- D101 helper: the declared aggregation — realized items (debt,
cost) sum directly; contingent items enter only through the declared
risk function (probability-weighted), never as raw amounts. -/
def taAggregate (debt cost : ℚ) (contingent : List ℚ) (prob : ℚ) : ℚ :=
  debt + cost + (contingent.map (fun c => prob * c)).sum

/-- D102 helper: the survival update of one obligation row on
termination — an accrued payable (kind 0) survives verbatim (never
cleared together with the main performance); a main performance
obligation (kind 1) survives only the part already complete at the
termination day; any undeclared kind contributes nothing (fail-closed). -/
def taSurvivalUpdate (kind : ℕ) (amount : ℚ) (endDay termDay : ℤ) : ℚ :=
  match kind with
  | 0 => amount
  | 1 => if endDay ≤ termDay then amount else 0
  | _ => 0

/-- D103 helper: working capital under one declared definition — the
same account scope at any reference date, minus the same exclusion
list (same definition, same exclusions; only the reference date
differs). -/
def taWorkingCapital : List (String × ℚ) → List String → ℚ
  | [], _ => 0
  | (name, v) :: rest, exclusions =>
      if exclusions.contains name then taWorkingCapital rest exclusions
      else v + taWorkingCapital rest exclusions

/-- D103 helper: the price adjustment — closing working capital minus
target working capital, both computed by the same definition; the
reconciliation difference is exact. -/
def taAdjustment (target closing : ℚ) : ℚ := closing - target

/-- D095 本息违约金费用按独立基数、期间和组合规则解释并守恒抵充（反例：还
款后仍用旧本金累计全部期间利息）：同一基数下期间在中点切开的两天数利
息相加等于整段利息（分段计息守恒——天数差来自统一历法的 ℤ 精确值，非
30 天均摊）；瀑布抵充不超付不丢失（每笔付款至多消费一次，付款额不超过
组件总额时恰全额分配）；还款后残余本金分段计息与旧本金全期间计息不同
（100000 元、日利率 1/1000、2024-01-15→2024-03-10 于 2024-02-01 还款
40000：正确 3980 ≠ 旧本金 5500）。 -/
def demand_D095 : Prop :=
  (∀ (y m d : ℕ) (h : d + 1 ≤ monthLen y m), dayOfYear y m (d + 1) = dayOfYear y m d + 1) ∧
    (∀ (a m b : CalDate) (base rate : ℚ),
        taInterestSeg base rate a m + taInterestSeg base rate m b = taInterestSeg base rate a b) ∧
    (∀ (pay : ℚ) (buckets : List ℚ), 0 ≤ pay → (∀ b ∈ buckets, 0 ≤ b) →
        (taImputeAll pay buckets).sum ≤ pay ∧
          (pay ≤ buckets.sum → (taImputeAll pay buckets).sum = pay)) ∧
    (taInterestSeg 100000 (1 / 1000) ⟨2024, 1, 15⟩ ⟨2024, 3, 10⟩ = 5500 ∧
      taInterestSeg 100000 (1 / 1000) ⟨2024, 1, 15⟩ ⟨2024, 2, 1⟩
        + taInterestSeg 60000 (1 / 1000) ⟨2024, 2, 1⟩ ⟨2024, 3, 10⟩ = 3980 ∧
      (5500 : ℚ) ≠ 3980)

/-- D096 基准率取值由事件与法律政策决定，倍数运算只作用于被确认基准（反
例：用当前LPR倒填所有历史借款期间）：政策事件日之前两天的基准取值相同
（同一政策段内基准一致——事件日决定取值而非当前日期，历元日序即日期
序）；未确认基准上倍数恒为恒等（倍数只作用于被确认基准）；2024-01-01
政策步进（旧 71/2000、新 69/2000）下 2023-06-30 的历史期间取旧基准得
4×71/2000，倒填新基准得 4×69/2000，两者不等。 -/
def demand_D096 : Prop :=
  (∀ (y m d : ℕ) (h : d + 1 ≤ monthLen y m), dayOfYear y m (d + 1) = dayOfYear y m d + 1) ∧
    (∀ (ev a b : CalDate) (oldRate newRate : ℚ),
        toEpochDay a ≤ toEpochDay b → toEpochDay b < toEpochDay ev →
          taStepRate (toEpochDay ev) oldRate newRate (toEpochDay a)
            = taStepRate (toEpochDay ev) oldRate newRate (toEpochDay b)) ∧
    (∀ (mult base : ℚ), taCappedMult mult false base = base) ∧
    (toEpochDay ⟨2023, 6, 30⟩ < toEpochDay ⟨2024, 1, 1⟩ ∧
      taCappedMult 4 true
          (taStepRate (toEpochDay ⟨2024, 1, 1⟩) (71 / 2000) (69 / 2000)
            (toEpochDay ⟨2023, 6, 30⟩)) = 4 * (71 / 2000) ∧
        taCappedMult 4 true
          (taStepRate (toEpochDay ⟨2024, 1, 1⟩) (71 / 2000) (69 / 2000)
            (toEpochDay ⟨2024, 1, 1⟩)) = 4 * (69 / 2000) ∧
        (4 * (71 / 2000) : ℚ) ≠ 4 * (69 / 2000))

/-- D097 现金、股份数、股价、汇率和转换比例按维度推导，舍入阶段显式（反
例：按股计价格与总价混用使倍率相差股份数）：股份数非零时不同的单价给
出不同的对价（每股价与总价两维不可混用）；汇率折算与股份数乘法可换（维
度一致：先折单价再乘股数＝先乘股数再折总价）；舍入阶段显式——期末一次
取整（1/2+3×(1/2)=2 取整得 2）与中段先取整再相加（0+1=1）结果不同。 -/
def demand_D097 : Prop :=
  (∀ (y m d : ℕ) (h : d + 1 ≤ monthLen y m), dayOfYear y m (d + 1) = dayOfYear y m d + 1) ∧
    (∀ (cash shares p1 p2 : ℚ), shares ≠ 0 → p1 ≠ p2 →
        taConsideration cash shares p1 ≠ taConsideration cash shares p2) ∧
    (∀ (shares price fx : ℚ), shares * (price * fx) = (shares * price) * fx) ∧
    (taRound (taConsideration (1 / 2) 3 (1 / 2)) = 2 ∧
      taRound (1 / 2) + taRound (3 * (1 / 2)) = 1 ∧ (2 : ℚ) ≠ 1)

/-- D098 提前清偿本金与premium分账；触发日和适用比例共同验证（反例：2%
溢价计在原授信额度而非应清偿余额）：倍数右消去律（余额≠额度⇒余额×比例
≠额度×比例——溢价只按应清偿余额计）；触发日未到溢价恒为零（日期与比例
共同验证，与金额无关）；2024-03-15 起息 6 个月触发日为 2024-09-15（月
算术、月末钳制）下 2024-09-01 未触发、2024-09-20 已触发溢价
400000×2%=8000，而计在原授信额度 1000000 上得 20000≠8000。 -/
def demand_D098 : Prop :=
  (∀ (y m d : ℕ) (h : d + 1 ≤ monthLen y m), dayOfYear y m (d + 1) = dayOfYear y m d + 1) ∧
    (∀ (facility balance ratio : ℚ), ratio ≠ 0 → balance ≠ facility →
        balance * ratio ≠ facility * ratio) ∧
    (∀ (trigger prepay : CalDate) (balance ratio : ℚ),
        ¬ (toEpochDay trigger ≤ toEpochDay prepay) →
          taMakeWhole (taTriggered trigger prepay) balance ratio = 0) ∧
    (addCalMonths 6 ⟨2024, 3, 15⟩ = ⟨2024, 9, 15⟩ ∧
      taTriggered ⟨2024, 9, 15⟩ ⟨2024, 9, 1⟩ = false ∧
      taTriggered ⟨2024, 9, 15⟩ ⟨2024, 9, 20⟩ = true ∧
      taMakeWhole true 400000 (2 / 100) = 8000 ∧
      taMakeWhole true 1000000 (2 / 100) = 20000 ∧ (20000 : ℚ) ≠ 8000)

/-- D099 不同期限带anchor、length、calendar、deadline_effect和证据状态（反
例：60日补正期未到，仅因30日通知期到便认定终止）：同锚点更长期限给出更
晚的基础期限（期限严格区分）；顺延后的期限是营业日不动点（deadline_
effect 只顺延一次）；到期与证据二者缺一权利不产生（证据状态独立）；
锚点 2024-05-06 下 30/60 日期限基础历元 739042/739072，第 739050 日通
知期已到而补正期未到——补正期限的权利不产生。 -/
def demand_D099 : Prop :=
  (∀ (y m d : ℕ) (h : d + 1 ≤ monthLen y m), dayOfYear y m (d + 1) = dayOfYear y m d + 1) ∧
    (∀ (p q : PeriodSpec), p.anchor.Valid → q.anchor.Valid → p.anchor = q.anchor →
        p.length < q.length → toEpochDay p.baseDeadline < toEpochDay q.baseDeadline) ∧
    (∀ (p : PeriodSpec),
        (∃ k, k ≤ p.rollFuel ∧ p.holiday (toEpochDay p.baseDeadline + k) = false) →
          nextBiz p.holiday p.rollFuel p.deadline = p.deadline) ∧
    (taRightArises true false = false ∧ taRightArises false true = false ∧
      taRightArises true true = true) ∧
    (toEpochDay (addCalDays 30 ⟨2024, 5, 6⟩) = 739042 ∧
      toEpochDay (addCalDays 60 ⟨2024, 5, 6⟩) = 739072 ∧
      taDeadlineArrived (⟨⟨2024, 5, 6⟩, 30, syntheticWeekend, 7⟩ : PeriodSpec) 739050 = true ∧
      taDeadlineArrived (⟨⟨2024, 5, 6⟩, 60, syntheticWeekend, 7⟩ : PeriodSpec) 739050 = false ∧
      taRightArises
        (taDeadlineArrived (⟨⟨2024, 5, 6⟩, 60, syntheticWeekend, 7⟩ : PeriodSpec) 739050)
        false = false)

/-- D100 倒排得到的时间表满足所有前置和日历约束；不可行时报告冲突（反例：
倒排某项日期在过去，不能仍输出可执行完整计划）：可行的倒排结果有效且
正向推回恰得原期限（前置约束满足，倒排不越过历元）；起算日落在底界日
（如今天）之前同样报冲突不输出计划——2024-03-31 回退 30 天得
2024-03-01，底界 2024-03-10 时起算日在过去→none，底界 2024-02-15 时输
出 some 2024-03-1 且正向 30 天回到 2024-03-31。 -/
def demand_D100 : Prop :=
  (∀ (y m d : ℕ) (h : d + 1 ≤ monthLen y m), dayOfYear y m (d + 1) = dayOfYear y m d + 1) ∧
    (∀ (deadline : CalDate) (lead : ℕ) (a : CalDate), deadline.Valid →
        backSchedule deadline lead = some a → a.Valid ∧ addCalDays lead a = deadline) ∧
    (∀ (floor deadline : CalDate) (lead : ℕ) (s : CalDate),
        backSchedule deadline lead = some s → toEpochDay s < toEpochDay floor →
          taBackItem floor deadline lead = none) ∧
    (backSchedule ⟨2024, 3, 31⟩ 30 = some ⟨2024, 3, 1⟩ ∧
      taBackItem ⟨2024, 3, 10⟩ ⟨2024, 3, 31⟩ 30 = none ∧
      taBackItem ⟨2024, 2, 15⟩ ⟨2024, 3, 31⟩ 30 = some ⟨2024, 3, 1⟩ ∧
      addCalDays 30 ⟨2024, 3, 1⟩ = ⟨2024, 3, 31⟩)

/-- D101 债务本金、成本、收入风险、或有赔偿用不同数量/条件；只按声明风险
函数聚合（反例：将收入风险当已实现损失并与原收入重复相加）：四类敞口
标签互异（数量/条件不同类，风险数字不能冒充已实现额）；概率加权项小于
同额已实现项（0<p<1、c>0 时 pc<c）；声明聚合只经风险函数计入或有项——
债务 5000＋成本 1000＋或有 2000 按 p=1/4 聚合得 6500，把或有项当已实现
直加得 8000≠6500，再与原收入重复相加得 8500≠6500；敞口期间天数差为
ℤ 精确（2024-Q1 为 90 天、2023-Q1 为 89 天，闰差不均摊）。 -/
def demand_D101 : Prop :=
  (∀ (y m d : ℕ) (h : d + 1 ≤ monthLen y m), dayOfYear y m (d + 1) = dayOfYear y m d + 1) ∧
    (taExpDebt ≠ taExpCost ∧ taExpDebt ≠ taExpRisk ∧ taExpDebt ≠ taExpContingent ∧
      taExpCost ≠ taExpRisk ∧ taExpCost ≠ taExpContingent ∧ taExpRisk ≠ taExpContingent) ∧
    (∀ (p c : ℚ), 0 < p → p < 1 → 0 < c → p * c < c) ∧
    (taAggregate 5000 1000 [2000] (1 / 4) = 6500 ∧
      (5000 + 1000 + 2000 : ℚ) = 8000 ∧ (8000 : ℚ) ≠ 6500 ∧
      (5000 + 1000 + 2000 + (1 / 4) * 2000 : ℚ) = 8500) ∧
    (daysDiff ⟨2024, 1, 1⟩ ⟨2024, 3, 31⟩ = 90 ∧ daysDiff ⟨2023, 1, 1⟩ ⟨2023, 3, 31⟩ = 89)

/-- D102 终止后的义务由存续规则更新，不与主履行义务一并清空（反例：删除
终止前已发生的应付款或已产生责任）：已发生应付款经存续规则更新后原额
存续（不清空）；终止日之后才开始的主履行义务被清零（主履行义务随终止
熄灭）；终止日之前已完结的主履行义务仍按原额计入（更新而非清空）；闭
期间整体落在终止日之后⟺起点落在终止日之后（存续射线律）；终止日
2024-06-30 下 2024-05-10→06-15 的 8000 元应付款存续 8000≠0（一并清空得
0），2024-07-01→07-31 的 9000 元未来服务义务清零，7 月期间起点 07-01 与
中点 07-15 都在终止日之后。 -/
def demand_D102 : Prop :=
  (∀ (y m d : ℕ) (h : d + 1 ≤ monthLen y m), dayOfYear y m (d + 1) = dayOfYear y m d + 1) ∧
    (∀ (amount : ℚ) (endDay termDay : ℤ),
        taSurvivalUpdate 0 amount endDay termDay = amount) ∧
    (∀ (amount : ℚ) (startDay endDay termDay : ℤ), startDay ≤ endDay → termDay < startDay →
        taSurvivalUpdate 1 amount endDay termDay = 0) ∧
    (∀ (amount : ℚ) (endDay termDay : ℤ), endDay ≤ termDay →
        taSurvivalUpdate 1 amount endDay termDay = amount) ∧
    (∀ (term a b : CalDate), toEpochDay a ≤ toEpochDay b →
        (toEpochDay term ≤ toEpochDay a ↔
          ∀ x : CalDate, toEpochDay a ≤ toEpochDay x ∧ toEpochDay x ≤ toEpochDay b →
            toEpochDay term ≤ toEpochDay x)) ∧
    (taSurvivalUpdate 0 8000 (toEpochDay ⟨2024, 6, 15⟩) (toEpochDay ⟨2024, 6, 30⟩) = 8000 ∧
      taSurvivalUpdate 1 9000 (toEpochDay ⟨2024, 7, 31⟩) (toEpochDay ⟨2024, 6, 30⟩) = 0 ∧
      toEpochDay ⟨2024, 6, 15⟩ ≤ toEpochDay ⟨2024, 6, 30⟩ ∧
      toEpochDay ⟨2024, 6, 30⟩ ≤ toEpochDay ⟨2024, 7, 1⟩ ∧
      toEpochDay ⟨2024, 6, 30⟩ ≤ toEpochDay ⟨2024, 7, 15⟩ ∧ (0 : ℚ) ≠ 8000)

/-- D103 价格调整由同一营运资金定义、参考日、排除项和对账差异计算（反例：
目标与期末使用不同科目范围仍报告精确差额）：同一历元日的两个合法日期
是同一参考日（参考日判据）；排除项按名称精确剔除且两侧同一（同一排除
项表下排除账户不入净值）；同一口径的目标/期末差额精确——目标 6000、期
末 6200 调整额恰为 200；期末侧混入现金科目 1000（不同科目范围）时差额
变 1200≠200，不是本定义的对账差异。 -/
def demand_D103 : Prop :=
  (∀ (y m d : ℕ) (h : d + 1 ≤ monthLen y m), dayOfYear y m (d + 1) = dayOfYear y m d + 1) ∧
    (∀ (d1 d2 : CalDate), d1.Valid → d2.Valid → toEpochDay d1 = toEpochDay d2 → d1 = d2) ∧
    (∀ (accounts : List (String × ℚ)) (exclusions : List String) (e : String) (v : ℚ),
        exclusions.contains e = true →
          taWorkingCapital ((e, v) :: accounts) exclusions
            = taWorkingCapital accounts exclusions) ∧
    (taWorkingCapital [("receivables", 5000), ("inventory", 3000), ("payables", -2000)] [] = 6000 ∧
      taWorkingCapital [("receivables", 5000), ("inventory", 3000), ("payables", -2000),
        ("debt-like", 999)] ["debt-like"] = 6000 ∧
      taWorkingCapital [("receivables", 5200), ("inventory", 3000), ("payables", -2000)] [] = 6200 ∧
      taAdjustment 6000 6200 = 200 ∧
      taWorkingCapital [("receivables", 5200), ("inventory", 3000), ("payables", -2000),
        ("cash", 1000)] [] = 7200 ∧
      taAdjustment 6000 7200 = 1200 ∧ (1200 : ℚ) ≠ 200)

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

/-! D116-D123 (group 13 办案、交易工作流与策略, W2-A batch B13): each def
is that demand's own contract, translated from ALL_134_MATH_CONTRACTS.md.
The first conjunct is the group-registered Bellman component (the
one-sided max-gap bound of the legal-action Bellman operator: when two
value tables differ pointwise by at most M, the optimized continuation
value of the first stays within β*M of the second — the kernel of every
explicit prediction/value model a workflow strategy uses); the remaining
conjuncts are the demand's own operational semantics with its adverse
case, built on helpers local to this region in the group-08 style (the
green Numeric/Bellman carrier supplies the registered component; the
green Action/* surface offers no workflow-scheduling carrier and
Seams/UnifiedTrajectory no per-demand witness this contract needs, so
the operational defs live here).  None of the eight bold sentences
carries a CAD/optimization sub-clause (D117 reports discrete-ordering
infeasibility, not a continuous program), so no C2-C5 suspension
annotation applies. -/

/-- D116 helper: string membership as a plain recursive Bool. -/
def strIn (d : String) : List String → Bool
  | [] => false
  | x :: xs => if x = d then true else strIn d xs

/-- D116 helper: the exact gap required_documents ∖ VDR catalog. -/
def vdrGap (required vdr : List String) : List String :=
  required.filter (fun d => !strIn d vdr)

/-- D116 helper: every missing document becomes an explicit pending row
(name, status) instead of being dropped. -/
def toPending : List String → List (String × String) :=
  fun missing => missing.map (fun d => (d, "pending"))

/-- D117 helper: one closing task — a name, its prerequisite task name
("" = none) and whether the authority/permission to run it is held. -/
structure CloTask where
  name : String
  prereq : String
  permitted : Bool

/-- D117 helper: `pre` occurs in `order` strictly before `name`. -/
def cloBefore (order : List String) (pre name : String) : Bool :=
  match order with
  | [] => false
  | w :: ws => if w = pre then strIn name ws else cloBefore ws pre name

/-- D117 helper: a task is ready in a proposed order when the permission
is held and its prerequisite (if any) ran earlier in that order. -/
def cloReady (order : List String) (t : CloTask) : Bool :=
  t.permitted && (if t.prereq = "" then true
    else cloBefore order t.prereq t.name)

/-- D117 helper: `order` legally executes `ts` when it covers the task
set (equal length with every name present over distinct names) and every
task is permitted and runs after its prerequisite. -/
def cloLegalOrder (ts : List CloTask) (order : List String) : Bool :=
  (order.length == ts.length)
    && ts.all (fun t => strIn t.name order && cloReady order t)

/-- D117 helper: the executable-checklist verdict — some order when the
proposal is legal, none (= infeasibility reported) otherwise. -/
def cloVerdict (ts : List CloTask) (order : List String) : Option (List String) :=
  if cloLegalOrder ts order = true then some order else none

/-- D117 witness: an acyclic board-approval → signature → closing chain
that does close. -/
def shipTasks : List CloTask :=
  [{ name := "board-approval", prereq := "", permitted := true },
   { name := "signature", prereq := "board-approval", permitted := true },
   { name := "closing", prereq := "signature", permitted := true }]

def shipOrder : List String := ["board-approval", "signature", "closing"]

/-- D117 adverse witness: a two-task dependency cycle. -/
def cycTasks : List CloTask :=
  [{ name := "task-a", prereq := "task-b", permitted := true },
   { name := "task-b", prereq := "task-a", permitted := true }]

/-- D118 helper: the three clarification moves of a transaction
workflow. -/
inductive ClarKind where
  | writtenConfirm | waiver | supplement
  deriving DecidableEq

/-- D118 helper: one clarification action against a norm — `waivable`
records whether that norm may be waived by private parties; the value
model inputs are explicit (success probability, gain if it succeeds,
cost of the move). -/
structure ClarAction where
  kind : ClarKind
  norm : String
  waivable : Bool
  prob : ℚ
  gain : ℚ
  cost : ℚ

/-- D118 helper: written confirmation and supplementary evidence are
always legal moves; a waiver is legal only against a waivable norm. -/
def clarLegal (a : ClarAction) : Bool :=
  match a.kind with
  | ClarKind.waiver => a.waivable
  | _ => true

/-- D118 helper: the explicit prediction-model value of a clarification
move — expected gain minus cost. -/
def clarValue (a : ClarAction) : ℚ := a.prob * a.gain - a.cost

/-- D119 helper: one risk to critical infrastructure or revenue — an
explicit preference weight, an explicit risk measure (preference
indices, not amounts), and whether a hard legal constraint blocks the
item outright. -/
structure RiskItem where
  name : String
  weight : ℕ
  measure : ℕ
  hardBlocked : Bool

/-- D119 helper: the explicit score = weight × measure. -/
def riskScore (i : RiskItem) : ℕ := i.weight * i.measure

/-- D119 helper: insertion into a descending-score list. -/
def riskInsert (i : RiskItem) : List RiskItem → List RiskItem
  | [] => [i]
  | j :: js => if riskScore j < riskScore i then i :: j :: js
    else j :: riskInsert i js

/-- D119 helper: descending-score sort — the explicit preference/risk
measure executed. -/
def riskSort : List RiskItem → List RiskItem
  | [] => []
  | i :: is => riskInsert i (riskSort is)

/-- D119 helper: the ranked readout — hard-blocked items are filtered
out before any weight is applied, the rest sorted by explicit score. -/
def riskRank (items : List RiskItem) : List (String × ℕ) :=
  (riskSort (items.filter (fun i => !i.hardBlocked))).map
    (fun i => (i.name, riskScore i))

/-- D119 helper: every ranked readout declares its origin — an explicit
preference, never a statutory order. -/
def rankOrigin : String := "explicit-preference"

/-- D119 witness: three unblocked risks scored 40 / 15 / 2. -/
def infraRisks : List RiskItem :=
  [{ name := "power-grid", weight := 4, measure := 10, hardBlocked := false },
   { name := "revenue-stream", weight := 5, measure := 3, hardBlocked := false },
   { name := "ip-license", weight := 1, measure := 2, hardBlocked := false }]

/-- D119 adverse witness: the highest-scoring item (100) is hard-blocked
and stays out of the ranked work list whatever its weight. -/
def blockedTop : List RiskItem :=
  [{ name := "unpermitted-plant", weight := 10, measure := 10, hardBlocked := true },
   { name := "power-grid", weight := 4, measure := 10, hardBlocked := false },
   { name := "revenue-stream", weight := 5, measure := 3, hardBlocked := false }]

/-- D119 adverse witness: the same measures under two explicit weight
vectors rank in different orders — the order follows the declared
weights, so no weight vector is the statutory unique priority. -/
def weightCfgA : List RiskItem :=
  [{ name := "power-grid", weight := 1, measure := 2, hardBlocked := false },
   { name := "revenue-stream", weight := 3, measure := 3, hardBlocked := false }]

def weightCfgB : List RiskItem :=
  [{ name := "power-grid", weight := 5, measure := 2, hardBlocked := false },
   { name := "revenue-stream", weight := 1, measure := 3, hardBlocked := false }]

/-- D120 helper: what kind of advice a clause comparison yields — a
market-sample observation or a legal duty; the two never merge. -/
inductive AdviceKind where
  | marketSample | legalDuty
  deriving DecidableEq

/-- D120 helper: a market-clause sample — how many of how many sampled
deals carry the clause. -/
structure MarketSample where
  clause : String
  count : ℕ
  total : ℕ

def marketShare (s : MarketSample) : ℚ := (s.count : ℚ) / (s.total : ℚ)

structure ClauseAdvice where
  kind : AdviceKind
  clause : String
  share : ℚ
  basis : String

/-- D120 helper: advice built from market data only — typed as a market
sample with the share it actually has, never as a legal duty. -/
def adviseFromMarket (s : MarketSample) : ClauseAdvice where
  kind := AdviceKind.marketSample
  clause := s.clause
  share := marketShare s
  basis := "market-sample"

/-- D120 adverse witness: a 3-of-5 market majority. -/
def majoritySample : MarketSample where
  clause := "change-of-control-consent"
  count := 3
  total := 5

/-- D121 helper: the three subpoena responses composed from their
gates — the quash motion is the non-party path and needs timeliness;
vacating needs timeliness alone; the protective order needs the
pre-trial stage and timeliness. -/
inductive SubpoenaMeasure where
  | quash | vacate | protective

structure SubpoenaCtx where
  isNonParty : Bool
  stagePreTrial : Bool
  filedInTime : Bool

def measureLegal : SubpoenaMeasure → SubpoenaCtx → Bool
  | SubpoenaMeasure.quash, c => c.isNonParty && c.filedInTime
  | SubpoenaMeasure.vacate, c => c.filedInTime
  | SubpoenaMeasure.protective, c => c.stagePreTrial && c.filedInTime

def legalOptions (c : SubpoenaCtx) : List SubpoenaMeasure :=
  [SubpoenaMeasure.quash, SubpoenaMeasure.vacate,
    SubpoenaMeasure.protective].filter (fun m => measureLegal m c)

/-- D122 helper: one node of the frozen claim/rebuttal graph — its
evidence dependencies and its alternative (备位) positions. -/
structure ArgNode where
  id : String
  deps : List String
  alts : List String

structure Outline where
  covered : List String
  depsKept : List (String × List String)
  altsKept : List (String × List String)

/-- D122 helper: list equality as a plain recursive Bool. -/
def strEqList : List String → List String → Bool
  | [], [] => true
  | x :: xs, y :: ys => if x = y then strEqList xs ys else false
  | _, _ => false

/-- D122 helper: the (key, value) row survives in the kept list. -/
def keptFor (rows : List (String × List String)) (key : String)
    (val : List String) : Bool :=
  match rows with
  | [] => false
  | p :: ps =>
      if p.1 = key then (if strEqList p.2 val then true else keptFor ps key val)
      else keptFor ps key val

/-- D122 helper: the node's evidence dependencies survive in the kept
list (a node with no dependencies keeps them vacuously). -/
def depsKeptFor (o : Outline) (n : ArgNode) : Bool :=
  match n.deps with
  | [] => true
  | ds => keptFor o.depsKept n.id ds

/-- D122 helper: the node's alternative (备位) positions survive in the
kept list (a node with no alternatives keeps them vacuously). -/
def altsKeptFor (o : Outline) (n : ArgNode) : Bool :=
  match n.alts with
  | [] => true
  | as => keptFor o.altsKept n.id as

/-- D122 helper: the outline covers the frozen graph when every node id
is covered with its evidence dependencies and alternatives kept. -/
def coversFrozen (g : List ArgNode) (o : Outline) : Bool :=
  g.all (fun n => strIn n.id o.covered && depsKeptFor o n && altsKeptFor o n)

/-- D122 witness: the frozen graph — main claim, best rebuttal, two weak
rebuttals, one primary theory with its fallback. -/
def frozenGraph : List ArgNode :=
  [{ id := "main-claim", deps := ["ex-contract", "ex-performance"], alts := [] },
   { id := "best-rebuttal", deps := ["ex-causation"], alts := [] },
   { id := "weak-rebuttal-a", deps := ["ex-timing"], alts := [] },
   { id := "weak-rebuttal-b", deps := [], alts := [] },
   { id := "primary-theory", deps := ["ex-contract"],
     alts := ["fallback-theory"] }]

def fullOutline : Outline where
  covered := ["main-claim", "best-rebuttal", "weak-rebuttal-a",
    "weak-rebuttal-b", "primary-theory"]
  depsKept := [("main-claim", ["ex-contract", "ex-performance"]),
    ("best-rebuttal", ["ex-causation"]), ("weak-rebuttal-a", ["ex-timing"]),
    ("weak-rebuttal-b", []), ("primary-theory", ["ex-contract"])]
  altsKept := [("primary-theory", ["fallback-theory"])]

/-- D122 adverse witness: three covered ids — the main claim and two
weak rebuttals — while the best rebuttal and the primary/alternative
structure are missing; the count alone does not answer the strongest
counter-argument. -/
def weakOutline : Outline where
  covered := ["main-claim", "weak-rebuttal-a", "weak-rebuttal-b"]
  depsKept := [("main-claim", ["ex-contract", "ex-performance"]),
    ("weak-rebuttal-a", ["ex-timing"]), ("weak-rebuttal-b", [])]
  altsKept := []

/-- D123 helper: a legal-tool query outcome — ok-with-records or a
timeout. -/
inductive QueryOutcome where
  | records (rs : List String)
  | timeout

/-- D123 helper: the readout of a tool query — an ok result reads as the
records found (an ok empty list is a verified no-records); a timeout
reads as unavailable, never as no records. -/
inductive FactReadout where
  | found (n : ℕ)
  | noRecords
  | unavailable

def readoutOf : QueryOutcome → FactReadout
  | QueryOutcome.records [] => FactReadout.noRecords
  | QueryOutcome.records rs => FactReadout.found rs.length
  | QueryOutcome.timeout => FactReadout.unavailable

/-- D123 helper: one data assertion of the final report with its full
provenance chain. -/
structure FinalAssertion where
  text : String
  inputs : List String
  joins : List String
  records : List String
  transform : String

/-- D123 helper: an assertion is sourced when every chain component is
present — query inputs, intermediate joins, original records and the
transform witness. -/
def sourced (a : FinalAssertion) : Bool :=
  !(a.inputs.isEmpty) && (!(a.joins.isEmpty)
    && (!(a.records.isEmpty) && !(a.transform.isEmpty)))

def litigationAssertion : FinalAssertion where
  text := "target has one pending litigation"
  inputs := ["query-litigation-by-entity"]
  joins := ["join-on-entity-id"]
  records := ["docket-2026-001"]
  transform := "normalize-and-count"

/-- D123 adverse witness: the hollow assertion a timed-out interface
would produce if silence were written up as a finding — no joins, no
records, a fabricated readout. -/
def hollowAssertion : FinalAssertion where
  text := "no litigation found"
  inputs := ["query-litigation-by-entity"]
  joins := []
  records := []
  transform := "silently-empty"

/-- D116 尽调请求清单与资料室目录是否对应，哪些材料仍缺失（反例：缺失
材料不得通过从现有目录生成"必需清单"抹去）：差集按成员资格精确刻画
（入差集 ⇔ 在必需清单且不在资料室目录——不从资料室反推必需）；每个缺失
文件转为显式未决行（名称，状态），不被静默丢弃；见证——必需清单含
litigation-search 而资料室只有 charter，差集恰为 [litigation-search]
（缺失材料无法被资料室现有目录抹去）。 -/
def demand_D116 : Prop :=
  (∀ {S A : Type} [Fintype S] [DecidableEq S] [DecidableEq A]
      (legal : S → Finset A) (r : S → A → ℚ)
      (p : S → A → S → ℚ)
      (hpn : ∀ s a s', 0 ≤ p s a s')
      (hsum : ∀ s a, ∑ s', p s a s' = 1)
      (β : ℚ) (hβ : 0 ≤ β)
      (x y : S → ℚ) (M : ℚ) (hM : ∀ t, |x t - y t| ≤ M) (s : S)
      (hne : (legal s).Nonempty) (hny : (legal s).Nonempty),
      bellmanOf legal r p β x s hne ≤ bellmanOf legal r p β y s hny + β * M) ∧
  ((∀ (required vdr : List String) (d : String),
      d ∈ vdrGap required vdr ↔ (d ∈ required ∧ ¬ d ∈ vdr)) ∧
   (∀ (required vdr : List String) (d : String), d ∈ vdrGap required vdr →
      (d, "pending") ∈ toPending (vdrGap required vdr)) ∧
   (vdrGap ["charter", "litigation-search"] ["charter"] = ["litigation-search"] ∧
      ¬ (("litigation-search" : String) ∈ ["charter"])))

/-- D117 交割清单、审批、同意与解除条件是否满足先后依赖（反例：互相依
赖形成环仍生成无条件可执行清单）：合法排序的每项任务权限在手且前置已
先行（发生事件、权限与前置满足的逐步语义）；无环链 board-approval →
signature → closing 的可行序过裁定（some）；两任务互为前置的环对一切
排序都不合法——不可行必须报告（none），不生成无条件清单。 -/
def demand_D117 : Prop :=
  (∀ {S A : Type} [Fintype S] [DecidableEq S] [DecidableEq A]
      (legal : S → Finset A) (r : S → A → ℚ)
      (p : S → A → S → ℚ)
      (hpn : ∀ s a s', 0 ≤ p s a s')
      (hsum : ∀ s a, ∑ s', p s a s' = 1)
      (β : ℚ) (hβ : 0 ≤ β)
      (x y : S → ℚ) (M : ℚ) (hM : ∀ t, |x t - y t| ≤ M) (s : S)
      (hne : (legal s).Nonempty) (hny : (legal s).Nonempty),
      bellmanOf legal r p β x s hne ≤ bellmanOf legal r p β y s hny + β * M) ∧
  ((∀ (ts : List CloTask) (order : List String) (t : CloTask),
      cloLegalOrder ts order = true → t ∈ ts → cloReady order t = true) ∧
   (cloVerdict shipTasks shipOrder =
      some ["board-approval", "signature", "closing"]) ∧
   (∀ (order : List String), cloLegalOrder cycTasks order = false))

/-- D118 对模糊条款应何时寻求书面确认、同意或豁免（反例：强制法义务
不能由私人豁免事件删除）：书面确认与补证恒为合法行动（对不可豁免规范
亦然）；豁免行动仅当目标规范可豁免时合法——不可豁免（强制法）规范的
豁免行动非法；价值由明确预测模型计算（成功概率×收益−成本），两个数值
见证：3/4×100−10=65、1/2×40−5=15。 -/
def demand_D118 : Prop :=
  (∀ {S A : Type} [Fintype S] [DecidableEq S] [DecidableEq A]
      (legal : S → Finset A) (r : S → A → ℚ)
      (p : S → A → S → ℚ)
      (hpn : ∀ s a s', 0 ≤ p s a s')
      (hsum : ∀ s a, ∑ s', p s a s' = 1)
      (β : ℚ) (hβ : 0 ≤ β)
      (x y : S → ℚ) (M : ℚ) (hM : ∀ t, |x t - y t| ≤ M) (s : S)
      (hne : (legal s).Nonempty) (hny : (legal s).Nonempty),
      bellmanOf legal r p β x s hne ≤ bellmanOf legal r p β y s hny + β * M) ∧
  ((∀ (a : ClarAction), a.kind = ClarKind.waiver → a.waivable = false →
      clarLegal a = false) ∧
   (∀ (norm : String) (pq g c : ℚ),
      clarLegal { kind := ClarKind.writtenConfirm, norm := norm,
                  waivable := false, prob := pq, gain := g, cost := c } = true ∧
      clarLegal { kind := ClarKind.supplement, norm := norm,
                  waivable := false, prob := pq, gain := g, cost := c } = true) ∧
   (clarLegal { kind := ClarKind.waiver, norm := "mandatory-audit",
                waivable := false, prob := 1, gain := 100, cost := 0 } = false) ∧
   (clarValue { kind := ClarKind.writtenConfirm, norm := "clause-7",
                waivable := true, prob := 3 / 4, gain := 100, cost := 10 } = 65 ∧
    clarValue { kind := ClarKind.supplement, norm := "missing-board-res",
                waivable := true, prob := 1 / 2, gain := 40, cost := 5 } = 15))

/-- D119 对关键基础设施和收入来源的风险应怎样排序（反例：将任意重要
性权重误标法定唯一优先序）：排序按明示偏好/风险度量执行——权重×度量
的降序读出（40/15/2 见证）；硬法律约束不被权重抵消——被硬约束封禁的
条目（哪怕评分最高 100）在任何权重下都不入排序工作清单；排序出处的
诚实标注——origin 是 explicit-preference 而非 statutory-unique；同一
度量在两组权重下产生不同排序，证明排序随明示权重而变、无唯一法定
序。 -/
def demand_D119 : Prop :=
  (∀ {S A : Type} [Fintype S] [DecidableEq S] [DecidableEq A]
      (legal : S → Finset A) (r : S → A → ℚ)
      (p : S → A → S → ℚ)
      (hpn : ∀ s a s', 0 ≤ p s a s')
      (hsum : ∀ s a, ∑ s', p s a s' = 1)
      (β : ℚ) (hβ : 0 ≤ β)
      (x y : S → ℚ) (M : ℚ) (hM : ∀ t, |x t - y t| ≤ M) (s : S)
      (hne : (legal s).Nonempty) (hny : (legal s).Nonempty),
      bellmanOf legal r p β x s hne ≤ bellmanOf legal r p β y s hny + β * M) ∧
  ((riskRank infraRisks =
      [("power-grid", 40), ("revenue-stream", 15), ("ip-license", 2)]) ∧
   (∀ (items : List RiskItem) (i : RiskItem), i.hardBlocked = true →
      ¬ (i ∈ items.filter (fun x => !x.hardBlocked))) ∧
   ((blockedTop.filter (fun x => !x.hardBlocked)).map RiskItem.name =
      ["power-grid", "revenue-stream"]) ∧
   (rankOrigin = "explicit-preference" ∧ rankOrigin ≠ "statutory-unique") ∧
   ((riskRank weightCfgA).map Prod.fst ≠ (riskRank weightCfgB).map Prod.fst))

/-- D120 先例市场条款比较如何支持谈判立场而非成为法律规则（反例：多
数合同如此写不自动推导依法必须如此）：先例条款分布与规范效力分类型
——市场样本建议恒带 marketSample 类型与 market-sample 基础标注，绝不
是 legalDuty；市场占比按样本显式计算（3/5）；多数见证——3/5 过半的
条款样本仍产不出任何 legalDuty 类型的建议（多数本身不是法律义务来
源）。 -/
def demand_D120 : Prop :=
  (∀ {S A : Type} [Fintype S] [DecidableEq S] [DecidableEq A]
      (legal : S → Finset A) (r : S → A → ℚ)
      (p : S → A → S → ℚ)
      (hpn : ∀ s a s', 0 ≤ p s a s')
      (hsum : ∀ s a, ∑ s', p s a s' = 1)
      (β : ℚ) (hβ : 0 ≤ β)
      (x y : S → ℚ) (M : ℚ) (hM : ∀ t, |x t - y t| ≤ M) (s : S)
      (hne : (legal s).Nonempty) (hny : (legal s).Nonempty),
      bellmanOf legal r p β x s hne ≤ bellmanOf legal r p β y s hny + β * M) ∧
  ((∀ (s : MarketSample), (adviseFromMarket s).kind = AdviceKind.marketSample ∧
      (adviseFromMarket s).basis = "market-sample" ∧
      (adviseFromMarket s).kind ≠ AdviceKind.legalDuty) ∧
   (marketShare majoritySample = 3 / 5 ∧ 1 / 2 < marketShare majoritySample) ∧
   (∀ (clause : String) (q : ℚ) (basis : String),
      adviseFromMarket majoritySample ≠
        { kind := AdviceKind.legalDuty, clause := clause, share := q,
          basis := basis }))

/-- D121 第三方传票应提出何种异议、撤销申请或保护措施（反例：将非当
事人异议路径无条件给另一诉讼当事人）：选项合法性由法域/主体资格/阶段
及期限的门组合——任何合法选项都以按期提出为前提（期限门对全部三类选
项普遍成立）；非当事人、审前、按期的完整上下文三选项皆合法；当事人
上下文得不到非当事人的撤销异议路径（quash 恒缺席）；逾期上下文一切
选项皆空（期限不被主体资格或阶段补正）。 -/
def demand_D121 : Prop :=
  (∀ {S A : Type} [Fintype S] [DecidableEq S] [DecidableEq A]
      (legal : S → Finset A) (r : S → A → ℚ)
      (p : S → A → S → ℚ)
      (hpn : ∀ s a s', 0 ≤ p s a s')
      (hsum : ∀ s a, ∑ s', p s a s' = 1)
      (β : ℚ) (hβ : 0 ≤ β)
      (x y : S → ℚ) (M : ℚ) (hM : ∀ t, |x t - y t| ≤ M) (s : S)
      (hne : (legal s).Nonempty) (hny : (legal s).Nonempty),
      bellmanOf legal r p β x s hne ≤ bellmanOf legal r p β y s hny + β * M) ∧
  ((∀ (c : SubpoenaCtx) (m : SubpoenaMeasure), measureLegal m c = true →
      c.filedInTime = true) ∧
   (legalOptions { isNonParty := true, stagePreTrial := true,
                   filedInTime := true } =
      [SubpoenaMeasure.quash, SubpoenaMeasure.vacate,
       SubpoenaMeasure.protective]) ∧
   (legalOptions { isNonParty := false, stagePreTrial := true,
                   filedInTime := true } =
      [SubpoenaMeasure.vacate, SubpoenaMeasure.protective]) ∧
   (legalOptions { isNonParty := true, stagePreTrial := true,
                   filedInTime := false } = []))

/-- D122 庭审或口头辩论提纲能否回应最佳反方观点与具体事实（反例：只
列弱反方并以数量宣称已回应最强反方）：提纲覆盖冻结图——主主张、最佳
反驳、两条弱反驳与主理论（含备位）全部覆盖且证据依赖逐节点保留（全
称：过覆盖门的图中每节点 id 覆盖、依赖与备位保持）；数量见证——只列
主主张加两条弱反驳的提纲（3 项）不过覆盖门，最佳反驳与备位结构缺
失，数量不等于回应了最强反方。 -/
def demand_D122 : Prop :=
  (∀ {S A : Type} [Fintype S] [DecidableEq S] [DecidableEq A]
      (legal : S → Finset A) (r : S → A → ℚ)
      (p : S → A → S → ℚ)
      (hpn : ∀ s a s', 0 ≤ p s a s')
      (hsum : ∀ s a, ∑ s', p s a s' = 1)
      (β : ℚ) (hβ : 0 ≤ β)
      (x y : S → ℚ) (M : ℚ) (hM : ∀ t, |x t - y t| ≤ M) (s : S)
      (hne : (legal s).Nonempty) (hny : (legal s).Nonempty),
      bellmanOf legal r p β x s hne ≤ bellmanOf legal r p β y s hny + β * M) ∧
  ((coversFrozen frozenGraph fullOutline = true) ∧
   (∀ (g : List ArgNode) (o : Outline), coversFrozen g o = true →
      ∀ (n : ArgNode), n ∈ g → strIn n.id o.covered = true
        ∧ depsKeptFor o n = true ∧ altsKeptFor o n = true) ∧
   (coversFrozen frozenGraph weakOutline = false ∧ weakOutline.covered.length = 3))

/-- D123 多跳法律工具查询是否足以支撑最后报告中的每项陈述（反例：接
口超时返回空列表，不能写成查无诉讼）：全称——过溯源门的断言必有查询
输入与原始记录（溯源门 = 四链组件全在场：输入、中间连接、原记录、转
换见证）；完整见证——有据断言过门且 ok 查询读出 found 1；超时≠查无
——超时读出 unavailable 且绝非 noRecords，只有 ok 空列表才是查无
（verified no-records）；空洞断言（无连接、无记录、静默空转换）不过
门。 -/
def demand_D123 : Prop :=
  (∀ {S A : Type} [Fintype S] [DecidableEq S] [DecidableEq A]
      (legal : S → Finset A) (r : S → A → ℚ)
      (p : S → A → S → ℚ)
      (hpn : ∀ s a s', 0 ≤ p s a s')
      (hsum : ∀ s a, ∑ s', p s a s' = 1)
      (β : ℚ) (hβ : 0 ≤ β)
      (x y : S → ℚ) (M : ℚ) (hM : ∀ t, |x t - y t| ≤ M) (s : S)
      (hne : (legal s).Nonempty) (hny : (legal s).Nonempty),
      bellmanOf legal r p β x s hne ≤ bellmanOf legal r p β y s hny + β * M) ∧
  ((∀ (a : FinalAssertion), sourced a = true → a.inputs ≠ [] ∧ a.records ≠ []) ∧
   (sourced litigationAssertion = true ∧
      readoutOf (QueryOutcome.records ["docket-2026-001"]) = FactReadout.found 1) ∧
   (readoutOf QueryOutcome.timeout = FactReadout.unavailable ∧
      ¬ (readoutOf QueryOutcome.timeout = FactReadout.noRecords) ∧
      readoutOf (QueryOutcome.records []) = FactReadout.noRecords) ∧
   (sourced hollowAssertion = false))

/-! D124-D134 (groups 14+15 伦理、隐私与表达可靠性＋美国法特定问题与
法律语言任务, W2-A batch B14): each def is that demand's own contract,
translated from ALL_134_MATH_CONTRACTS.md.  The first conjunct is the
group-registered component — Evidence.step_rules_mono for group 14
(D124-D130), Probability.condition_incompatible_iff for group 15
(D131-D134); the remaining conjuncts are the demand's own operational
semantics with its adverse case, built on helpers local to this region
in the group-08/13 style.  C2-C5 suspension check (W2B §5.3 B14 row):
none of the eleven bold sentences carries a CAD/optimization sub-clause —
D128's "明示价值序/约束下的决策与敏感性" is a discrete lexicographic
decision over an explicitly declared finite value order with an
order-swap sensitivity witness (no continuous program, no quantifier
elimination, values are ℕ preference indices, not amounts), so no C2-C5
suspension annotation applies — determination recorded in
.local/agent_AG_w2a_b14_report.md §三, following the B13 precedent of
recording the honest reading instead of fabricating a suspension.  The
green carriers actually consumed: Evidence/Withdrawal (step_rules_mono)
and Probability/Conditioning (condition_incompatible_iff) as the
first-conjunct components; Seams/UnifiedBetaDomain was checked and needs
no Lean-side face here (no bold sentence claims a posterior weight or
CDF value) — the PY-PROB faces of D125/D134 consume its exact-ℚ mirror
unified.beta on the Python side. -/

/-- D124 helper: one interest-relation edge of the matter's interest
graph — the person, the related party and the relation kind. -/
structure IntEdge where
  person : String
  party : String
  kind : String

/-- D124 helper: a registered conflict rule — the relation kind that
triggers it, the disposition obligation it carries, and whether the
conflict class may be waived at all. -/
structure ConRule where
  trigger : String
  duty : String
  waivable : Bool

/-- D124 helper: does any edge of the graph carry relation kind `k`. -/
def ethKindIn (k : String) : List IntEdge → Bool
  | [] => false
  | e :: es => if e.kind = k then true else ethKindIn k es

/-- D124 helper: the triggered obligations — exactly the registered
rules whose trigger kind occurs in the interest graph, each reported
with its disposition duty. -/
def ethDuties (edges : List IntEdge) (rules : List ConRule) :
    List (String × String) :=
  (rules.filter (fun r => ethKindIn r.trigger edges)).map
    (fun r => (r.trigger, r.duty))

/-- D124 helper: the authority levels that may grant a waiver or
approval. -/
inductive AuthLevel where
  | none | managingPartner | ethicsPanel
  deriving DecidableEq

/-- D124 helper: the state of an approval document — a draft nobody has
granted, or a grant by a named authority. -/
inductive ApprovalState where
  | draft
  | granted (auth : AuthLevel)

/-- D124 helper: a conflict is cleared only by a granted approval with
adequate authority — non-waivable conflicts are never cleared, waivable
ones need the ethics panel, and a draft clears nothing. -/
def ethCleared (r : ConRule) (st : ApprovalState) : Bool :=
  match st with
  | ApprovalState.draft => false
  | ApprovalState.granted auth =>
      if r.waivable = true then
        (if auth = AuthLevel.ethicsPanel then true else false)
      else false

/-- D124 witness: the ethics registry — a non-waivable concurrent-client
conflict and a waivable former-client conflict. -/
def ethRegistry : List ConRule :=
  [{ trigger := "concurrent-client", duty := "disclose-and-screen",
     waivable := false },
   { trigger := "former-client", duty := "disclose-and-obtain-waiver",
     waivable := true }]

/-- D124 witness: the matter's interest graph carries a concurrent-client
edge (and nothing else). -/
def matterEdges : List IntEdge :=
  [{ person := "attorney-x", party := "opposing-corp",
     kind := "concurrent-client" }]

/-- D125 helper: one row of a fairness audit — the protected attribute,
a proxy variable that may leak it, and a case number. -/
structure FairRow where
  prot : Bool
  proxy : String
  caseNo : ℕ

/-- D125 helper: the counterfactual twin of a row — the same row with
the protected attribute flipped. -/
def flipProt (r : FairRow) : FairRow := { r with prot := !r.prot }

/-- D125 helper: equality of two verdicts as a plain match on Bool. -/
def verdictSame (a b : Bool) : Bool :=
  match a, b with
  | true, true => true
  | false, false => true
  | _, _ => false

/-- D125 helper: the counterfactual invariance check — flipping the
protected attribute of every audited row leaves the classifier output
unchanged. -/
def invariantUnder (f : FairRow → Bool) (rows : List FairRow) : Bool :=
  rows.all (fun r => verdictSame (f (flipProt r)) (f r))

/-- D125 helper: how many rows of group `g` the classifier flags. -/
def groupSel (f : FairRow → Bool) (rows : List FairRow) (g : Bool) : ℕ :=
  (rows.filter (fun r => (r.prot == g) && f r)).length

/-- D125 helper: the size of group `g` among the audited rows. -/
def groupSize (rows : List FairRow) (g : Bool) : ℕ :=
  (rows.filter (fun r => r.prot == g)).length

/-- D125 helper: the group risk indicator — the flagging rate of one
protected group (exact ℚ ratio). -/
def groupRate (f : FairRow → Bool) (rows : List FairRow) (g : Bool) : ℚ :=
  (groupSel f rows g : ℚ) / (groupSize rows g : ℚ)

/-- D125 helper: which check a fairness certificate attests — the two
checks stay separately tagged; a tag attests exactly one. -/
inductive FairTag where
  | invariance | groupRisk
  deriving DecidableEq

def isInvTag (t : FairTag) : Bool :=
  match t with
  | FairTag.invariance => true
  | FairTag.groupRisk => false

def isRiskTag (t : FairTag) : Bool :=
  match t with
  | FairTag.invariance => false
  | FairTag.groupRisk => true

/-- D125 helper: the full-fairness claim needs both certificates — no
single-tag certificate list suffices. -/
def fairnessAll (tags : List FairTag) : Bool :=
  (tags.any isInvTag) && (tags.any isRiskTag)

/-- D125 adverse witness: rows whose protected attribute is perfectly
leaked by the proxy. -/
def leakRows : List FairRow :=
  [{ prot := true, proxy := "zip-17", caseNo := 1 },
   { prot := true, proxy := "zip-17", caseNo := 2 },
   { prot := false, proxy := "zip-03", caseNo := 3 },
   { prot := false, proxy := "zip-03", caseNo := 4 }]

/-- D125 adverse witness: the proxy-keyed classifier — it never reads
`prot`, so invariance holds, while the two groups' flagging rates differ
maximally. -/
def proxyKeyed : FairRow → Bool :=
  fun r => if r.proxy = "zip-17" then true else false

/-- D125 adverse witness: the leak audit produced only the invariance
certificate — the full-fairness claim is not licensed. -/
def leakCerts : List FairTag := [FairTag.invariance]

/-- D126 helper: one actual data flow — the data category, the
destination and the declared purpose. -/
structure DataFlow where
  category : String
  dest : String
  purpose : String

/-- D126 helper: one permitted use — a category/purpose pair the user
has consented to. -/
structure UsePerm where
  category : String
  purpose : String

/-- D126 helper: one policy-promise sentence — the text ledger is a
separate type and never enters the compliance computation. -/
structure PolicyPromise where
  category : String
  text : String

/-- D126 helper: a flow is compliant iff its category/purpose pair is a
permitted use — the promises ledger is not an input. -/
def flowOk (perms : List UsePerm) (f : DataFlow) : Bool :=
  perms.any (fun p =>
    if p.category = f.category then
      (if p.purpose = f.purpose then true else false)
    else false)

/-- D126 helper: the compliance verdict over all flows. -/
def flowsOk (perms : List UsePerm) (flows : List DataFlow) : Bool :=
  flows.all (fun f => flowOk perms f)

/-- D126 adverse witness: the policy promises "we never share" while an
actual ad-partner marketing flow exists. -/
def noSharePromise : PolicyPromise where
  category := "email-list"
  text := "we never share"

def adFlow : DataFlow where
  category := "email-list"
  dest := "ad-partner"
  purpose := "marketing"

/-- D126 witness: the permitted service flow. -/
def serviceFlow : DataFlow where
  category := "usage-stats"
  dest := "internal-analytics"
  purpose := "service-improvement"

/-- D126 witness: the site's permitted uses. -/
def sitePerms : List UsePerm :=
  [{ category := "usage-stats", purpose := "service-improvement" }]

/-- D127 helper: disclosure items are typed — statutory requirements vs
best-practice recommendations; the two types never merge. -/
inductive DiscKind where
  | statutory | bestPractice
  deriving DecidableEq

structure DiscItem where
  item : String
  kind : DiscKind

def isStatutory (i : DiscItem) : Bool :=
  if i.kind = DiscKind.statutory then true else false

def isBestPractice (i : DiscItem) : Bool :=
  if i.kind = DiscKind.bestPractice then true else false

/-- D127 helper: the statutory-coverage gate — every statutory item of
the register is in the done list. -/
def statCovered (items : List DiscItem) (done : List String) : Bool :=
  (items.filter isStatutory).all (fun i => strIn i.item done)

/-- D127 helper: the best-practice readout stays advisory-typed — done
best-practice items are reported as (item, "advisory") pairs. -/
def advisoryDone (items : List DiscItem) (done : List String) :
    List (String × String) :=
  (items.filter (fun i => isBestPractice i && strIn i.item done)).map
    (fun i => (i.item, "advisory"))

/-- D127 witness: the register — three statutory items, two best-practice
items. -/
def scRegister : List DiscItem :=
  [{ item := "conflict-mineral-report", kind := DiscKind.statutory },
   { item := "forced-labor-disclosure", kind := DiscKind.statutory },
   { item := "ghg-emissions", kind := DiscKind.statutory },
   { item := "supplier-diversity", kind := DiscKind.bestPractice },
   { item := "open-source-policy", kind := DiscKind.bestPractice }]

/-- D127 adverse witness: the filing covers two of three statutory items
plus both best-practice items — four done entries, yet the statutory
gate fails; optional disclosures cannot compensate. -/
def gapDone : List String :=
  ["conflict-mineral-report", "forced-labor-disclosure",
   "supplier-diversity", "open-source-policy"]

def fullDone : List String :=
  ["conflict-mineral-report", "forced-labor-disclosure", "ghg-emissions",
   "supplier-diversity", "open-source-policy"]

/-- D128 helper: one decision option with its explicit scores on the two
declared value dimensions — privacy standing and efficiency standing
(ℕ preference indices, not amounts). -/
structure ValChoice where
  name : String
  privacy : ℕ
  efficiency : ℕ
  deriving DecidableEq

/-- D128 helper: the score of an option on a named declared dimension. -/
def scoreOn (c : ValChoice) (dim : String) : ℕ :=
  if dim = "privacy" then c.privacy
  else if dim = "efficiency" then c.efficiency
  else 0

/-- D128 helper: `a` is strictly better than `b` under the declared
lexicographic order — the first declared dimension on which they differ
decides. -/
def betterUnder : List String → ValChoice → ValChoice → Bool
  | [], _, _ => false
  | d :: ds, a, b =>
      if scoreOn a d > scoreOn b d then true
      else if scoreOn b d > scoreOn a d then false
      else betterUnder ds a b

def nameNe (x y : String) : Bool := if x = y then false else true

/-- D128 helper: does any option strictly beat `a` under the declared
order. -/
def beatsAny (order : List String) (opts : List ValChoice)
    (a : ValChoice) : Bool :=
  opts.any (fun b => nameNe b.name a.name && betterUnder order b a)

/-- D128 helper: the decision under a declared order — an option that no
other option strictly beats; with no declared order there is no
decision (none). -/
def decideBy (order : List String) (opts : List ValChoice) :
    Option ValChoice :=
  match order with
  | [] => none
  | _ :: _ =>
      match (opts.filter (fun a => !beatsAny order opts a)) with
      | winner :: _ => some winner
      | [] => none

/-- D128 helper: the kind of premise that may license a value-ordered
decision — an explicitly declared value order, or a historical majority
preference; only the first licenses decisions. -/
inductive PremKind where
  | declaredValue | majorityPreference
  deriving DecidableEq

structure ValPremise where
  kind : PremKind
  order : List String

/-- D128 helper: decisions ride only on declared-value premises — a
majority-preference premise yields no decision. -/
def decideUnder (prem : ValPremise) (opts : List ValChoice) :
    Option ValChoice :=
  if prem.kind = PremKind.declaredValue then decideBy prem.order opts
  else none

/-- D128 witness: three disclosure options — a strict-privacy option, a
fast option and a privacy-preserving efficient option. -/
def valOpts : List ValChoice :=
  [{ name := "full-privacy", privacy := 5, efficiency := 2 },
   { name := "fast-track", privacy := 2, efficiency := 5 },
   { name := "balanced-veil", privacy := 5, efficiency := 4 }]

def privacyFirst : List String := ["privacy", "efficiency"]

def efficiencyFirst : List String := ["efficiency", "privacy"]

/-- D128 adverse witness: a historical majority preference (the rubric
majority liked the fast track) — as a premise it licenses no decision. -/
def majorityPrem : ValPremise where
  kind := PremKind.majorityPreference
  order := efficiencyFirst

/-- D129 helper: one source of record with its declared support scope —
the proposition ids it actually supports. -/
structure SourceRec where
  id : String
  supports : List String

/-- D129 helper: one report claim — the proposition, the cited source,
the data rows, the declared operation, and the claimed number. -/
structure ClaimRow where
  prop : String
  source : String
  data : List ℚ
  op : String
  claimed : ℚ

/-- D129 helper: the citation read-back — the cited id exists in the
source registry. -/
def citeOk (srcs : List SourceRec) (c : ClaimRow) : Bool :=
  srcs.any (fun s => if s.id = c.source then true else false)

/-- D129 helper: the support-scope check — the cited source's declared
scope actually contains the proposition. -/
def scopeOk (srcs : List SourceRec) (c : ClaimRow) : Bool :=
  srcs.any (fun s =>
    if s.id = c.source then (if strIn c.prop s.supports then true else false)
    else false)

/-- D129 helper: the numeric recomputation of the claimed value. -/
def recompute (c : ClaimRow) : ℚ :=
  if c.op = "sum" then c.data.foldl (fun acc x => acc + x) 0
  else if c.op = "count" then (c.data.length : ℚ)
  else 0

/-- D129 helper: the verification verdict — an unresolved conflict
touching the cited source holds the claim (never escalates); otherwise
the claim verifies only with citation read-back and support scope. -/
inductive ClaimVerdict where
  | verified | failed | held
  deriving DecidableEq

def conflictTouches (conflicts : List (String × String)) (src : String) :
    Bool :=
  conflicts.any (fun k =>
    if k.1 = src then true else (if k.2 = src then true else false))

def claimVerdict (srcs : List SourceRec)
    (conflicts : List (String × String)) (c : ClaimRow) : ClaimVerdict :=
  if conflictTouches conflicts c.source = true then ClaimVerdict.held
  else if (citeOk srcs c && scopeOk srcs c) = true then ClaimVerdict.verified
  else ClaimVerdict.failed

/-- D129 witness: the source registry — a damages table supporting the
loss-total proposition, a docket index supporting the count
proposition. -/
def repSources : List SourceRec :=
  [{ id := "damages-table-7", supports := ["total-loss"] },
   { id := "docket-index-2026", supports := ["pending-count"] }]

/-- D129 witness: the faithful claims — the numbers recompute and the
propositions sit in the cited sources' scopes. -/
def lossClaim : ClaimRow where
  prop := "total-loss"
  source := "damages-table-7"
  data := [100, 250, 150]
  op := "sum"
  claimed := 500

def countClaim : ClaimRow where
  prop := "pending-count"
  source := "docket-index-2026"
  data := [1, 1, 1]
  op := "count"
  claimed := 3

/-- D129 adverse witness: a real citation that does not support the
proposition — the docket index cited for the loss total. -/
def misusedCitation : ClaimRow where
  prop := "total-loss"
  source := "docket-index-2026"
  data := [100, 250, 150]
  op := "sum"
  claimed := 500

/-- D129 adverse witness: a hallucinated number on a right citation —
the same source and proposition, the claimed value inflated. -/
def inflatedClaim : ClaimRow where
  prop := "total-loss"
  source := "damages-table-7"
  data := [100, 250, 150]
  op := "sum"
  claimed := 600

/-- D129 witness: an unresolved authenticity conflict on the damages
table. -/
def tableConflict : List (String × String) :=
  [("damages-table-7", "affidavit-9")]

/-- D130 helper: one scenario-tagged conclusion — the scenario label (κ,
fact assumption or interpretation) and the conclusion reached under it. -/
structure ScenConc where
  scenario : String
  conclusion : String

/-- D130 helper: every conclusion of `cs` carries scenario `s`. -/
def allSameScen (s : String) : List ScenConc → Bool
  | [] => true
  | c :: cs => if c.scenario = s then allSameScen s cs else false

/-- D130 helper: assembling a witness — conclusions from a single
scenario assemble into a conditional witness carrying that label;
conclusions from different scenarios are rejected outright. -/
inductive AssembleOut where
  | conditional (scen : String)
  | rejected
  deriving DecidableEq

def assemble (cs : List ScenConc) : AssembleOut :=
  match cs with
  | [] => AssembleOut.rejected
  | c :: rest =>
      if allSameScen c.scenario (c :: rest) then
        AssembleOut.conditional c.scenario
      else AssembleOut.rejected

/-- D130 witness: two conclusions under κ1 alone assemble
conditionally. -/
def kappa1Only : List ScenConc :=
  [{ scenario := "kappa-1", conclusion := "motion-to-dismiss-denied" },
   { scenario := "kappa-1", conclusion := "liability-found" }]

/-- D130 adverse witness: the favorable conclusions cherry-picked from
two mutually exclusive scenarios — rejected, no unconditional witness. -/
def cherryPicked : List ScenConc :=
  [{ scenario := "kappa-1", conclusion := "liability-found" },
   { scenario := "kappa-2", conclusion := "damages-maximized" }]

/-- D131 helper: the provision types inside a selected statute fragment —
a private-action pathway, a substantive right, a bare prohibition. -/
inductive ProvKind where
  | privateAction | substantiveRight | prohibition
  deriving DecidableEq

structure Provision where
  cite : String
  kind : ProvKind

def kindIs (p : Provision) (k : ProvKind) : Bool :=
  if p.kind = k then true else false

/-- D131 helper: the provisions of the fragment of one kind. -/
def provOf (frags : List Provision) (k : ProvKind) : List Provision :=
  frags.filter (fun p => kindIs p k)

/-- D131 helper: the private-action determination — made only inside the
selected fragment: some provision of the fragment is a private-action
pathway. -/
def hasPrivAction (frags : List Provision) : Bool :=
  !(provOf frags ProvKind.privateAction).isEmpty

/-- D131 adverse witness: a prohibition-only fragment — no private
action follows. -/
def prohibitionFragment : List Provision :=
  [{ cite := "§5(a)(1)", kind := ProvKind.prohibition }]

/-- D131 adverse witness: prohibition plus substantive rights — still no
private-action pathway. -/
def rightPlusBanFragment : List Provision :=
  [{ cite := "§5(a)(1)", kind := ProvKind.prohibition },
   { cite := "§4(b)", kind := ProvKind.substantiveRight }]

/-- D131 witness: a fragment with an explicit private-action pathway
beside its substantive right — separately identified. -/
def privActionFragment : List Provision :=
  [{ cite := "§4(b)", kind := ProvKind.substantiveRight },
   { cite := "§4(c)", kind := ProvKind.privateAction }]

/-- D132 helper: one holding candidate — a core holding or a dictum, its
issue key, and its salient words. -/
structure HoldingCand where
  id : String
  isHolding : Bool
  issueKey : String
  words : List String

/-- D132 helper: keyword similarity — the candidate shares at least one
salient word with the question. -/
def keywordSimilar (qwords : List String) (c : HoldingCand) : Bool :=
  c.words.any (fun w => strIn w qwords)

/-- D132 helper: the match certificate — the matched candidate, the
question it answers, and a transferable flag that stays false (transfer
to a new case needs its own relevance proof). -/
structure MatchCert where
  cand : String
  question : String
  transferable : Bool
  deriving DecidableEq

/-- D132 helper: holding matching under the given candidates and question
semantics — only a core holding whose issue key matches the question's
keys and whose words overlap counts; a dictum never matches however
similar its words. -/
def holdingMatch (question : String) (qkeys : List String)
    (qwords : List String) (cands : List HoldingCand) : Option MatchCert :=
  match cands.filter (fun c =>
    c.isHolding && strIn c.issueKey qkeys && keywordSimilar qwords c) with
  | [] => none
  | c :: _ => some { cand := c.id, question := question,
                     transferable := false }

/-- D132 witness: the question — preemption of state-law claims. -/
def scqQuestion : String := "is the state-law claim preempted"

def scqKeys : List String := ["federal-preemption"]

def scqWords : List String := ["preempt", "state-law", "federal"]

/-- D132 witness: the core holding with the matching issue key. -/
def coreHolding : HoldingCand where
  id := "holding-preemption"
  isHolding := true
  issueKey := "federal-preemption"
  words := ["preempt", "federal", "scheme"]

/-- D132 adverse witness: a keyword-similar dictum — same salient words,
wrong status (a dictum), so it never substitutes for the core holding. -/
def similarDictum : HoldingCand where
  id := "dictum-preemption-aside"
  isHolding := false
  issueKey := "federal-preemption"
  words := ["preempt", "state-law", "aside"]

def holdingPool : List HoldingCand := [coreHolding, similarDictum]

def dictumOnly : List HoldingCand := [similarDictum]

/-- D133 helper: one independently annotated plaintiff mention — the
person key and the character span of the mention in the segment. -/
structure Mention where
  person : String
  st : ℕ
  en : ℕ

/-- D133 helper: the segment under extraction — its length and the
annotated mentions. -/
structure ExSegment where
  len : ℕ
  mentions : List Mention

/-- D133 helper: a mention's span is valid — nonempty and inside the
segment. -/
def spanOk (seg : ExSegment) (m : Mention) : Bool :=
  Nat.ble m.st m.en && Nat.ble m.en seg.len

/-- D133 helper: the plaintiff extraction — exactly the persons whose
annotated mentions carry valid spans; each person stays a separate key. -/
def plaintiffsOf (seg : ExSegment) : List String :=
  (seg.mentions.filter (fun m => spanOk seg m)).map Mention.person

/-- D133 witness: the class-action segment — two co-plaintiffs, each
with her own annotated span. -/
def sslaSegment : ExSegment where
  len := 120
  mentions :=
    [{ person := "Alice Chen", st := 14, en := 24 },
     { person := "Bob Diaz", st := 60, en := 67 }]

/-- D133 adverse witness: the merged-name row — "Alice Chen and Bob Diaz"
as one key is not an annotated person and never enters the extraction. -/
def mergedName : String := "Alice Chen and Bob Diaz"

/-- D133 adverse witness: a span running past the segment end (en > len)
— the annotation is excluded from the extraction. -/
def ghostSegment : ExSegment where
  len := 10
  mentions := [{ person := "Ghost", st := 8, en := 12 }]

/-- D134 helper: the argument-evidence text classes — statistical
evidence, direct evidence, or neither. -/
inductive EvClass where
  | statistical | directEvidence | neither
  deriving DecidableEq

/-- D134 helper: the text classification of one passage by its evidence
markers — statistical hits vs direct-evidence hits (ℕ marker counts). -/
def classifyHits (statHits directHits : ℕ) : EvClass :=
  if 0 < statHits && statHits > directHits then EvClass.statistical
  else if 0 < directHits && directHits > statHits then EvClass.directEvidence
  else EvClass.neither

/-- D134 helper: a do-effect (interventional causal-effect) conclusion —
requires an identification witness of its own type. -/
structure DoEffect where
  eff : ℚ
  ident : String

/-- D134 helper: the classification-to-causation bridge — structurally
absent: no text classification generates a do-effect conclusion. -/
def doFromEvidence : EvClass → Option DoEffect :=
  fun _ => none

/-- D134 witness: the discrimination brief's marker profiles — a
statistical passage, a direct-evidence passage, and an off-topic tie. -/
def statPassage : ℕ × ℕ := (3, 0)

def directPassage : ℕ × ℕ := (0, 2)

def mixedOffTopic : ℕ × ℕ := (1, 1)

/-- D124 专业利益冲突是否被识别并在批准中给出保障措施（反例：只生成董
事会批准草稿就自动消除实际利益冲突）：利益关系图触发已登记的冲突与处
置义务——触发的义务对恰来自登记规则且触发关系确实出现在图中；豁免或
批准需适当权限——草稿对一切冲突不消除（草稿≠批准），不可豁免冲突哪怕
伦理委员会也不消除，可豁免冲突仅伦理委员会消除（管理合伙人权限不
足）；见证——concurrent-client 边触发 disclose-and-screen 义务。 -/
def demand_D124 : Prop :=
  (∀ {A : Type} [DecidableEq A] [Fintype A] (R R' : Finset (Finset A × A)) (hR : R ⊆ R') (F S : Finset A), step R F S ⊆ step R' F S) ∧
  ((∀ (edges : List IntEdge) (rules : List ConRule) (tr duty : String),
      (tr, duty) ∈ ethDuties edges rules →
        ethKindIn tr edges = true ∧
          ∃ r : ConRule, r ∈ rules ∧ r.trigger = tr ∧ r.duty = duty) ∧
   (∀ (r : ConRule), ethCleared r ApprovalState.draft = false) ∧
   (ethDuties matterEdges ethRegistry =
      [("concurrent-client", "disclose-and-screen")] ∧
    ethCleared { trigger := "concurrent-client",
                 duty := "disclose-and-screen", waivable := false }
        (ApprovalState.granted AuthLevel.ethicsPanel) = false) ∧
   (ethCleared { trigger := "former-client",
                 duty := "disclose-and-obtain-waiver", waivable := true }
        (ApprovalState.granted AuthLevel.managingPartner) = false ∧
    ethCleared { trigger := "former-client",
                 duty := "disclose-and-obtain-waiver", waivable := true }
        (ApprovalState.granted AuthLevel.ethicsPanel) = true))

/-- D125 回答是否体现偏见、歧视或不当的法律伦理判断（反例：移除敏感属
性但代理变量仍泄露，不得声称已证明公平）：可指定的反事实输入不变性与
群体风险指标分别检验——不变性检查全称成立当且仅当翻转保护属性逐行保
持输出；两项检查分立标注——单一标签证书不构成公平全概念；反例见证
——代理键分类器通过不变性检查（从不读保护属性）而两组风险指标一个为
1 一个为 0（代理泄露），不变性通过≠公平。 -/
def demand_D125 : Prop :=
  (∀ {A : Type} [DecidableEq A] [Fintype A] (R R' : Finset (Finset A × A)) (hR : R ⊆ R') (F S : Finset A), step R F S ⊆ step R' F S) ∧
  ((∀ (f : FairRow → Bool) (rows : List FairRow),
      invariantUnder f rows = true →
        ∀ r ∈ rows, f (flipProt r) = f r) ∧
   (invariantUnder proxyKeyed leakRows = true ∧
      groupRate proxyKeyed leakRows true = 1 ∧
      groupRate proxyKeyed leakRows false = 0 ∧
      ¬ (groupRate proxyKeyed leakRows true =
         groupRate proxyKeyed leakRows false)) ∧
   (fairnessAll leakCerts = false ∧
      ∀ (t : FairTag), isInvTag t = true → isRiskTag t = false))

/-- D126 隐私政策如何描述收集、使用、共享、保存与用户权利（反例：文本
写“不共享”不能直接证明代码与运营从不共享）：隐私政策承诺、实际数据流
与准许用途分开——合规判定只吃准许用途表与实际数据流，承诺文本账本根
本不是判定的输入（任何承诺文本都翻转不了判定）；全称——过合规门的
数据流的类别/目的对确实登记为准许用途；见证——准许的 service 流过
门、未准许的 ad-partner 营销流不过门（哪怕政策写着 we never
share）。 -/
def demand_D126 : Prop :=
  (∀ {A : Type} [DecidableEq A] [Fintype A] (R R' : Finset (Finset A × A)) (hR : R ⊆ R') (F S : Finset A), step R F S ⊆ step R' F S) ∧
  ((∀ (perms : List UsePerm) (flows : List DataFlow),
      flowsOk perms flows = true →
        ∀ f ∈ flows, ∃ p ∈ perms, p.category = f.category ∧
          p.purpose = f.purpose) ∧
   (flowsOk sitePerms [serviceFlow] = true) ∧
   (flowsOk sitePerms [adFlow] = false ∧
      ∀ (p : PolicyPromise), flowsOk sitePerms [adFlow] = false))

/-- D127 供应链披露是否包含规定项目，与最佳实践是否区分（反例：遗漏法
定项目却用更多可选披露补分，不算满足）：法定必需披露集合逐项覆盖
——过覆盖门当且仅当每个法定条目都在完成清单里；反例见证——三法定条
目只完成两条加两条最佳实践（四条完成记录）仍不过门，可选披露补不了法
定缺口；全法定完成才过门；最佳实践保持建议类型——建议读出全部带
advisory 标注。 -/
def demand_D127 : Prop :=
  (∀ {A : Type} [DecidableEq A] [Fintype A] (R R' : Finset (Finset A × A)) (hR : R ⊆ R') (F S : Finset A), step R F S ⊆ step R' F S) ∧
  ((∀ (items : List DiscItem) (done : List String),
      statCovered items done = true →
        ∀ i ∈ items, i.kind = DiscKind.statutory →
          strIn i.item done = true) ∧
   (statCovered scRegister gapDone = false ∧ gapDone.length = 4 ∧
      statCovered scRegister fullDone = true) ∧
   (∀ (items : List DiscItem) (done : List String) (p : String × String),
      p ∈ advisoryDone items done → p.2 = "advisory"))

/-- D128 法律与道德、社会影响问题能否给出符合题目要求的判断（反例：把
评分rubric或历史多数偏好当规范真理）：可形式化的是明示价值序/约束下
的决策与敏感性——决策随声明的价值序走（privacy 优先选出
balanced-veil、efficiency 优先选出 fast-track，两序不同结论不同＝敏
感性见证）；不从事实推出价值——无声明序则无决策（none），历史多数偏
好作为前提同样不产生决策（类型分立，多数偏好≠声明的价值前提）；全称
——任何决策输出都落在声明选项集内。 -/
def demand_D128 : Prop :=
  (∀ {A : Type} [DecidableEq A] [Fintype A] (R R' : Finset (Finset A × A)) (hR : R ⊆ R') (F S : Finset A), step R F S ⊆ step R' F S) ∧
  ((decideUnder { kind := PremKind.declaredValue, order := privacyFirst }
        valOpts =
      some { name := "balanced-veil", privacy := 5, efficiency := 4 } ∧
    decideUnder { kind := PremKind.declaredValue, order := efficiencyFirst }
        valOpts =
      some { name := "fast-track", privacy := 2, efficiency := 5 } ∧
    (decideUnder { kind := PremKind.declaredValue,
                   order := privacyFirst } valOpts).map ValChoice.name ≠
      (decideUnder { kind := PremKind.declaredValue,
                     order := efficiencyFirst } valOpts).map ValChoice.name) ∧
   (decideBy ([] : List String) valOpts = none ∧
      decideUnder majorityPrem valOpts = none) ∧
   (∀ (order : List String) (opts : List ValChoice) (o : ValChoice),
      decideBy order opts = some o → o ∈ opts))

/-- D129 引文、事实和数值是否有据，是否有幻觉或相关但误用的信息（反
例：引用真实但不支持该命题仍应失败）：引文回读、数值重算、支持范围与
声明逐项绑定——过验证门的断言其引文确实登记且命题确实落在该源的支
持范围内；数值重算——忠实声明的数值重算相等（sum 500、count 3），灌
水数值（600）重算不等即失败；反例见证——docket-index 真实存在但不
支持 total-loss，判定 failed；冲突未决不升级——damages-table 上的未
决真实性冲突使引用它的断言 held（既不 verified 也不升级），冲突消解
后才 verified。 -/
def demand_D129 : Prop :=
  (∀ {A : Type} [DecidableEq A] [Fintype A] (R R' : Finset (Finset A × A)) (hR : R ⊆ R') (F S : Finset A), step R F S ⊆ step R' F S) ∧
  ((∀ (srcs : List SourceRec) (conflicts : List (String × String))
      (c : ClaimRow),
      claimVerdict srcs conflicts c = ClaimVerdict.verified →
        citeOk srcs c = true ∧ scopeOk srcs c = true) ∧
   (recompute lossClaim = 500 ∧ lossClaim.claimed = 500 ∧
      recompute inflatedClaim = 500 ∧
      ¬ (recompute inflatedClaim = inflatedClaim.claimed) ∧
      recompute countClaim = 3 ∧ countClaim.claimed = 3) ∧
   (citeOk repSources misusedCitation = true ∧
      scopeOk repSources misusedCitation = false ∧
      claimVerdict repSources ([] : List (String × String)) misusedCitation =
        ClaimVerdict.failed) ∧
   (claimVerdict repSources tableConflict lossClaim = ClaimVerdict.held ∧
      ¬ (claimVerdict repSources tableConflict lossClaim =
         ClaimVerdict.verified) ∧
      claimVerdict repSources ([] : List (String × String)) lossClaim =
        ClaimVerdict.verified))

/-- D130 不同事实、规则、法域及假设的结论是否被不当混成单一确定答案
（反例：从互斥分支各取有利结论合并必须拒绝）：不同κ、事实假设或解释
的结果不得组成一个无条件见证——装配器只产条件见证（带单一场景标签）
或拒绝，无无条件形态；全称——装成条件见证则每条结论都带同一场景标
签；反例见证——κ1 下的两条结论装配为 conditional kappa-1，而跨 κ1/
κ2 各取一条有利结论（liability-found＋damages-maximized）被拒
绝。 -/
def demand_D130 : Prop :=
  (∀ {A : Type} [DecidableEq A] [Fintype A] (R R' : Finset (Finset A × A)) (hR : R ⊆ R') (F S : Finset A), step R F S ⊆ step R' F S) ∧
  ((∀ (cs : List ScenConc) (s : String),
      assemble cs = AssembleOut.conditional s →
        ∀ c ∈ cs, c.scenario = s) ∧
   (assemble kappa1Only = AssembleOut.conditional "kappa-1" ∧
      assemble cherryPicked = AssembleOut.rejected))

/-- D131 法条是否明文赋予私人起诉实施权利的途径（反例：存在禁止性条文
不自动推出任何私人可起诉）：规定的私人起诉途径/权限与实体权利分别标
识——途径查找与权利查找的成员互斥（一个条文不会同时是途径与权利，
类型分立）；并在选择法片段内判定——全称——判定为有私人起诉途径当
且仅当片段内存在 privateAction 条文（不从片段外推断）；反例见证
——仅禁止条文的片段判定无途径，禁止＋实体权利的片段同样无途径，含
§4(c) 明文途径的片段才判定有。 -/
def demand_D131 : Prop :=
  (∀ {S : Type} [Fintype S] [DecidableEq S] (p : S → ℚ) (e : S → Bool), condition p e = .incompatible ↔ ¬ (0 < evMass p e)) ∧
  ((∀ (frags : List Provision), hasPrivAction frags = true →
      ∃ p ∈ frags, p.kind = ProvKind.privateAction) ∧
   (∀ (frags : List Provision) (p : Provision),
      p ∈ provOf frags ProvKind.privateAction →
        p ∉ provOf frags ProvKind.substantiveRight) ∧
   (hasPrivAction prohibitionFragment = false ∧
      hasPrivAction rightPlusBanFragment = false ∧
      hasPrivAction privActionFragment = true))

/-- D132 最高法院审理问题应对应哪一个核心裁判要旨，而非相近措辞（反
例：关键词相似的旁论不能替代核心裁判要旨）：holding匹配在给定候选与
问题语义下检查——全称——任何匹配证书的候选都确实是核心要旨
（isHolding）且问题键在范围内且关键词确有重叠；类案迁移另证——匹配
证书恒不可迁移（transferable=false，迁移需要自己的相关性证明）；见
证——holding 池中核心要旨被配上不可迁移证书，而只含关键词相似旁论
的候选池匹配不出任何证书。 -/
def demand_D132 : Prop :=
  (∀ {S : Type} [Fintype S] [DecidableEq S] (p : S → ℚ) (e : S → Bool), condition p e = .incompatible ↔ ¬ (0 < evMass p e)) ∧
  ((∀ (question : String) (qkeys qwords : List String)
      (cands : List HoldingCand) (cert : MatchCert),
      holdingMatch question qkeys qwords cands = some cert →
        ∃ c ∈ cands, cert.cand = c.id ∧ c.isHolding = true ∧
          strIn c.issueKey qkeys = true ∧
          keywordSimilar qwords c = true) ∧
   (∀ (question : String) (qkeys qwords : List String)
      (cands : List HoldingCand) (cert : MatchCert),
      holdingMatch question qkeys qwords cands = some cert →
        cert.transferable = false) ∧
   (holdingMatch scqQuestion scqKeys scqWords holdingPool =
      some { cand := "holding-preemption",
             question := "is the state-law claim preempted",
             transferable := false } ∧
    holdingMatch scqQuestion scqKeys scqWords dictumOnly = none))

/-- D133 证券集体诉讼片段是否载明原告；有多人时是否全部抽取（反例：首
个名字抽对不等于全体原告齐全）：片段原告提及集合完整抽取需独立跨度标
注——全称——抽出的每个原告都有带合法跨度的独立标注（跨度在段内且非
空）；见证——两位共同原告 Alice Chen 与 Bob Diaz 各带自己的跨度被分
别抽出（只抽对首个名字不等于齐全：单名字表≠完整抽取）；多主体键不
合并——合并名"Alice Chen and Bob Diaz"不是标注过的主体键，永不入抽
取；越界跨度的标注（Ghost，en>len）被排除。 -/
def demand_D133 : Prop :=
  (∀ {S : Type} [Fintype S] [DecidableEq S] (p : S → ℚ) (e : S → Bool), condition p e = .incompatible ↔ ¬ (0 < evMass p e)) ∧
  ((∀ (seg : ExSegment) (n : String), n ∈ plaintiffsOf seg →
      ∃ m ∈ seg.mentions, m.person = n ∧ spanOk seg m = true) ∧
      (plaintiffsOf sslaSegment = ["Alice Chen", "Bob Diaz"] ∧
      ¬ (mergedName ∈ plaintiffsOf sslaSegment) ∧
      (["Alice Chen"] ≠ plaintiffsOf sslaSegment) ∧
      (plaintiffsOf ghostSegment = ([] : List String))))

/-- D134 劳动歧视案因果论证使用统计还是直接证据？这不是估计干预效果
（反例：统计证据类别命中不意味着识别了个案因果效应）：输出“统计/直接
证据使用”是文本分类——按标记命中数分类（统计型、直接证据型、皆非三
型，见证 3/0、0/2、1/1）；不得自动生成do效果结论——分类→因果结论的
桥结构性缺失：对一切分类标签 doFromEvidence 都是 none，统计型命中
（3/0）也产不出任何 do-effect 结论记录。 -/
def demand_D134 : Prop :=
  (∀ {S : Type} [Fintype S] [DecidableEq S] (p : S → ℚ) (e : S → Bool), condition p e = .incompatible ↔ ¬ (0 < evMass p e)) ∧
  ((classifyHits 3 0 = EvClass.statistical ∧
      classifyHits 0 2 = EvClass.directEvidence ∧
      classifyHits 1 1 = EvClass.neither) ∧
   (∀ (c : EvClass), doFromEvidence c = none) ∧
   (¬ ∃ (d : DoEffect), doFromEvidence (classifyHits 3 0) = some d))

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
