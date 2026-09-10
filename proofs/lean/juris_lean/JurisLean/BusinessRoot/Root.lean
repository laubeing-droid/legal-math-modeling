import Mathlib
import JurisLean.BusinessRoot.Semantics
import JurisLean.BusinessRoot.InputCodec
import JurisLean.BusinessRoot.GuardMachine
import JurisLean.BusinessRoot.PrincipalChecker
import JurisLean.BusinessRoot.Analytics
import JurisLean.BusinessRoot.ArtifactParser

/-!
ROOT06 — The instantiated end-to-end business root for the frozen task
`SYNTHETIC_EXACT_PRINCIPAL_ANALYTICS_TWO_FILES/1`:

WF(I0) ∧ CheckBusinessBundle(I0, π, d1, d2) = accept ⇒
∃ W, Worlds(W) = Ω(I0) ∧ JointSem_principal(I0, W) ∧ TaskSat_Q(W, m) ∧
     ReadBoth(d1, d2) = Protected_Q(W, m).

The frozen I0 is the synthetic principal task P=1000, one conditional payment
q=300 with recognition probability 2/5, threshold 800, costs (100, 60, 10, 10),
legal grid {600, 850, 1100}. `rootProtected` is computed from the independent
objects only — never from a renderer or a submitted certificate.

The checker reflected here is the mirrored independent checker (guarantee
level: kernel-checked semantics of mirrored algorithms + Python cross-check
evidence; byte-level lexing remains documented TCB). This proves no legal
statement, no real-case claim and no empirical property.
-/

namespace JurisLean.BusinessRoot

/-! ### The frozen input I0 -/

def rootAtom : String := "payment_recognized"

def rootSpec : PrincipalSpec :=
  { keys := [rootAtom]
    principal := 1000
    payments := [{ paymentId := "P1", amount := 300, recognitionAtom := rootAtom }]
    facts := [(rootAtom, Option.none)]
    constraint := Guard.truthy }

def rootWorldT : World := [true]
def rootWorldF : World := [false]

def rootModel : ModelInputs :=
  { weights := [(2 / 5, rootWorldT), (3 / 5, rootWorldF)]
    threshold := 800
    costP := 100
    costD := 60
    settleP := 10
    settleD := 10
    legalOptions := [600, 850, 1100]
    expectedC := 880
    expectedU := 0
    eventProbability := 3 / 5
    lower := 790
    upper := 930
    eligible := [850]
    selected := some 850 }

/-- The typed exact input, used by the binding check of ROOT02. -/
def rootInput : ExactInput :=
  { principal := 1000
    payment := 300
    probability := 2 / 5
    threshold := 800
    costP := 100
    costD := 60
    settleP := 10
    settleD := 10
    options := [600, 850, 1100] }

/-! ### Well-formedness of the frozen input (WF) -/

/-- WF(I0): declared keys, nonnegative principal and exactly two weighted
scenarios of the frozen shape. -/
theorem root_wf :
    rootSpec.keys = [rootAtom] ∧ 0 ≤ rootSpec.principal ∧
      rootModel.weights.length = 2 := by
  constructor
  · rfl
  · constructor
    · decide
    · decide

/-! ### Residuals and the witness table -/

theorem root_residual_true :
    residualOf 1000 [rootAtom] rootSpec.payments [true] = 700 := by
  simp [residualOf, recognizedSum, rootSpec, rootAtom, lookupVal]

theorem root_residual_false :
    residualOf 1000 [rootAtom] rootSpec.payments [false] = 1000 := by
  simp [residualOf, recognizedSum, rootSpec, rootAtom, lookupVal]

/-- Per-scenario clipped/overpayment values of the frozen task. -/
theorem root_cbal_true :
    clipC (residualOf 1000 [rootAtom] rootSpec.payments [true]) = 700 := by
  rw [root_residual_true]
  norm_num [clipC]

theorem root_cbal_false :
    clipC (residualOf 1000 [rootAtom] rootSpec.payments [false]) = 1000 := by
  rw [root_residual_false]
  norm_num [clipC]

theorem root_cover_true :
    clipU (residualOf 1000 [rootAtom] rootSpec.payments [true]) = 0 := by
  rw [root_residual_true]
  norm_num [clipU]

theorem root_cover_false :
    clipU (residualOf 1000 [rootAtom] rootSpec.payments [false]) = 0 := by
  rw [root_residual_false]
  norm_num [clipU]

def rootRowT : Witness := ⟨rootWorldT, 700, 0⟩
def rootRowF : Witness := ⟨rootWorldF, 1000, 0⟩
def rootRows : List Witness := [rootRowT, rootRowF]

/-- Condition rows of the frozen task, in solver enumeration order. -/
def rootRowsCond : List (List (String × Bool) × ℚ × ℚ) :=
  [([(rootAtom, true)], 700, 0), ([(rootAtom, false)], 1000, 0)]

/-- Expected protected record from independent objects — never from a
renderer or a submitted certificate. -/
def rootProtected : Protected := protectedOf 1000 rootRowsCond [] rootModel

/-! ### Frozen artifacts (as delivered, as structured tokens) -/

def rootDoc : DocArt :=
  { caseId := "DEMO-PRINCIPAL-01"
    issue := "principal-balance"
    creditor := "甲公司"
    debtor := "乙公司"
    debt := "DEBT-1"
    basis := "SYNTHETIC-BASIS"
    dueDay := "2026-08-01"
    asOfDay := "2026-09-09"
    assumptions := "合成示例前提"
    ctx := "synthetic-context-1"
    mode := "EXACT_FINITE_SCENARIOS"
    condT := [(rootAtom, true)]
    balT := 700
    overT := 0
    condF := [(rootAtom, false)]
    balF := 1000
    overF := 0 }

def rootJson : JsonArt :=
  { schema := "br/reference-two-file-delivery/1"
    requirement := requirementQ
    contextVersion := "synthetic-1"
    basisSid := "SYNTHETIC-BASIS"
    basisVer := "1"
    principal := 1000
    outT := ([(rootAtom, true)], 700, 0)
    outF := ([(rootAtom, false)], 1000, 0)
    weightT := ([(rootAtom, true)], 2 / 5)
    weightF := ([(rootAtom, false)], 3 / 5)
    threshold := 800
    costP := 100
    costD := 60
    settleP := 10
    settleD := 10
    options := [600, 850, 1100]
    expC := 880
    expU := 0
    event := 3 / 5
    lower := 790
    upper := 930
    eligible := [850]
    selected := some 850 }

/-! ### The three independent obligations, discharged for the frozen I0 -/

/-- Two-element membership decomposition. -/
theorem mem_two {x : Witness} {p q : Witness} (h : x ∈ [p, q]) : x = p ∨ x = q := by
  rcases List.mem_cons.mp h with h1 | h2
  · exact Or.inl h1
  · rcases List.mem_cons.mp h2 with h3 | h4
    · exact Or.inr h3
    · exact absurd h4 (by simp)

theorem root_worlds_match :
    WorldsMatch [rootAtom] [(rootAtom, Option.none)] Guard.truthy rootRows := by
  unfold WorldsMatch
  refine ⟨?_, ?_, ?_⟩
  · intro o ho
    rcases mem_two ho with rfl | rfl
    · simp [DomainOf, factsExtend, rootAtom, rootWorldT, Guard.denote, rootRowT]
    · simp [DomainOf, factsExtend, rootAtom, rootWorldF, Guard.denote, rootRowF]
  · intro vals hv
    rcases (domain_pair_exact rootAtom vals).mp hv with h | h
    · exact ⟨rootRowT, by simp [rootRows], by simpa [rootRowT, rootWorldT] using h.symm⟩
    · exact ⟨rootRowF, by simp [rootRows], by simpa [rootRowF, rootWorldF] using h.symm⟩
  · intro a ha b hb hab
    rcases mem_two ha with rfl | rfl
    · rcases mem_two hb with rfl | rfl
      · rfl
      · simp [rootRowT, rootWorldT, rootRowF, rootWorldF] at hab
    · rcases mem_two hb with rfl | rfl
      · simp [rootRowT, rootWorldT, rootRowF, rootWorldF] at hab
      · rfl

theorem root_joint_sem :
    JointSem 1000 [rootAtom] rootSpec.payments rootRows := by
  intro o ho
  rcases List.mem_cons.mp ho with h0 | ho
  · subst h0
    simp only [rootRowT, rootWorldT]
    refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
    rw [root_residual_true]
  · rcases List.mem_cons.mp ho with h0 | ho
    · subst h0
      simp only [rootRowF, rootWorldF]
      refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
      rw [root_residual_false]
    · simp [rootRows] at ho

theorem root_task_sat :
    TaskSat 1000 [rootAtom] rootSpec.payments rootModel rootRows := by
  unfold TaskSat
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    have hpm : p = ((2:ℚ) / 5, [true]) ∨ p = ((3:ℚ) / 5, [false]) := by
      simpa [rootModel] using hp
    rcases hpm with h0 | h0
    · subst h0; norm_num
    · subst h0; norm_num
  · norm_num [rootModel, weighted]
  · intro o ho p hp _
    rcases mem_two ho with rfl | rfl
    · all_goals rw [root_cbal_true]
    · all_goals rw [root_cbal_false]
  · intro o ho p hp _
    rcases mem_two ho with rfl | rfl
    · all_goals rw [root_cover_true]
    · all_goals rw [root_cover_false]
  · norm_num [rootModel, weighted]
  · norm_num [rootModel, weighted]
  · norm_num [rootModel, eventMass, cbal, cres, isRecognized, clipC]
  · norm_num [rootModel]
  · norm_num [rootModel]
  · simp [rootModel]
  · right
    exact ⟨850, by simp [rootModel], rfl⟩

/-! ### The mirrored bundle checker and the root theorem -/

/-- ULM04/ULM16-style obligation set for the frozen task, discharged by W. -/
def RootObligations (W : List Witness) : Prop :=
  WorldsMatch rootSpec.keys rootSpec.facts rootSpec.constraint W ∧
    JointSem rootSpec.principal rootSpec.keys rootSpec.payments W ∧
    TaskSat rootSpec.principal rootSpec.keys rootSpec.payments rootModel W

/-- The read-back always returns the independently computed record when it
returns anything: the producer can never make the two files "prove" a record
different from the one derived from I0. -/
theorem readBoth_returns_expected (doc : List DocLine) (js : List JsonRow)
    (p : Protected) (h : readBoth rootProtected doc js = some p) :
    p = rootProtected := by
  unfold readBoth at h
  cases hd : ofLines doc with
  | none => simp only [hd] at h; exact Option.noConfusion h
  | some d =>
      cases hj : ofJson js with
      | none => simp only [hd, hj] at h; exact Option.noConfusion h
      | some j =>
          simp only [hd, hj] at h
          cases hb : readBothCheck rootProtected d j with
          | false => simp only [hb] at h; exact Option.noConfusion h
          | true => simp only [hb] at h; exact (Option.some.inj h).symm

/-- The bundle acceptance predicate of the frozen formula. -/
def rootBundleAccepts (doc : List DocLine) (js : List JsonRow) : Bool :=
  (readBoth rootProtected doc js).isSome

/-- ROOT06 — the instantiated root: if the frozen input is well-formed and the
bundle check accepts the two actual artifacts, then there is a witness table W
that exactly covers the independent scenario domain Ω(I0), satisfies the
independent joint semantics and the independent task satisfaction of the frozen
Q, and whose protected record is exactly the joint read-back of both files. -/
theorem business_root_two_files (doc : List DocLine) (js : List JsonRow)
    (_hwf : root_wf.1 ∧ root_wf.2) (h : rootBundleAccepts doc js = true) :
    ∃ W : List Witness, RootObligations W ∧
      readBoth rootProtected doc js = some (protectedOf 1000 rootRowsCond [] rootModel) := by
  cases hr : readBoth rootProtected doc js with
  | none =>
      simp only [rootBundleAccepts, hr] at h
      exact Bool.noConfusion h
  | some p =>
      have hpe : p = rootProtected := readBoth_returns_expected doc js p hr
      subst hpe
      unfold RootObligations
      refine ⟨rootRows, ?_, ?_, ?_, hr⟩
      · exact root_worlds_match
      · exact root_joint_sem
      · exact root_task_sat

/-! ### Non-vacuity: the real artifacts pass, tampered ones do not -/

/-- The actually delivered artifact pair passes the bundle check. -/
theorem root_bundle_accepts_real :
    readBoth rootProtected (toLines rootDoc) (toJson rootJson) = some rootProtected := by
  decide

/-- ROOT02: the binding accepts exactly the selected input. -/
theorem root_binding_accepts_selected : CheckBinding rootInput rootInput = true := by
  decide

/-- ROOT02: a same-version parameter change (principal 1200 instead of 1000)
is refused as this selected input. -/
theorem root_binding_refuses_change :
    CheckBinding rootInput { rootInput with principal := 1200 } = false := by
  decide

/-- ROOT02: the changed parameter set remains a legitimate NEW task object. -/
theorem root_changed_is_new_task :
    (decodeInput (encodeInput { rootInput with principal := 1200 })).isSome = true := by
  decide

/-- Text tamper helper: replaces the first scenario row balance. -/
def swapDocBalance : List DocLine → ℚ → List DocLine
  | [], _ => []
  | DocLine.scenarioRow ct _ o :: rest, p => DocLine.scenarioRow ct p o :: rest
  | x :: rest, p => x :: swapDocBalance rest p

/-- Tampered text balance (JSON correct) is rejected. -/
theorem tampered_text_rejected :
    readBoth rootProtected (swapDocBalance (toLines rootDoc) 800) (toJson rootJson) = none := by
  decide

/-- JSON tamper helper: replaces the first weight row probability. -/
def swapJsonWeight : List JsonRow → ℚ → List JsonRow
  | [], _ => []
  | JsonRow.weightRow ct _ :: rest, p => JsonRow.weightRow ct p :: rest
  | x :: rest, p => x :: swapJsonWeight rest p

/-- Tampered JSON weight (7/16 instead of the exact 2/5) is rejected while the
text is correct. -/
theorem tampered_json_rejected :
    readBoth rootProtected (toLines rootDoc)
        (swapJsonWeight (toJson rootJson) (7 / 16)) = none := by
  decide

/-- Mixed snapshots: the text from a P=1200 input and the JSON from the frozen
P=1000 input are rejected — two source snapshots cannot be combined. -/
def mixedDoc : DocArt := { rootDoc with balT := 900, balF := 1200 }

theorem mixed_snapshots_rejected :
    readBoth rootProtected (toLines mixedDoc) (toJson rootJson) = none := by
  decide

/-- A same-version wholesale model replacement changes the expected record, so
the previously delivered artifacts no longer pass. -/
def swappedProtected : Protected := { rootProtected with expectedC := 910 }

theorem wholesale_swap_rejected :
    readBoth swappedProtected (toLines rootDoc) (toJson rootJson) = none := by
  decide

/-! ### Concrete numeric samples pinned for the Python cross-check -/

/-- Overpayment sample (P=100, q=300, p=2/5): E[C]=60, E[U]=80, E[R]=−20. -/
theorem overpay_sample :
    weighted (twoBranchWeights (2 / 5)) (fun w => cbal 100 300 w) = 60 ∧
    weighted (twoBranchWeights (2 / 5)) (fun w => cover 100 300 w) = 80 ∧
    weighted (twoBranchWeights (2 / 5)) (fun w => cres 100 300 w) = -20 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [weighted_twoBranch]
    show (2 / 5) * clipC (cres 100 300 [true]) + (1 - 2 / 5) * clipC (cres 100 300 [false]) = 60
    rw [cres_true_eq, cres_false_eq]
    simp only [clipC]
    rw [max_eq_right (by norm_num : (100:ℚ) - 300 ≤ 0), max_eq_left (by norm_num : (0:ℚ) ≤ 100)]
    norm_num
  · rw [weighted_twoBranch]
    show (2 / 5) * clipU (cres 100 300 [true]) + (1 - 2 / 5) * clipU (cres 100 300 [false]) = 80
    rw [cres_true_eq, cres_false_eq]
    simp only [cover, clipU]
    rw [max_eq_left (by norm_num : (0:ℚ) ≤ 200), max_eq_right (by norm_num : (-100:ℚ) ≤ 0)]
    norm_num
  · rw [weighted_twoBranch]
    show (2 / 5) * cres 100 300 [true] + (1 - 2 / 5) * cres 100 300 [false] = -20
    rw [cres_true_eq, cres_false_eq]
    norm_num

/-- Main sample: E[C]=880, threshold-800 event 3/5, interval [790, 930],
eligible grid member 850 only. -/
theorem main_sample :
    weighted (twoBranchWeights (2 / 5)) (fun w => cbal 1000 300 w) = 880 ∧
    eventMass (twoBranchWeights (2 / 5)) (fun w => cbal 1000 300 w) 800 = 3 / 5 ∧
    ((880 : ℚ) - 100 + 10 = 790 ∧ 880 + 60 - 10 = 930) ∧
    ([600, 850, 1100] : List ℚ).filter (fun x => decide ((790 : ℚ) ≤ x ∧ x ≤ 930)) = [850] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [weighted_twoBranch]
    show (2 / 5) * clipC (cres 1000 300 [true]) + (1 - 2 / 5) * clipC (cres 1000 300 [false]) = 880
    rw [cres_true_eq, cres_false_eq]
    simp only [clipC]
    rw [max_eq_left (by norm_num : (0:ℚ) ≤ 700), max_eq_left (by norm_num : (0:ℚ) ≤ 1000)]
    norm_num
  · rw [eventMass_twoBranch]
    show (if (800:ℚ) ≤ clipC (cres 1000 300 [true]) then 2 / 5 else 0)
        + (if (800:ℚ) ≤ clipC (cres 1000 300 [false]) then 1 - 2 / 5 else 0) = 3 / 5
    rw [cres_true_eq, cres_false_eq]
    simp only [clipC]
    rw [max_eq_right (by norm_num : (800:ℚ) - 300 ≤ 0), max_eq_left (by norm_num : (0:ℚ) ≤ 1000)]
    norm_num
  · norm_num
  · simp

end JurisLean.BusinessRoot
