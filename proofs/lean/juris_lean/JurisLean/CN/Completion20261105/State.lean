import JurisLean.CN.Completion20261105.Foundation
import JurisLean.CN.Completion20261105.InstitutionRules
import JurisLean.CN.Completion20261105.PolicyIR
import JurisLean.CN.Completion20261105.EngineTypes

/-!
Common object used by institution commands, operator programs and runtime.
The dated extension adds institution-indexed legal positions; there is one
underlying F/E/N/L/A/ledger, exposed by core.state, not a second fact system.
V4 P1/P4/P12 require stateful instances and ordered, composable histories.
-/
namespace JurisLean.CN.Completion20261105
open JurisLean.KernelV3
open JurisLean.CN.Revision20261101
namespace IR
export InstitutionRules (ExecProc InterestClaim InterestLedger Participation RevokeGuard
  ApparentGuard FourOut CompTrack)
end IR

def CaseState.putState (x : CaseState) (s : Sit) (h : s.E = x.state.E) : CaseState :=
  ⟨s, x.keys, by intro i hi; rw [h]; exact x.closed i hi⟩

def CaseState.setCell (x : CaseState) (i : Ref .material) (cell : EvidenceCell i) : CaseState :=
  ⟨{x.state with E := setEvidence x.state.E i cell}, i :: x.keys, by
    intro j hj
    have hn : j ≠ i ∧ j ∉ x.keys := by simpa using hj
    simp only [setEvidence, hn.1, dite_false]
    exact x.closed j hn.2⟩

structure IssuedTemplate where
  request : Request
  body : ProofTemplate

inductive InstitutionKind
  | lifecycle | agency | jurisdiction | evidence | acquisition | offense | bankruptcy
  | compensation (kind : CompensationKind) | rights | interpretation | resJudicata | proposal
  deriving DecidableEq, Repr

structure InstitutionPermit where
  source : NormRef
  scope : Scope
  kind : InstitutionKind

structure Situation where
  core : CaseState
  life : Ref .object → Option CivilActLife
  agencies : Ref .object → Option Agency
  meanings : Ref .object → Option Formula
  executions : List IR.ExecProc
  stayed : List (Ref .event)
  interest : Ref .relation → Option IR.InterestLedger
  cutoffs : Ref .relation → Option Nat
  tracks : LiabilityTracks
  paused : List Scope
  actRelations : Ref .object → List (Ref .relation)
  choices : Scope → Option (Ref .relation)
  templates : List IssuedTemplate
  accounts : Ref .relation → Option JurisLean.Candidates.Final20261021.Ledger.State
  engineInputs : List EngineMaterial
  uses : List InstitutionPermit
  bankruptcyCases : Ref .actor → Option Nat
  disputes : List (Scope × ConflictKind)
  participations : List IR.Participation

def Situation.initial : Situation :=
  ⟨initialCase, fun _ => none, fun _ => none, fun _ => none, [], [],
    fun _ => none, fun _ => none, ⟨[], [], [], []⟩, [],
    fun _ => [], fun _ => none, [], fun _ => none, [], [], fun _ => none, [], []⟩

def activeConflict (s : Situation) (scope : Scope) : Option ReviewRoute :=
  match ((s.disputes.filter (fun d => d.1 == scope)).map (fun d => reviewRoute d.2)).eraseDups with
  | [] => none
  | [route] => some route
  | _ :: _ :: _ => some .competentReview

def institutionAllowed (s : Situation) (r : Request) (kind : InstitutionKind) : Bool :=
  s.uses.any (fun u => u.kind == kind && u.source.id == r.rule &&
    u.source.version == r.version && u.scope == r.scope &&
    s.core.state.N.rules.any (fun law => law.source.id == u.source.id &&
      law.source.version == u.source.version && law.source.source == u.source.source && law.scope == u.scope))

def Situation.withCore (s : Situation) (x : CaseState) : Situation := {s with core := x}

def assign {α : Type} (m : Ref .object → α) (key : Ref .object) (value : α) :
    Ref .object → α :=
  fun j => if j = key then value else m j

/- Obligation P12: a concrete keyed update has the claimed scope; this is used
   by actual lifecycle, agency and interpretation commands, not a label test. -/
theorem assign_self {α : Type} (m : Ref .object → α) (k : Ref .object) (v : α) :
    assign m k v k = v := by simp [assign]

theorem assign_other {α : Type} (m : Ref .object → α) (a b : Ref .object) (v : α)
    (h : b ≠ a) : assign m a v b = m b := by simp [assign, h]

inductive Refusal
  | unauthorized | prerequisites | unsupported
  deriving DecidableEq, Repr

inductive Answer (α : Type)
  | success (value : α)
  | rejected (why : Refusal)
  | unknown (why : UnknownKind)
  | conflict (route : ReviewRoute)
  | blockedHuman
  deriving DecidableEq, Repr

structure Reply (α : Type) where
  after : Situation
  answer : Answer α

def ruleIdentityMatches (r : Request) (law : Rule) : Bool :=
  law.source.id == r.rule && law.source.version == r.version && law.scope == r.scope

def selectedRules (x : CaseState) (r : Request) : List Rule :=
  x.state.N.rules.filter (ruleIdentityMatches r)

def statusAnswer : StepStatus → Answer Unit
  | .applied => .success ()
  | .unauthorized => .rejected .unauthorized
  | .blockedHuman => .blockedHuman
  | .awaiting k => .unknown k

/- The public legal dispatcher obtains its law from N. No caller can pass an
   unregistered rule or assume a unique applicable norm in a ticket. -/
def fragmentDispatch (s : Situation) (r : Request) (p : ProofPolicy)
    (m : Mode) (w : PossibleWorld) : Reply Unit :=
  if automationAllowed s.core.state r.scope m = false then ⟨s, .blockedHuman⟩
  else
  match selectedRules s.core r with
  | [] => ⟨s, .unknown .inputUnchecked⟩
  | [law] =>
    let ex := executeChecked s.core r law p m w
    ⟨s.withCore (s.core.putState ex.after (executeChecked_frame s.core r law p m w).2.2),
      statusAnswer ex.status⟩
  | _ :: _ :: _ => ⟨s, .conflict .competentReview⟩

/- Obligation F01/F02/S1: the actual selected rule is in N, and unresolved
   alternatives return conflict without a state change. -/
theorem selected_rule_member (x : CaseState) (r : Request) (law : Rule)
    (h : selectedRules x r = [law]) : law ∈ x.state.N.rules := by
  have hm : law ∈ selectedRules x r := by rw [h]; simp
  exact (List.mem_filter.mp hm).1

theorem fragmentDispatch_conflict (s : Situation) (r : Request) (p : ProofPolicy)
    (m : Mode) (w : PossibleWorld) (a b : Rule) (rest : List Rule)
    (h : selectedRules s.core r = a :: b :: rest) :
    (fragmentDispatch s r p m w).after = s ∧
      (fragmentDispatch s r p m w).answer =
        (if automationAllowed s.core.state r.scope m = false then .blockedHuman
          else .conflict .competentReview) := by
  by_cases hm : automationAllowed s.core.state r.scope m = false <;>
    simp [fragmentDispatch, h, hm]

theorem fragmentDispatch_missing (s : Situation) (r : Request) (p : ProofPolicy)
    (m : Mode) (w : PossibleWorld) (h : selectedRules s.core r = []) :
    (fragmentDispatch s r p m w).answer =
      (if automationAllowed s.core.state r.scope m = false then .blockedHuman
        else .unknown .inputUnchecked) := by
  by_cases hm : automationAllowed s.core.state r.scope m = false <;>
    simp [fragmentDispatch, h, hm]

/- S4 has priority even when no rule or several rules are selected. This
   corrects the initial local dispatcher's ordering, not a frozen theorem. -/
theorem fragmentDispatch_refused (s : Situation) (r : Request) (p : ProofPolicy)
    (w : PossibleWorld) (h : s.core.state.refusals.contains r.scope = true) :
    (fragmentDispatch s r p .automated w).answer = .blockedHuman := by
  have hg : automationAllowed s.core.state r.scope .automated = false := by
    simp only [automationAllowed, h, Bool.not_true]
  simp [fragmentDispatch, hg]

def quiet (s : Situation) {α : Type} (a : Answer α) : Reply α := ⟨s, a⟩

/- State coherence is preserved when a new cell is recorded at any material
   key. Admission permission is checked by the command, not by this helper. -/
theorem setCell_closed (x : CaseState) (i j : Ref .material) (c : EvidenceCell i)
    (h : j ∉ (x.setCell i c).keys) :
    (x.setCell i c).state.E j = .absent :=
  (x.setCell i c).closed j h

theorem fragmentDispatch_success_ready (s : Situation) (r : Request) (p : ProofPolicy)
    (m : Mode) (w : PossibleWorld)
    (h : (fragmentDispatch s r p m w).answer = .success ()) :
    ∃ law, law ∈ s.core.state.N.rules ∧ SemanticReady s.core law := by
  by_cases hg : automationAllowed s.core.state r.scope m = false
  · simp [fragmentDispatch, hg] at h
  ·
   cases hs : selectedRules s.core r with
   | nil => simp [fragmentDispatch, hs, hg] at h
   | cons law rest =>
     cases rest with
     | nil =>
       have ha : (executeChecked s.core r law p m w).status = .applied := by
         cases he : (executeChecked s.core r law p m w).status <;>
           simp_all [fragmentDispatch, statusAnswer]
       exact ⟨law, selected_rule_member s.core r law hs,
         executeChecked_ready s.core r law p m w ha⟩
     | cons b tail => simp [fragmentDispatch, hs, hg] at h

#print axioms assign_self
#print axioms assign_other
#print axioms selected_rule_member
#print axioms fragmentDispatch_conflict
#print axioms fragmentDispatch_missing
#print axioms fragmentDispatch_refused
#print axioms setCell_closed
#print axioms fragmentDispatch_success_ready

end JurisLean.CN.Completion20261105

