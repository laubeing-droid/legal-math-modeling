import JurisLean.CN.Completion20261105.Ready

/-!
C5/A10/B8: full prerequisites of this represented legal-step entry, derived
from its actual success, rather than just the epistemic Ready fragment.
Authorization includes the exact actor/action/scope/version/time/role check;
requestGate checks the effect and source, and current admitted dependencies are
evaluated by the registered method. No prepared Ready ticket is accepted.
Natural truth is not identified with the legal proof-policy assessment.
-/
namespace JurisLean.CN.Completion20261105
open JurisLean.KernelV3
open JurisLean.CN.Revision20261101

def OperationalPre (s : Situation) (r : Request) (p : ProofPolicy) (m : Mode)
    (law : Rule) (t : IssuedTemplate) : Prop :=
  automationAllowed s.core.state r.scope m ≠ false ∧
  authorized s.core.state.N r ≠ false ∧
  (activeConflict s r.scope).isSome ≠ true ∧
  selectedRules s.core r = [law] ∧ selectedTemplates s law = [t] ∧
  requestGate s.core r law p ≠ false ∧ Ready s law t p

def LegalPreAt (s : Situation) (r : Request) (p : ProofPolicy) (m : Mode)
    (law : Rule) (t : IssuedTemplate) (w : PossibleWorld) : Prop :=
  legalCompatible s w ∧ OperationalPre s r p m law t

theorem checkedLaw_request_passes (s : Situation) (r : Request) (p : ProofPolicy)
    (law : Rule) (t : IssuedTemplate) (w : PossibleWorld)
    (h : (checkedLaw s r law p w t).answer = .success ()) :
    requestGate s.core r law p ≠ false := by
  intro bad
  simp [checkedLaw,bad,quiet] at h

/- The success branch supplies all checks. The template membership required
   by checkedLaw_ready is obtained from actual unique selection here. -/
theorem legal_success_operational_pre (s : Situation) (r : Request) (p : ProofPolicy)
    (m : Mode) (w : PossibleWorld)
    (h : (legalDispatch s r p m w).answer = .success ()) :
    ∃ law t, OperationalPre s r p m law t := by
  unfold legalDispatch at h
  split at h
  · cases h
  · rename_i hm
    split at h
    · cases h
    · rename_i ha
      split at h
      · cases h
      · rename_i hc
        cases hs : selectedRules s.core r with
        | nil => simp [hs,quiet] at h
        | cons law rest =>
          cases rest with
          | cons other tail => simp [hs,quiet] at h
          | nil =>
            simp only [hs] at h
            cases ht : selectedTemplates s law with
            | nil => simp [ht,quiet] at h
            | cons t rest =>
              cases rest with
              | cons other tail => simp [ht,quiet] at h
              | nil =>
                simp only [ht] at h
                refine ⟨law,t,hm,ha,hc,hs,ht,checkedLaw_request_passes s r p law t w h,?_⟩
                exact checkedLaw_ready s r law p w t (by rw [ht]; simp) h

/- B8 non-vacuity and universal operational prerequisite reliability, on
   supported legal states. Unobserved natural truth may vary; method approval,
   current materials and authority are shared legal-state projections. -/
theorem legal_success_ready_contract (s : Situation) (r : Request) (p : ProofPolicy)
    (m : Mode) (w : PossibleWorld)
    (h : (legalDispatch s r p m w).answer = .success ()) :
    ∃ law t, (∃ z, legalCompatible s z) ∧
      ∀ z, legalCompatible s z → LegalPreAt s r p m law t z := by
  obtain ⟨law,t,hp⟩ := legal_success_operational_pre s r p m w h
  exact ⟨law,t,hp.2.2.2.2.2.2.1,fun z hz => ⟨hz,hp⟩⟩

theorem no_authority_no_legal_change (s : Situation) (r : Request) (p : ProofPolicy)
    (m : Mode) (w : PossibleWorld) (h : authorized s.core.state.N r = false) :
    (legalDispatch s r p m w).after = s := by
  by_cases hg : automationAllowed s.core.state r.scope m = false <;>
    simp [legalDispatch,hg,h,quiet]

#print axioms checkedLaw_request_passes
#print axioms legal_success_operational_pre
#print axioms legal_success_ready_contract
#print axioms no_authority_no_legal_change
end JurisLean.CN.Completion20261105
