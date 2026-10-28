import JurisLean.Candidates.PolicyResponse20261027

namespace JurisLean.Candidates.U12_4FrozenAuditModel20261029

open JurisLean.Candidates.PolicyResponse20261027

def auditMass (p : ℝ) (v : Bool) : ℝ := if v = true then p else 1 - p

def auditRate (pE pG : ℝ) (b : Fin 3) : ℝ := if b = 1 then pE else pG

def auditReward (b : Fin 3) (v : Bool) : ℝ :=
  if preparationScore b = 1 ∧ v = true then 1 else 0

-- The zero action never passes, so its unused audit law is not assigned.
def auditedUtility (pE pG : ℝ) (b : Fin 3) : ℝ :=
  if b = 0 then -(preparationCost b : ℝ)
  else ∑ v : Bool, auditMass (auditRate pE pG b) v *
    (auditReward b v - (preparationCost b : ℝ))

-- Frozen U12.4: fixed actions, scores, costs, unit reward, binary audit.
-- Probability normalization and computed payoffs precede the reused iff.
theorem frozen_audit_model_acceptance (pE pG : ℝ)
    (hE : 0 ≤ pE ∧ pE ≤ 1) (hG : 0 ≤ pG ∧ pG ≤ 1) :
    (∀ v, auditReward 0 v = 0) ∧
    (∀ b : Fin 3, b ≠ 0 →
      (∀ v, 0 ≤ auditMass (auditRate pE pG b) v) ∧
      (∑ v : Bool, auditMass (auditRate pE pG b) v) = 1) ∧
    auditedUtility pE pG 0 = 0 ∧
    auditedUtility pE pG 1 = pE - 3/5 ∧
    auditedUtility pE pG 2 = pG - 1/10 ∧
    ((∀ b : Fin 3, b ≠ 1 → auditedUtility pE pG b < auditedUtility pE pG 1) ↔
      (1/2 < pE - pG ∧ 3/5 < pE)) := by
  have univ : (Finset.univ : Finset Bool) = {false, true} := by decide
  have noReward : ∀ v, auditReward 0 v = 0 := by
    intro v
    cases v <;> norm_num [auditReward, preparationScore]
  have normalized : ∀ b : Fin 3, b ≠ 0 →
      (∀ v, 0 ≤ auditMass (auditRate pE pG b) v) ∧
      (∑ v : Bool, auditMass (auditRate pE pG b) v) = 1 := by
    intro b hb
    have hp : 0 ≤ auditRate pE pG b ∧ auditRate pE pG b ≤ 1 := by
      by_cases he : b = 1
      · simpa [auditRate, he] using hE
      · simpa [auditRate, he] using hG
    constructor
    · intro v
      cases v <;> simp [auditMass] <;> linarith [hp.1, hp.2]
    · simp [auditMass, univ]
  have payoff0 : auditedUtility pE pG 0 = 0 := by
    norm_num [auditedUtility, preparationCost]
  have payoffE : auditedUtility pE pG 1 = pE - 3/5 := by
    norm_num [auditedUtility, auditRate, auditMass, auditReward, univ,
      preparationScore, preparationCost, Fin.ext_iff] <;> ring
  have payoffG : auditedUtility pE pG 2 = pG - 1/10 := by
    norm_num [auditedUtility, auditRate, auditMass, auditReward, univ,
      preparationScore, preparationCost, Fin.ext_iff] <;> ring
  refine ⟨noReward, normalized, payoff0, payoffE, payoffG, ?_⟩
  have comparison :
      (∀ b : Fin 3, b ≠ 1 → auditedUtility pE pG b < auditedUtility pE pG 1) ↔
      (pG - 1/10 < pE - 3/5 ∧ 0 < pE - 3/5) := by
    constructor
    · intro best
      constructor
      · simpa only [payoffG, payoffE] using best 2 (by decide)
      · simpa only [payoff0, payoffE] using best 0 (by decide)
    · rintro ⟨betterG, better0⟩ b hb
      fin_cases b
      · change auditedUtility pE pG (0 : Fin 3) < auditedUtility pE pG (1 : Fin 3)
        rw [payoff0, payoffE]
        exact better0
      · exact (hb rfl).elim
      · change auditedUtility pE pG (2 : Fin 3) < auditedUtility pE pG (1 : Fin 3)
        rw [payoffG, payoffE]
        exact betterG
  exact comparison.trans
    (JurisLean.Candidates.Final20261021.Policy.u12_4_signal_vs_incentive pE pG)

example : auditedUtility (3/5) (1/2) 1 = 0 ∧
    auditedUtility (3/5) (1/2) 2 = 2/5 := by
  have accepted := frozen_audit_model_acceptance (3/5) (1/2) (by norm_num) (by norm_num)
  have effort := accepted.2.2.2.1
  have gaming := accepted.2.2.2.2.1
  norm_num at effort gaming
  exact ⟨effort, gaming⟩

example : auditedUtility 1 0 1 = 2/5 ∧ auditedUtility 1 0 2 = -(1/10) := by
  have accepted := frozen_audit_model_acceptance 1 0 (by norm_num) (by norm_num)
  have effort := accepted.2.2.2.1
  have gaming := accepted.2.2.2.2.1
  norm_num at effort gaming
  exact ⟨effort, gaming⟩

end JurisLean.Candidates.U12_4FrozenAuditModel20261029

#check JurisLean.Candidates.Final20261021.Policy.u12_4_signal_vs_incentive
#print axioms JurisLean.Candidates.Final20261021.Policy.u12_4_signal_vs_incentive
#check JurisLean.Candidates.Final20261021.Policy.distinguishable_signal_insufficient
#print axioms JurisLean.Candidates.Final20261021.Policy.distinguishable_signal_insufficient
#check JurisLean.Candidates.PolicyResponse20261027.finite_response_payoffs
#print axioms JurisLean.Candidates.PolicyResponse20261027.finite_response_payoffs
#check JurisLean.Candidates.PolicyResponse20261027.score_only_cannot_distinguish_preparation
#print axioms JurisLean.Candidates.PolicyResponse20261027.score_only_cannot_distinguish_preparation
#check JurisLean.Candidates.U12_4FrozenAuditModel20261029.frozen_audit_model_acceptance
#print axioms JurisLean.Candidates.U12_4FrozenAuditModel20261029.frozen_audit_model_acceptance
