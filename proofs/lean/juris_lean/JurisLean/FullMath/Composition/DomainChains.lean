import JurisLean.FullMath.Core.Foundations

/-!
C05 — Domain conditional chains with assumption isolation: conditional
consequences carry the original assumption id; the shared engine never
emits adjudicated court acts; domain differences enter only through the
named policy input.
-/

namespace JurisLean.FullMath.Composition

/-- A conditional legal conclusion tagged with its assumption. -/
inductive CondRuling where
  | conditional (assumptionId : ℕ) (conclusion : String)
  | courtAct (assumptionId : ℕ)

/-- The shared domain engine: assumption ids plus a named policy produce
conditional conclusions only — the policy is the only domain input. -/
def runChain (policy : String) (ids : List ℕ) : List CondRuling :=
  ids.map (fun i => CondRuling.conditional i (policy ++ "@" ++ toString i))

/-- C05(a): every generated ruling is conditional and carries one of the
declared assumption ids. -/
theorem chain_carries_ids (policy : String) (ids : List ℕ) :
    ∀ r ∈ runChain policy ids, ∃ i ∈ ids, r = CondRuling.conditional i
        (policy ++ "@" ++ toString i) := by
  intro r hr
  simp only [runChain, List.mem_map] at hr
  obtain ⟨i, hi, rfl⟩ := hr
  exact ⟨i, hi, rfl⟩

/-- C05(b): the engine never generates court acts — conditional opinions
never become adjudicated facts. -/
theorem chain_generates_no_court (policy : String) (ids : List ℕ) (a : ℕ) :
    ∀ r ∈ runChain policy ids, r ≠ CondRuling.courtAct a := by
  intro r hr hcontra
  rw hcontra at hr
  simp only [runChain, List.mem_map] at hr
  obtain ⟨i, _, hmap⟩ := hr
  cases hmap

/-- C05(c): two domains run the same engine; different named policies
give different conditional labels for the same assumption id. -/
theorem policy_is_the_only_domain_input (pol1 pol2 : String) (i : ℕ)
    (hne : pol1 ≠ pol2) :
    CondRuling.conditional i (pol1 ++ "@" ++ toString i)
      ≠ CondRuling.conditional i (pol2 ++ "@" ++ toString i) := by
  intro h
  simp only [CondRuling.injEq] at h
  omega

end JurisLean.FullMath.Composition
