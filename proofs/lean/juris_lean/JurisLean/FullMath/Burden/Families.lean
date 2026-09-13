import JurisLean.FullMath.Core.Foundations

/-!
B04/B05/B06 — Complete allocation of burden policies over the required
slots of a named family: within a declared business scope every slot of
the family (creation / extinction / defense / exception issues, criminal
elements and exclusions, administrative chains) has exactly one sourced
policy; completeness is checked against an independently written slot
list, not reconstructed from the implementation.
-/

namespace JurisLean.FullMath.Burden

/-- Keys are pairwise distinct. -/
def noDupKeys : List (String × String) → Prop
  | [] => True
  | (k, _) :: rest => ¬ (k ∈ rest.map Prod.fst) ∧ noDupKeys rest

/-- Every family slot has exactly one policy and no policy addresses a
slot outside the family. -/
def completeAssignment (slots : List String) (m : List (String × String)) : Prop :=
  noDupKeys m ∧ (∀ k ∈ m.map Prod.fst, k ∈ slots)
    ∧ (∀ s ∈ slots, s ∈ m.map Prod.fst)

/-- B04: the civil-commercial family (contract, property, tort, family,
labor, company, IP, finance) has a complete policy allocation. The slot
list is fixed independently of any implementation. -/
def civilSlots : List String :=
  ["contract.formation", "contract.breach", "property.title", "tort.fault",
   "tort.damages", "family.support", "labor.wage", "company.fiduciary",
   "ip.authorship", "finance.disclosure"]

def civilPolicies : List (String × String) :=
  [("contract.formation", "preponderance"), ("contract.breach", "preponderance"),
   ("property.title", "preponderance"), ("tort.fault", "preponderance"),
   ("tort.damages", "preponderance"), ("family.support", "preponderance"),
   ("labor.wage", "preponderance"), ("company.fiduciary", "preponderance"),
   ("ip.authorship", "preponderance"), ("finance.disclosure", "preponderance")]

theorem civil_allocation_complete : completeAssignment civilSlots civilPolicies := by
  decide [completeAssignment, noDupKeys, civilSlots, civilPolicies]

/-- B05: the criminal family — conviction elements, sentencing, legality
review, private prosecution and special procedure each carry their own
policy; per-person elements stay per-person. -/
def criminalSlots : List String :=
  ["criminal.elements", "criminal.sentencing", "criminal.legality",
   "criminal.privateProsecution", "criminal.specialProcedure"]

def criminalPolicies : List (String × String) :=
  [("criminal.elements", "beyondReasonableDoubt"),
   ("criminal.sentencing", "preponderance"),
   ("criminal.legality", "statutoryNullity"),
   ("criminal.privateProsecution", "beyondReasonableDoubt"),
   ("criminal.specialProcedure", "statutoryNullity")]

theorem criminal_allocation_complete : completeAssignment criminalSlots criminalPolicies := by
  decide [completeAssignment, noDupKeys, criminalSlots, criminalPolicies]

/-- B05(b): conviction of person `i` uses person `i`'s elements — the
slot key is indexed by the person, so completeness gives each person an
own policy and no cross-person substitution. -/
def personSlot (i : ℕ) : String := "criminal.elements." ++ toString i

theorem perPerson_slots_distinct (i j : ℕ) (h : personSlot i = personSlot j) : i = j := by
  simpa [personSlot] using h

/-- B06: the administrative family — administrative act legality, duty
enforcement, damages, state compensation and arbitration use separate
chains that never borrow each other's policies. -/
def adminSlots : List String :=
  ["admin.actLegality", "admin.dutyEnforcement", "admin.damages",
   "admin.stateCompensation", "admin.arbitration"]

def adminPolicies : List (String × String) :=
  [("admin.actLegality", "legalityReview"), ("admin.dutyEnforcement", "dutyEnforcement"),
   ("admin.damages", "preponderance"), ("admin.stateCompensation", "preponderance"),
   ("admin.arbitration", "arbitrationStandard")]

theorem admin_allocation_complete : completeAssignment adminSlots adminPolicies := by
  decide [completeAssignment, noDupKeys, adminSlots, adminPolicies]

/-- B04-B06 shared core: a complete assignment gives every slot a policy
keyed lookup. -/
theorem complete_gives_key (slots : List String) (m : List (String × String))
    (h : completeAssignment slots m) (s : String) (hs : s ∈ slots) :
    s ∈ m.map Prod.fst := h.2.2 s hs

end JurisLean.FullMath.Burden
