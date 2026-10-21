import JurisLean.Candidates.Final20261021.Interfaces

namespace JurisLean.Candidates.Final20261021.EvidenceProcedure

structure EvidenceItem where
  source : SourceRef
  query : Nat
  admissibility : Applicable
  credibleUnderPolicy : Bool
  supports : Bool
  deriving DecidableEq, Repr

def usable (q : Nat) (e : EvidenceItem) : Bool :=
  decide (e.query = q ∧ e.admissibility = .yes ∧ e.credibleUnderPolicy = true)

def classify (support opposition : Bool) : Judgment :=
  match support, opposition with
  | true, false => .supported
  | false, true => .opposed
  | true, true => .incompatible
  | false, false => .insufficient

theorem u08_3_evidence_four_states (a b : Bool) :
    (classify a b = .supported ↔ a = true ∧ b = false) ∧
    (classify a b = .opposed ↔ a = false ∧ b = true) ∧
    (classify a b = .incompatible ↔ a = true ∧ b = true) ∧
    (classify a b = .insufficient ↔ a = false ∧ b = false) := by
  cases a <;> cases b <;> decide

def judgment (q : Nat) (items : List EvidenceItem) : Judgment :=
  classify (items.any fun e => usable q e && e.supports)
    (items.any fun e => usable q e && !e.supports)

def Truth (q : Nat) (world : Nat → Bool) : Bool := world q

structure Opportunity where
  id : Nat
  rank : Nat
  executedReceipt : Option SourceRef
  waivedBy : Option SourceRef
  dependencies : List Nat
  deriving DecidableEq, Repr

structure ProcessInput where
  required : List Nat
  policyDomain : List Nat
  records : List Opportunity
  -- These registries are external, versioned premises, not statutory truth.
  validExecutionReceipts : List SourceRef
  validWaivers : List SourceRef
  closureAuthority : Option SourceRef
  validClosureAuthorities : List SourceRef
  blocked : Bool
  deriving DecidableEq, Repr

def terminal (p : ProcessInput) (id : Nat) : Bool :=
  p.records.any fun o => decide (o.id = id) &&
    ((o.executedReceipt.any fun r => decide (r ∈ p.validExecutionReceipts)) ||
     (o.waivedBy.any fun r => decide (r ∈ p.validWaivers))) &&
    o.dependencies.all (fun d => p.records.any fun dep =>
      decide (dep.id = d ∧ d ∈ p.policyDomain ∧ dep.rank < o.rank) &&
      ((dep.executedReceipt.any fun r => decide (r ∈ p.validExecutionReceipts)) ||
       (dep.waivedBy.any fun r => decide (r ∈ p.validWaivers))))

def covered (p : ProcessInput) : Bool := p.required.all (fun o => decide (o ∈ p.policyDomain))
def exhausted (p : ProcessInput) : Bool := p.policyDomain.all (terminal p)

def procedure (p : ProcessInput) : Procedure :=
  if covered p && exhausted p &&
    decide ((p.records.map (·.id)).Nodup) &&
    p.closureAuthority.any (fun r => decide (r ∈ p.validClosureAuthorities)) then .closedLawfully
  else if p.blocked then .blocked else .open

theorem necessary_exhausted (p : ProcessInput) (hc : covered p = true)
    (he : exhausted p = true) : ∀ o ∈ p.required, terminal p o = true := by
  have coverage : ∀ o ∈ p.required, o ∈ p.policyDomain := by
    simpa [covered, List.all_eq_true] using hc
  have done : ∀ o ∈ p.policyDomain, terminal p o = true := by
    simpa [exhausted, List.all_eq_true] using he
  exact fun o ho => done o (coverage o ho)

def proposed_judgment_and_process (q : Nat) (es : List EvidenceItem) (p : ProcessInput) :=
  (judgment q es, procedure p)

def forgedEvidence : EvidenceItem := ⟨⟨1⟩, 0, .yes, true, true⟩

theorem u08_3_judgment_not_truth :
    judgment 0 [forgedEvidence] = .supported ∧ Truth 0 (fun _ => false) = false := by
  decide

theorem u08_3_opposition_does_not_erase_support :
    judgment 0 [forgedEvidence, { forgedEvidence with supports := false }] = .incompatible := by
  decide

end JurisLean.Candidates.Final20261021.EvidenceProcedure
