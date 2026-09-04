import JurisLean.ULM08ArgumentConstruction

/-! Directed query refutation, typed attacks, and frozen defeat resolution. -/

namespace JurisLean.ULM

inductive AttackKind where
  | rebut
  | undermine
  | undercut
  | exceptionAttack
  | authorityAttack
  | scopeAttack
  | procedureAttack
deriving DecidableEq

structure TypedAttackV1 where
  attacker : CanonicalArgument
  target : CanonicalArgument
  kind : AttackKind
  witness : String
deriving DecidableEq

def AttackWF (a : TypedAttackV1) : Prop :=
  a.witness ≠ "" ∧ a.attacker.request = a.target.request

/-- A validated attack set has one request identity and prevents malformed
attacks from entering defeat resolution by construction. -/
structure ValidatedAttackSet where
  request : RequestKey
  attacks : Finset TypedAttackV1
  allWellFormed : ∀ a ∈ attacks, AttackWF a
  allRequestBound : ∀ a ∈ attacks, a.attacker.request = request

structure DefeatPolicy where
  succeeds : TypedAttackV1 → Bool

/-- Priority, authority, guard, and attack-kind policy are resolved before the
Dung layer receives its binary defeat graph. -/
def resolveDefeat
    (input : ValidatedAttackSet) (policy : DefeatPolicy) :
    Finset (CanonicalArgument × CanonicalArgument) :=
  (input.attacks.filter (fun a => policy.succeeds a = true)).image
    (fun a => (a.attacker, a.target))

theorem mem_resolveDefeat_iff
    {input : ValidatedAttackSet} {policy : DefeatPolicy}
    {x y : CanonicalArgument} :
    (x, y) ∈ resolveDefeat input policy ↔
      ∃ a ∈ input.attacks,
        policy.succeeds a = true ∧ a.attacker = x ∧ a.target = y := by
  classical
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨a, ha, hpair⟩
    rcases Finset.mem_filter.mp ha with ⟨hain, hpolicy⟩
    have hx : a.attacker = x := congrArg Prod.fst hpair
    have hy : a.target = y := congrArg Prod.snd hpair
    exact ⟨a, hain, hpolicy, hx, hy⟩
  · rintro ⟨a, hain, hpolicy, hx, hy⟩
    apply Finset.mem_image.mpr
    refine ⟨a, Finset.mem_filter.mpr ⟨hain, hpolicy⟩, ?_⟩
    simpa [hx, hy]

theorem resolved_defeat_has_wf_source
    {input : ValidatedAttackSet} {policy : DefeatPolicy}
    {x y : CanonicalArgument} (h : (x, y) ∈ resolveDefeat input policy) :
    ∃ a ∈ input.attacks,
      AttackWF a ∧ policy.succeeds a = true ∧
      a.attacker = x ∧ a.target = y := by
  rcases (mem_resolveDefeat_iff.mp h) with ⟨a, ha, hs, hx, hy⟩
  exact ⟨a, ha, input.allWellFormed a ha, hs, hx, hy⟩

theorem resolved_defeat_preserves_request
    {input : ValidatedAttackSet} {policy : DefeatPolicy}
    {x y : CanonicalArgument} (h : (x, y) ∈ resolveDefeat input policy) :
    x.request = input.request ∧ y.request = input.request := by
  rcases (mem_resolveDefeat_iff.mp h) with ⟨a, ha, _, hx, hy⟩
  have hatk : a.attacker.request = input.request := input.allRequestBound a ha
  have hsame : a.attacker.request = a.target.request :=
    (input.allWellFormed a ha).2
  have htgt : a.target.request = input.request := hsame.symm.trans hatk
  constructor
  · simpa [hx] using hatk
  · simpa [hy] using htgt

structure QueryRefutation where
  request : RequestKey
  refuter : JurisLean.LegalId .claim
  target : JurisLean.LegalId .claim
deriving DecidableEq

def QueryRefutation.WellFormed (r : QueryRefutation) : Prop :=
  r.refuter ≠ r.target

/-- Query refutation is directed, irreflexive, and request-scoped. Symmetry is a
separate property, not a global axiom. -/
def QueryRefutes
    (relations : Finset QueryRefutation) (request : RequestKey)
    (refuter target : JurisLean.LegalId .claim) : Prop :=
  ∃ r ∈ relations,
    r.request = request ∧ r.refuter = refuter ∧
      r.target = target ∧ r.WellFormed

def QueryContradictory
    (relations : Finset QueryRefutation) (request : RequestKey)
    (a b : JurisLean.LegalId .claim) : Prop :=
  QueryRefutes relations request a b ∧ QueryRefutes relations request b a

theorem queryRefutes_irreflexive
    (relations : Finset QueryRefutation) (request : RequestKey)
    (q : JurisLean.LegalId .claim) :
    ¬ QueryRefutes relations request q q := by
  intro h
  rcases h with ⟨r, _, _, href, htarget, hwf⟩
  exact hwf (href.trans htarget.symm)

theorem attack_witness_required {a : TypedAttackV1} (h : AttackWF a) :
    a.witness ≠ "" := h.1

theorem attack_preserves_request {a : TypedAttackV1} (h : AttackWF a) :
    a.attacker.request = a.target.request := h.2

end JurisLean.ULM
