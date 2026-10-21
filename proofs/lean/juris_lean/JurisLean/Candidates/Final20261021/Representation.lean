import JurisLean.Candidates.Final20261021.Interfaces

namespace JurisLean.Candidates.Final20261021.Representation

theorem u07_1_retraction_injective {A B : Type} (e : A → B) (d : B → A)
    (roundtrip : ∀ a, d (e a) = a) : Function.Injective e := by
  intro a b h
  calc a = d (e a) := (roundtrip a).symm
       _ = d (e b) := congrArg d h
       _ = b := roundtrip b

theorem u07_1_section_surjective {A B : Type} (e : A → B) (d : B → A)
    (roundtrip : ∀ a, d (e a) = a) : Function.Surjective d := by
  intro a
  exact ⟨e a, roundtrip a⟩

theorem u07_1_rho_idempotent {A B : Type} (e : A → B) (d : B → A)
    (roundtrip : ∀ a, d (e a) = a) (b : B) : e (d (e (d b))) = e (d b) :=
  congrArg e (roundtrip (d b))

def Separates {A O V : Type} (family : O → Prop) (read : O → A → V) : Prop :=
  ∀ a b, (∀ o, family o → read o a = read o b) → a = b

theorem u07_1_separation_monotone {A O V : Type} (small large : O → Prop)
    (read : O → A → V) (included : ∀ o, small o → large o)
    (h : Separates small read) : Separates large read := by
  intro a b same
  exact h a b (fun o ho => same o (included o ho))

theorem u07_2_common_fiber_nonempty {I B : Type} [Fintype I]
    (W : I → Type) (projection : (i : I) → W i → B)
    (b : B) (localWitness : ∀ i, ∃ w, projection i w = b) :
    ∃ ws : (i : I) → W i, ∀ i, projection i (ws i) = b := by
  classical
  exact ⟨fun i => Classical.choose (localWitness i),
    fun i => Classical.choose_spec (localWitness i)⟩

theorem n07_2_incompatible_fiber : ¬ ∃ b : Bool, false = b ∧ true = b := by decide

-- This finite view retains each consumed payload and history position.
inductive HistoryEvent where
  | formation (relation : RelationId)
  | performance (payload : PaymentPayload)
  deriving DecidableEq, Repr

structure SourceView where
  gamma : Gamma
  history : List HistoryEvent
  objectMap : List (SourceRef × ObjectId)
  observedRef : SourceRef
  observedRelation : RelationId
  deriving DecidableEq, Repr

structure PaymentRow where
  payload : PaymentPayload
  annotation : String
  deriving DecidableEq, Repr

def proposed_source_view (v : SourceView) : Result SourceView :=
  match v.objectMap.filter (fun x => x.1 == v.observedRef) with
  | [(_, .relation r)] =>
      if r = v.observedRelation then .known v
      else .rejected .observationBindingMismatch
  | [] => .unknown .identityUnknown
  | _ => .conflict 0 1

def selectedPayload (v : SourceView) (j : Nat) : Option PaymentPayload :=
  match v.history[j]? with
  | some (.performance p) =>
      if p.caseId = v.gamma.caseId ∧ p.caseRevision = v.gamma.caseRevision
        ∧ p.relation = v.observedRelation then some p else none
  | _ => none

-- Section 17.2: copy from the fixed history constructor, not from an
-- independently supplied row whose equality to another row is assumed.
def proposed_binding (v : SourceView) (j : Nat) (note : String) : Option PaymentRow :=
  (selectedPayload v j).map (fun p => ⟨p, note⟩)

theorem u07_3_projection_unique_under_fixed_binding
    (v : SourceView) (j : Nat) (n1 n2 : String) (r1 r2 : PaymentRow)
    (h1 : proposed_binding v j n1 = some r1)
    (h2 : proposed_binding v j n2 = some r2) : r1.payload = r2.payload := by
  cases hs : selectedPayload v j with
  | none => simp [proposed_binding, hs] at h1
  | some p =>
      simp only [proposed_binding, hs, Option.map_some, Option.some.injEq] at h1 h2
      cases h1
      cases h2
      rfl

def proposed_common_model (v : SourceView) (j : Nat) : Result PaymentPayload :=
  match proposed_source_view v with
  | .known checked =>
      match proposed_binding checked j "history projection" with
      | some row => .known row.payload
      | none => .unknown .identityUnknown
  | .unknown e => .unknown e
  | .rejected e => .rejected e
  | .conflict l r => .conflict l r

-- mu is partial: two unresolved references are not thereby the same object.
def InterpretedSame (mu : SourceRef → Option ObjectId) (a b : SourceRef) : Prop :=
  ∃ obj, mu a = some obj ∧ mu b = some obj

theorem unknown_not_an_identity (mu : SourceRef → Option ObjectId) (a b : SourceRef)
    (ha : mu a = none) : ¬ InterpretedSame mu a b := by
  rintro ⟨obj, h, _⟩
  rw [ha] at h
  cases h

end JurisLean.Candidates.Final20261021.Representation
