import JurisLean.UnifiedV21.Context

namespace JurisLean.ULM.UnifiedV21

inductive EvidenceClass where
  | localRecord
  | synthetic
  | institutionalSourceVerified
  deriving DecidableEq

structure HostRecord where
  context : ContextKey
  content : String
  use : String
  evidenceClass : EvidenceClass
  revoked : Bool
  intervalValid : Bool
  deriving DecidableEq

/-- Record existence/verification is provided by the existing host boundary;
this model does not authenticate a court or prove the contents of a judgment. -/
def CanProjectInstitution (record : HostRecord) (context : ContextKey)
    (content : String) : Prop :=
  record.context = context ∧ record.content = content ∧
  record.use = "institutional_finding" ∧
  record.evidenceClass = .institutionalSourceVerified ∧
  record.revoked = false ∧ record.intervalValid = true

theorem local_record_not_external (r : HostRecord) (c : ContextKey) (s : String)
    (h : r.evidenceClass = .localRecord) : ¬ CanProjectInstitution r c s := by
  intro hc
  have he := hc.2.2.2.1
  rw [h] at he
  cases he

theorem synthetic_record_not_external (r : HostRecord) (c : ContextKey) (s : String)
    (h : r.evidenceClass = .synthetic) : ¬ CanProjectInstitution r c s := by
  intro hc
  have he := hc.2.2.2.1
  rw [h] at he
  cases he

theorem institution_projection_preserves_subject {r : HostRecord} {c : ContextKey}
    {s : String} (h : CanProjectInstitution r c s) : r.context = c := h.1

end JurisLean.ULM.UnifiedV21
