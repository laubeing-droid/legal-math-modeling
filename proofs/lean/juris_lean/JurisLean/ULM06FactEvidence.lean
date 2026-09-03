import JurisLean.ULM05Machine
import JurisLean.FactAdmissionSpec

/-! Fact, evidence, assumption, and strict-premise separation. -/

namespace JurisLean.ULM

inductive Establishment where
  | established
  | notEstablished
  | undetermined
deriving DecidableEq, Repr

inductive ContestStatus where
  | uncontested
  | contested
  | resolved
deriving DecidableEq, Repr

inductive PremisePermission where
  | strictPremise
  | argumentOnly
  | prohibited
deriving DecidableEq, Repr

structure FactAssessment where
  fact : JurisLean.LegalId .fact
  establishment : Establishment
  contest : ContestStatus
  permission : PremisePermission
  request : RequestKey
deriving DecidableEq, Repr

structure EvidenceToken where
  evidenceId : String
  fact : JurisLean.LegalId .fact
  source : JurisLean.SourceLocator
  request : RequestKey
deriving DecidableEq, Repr

structure AssumptionWitness where
  assumptionId : String
  fact : JurisLean.LegalId .fact
  request : RequestKey
  scope : String
deriving DecidableEq, Repr

/-- Reuse the repository's formal fact-attestation object for unconditional
premises; assumptions remain a different constructor. -/
inductive PremiseOrigin where
  | admitted (attestation : JurisLean.FactAdmissionAttestation)
  | assumed (witness : AssumptionWitness)
deriving DecidableEq

structure PremiseToken where
  fact : JurisLean.LegalId .fact
  request : RequestKey
  origin : PremiseOrigin
deriving DecidableEq

/-- The origin must bind the same fact, case, run, and request. -/
def PremiseToken.WF (p : PremiseToken) : Prop :=
  match p.origin with
  | .admitted a =>
      a.fact = p.fact ∧
      a.caseScope = p.request.context.caseScope ∧
      a.runScope = p.request.context.runScope ∧
      a.status = .admitted
  | .assumed w =>
      w.fact = p.fact ∧ w.request = p.request

/-- Assumption dependencies are explicit and never silently erased. -/
def PremiseToken.dependencies (p : PremiseToken) : Finset String :=
  match p.origin with
  | .admitted _ => ∅
  | .assumed w => {w.assumptionId}

/-- Request identity is part of every Horn atom. This prevents a finite Horn
carrier from silently combining facts belonging to different LH/JC requests. -/
structure TaggedAtom where
  request : RequestKey
  atom : String
  dependencies : Finset String
deriving DecidableEq, Repr

def tagPremise (p : PremiseToken) : TaggedAtom :=
  { request := p.request
    atom := p.fact.payload
    dependencies := p.dependencies }

@[simp] theorem tagPremise_request (p : PremiseToken) :
    (tagPremise p).request = p.request := rfl

@[simp] theorem admitted_token_has_no_assumption
    (a : JurisLean.FactAdmissionAttestation)
    (f : JurisLean.LegalId .fact) (r : RequestKey) :
    PremiseToken.dependencies
      { fact := f, request := r, origin := .admitted a } = ∅ := rfl

@[simp] theorem assumed_token_keeps_assumption
    (w : AssumptionWitness) (f : JurisLean.LegalId .fact)
    (r : RequestKey) :
    w.assumptionId ∈
      PremiseToken.dependencies
        { fact := f, request := r, origin := .assumed w } := by
  simp [PremiseToken.dependencies]

theorem admitted_wf_has_admitted_status
    (a : JurisLean.FactAdmissionAttestation)
    (f : JurisLean.LegalId .fact) (r : RequestKey)
    (h : PremiseToken.WF
      { fact := f, request := r, origin := .admitted a }) :
    a.status = .admitted := h.2.2.2

theorem premise_origin_is_closed (p : PremiseToken) :
    (∃ a, p.origin = .admitted a) ∨
    (∃ w, p.origin = .assumed w) := by
  cases p.origin with
  | admitted a => exact Or.inl ⟨a, rfl⟩
  | assumed w => exact Or.inr ⟨w, rfl⟩

end JurisLean.ULM
