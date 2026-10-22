import Mathlib

/-!
Candidate construction against 825792b, frozen manuscript 01 sections 1/14/17,
13 S07--S10, 14 C1--C2, and construction card 06. CI_NOT_RUN.

Six logical layers (DS09, not six storage services):
* Real events: external occurrence evidence, never inferred from a field.
* Source/identity: scoped references and the partial interpretation mu.
* Legal semantics: versioned external interpretation and effects.
* Quantities: exact arithmetic and allocation conservation.
* Procedure/evidence: judgment, opportunities, lawful closure, eligibility.
* Cash/receipts: actual cash events, distinct from orders and accrual.
An equality or calculation in one layer supplies no conclusion in another.
Truth is a world predicate; Judgment is an evidence-policy output.
-/

namespace JurisLean.Candidates.Final20261021

structure CaseId where
  value : Nat
  deriving DecidableEq, Repr
structure SourceRef where
  value : Nat
  deriving DecidableEq, Repr
structure EventId where
  value : Nat
  deriving DecidableEq, Repr
structure PaymentId where
  value : Nat
  deriving DecidableEq, Repr
structure RelationId where
  value : Nat
  deriving DecidableEq, Repr
structure AttemptId where
  value : Nat
  deriving DecidableEq, Repr
structure MeasurementId where
  value : Nat
  deriving DecidableEq, Repr
structure RecordId where
  value : Nat
  deriving DecidableEq, Repr
structure PartyId where
  value : Nat
  deriving DecidableEq, Repr

inductive ObjectId where
  | party (id : PartyId)
  | relation (id : RelationId)
  | payment (id : PaymentId)
  | document (id : Nat)
  deriving DecidableEq, Repr

structure LawDate where
  ordinal : Int
  deriving DecidableEq, Repr
structure Instant where
  ticks : Int
  deriving DecidableEq, Repr

-- No implicit coercion from Instant to LawDate. The conversion rule is input.
structure DateInterpretation where
  jurisdiction : String
  timezone : String
  ruleVersion : Nat
  toDate : Instant → LawDate

structure AmountTag where
  currency : String
  unit : String
  ruleVersion : Nat
  deriving DecidableEq, Repr

structure Amount where
  value : ℚ
  tag : AmountTag
  deriving DecidableEq, Repr

structure Gamma where
  caseId : CaseId
  caseRevision : Nat
  evidenceVersion : Nat
  jurisdiction : String
  question : Nat
  interpretation : Nat
  normVersion : Nat
  lawDate : LawDate
  knowledgeCutoff : Instant
  recordCutoff : Instant
  schemaVersion : Nat
  observationFamily : Nat
  mechanismVersion : Nat
  deriving DecidableEq, Repr

inductive Applicable where
  | yes | no | unknown
  deriving DecidableEq, Repr

inductive Judgment where
  | supported | opposed | incompatible | insufficient
  deriving DecidableEq, Repr

inductive Procedure where
  | open | blocked | closedLawfully
  deriving DecidableEq, Repr

inductive Error where
  | identityUnknown | notApplicable | applicabilityUnknown
  | prestateRequired | scopeMismatch | unitBindingMissing | mixedCurrency
  | authorityUnresolved | versionConflict | missingEvidence
  | openMissingOpportunity | checkIncomplete | incompatibleFiber
  | observationBindingMismatch | stageFrameMismatch
  | roundingBasisMissing | cashEventMissing | duplicateCash
  | layerCollapse | prematureCash | restNotEligible | autoFullRefund | accrualCashCollapse
  | burnedByUnknown | nonContinuousConsume | stateConservationMismatch
  | unsupported | notIdentified | targetMismatch
  deriving DecidableEq, Repr

inductive Result (A : Type) where
  | known (value : A)
  | unknown (reason : Error)
  | rejected (reason : Error)
  | conflict (left right : Nat)
  deriving DecidableEq, Repr

inductive TxResult (Receipt Payload : Type) where
  | committed (receipt : Receipt)
  | replay (receipt : Receipt)
  | rejectedNoCommit (attempt : AttemptId) (reason : Error)
  | conflict (registered requested : Payload)
  | unknownCommit (key : PaymentId) (attempt : AttemptId)
  deriving DecidableEq, Repr

-- A handle contains the complete immutable output, not merely a name/hash.
-- Pipeline passes this value as the next call's previous_output_ref.
structure PostStateHandle (S : Type) where
  gamma : Gamma
  revision : Nat
  state : S
  deriving DecidableEq, Repr

structure DebtRecord where
  relation : RelationId
  obligor : PartyId
  creditor : PartyId
  amount : Amount
  metadata : String
  deriving DecidableEq, Repr

structure CashEvent where
  id : EventId
  source : SourceRef
  payer : PartyId
  payee : PartyId
  amount : Amount
  deriving DecidableEq, Repr

structure PaymentPayload where
  caseId : CaseId
  caseRevision : Nat
  relation : RelationId
  payer : PartyId
  payee : PartyId
  amount : Amount
  source : SourceRef
  cashId : EventId
  normVersion : Nat
  factDate : LawDate
  deriving DecidableEq, Repr

structure PaymentRequest where
  key : PaymentId
  attempt : AttemptId
  payload : PaymentPayload
  applicable : Applicable
  interpretedPayment : Option PaymentId
  deriving DecidableEq, Repr

-- Descriptive layer names, not proof certificates.
inductive LogicalLayer where
  | realEvent | identity | legalSemantics | quantity | procedureEvidence | cashReceipt
  deriving DecidableEq, Repr

end JurisLean.Candidates.Final20261021
