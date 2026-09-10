import Mathlib
import JurisLean.BusinessRoot.Semantics

/-!
ROOT05 — Parsing and refinement of the two actual artifacts.

Guarantee level (recorded per ROOT_REFINEMENT §4): the byte-to-token lexing of
the real UTF-8 files stays on the Python/TCB side; the Lean side models the
closed line grammar of `conditional_principal.txt` and the closed typed row
grammar of `calculation.json` as inductive token lists, and proves here that

* parsing is total and returns `none` on any closed-grammar violation: extra or
  missing lines, replaced rows, duplicate keys, demoted scenario rows;
* the value grammar is typed — rationals, strings, booleans and options only —
  so floats, NaN, infinities and pseudo-nulls cannot even be written (the real
  bytes are rejected on the Python side of the boundary, which is documented
  TCB);
* `parse ∘ render = id` for both structured artifacts;
* `readBoth` accepts only when BOTH files parse to the SAME protected record
  with the requirement identity and the complete mode, so a JSON that is
  correct while the text is wrong (and vice versa), a same-version model
  swapped wholesale, or two mixed source snapshots are all rejected.

No claim is made about arbitrary prose, DOCX display semantics or PDF.
-/

namespace JurisLean.BusinessRoot

/-- The exact notice text binding both artifacts. -/
def rootNotice : String := "SYNTHETIC_CONDITIONAL_MODEL_NOT_LITIGATION_FORECAST"

/-! ### Closed line grammar of the principal text artifact -/

inductive DocLine where
  | title
  | warning (s : String)
  | caseId (v : String)
  | issue (v : String)
  | creditor (v : String)
  | debtor (v : String)
  | debt (v : String)
  | basis (v : String)
  | dueDay (v : String)
  | asOfDay (v : String)
  | assumptions (v : String)
  | ctx (v : String)
  | mode (v : String)
  | scenarioRow (conds : List (String × Bool)) (balance over : ℚ)
  | pendingRow (conds : List (String × Bool))
  | footer

/-- Structured content of the frozen text artifact (exactly two scenario rows). -/
structure DocArt where
  caseId : String
  issue : String
  creditor : String
  debtor : String
  debt : String
  basis : String
  dueDay : String
  asOfDay : String
  assumptions : String
  ctx : String
  mode : String
  condT : List (String × Bool)
  balT : ℚ
  overT : ℚ
  condF : List (String × Bool)
  balF : ℚ
  overF : ℚ
  deriving DecidableEq

def toLines (a : DocArt) : List DocLine :=
  [.title, .warning rootNotice,
    .caseId a.caseId, .issue a.issue, .creditor a.creditor, .debtor a.debtor,
    .debt a.debt, .basis a.basis, .dueDay a.dueDay, .asOfDay a.asOfDay,
    .assumptions a.assumptions, .ctx a.ctx, .mode a.mode,
    .scenarioRow a.condT a.balT a.overT, .scenarioRow a.condF a.balF a.overF,
    .footer]

/-- Closed parse: the warning line must be the exact notice, and any extra or
missing line, replaced row, or demoted scenario row fails the exact shape. -/
def ofLines : List DocLine → Option DocArt
  | [.title, .warning w, .caseId c, .issue i, .creditor cr, .debtor de,
     .debt db, .basis ba, .dueDay dd, .asOfDay ad, .assumptions asu,
     .ctx cx, .mode mo,
     .scenarioRow ct b1 o1, .scenarioRow cf b2 o2, .footer] =>
      if w = rootNotice then
        some ⟨c, i, cr, de, db, ba, dd, ad, asu, cx, mo, ct, b1, o1, cf, b2, o2⟩
      else none
  | _ => none

theorem doc_roundtrip (a : DocArt) : ofLines (toLines a) = some a := by
  cases a
  rfl

/-- Demoting a scenario row to a pending row is not completeness: the artifact
becomes unparseable at the frozen shape instead of "complete by default". -/
theorem demoted_row_not_parseable (a : DocArt) (conds : List (String × Bool)) :
    ofLines ([DocLine.title, DocLine.warning rootNotice,
      DocLine.caseId a.caseId, DocLine.issue a.issue, DocLine.creditor a.creditor,
      DocLine.debtor a.debtor, DocLine.debt a.debt, DocLine.basis a.basis,
      DocLine.dueDay a.dueDay, DocLine.asOfDay a.asOfDay,
      DocLine.assumptions a.assumptions, DocLine.ctx a.ctx, DocLine.mode "PARTIAL_SCENARIOS",
      DocLine.scenarioRow a.condT a.balT a.overT, DocLine.pendingRow conds,
      DocLine.footer]) = none := by
  rfl

/-! ### Closed typed row grammar of the calculation.json artifact -/

/-- Each key occurs at most once and carries a typed value: strings, exact
rationals, booleans, lists of condition pairs or rationals, one optional
settlement. There is no float, NaN, infinity or null constructor, so such
values cannot be written in this grammar at all. -/
inductive JsonRow where
  | schemaField (v : String)
  | requirementField (v : String)
  | contextRow (version : String)
  | basisRow (sid ver : String)
  | principalField (q : ℚ)
  | outcomeRow (conds : List (String × Bool)) (balance over : ℚ)
  | weightRow (conds : List (String × Bool)) (p : ℚ)
  | thresholdField (t : ℚ)
  | costsRow (cp cd sp sd : ℚ)
  | optionsRow (xs : List ℚ)
  | analyticsRow (ec eu ev lo hi : ℚ) (eligible : List ℚ) (sel : Option ℚ)

structure JsonArt where
  schema : String
  requirement : String
  contextVersion : String
  basisSid : String
  basisVer : String
  principal : ℚ
  outT : List (String × Bool) × ℚ × ℚ
  outF : List (String × Bool) × ℚ × ℚ
  weightT : List (String × Bool) × ℚ
  weightF : List (String × Bool) × ℚ
  threshold : ℚ
  costP : ℚ
  costD : ℚ
  settleP : ℚ
  settleD : ℚ
  options : List ℚ
  expC : ℚ
  expU : ℚ
  event : ℚ
  lower : ℚ
  upper : ℚ
  eligible : List ℚ
  selected : Option ℚ
  deriving DecidableEq

def toJson (a : JsonArt) : List JsonRow :=
  [.schemaField a.schema, .requirementField a.requirement, .contextRow a.contextVersion,
    .basisRow a.basisSid a.basisVer, .principalField a.principal,
    .outcomeRow a.outT.1 a.outT.2.1 a.outT.2.2,
    .outcomeRow a.outF.1 a.outF.2.1 a.outF.2.2,
    .weightRow a.weightT.1 a.weightT.2, .weightRow a.weightF.1 a.weightF.2,
    .thresholdField a.threshold, .costsRow a.costP a.costD a.settleP a.settleD,
    .optionsRow a.options,
    .analyticsRow a.expC a.expU a.event a.lower a.upper a.eligible a.selected]

/-- Strict parse: every key exactly once, in the fixed order. A duplicated key
row breaks the shape and yields `none`. -/
def ofJson : List JsonRow → Option JsonArt
  | [.schemaField s, .requirementField r, .contextRow v,
     .basisRow sid ver, .principalField p,
     .outcomeRow ct b1 o1, .outcomeRow cf b2 o2,
     .weightRow wt pw, .weightRow wf pwf,
     .thresholdField t, .costsRow cp cd sp sd, .optionsRow xs,
     .analyticsRow ec eu ev lo hi el sel] =>
      some ⟨s, r, v, sid, ver, p, (ct, b1, o1), (cf, b2, o2), (wt, pw), (wf, pwf),
        t, cp, cd, sp, sd, xs, ec, eu, ev, lo, hi, el, sel⟩
  | _ => none

theorem json_roundtrip (a : JsonArt) : ofJson (toJson a) = some a := by
  cases a
  rfl

/-- Duplicate key: a second threshold field makes the row list unparseable. -/
theorem duplicate_key_rejected (a : JsonArt) :
    ofJson (JsonRow.thresholdField a.threshold :: toJson a) = none := by
  rfl

/-! ### Protected records and the joint read-back -/

/-- The text artifact determines its scenario rows; requirement identity,
principal and the analytics block come from the independent frozen input. -/
def docToProtected (a : DocArt) (principal ec eu ev lo hi : ℚ)
    (eligible : List ℚ) (sel : Option ℚ) : Protected :=
  { requirement := requirementQ
    principal := principal
    rows := [(a.condT, a.balT, a.overT), (a.condF, a.balF, a.overF)]
    pending := []
    expectedC := ec
    expectedU := eu
    eventProbability := ev
    lower := lo
    upper := hi
    eligible := eligible
    selected := sel
    notice := rootNotice }

/-- The JSON artifact determines its whole protected record, including the
requirement identity it claims for itself. -/
def jsonToProtected (a : JsonArt) : Protected :=
  { requirement := a.requirement
    principal := a.principal
    rows := [(a.outT.1, a.outT.2.1, a.outT.2.2), (a.outF.1, a.outF.2.1, a.outF.2.2)]
    pending := []
    expectedC := a.expC
    expectedU := a.expU
    eventProbability := a.event
    lower := a.lower
    upper := a.upper
    eligible := a.eligible
    selected := a.selected
    notice := rootNotice }

/-- The pairwise acceptance condition of the frozen delivery. -/
def readBothCheck (expected : Protected) (d : DocArt) (j : JsonArt) : Bool :=
  decide (d.mode = "EXACT_FINITE_SCENARIOS" ∧
    docToProtected d expected.principal expected.expectedC expected.expectedU
        expected.eventProbability expected.lower expected.upper
        expected.eligible expected.selected = expected ∧
    jsonToProtected j = expected)

/-- Joint read-back of the two actual artifacts. Both must parse, the text must
declare the complete mode, and BOTH protected records must equal the expected
record computed from the independent frozen input; on success the joint
protected record is returned. A JSON that is correct while the text is wrong
(and vice versa), a wholesale model swap, or two mixed snapshots therefore
cannot pass. -/
def readBoth (expected : Protected) (doc : List DocLine) (js : List JsonRow) :
    Option Protected :=
  match ofLines doc, ofJson js with
  | some d, some j =>
      match readBothCheck expected d j with
      | true => some expected
      | false => none
  | _, _ => none

end JurisLean.BusinessRoot
