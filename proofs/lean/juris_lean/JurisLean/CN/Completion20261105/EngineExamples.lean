import JurisLean.CN.Completion20261105.Runtime
import JurisLean.Candidates.AdaptiveRoundLedgerAudit20261027

/-!
C4 acceptance: eight distinct native computations, using the public admitted
material lookup. Existing main synthetic RSI fixtures are reused as data; no U
obligation is re-proved, re-opened or re-accepted by this test module.
-/
namespace JurisLean.CN.Completion20261105.EngineExamples
open JurisLean.KernelV3
open JurisLean.CN.Revision20261101
open Examples

def context : EngineContext := ⟨toyScope,toyScope.question⟩
def input (call : EngineCall) : EngineMaterial := ⟨⟨9⟩,toyScope,toyScope.question,⟨10⟩,1,call⟩
def stored (call : EngineCall) : Situation := advance normal (.registerEngine (request .learnModel) (input call))
def run (call : EngineCall) : Reply EngineOutput := executeCommand (stored call) (.engine context ⟨9⟩)

def protocol : Native.Fit.LearningProtocol :=
  ⟨⟨1,1,1,1,1,⟨0⟩,⟨1⟩⟩,1,1,1,1,1,1,1,1/10⟩
def fit : EngineCall := .fit 1 1 protocol
  (fun q b => (q - if b then 1 else 0)^2) [[0],[1]] (fun _ => (0,true))
def one : Native.Prob.FiniteLaw (Fin 1) :=
  ⟨fun _ => 1,by decide,by decide⟩
def coin : Native.Prob.FiniteLaw Bool :=
  ⟨fun _ => 1/2,by decide,by decide⟩
def prob : EngineCall := .prob 1 one (fun _ => 1) (fun _ => ⟨80⟩)
def causalModel : CausalInput 1 1 :=
  ⟨one,fun _ => one,fun _ => coin,fun _ _ => 1,fun _ _ a => if a then 2 else 0⟩
def causal : EngineCall := .causal 1 1 causalModel (some ⟨toyScope,toyNorm,toyScope.question⟩)
def bargain : EngineCall := .bargain 2 (fun a => a.val) (fun _ => true) [0,1]
  (fun a => [(⟨12⟩,⟨a.val⟩)])
def amountTag : Native.AmountTag := ⟨"CNY","yuan",1⟩
def cashBefore : Native.Cash.State :=
  {debt := ⟨⟨6⟩,⟨8⟩,⟨7⟩,⟨10,amountTag⟩,"synthetic source debt"⟩
   formations := [⟨6⟩]
   judgment := .supported
   procedure := .open
   claim := .yes
   executionEligible := true
   initialDebt := 10
   newDebt := 0
   accrual := 0
   allocated := 0
   writtenOff := 0
   paid := 0
   surplus := 0
   cash := []
   used := ∅
   receipts := []
   rest := none
   refundCash := []
   normHistory := []
   env := .known 0}
def payment : Native.PaymentPayload :=
  ⟨⟨1⟩,0,⟨6⟩,⟨8⟩,⟨7⟩,⟨3,amountTag⟩,⟨10⟩,⟨81⟩,1,⟨0⟩⟩
def cash : EngineCall := .cash cashBefore payment
def exact : EngineCall := .exact .scalar ⟨.rational (1/2),none⟩ ⟨.rational (1/3),none⟩
def behavior : EngineCall := .behavior (1/2) ⟨12⟩ (fun a => ⟨100+a.val⟩)

def kindOf (reply : Reply EngineOutput) : Option UEng :=
  match reply.answer with | .success out => some out.engine | _ => none
def exactScalar (reply : Reply EngineOutput) : Option Rat :=
  match reply.answer with
  | .success out => match out.engine,out.payload with
    | .exact,⟨.scalar,q⟩ => some q.value
    | _,_ => none
  | _ => none

theorem fit_actual_call : kindOf (run fit) = some .fit := by decide
theorem prob_actual_call : kindOf (run prob) = some .prob := by decide
theorem causal_actual_call : kindOf (run causal) = some .causal := by decide
theorem bargain_actual_call : kindOf (run bargain) = some .bargain := by decide
theorem cash_actual_call : kindOf (run cash) = some .cash := by decide
theorem exact_actual_call : exactScalar (run exact) = some (5/6) := by decide
theorem behavior_actual_call : kindOf (run behavior) = some .behave := by decide

theorem exact_cannot_relabel_money_as_day :
    kindOf (run (.exact .day ⟨.rational 1,some amountTag⟩ ⟨.rational 2,some amountTag⟩)) = none := by decide
theorem probability_labels_cannot_collide :
    kindOf (run (.prob 2 ⟨fun _ => 1/2,by decide,by decide⟩ (fun _ => 1) (fun _ => ⟨80⟩))) = none := by decide
theorem withdrawal_blocks_actual_engine :
    kindOf (executeCommand (advance (stored exact) (.withdraw (request .admitEvidence) ⟨9⟩ ⟨82⟩))
      (.engine context ⟨9⟩)) = none := by decide

def cashStart : Situation :=
  let st := {formedCase.core.state with F := [⟨⟨81⟩,⟨8⟩,toyAtom,0⟩]}
  {formedCase.withCore (formedCase.core.putState st rfl) with
    accounts := fun id => if id = ⟨6⟩ then some cashBefore else none}
def paid : Reply Unit := executeCommand cashStart (.perform (request .perform) .human ⟨6⟩ payment)
theorem actual_performance_consumes_native_cash :
    paid.answer = .success () ∧
    (paid.after.accounts ⟨6⟩).map Native.Cash.balance = some 7 ∧
    paid.after.core.state.ledger.length = 1 ∧
    paid.after.core.state.F = cashStart.core.state.F ∧ paid.after.core.state.L = cashStart.core.state.L := by decide
theorem performance_duplicate_is_no_commit :
    (executeCommand paid.after (.perform (request .perform) .human ⟨6⟩ payment)).after.core.state.ledger.length = 1 := by decide

def rsiCheck : Bool :=
  match ValidatedFeedbackLoadFixture.built with
  | .known (service,evaluation) =>
    let generated := AdaptiveRoundLedgerFixture.generate (AdaptiveRoundLedgerFixture.base service)
    let req := AdaptiveRoundLedgerFixture.request generated evaluation evaluation.blocks
    let engine := EngineCall.rsi 2 generated req [req.sampling] [req.permit] ⟨83⟩
    let s := stored engine
    let result := runBoundEngine s context ⟨9⟩
    let actual := consumeRSI s context generated req [req.sampling] [req.permit] ⟨83⟩
    decide (kindOf result.legal = some .rsi ∧ actual.native.status = .evaluated ∧
      Native.RSI.roundSpent actual.native.post = 1/10 ∧
      actual.native.post.service.loaded =
        (AdaptiveRoundLedgerFixture.firstRound service evaluation).post.service.loaded ∧
      result.legal.after.core.state.decisions.isEmpty = true ∧
      result.legal.after.core.state.bindings.isEmpty = true)
  | _ => false

def checkIO : IO Unit := do
  unless rsiCheck do throw (IO.userError "actual admitted RSI consumer/load/round budget failed")
  IO.println "CN_EIGHT_NATIVE_CONSUMERS_PASS; RSI_ACTUAL_POST_RETAINED"

#eval checkIO
#print axioms fit_actual_call
#print axioms prob_actual_call
#print axioms causal_actual_call
#print axioms bargain_actual_call
#print axioms cash_actual_call
#print axioms exact_actual_call
#print axioms behavior_actual_call
#print axioms exact_cannot_relabel_money_as_day
#print axioms probability_labels_cannot_collide
#print axioms withdrawal_blocks_actual_engine
#print axioms actual_performance_consumes_native_cash
#print axioms performance_duplicate_is_no_commit
end JurisLean.CN.Completion20261105.EngineExamples
