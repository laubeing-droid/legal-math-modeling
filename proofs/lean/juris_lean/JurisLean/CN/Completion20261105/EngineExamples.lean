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
def stored (call : EngineCall) : Situation :=
  advance {normal with causalClauses := [⟨toyNorm,toyScope,toyScope.question,toyAtom⟩]}
    (.registerEngine (request .learnModel) (input call))
def run (call : EngineCall) : Reply EngineOutput := executeCommand (stored call) (.engine context ⟨9⟩)

def protocol : Native.Fit.LearningProtocol :=
  ⟨⟨1,1,1,1,1,⟨0⟩,⟨1⟩⟩,1,1,1,1,1,1,1,1/10⟩
def fit : EngineCall := .fit 1 1 protocol
  (fun q b => (q - if b then 1 else 0)^2) [[0],[1]] (fun _ => (0,true))
def one : Native.Prob.FiniteLaw (Fin 1) :=
  ⟨fun _ => 1,by intro w; norm_num,by norm_num [Fin.sum_univ_succ]⟩
def coin : Native.Prob.FiniteLaw Bool :=
  ⟨fun _ => 1/2,by intro w; norm_num,by norm_num [Fintype.sum_bool]⟩
def prob : EngineCall := .prob 1 one (fun _ => 1) (fun _ => ⟨80⟩)
def causalModel : CausalInput 1 1 :=
  ⟨one,fun _ => one,fun _ => coin,fun _ _ => 1,fun _ _ a => if a then 2 else 0⟩
def causal : EngineCall := .causal 1 1 causalModel (some ⟨toyNorm,toyScope,toyScope.question⟩)
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









theorem exact_cannot_relabel_money_as_day :
    kindOf (run (.exact .day ⟨.rational 1,some amountTag⟩ ⟨.rational 2,some amountTag⟩)) = none := by decide
theorem probability_labels_cannot_collide :
    kindOf (run (.prob 2 ⟨fun _ => 1/2,by intro w; norm_num,by norm_num [Fin.sum_univ_succ]⟩ (fun _ => 1) (fun _ => ⟨80⟩))) = none := by decide
theorem withdrawal_blocks_actual_engine :
    kindOf (executeCommand (advance (stored exact) (.withdraw (request .admitEvidence) ⟨9⟩ ⟨82⟩))
      (.engine context ⟨9⟩)) = none := by decide

def cashStart : Situation :=
  let s := readyCase {confirmation with effect := .performance} .evidence
  let st := {s.core.state with F := [⟨⟨81⟩,⟨8⟩,toyAtom,0⟩],L := [toyRelation]}
  {s.withCore (s.core.putState st rfl) with
    accounts := fun id => if id = ⟨6⟩ then some cashBefore else none}
def paid : Reply Unit := executeCommand cashStart (.perform (call .perform) ⟨6⟩ payment)

def secondClaim : LegalRelation := {toyRelation with id := ⟨16⟩}
def secondAccount : Native.Cash.State := {cashBefore with debt := {cashBefore.debt with relation := ⟨16⟩}}
def jointStart : Situation :=
  let st := {cashStart.core.state with
    L := [toyRelation,secondClaim]
    constraints := [.equalReduction toyRelation secondClaim,.sameLoss toyRelation secondClaim]}
  {cashStart.withCore (cashStart.core.putState st rfl) with
    accounts := fun id => if id = ⟨16⟩ then some secondAccount else cashStart.accounts id
    equalReductionRules := [⟨toyNorm,toyScope,[⟨6⟩,⟨16⟩]⟩]}
def jointlyPaid : Reply Unit := executeCommand jointStart (.perform (call .perform) ⟨6⟩ payment)

def jointChecks : Bool := decide
  (jointlyPaid.answer = .success () ∧
   (jointlyPaid.after.accounts ⟨6⟩).map Native.Cash.balance = some 7 ∧
   (jointlyPaid.after.accounts ⟨16⟩).map Native.Cash.balance = some 7 ∧
   (jointlyPaid.after.accounts ⟨6⟩).map (fun s => s.paid) = some 3 ∧
   (jointlyPaid.after.accounts ⟨16⟩).map (fun s => s.paid) = some 0 ∧
   (jointlyPaid.after.accounts ⟨16⟩).map (fun s => s.cash.length) = some 0 ∧
   jointlyPaid.after.core.state.ledger.length = 1)



def rsiCheck : Bool :=
  match ValidatedFeedbackLoadFixture.built with
  | .known (service,evaluation) =>
    let generated := AdaptiveRoundLedgerFixture.generate (AdaptiveRoundLedgerFixture.base service)
    let req := AdaptiveRoundLedgerFixture.request generated evaluation evaluation.blocks
    let engine := EngineCall.rsi 2 generated req [req.sampling] [req.permit] ⟨83⟩
    let s := stored engine
    let result := runBoundEngine s context ⟨9⟩
    match result.native with
    | some ⟨.rsi _ _ _ _ _ _,actual⟩ =>
      decide (kindOf result.legal = some .rsi ∧ actual.status = .evaluated ∧
        Native.RSI.roundSpent actual.post = 1/10 ∧
        actual.post.service.loaded.fitted.table = [0,1] ∧
        (actual.receipt.bind (fun record => record.load)).map (fun load => load.status) = some .loaded ∧
        result.legal.after.engineResults.length = 1 ∧
        result.legal.after.core.state.decisions.isEmpty = true ∧
        result.legal.after.core.state.bindings.isEmpty = true)
    | _ => false
  | _ => false

def checkIO : IO Unit := do
  unless jointChecks do throw (IO.userError "actual shared reduction did not update both accounts from one payment")
  let noRule := executeCommand {jointStart with equalReductionRules := []}
    (.perform (call .perform) ⟨6⟩ payment)
  unless decide (noRule.answer = .unknown .inputUnchecked ∧ noRule.after.core.state.ledger.isEmpty = true) do
    throw (IO.userError "same-loss label fabricated a reduction rule")
  let foreignAccount := {secondAccount with debt := {secondAccount.debt with
    amount := {secondAccount.debt.amount with tag := ⟨"USD","money",1⟩}}}
  let foreignAccounts := fun id => if id = ⟨16⟩ then some foreignAccount else jointStart.accounts id
  let mixed := executeCommand {jointStart with accounts := foreignAccounts} (.perform (call .perform) ⟨6⟩ payment)
  unless decide (mixed.after.core.state.ledger.isEmpty = true) do
    throw (IO.userError "mixed currency silently committed")
  let mixedLedger := {jointStart.core.state with ledger :=
    [⟨⟨81⟩,⟨6⟩,⟨3⟩,request .perform⟩,⟨⟨82⟩,⟨16⟩,⟨4⟩,request .perform⟩]}
  let mixedMeasure := {jointStart.withCore (jointStart.core.putState mixedLedger rfl) with
    accounts := foreignAccounts}
  unless decide ((executeCommand mixedMeasure (.operator ⟨[],[],[]⟩ (.measure .money toyScope))).answer =
      .unknown .inputUnchecked) do
    throw (IO.userError "money measure silently summed different currency tags")
  let agentAccount := {cashBefore with debt := {cashBefore.debt with creditor := ⟨22⟩}}
  let agentAccounts := fun id => if id = ⟨6⟩ then some agentAccount else none
  let attributed := executeCommand {apparentStart with accounts := agentAccounts}
    (.institution (.apparent (call .constitute) (.atom toyAtom) ⟨22⟩ ⟨12⟩
      ⟨true,true,.established,true⟩))
  unless decide (attributed.answer = .success .established ∧
      (attributed.after.accounts ⟨6⟩).map (fun a => a.debt.creditor.value) = some 12 ∧
      (attributed.after.accounts ⟨6⟩).map (fun a => a.debt.amount.value) = some 10 ∧
      (attributed.after.accounts ⟨6⟩).map (fun a => a.cash.length) = some 0) do
    throw (IO.userError "apparent attribution did not preserve the native account identity/history")
  unless decide (kindOf (run fit) = some .fit) do throw (IO.userError "fit_actual_call failed")
  unless decide (kindOf (run prob) = some .prob) do throw (IO.userError "prob_actual_call failed")
  unless decide (kindOf (run causal) = some .causal) do throw (IO.userError "causal_actual_call failed")
  unless decide (kindOf (run bargain) = some .bargain) do throw (IO.userError "bargain_actual_call failed")
  unless decide (kindOf (run cash) = some .cash) do throw (IO.userError "cash_actual_call failed")
  unless decide (exactScalar (run exact) = some (5/6)) do throw (IO.userError "exact_actual_call failed")
  unless decide (kindOf (run behavior) = some .behave) do throw (IO.userError "behavior_actual_call failed")
  unless decide (paid.answer = .success () ∧
    (paid.after.accounts ⟨6⟩).map Native.Cash.balance = some 7 ∧
    (executeCommand paid.after (.operator ⟨[],[],[]⟩ (.measure .money toyScope))).answer = .success ⟨3⟩ ∧
    paid.after.core.state.ledger.length = 1 ∧
    paid.after.core.state.F = cashStart.core.state.F ∧ paid.after.core.state.L = cashStart.core.state.L) do throw (IO.userError "actual_performance_consumes_native_cash failed")
  unless decide ((executeCommand paid.after (.perform (call .perform) ⟨6⟩ payment)).after.core.state.ledger.length = 1) do throw (IO.userError "performance_duplicate_is_no_commit failed")

  let fitted := run fit
  let learned := executeCommand fitted.after (.learnReport (request .learnModel) ⟨9⟩)
  unless decide (learned.after.core.state.A.theta = [1] ∧ learned.after.core.state.N.version = 1 ∧
      learned.after.core.state.L.isEmpty = true) do
    throw (IO.userError "Learn did not consume the retained actual fitted table")
  unless rsiCheck do throw (IO.userError "actual admitted RSI consumer/load/round budget failed")
  IO.println "CN_EIGHT_NATIVE_CONSUMERS_PASS; RSI_ACTUAL_POST_RETAINED"
  IO.println "CN_SHARED_REDUCTION_ONE_CASH_PASS"

#eval checkIO
#print axioms exact_cannot_relabel_money_as_day
#print axioms probability_labels_cannot_collide
#print axioms withdrawal_blocks_actual_engine
end JurisLean.CN.Completion20261105.EngineExamples
