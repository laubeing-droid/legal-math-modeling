import JurisLean.CN.Revision20261101.World

/-!
中文说明：八引擎具名消费。
消费 Revision20261101 的 EngineOutput / EngineValue / Candidate / bridgeCandidate。
不重证 U 债。不把分数当 Judgment。无 sorry。
法律是参数；本模块只给消费门，不给引擎的完整数值语义。
-/
namespace JurisLean.CN.Completion20261105.Payloads

open JurisLean.CN.Revision20261101
open JurisLean.KernelV3

/-! ## 具名消费载荷：八个构造子，没有 Judgment，没有 DecideBind。 -/

/-- 中文说明：八引擎具名消费的载荷。
    没有 established / notEstablished / undetermined 构造子，
    也没有 DecideBinding 构造子。分数留成分数。 -/
inductive ConsumePayload where
  | fitP (p : Quantity .scalar × Quantity .scalar)
  | probP (ps : List (Ref .event × Quantity .scalar))
  | causalP (p : Quantity .scalar × Quantity .scalar)
  | bargainP (ps : List (Ref .actor × Quantity .money))
  | cashP (ps : List (Ref .relation × Quantity .money))
  | exactP (p : (u : UnitKind) × Quantity u)
  | behaveP (ps : List (Ref .actor × Ref .query))
  | rsiP (p : Ref .model × Ref .model)

/-- 中文说明：消费出口三分：具名载荷 / KernelV3.Judgment / DecideBind。
    只有 Decide 通道能到 decideBind；八引擎 namedConsume 只走 consume。 -/
inductive Flow where
  | consume (c : ConsumePayload)
  | judgment (j : Judgment)
  | decideBind (d : DecideBinding)

/-! ## 现金守恒的具名和（先于现金消费门）。 -/

/-- 中文说明：分配向量和。单元素免 Rat+0，两元素直接加。 -/
def cashTotal : List (Ref .relation × Quantity .money) → Rat
  | [] => 0
  | [(_, q)] => q.value
  | [(_, q1), (_, q2)] => q1.value + q2.value
  | (_, q1) :: (_, q2) :: xs => q1.value + q2.value + cashTotal xs

theorem cashTotal_nil : cashTotal [] = 0 := rfl

theorem cashTotal_one (r : Ref .relation) (q : Quantity .money) :
    cashTotal [(r, q)] = q.value := rfl

theorem cashTotal_two (r1 r2 : Ref .relation) (q1 q2 : Quantity .money) :
    cashTotal [(r1, q1), (r2, q2)] = q1.value + q2.value := rfl

/-! ## 八引擎统一具名分发。 -/

/-- 中文说明：按 UEng 标签把 EngineValue 分派到具名载荷。 -/
def dispatch : (e : UEng) → EngineValue e → ConsumePayload
  | .fit, p => .fitP p
  | .prob, p => .probP p
  | .causal, p => .causalP p
  | .bargain, p => .bargainP p
  | .cash, p => .cashP p
  | .exact, p => .exactP p
  | .behave, p => .behaveP p
  | .rsi, p => .rsiP p

@[simp] theorem dispatch_fit (p : Quantity .scalar × Quantity .scalar) :
    dispatch .fit p = .fitP p := rfl

@[simp] theorem dispatch_prob (ps : List (Ref .event × Quantity .scalar)) :
    dispatch .prob ps = .probP ps := rfl

@[simp] theorem dispatch_causal (p : Quantity .scalar × Quantity .scalar) :
    dispatch .causal p = .causalP p := rfl

@[simp] theorem dispatch_bargain (ps : List (Ref .actor × Quantity .money)) :
    dispatch .bargain ps = .bargainP ps := rfl

@[simp] theorem dispatch_cash (xs : List (Ref .relation × Quantity .money)) :
    dispatch .cash xs = .cashP xs := rfl

@[simp] theorem dispatch_exact (p : (u : UnitKind) × Quantity u) :
    dispatch .exact p = .exactP p := rfl

@[simp] theorem dispatch_behave (ps : List (Ref .actor × Ref .query)) :
    dispatch .behave ps = .behaveP ps := rfl

@[simp] theorem dispatch_rsi (p : Ref .model × Ref .model) :
    dispatch .rsi p = .rsiP p := rfl

/-- 中文说明：按 engine 标签具名分发载荷。
    输入是 EngineOutput，不是 UEng 名字加裸数。 -/
def namedConsume (out : EngineOutput) : ConsumePayload :=
  dispatch out.engine out.payload

/-! ## 八引擎各 namedConsume（具名出口）。 -/

/-- 中文说明：拟合消费。返回标量对，不是 Judgment。 -/
def namedConsumeFit (out : EngineOutput) :
    Option (Quantity .scalar × Quantity .scalar) :=
  match namedConsume out with
  | .fitP p => some p
  | _ => none

/-- 中文说明：概率材料消费。返回事件权重表，不设法定尺。 -/
def namedConsumeProb (out : EngineOutput) :
    Option (List (Ref .event × Quantity .scalar)) :=
  match namedConsume out with
  | .probP ps => some ps
  | _ => none

/-- 中文说明：因果消费。没 permit 不桥；桥了也还是区间材料，不是法律因果认定。 -/
def namedConsumeCausal (out : EngineOutput) (permit : Option CausalPermit) :
    Check (Quantity .scalar × Quantity .scalar) :=
  match bridgeCandidate permit out with
  | .unknown r => .unknown r
  | .known o =>
    match namedConsume o with
    | .causalP p => .known p
    | _ => .unknown .inputUnchecked

/-- 中文说明：议价消费。返回报价向量；不产生 Bind。 -/
def namedConsumeBargain (out : EngineOutput) :
    Option (List (Ref .actor × Quantity .money)) :=
  match namedConsume out with
  | .bargainP ps => some ps
  | _ => none

/-- 中文说明：现金消费。需守恒：分配和等于总额才 known，否则 inputUnchecked。 -/
def namedConsumeCash (out : EngineOutput) (total : Quantity .money) :
    Check (List (Ref .relation × Quantity .money)) :=
  match namedConsume out with
  | .cashP xs =>
    if cashTotal xs = total.value then .known xs else .unknown .inputUnchecked
  | _ => .unknown .inputUnchecked

/-- 中文说明：精确量消费。带单位有理数。 -/
def namedConsumeExact (out : EngineOutput) :
    Option ((u : UnitKind) × Quantity u) :=
  match namedConsume out with
  | .exactP p => some p
  | _ => none

/-- 中文说明：行为消费。返回主体-查询表；经验有效不等于法律允许。 -/
def namedConsumeBehave (out : EngineOutput) :
    Option (List (Ref .actor × Ref .query)) :=
  match namedConsume out with
  | .behaveP ps => some ps
  | _ => none

/-- 中文说明：RSI 消费。只给旧/新模型身份；加载与换 N 不在这门里。 -/
def namedConsumeRsi (out : EngineOutput) :
    Option (Ref .model × Ref .model) :=
  match namedConsume out with
  | .rsiP p => some p
  | _ => none

/-! ## 合成输出（只用于消费门的正反见证；不是真实引擎）。 -/

def mkFit (scope : Scope) (target : Ref .query) (a b : Quantity .scalar) : EngineOutput :=
  { engine := .fit, scope := scope, target := target
    sourceHistory := [], theoremRef := "U01", assumptions := []
    payload := (a, b) }

def mkProb (scope : Scope) (target : Ref .query)
    (ps : List (Ref .event × Quantity .scalar)) : EngineOutput :=
  { engine := .prob, scope := scope, target := target
    sourceHistory := [], theoremRef := "U02", assumptions := []
    payload := ps }

def mkCausal (scope : Scope) (target : Ref .query) (lo hi : Quantity .scalar) : EngineOutput :=
  { engine := .causal, scope := scope, target := target
    sourceHistory := [], theoremRef := "U11", assumptions := []
    payload := (lo, hi) }

def mkBargain (scope : Scope) (target : Ref .query)
    (ps : List (Ref .actor × Quantity .money)) : EngineOutput :=
  { engine := .bargain, scope := scope, target := target
    sourceHistory := [], theoremRef := "U06", assumptions := []
    payload := ps }

def mkCash (scope : Scope) (target : Ref .query)
    (xs : List (Ref .relation × Quantity .money)) : EngineOutput :=
  { engine := .cash, scope := scope, target := target
    sourceHistory := [], theoremRef := "U09", assumptions := []
    payload := xs }

def mkExact (scope : Scope) (target : Ref .query)
    (p : (u : UnitKind) × Quantity u) : EngineOutput :=
  { engine := .exact, scope := scope, target := target
    sourceHistory := [], theoremRef := "exact", assumptions := []
    payload := p }

def mkBehave (scope : Scope) (target : Ref .query)
    (ps : List (Ref .actor × Ref .query)) : EngineOutput :=
  { engine := .behave, scope := scope, target := target
    sourceHistory := [], theoremRef := "behave", assumptions := []
    payload := ps }

def mkRsi (scope : Scope) (target : Ref .query) (oldModel newModel : Ref .model) : EngineOutput :=
  { engine := .rsi, scope := scope, target := target
    sourceHistory := [], theoremRef := "U10", assumptions := []
    payload := (oldModel, newModel) }

/-! ## 构造子不混。 -/

/-- 中文证明：具名载荷不是 Judgment。 -/
theorem consume_ne_judgment (c : ConsumePayload) (j : Judgment) :
    Flow.consume c ≠ Flow.judgment j := by
  intro h
  cases h

/-- 中文证明：具名载荷不是 DecideBind。 -/
theorem consume_ne_decideBind (c : ConsumePayload) (d : DecideBinding) :
    Flow.consume c ≠ Flow.decideBind d := by
  intro h
  cases h

/-! ## 五个门。 -/

/-- 中文证明：拟合落位是 fitP，不是 Judgment。
    这是 API 限制（S2/P8）：本模块不定义 Quantity → Judgment；
    不是“不存在任何单调函数”的数学定理。 -/
theorem fit_is_fitP (s : Scope) (t : Ref .query) (a b : Quantity .scalar) :
    namedConsume (mkFit s t a b) = .fitP (a, b) := rfl

theorem namedConsumeFit_mkFit (s : Scope) (t : Ref .query) (a b : Quantity .scalar) :
    namedConsumeFit (mkFit s t a b) = some (a, b) := rfl

/-- 中文证明：任何 EngineOutput 的具名消费都不产生 Judgment。拟合是其中一例。 -/
theorem namedConsume_not_judgment (out : EngineOutput) (j : Judgment) :
    Flow.consume (namedConsume out) ≠ Flow.judgment j :=
  consume_ne_judgment _ j

/-- 中文证明：任何 EngineOutput 的具名消费都不产生 DecideBind。议价、候选都是其中一例。 -/
theorem namedConsume_not_decideBind (out : EngineOutput) (d : DecideBinding) :
    Flow.consume (namedConsume out) ≠ Flow.decideBind d :=
  consume_ne_decideBind _ d

/-- 中文证明：候选经 propose 只写 candidates 和 A.version，
    bindings / L / N / F 逐位不变，故该路径不新增 DecideBind。 -/
theorem candidateFromEngine_propose_frame (s : Sit) (parent : Ref .model) (out : EngineOutput) :
    (propose s (candidateFromEngine parent out)).bindings = s.bindings
    ∧ (propose s (candidateFromEngine parent out)).L = s.L
    ∧ (propose s (candidateFromEngine parent out)).N = s.N
    ∧ (propose s (candidateFromEngine parent out)).F = s.F :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- 中文证明：候选路径不新增 DecideBind：propose 不写 bindings。 -/
theorem candidate_propose_bindings (s : Sit) (c : Candidate) :
    (propose s c).bindings = s.bindings := rfl

/-- 中文证明：议价落位是 bargainP；消费出口不是 DecideBind。 -/
theorem bargain_is_bargainP (s : Scope) (t : Ref .query)
    (ps : List (Ref .actor × Quantity .money)) :
    namedConsume (mkBargain s t ps) = .bargainP ps := rfl

theorem namedConsumeBargain_mkBargain (s : Scope) (t : Ref .query)
    (ps : List (Ref .actor × Quantity .money)) :
    namedConsumeBargain (mkBargain s t ps) = some ps := rfl

/-- 中文证明：因果没 permit 不桥。消费 Revision20261101.no_causal_permit_no_bridge，不重证。 -/
theorem namedConsumeCausal_none (out : EngineOutput) :
    namedConsumeCausal out none = .unknown .inputUnchecked := by
  unfold namedConsumeCausal
  rw [no_causal_permit_no_bridge]

/-- 中文证明：因果引擎错配也不桥（permit 在但 engine ≠ causal）。 -/
theorem namedConsumeCausal_wrong_engine (permit : CausalPermit)
    (s : Scope) (t : Ref .query) (a b : Quantity .scalar) :
    namedConsumeCausal (mkFit s t a b) (some permit) = .unknown .inputUnchecked := by
  unfold namedConsumeCausal
  simp only [bridgeCandidate, mkFit]
  have hbe : (JurisLean.CN.Ops.UEng.fit == JurisLean.CN.Ops.UEng.causal) = false := by decide
  simp [hbe]

/-- 中文证明：现金不守恒 → 拒绝消费（inputUnchecked），不填数。 -/
theorem cash_unconserved_unknown (s : Scope) (t : Ref .query) (r : Ref .relation)
    (q1 q2 : Quantity .money) (h : q1.value ≠ q2.value) :
    namedConsumeCash (mkCash s t [(r, q1)]) q2 = .unknown .inputUnchecked := by
  have htot : cashTotal [(r, q1)] = q1.value := rfl
  simp [namedConsumeCash, namedConsume, mkCash, htot, h]

/-- 中文证明：现金守恒 → known 分配向量。 -/
theorem cash_conserved_known (s : Scope) (t : Ref .query) (r : Ref .relation)
    (q : Quantity .money) :
    namedConsumeCash (mkCash s t [(r, q)]) q = .known [(r, q)] := by
  have htot : cashTotal [(r, q)] = q.value := rfl
  simp [namedConsumeCash, namedConsume, mkCash, htot]

/-- 中文证明：两笔分配守恒也 known。 -/
theorem cash_two_way_known (s : Scope) (t : Ref .query) (r1 r2 : Ref .relation)
    (q1 q2 total : Quantity .money) (h : q1.value + q2.value = total.value) :
    namedConsumeCash (mkCash s t [(r1, q1), (r2, q2)]) total
      = .known [(r1, q1), (r2, q2)] := by
  have htot : cashTotal [(r1, q1), (r2, q2)] = q1.value + q2.value := rfl
  simp [namedConsumeCash, namedConsume, mkCash, htot, h]

/-- 中文证明：known 出口必守恒。 -/
theorem namedConsumeCash_known_conserves (out : EngineOutput) (total : Quantity .money)
    (xs : List (Ref .relation × Quantity .money))
    (h : namedConsumeCash out total = .known xs) :
    cashTotal xs = total.value := by
  unfold namedConsumeCash at h
  cases hns : namedConsume out with
  | cashP ys =>
    simp only [hns] at h
    split at h
    next heq =>
      injection h with hxx
      subst hxx
      exact heq
    next =>
      simp at h
  | _ =>
    simp only [hns] at h
    simp at h

/-! ## 其余四引擎落位。 -/

theorem prob_is_probP (s : Scope) (t : Ref .query)
    (ps : List (Ref .event × Quantity .scalar)) :
    namedConsume (mkProb s t ps) = .probP ps := rfl

theorem namedConsumeProb_mkProb (s : Scope) (t : Ref .query)
    (ps : List (Ref .event × Quantity .scalar)) :
    namedConsumeProb (mkProb s t ps) = some ps := rfl

theorem exact_is_exactP (s : Scope) (t : Ref .query) (p : (u : UnitKind) × Quantity u) :
    namedConsume (mkExact s t p) = .exactP p := rfl

theorem namedConsumeExact_mkExact (s : Scope) (t : Ref .query) (p : (u : UnitKind) × Quantity u) :
    namedConsumeExact (mkExact s t p) = some p := rfl

theorem behave_is_behaveP (s : Scope) (t : Ref .query)
    (ps : List (Ref .actor × Ref .query)) :
    namedConsume (mkBehave s t ps) = .behaveP ps := rfl

theorem namedConsumeBehave_mkBehave (s : Scope) (t : Ref .query)
    (ps : List (Ref .actor × Ref .query)) :
    namedConsumeBehave (mkBehave s t ps) = some ps := rfl

theorem rsi_is_rsiP (s : Scope) (t : Ref .query) (oldModel newModel : Ref .model) :
    namedConsume (mkRsi s t oldModel newModel) = .rsiP (oldModel, newModel) := rfl

theorem namedConsumeRsi_mkRsi (s : Scope) (t : Ref .query) (oldModel newModel : Ref .model) :
    namedConsumeRsi (mkRsi s t oldModel newModel) = some (oldModel, newModel) := rfl

/-- 中文证明：fitP 与 bargainP 是不同构造子。 -/
theorem fitP_ne_bargainP (a b : Quantity .scalar)
    (ps : List (Ref .actor × Quantity .money)) :
    ConsumePayload.fitP (a, b) ≠ ConsumePayload.bargainP ps := by
  intro h
  cases h

/-! ## 公理审计。 -/
#print axioms consume_ne_judgment
#print axioms consume_ne_decideBind
#print axioms fit_is_fitP
#print axioms namedConsumeFit_mkFit
#print axioms namedConsume_not_judgment
#print axioms namedConsume_not_decideBind
#print axioms candidateFromEngine_propose_frame
#print axioms candidate_propose_bindings
#print axioms bargain_is_bargainP
#print axioms namedConsumeBargain_mkBargain
#print axioms namedConsumeCausal_none
#print axioms namedConsumeCausal_wrong_engine
#print axioms cash_unconserved_unknown
#print axioms cash_conserved_known
#print axioms cash_two_way_known
#print axioms namedConsumeCash_known_conserves
#print axioms prob_is_probP
#print axioms namedConsumeProb_mkProb
#print axioms exact_is_exactP
#print axioms namedConsumeExact_mkExact
#print axioms behave_is_behaveP
#print axioms namedConsumeBehave_mkBehave
#print axioms rsi_is_rsiP
#print axioms namedConsumeRsi_mkRsi
#print axioms fitP_ne_bargainP
#print axioms cashTotal_nil
#print axioms cashTotal_one
#print axioms cashTotal_two

end JurisLean.CN.Completion20261105.Payloads
