import Mathlib.Tactic

/-!
W4 试点 T122 五方法解释 ＋ T123 解释分支 —— 六件套之 Lean 合同件。

出处（施工合同）：
- `docs/spec/20261007-统一法律数学模型_附录K_全量目标落实表.md:2551`（T122 行：
  §3.1,11.2：五解释构造有原文理由，分支先隔离；I.0/I.4/I.11 与 J.0/J.6/J.12–14；
  本行原反例独立保留）与 `:2552`（T123 行：§3.1,4.3：解释相容/攻击/优先，
  不能引用另支前提；锚与反例条款同上）。
- `docs/spec/20261007-统一法律数学模型_全量施工方案.md:91`（§3.1：解释构造子为
  文义、体系、目的、历史、合宪；输入原文、上下文或相应理由材料，输出具体有类型
  规则 AST 及理由，**不以"使用了某方法"自动证明解释正确**；采用/排除解释仍须
  法定权限与具名理由；未采用候选不进入无条件规则库；来源查明不完整与法律允许
  数个解释分开——后者保留每个具来源的解释支路及相互攻击）。
- 同文件 `:757–763`（§11.2 P066：五解释构造子应保存输入文本、解释目标、范围及
  新增/选择/保持效应；合宪解释是受相应制度权限约束的解释路径，不使普通法院或
  模型取得宣告法律失效的权限；类推另列为漏洞续造构造子，不在五解释之列）。
- 同文件 `:123–145`（§4.3：攻击由具来源论证树构造、按具名规则核对靶点，不从
  标签或结果需要倒填边）。

六件套分工：本件＝新合同（T122 五构造子＋理由字段＋合法性定理；T123 相容/攻击/
优先关系＋**分支隔离定理**＋反例见证保留）。Python 入口
`tools/full_math/implementation/interpretation_ref.py`、独立 checker
`tools/full_math/implementation/interp_ref_check.py`、下游消费
`tools/unified_math_v2/unified/pipeline.py`（run_case）、正反例
`tools/full_math/implementation_tests/test_interpretation_ref.py` 与
`tools/unified_math_v2/tests/test_interpretation_branch.py`、合成回执见报告
`.local/agent_L_w4_t122_report.md`。

## 一、法律语义（人话）

- **T122（五解释构造）**：对同一法源文本，文义/体系/目的/历史/合宪五个构造子各自
  从原文与上下文/理由材料出发，输出"具体有类型规则 AST ＋具名理由"。三个不变量：
  ①构造子**保存输入面**（输入文本、目标、范围、新增/选择/保持效应——P066）；
  ②**构造不等于采用**：使用某方法不自动证明解释正确，采用须法定权限＋具名理由，
  未采用候选不进规则库（§3.1；本行原反例＝"只跑了文义方法、无权限"的候选被拒于
  规则库之外，见 `unauthLiteral`/`method_use_not_proof_of_correctness`/`unauth_rule_not_in_base`）；
  ③采用只增规则 AST 本身、不附带宣告法源失效等额外权力（P066，`adoption_adds_only_rule`）。
- **T123（解释分支）**：法律允许数个解释时，每个具来源支路作为独立分支保留并带
  相互攻击（不合并、不丢弃、不唯一化）；攻击由已采用的具体候选构造（§4.3：不从
  标签倒填）；优先是具名排除边、只落在真冲突上，采用集按具名优先收敛；**分支隔离
  定理**：一支推导引用的前提必须全在本支私有前提内——前提不相交的两支，一支的
  合法推导不引用另一支的任何前提，引用另支前提的推导被隔离门拒绝（本行原反例＝
  `crossDeriv` 被 `branchX` 拒绝，见 `witness_cross_rejected`/`witness_cross_not_wf`）。

## 二、数学对象

- `InterpMethod`（恰五构造子：`literal`/`systematic`/`teleological`/`historical`/
  `constitutional`）、`InterpEffect`（新增/选择/保持）、`RuleAst`（有类型规则
  AST：`ruleId`/`premises`/`conclusion`）、`InterpInput`（原文 textId＋上下文
  理由材料表）、`InterpCandidate`（candId＋方法＋输入＋目标＋范围＋效应＋规则
  AST＋具名理由 `reasonId : Option Nat`＋法定权限 `authorityId : Option Nat`）。
- 五个构造子 `mkLiteral/mkSystematic/mkTeleological/mkHistorical/mkConstitutional`，
  每个带合法性定理 `*_legal`（保存输入面∧理由具名∧不内置采用权限）。
- `adoptableB`（采用门：具名理由∧法定权限）、`ruleBase`（只收可合法采用候选的
  规则 AST）。
- `InterpBranch`（branchId＋已采用候选表＋本支私有前提表）、`BranchDerivation`
  （结论＋引用前提表）、`derivationOk`（Bool 隔离门）↔ `DerivationWF`（Prop）、
  `DisjointPremises`、`ConflictOn`/`InterpAttack`/`BranchCompatible`、
  `PriorityPair`/`HasPriority`/`hasPriorityB`/`PriorityWF`/`resolvedByPriority`、
  `branchEach`（支路枚举：一候选一支，不合并不丢弃）。

## 三、本件证明 API 纪律（第一轮 CI 38104892437 的 32 错教训，全部按
v4.30 工具链源码/本仓已绿模块核实后改写）

- 合取命题不能 `:= rfl`（term-rfl 只对 Eq 目标点火）——改 `⟨rfl, …, rfl⟩` 逐分量；
- v4.30 core `Bool.and_eq_true (a b : Bool) : ((a && b) = true) = (a = true ∧ b = true)`
  是 **Prop 等式形**（非 Iff）——只作 `rw`/`simp only` 引理，不做 `.mp/.mpr`；
- 自家 Iff 定理的投影一律写显式 `Iff.mp`/`Iff.mpr`；
- v4.30 `List.mem_filter` 分量序＝⟨成员, 谓词⟩；`List.length_map` 只有一个显式参；
  `List.not_mem_nil` 不作函数式应用，用 `simp` 收；
- 前缀 `!` 优先级低于 `=`：`!p = true` 会被析成 `!(p = true)` 并插 decide 强转——
  一律带括号写 `((!p) = true)` 或经 `dsimp only`/`rw` 绕开。

**证**：本文件全部定理，零 sorry / 零自定义 axiom / 零 `True :=` 逃避。
CI 模块轮为唯一 Lean 权威。
-/

namespace JurisLean.Seams.UnifiedW4Interp

/-! ## T122：五解释构造（§3.1、§11.2 P066） -/

/-- §3.1 解释构造子恰五个：文义、体系、目的、历史、合宪。
§11.2 P066 修正注记：类推是**漏洞续造**构造子，不在五解释之列——本类型没有
第六个构造子，`five_methods_exhaust` 与 `five_methods_pairwise_ne` 把这一点
钉死为定理。 -/
inductive InterpMethod where
  | literal | systematic | teleological | historical | constitutional
deriving DecidableEq, Repr

/-- 解释效应（P066：构造子须保存新增/选择/保持效应）。 -/
inductive InterpEffect where
  | addRule | selectReading | keepReading
deriving DecidableEq, Repr

/-- 输出的具体有类型规则 AST（§3.1：解释构造子输出具体有类型规则 AST）。 -/
structure RuleAst where
  ruleId : Nat
  premises : List Nat
  conclusion : Nat
deriving DecidableEq, Repr

/-- 解释输入面：原文与上下文/理由材料（构造子保存输入文本——P066）。 -/
structure InterpInput where
  textId : Nat
  contextIds : List Nat
deriving DecidableEq, Repr

/-- §3.1 解释候选：方法＋保存的输入面＋目标＋范围＋效应＋具体规则 AST＋具名
理由（`reasonId`）＋法定权限（`authorityId`；`none`＝未获采用权限——构造不等于
采用）。 -/
structure InterpCandidate where
  candId : Nat
  method : InterpMethod
  input : InterpInput
  target : Nat
  scope : Nat
  effect : InterpEffect
  rule : RuleAst
  reasonId : Option Nat
  authorityId : Option Nat
deriving DecidableEq, Repr

/-- 文义解释构造子：输出带具名理由的候选；权限位恒为 `none`（使用方法≠采用）。 -/
def mkLiteral (candId : Nat) (i : InterpInput) (target scope : Nat)
    (e : InterpEffect) (r : RuleAst) (reason : Nat) : InterpCandidate :=
  { candId := candId, method := .literal, input := i, target := target,
    scope := scope, effect := e, rule := r, reasonId := some reason,
    authorityId := none }

/-- 体系解释构造子。 -/
def mkSystematic (candId : Nat) (i : InterpInput) (target scope : Nat)
    (e : InterpEffect) (r : RuleAst) (reason : Nat) : InterpCandidate :=
  { candId := candId, method := .systematic, input := i, target := target,
    scope := scope, effect := e, rule := r, reasonId := some reason,
    authorityId := none }

/-- 目的解释构造子。 -/
def mkTeleological (candId : Nat) (i : InterpInput) (target scope : Nat)
    (e : InterpEffect) (r : RuleAst) (reason : Nat) : InterpCandidate :=
  { candId := candId, method := .teleological, input := i, target := target,
    scope := scope, effect := e, rule := r, reasonId := some reason,
    authorityId := none }

/-- 历史解释构造子。 -/
def mkHistorical (candId : Nat) (i : InterpInput) (target scope : Nat)
    (e : InterpEffect) (r : RuleAst) (reason : Nat) : InterpCandidate :=
  { candId := candId, method := .historical, input := i, target := target,
    scope := scope, effect := e, rule := r, reasonId := some reason,
    authorityId := none }

/-- 合宪解释构造子（P066：受相应制度权限约束的解释路径；权限在采用时法定授予，
构造子本身不内置）。 -/
def mkConstitutional (candId : Nat) (i : InterpInput) (target scope : Nat)
    (e : InterpEffect) (r : RuleAst) (reason : Nat) : InterpCandidate :=
  { candId := candId, method := .constitutional, input := i, target := target,
    scope := scope, effect := e, rule := r, reasonId := some reason,
    authorityId := none }

/-- 五解释枚举的完备性：任一方法必是五者之一（类推不在其列——类型无第六构造子）。 -/
theorem five_methods_exhaust (m : InterpMethod) :
    m = InterpMethod.literal ∨ m = InterpMethod.systematic ∨
      m = InterpMethod.teleological ∨ m = InterpMethod.historical ∨
      m = InterpMethod.constitutional := by
  cases m with
  | literal => exact Or.inl rfl
  | systematic => exact Or.inr (Or.inl rfl)
  | teleological => exact Or.inr (Or.inr (Or.inl rfl))
  | historical => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | constitutional => exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

/-- 五方法两两相异（五解释构造子恰五，不是一格多挂的假五分）。 -/
theorem five_methods_pairwise_ne :
    InterpMethod.literal ≠ InterpMethod.systematic ∧
    InterpMethod.literal ≠ InterpMethod.teleological ∧
    InterpMethod.literal ≠ InterpMethod.historical ∧
    InterpMethod.literal ≠ InterpMethod.constitutional ∧
    InterpMethod.systematic ≠ InterpMethod.teleological ∧
    InterpMethod.systematic ≠ InterpMethod.historical ∧
    InterpMethod.systematic ≠ InterpMethod.constitutional ∧
    InterpMethod.teleological ≠ InterpMethod.historical ∧
    InterpMethod.teleological ≠ InterpMethod.constitutional ∧
    InterpMethod.historical ≠ InterpMethod.constitutional := by
  decide

/-- 文义解释合法性定理：构造子保存输入面（原文/上下文/目标/范围/效应——P066），
理由具名，且不内置采用权限（使用方法≠采用，§3.1）。 -/
theorem literal_legal (candId : Nat) (i : InterpInput) (target scope : Nat)
    (e : InterpEffect) (r : RuleAst) (reason : Nat) :
    (mkLiteral candId i target scope e r reason).input = i ∧
    (mkLiteral candId i target scope e r reason).target = target ∧
    (mkLiteral candId i target scope e r reason).scope = scope ∧
    (mkLiteral candId i target scope e r reason).effect = e ∧
    (mkLiteral candId i target scope e r reason).reasonId = some reason ∧
    (mkLiteral candId i target scope e r reason).authorityId = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- 体系解释合法性定理（同上六面）。 -/
theorem systematic_legal (candId : Nat) (i : InterpInput) (target scope : Nat)
    (e : InterpEffect) (r : RuleAst) (reason : Nat) :
    (mkSystematic candId i target scope e r reason).input = i ∧
    (mkSystematic candId i target scope e r reason).target = target ∧
    (mkSystematic candId i target scope e r reason).scope = scope ∧
    (mkSystematic candId i target scope e r reason).effect = e ∧
    (mkSystematic candId i target scope e r reason).reasonId = some reason ∧
    (mkSystematic candId i target scope e r reason).authorityId = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- 目的解释合法性定理（同上六面）。 -/
theorem teleological_legal (candId : Nat) (i : InterpInput) (target scope : Nat)
    (e : InterpEffect) (r : RuleAst) (reason : Nat) :
    (mkTeleological candId i target scope e r reason).input = i ∧
    (mkTeleological candId i target scope e r reason).target = target ∧
    (mkTeleological candId i target scope e r reason).scope = scope ∧
    (mkTeleological candId i target scope e r reason).effect = e ∧
    (mkTeleological candId i target scope e r reason).reasonId = some reason ∧
    (mkTeleological candId i target scope e r reason).authorityId = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- 历史解释合法性定理（同上六面）。 -/
theorem historical_legal (candId : Nat) (i : InterpInput) (target scope : Nat)
    (e : InterpEffect) (r : RuleAst) (reason : Nat) :
    (mkHistorical candId i target scope e r reason).input = i ∧
    (mkHistorical candId i target scope e r reason).target = target ∧
    (mkHistorical candId i target scope e r reason).scope = scope ∧
    (mkHistorical candId i target scope e r reason).effect = e ∧
    (mkHistorical candId i target scope e r reason).reasonId = some reason ∧
    (mkHistorical candId i target scope e r reason).authorityId = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- 合宪解释合法性定理（同上六面；P066：受制度权限约束——权限位不内置，
采用时另行法定授予）。 -/
theorem constitutional_legal (candId : Nat) (i : InterpInput) (target scope : Nat)
    (e : InterpEffect) (r : RuleAst) (reason : Nat) :
    (mkConstitutional candId i target scope e r reason).input = i ∧
    (mkConstitutional candId i target scope e r reason).target = target ∧
    (mkConstitutional candId i target scope e r reason).scope = scope ∧
    (mkConstitutional candId i target scope e r reason).effect = e ∧
    (mkConstitutional candId i target scope e r reason).reasonId = some reason ∧
    (mkConstitutional candId i target scope e r reason).authorityId = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- 采用门（§3.1：采用/排除解释仍须法定权限与具名理由）：候选可被采用当且仅当
具名理由与法定权限都在位。 -/
def adoptableB (c : InterpCandidate) : Bool :=
  c.reasonId.isSome && c.authorityId.isSome

/-- 采用门双侧互译。 -/
theorem adoptableB_iff (c : InterpCandidate) :
    adoptableB c = true ↔ c.reasonId.isSome = true ∧ c.authorityId.isSome = true := by
  simp [adoptableB]

/-- 无条件规则库：只收可合法采用候选的规则 AST（§3.1：未采用候选不进入无条件
规则库）。 -/
def ruleBase (cands : List InterpCandidate) : List RuleAst :=
  (cands.filter adoptableB).map (fun c => c.rule)

/-- 规则库健全：库中每条规则都来自某个可合法采用候选。 -/
theorem rule_base_only_adoptable (cands : List InterpCandidate) (r : RuleAst)
    (h : r ∈ ruleBase cands) :
    ∃ c ∈ cands, c.rule = r ∧ adoptableB c = true := by
  obtain ⟨x, hx, hrx⟩ := List.mem_map.mp h
  obtain ⟨hx_mem, hx_ad⟩ := List.mem_filter.mp hx
  exact ⟨x, hx_mem, hrx, hx_ad⟩

/-- 规则库排除（一般形）：候选 x 不可合法采用、且库源中无同规则候选时，x 的规则
不进库（未采用候选不进入无条件规则库）。 -/
theorem rule_base_omits_unadoptable (cands : List InterpCandidate) (x : InterpCandidate)
    (huniq : ∀ c ∈ cands, c.rule = x.rule → c = x)
    (hx : adoptableB x = false) :
    x.rule ∉ ruleBase cands := by
  intro hmem
  obtain ⟨c, hc_mem, hc_rule, hc_ad⟩ := rule_base_only_adoptable cands x.rule hmem
  have hcx : c = x := huniq c hc_mem hc_rule
  rw [hcx] at hc_ad
  rw [hx] at hc_ad
  exact Bool.noConfusion hc_ad

/-- **T122 原反例见证（独立保留）**：只跑了文义方法、无采用权限的候选——
理由具名但权限缺位，采用门拒绝。这就是 §3.1"不以使用了某方法自动证明解释
正确"的构造性反例：方法被使用了，解释仍不可采用。 -/
def unauthLiteral : InterpCandidate :=
  mkLiteral 99 ⟨100, [11]⟩ 7 1 .selectReading ⟨1, [1], 2⟩ 5

/-- 反例见证的采用门判定：拒绝。 -/
theorem unauth_not_adoptable : adoptableB unauthLiteral = false := rfl

/-- 反例见证的规则库判定：该候选的规则不进库（未采用候选不进入无条件规则库）。 -/
theorem unauth_rule_not_in_base : unauthLiteral.rule ∉ ruleBase [unauthLiteral] := by
  intro hmem
  obtain ⟨c, hc_mem, _hc_rule, hc_ad⟩ := rule_base_only_adoptable [unauthLiteral]
    unauthLiteral.rule hmem
  have hcu : c = unauthLiteral := by
    rcases List.mem_cons.mp hc_mem with h | h
    · exact h
    · exact absurd h (by simp)
  rw [hcu] at hc_ad
  rw [unauth_not_adoptable] at hc_ad
  exact Bool.noConfusion hc_ad

/-- §3.1 原反例的一般陈述：存在使用了解释方法（此见证为文义）却不可采用的
候选——"使用了某方法"绝不自动等于"解释正确/可采用"。 -/
theorem method_use_not_proof_of_correctness :
    ∃ c : InterpCandidate, c.method = InterpMethod.literal ∧ adoptableB c = false :=
  ⟨unauthLiteral, rfl, unauth_not_adoptable⟩

/-- 采用只增规则本身（P066：合宪等解释路径不附带宣告法源失效等额外权力——
采用一名候选进入规则库，库中新增的只有它的规则 AST）。 -/
theorem adoption_adds_only_rule (c : InterpCandidate) (cands : List InterpCandidate)
    (r : RuleAst) (h : r ∈ ruleBase (c :: cands)) :
    r = c.rule ∨ r ∈ ruleBase cands := by
  obtain ⟨x, hx_mem, hx_rule, _hx_ad⟩ := rule_base_only_adoptable (c :: cands) r h
  rcases List.mem_cons.mp hx_mem with hx_eq | hx_in
  · rw [hx_eq] at hx_rule
    exact Or.inl hx_rule.symm
  · exact Or.inr (List.mem_map.mpr
      ⟨x, List.mem_filter.mpr ⟨hx_in, _hx_ad⟩, hx_rule⟩)

/-! ## T123：解释分支（§3.1、§4.3） -/

/-- 解释分支：具来源支路＝本支已采用候选表＋本支私有前提（§3.1：法律允许数个
解释时保留每个具来源的解释支路）。 -/
structure InterpBranch where
  branchId : Nat
  adopted : List InterpCandidate
  privatePremises : List Nat
deriving DecidableEq, Repr

/-- 攻击靶点冲突：同一解释目标上输出不相容的两条规则 AST。 -/
def ConflictOn (x y : InterpCandidate) : Prop :=
  x.target = y.target ∧ x.rule ≠ y.rule

/-- 支路攻击：存在攻击支的已采用候选与被攻击支的已采用候选构成靶点冲突
（§4.3：攻击由具来源候选的实际构造给出，不从标签或结果需要倒填边——
本定义量化范围就是"已采用候选"，无标签通道）。 -/
def InterpAttack (A B : InterpBranch) : Prop :=
  ∃ x ∈ A.adopted, ∃ y ∈ B.adopted, ConflictOn x y

/-- 支路相容：互不攻击（§3.1：保留支路及相互攻击，相容即共存的许可面）。 -/
def BranchCompatible (A B : InterpBranch) : Prop := ¬ InterpAttack A B

/-- 支路攻击的相互性（§3.1"相互攻击"）：冲突谓词对称，故攻击对称。 -/
theorem interpAttack_symmetric (A B : InterpBranch) :
    InterpAttack A B ↔ InterpAttack B A := by
  constructor
  · rintro ⟨x, hx, y, hy, hconf⟩
    exact ⟨y, hy, x, hx, hconf.1.symm, hconf.2.symm⟩
  · rintro ⟨y, hy, x, hx, hconf⟩
    exact ⟨x, hx, y, hy, hconf.1.symm, hconf.2.symm⟩

/-- 相容即"无攻击"的定义桥（两侧互译）。 -/
theorem branchCompatible_iff (A B : InterpBranch) :
    BranchCompatible A B ↔ ¬ InterpAttack A B := Iff.rfl

/-- 相容对称。 -/
theorem branchCompatible_symmetric (A B : InterpBranch) :
    BranchCompatible A B ↔ BranchCompatible B A := by
  unfold BranchCompatible
  rw [interpAttack_symmetric]

/-- 具名优先对：法源规定的排除效力（superior 压 inferior；§3.1：边由具名法源
规定的排除效力产生）。 -/
structure PriorityPair where
  superior : Nat
  inferior : Nat
deriving DecidableEq, Repr

/-- 具名优先关系（Prop 形）。 -/
def HasPriority (pairs : List PriorityPair) (s n : Nat) : Prop :=
  ∃ p ∈ pairs, p.superior = s ∧ p.inferior = n

/-- 具名优先关系的 Bool 参考核（对 Nat 恒等式 decide）。 -/
def hasPriorityB (pairs : List PriorityPair) (s n : Nat) : Bool :=
  pairs.any (fun p => decide (p.superior = s) && decide (p.inferior = n))

/-- Bool 考核与 Prop 关系双侧互译。 -/
theorem hasPriorityB_iff (pairs : List PriorityPair) (s n : Nat) :
    hasPriorityB pairs s n = true ↔ HasPriority pairs s n := by
  constructor
  · intro h
    obtain ⟨p, hp, hpv⟩ := List.any_eq_true.mp h
    simp only [Bool.and_eq_true, decide_eq_true_iff] at hpv
    exact ⟨p, hp, hpv.1, hpv.2⟩
  · rintro ⟨p, hp, hs, hn⟩
    refine List.any_eq_true.mpr ⟨p, hp, ?_⟩
    simp [hs, hn]

/-- 优先良构：每条具名排除边都落在池中一对真冲突上（§3.1：相冲突的候选才进入
冲突实例；无冲突不造边）。 -/
def PriorityWF (pairs : List PriorityPair) (pool : List InterpCandidate) : Prop :=
  ∀ p ∈ pairs, ∃ x ∈ pool, ∃ y ∈ pool,
    x.candId = p.superior ∧ y.candId = p.inferior ∧ ConflictOn x y

/-- 优先边只有真冲突（良构的读出形）。 -/
theorem priority_wf_targets_conflict (pairs : List PriorityPair)
    (pool : List InterpCandidate) (hwf : PriorityWF pairs pool)
    (s n : Nat) (h : HasPriority pairs s n) :
    ∃ x ∈ pool, ∃ y ∈ pool, x.candId = s ∧ y.candId = n ∧ ConflictOn x y := by
  obtain ⟨p, hp_mem, hs, hn⟩ := h
  obtain ⟨x, hx, y, hy, hxid, hyid, hconf⟩ := hwf p hp_mem
  refine ⟨x, hx, y, hy, ?_, ?_, hconf⟩
  · exact hxid.trans hs
  · exact hyid.trans hn

/-- 优先解决后的采用集：池中未被任何在池候选（按具名边）压掉的候选
（§3.1 profile：被采纳候选排除其靶点）。 -/
def resolvedByPriority (pairs : List PriorityPair) (pool : List InterpCandidate) :
    List InterpCandidate :=
  pool.filter
    (fun c => !(pool.any
      (fun s => decide (s ≠ c) && hasPriorityB pairs s.candId c.candId)))

/-- 采用集确在池内。 -/
theorem resolved_subset_of_pool (pairs : List PriorityPair)
    (pool : List InterpCandidate) (c : InterpCandidate)
    (h : c ∈ resolvedByPriority pairs pool) : c ∈ pool :=
  (List.mem_filter.mp h).1

/-- 劣位被排除：若 superior ∈ 池、具名边 superior→inferior、二者不同候选且
superior 本身存活，则 inferior 不进采用集。 -/
theorem resolved_omits_inferior (pairs : List PriorityPair)
    (pool : List InterpCandidate) (x y : InterpCandidate)
    (hx : x ∈ pool) (_hy : y ∈ pool)
    (hprio : HasPriority pairs x.candId y.candId)
    (hxy : x ≠ y)
    (_hxres : x ∈ resolvedByPriority pairs pool) :
    y ∉ resolvedByPriority pairs pool := by
  intro hyres
  have hpred := (List.mem_filter.mp hyres).2
  simp only at hpred
  obtain ⟨p, hp_mem, hs, hn⟩ := hprio
  have h2 : hasPriorityB pairs x.candId y.candId = true :=
    Iff.mpr (hasPriorityB_iff pairs x.candId y.candId) ⟨p, hp_mem, hs, hn⟩
  have hany : pool.any
      (fun s => decide (s ≠ y) && hasPriorityB pairs s.candId y.candId) = true := by
    refine List.any_eq_true.mpr ⟨x, hx, ?_⟩
    dsimp only
    rw [decide_eq_true_iff.mpr hxy, h2]
  rw [hany] at hpred
  simp at hpred

/-- 优位存活（一般形）：x ∈ 池且池中无其他候选对 x 具名优先时，x 进采用集。 -/
theorem resolved_keeps_unopposed (pairs : List PriorityPair)
    (pool : List InterpCandidate) (x : InterpCandidate) (hx : x ∈ pool)
    (hanti : ∀ s ∈ pool, s ≠ x →
      ¬ HasPriority pairs s.candId x.candId) :
    x ∈ resolvedByPriority pairs pool := by
  refine List.mem_filter.mpr ⟨hx, ?_⟩
  dsimp only
  cases hany : pool.any
      (fun s => decide (s ≠ x) && hasPriorityB pairs s.candId x.candId) with
  | true =>
    obtain ⟨s, hs_mem, hs_val⟩ := List.any_eq_true.mp hany
    simp only [Bool.and_eq_true, decide_eq_true_iff] at hs_val
    exact absurd (Iff.mp (hasPriorityB_iff pairs s.candId x.candId) hs_val.2)
      (hanti s hs_mem hs_val.1)
  | false => rfl

/-- 见证候选 x：文义构造，目标 7，规则 AST#1，上下文材料 11，理由与权限具名。 -/
def candX : InterpCandidate :=
  { candId := 1, method := .literal, input := ⟨100, [11]⟩, target := 7,
    scope := 1, effect := .selectReading, rule := ⟨1, [1], 2⟩,
    reasonId := some 5, authorityId := some 9 }

/-- 见证候选 y：体系构造，同一目标 7，不相容规则 AST#2，上下文材料 22，
理由与权限具名。 -/
def candY : InterpCandidate :=
  { candId := 2, method := .systematic, input := ⟨100, [22]⟩, target := 7,
    scope := 1, effect := .selectReading, rule := ⟨2, [3], 4⟩,
    reasonId := some 6, authorityId := some 9 }

/-- **见证 1（具名优先收敛）**：真冲突 x–y 上唯一具名边 1→2 时，采用集恰为
{x}——同位冲突由具名法定胜负解决，不再保留劣位支（§3.1 profile）。 -/
theorem witness_superior_adopted :
    resolvedByPriority [⟨1, 2⟩] [candX, candY] = [candX] := rfl

/-- **见证 2（无法定胜负全保留）**：无任何具名边时，冲突对两支全保留、不作
选择（§3.1：同位无法定胜负的冲突……若法律要求报请，则产生报请路径而不作
这种选择）。 -/
theorem witness_no_priority_keeps_both :
    resolvedByPriority [] [candX, candY] = [candX, candY] := rfl

/-- 支路私有前提默认取该候选的上下文理由材料（输入面保存的下游读法）。 -/
def branchPremisesOf (c : InterpCandidate) : List Nat := c.input.contextIds

/-- 一候选一支的支路构造（具名顶层 def——lambda 内多行结构实例不采用）。 -/
def branchOf (c : InterpCandidate) : InterpBranch :=
  { branchId := c.candId, adopted := [c], privatePremises := branchPremisesOf c }

/-- 支路枚举（一候选一支，不合并不丢弃——§3.1：保留每个具来源的解释支路）。 -/
def branchEach (cands : List InterpCandidate) : List InterpBranch :=
  cands.map branchOf

/-- 枚举不丢弃：支路数＝候选数。 -/
theorem branchEach_count (cands : List InterpCandidate) :
    (branchEach cands).length = cands.length := by
  simp [branchEach]

/-- 支路 X：已采用 candX，私有前提＝材料 11。 -/
def branchX : InterpBranch :=
  { branchId := 1, adopted := [candX], privatePremises := [11] }

/-- 支路 Y：已采用 candY，私有前提＝材料 22。 -/
def branchY : InterpBranch :=
  { branchId := 2, adopted := [candY], privatePremises := [22] }

/-- **见证 3（支路保留）**：冲突对枚举出两支不同支路——法律允许数个解释时
分支层不作唯一化（采用层才按具名优先收敛，见 `witness_superior_adopted`）。 -/
theorem witness_two_branches_kept :
    branchEach [candX, candY] = [branchX, branchY] ∧ branchX ≠ branchY := by
  refine ⟨?_, ?_⟩
  · simp [branchEach, branchOf, candX, candY, branchX, branchY]
  · intro h
    have hprem := congrArg InterpBranch.privatePremises h
    simp [branchX, branchY] at hprem

/-! ### 分支隔离（T123 旗舰：一支的证明不能引用另一支的前提） -/

/-- 分支内推导：结论＋所引用前提表。 -/
structure BranchDerivation where
  derivationId : Nat
  conclusion : Nat
  citedPremises : List Nat
deriving DecidableEq, Repr

/-- 前提不相交：两支私有前提无公共材料。 -/
def DisjointPremises (A B : InterpBranch) : Prop :=
  ∀ p ∈ A.privatePremises, p ∉ B.privatePremises

/-- 分支隔离门（Prop 形）：推导引用的前提全在本支私有前提内。 -/
def DerivationWF (B : InterpBranch) (d : BranchDerivation) : Prop :=
  ∀ p ∈ d.citedPremises, p ∈ B.privatePremises

/-- 分支隔离门（Bool 参考核，对 List 成员 decide）。 -/
def derivationOk (B : InterpBranch) (d : BranchDerivation) : Bool :=
  d.citedPremises.all (fun p => decide (p ∈ B.privatePremises))

/-- 隔离门双侧互译：Bool 考核 ↔ Prop 良构。 -/
theorem derivationOk_iff (B : InterpBranch) (d : BranchDerivation) :
    derivationOk B d = true ↔ DerivationWF B d := by
  constructor
  · intro h p hp
    exact decide_eq_true_iff.mp (List.all_eq_true.mp h p hp)
  · intro h
    exact List.all_eq_true.mpr fun p hp => decide_eq_true_iff.mpr (h p hp)

/-- 本支前提内的推导被隔离门接受。 -/
theorem derivation_wf_accepts (B : InterpBranch) (d : BranchDerivation)
    (h : DerivationWF B d) : derivationOk B d = true :=
  Iff.mpr (derivationOk_iff B d) h

/-- 越界即拒（一般形）：引用前提只要有一个不在本支私有前提内，隔离门拒绝。 -/
theorem rejects_foreign_premise (B : InterpBranch) (d : BranchDerivation)
    (hf : ∃ p ∈ d.citedPremises, p ∉ B.privatePremises) :
    derivationOk B d = false := by
  obtain ⟨p, hp_mem, hp_out⟩ := hf
  by_contra hcon
  have htrue : derivationOk B d = true := by
    cases h : derivationOk B d with
    | true => exact rfl
    | false => exact absurd h hcon
  exact hp_out (Iff.mp (derivationOk_iff B d) htrue p hp_mem)

/-- **分支隔离定理（T123 旗舰）**：前提不相交的两支，一支的合法推导不可能引用
另一支的任何前提——否则立刻矛盾。这就是"一支的证明不能引用另一支前提"的
形式化：引用资格由本支私有前提限定，跨支前提在隔离门处结构性不可达。 -/
theorem branch_isolation (A B : InterpBranch) (d : BranchDerivation)
    (hdisj : DisjointPremises A B) (hwf : DerivationWF A d)
    (hforeign : ∃ p ∈ d.citedPremises, p ∈ B.privatePremises) : False := by
  obtain ⟨p, hp_mem, hp_B⟩ := hforeign
  exact hdisj p (hwf p hp_mem) hp_B

/-- 隔离定理的否定读形：前提不相交时，引用了 B 支前提的推导在 A 支**不是**
合法推导（结论不可携另一支前提进口）。 -/
theorem cross_citation_not_wf (A B : InterpBranch) (d : BranchDerivation)
    (hdisj : DisjointPremises A B)
    (hforeign : ∃ p ∈ d.citedPremises, p ∈ B.privatePremises) :
    ¬ DerivationWF A d :=
  fun hwf => branch_isolation A B d hdisj hwf hforeign

/-! ### T123 原反例见证（独立保留）：引用另支前提被拒 -/

/-- 反例推导：想引用**另一支（Y）**的私有前提 22 在 X 支得出结论 4。 -/
def crossDeriv : BranchDerivation :=
  { derivationId := 1, conclusion := 4, citedPremises := [22] }

/-- 见证：两支前提不相交。 -/
theorem witness_disjoint : DisjointPremises branchX branchY := by
  intro p hp hin
  have h11 : p ∈ [11] := hp
  have h22 : p ∈ [22] := hin
  simp at h11 h22
  exact absurd (h11.symm.trans h22) (by decide)

/-- 见证：两支确在真冲突（同目标、不相容规则）。 -/
theorem witness_conflict : ConflictOn candX candY := ⟨rfl, by decide⟩

/-- 见证：攻击关系在两支间成立且相互（§3.1"相互攻击"）。 -/
theorem witness_attack_both_ways :
    InterpAttack branchX branchY ∧ InterpAttack branchY branchX := by
  have h1 : InterpAttack branchX branchY :=
    ⟨candX, by simp [branchX], candY, by simp [branchY], witness_conflict⟩
  exact ⟨h1, Iff.mp (interpAttack_symmetric branchX branchY) h1⟩

/-- 见证：X 支自身的合法推导（引用本支前提 11）被隔离门接受。 -/
theorem witness_own_accepted : derivationOk branchX
    { derivationId := 0, conclusion := 2, citedPremises := [11] } = true := rfl

/-- **T123 原反例见证（独立保留）**：跨支推导被隔离门拒绝——Bool 考核判 false。 -/
theorem witness_cross_rejected : derivationOk branchX crossDeriv = false := rfl

/-- **T123 原反例见证（独立保留）**：跨支推导在 X 支不合法——
`branch_isolation` 的具体实例形态。 -/
theorem witness_cross_not_wf : ¬ DerivationWF branchX crossDeriv := by
  intro h
  exact branch_isolation branchX branchY crossDeriv witness_disjoint h
    ⟨22, by simp [crossDeriv], by simp [branchY]⟩

end JurisLean.Seams.UnifiedW4Interp
