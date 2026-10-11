import Mathlib.Tactic
import JurisLean.Seams.UnifiedW4Interp

/-!
W4 批次 T124–T127（解释一致性／三参照偏离／倾向分层／偏离报告）——六件套之
Lean 合同件。

出处（施工合同）：
- `docs/spec/20261007-统一法律数学模型_附录K_全量目标落实表.md:2553`（T124 行：
  §10.1,11.2：已采用解释表示保持；回流有权限/时际）、`:2554`（T125 行：§12.2：
  三参照距离及固定域/基准 Hausdorff 偏移界）、`:2555`（T126 行：§12.3,7.3：
  分层倾向实算、选择/迁移假设，不重复先验数据）、`:2556`（T127 行：§12.5：
  偏离报告完整比较/来源/不确定性，忠实投影；锚 I.0/I.4/I.11 与 J.0/J.6/J.12–14；
  各行原反例独立保留）。
- `docs/spec/20261007-统一法律数学模型_全量施工方案.md:624–639`（§10.1：已采用
  解释经表示层投影不漂移；实际事件序列不可改，撤销/回流只追加具名事件，不删除
  发生记录）、`:616–620`（§9.4：规范回流必须是有权限、有程序、有生效条件的事件）、
  `:1136–1156`（§12.2：SELF/PEER/UPPER 三参照各自先过可比性规则得参照集合 S，
  `dev(x,S)=inf_{s∈S}d(x,s)` 有限为 min；三角不等式给 `|dev(x,S)−dev(y,S)|≤d(x,y)`，
  参照集合变化 `|dev(x,S)−dev(x,T)|≤d_H(S,T)`；**空 S 是无比较基准，不能填 0 偏离**；
  结构偏离/规范不一致/经验异常三种报告分别给依据，不能用距离大判违法）、
  `:1158–1174`（§12.3：T126 按法院/法官/地区×时期/法版本分层；同案族去重；按层
  实算倾向；进入预测必须满足 §7.3 的选择/迁移机制，**不能写入法源**）、
  `:449–457`（§7.3：同一训练标签不能先调整权重又作为新的独立个案证据重复使用；
  一般似然必须含选择）、`:1195–1201`（§12.5：报告逐项保留比较对象、差异事实、
  规范对应、误差/样本边界和引用定位；生成文句不能抹掉原始 status）。

六件套分工：本件＝新合同。直接消费已绿模块
`JurisLean.Seams.UnifiedW4Interp`（T122/T123：`InterpCandidate`/`adoptableB`/
`ruleBase`/`branchEach`/`branch_isolation`——T124 的表示层正是其采用层原像的
下游投影）。Python 入口 `tools/full_math/implementation/deviation_ref.py`、
独立 checker `tools/full_math/implementation/deviation_check.py`（只共享冻结
载体、谓词全部内联重实现）、下游消费经既有 interp 层入口
（`tools/unified_math_v2/unified/pipeline.py:291` 的 `build_interp_layer`），
正反例 `tools/full_math/implementation_tests/test_deviation_w4.py`，合成回执
见报告 `.local/agent_P_w4_t124_report.md`。

## 一、法律语义（人话）

- **T124（解释一致性）**：已采用的解释序列化为表示层记录后，表示层读数＝采用层
  原像（不漂移：`repReadings = ruleBase`，记录逐字段保真）；未采用候选的"读数"
  进不了表示层（T122 采用门同一道门）。**回流（§9.4）**：已采用解释流回规范层
  的事件必须带具名权限与生效时点——无权限回流被拒、时点越窗被拒；被拒事件不
  改日志（append-only：接受才追加，历史不重写——§10.1 撤销只追加具名事件）。
- **T125（三参照偏离）**：当前读数 x 对三参照（本人先例 SELF／同级同行 PEER／
  上级裁判 UPPER）各自过可比性与非空门后取 `dev(x,S)=min_{s∈S}|x−s|`（ℚ 值；
  有限集为 min，空集无基准拒填 0）。距离结构：非负、可达（在参照点取到）、对
  x 的 Lipschitz（`|dev(x,S)−dev(y,S)|≤|x−y|`）；参照集变化的 Hausdorff 界
  `|dev(x,S)−dev(x,T)|≤d_H(S,T)`；**固定域平移界（本件核心）**：域平移 δ 后
  `d_H(S,S+δ)≤|δ|`，含闭式数值例 S=[0,2]、δ=1/2 时 d_H=1/2（恰等）。
- **T126（倾向分层）**：层＝有限分层键（法院/法官/地区×时期/法版本的有限编码），
  各层倾向＝层内计数比 s/(s+f)（ℚ 精确，不浮点）。**不重复先验数据合同**：
  倾向计算输入类型只含分层观测表（无先验通道），先验表 (α,β) 另列分型——同一
  观测 (3/1) 的倾向实算是 3/4，混入 (1,1) 先验的后验均值是 2/3，二者可区分，
  混入即被检验层拒绝（§7.3 同一标签不重复使用）。**选择/迁移假设显式**：
  层间比较门要求选择机制已建模、迁移支持覆盖已具名（显式假设参数，不在定理内
  隐含；无名假设即拒——§12.3 进入预测须满足 §7.3 机制，倾向不写入法源——
  用途分型无"法源"构造子）。
- **T127（偏离报告）**：报告记录打包三参照距离读数＋具名来源标注（结构偏离/
  规范不一致/经验异常三分型，分别给依据）＋不确定性区间（ℚ 端点）。**忠实投影
  定理**：报告读数＝底层计算原像（构造器不重算不漂移；重算值与投影值不一致的
  报告被门拒绝）；**完整性**：全部实际偏离来源逐项枚举进报告，或具名列残余
  （有来源未列且残余未具名 → 门拒）；生成文句不抹掉原始 status。

## 二、数学对象

- T124：`RepRecord`（已采用候选的冻结序列化）＋`recordOf`/`recordRule`/
  `recordAdoptableB`（逐字段保真）＋`repLog`（表示层日志＝采用门过滤的冻结
  原像）＋`repReadings`（表示层读数＝采用层 `ruleBase`，逐点相等）＋
  `repOkB`（不漂移门）＋`ReflowEvent`/`ReflowWindow`/`authorityOkB`/
  `inWindowB`/`reflowOkB`（权限×时点门）＋`applyReflow`（append-only 回流）。
- T125：`devMinList`/`devMaxList`（有限 ℚ 表 min/max，显式递归）＋`devOf`
  （三参照偏离=min|x−s|）＋`dHaus`（Hausdorff=max-min）＋`RefKind`/`ThreeRefs`
  ＋`Comparability`/`comparableB`/`refAdmitB`（可比×非空门）＋
  `hausdorff_shift_bound`（域平移偏移界）＋`devOf_lipschitz`/
  `dev_set_change_bound`（§12.2 两条联合变化界）＋闭式数值例见证。
- T126：`StratObs`（层键×成功/失败计数）＋`obsTotal`/`obsOkB`/`propensity`
  （ℚ 计数比）＋`StratTable`/`buildStratTable`（只由观测表构造）＋`PriorTable`
  （先验另列分型）＋`PropensityAssumptions`/`assumptionsNamed`/
  `comparisonGateB`（显式假设门）＋`StratUse`（用途分型，无法源构造子）＋
  `witness_prior_not_double_used`（3/4 ≠ 2/3 见证）＋
  `witness_mixed_in_detectable`（混入 (1,0) 后 4/5 ≠ 3/4）。
- T127：`DevKind`（结构/规范/经验三分型）＋`DevSource`（具名来源）＋`Uncert`
  （ℚ 区间）＋`DeviationReport`/`mkReport`（打包构造器）＋`reportOkB`（忠实
  投影门）＋`coverageOkB`（完整性门：逐项枚举∨残余具名）＋
  `flagshipReport`＋旗舰定理 `w4_deviation_flagship`（四件合同合取）。

## 三、本件证明 API 纪律（全部按 v4.30 工具链源码/本仓已绿模块核实）

- 合取命题不能 `:= rfl`——`⟨rfl, …, rfl⟩` 逐分量；
- v4.30 core `Bool.and_eq_true` 是 Prop 等式形——只作 `rw`/`simp only` 引理；
  自家 ∀ 型 Iff 定理投影先全参应用再 `Iff.mp/mpr`；
- v4.30 core：`decide_eq_true_iff`（PropLemmas:510，Iff）、
  `decide_eq_false_iff_not`（SimpLemmas:402，Iff）、`List.mem_filter`
  （Init/Data/List/Lemmas:1309，⟨成员,谓词⟩）、`List.mem_map`（:1124）、
  `List.all_eq_true`（:576，∀ 形成员谓词）、`List.exists_mem_of_ne_nil`
  （:393）、`Nat.not_le`（Init/Data/Nat/Basic:444，protected）、
  `Nat.le_add_right`（:374）；
- ℚ 距离用 Mathlib `abs_add_le`（三角不等式——本仓已绿 WeightedSupNorm:59
  同款用法）、`abs_le.mpr ⟨_,_⟩`（MixedExtension:150 同款）、`abs_nonneg`、
  `rw [← abs_neg, neg_sub]`（|y−x|=|x−y|，WeightedSupNorm:76 同款）；
  min/max 系（`min_le_left`/`min_eq_left`/`le_max_left`/`max_le`/`le_total`/
  `max_comm` 等）在 Mathlib/Order/Defs/LinearOrder.lean；`div_nonneg`/
  `div_le_one (0<b)`/`Nat.cast_le`/`Nat.cast_nonneg` 均按源码核名；
- 递归 `devMinList`/`devMaxList` 的归纳一律 `cases` 出 [a] 与 a::b::rest
  两支（单支匹配 `[a]` 的方程形），`simp only [devMinList]` 用方程组展开；
- 数值见证用 `norm_num [ … ]`（min/max/abs/÷ 对字面 ℚ 可判定）。

**证**：本文件全部定理，零 sorry / 零自定义 axiom / 零 `True :=` 逃避。
CI 模块轮为唯一 Lean 权威。
-/

namespace JurisLean.Seams.UnifiedW4Deviation

open JurisLean.Seams.UnifiedW4Interp

/-! ## T124：解释一致性——已采用解释表示保持 ＋ 回流权限/时际（§10.1、§11.2、§9.4） -/

/-- 表示层记录：已采用候选的冻结序列化（§10.1 表示保持——记录逐字段保存原像：
方法、规则 AST、具名理由、法定权限）。 -/
structure RepRecord where
  candId : Nat
  method : InterpMethod
  rule : RuleAst
  reasonId : Option Nat
  authorityId : Option Nat
deriving DecidableEq, Repr

/-- 序列化门（fail-fast 的合同面）：记录由候选逐字段投影。 -/
def recordOf (c : InterpCandidate) : RepRecord :=
  { candId := c.candId, method := c.method, rule := c.rule,
    reasonId := c.reasonId, authorityId := c.authorityId }

/-- 表示层读数（规则面）：记录读出的规则 AST。 -/
def recordRule (r : RepRecord) : RuleAst := r.rule

/-- 表示层读数（可采用面）：记录层对原像可采用性的读数——与采用层 `adoptableB`
同型同值。 -/
def recordAdoptableB (r : RepRecord) : Bool :=
  r.reasonId.isSome && r.authorityId.isSome

/-- **字段保真定理**：序列化记录的规则读数＝采用层原像的规则（不漂移）。 -/
theorem record_rule_faithful (c : InterpCandidate) :
    recordRule (recordOf c) = c.rule := rfl

/-- **可采用面保真定理**：记录层的可采用读数与采用层门逐点一致。 -/
theorem record_adoptable_matches (c : InterpCandidate) :
    recordAdoptableB (recordOf c) = adoptableB c := rfl

/-- 表示层日志：只收采用门通过的候选（§3.1 未采用候选不进入无条件规则库的
下游面——日志记录就是原像本身冻结）。 -/
def repLog (cands : List InterpCandidate) : List InterpCandidate :=
  cands.filter adoptableB

/-- 表示层读数：日志的规则投影。 -/
def repReadings (cands : List InterpCandidate) : List RuleAst :=
  (repLog cands).map (fun c => c.rule)

/-- **表示保持定理（T124 第一面）**：表示层读数＝采用层规则库原像（逐点相等，
不漂移——`repLog` 的过滤与 `ruleBase` 的过滤同门同序）。 -/
theorem rep_readings_match_rule_base (cands : List InterpCandidate) :
    repReadings cands = ruleBase cands := rfl

/-- 日志只收可合法采用候选：日志成员必有采用门通过 ∧ 在源表内。 -/
theorem rep_log_only_adoptable (cands : List InterpCandidate) (c : InterpCandidate)
    (h : c ∈ repLog cands) : c ∈ cands ∧ adoptableB c = true :=
  List.mem_filter.mp h

/-- 日志成员的规则在读数里：表示层读到的每条规则都是某个已采用候选的规则。 -/
theorem rep_log_rule_is_preimage (cands : List InterpCandidate) (c : InterpCandidate)
    (h : c ∈ repLog cands) : c.rule ∈ ruleBase cands := by
  have h2 := rep_log_only_adoptable cands c h
  exact List.mem_map.mpr ⟨c, List.mem_filter.mpr ⟨h2.1, h2.2⟩, rfl⟩

/-- 未采用候选不进表示层日志（T122 反例的下游面一般形）。 -/
theorem rep_log_omits_unadoptable (cands : List InterpCandidate) (x : InterpCandidate)
    (hx : adoptableB x = false) : x ∉ repLog cands := by
  intro h
  have hpred := (List.mem_filter.mp h).2
  rw [hx] at hpred
  exact Bool.noConfusion hpred

/-- 不漂移门：表示层读数与采用层原像不一致即拒。 -/
def repOkB (cands : List InterpCandidate) (claimed : List RuleAst) : Bool :=
  decide (repReadings cands = claimed)

/-- 不漂移门拒绝（一般形）：读数被篡改即 false。 -/
theorem rep_gate_rejects_drift (cands : List InterpCandidate) (claimed : List RuleAst)
    (h : repReadings cands ≠ claimed) : repOkB cands claimed = false := by
  have hd : (decide (repReadings cands = claimed) : Bool) = false :=
    decide_eq_false_iff_not.mpr h
  simp [repOkB, hd]

/-- **T124 原反例见证（独立保留）**：无采用权限的候选（只跑了文义方法）——
其"读数"进不了表示层：日志为空，声称读数为 [其规则] 被不漂移门拒绝。 -/
def unauthCand : InterpCandidate :=
  mkLiteral 99 ⟨100, [11]⟩ 7 1 .selectReading ⟨1, [1], 2⟩ 5

/-- 反例候选不可采用（权限缺位）。 -/
theorem unauthCand_not_adoptable : adoptableB unauthCand = false := rfl

/-- 反例见证：未采用候选的日志为空，且声称读数 [其规则] 被拒。 -/
theorem witness_unadopted_not_readable :
    repReadings [unauthCand] = [] ∧ repOkB [unauthCand] [unauthCand.rule] = false := by
  refine ⟨?_, ?_⟩
  · simp [repReadings, repLog, unauthCand_not_adoptable]
  · exact rep_gate_rejects_drift _ _ (by
      have hempty : repReadings [unauthCand] = ([] : List RuleAst) := by
        simp [repReadings, repLog, unauthCand_not_adoptable]
      rw [hempty]
      simp)

/-- 回流事件（§9.4：规范回流必须是有权限、有程序、有生效条件的事件——本件
合同面取权限与时点两个必需面）。 -/
structure ReflowEvent where
  eventId : Nat
  candId : Nat
  authorityId : Option Nat
  atDay : Nat
deriving DecidableEq, Repr

/-- 回流生效窗（§10.1 asOf 面：生效条件的有限窗）。 -/
structure ReflowWindow where
  openDay : Nat
  closeDay : Nat
deriving DecidableEq, Repr

/-- 权限门：回流事件必须带具名权限。 -/
def authorityOkB (e : ReflowEvent) : Bool := e.authorityId.isSome

/-- 时点门：生效时点必须在窗内（时点越窗拒）。 -/
def inWindowB (w : ReflowWindow) (e : ReflowEvent) : Bool :=
  decide (w.openDay ≤ e.atDay) && decide (e.atDay ≤ w.closeDay)

/-- 回流门＝权限∧时点。 -/
def reflowOkB (w : ReflowWindow) (e : ReflowEvent) : Bool :=
  authorityOkB e && inWindowB w e

/-- **无权限回流被拒**（§9.4：回流必须是有权限事件）。 -/
theorem reflow_rejects_unauthorized (w : ReflowWindow) (e : ReflowEvent)
    (h : e.authorityId = none) : reflowOkB w e = false := by
  simp [reflowOkB, authorityOkB, h]

/-- **时点越窗回流被拒**。 -/
theorem reflow_rejects_out_of_window (w : ReflowWindow) (e : ReflowEvent)
    (h : e.atDay < w.openDay) : reflowOkB w e = false := by
  have hd : (decide (w.openDay ≤ e.atDay) : Bool) = false :=
    decide_eq_false_iff_not.mpr (Nat.not_le.mpr h)
  simp [reflowOkB, inWindowB, hd]

/-- 有权限且在窗内的回流被接受。 -/
theorem reflow_accepts_authorized_in_window (w : ReflowWindow) (e : ReflowEvent)
    (ha : e.authorityId.isSome = true) (hlo : w.openDay ≤ e.atDay)
    (hhi : e.atDay ≤ w.closeDay) : reflowOkB w e = true := by
  have h1 : (decide (w.openDay ≤ e.atDay) : Bool) = true := decide_eq_true_iff.mpr hlo
  have h2 : (decide (e.atDay ≤ w.closeDay) : Bool) = true := decide_eq_true_iff.mpr hhi
  simp [reflowOkB, inWindowB, authorityOkB, ha, h1, h2]

/-- 回流应用（§10.1：撤销/回流只追加具名事件，不删除发生记录——append-only）。 -/
def applyReflow (log : List InterpCandidate) (w : ReflowWindow) (e : ReflowEvent)
    (c : InterpCandidate) : List InterpCandidate :=
  if reflowOkB w e = true then log ++ [c] else log

/-- 被拒回流不改日志（历史不重写）。 -/
theorem reflow_rejected_keeps_log (log : List InterpCandidate) (w : ReflowWindow)
    (e : ReflowEvent) (c : InterpCandidate) (h : reflowOkB w e = false) :
    applyReflow log w e c = log := by
  simp [applyReflow, h]

/-- 接受的回流是纯追加（存在后缀使新日志＝旧日志＋后缀；具体形即 `++ [c]`）。 -/
theorem reflow_accepted_appends (log : List InterpCandidate) (w : ReflowWindow)
    (e : ReflowEvent) (c : InterpCandidate) (h : reflowOkB w e = true) :
    applyReflow log w e c = log ++ [c] := by
  simp [applyReflow, h]

/-- **T124 独立结论定理（解释一致性）**：已采用候选的表示层——读数＝规则库
原像、原像进日志、有权限在窗内回流接受且纯追加。 -/
theorem t124_interp_consistency (cands : List InterpCandidate) (c : InterpCandidate)
    (hc : adoptableB c = true)
    (w : ReflowWindow) (e : ReflowEvent)
    (ha : e.authorityId.isSome = true) (hlo : w.openDay ≤ e.atDay)
    (hhi : e.atDay ≤ w.closeDay) :
    repReadings (c :: cands) = ruleBase (c :: cands) ∧
    c ∈ repLog (c :: cands) ∧
    reflowOkB w e = true ∧
    applyReflow (repLog (c :: cands)) w e c = repLog (c :: cands) ++ [c] := by
  refine ⟨rep_readings_match_rule_base _, ?_, ?_, ?_⟩
  · exact List.mem_filter.mpr ⟨by simp, hc⟩
  · exact reflow_accepts_authorized_in_window w e ha hlo hhi
  · exact reflow_accepted_appends _ w e c
      (reflow_accepts_authorized_in_window w e ha hlo hhi)

/-! ## T125：三参照偏离——ℚ 值距离结构 ＋ 固定域/基准 Hausdorff 偏移界（§12.2） -/

/-- 有限 ℚ 表的最小值（空表回退 0；合同面由非空门另行把关）。 -/
def devMinList : List ℚ → ℚ
  | [] => 0
  | [a] => a
  | a :: b :: rest => min a (devMinList (b :: rest))

/-- 有限 ℚ 表的最大值（同上）。 -/
def devMaxList : List ℚ → ℚ
  | [] => 0
  | [a] => a
  | a :: b :: rest => max a (devMaxList (b :: rest))

/-- min 可达成员（非空表的最小值是表中元素——可达性引理）。 -/
theorem devMinList_mem : ∀ (l : List ℚ), l ≠ [] → ∃ v, v ∈ l ∧ devMinList l = v := by
  intro l
  induction l with
  | nil => intro h; exact absurd rfl h
  | cons a rest ih =>
    intro _
    cases rest with
    | nil => exact ⟨a, by simp, by simp [devMinList]⟩
    | cons b rest2 =>
      obtain ⟨v, hv_mem, hv_eq⟩ := ih (by simp)
      rcases le_total a v with h | h
      · refine ⟨min a v, ?_, ?_⟩
        · rw [min_eq_left h]; simp
        · simp only [devMinList, hv_eq, min_eq_left h]
      · refine ⟨min a v, ?_, ?_⟩
        · rw [min_eq_right h]; simp
        · simp only [devMinList, hv_eq, min_eq_right h]

/-- 成员上界：表中任意元素 ≥ 最小值。 -/
theorem devMinList_le_of_mem : ∀ (l : List ℚ) (v : ℚ), v ∈ l → devMinList l ≤ v := by
  intro l
  induction l with
  | nil => intro v hv; simp at hv
  | cons a rest ih =>
    intro v hv
    cases rest with
    | nil =>
      simp at hv
      subst hv
      simp [devMinList]
    | cons b rest2 =>
      simp only [devMinList]
      rcases List.mem_cons.mp hv with h | h
      · subst h; exact min_le_left _ _
      · exact min_le_right _ _ (ih v h)

/-- 成员下界：表中任意元素 ≤ 最大值。 -/
theorem devMaxList_ge_of_mem : ∀ (l : List ℚ) (v : ℚ), v ∈ l → v ≤ devMaxList l := by
  intro l
  induction l with
  | nil => intro v hv; simp at hv
  | cons a rest ih =>
    intro v hv
    cases rest with
    | nil =>
      simp at hv
      subst hv
      simp [devMaxList]
    | cons b rest2 =>
      simp only [devMaxList]
      rcases List.mem_cons.mp hv with h | h
      · subst h; exact le_max_left _ _
      · exact le_max_right _ _ (ih v h)

/-- 全员上界则 max 上界（空表用 0 ≤ B 兜底）。 -/
theorem devMaxList_le_of_forall : ∀ (l : List ℚ) (B : ℚ), (∀ v ∈ l, v ≤ B) →
    0 ≤ B → devMaxList l ≤ B := by
  intro l
  induction l with
  | nil => intro B _ h0; simpa [devMaxList] using h0
  | cons a rest ih =>
    intro B hall h0
    cases rest with
    | nil => simpa [devMaxList] using hall a (by simp)
    | cons b rest2 =>
      simp only [devMaxList]
      exact max_le (hall a (by simp)) (ih B (fun v hv => hall v (by simp)) h0)

/-- 全员非负则 min 非负。 -/
theorem devMinList_nonneg : ∀ (l : List ℚ), (∀ v ∈ l, 0 ≤ v) → 0 ≤ devMinList l := by
  intro l
  induction l with
  | nil => intro _; simp [devMinList]
  | cons a rest ih =>
    intro hall
    cases rest with
    | nil => simpa [devMinList] using hall a (by simp)
    | cons b rest2 =>
      simp only [devMinList]
      exact le_min (hall a (by simp)) (ih (fun v hv => hall v (by simp)))

/-- §12.2 偏离：`dev(x,S)=min_{s∈S}|x−s|`（ℚ 值；有限参照集为 min；
空集回退 0 但由非空门拒填——见 `devReadingOkB`）。 -/
def devOf (x : ℚ) (S : List ℚ) : ℚ := devMinList (S.map (fun s => |x - s|))

/-- 偏离非负。 -/
theorem devOf_nonneg (x : ℚ) (S : List ℚ) : 0 ≤ devOf x S :=
  devMinList_nonneg _ (fun v hv => by
    obtain ⟨s, _, hs⟩ := List.mem_map.mp hv
    rw [hs]; exact abs_nonneg _)

/-- 偏离上界面：对任意参照点 s ∈ S，dev ≤ |x−s|。 -/
theorem devOf_le_of_mem (x : ℚ) (S : List ℚ) (s : ℚ) (h : s ∈ S) :
    devOf x S ≤ |x - s| :=
  devMinList_le_of_mem _ _ (List.mem_map.mpr ⟨s, h, rfl⟩)

/-- 偏离可达面（有限集 min 取到）：非空 S 时存在参照点使 dev 恰等于其距离。 -/
theorem devOf_attained (x : ℚ) (S : List ℚ) (hS : S ≠ []) :
    ∃ s ∈ S, devOf x S = |x - s| := by
  have hmap : (S.map (fun s => |x - s|)) ≠ [] := by
    cases S with
    | nil => exact absurd rfl hS
    | cons a rest => simp
  obtain ⟨v, hv_mem, hv_eq⟩ := devMinList_mem _ hmap
  obtain ⟨s, hs, hs_eq⟩ := List.mem_map.mp hv_mem
  have hs_eq' : |x - s| = v := hs_eq
  refine ⟨s, hs, ?_⟩
  have h1 : devOf x S = v := hv_eq
  rw [h1, hs_eq']

/-- ℚ 距离三角不等式（Mathlib `abs_add_le`——本仓已绿同款）。 -/
theorem dev_triangle (x y s : ℚ) : |x - s| ≤ |x - y| + |y - s| := by
  have h : x - s = (x - y) + (y - s) := by ring
  rw [h]
  exact abs_add_le _ _

/-- 过渡点放行：dev(x,S) ≤ |x−t| + dev(t,S)（§12.2 三角不等式的偏离面）。 -/
theorem devOf_le_add_devOf (x t : ℚ) (S : List ℚ) (hS : S ≠ []) :
    devOf x S ≤ |x - t| + devOf t S := by
  obtain ⟨s₀, hs₀mem, hs₀att⟩ := devOf_attained t S hS
  have h1 : devOf x S ≤ |x - s₀| := devOf_le_of_mem x S s₀ hs₀mem
  have h2 : |x - s₀| ≤ |x - t| + |t - s₀| := dev_triangle x t s₀
  rw [hs₀att]
  linarith

/-- **对读数点的 Lipschitz 界**：`|dev(x,S)−dev(y,S)|≤|x−y|`
（§12.2：由三角不等式，对任意 s 有 d(x,s)≤d(x,y)+d(y,s)，取 inf 再交换 x,y）。 -/
theorem devOf_lipschitz (x y : ℚ) (S : List ℚ) (hS : S ≠ []) :
    |devOf x S - devOf y S| ≤ |x - y| := by
  have h1 : devOf x S ≤ |x - y| + devOf y S := devOf_le_add_devOf x y S hS
  have h2 : devOf y S ≤ |y - x| + devOf x S := devOf_le_add_devOf y x S hS
  have hsy : |y - x| = |x - y| := by rw [← abs_neg, neg_sub]
  rw [hsy] at h2
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith

/-- §12.2 Hausdorff 距离（ℚ 值；有限集 max-min）。 -/
def dHaus (S T : List ℚ) : ℚ :=
  max (devMaxList (S.map (fun s => devOf s T)))
    (devMaxList (T.map (fun t => devOf t S)))

/-- Hausdorff 对称。 -/
theorem dHaus_symm (S T : List ℚ) : dHaus S T = dHaus T S := by
  simp only [dHaus]
  exact max_comm _ _

/-- **参照集变化界**：`|dev(x,S)−dev(x,T)|≤d_H(S,T)`
（§12.2：双向用任意 ε 近邻——有限集取到）。 -/
theorem dev_set_change_bound (x : ℚ) (S T : List ℚ) (hS : S ≠ []) (hT : T ≠ []) :
    |devOf x S - devOf x T| ≤ dHaus S T := by
  obtain ⟨t*, htmem, htatt⟩ := devOf_attained x T hT
  have h1 : devOf x S ≤ |x - t*| + devOf t* S := devOf_le_add_devOf x t* S hS
  have h2 : devOf t* S ≤ devMaxList (T.map (fun t => devOf t S)) :=
    devMaxList_ge_of_mem _ _ (List.mem_map.mpr ⟨t*, htmem, rfl⟩)
  have h3 : |x - t*| = devOf x T := htatt.symm
  have hmax : devMaxList (T.map (fun t => devOf t S)) ≤ dHaus S T := le_max_right _ _
  obtain ⟨s*, hsmem, hsatt⟩ := devOf_attained x S hS
  have h1' : devOf x T ≤ |x - s*| + devOf s* T := devOf_le_add_devOf x s* T hT
  have h2' : devOf s* T ≤ devMaxList (S.map (fun s => devOf s T)) :=
    devMaxList_ge_of_mem _ _ (List.mem_map.mpr ⟨s*, hsmem, rfl⟩)
  have h3' : |x - s*| = devOf x S := hsatt.symm
  have hmax' : devMaxList (S.map (fun s => devOf s T)) ≤ dHaus S T := le_max_left _ _
  refine abs_le.mpr ⟨?_, ?_⟩
  · rw [h3] at h1
    linarith
  · rw [h3'] at h1'
    linarith

/-- **固定域平移 Hausdorff 偏移界（T125 核心）**：域 S 平移 δ 后
`d_H(S,S+δ)≤|δ|`（§12.2 固定域/基准的偏移界——偏移常数即平移量）。 -/
theorem hausdorff_shift_bound (S : List ℚ) (δ : ℚ) :
    dHaus S (S.map (fun t => t + δ)) ≤ |δ| := by
  have h0 : (0 : ℚ) ≤ |δ| := abs_nonneg δ
  have h1 : devMaxList (S.map (fun s => devOf s (S.map (fun t => t + δ)))) ≤ |δ| := by
    refine devMaxList_le_of_forall _ _ ?_ h0
    intro v hv
    obtain ⟨s, hs, hs_eq⟩ := List.mem_map.mp hv
    have hv' : devOf s (S.map (fun t => t + δ)) = v := hs_eq
    rw [← hv']
    have hmem : s + δ ∈ S.map (fun t => t + δ) := List.mem_map.mpr ⟨s, hs, rfl⟩
    have hdev : devOf s (S.map (fun t => t + δ)) ≤ |s - (s + δ)| :=
      devOf_le_of_mem s _ _ hmem
    have hex : s - (s + δ) = -δ := by ring
    rw [hex, abs_neg] at hdev
    exact hdev
  have h2 : devMaxList ((S.map (fun t => t + δ)).map (fun t => devOf t S)) ≤ |δ| := by
    refine devMaxList_le_of_forall _ _ ?_ h0
    intro v hv
    obtain ⟨t, ht, ht_eq⟩ := List.mem_map.mp hv
    have hv' : devOf t S = v := ht_eq
    obtain ⟨s, hs, hst⟩ := List.mem_map.mp ht
    have hst' : s + δ = t := hst
    rw [← hv', ← hst']
    have hdev : devOf (s + δ) S ≤ |(s + δ) - s| := devOf_le_of_mem _ S s hs
    have hex : (s + δ) - s = δ := by ring
    rw [hex] at hdev
    exact hdev
  simp only [dHaus]
  exact max_le h1 h2

/-- **闭式数值例**：S=[0,2]、δ=1/2 → 平移域 [1/2, 5/2]，d_H = 1/2（恰等——
偏移界紧）。 -/
theorem witness_hausdorff_shift_half :
    dHaus [(0 : ℚ), 2] [(1 : ℚ) / 2, 5 / 2] = 1 / 2 := by
  norm_num [dHaus, devOf, devMaxList, devMinList]

/-- §12.2 三参照：本人先例 SELF、同级同行 PEER、上级裁判 UPPER。 -/
inductive RefKind where
  | self | peer | upper
deriving DecidableEq, Repr

/-- 三参照集合（各自先过可比性与非空门，见 `refAdmitB`）。 -/
structure ThreeRefs where
  selfSet : List ℚ
  peerSet : List ℚ
  upperSet : List ℚ
deriving DecidableEq, Repr

/-- 可比性门输入（§12.2：同法域/版本/程序/争点及事实可比性规则——合成域
有限编码为具名 Bool 面）。 -/
structure Comparability where
  sameDomain : Bool
  sameVersion : Bool
  sameProcedure : Bool
  sameIssue : Bool
deriving DecidableEq, Repr

/-- 可比性门。 -/
def comparableB (g : Comparability) : Bool :=
  g.sameDomain && g.sameVersion && g.sameProcedure && g.sameIssue

/-- 非空门（§12.2：空 S 是无比较基准，不能填 0 偏离——非空才发偏离读数）。 -/
def devReadingOkB (S : List ℚ) : Bool := !(S.isEmpty)

/-- 非空门互译。 -/
theorem devReadingOkB_iff (S : List ℚ) : devReadingOkB S = true ↔ S ≠ [] := by
  cases S with
  | nil => simp [devReadingOkB]
  | cons a rest => simp [devReadingOkB]

/-- 空参照集无比较基准：门拒。 -/
theorem empty_ref_no_baseline : devReadingOkB [] = false := rfl

/-- 参照准入门＝可比∧非空。 -/
def refAdmitB (g : Comparability) (S : List ℚ) : Bool :=
  comparableB g && !(S.isEmpty)

/-- 不可比参照被拒。 -/
theorem incomparable_refs_rejected (g : Comparability) (S : List ℚ)
    (h : comparableB g = false) : refAdmitB g S = false := by
  simp [refAdmitB, comparableB, h]

/-- 可比且非空的参照被准入。 -/
theorem comparable_refs_admitted (g : Comparability) (S : List ℚ)
    (h : comparableB g = true) (hne : S ≠ []) : refAdmitB g S = true := by
  have hne' : (!(S.isEmpty)) = true := Iff.mpr (devReadingOkB_iff S) hne
  simp [refAdmitB, comparableB, h, hne']

/-- **T125 独立结论定理（三参照偏离）**：三参照各自偏离非负、SELF 偏离可达、
对读数点 Lipschitz、对 UPPER 的参照集变化 Hausdorff 界、固定域平移偏移界。 -/
theorem t125_three_ref_deviation (refs : ThreeRefs) (x y δ : ℚ)
    (h1 : refs.selfSet ≠ []) (h2 : refs.peerSet ≠ []) (h3 : refs.upperSet ≠ []) :
    0 ≤ devOf x refs.selfSet ∧
    0 ≤ devOf x refs.peerSet ∧
    0 ≤ devOf x refs.upperSet ∧
    (∃ s ∈ refs.selfSet, devOf x refs.selfSet = |x - s|) ∧
    (|devOf x refs.selfSet - devOf x refs.peerSet| ≤ |x - y|) ∧
    (|devOf x refs.selfSet - devOf x refs.upperSet| ≤
      dHaus refs.selfSet refs.upperSet) ∧
    (dHaus refs.selfSet (refs.selfSet.map (fun t => t + δ)) ≤ |δ|) := by
  refine ⟨devOf_nonneg x _, devOf_nonneg x _, devOf_nonneg x _,
    devOf_attained x refs.selfSet h1, devOf_lipschitz x y refs.peerSet h2,
    dev_set_change_bound x refs.selfSet refs.upperSet h1 h3,
    hausdorff_shift_bound refs.selfSet δ⟩

/-! ## T126：倾向分层——ℚ 计数比实算 ＋ 不重复先验 ＋ 显式选择/迁移假设
（§12.3、§7.3） -/

/-- 有限分层键（法院/法官/地区×时期/法版本的有限编码）。 -/
abbrev LayerKey := Nat

/-- 分层观测：层键＋层内成功/失败计数（观测表——类型上没有先验字段，
§7.3 不重复先验数据合同的第一面）。 -/
structure StratObs where
  key : LayerKey
  successes : Nat
  failures : Nat
deriving DecidableEq, Repr

/-- 层内总计数。 -/
def obsTotal (o : StratObs) : Nat := o.successes + o.failures

/-- 观测门：零计数层不进分层表。 -/
def obsOkB (o : StratObs) : Bool := decide (0 < obsTotal o)

/-- **分层倾向实算**：层内计数比 s/(s+f)（ℚ 精确——T126 实算，不浮点）。 -/
def propensity (o : StratObs) : ℚ := (o.successes : ℚ) / (obsTotal o : ℚ)

/-- 倾向落在单位区间（实算的良构面）。 -/
theorem propensity_unit_interval (o : StratObs) (h : 0 < obsTotal o) :
    0 ≤ propensity o ∧ propensity o ≤ 1 := by
  have hpos : (0 : ℚ) < (obsTotal o : ℚ) := by exact_mod_cast h
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) (le_of_lt hpos)
  · exact Iff.mpr (div_le_one hpos)
      (by exact_mod_cast Nat.le_add_right o.successes o.failures)

/-- 分层倾向表：层键×倾向（只由观测表构造——`buildStratTable` 的输入类型
没有先验通道，§7.3 不重复先验数据合同的类型面）。 -/
structure StratTable where
  layers : List (LayerKey × ℚ)
deriving DecidableEq, Repr

/-- 总装：观测门过滤后逐层实算。 -/
def buildStratTable (obs : List StratObs) : StratTable :=
  ⟨(obs.filter obsOkB).map (fun o => (o.key, propensity o))⟩

/-- 分层表只由观测表决定（读形：层＝门过滤观测的逐层计数比）。 -/
theorem strat_table_reads_obs_only (obs : List StratObs) :
    (buildStratTable obs).layers =
      (obs.filter obsOkB).map (fun o => (o.key, propensity o)) :=
  rfl

/-- 层在表中：过门观测的 (层键, 倾向) 逐项在分层表内。 -/
theorem strat_layer_in_table (obs : List StratObs) (o : StratObs)
    (hmem : o ∈ obs) (hok : obsOkB o = true) :
    (o.key, propensity o) ∈ (buildStratTable obs).layers :=
  List.mem_map.mpr ⟨o, List.mem_filter.mpr ⟨hmem, hok⟩, rfl⟩

/-- §7.3 先验表：Beta (α,β) 逐层另列——与观测表**分型**，不进倾向输入。 -/
structure PriorTable where
  entries : List (LayerKey × Nat × Nat)
deriving DecidableEq, Repr

/-- §7.3 后验均值 (α+s)/(α+β+n)——仅作混入检验对照，不进倾向层输出。 -/
def posteriorMean (α β : Nat) (o : StratObs) : ℚ :=
  (α + o.successes : ℚ) / (α + β + obsTotal o : ℚ)

/-- **§7.3 原反例见证（独立保留）**：同一观测（层 1，成功 3/失败 1）的倾向
实算是 3/4，混入 (1,1) 先验的后验均值是 2/3——二者可区分；倾向层输出前者
（数据比），从不输出后者。同一训练标签不能先调权重又作独立证据重复使用。 -/
theorem witness_prior_not_double_used :
    propensity ⟨1, 3, 1⟩ = 3 / 4 ∧
      posteriorMean 1 1 ⟨1, 3, 1⟩ = 2 / 3 ∧
      propensity ⟨1, 3, 1⟩ ≠ posteriorMean 1 1 ⟨1, 3, 1⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [propensity, posteriorMean, obsTotal]; norm_num
  · simp only [posteriorMean, obsTotal]; norm_num
  · simp only [propensity, posteriorMean, obsTotal]; norm_num

/-- **混入可检见证**：把先验 (1,0) 的计数加进观测再算倾向得 4/5 ≠ 3/4——
检验层从原始观测重算即可拒绝混入表。 -/
theorem witness_mixed_in_detectable :
    propensity { key := 1, successes := 3 + 1, failures := 1 } = 4 / 5 ∧
      propensity { key := 1, successes := 3 + 1, failures := 1 } ≠
        propensity ⟨1, 3, 1⟩ := by
  refine ⟨?_, ?_⟩
  · simp only [propensity, obsTotal]; norm_num
  · simp only [propensity, obsTotal]; norm_num

/-- §7.3 选择/迁移假设——**显式假设参数**（不在定理内隐含）：选择机制已建模
或已证可忽略；迁移支持覆盖已具名。 -/
structure PropensityAssumptions where
  selectionModeled : Bool
  migrationCovered : Bool
deriving DecidableEq, Repr

/-- 假设具名门：两面都具名才放行层间比较。 -/
def assumptionsNamed (a : PropensityAssumptions) : Bool :=
  a.selectionModeled && a.migrationCovered

/-- 层间比较门（§12.3：进入预测必须满足 §7.3 的选择/迁移机制）。 -/
def comparisonGateB (a : PropensityAssumptions) : Bool := assumptionsNamed a

/-- 比较门互译。 -/
theorem comparisonGateB_iff (a : PropensityAssumptions) :
    comparisonGateB a = true ↔ assumptionsNamed a = true := Iff.rfl

/-- **无名假设的比较被拒**。 -/
theorem comparison_requires_named_assumptions (a : PropensityAssumptions)
    (h : assumptionsNamed a = false) : comparisonGateB a = false := by
  simp only [comparisonGateB]
  rw [h]

/-- 具名假设的比较被接受。 -/
theorem comparison_accepts_named_assumptions (a : PropensityAssumptions)
    (h : assumptionsNamed a = true) : comparisonGateB a = true := h

/-- 倾向输出用途分型：描述／经具名假设的比较——**没有"写入法源"构造子**
（T126：倾向不写入法源；进入预测须满足 §7.3 机制）。 -/
inductive StratUse where
  | descriptive
  | comparisonUnderNamedAssumptions
deriving DecidableEq, Repr

/-- 用途分型完备。 -/
theorem strat_use_exhaustive (u : StratUse) :
    u = StratUse.descriptive ∨ u = StratUse.comparisonUnderNamedAssumptions := by
  cases u with
  | descriptive => exact Or.inl rfl
  | comparisonUnderNamedAssumptions => exact Or.inr rfl

/-- **T126 独立结论定理（倾向分层）**：分层表只由观测实算（无先验通道）、
层间比较门由显式假设参数把守、每个过门层的倾向落在单位区间。 -/
theorem t126_stratified_propensity (obs : List StratObs)
    (a : PropensityAssumptions) (hass : assumptionsNamed a = true) :
    (buildStratTable obs).layers =
      (obs.filter obsOkB).map (fun o => (o.key, propensity o)) ∧
    comparisonGateB a = true ∧
    (∀ o ∈ obs, obsOkB o = true → 0 ≤ propensity o ∧ propensity o ≤ 1) := by
  refine ⟨strat_table_reads_obs_only obs, comparison_accepts_named_assumptions a hass,
    ?_⟩
  intro o hmem hok
  exact propensity_unit_interval o (decide_eq_true_iff.mp hok)

/-! ## T127：偏离报告——打包记录 ＋ 忠实投影 ＋ 完整性（§12.5） -/

/-- 偏离来源三分型（§12.2：结构偏离、现行规范不一致、经验异常三种报告分别
给依据，不能用距离大判违法）。 -/
inductive DevKind where
  | structural
  | normative
  | empirical
deriving DecidableEq, Repr

/-- 具名偏离来源标注。 -/
structure DevSource where
  sourceId : Nat
  kind : DevKind
deriving DecidableEq, Repr

/-- 来源分型完备（三分型恰尽）。 -/
theorem dev_kind_exhaustive (k : DevKind) :
    k = DevKind.structural ∨ k = DevKind.normative ∨ k = DevKind.empirical := by
  cases k with
  | structural => exact Or.inl rfl
  | normative => exact Or.inr (Or.inl rfl)
  | empirical => exact Or.inr (Or.inr rfl)

/-- 不确定性区间（§12.5 误差/样本边界——ℚ 端点，不浮点）。 -/
structure Uncert where
  lo : ℚ
  hi : ℚ
deriving DecidableEq, Repr

/-- 区间良构门。 -/
def uncertWFB (u : Uncert) : Bool := decide (u.lo ≤ u.hi)

/-- 偏离报告记录（§12.5：逐项保留比较对象、差异事实、规范对应、误差/样本
边界和引用定位；生成文句不能抹掉原始 status）。 -/
structure DeviationReport where
  reportId : Nat
  refKind : RefKind
  reading : ℚ
  sources : List DevSource
  interval : Uncert
  residualNamed : Bool
  statusKept : Bool
deriving DecidableEq, Repr

/-- 报告构造器（打包：读数原样投影；残余具名与 status 保持默认置真——抹除
是显式构造的伪造面，由 `reportOkB`/`coverageOkB` 把守）。 -/
def mkReport (reportId : Nat) (k : RefKind) (v : ℚ) (sources : List DevSource)
    (u : Uncert) : DeviationReport :=
  { reportId := reportId, refKind := k, reading := v, sources := sources,
    interval := u, residualNamed := true, statusKept := true }

/-- **忠实投影定理（T127 旗舰面）**：报告读数＝底层计算原像——构造器不重算
不漂移。 -/
theorem report_faithful_projection (reportId : Nat) (k : RefKind) (v : ℚ)
    (sources : List DevSource) (u : Uncert) :
    (mkReport reportId k v sources u).reading = v := rfl

/-- 来源逐项保留。 -/
theorem report_preserves_sources (reportId : Nat) (k : RefKind) (v : ℚ)
    (sources : List DevSource) (u : Uncert) :
    (mkReport reportId k v sources u).sources = sources := rfl

/-- 区间逐项保留。 -/
theorem report_preserves_interval (reportId : Nat) (k : RefKind) (v : ℚ)
    (sources : List DevSource) (u : Uncert) :
    (mkReport reportId k v sources u).interval = u := rfl

/-- status 不被抹（残余具名＋原始 status 保持）。 -/
theorem report_preserves_status (reportId : Nat) (k : RefKind) (v : ℚ)
    (sources : List DevSource) (u : Uncert) :
    (mkReport reportId k v sources u).residualNamed = true ∧
      (mkReport reportId k v sources u).statusKept = true :=
  ⟨rfl, rfl⟩

/-- 忠实投影门：报告读数与底层原像不一致即拒（不重算——重算值≠投影值被拒）。 -/
def reportOkB (r : DeviationReport) (preimage : ℚ) : Bool :=
  decide (r.reading = preimage)

/-- 投影门拒绝（一般形）：读数漂移的报告被拒。 -/
theorem report_gate_rejects_drift (r : DeviationReport) (preimage : ℚ)
    (h : r.reading ≠ preimage) : reportOkB r preimage = false := by
  have hd : (decide (r.reading = preimage) : Bool) = false :=
    decide_eq_false_iff_not.mpr h
  simp [reportOkB, hd]

/-- 完整性门：实际来源逐项在报告中枚举 ∨ 残余具名（§12.5 完整性）。 -/
def coverageOkB (actual : List DevSource) (r : DeviationReport) : Bool :=
  actual.all (fun s => decide (s ∈ r.sources)) || r.residualNamed

/-- 完整性门拒绝（一般形）：有实际来源未入报告且残余未具名 → 不完整即拒。 -/
theorem report_gate_rejects_unnamed_source (actual : List DevSource)
    (r : DeviationReport) (s : DevSource) (hmem : s ∈ actual)
    (hmiss : s ∉ r.sources) (hr : r.residualNamed = false) :
    coverageOkB actual r = false := by
  have hp : (decide (s ∈ r.sources) : Bool) = false := decide_eq_false_iff_not.mpr hmiss
  have hall : actual.all (fun s => decide (s ∈ r.sources)) = false := by
    cases h : actual.all (fun s => decide (s ∈ r.sources)) with
    | true =>
      exact absurd (Iff.mp (decide_eq_true_iff)
        (List.all_eq_true.mp h s hmem)) hmiss
    | false => exact rfl
  simp [coverageOkB, hall, hr]

/-- 完整报告的诚实面：逐项枚举全在 → 门接受。 -/
theorem report_gate_accepts_full_coverage (actual : List DevSource)
    (r : DeviationReport) (hcov : ∀ s ∈ actual, s ∈ r.sources) :
    coverageOkB actual r = true := by
  refine Bool.or_eq_true.mpr (Or.inl ?_)
  exact List.all_eq_true.mpr fun s hs => decide_eq_true_iff.mpr (hcov s hs)

/-- **T127 独立结论定理（偏离报告）**：忠实投影（读数＝原像）＋来源/区间/status
逐项保留＋完整性门接受。 -/
theorem t127_deviation_report_complete (reportId : Nat) (k : RefKind) (v : ℚ)
    (sources : List DevSource) (u : Uncert) (preimage : ℚ)
    (hpre : v = preimage) (hu : uncertWFB u = true)
    (actual : List DevSource) (hcov : ∀ s ∈ actual, s ∈ sources) :
    reportOkB (mkReport reportId k v sources u) preimage = true ∧
    coverageOkB actual (mkReport reportId k v sources u) = true ∧
    (mkReport reportId k v sources u).reading = preimage ∧
    uncertWFB (mkReport reportId k v sources u).interval = true ∧
    (mkReport reportId k v sources u).residualNamed = true ∧
    (mkReport reportId k v sources u).statusKept = true := by
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl⟩
  · show decide ((mkReport reportId k v sources u).reading = preimage) = true
    rw [report_faithful_projection reportId k v sources u]
    exact decide_eq_true_iff.mpr hpre
  · refine Bool.or_eq_true.mpr (Or.inl ?_)
    exact List.all_eq_true.mpr fun s hs => decide_eq_true_iff.mpr (hcov s hs)
  · rw [report_faithful_projection reportId k v sources u]
    exact hpre
  · show decide ((mkReport reportId k v sources u).interval.lo ≤
        (mkReport reportId k v sources u).interval.hi) = true
    rw [report_preserves_interval reportId k v sources u]
    exact hu

/-! ## 旗舰：四件合同合取（T124 表示保持/回流 × T125 三参照/偏移界 ×
T126 分层实算/显式假设 × T127 忠实投影/完整性） -/

/-- 旗舰报告：三参照偏离读数 ＋ 观测来源逐项标注（经验异常型） ＋ 不确定性
区间打包。 -/
def flagshipReport (refs : ThreeRefs) (x : ℚ) (obs : List StratObs) (u : Uncert) :
    DeviationReport :=
  mkReport 0 RefKind.self (devOf x refs.selfSet)
    ((obs.filter obsOkB).map (fun o =>
      ({ sourceId := o.key, kind := DevKind.empirical } : DevSource))) u

/-- **旗舰定理（W4 T124–T127 合取）**：显式假设全部作为具名参数列出——
已采用候选过表示层不漂移、有权限在窗内回流接受且纯追加；三参照偏离非负、
固定域平移 Hausdorff 偏移 ≤ 偏移常数、SELF 偏离可达；分层表只由观测实算、
比较门由显式假设放行；旗舰报告忠实投影且完整。 -/
theorem w4_deviation_flagship (cands : List InterpCandidate) (c : InterpCandidate)
    (hc : adoptableB c = true)
    (w : ReflowWindow) (e : ReflowEvent) (he : e.authorityId.isSome = true)
    (hlo : w.openDay ≤ e.atDay) (hhi : e.atDay ≤ w.closeDay)
    (refs : ThreeRefs) (h1 : refs.selfSet ≠ []) (h2 : refs.peerSet ≠ [])
    (h3 : refs.upperSet ≠ []) (x y δ : ℚ)
    (obs : List StratObs) (a : PropensityAssumptions)
    (hass : assumptionsNamed a = true) (u : Uncert) (hu : uncertWFB u = true) :
    -- T124 面
    (repReadings (c :: cands) = ruleBase (c :: cands) ∧
      c ∈ repLog (c :: cands) ∧
      reflowOkB w e = true ∧
      applyReflow (repLog (c :: cands)) w e c = repLog (c :: cands) ++ [c]) ∧
    -- T125 面
    (0 ≤ devOf x refs.selfSet ∧
      dHaus refs.selfSet (refs.selfSet.map (fun t => t + δ)) ≤ |δ| ∧
      (∃ s ∈ refs.selfSet, devOf x refs.selfSet = |x - s|)) ∧
    -- T126 面
    ((buildStratTable obs).layers =
        (obs.filter obsOkB).map (fun o => (o.key, propensity o)) ∧
      comparisonGateB a = true) ∧
    -- T127 面
    (reportOkB (flagshipReport refs x obs u) (devOf x refs.selfSet) = true ∧
      coverageOkB
        ((obs.filter obsOkB).map (fun o =>
          ({ sourceId := o.key, kind := DevKind.empirical } : DevSource)))
        (flagshipReport refs x obs u) = true ∧
      (flagshipReport refs x obs u).reading = devOf x refs.selfSet ∧
      uncertWFB (flagshipReport refs x obs u).interval = true) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- T124
    have hreflow := reflow_accepts_authorized_in_window w e he hlo hhi
    refine ⟨rep_readings_match_rule_base _, List.mem_filter.mpr ⟨by simp, hc⟩,
      hreflow, reflow_accepted_appends _ w e c hreflow⟩
  · -- T125
    exact ⟨devOf_nonneg x refs.selfSet, hausdorff_shift_bound refs.selfSet δ,
      devOf_attained x refs.selfSet h1⟩
  · -- T126
    exact ⟨strat_table_reads_obs_only obs,
      comparison_accepts_named_assumptions a hass⟩
  · -- T127
    have hread : (flagshipReport refs x obs u).reading = devOf x refs.selfSet := rfl
    refine ⟨?_, ?_, hread, ?_⟩
    · show decide ((flagshipReport refs x obs u).reading = devOf x refs.selfSet) = true
      rw [hread]
      exact decide_eq_true_iff.mpr rfl
    · refine Bool.or_eq_true.mpr (Or.inl ?_)
      refine List.all_eq_true.mpr fun s hs => decide_eq_true_iff.mpr ?_
      have hsrc : (flagshipReport refs x obs u).sources =
        (obs.filter obsOkB).map (fun o =>
          ({ sourceId := o.key, kind := DevKind.empirical } : DevSource)) := rfl
      rw [hsrc]
      exact hs
    · show decide ((flagshipReport refs x obs u).interval.lo ≤
          (flagshipReport refs x obs u).interval.hi) = true
      exact hu

end JurisLean.Seams.UnifiedW4Deviation
