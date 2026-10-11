import Mathlib.Tactic

/-!
W4 批 T112–T115 —— 六件套之 Lean 合同件（量刑双线／动态谈判／隐藏信息与信念／
无限重复折扣）。

出处（施工合同）：
- `docs/spec/20261007-统一法律数学模型_附录K_全量目标落实表.md:2541`（T112 行：
  §8.6,11.3.10：责任刑规范域＋预防/经验线，刑种分型与同源证书）与 `:2542`
  （T113 行：§8.3：有限动态谈判完全信息后向归纳/隐藏信息序贯均衡）与 `:2543`
  （T114 行：§8.3：类型/信息集/一致离轨信念与全部延续偏离）与 `:2544`
  （T115 行：§8.3：无限重复折扣尾界/离轨单偏离/可信惩罚阈值；锚与反例条款
  I.0/I.4/I.11 与 J.0/J.6/J.12–14；各行原反例独立保留）。
- `docs/spec/20261007-统一法律数学模型_全量施工方案.md:521–530`（§8.3：有限时域
  完整信息情景树的后向归纳——最末节点先成立、逐层替换；隐藏信息用信息集与类型
  先验，不能把树的真实状态直接交行动者；可达信息集上 Bayes 归一、离轨信念属
  全混合策略诱导信念的极限闭包、不能任填 0/0；每个信息集全部纯延续计划的条件
  收益不增，完美记忆保证混合偏离为这些计划的凸组合；无限重复折扣 δ∈(0,1)、
  有界阶段收益、几何级数尾界 ≤ Mδ^N/(1−δ)；单次偏离不获利则有限偏离由从末次
  替换不提高、无限偏离由尾界取极限不提高；合作条件 R/(1−δ) ≥ T+δP/(1−δ)，
  T>P 时 δ ≥ (T−R)/(T−P)，惩罚必须本身为其子博弈允许/可信行动）。
- 同文件 `:549–555`（§8.6：规范量刑域按罪名/法定情节/刑种与程序生成，经验拟合
  只能作为其独立预测或允许域内辅助，不能反向修改法定范围；T84 有界经验模型
  Y∈[a,a+D]；`Term(months)`、无期、死刑是不同类，不用 −1/−2 混算均值）。
- 同文件 `:872–876`（§11.3.10：量刑规范区间与经验预测分开，无期、死刑和期间
  不是同一数轴；刑罚执行要实际阶段事件）。

六件套分工：本件＝四项各自的独立结论定理＋旗舰合取（禁参数化别名——四项陈述
各自独立成定理，旗舰只是同一见证包上的合取读出）。Python 入口
`tools/full_math/implementation/games_ref.py`、独立 checker
`tools/full_math/implementation/games_check.py`（零函数共享）、正反例
`tools/full_math/implementation_tests/test_games_w4.py`、合成回执见报告
`.local/agent_N_w4_t112_report.md`。

## 一、法律语义（人话）

- **T112（量刑双线）**：责任刑落在法定规范域（月刑期区间＋无期/死刑许可位）内；
  预防/经验线只在域内辅助——任意预防调整经裁剪投影后恒在域内（预防线不得越出
  责任刑边界），域内合成不扭曲；经验预测值越出法定域时其裸值被拒、只有裁剪后才
  可入域（经验拟合不能反向修改法定范围）；双线各自携带证书，只有共享同一事实
  输入（同源）且一责任一预防才可合成，异源证书被拒（本行原反例＝基于不同事实
  输入的预防线证书被合成门拒绝）。
- **T113（动态谈判）**：两轮轮流出价的有限时域完全信息谈判（有限菜单＝每节点
  行动集有限非空）；后向归纳从末轮开始：应答者按阈值行动（平局接受＝保留最大化
  分支后的规范化），出价者在菜单上取自身收益最大化分支；**单步偏离检查**：四个
  子博弈节点（两出价＋两应答）上任何单步替代行动都不提高行动者收益；**结果唯一
  类定理**：任一在菜单上最大化第一分量收益的出价都产出同一后向归纳结果（无差异
  边缘由"可接受报价不得与拒绝延续同收益"的严格性假设排除）。
- **T114（隐藏信息与信念）**：两型发送者＋两信息集接收者的信号博弈；一致信念：
  可达信息集被路径贝叶斯唯一钉定（两型同发＝先验、独发＝1/0），离轨信息集只要求
  信念落支撑内（全混合极限闭包的两节点代数刻画——不能任填 0/0）；序贯检查器 =
  一致性∧接收者两信息集最优回应∧发送者两型最优回应；**全部延续偏离无益**：
  两纯行动的检查通过 ⇒ 任意凸组合（即全部混合延续偏离）也不增收益。
- **T115（无限重复折扣）**：δ∈[0,1)、逐期收益有界 M；**尾界**：任意 N 起任意
  k 期折扣和满足 |·|·(1−δ) ≤ M·δ^N（除法形 ≤ Mδ^N/(1−δ)）——无限和用有限尾界
  定理形式，不写无穷级数极限；**离轨单偏离原理**：任何单期替换（其余按原流）
  都不获利 ⇒ 任何只在窗口内不同的替代流整体不获利（从末次替换逐期不降低）；
  **可信惩罚阈值**：合作值 R/(1−δ) ≥ 背离值 T+δP/(1−δ) ⟺ δ ≥ (T−R)/(T−P)
  （T>P 时阈值正）；惩罚路径须在其子博弈允许行动集内（credibility 前置，
  作为独立检查项 `punishPermitted`）。

## 二、显式假设开放点（如实列出）

- T113 限制在**两轮**有限谈判（一般 T 期情景树的后向归纳是开放点，本件只对
  T=1 的完全信息轮流出价闭合）；菜单各两报价（有限非空的最小情形）；分歧收益
  取 (0,0)（合成参数可另设）；平局规范化取"接受优先/取第一报价"。
- T114 限制在**两型/两信息集/两行动**（一般有限树的序贯均衡存在性属 §8.3 的
  CAD 量化消去路线，本件不展开）；离轨信念闭包条件以"支撑内良构"承载——
  两节点信息集上全支撑信念恰在全混合极限闭包内，一般树的一致性序列见证是
  开放点；发送者收益不依赖信念（完美信息发送层）。
- T115 的折扣估值以"递归＋逐点乘法有界"结构承载（V=r+δPV 的单状态流形式）；
  无限偏离的尾界只给乘法/除法形不等式，不构造拓扑极限；可信惩罚的
  "允许行动集"以谓词前置，不建完整子博弈许可树。
- 全部金额/概率/折扣一律 ℚ；零浮点。

## 三、本件证明 API 纪律（承 UnifiedW4Interp 头注，全部按 v4.30 工具链源码核实）

- 合取命题逐分量 ⟨…⟩，不 `:= rfl`；`Bool.and_eq_true` 是 Prop 等式形，只作
  `simp only` 引理；自家 Iff 投影写显式 `Iff.mp/Iff.mpr`；
- Prop 谓词若被 `decide` 消费，一律 `abbrev`（可归约）——普通 def 不参与
  instance 搜索，`decide (plainDef …)` 找不到 Decidable 实例；
- `rw [plainDef]` 不可用（普通 def 无方程式可重写）——展开走 `show`（defeq）、
  `unfold` 或 `simp only [def]`；`ite` 下的模式匹配先 `show` 做 beta 归约；
- ℚ 比较：参数化的走 `decide_eq_true_iff`＋`linarith`；闭式数值见证走 `decide`
  或 `norm_num`；含分母的目标先给 `≠ 0`/`0 <` 显式事实再 `linarith`；
- `Finset.sum_range_succ`/`pow_succ`/`Finset.mul_sum`/`Finset.sum_mul`/
  `Finset.abs_sum_le_sum_abs`/`div_le_iff₀`/`le_div_iff₀`/`div_mul_cancel₀`
  均按 .lake/packages/mathlib（v4.30）实际签名核对。

**证**：本文件全部定理，零 sorry / 零自定义 axiom / 零 `True :=` 逃避。
CI 模块轮为唯一 Lean 权威（本机不编译，协议禁止）。
-/

namespace JurisLean.Seams.UnifiedW4Games

/-! ## T112：量刑双线（§8.6、§11.3.10） -/

/-- 刑种分型（§11.3.10：`Term(months)`、无期、死刑是不同类，不用 −1/−2 混算
均值；无期、死刑和期间不是同一数轴——枚举分型使这一点结构性成立）。 -/
inductive PenaltyKind where
  | fixed (months : ℚ)
  | life
  | death
deriving DecidableEq, Repr

/-- 刑种枚举完备：任一刑种是有期徒刑（某月数）、无期或死刑之一。 -/
theorem penalty_exhaust (p : PenaltyKind) :
    (∃ m, p = PenaltyKind.fixed m) ∨ p = PenaltyKind.life ∨ p = PenaltyKind.death := by
  cases p with
  | fixed m => exact Or.inl ⟨m, rfl⟩
  | life => exact Or.inr (Or.inl rfl)
  | death => exact Or.inr (Or.inr rfl)

/-- 刑种两两相异（同一数轴 −1/−2 编码的反面：分型不相交）。 -/
theorem penalty_pairwise_ne :
    PenaltyKind.fixed 5 ≠ PenaltyKind.life ∧
    PenaltyKind.fixed 5 ≠ PenaltyKind.death ∧
    PenaltyKind.life ≠ PenaltyKind.death := by
  decide

/-- 量刑规范域（§8.6：按罪名/法定情节/刑种与程序生成；§11.3.10：量刑规范区间
与经验预测分开）。 -/
structure NormDomain where
  monthsLo : ℚ
  monthsHi : ℚ
  allowsLife : Bool
  allowsDeath : Bool
  lo_le_hi : monthsLo ≤ monthsHi

/-- 刑种在域判定（Bool 参考核：有期徒刑看月区间，无期/死刑看许可位）。 -/
def penaltyInDomainB (d : NormDomain) (p : PenaltyKind) : Bool :=
  match p with
  | .fixed m => decide (d.monthsLo ≤ m ∧ m ≤ d.monthsHi)
  | .life => d.allowsLife
  | .death => d.allowsDeath

/-- 在域判定的展开形（三分支互斥、与枚举完备对齐）。 -/
theorem penaltyInDomainB_iff (d : NormDomain) (p : PenaltyKind) :
    penaltyInDomainB d p = true ↔
      (∃ m, p = PenaltyKind.fixed m ∧ d.monthsLo ≤ m ∧ m ≤ d.monthsHi) ∨
      (p = PenaltyKind.life ∧ d.allowsLife = true) ∨
      (p = PenaltyKind.death ∧ d.allowsDeath = true) := by
  cases p with
  | fixed m =>
    constructor
    · intro h
      have hc := decide_eq_true_iff.mp h
      exact Or.inl ⟨m, rfl, hc.1, hc.2⟩
    · intro h
      rcases h with ⟨m', hm', hlo, hhi⟩ | ⟨_, hl⟩ | ⟨_, hd⟩
      · injection hm' with hm'
        subst hm'
        exact decide_eq_true_iff.mpr ⟨hlo, hhi⟩
      · exact absurd hl (by decide)
      · exact absurd hd (by decide)
  | life =>
    constructor
    · intro h
      exact Or.inr (Or.inl ⟨rfl, h⟩)
    · intro h
      rcases h with ⟨m', hm', _, _⟩ | ⟨_, hl⟩ | ⟨_, hd⟩
      · exact absurd hm' (by decide)
      · exact hl
      · exact absurd hd (by decide)
  | death =>
    constructor
    · intro h
      exact Or.inr (Or.inr ⟨rfl, h⟩)
    · intro h
      rcases h with ⟨m', hm', _, _⟩ | ⟨_, hl⟩ | ⟨_, hd⟩
      · exact absurd hm' (by decide)
      · exact absurd hl (by decide)
      · exact hd

/-- 有期徒刑在域的充分条件（构造级门）。 -/
theorem penaltyInDomainB_fixed_of_le (d : NormDomain) (x : ℚ)
    (hlo : d.monthsLo ≤ x) (hhi : x ≤ d.monthsHi) :
    penaltyInDomainB d (PenaltyKind.fixed x) = true :=
  decide_eq_true_iff.mpr ⟨hlo, hhi⟩

/-- 域内裁剪投影（§8.6 clip 非扩张先例）：把任意预防调整投影回规范域。 -/
def clipTo (d : NormDomain) (x : ℚ) : ℚ := max d.monthsLo (min d.monthsHi x)

/-- 裁剪恒在域内（预防线调整不得越出责任刑边界——投影保证）。 -/
theorem clip_in_domain (d : NormDomain) (x : ℚ) :
    d.monthsLo ≤ clipTo d x ∧ clipTo d x ≤ d.monthsHi :=
  ⟨le_max_left _ _, max_le d.lo_le_hi (min_le_right _ _)⟩

/-- 域内不动点（责任刑边界内的合成不扭曲：调整后仍在域内时裁剪＝恒等）。 -/
theorem clip_fix_in_domain (d : NormDomain) (x : ℚ)
    (hlo : d.monthsLo ≤ x) (hhi : x ≤ d.monthsHi) : clipTo d x = x := by
  show max d.monthsLo (min d.monthsHi x) = x
  rw [min_eq_right hhi, max_eq_left hlo]

/-- 经验/预防线的有界预测输入（§8.6 T84：有界经验模型 Y∈[a,a+D]；构造级
fail-fast——值域声明与值同时给出，越界预测构造不出来）。 -/
structure EmpPrediction where
  base : ℚ
  span : ℚ
  hspan : 0 ≤ span
  value : ℚ
  hval : base ≤ value ∧ value ≤ base + span

/-- **T112 独立结论（责任刑规范域约束预防调整）**：双线合成（责任刑 r ＋ 预防
调整 t，经裁剪投影）恒落在规范域内，且域内合成不扭曲。 -/
theorem dual_line_stays_normative (d : NormDomain) (r t : ℚ) :
    d.monthsLo ≤ clipTo d (r + t) ∧ clipTo d (r + t) ≤ d.monthsHi ∧
      (d.monthsLo ≤ r + t → r + t ≤ d.monthsHi → clipTo d (r + t) = r + t) := by
  exact ⟨(clip_in_domain d (r + t)).1, (clip_in_domain d (r + t)).2,
    clip_fix_in_domain d (r + t)⟩

/-- 经验线不能反向修改法定范围（§8.6：经验拟合只能作为其独立预测或允许域内
辅助）：经验值越出法定域时裸值被判不在域，裁剪后才入域——域 d 不因经验输入
改变，越界只有裁剪一条路。 -/
theorem empirical_outside_needs_clip (d : NormDomain) (e : EmpPrediction)
    (_hout : penaltyInDomainB d (PenaltyKind.fixed e.value) = false) :
    penaltyInDomainB d (PenaltyKind.fixed (clipTo d e.value)) = true :=
  penaltyInDomainB_fixed_of_le d (clipTo d e.value)
    (clip_in_domain d e.value).1 (clip_in_domain d e.value).2

/-- 双线线型分型（一责任一预防）。 -/
inductive LineKind where
  | responsibility
  | prevention
deriving DecidableEq, Repr

/-- 双线证书：各自携带线型、刑种与共享事实输入身份 `factsId`（同源证书结构——
两线共享同一事实输入）。 -/
structure SentCert where
  certId : Nat
  factsId : Nat
  line : LineKind
  kind : PenaltyKind
deriving DecidableEq, Repr

/-- 同源合成门（Bool）：一责任一预防（线型不同）且事实输入同源才可合成。 -/
def composeGateB (x y : SentCert) : Bool :=
  decide (x.line ≠ y.line) && decide (x.factsId = y.factsId)

/-- 合成门双侧互译。 -/
theorem composeGateB_iff (x y : SentCert) :
    composeGateB x y = true ↔ x.line ≠ y.line ∧ x.factsId = y.factsId := by
  constructor
  · intro h
    simp only [composeGateB, Bool.and_eq_true, decide_eq_true_iff] at h
    exact h
  · rintro ⟨hne, hsrc⟩
    show (decide (x.line ≠ y.line) && decide (x.factsId = y.factsId)) = true
    rw [decide_eq_true_iff.mpr hne, decide_eq_true_iff.mpr hsrc]
    rfl

/-- 异源证书被合成门拒绝（一般形）。 -/
theorem composeGateB_rejects_foreign_facts (x y : SentCert)
    (hne : x.factsId ≠ y.factsId) : composeGateB x y = false := by
  by_cases hxy : x.factsId = y.factsId
  · exact absurd hxy hne
  · show (decide (x.line ≠ y.line) && decide (x.factsId = y.factsId)) = false
    rw [decide_eq_false_iff_not.mpr hxy]
    exact Bool.and_false _

/-- **T112 原反例见证（独立保留）**：责任线证书与基于**不同事实输入**（异源，
factsId 100 对 200）的预防线证书——合成门拒绝。预防线不得携带另一案件的事实
输入来调整本线的量刑。 -/
def certRespDemo : SentCert := ⟨1, 100, .responsibility, .fixed 30⟩
def certPrevDemo : SentCert := ⟨2, 100, .prevention, .fixed 36⟩
def certPrevForeignDemo : SentCert := ⟨3, 200, .prevention, .fixed 36⟩

/-- 同源双线通过合成门。 -/
theorem witness_same_source_passes :
    composeGateB certRespDemo certPrevDemo = true := by
  decide

/-- **T112 原反例（独立保留）**：异源被拒。 -/
theorem witness_foreign_facts_rejected :
    composeGateB certRespDemo certPrevForeignDemo = false :=
  composeGateB_rejects_foreign_facts certRespDemo certPrevForeignDemo (by decide)

/-- 合成数值见证：法定域 [10,60] 月；责任刑 25，预防线想推 40 → 合成 65 越界，
裁剪回 60；裸 65 判不在域。 -/
def normDomainDemo : NormDomain := ⟨10, 60, false, false, by norm_num⟩

theorem witness_prevention_clipped :
    clipTo normDomainDemo (25 + 40) = 60 ∧
    penaltyInDomainB normDomainDemo
      (PenaltyKind.fixed (clipTo normDomainDemo (25 + 40))) = true ∧
    penaltyInDomainB normDomainDemo (PenaltyKind.fixed 65) = false := by
  decide

/-- 经验线见证：预测值 75 在自身值域 [70,80] 内、但越出法定域 [10,60]——
裸值被拒、裁剪回 60 后入域（经验拟合不反向修改法定范围）。 -/
def empHighDemo : EmpPrediction :=
  ⟨70, 10, by norm_num, 75, ⟨by norm_num, by norm_num⟩⟩

theorem witness_empirical_outside_needs_clip :
    penaltyInDomainB normDomainDemo (PenaltyKind.fixed empHighDemo.value) = false ∧
    penaltyInDomainB normDomainDemo
      (PenaltyKind.fixed (clipTo normDomainDemo empHighDemo.value)) = true := by
  refine ⟨?_, ?_⟩
  · decide
  · exact empirical_outside_needs_clip normDomainDemo empHighDemo (by decide)

/-! ## T113：动态谈判（§8.3：有限时域、轮流出价、完全信息后向归纳） -/

/-- 两轮轮流出价谈判参数：蛋糕 `cake`、折扣 `delta`；第 0 轮 A 出价（给 B 的
份额）菜单 {x1, x2}，第 1 轮 B 出价（给 A 的份额）菜单 {y1, y2}；末轮拒绝＝
分歧收益 (0,0)（§8.3：有限时域完整信息情景树；有限菜单＝每节点行动集有限
非空；终局收益按同一轨迹计算）。 -/
structure BargainParams where
  cake : ℚ
  delta : ℚ
  x1 x2 y1 y2 : ℚ
  hdelta : 0 ≤ delta
  hcake : 0 ≤ cake

/-- 第 1 轮 A 的接受门：δ·y ≥ 0 时接受（平局接受＝最大化分支保留后的规范化）。 -/
def accR1 (p : BargainParams) (y : ℚ) : Bool := decide (p.delta * y ≥ 0)

/-- 第 1 轮收益：接受＝(δ·y, δ·(cake−y))，拒绝＝(0,0)。 -/
def r1Pay (p : BargainParams) (y : ℚ) : ℚ × ℚ :=
  if accR1 p y then (p.delta * y, p.delta * (p.cake - y)) else (0, 0)

/-- 第 1 轮 B 的后向归纳选择：菜单上自身（第二分量）收益最大化分支；平局取 y1
（保留全部分支后的规范化）。 -/
def b1Choice (p : BargainParams) : ℚ :=
  if (r1Pay p p.y1).2 ≥ (r1Pay p p.y2).2 then p.y1 else p.y2

/-- 末轮后向归纳值。 -/
def biR1 (p : BargainParams) : ℚ × ℚ := r1Pay p (b1Choice p)

/-- 第 0 轮 B 的接受门：x ≥ δ·（B 的末轮延续份额）时接受。 -/
def accR0 (p : BargainParams) (x : ℚ) : Bool := decide (x ≥ p.delta * (biR1 p).2)

/-- 第 0 轮收益：接受＝(cake−x, x)，拒绝＝末轮延续 biR1。 -/
def r0Pay (p : BargainParams) (x : ℚ) : ℚ × ℚ :=
  if accR0 p x then (p.cake - x, x) else biR1 p

/-- 第 0 轮 A 的后向归纳选择：菜单上自身（第一分量）收益最大化分支；平局取 x1。 -/
def a0Choice (p : BargainParams) : ℚ :=
  if (r0Pay p p.x1).1 ≥ (r0Pay p p.x2).1 then p.x1 else p.x2

/-- 后向归纳结果（子博弈精炼剖面下的终局收益向量）。 -/
def biOutcome (p : BargainParams) : ℚ × ℚ := r0Pay p (a0Choice p)

theorem accR1_iff (p : BargainParams) (y : ℚ) :
    accR1 p y = true ↔ 0 ≤ p.delta * y :=
  decide_eq_true_iff

theorem accR1_false_iff (p : BargainParams) (y : ℚ) :
    accR1 p y = false ↔ p.delta * y < 0 := by
  constructor
  · intro h
    have hnot : ¬ (0 ≤ p.delta * y) := fun hh => h (decide_eq_true_iff.mpr hh)
    linarith
  · intro h
    show decide (p.delta * y ≥ 0) = false
    rw [decide_eq_false_iff_not]
    linarith

theorem accR0_iff (p : BargainParams) (x : ℚ) :
    accR0 p x = true ↔ x ≥ p.delta * (biR1 p).2 :=
  decide_eq_true_iff

theorem accR0_false_iff (p : BargainParams) (x : ℚ) :
    accR0 p x = false ↔ x < p.delta * (biR1 p).2 := by
  constructor
  · intro h
    have hnot : ¬ (x ≥ p.delta * (biR1 p).2) := fun hh => h (decide_eq_true_iff.mpr hh)
    linarith
  · intro h
    show decide (x ≥ p.delta * (biR1 p).2) = false
    rw [decide_eq_false_iff_not]
    linarith

/-- 后向归纳选择都在菜单内（保留最大化分支不外造行动）。 -/
theorem b1Choice_menu (p : BargainParams) :
    b1Choice p = p.y1 ∨ b1Choice p = p.y2 := by
  unfold b1Choice
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem a0Choice_menu (p : BargainParams) :
    a0Choice p = p.x1 ∨ a0Choice p = p.x2 := by
  unfold a0Choice
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem b1Choice_val (p : BargainParams) :
    ((r1Pay p p.y1).2 ≥ (r1Pay p p.y2).2 ∧ b1Choice p = p.y1) ∨
    ((r1Pay p p.y1).2 < (r1Pay p p.y2).2 ∧ b1Choice p = p.y2) := by
  unfold b1Choice
  split_ifs with h
  · exact Or.inl ⟨h, rfl⟩
  · exact Or.inr ⟨by linarith, rfl⟩

theorem a0Choice_val (p : BargainParams) :
    ((r0Pay p p.x1).1 ≥ (r0Pay p p.x2).1 ∧ a0Choice p = p.x1) ∨
    ((r0Pay p p.x1).1 < (r0Pay p p.x2).1 ∧ a0Choice p = p.x2) := by
  unfold a0Choice
  split_ifs with h
  · exact Or.inl ⟨h, rfl⟩
  · exact Or.inr ⟨by linarith, rfl⟩

/-- 末轮 B 的选择是其收益最大化分支（§8.3：后向归纳保留全部最大化分支）。 -/
theorem b1_best_response (p : BargainParams) :
    (biR1 p).2 ≥ (r1Pay p p.y1).2 ∧ (biR1 p).2 ≥ (r1Pay p p.y2).2 := by
  rcases b1Choice_val p with ⟨h1, hc⟩ | ⟨h1, hc⟩
  · have hexp : biR1 p = r1Pay p p.y1 := by
      show r1Pay p (b1Choice p) = r1Pay p p.y1
      rw [hc]
    rw [hexp]
    exact ⟨le_refl _, h1⟩
  · have hexp : biR1 p = r1Pay p p.y2 := by
      show r1Pay p (b1Choice p) = r1Pay p p.y2
      rw [hc]
    rw [hexp]
    exact ⟨by linarith, le_refl _⟩

/-- 根节点 A 的选择是其收益最大化分支。 -/
theorem a0_best_response (p : BargainParams) :
    (biOutcome p).1 ≥ (r0Pay p p.x1).1 ∧ (biOutcome p).1 ≥ (r0Pay p p.x2).1 := by
  rcases a0Choice_val p with ⟨h1, hc⟩ | ⟨h1, hc⟩
  · have hexp : biOutcome p = r0Pay p p.x1 := by
      show r0Pay p (a0Choice p) = r0Pay p p.x1
      rw [hc]
    rw [hexp]
    exact ⟨le_refl _, h1⟩
  · have hexp : biOutcome p = r0Pay p p.x2 := by
      show r0Pay p (a0Choice p) = r0Pay p p.x2
      rw [hc]
    rw [hexp]
    exact ⟨by linarith, le_refl _⟩

/-- 接受分支下结果读形。 -/
theorem biOutcome_accept (p : BargainParams)
    (h : accR0 p (a0Choice p) = true) :
    biOutcome p = (p.cake - a0Choice p, a0Choice p) := by
  unfold biOutcome r0Pay
  rw [if_pos h]

/-- **T113 独立结论（子博弈精炼的单步偏离检查）**：四个子博弈节点上——末轮 B
换报价、末轮 A 换接受/拒绝、根 A 换报价、根 B 换接受/拒绝——任何单步替代行动
都不提高行动者收益（§8.3：最末节点先成立，再逐层替换；菜单有限故偏离域恰为
两点菜单＋接受/拒绝二元，枚举完备）。 -/
theorem bi_one_step_no_gain (p : BargainParams) :
    (biR1 p).2 ≥ (r1Pay p p.y1).2 ∧ (biR1 p).2 ≥ (r1Pay p p.y2).2 ∧
    (accR1 p (b1Choice p) = true → 0 ≤ p.delta * (b1Choice p)) ∧
    (accR1 p (b1Choice p) = false → p.delta * (b1Choice p) ≤ 0) ∧
    (biOutcome p).1 ≥ (r0Pay p p.x1).1 ∧ (biOutcome p).1 ≥ (r0Pay p p.x2).1 ∧
    (accR0 p (a0Choice p) = true → p.delta * (biR1 p).2 ≤ (biOutcome p).2) ∧
    (accR0 p (a0Choice p) = false → a0Choice p ≤ p.delta * (biR1 p).2) := by
  refine ⟨(b1_best_response p).1, (b1_best_response p).2, ?_, ?_,
    (a0_best_response p).1, (a0_best_response p).2, ?_, ?_⟩
  · intro h
    exact decide_eq_true_iff.mp h
  · intro h
    have hlt := (accR1_false_iff p (b1Choice p)).mp h
    linarith
  · intro h
    have hth : p.delta * (biR1 p).2 ≤ a0Choice p := decide_eq_true_iff.mp h
    have h2 : (biOutcome p).2 = a0Choice p := by
      rw [biOutcome_accept p h]
    rw [h2]
    exact hth
  · intro h
    have hlt := (accR0_false_iff p (a0Choice p)).mp h
    linarith

/-- **T113 结果唯一类定理**：任一在菜单上最大化 A 第一分量收益的出价 x 都产出
同一后向归纳结果。无差异边缘（可接受报价与拒绝延续同收益）由 `hind` 排除——
这正是"后向归纳在每个节点保留全部最大化分支后结果唯一"的精确含义（完全一般
平局下的剖面差异不是收益差异，被严格性假设钉住）。 -/
theorem bi_outcome_unique (p : BargainParams) (x : ℚ)
    (hx : x = p.x1 ∨ x = p.x2)
    (ha0 : (r0Pay p x).1 ≥ (r0Pay p p.x1).1 ∧ (r0Pay p x).1 ≥ (r0Pay p p.x2).1)
    (hind : ∀ z, accR0 p z = true → (r0Pay p z).1 ≠ (biR1 p).1) :
    r0Pay p x = biOutcome p := by
  obtain ⟨ha01, ha02⟩ := ha0
  have hbA := a0_best_response p
  obtain ⟨hb1, hb2⟩ := hbA
  have hxm : (r0Pay p x).1 = (r0Pay p p.x1).1 ∨ (r0Pay p x).1 = (r0Pay p p.x2).1 := by
    rcases hx with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h])
  have ham : (r0Pay p (a0Choice p)).1 = (r0Pay p p.x1).1 ∨
      (r0Pay p (a0Choice p)).1 = (r0Pay p p.x2).1 := by
    rcases a0Choice_menu p with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h])
  have hmaxeq : (r0Pay p x).1 = (r0Pay p (a0Choice p)).1 := by
    rcases hxm with hx1 | hx2
    · rcases ham with ha1 | ha2
      · rw [hx1, ha1]
      · linarith
    · rcases ham with ha1 | ha2
      · linarith
      · rw [hx2, ha2]
  unfold biOutcome r0Pay
  by_cases hax : accR0 p x = true
  · by_cases haa : accR0 p (a0Choice p) = true
    · rw [if_pos hax, if_pos haa]
      have hfx : (r0Pay p x).1 = p.cake - x := by unfold r0Pay; rw [if_pos hax]
      have hfa : (r0Pay p (a0Choice p)).1 = p.cake - a0Choice p := by
        unfold r0Pay; rw [if_pos haa]
      have hxa : x = a0Choice p := by
        rw [hfx, hfa] at hmaxeq
        linarith
      rw [hxa]
    · exfalso
      have hfx : (r0Pay p x).1 = p.cake - x := by unfold r0Pay; rw [if_pos hax]
      have hfa : (r0Pay p (a0Choice p)).1 = (biR1 p).1 := by
        unfold r0Pay; rw [if_neg haa]
      have hnd := hind x hax
      rw [hfx] at hnd hmaxeq
      rw [hfa] at hmaxeq
      exact hnd hmaxeq
  · by_cases haa : accR0 p (a0Choice p) = true
    · exfalso
      have hfx : (r0Pay p x).1 = (biR1 p).1 := by unfold r0Pay; rw [if_neg hax]
      have hfa : (r0Pay p (a0Choice p)).1 = p.cake - a0Choice p := by
        unfold r0Pay; rw [if_pos haa]
      have hnd := hind (a0Choice p) haa
      rw [hfa] at hnd hmaxeq
      rw [hfx] at hmaxeq
      exact hnd hmaxeq.symm
    · rw [if_neg hax, if_neg haa]

/-- 合成数值例：蛋糕 100、δ=1/2、菜单 x∈{40,60}、y∈{20,50}。末轮 y=20：A 接受
（δ·20=10 ≥ 0），B 得 δ·80=40 > δ·50=25 → b1Choice=20，biR1=(10,40)；根门槛
x ≥ δ·40=20，两报价都可接受，A 取 40（得 60 > 40）→ 后向归纳结果 (60,40)。 -/
def bParamsDemo : BargainParams :=
  { cake := 100, delta := 1 / 2, x1 := 40, x2 := 60, y1 := 20, y2 := 50,
    hdelta := by norm_num, hcake := by norm_num }

theorem witness_bargain_bi :
    b1Choice bParamsDemo = 20 ∧ biOutcome bParamsDemo = ((60 : ℚ), (40 : ℚ)) := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ## T114：隐藏信息与信念（§8.3：类型/信息集/一致离轨信念与全部延续偏离） -/

/-- 类型（§8.3：类型先验；两型：strong/weak）。 -/
inductive SigType where
  | strong
  | weak
deriving DecidableEq, Repr

/-- 信息集信念：接收者对 strong 型的概率（两节点信息集的信念由一点钉定）。 -/
structure Belief where
  muStrong : ℚ
deriving DecidableEq, Repr

/-- 信念良构：落在支撑内（离轨不任填 0/0、不越界——§8.3 全混合极限闭包的
两节点代数刻画：支撑内每一点都由全混合策略序列逼近，越界点不在闭包内）。
abbrev＝可归约（被 decide 消费，普通 def 不参与 instance 搜索）。 -/
abbrev beliefWF (μ : Belief) : Prop := 0 ≤ μ.muStrong ∧ μ.muStrong ≤ 1

/-- 信号博弈：先验 π；`pay m a t`＝接收者在信息集 m（true＝L）行动 a（true＝u）
对真实型 t 的收益；`uS m a t`＝型 t 发信号 m 后接收者行动 a 时发送者的收益。
（发送者收益不依赖信念——发送层完全信息的假设开放点见头注。） -/
structure SigGame where
  prior : ℚ
  hprior : 0 ≤ prior ∧ prior ≤ 1
  pay : Bool → Bool → SigType → ℚ
  uS : Bool → Bool → SigType → ℚ

/-- 一致信念（§8.3：可达信息集上 Bayes 用路径概率归一；离轨信念不能任填 0/0）：
两型同发 m ⇒ 后验＝先验；仅强型发 ⇒ 1；仅弱型发 ⇒ 0；离轨 ⇒ 只要求支撑内良构。
abbrev＝可归约（被 decide 消费）。 -/
abbrev consistentB (g : SigGame) (sS : SigType → Bool) (m : Bool) (μ : Belief) : Prop :=
  if sS .strong = m then
    (if sS .weak = m then μ.muStrong = g.prior else μ.muStrong = 1)
  else (if sS .weak = m then μ.muStrong = 0 else beliefWF μ)

/-- 可达信息集上信念被路径贝叶斯唯一钉定（一致离轨信念的核心：可达处无自由度，
离轨处才有限定在支撑内的自由度）。 -/
theorem consistentB_on_path_pins (g : SigGame) (sS : SigType → Bool) (m : Bool)
    (μ₁ μ₂ : Belief) (h : sS .strong = m ∨ sS .weak = m)
    (hc₁ : consistentB g sS m μ₁) (hc₂ : consistentB g sS m μ₂) :
    μ₁.muStrong = μ₂.muStrong := by
  unfold consistentB at hc₁ hc₂
  by_cases hs : sS .strong = m
  · by_cases hw : sS .weak = m
    · rw [if_pos hs, if_pos hw] at hc₁ hc₂
      rw [hc₁, hc₂]
    · rw [if_pos hs, if_neg hw] at hc₁ hc₂
      rw [hc₁, hc₂]
  · by_cases hw : sS .weak = m
    · rw [if_neg hs, if_pos hw] at hc₁ hc₂
      rw [hc₁, hc₂]
    · exact absurd h (by simp [hs, hw])

/-- 接收者在信息集 m 信念 μ 下行动 a 的期望收益（信念线性）。 -/
def euR (g : SigGame) (m : Bool) (μ : Belief) (a : Bool) : ℚ :=
  μ.muStrong * g.pay m a .strong + (1 - μ.muStrong) * g.pay m a .weak

/-- 接收者最优回应（两行动菜单：选的行动不劣于另一行动）。abbrev＝可归约。 -/
abbrev receiverBR (g : SigGame) (m : Bool) (μ : Belief) (sR : Bool → Bool) : Prop :=
  euR g m μ (sR m) ≥ euR g m μ (!(sR m))

/-- 发送者型 t 发 m 后按接收者策略的收益。 -/
def senderPay (g : SigGame) (sR : Bool → Bool) (t : SigType) (m : Bool) : ℚ :=
  g.uS m (sR m) t

/-- 发送者型 t 最优回应（两消息菜单）。abbrev＝可归约。 -/
abbrev senderBR (g : SigGame) (sS : SigType → Bool) (sR : Bool → Bool)
    (t : SigType) : Prop :=
  senderPay g sR t (sS t) ≥ senderPay g sR t (!(sS t))

/-- 序贯均衡检查器（Bool 参考核）：两信息集一致性 ∧ 接收者两信息集最优回应 ∧
发送者两型最优回应（§8.3：每个信息集全部纯延续计划的条件收益不增）。 -/
def seqEqCheckB (g : SigGame) (sS : SigType → Bool) (sR : Bool → Bool)
    (μL μH : Belief) : Bool :=
  decide (consistentB g sS true μL) && decide (consistentB g sS false μH) &&
    decide (receiverBR g true μL sR) && decide (receiverBR g false μH sR) &&
    decide (senderBR g sS sR .strong) && decide (senderBR g sS sR .weak)

/-- 检查器双侧互译（六项合取分解）。 -/
theorem seqEqCheckB_iff (g : SigGame) (sS : SigType → Bool) (sR : Bool → Bool)
    (μL μH : Belief) :
    seqEqCheckB g sS sR μL μH = true ↔
      consistentB g sS true μL ∧ consistentB g sS false μH ∧
      receiverBR g true μL sR ∧ receiverBR g false μH sR ∧
      senderBR g sS sR .strong ∧ senderBR g sS sR .weak := by
  simp only [seqEqCheckB, Bool.and_eq_true, decide_eq_true_iff]

/-- **全部延续偏离无益（接收者侧）**：两纯行动的检查通过 ⇒ 任意凸组合偏离
（§8.3：完美记忆保证混合偏离为纯延续计划的凸组合——两行动菜单上凸组合即
全部混合延续）也不增收益。 -/
theorem receiver_all_continuation_no_gain (g : SigGame) (m : Bool) (μ : Belief)
    (a₀ : Bool) (h0 : euR g m μ a₀ ≥ euR g m μ true)
    (h1 : euR g m μ a₀ ≥ euR g m μ false)
    (w : ℚ) (hw : 0 ≤ w ∧ w ≤ 1) :
    w * euR g m μ true + (1 - w) * euR g m μ false ≤ euR g m μ a₀ := by
  have hw0 : 0 ≤ 1 - w := by linarith
  have e1 : w * euR g m μ true ≤ w * euR g m μ a₀ :=
    mul_le_mul_of_nonneg_left h0 hw.1
  have e2 : (1 - w) * euR g m μ false ≤ (1 - w) * euR g m μ a₀ :=
    mul_le_mul_of_nonneg_left h1 hw0
  have hcomb : w * euR g m μ a₀ + (1 - w) * euR g m μ a₀ = euR g m μ a₀ := by
    ring
  linarith

/-- **全部延续偏离无益（发送者侧）**：两消息的检查通过 ⇒ 任意混合消息偏离
不增收益（同一凸组合论证，收益面为发送者支付）。 -/
theorem sender_all_continuation_no_gain (g : SigGame) (sR : Bool → Bool) (t : SigType)
    (m₀ : Bool) (h0 : senderPay g sR t m₀ ≥ senderPay g sR t true)
    (h1 : senderPay g sR t m₀ ≥ senderPay g sR t false)
    (w : ℚ) (hw : 0 ≤ w ∧ w ≤ 1) :
    w * senderPay g sR t true + (1 - w) * senderPay g sR t false
      ≤ senderPay g sR t m₀ := by
  have hw0 : 0 ≤ 1 - w := by linarith
  have e1 : w * senderPay g sR t true ≤ w * senderPay g sR t m₀ :=
    mul_le_mul_of_nonneg_left h0 hw.1
  have e2 : (1 - w) * senderPay g sR t false ≤ (1 - w) * senderPay g sR t m₀ :=
    mul_le_mul_of_nonneg_left h1 hw0
  have hcomb : w * senderPay g sR t m₀ + (1 - w) * senderPay g sR t m₀
      = senderPay g sR t m₀ := by
    ring
  linarith

/-- 合成见证博弈：先验 1/2；接收者在 L：u=(2,2)、d=(1,1)（恒选 u）；在 H：
u=(1,1)、d=(0,0)（恒选 u）；发送者发 L 得 3（接收者 u）、发 H 得 1——两型同发
L（池化），H 为离轨信息集。 -/
def demoGame : SigGame :=
  { prior := 1 / 2, hprior := ⟨by norm_num, by norm_num⟩,
    pay := fun m a _t =>
      if a then (if m then (2 : ℚ) else (1 : ℚ)) else (if m then (1 : ℚ) else (0 : ℚ)),
    uS := fun m a _t =>
      if m then (if a then (3 : ℚ) else (0 : ℚ)) else (if a then (1 : ℚ) else (0 : ℚ)) }

/-- **T114 原反例见证（独立保留）**：池化均衡在一致信念 μL＝先验 1/2 下通过
序贯检查器。 -/
theorem witness_pooling_seq_eq :
    seqEqCheckB demoGame (fun _ => true) (fun _ => true) ⟨1 / 2⟩ ⟨1 / 2⟩ = true := by
  decide

/-- **T114 原反例见证（独立保留）：不一致信念被拒**——池化下信息集 L 可达，
路径贝叶斯钉定 μL＝先验 1/2；谎报 9/10 被检查器拒绝。 -/
theorem witness_inconsistent_mu_rejected :
    seqEqCheckB demoGame (fun _ => true) (fun _ => true) ⟨9 / 10⟩ ⟨1 / 2⟩ = false := by
  decide

/-- **T114 原反例见证（独立保留）：离轨信念越界被拒**——H 离轨只要求支撑内
良构；3/2 越界被拒（不能任填）。 -/
theorem witness_offpath_unnormalized_rejected :
    seqEqCheckB demoGame (fun _ => true) (fun _ => true) ⟨1 / 2⟩ ⟨3 / 2⟩ = false := by
  decide

/-- 合成见证上的凸组合偏离读数：u 支配 d（2 > 1），任意混合不超 u——w=2/5 时
混合收益 7/5 ≤ 2。 -/
theorem witness_receiver_mixed_no_gain :
    (2 / 5 : ℚ) * euR demoGame true ⟨1 / 2⟩ true
      + (1 - 2 / 5) * euR demoGame true ⟨1 / 2⟩ false
      ≤ euR demoGame true ⟨1 / 2⟩ true := by
  decide

/-! ## T115：无限重复折扣（§8.3：尾界/离轨单偏离/可信惩罚阈值） -/

/-- 前 N 期折扣和（截断值——§8.3：无限和用有限尾界定理形式，不写无穷级数
极限）。 -/
def truncSum (δ : ℚ) (u : Nat → ℚ) (N : Nat) : ℚ := ∑ t ∈ Finset.range N, δ ^ t * u t

/-- 截断和只依赖窗口内的项。 -/
theorem truncSum_congr (δ : ℚ) {u u' : Nat → ℚ} {N : Nat}
    (h : ∀ s < N, u s = u' s) : truncSum δ u N = truncSum δ u' N :=
  Finset.sum_congr rfl fun t ht => by
    have hlt := Finset.mem_range.mp ht
    rw [h t hlt]

/-- 截断和的一层展开。 -/
theorem truncSum_succ (δ : ℚ) (u : Nat → ℚ) (N : Nat) :
    truncSum δ u (N + 1) = truncSum δ u N + δ ^ N * u N := by
  unfold truncSum
  rw [Finset.sum_range_succ]
  rfl

/-- 几何部分和恒等式（§8.3 几何级数的有限形式）：(1−δ)·∑_{t<k} δ^t = 1 − δ^k。 -/
theorem geom_partial (δ : ℚ) (k : Nat) :
    (1 - δ) * ∑ t ∈ Finset.range k, δ ^ t = 1 - δ ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
    ring

/-- **T115 独立结论之一（尾界·乘法形）**：δ∈[0,1)、逐期收益 |u t| ≤ M 时，
任意 N 起任意 k 期的折扣和满足 |·|·(1−δ) ≤ M·δ^N——无限重复不任意截断的
有限证书（§8.3：几何级数收敛且尾界 ≤ Mδ^N/(1−δ)）。 -/
theorem tail_bound_mul (δ M : ℚ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hM : 0 ≤ M)
    (u : Nat → ℚ) (hu : ∀ t, |u t| ≤ M) (N k : Nat) :
    |∑ t ∈ Finset.range k, δ ^ (N + t) * u (N + t)| * (1 - δ) ≤ M * δ ^ N := by
  have hpos : (0 : ℚ) ≤ 1 - δ := by linarith
  have hδpow : ∀ n : Nat, 0 ≤ δ ^ n := fun n => pow_nonneg hδ0 n
  have hsplit : |∑ t ∈ Finset.range k, δ ^ (N + t) * u (N + t)|
      ≤ ∑ t ∈ Finset.range k, |δ ^ (N + t) * u (N + t)| :=
    Finset.abs_sum_le_sum_abs (fun t => δ ^ (N + t) * u (N + t)) _
  have habs : ∀ t : Nat, |δ ^ (N + t) * u (N + t)| = δ ^ (N + t) * |u (N + t)| := by
    intro t
    rw [abs_mul, abs_of_nonneg (hδpow (N + t))]
  have hle1 : ∑ t ∈ Finset.range k, |δ ^ (N + t) * u (N + t)|
      ≤ ∑ t ∈ Finset.range k, δ ^ (N + t) * M := by
    refine Finset.sum_le_sum fun t _ => ?_
    rw [habs t]
    exact mul_le_mul_of_nonneg_left (hu (N + t)) (hδpow (N + t))
  have hfact : ∑ t ∈ Finset.range k, δ ^ (N + t) * M
      = δ ^ N * (∑ t ∈ Finset.range k, δ ^ t * M) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [pow_add]
    ring
  have hkey : (1 - δ) * (∑ t ∈ Finset.range k, δ ^ t * M) ≤ M := by
    have h2 : (∑ t ∈ Finset.range k, δ ^ t * M)
        = (∑ t ∈ Finset.range k, δ ^ t) * M := Finset.sum_mul _ _ _
    have h3 : (1 - δ) * ((∑ t ∈ Finset.range k, δ ^ t) * M)
        = ((1 - δ) * (∑ t ∈ Finset.range k, δ ^ t)) * M := by ring
    rw [h2, h3, geom_partial δ k]
    nlinarith [hM, hδpow k]
  calc |∑ t ∈ Finset.range k, δ ^ (N + t) * u (N + t)| * (1 - δ)
      ≤ (∑ t ∈ Finset.range k, δ ^ (N + t) * M) * (1 - δ) :=
        mul_le_mul_of_nonneg_right
          (le_trans hsplit (le_trans (Finset.sum_congr rfl fun t _ => habs t) hle1)) hpos
    _ = δ ^ N * ((1 - δ) * (∑ t ∈ Finset.range k, δ ^ t * M)) := by
        rw [hfact]
        ring
    _ ≤ δ ^ N * M := mul_le_mul_of_nonneg_left hkey (hδpow N)
    _ = M * δ ^ N := by ring

/-- **尾界（除法形，§8.3 原式）**：折扣和尾部 ≤ M·δ^N/(1−δ)。 -/
theorem tail_bound (δ M : ℚ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hM : 0 ≤ M)
    (u : Nat → ℚ) (hu : ∀ t, |u t| ≤ M) (N k : Nat) :
    |∑ t ∈ Finset.range k, δ ^ (N + t) * u (N + t)| ≤ M * δ ^ N / (1 - δ) := by
  have hpos : (0 : ℚ) < 1 - δ := by linarith
  exact (le_div_iff₀ hpos).mpr (tail_bound_mul δ M hδ0 hδ1 hM u hu N k)

/-- 折扣估值：满足 Bellman 递归 V t = u t + δ·V (t+1)、且逐点乘法有界的赋值
（§8.3：V = r + δPV 的单状态流形式；有界性＝几何级数收敛前提）。 -/
structure DiscountVal (M : ℚ) (u : Nat → ℚ) where
  delta : ℚ
  hd0 : 0 ≤ delta
  hd1 : delta < 1
  V : Nat → ℚ
  hrec : ∀ t, V t = u t + delta * V (t + 1)
  hbnd : ∀ t, |V t| * (1 - delta) ≤ M

/-- 望远镜展开（§8.3：V = r + δPV 逐层代入的有限形式）。 -/
theorem val_telescoping (M : ℚ) (u : Nat → ℚ) (v : DiscountVal M u) (N : Nat) :
    v.V 0 = truncSum v.delta u N + v.delta ^ N * v.V N := by
  induction N with
  | zero => simp [truncSum]
  | succ N ih =>
    rw [ih]
    have hrecN := v.hrec N
    simp only [truncSum, Finset.sum_range_succ, pow_succ]
    rw [hrecN]
    ring

/-- **估值尾界**：任意截断与估值的差被 M·δ^N 控制（乘法形）——估值与截断的
距离由尾界给出，不构造极限（§8.3）。 -/
theorem val_tail_bound (M : ℚ) (u : Nat → ℚ) (v : DiscountVal M u) (N : Nat) :
    |v.V 0 - truncSum v.delta u N| * (1 - v.delta) ≤ M * v.delta ^ N := by
  have hterm : v.V 0 - truncSum v.delta u N = v.delta ^ N * v.V N := by
    have htel := val_telescoping M u v N
    linarith
  have hδN : 0 ≤ v.delta ^ N := pow_nonneg v.hd0 N
  have hbound := v.hbnd N
  rw [hterm, abs_mul, abs_of_nonneg hδN]
  nlinarith [hbound, hδN]

/-- **T115 独立结论之二（离轨单偏离原理）**：任何单期替换（其余按原流，全称
量化替换行动与期号）都不获利时，只在窗口内行动不同的任何替代流整体不获利
（§8.3：任意有限偏离由从末次开始替换不提高收益）。替代流 b 全称量化在 N 之后，
使归纳假设可代入"撤回末次偏离"后的中间流。 -/
theorem one_dev_principle (δ : ℚ) (g : Nat → Bool → ℚ) (a : Nat → Bool) (N : Nat)
    (h1 : ∀ t < N, ∀ x : Bool,
      truncSum δ (fun s => g s (if s = t then x else a s)) N
        ≤ truncSum δ (fun s => g s (a s)) N)
    (b : Nat → Bool) (h2 : ∀ s, N ≤ s → b s = a s) :
    truncSum δ (fun s => g s (b s)) N ≤ truncSum δ (fun s => g s (a s)) N := by
  induction N with
  | zero => intro h1 b _; simp [truncSum]
  | succ N ih =>
    intro h1 b h2
    by_cases hbN : b N = a N
    · -- 末位一致：限制假设后直接用归纳
      have key := ih (fun t ht x => h1 t (Nat.lt_succ_of_lt ht) x) b (by
        intro s hs
        rcases Nat.lt_or_ge s N with hlt | hge
        · have hbad : s < s := Nat.lt_of_lt_of_le hlt hs
          exact absurd hbad (Nat.lt_irrefl s)
        · by_cases heq : s = N
          · rw [heq]; exact hbN
          · exact h2 s (by omega))
      simp only [truncSum_succ, hbN]
      linarith
    · -- 末位不同：从末次替换读出单期不获利，再接归纳
      have h1N := h1 N (Nat.lt_succ_self N) (b N)
      have devEq : truncSum δ (fun s => g s (if s = N then b N else a s)) (N + 1)
          = truncSum δ (fun s => g s (a s)) N + δ ^ N * g N (b N) := by
        rw [truncSum_succ δ _ N]
        have hpre : truncSum δ (fun s => g s (if s = N then b N else a s)) N
            = truncSum δ (fun s => g s (a s)) N :=
          truncSum_congr δ (N := N) (u := fun s => g s (if s = N then b N else a s))
            (u' := fun s => g s (a s))
            (fun s hs => congrArg (g s) (if_neg (Nat.ne_of_lt hs)))
        rw [hpre]
        show truncSum δ (fun s => g s (a s)) N
            + δ ^ N * g N (if N = N then b N else a N)
            = truncSum δ (fun s => g s (a s)) N + δ ^ N * g N (b N)
        rw [if_pos rfl]
      rw [devEq] at h1N
      simp only [truncSum_succ] at h1N
      -- h1N : truncSum(a,N) + δ^N·g N (b N) ≤ truncSum(a,N) + δ^N·g N (a N)
      have ihApp : truncSum δ (fun s => g s (if s = N then a N else b s)) N
          ≤ truncSum δ (fun s => g s (a s)) N :=
        ih (fun t ht x => h1 t (Nat.lt_succ_of_lt ht) x)
          (fun s => if s = N then a N else b s)
          (by
            intro s hs
            show (if s = N then a N else b s) = a s
            rcases Nat.lt_or_ge s N with hlt | hge
            · have hbad : s < s := Nat.lt_of_lt_of_le hlt hs
              exact absurd hbad (Nat.lt_irrefl s)
            · by_cases heq : s = N
              · rw [heq, if_pos rfl]
              · rw [if_neg heq, h2 s (by omega)]))
      have preEq : truncSum δ (fun s => g s (if s = N then a N else b s)) N
          = truncSum δ (fun s => g s (b s)) N :=
        truncSum_congr δ (N := N) (u := fun s => g s (if s = N then a N else b s))
          (u' := fun s => g s (b s))
          (fun s hs => congrArg (g s) (if_neg (Nat.ne_of_lt hs)))
      rw [preEq] at ihApp
      simp only [truncSum_succ]
      linarith

/-- **T115 独立结论之三（可信惩罚阈值，§8.3 原式）**：合作值 R/(1−δ) 不低于
背离值 T+δ·P/(1−δ) 当且仅当 δ ≥ (T−R)/(T−P)（T>P 时阈值正）。惩罚路径本身
须为其子博弈允许行动（credibility）——由许可谓词前置承担，见
`punishPermitted`。 -/
theorem coop_threshold_iff (R T P δ : ℚ) (hTP : P < T) (hδ1 : δ < 1) (hδ0 : 0 ≤ δ) :
    (T + δ * P / (1 - δ) ≤ R / (1 - δ)) ↔ ((T - R) / (T - P) ≤ δ) := by
  have hpos : (0 : ℚ) < 1 - δ := by linarith
  have hq : (0 : ℚ) < T - P := by linarith
  have hM1 : (1 : ℚ) - δ ≠ 0 := by linarith
  have hmul : ∀ X : ℚ, (1 - δ) * (X / (1 - δ)) = X := by
    intro X
    rw [mul_comm, div_mul_cancel₀ _ hM1]
  have e1 : (T + δ * P / (1 - δ)) * (1 - δ) = T * (1 - δ) + δ * P := by
    rw [mul_add, div_mul_cancel₀ (δ * P) hM1]
  constructor
  · intro h
    have he := (le_div_iff₀ hpos).mp h
    rw [e1] at he
    refine (div_le_iff₀ hq).mpr ?_
    linarith
  · intro h
    have h2 : T * (1 - δ) + δ * P ≤ R := by
      have he := (div_le_iff₀ hq).mp h
      linarith
    refine (le_div_iff₀ hpos).mpr ?_
    rw [e1]
    exact h2

/-- 可信性前置（§8.3：惩罚必须本身为其子博弈允许/可信行动）：惩罚路径在允许
行动集内的谓词位，作为阈值定理适用的独立检查项（缺许可则不给"可信"结论）。 -/
def punishPermitted (permitted : Bool → Bool) : Prop := permitted false = true

/-- 合成数值见证：R=3、T=4、P=2 → 阈值 (4−3)/(4−2) = 1/2；δ=2/3 合作维持、
δ=1/3 背离获利。 -/
theorem witness_threshold_directions :
    ((4 : ℚ) + (2 / 3) * 2 / (1 - 2 / 3) ≤ 3 / (1 - 2 / 3) ↔
      (4 - 3 : ℚ) / (4 - 2) ≤ 2 / 3) ∧
    ¬ ((4 : ℚ) + (1 / 3) * 2 / (1 - 1 / 3) ≤ 3 / (1 - 1 / 3)) ∧
    (4 - 3 : ℚ) / (4 - 2) = 1 / 2 := by
  refine ⟨?_, ?_, ?_⟩
  · exact coop_threshold_iff 3 4 2 (2 / 3) (by norm_num) (by norm_num) (by norm_num)
  · intro h
    have hth := (coop_threshold_iff 3 4 2 (1 / 3) (by norm_num) (by norm_num)
      (by norm_num)).mp h
    norm_num at hth
  · norm_num

/-- 尾界见证：每期惩罚收益 2、δ=2/3——从 N=1 起 5 期的折扣和满足乘法尾界
（实例读数，直接由一般定理给出）。 -/
theorem witness_tail_bound_instance :
    |∑ t ∈ Finset.range 5, (2 / 3 : ℚ) ^ (1 + t) * 2| * (1 - 2 / 3)
      ≤ 2 * (2 / 3 : ℚ) ^ 1 :=
  tail_bound_mul (2 / 3) 2 (by norm_num) (by norm_num) (by norm_num)
    (fun _ => (2 : ℚ)) (fun _ => by decide) 1 5

/-- 惩罚可信性见证：许可谓词 full（两行动都许可）满足可信前置。 -/
def permittedFull : Bool → Bool := fun _ => true

theorem witness_punish_credible : punishPermitted permittedFull := rfl

/-! ## W4 博弈批旗舰（四项独立结论在同一见证包上的合取读出） -/

/-- **旗舰定理**：T112 双线域内合成＋异源拒绝＋越界裁剪回域、T113 后向归纳
单步全不获利＋数值例 (60,40)、T114 池化序贯检查通过＋不一致信念被拒、
T115 尾界实例＋可信惩罚阈值双向读数——四件独立结论同时成立（各项独立定理
见上；反例另行独立保留，不合入旗舰）。 -/
theorem w4_games_flagship :
    -- T112
    (dual_line_stays_normative normDomainDemo 25 40).1 ∧
    composeGateB certRespDemo certPrevForeignDemo = false ∧
    penaltyInDomainB normDomainDemo
      (PenaltyKind.fixed (clipTo normDomainDemo (25 + 40))) = true ∧
    -- T113
    bi_one_step_no_gain bParamsDemo ∧
    biOutcome bParamsDemo = ((60 : ℚ), (40 : ℚ)) ∧
    -- T114
    seqEqCheckB demoGame (fun _ => true) (fun _ => true) ⟨1 / 2⟩ ⟨1 / 2⟩ = true ∧
    seqEqCheckB demoGame (fun _ => true) (fun _ => true) ⟨9 / 10⟩ ⟨1 / 2⟩ = false ∧
    -- T115
    ((∀ t : Nat, |(2 : ℚ)| ≤ 2) →
      |∑ t ∈ Finset.range 5, (2 / 3 : ℚ) ^ (1 + t) * 2|
        ≤ 2 * (2 / 3 : ℚ) ^ 1 / (1 - 2 / 3)) ∧
    ((4 : ℚ) + (2 / 3) * 2 / (1 - 2 / 3) ≤ 3 / (1 - 2 / 3) ↔
      (4 - 3 : ℚ) / (4 - 2) ≤ 2 / 3) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (dual_line_stays_normative normDomainDemo 25 40).1
  · exact witness_foreign_facts_rejected
  · exact witness_prevention_clipped.2.1
  · exact bi_one_step_no_gain bParamsDemo
  · exact witness_bargain_bi.2
  · exact witness_pooling_seq_eq
  · exact witness_inconsistent_mu_rejected
  · intro h
    exact tail_bound (2 / 3 : ℚ) 2 (by norm_num) (by norm_num) (by norm_num)
      (fun _ => (2 : ℚ)) h 1 5
  · exact coop_threshold_iff 3 4 2 (2 / 3) (by norm_num) (by norm_num) (by norm_num)

end JurisLean.Seams.UnifiedW4Games
