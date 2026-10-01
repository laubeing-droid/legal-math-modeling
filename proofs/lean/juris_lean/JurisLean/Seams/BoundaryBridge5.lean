import JurisLean.ULM14CoverageTrust
import JurisLean.ReceiptAuthority
import Mathlib.Order.MinMax

/-!
# ⑤ 两版聚合的**共同抽象**（桥接件 · 非等价件）

> 契约来源：`docs/master-plan/06_六类边界绑定表.md` §二第 5 行、§五行、§七表（164 行）
> "⑤ | 信任向量 meet 与权限秩升级之间的桥接 | 需两套序的统一载体或转换定理"。
> 本件交付的就是那个**统一载体**。§五禁止的是"桥接等价"主张，本件**不**主张等价。

## §法律语义

法律担保的聚合在本仓有两种写法，它们对"抬高保证"的方向感相反：

- **⑤-A 信任向量版**（主干内）：`ULM14CoverageTrust.lean:70-76` 的 `TrustVector`（五坐标，
  坐标类型 `TrustLevel := Fin 3`，`:68`），汇合运算 `TrustVector.meet`（`:78`）逐坐标取小，
  序 `TrustLE`（`:85`）逐坐标比较。法律含义：来源/文本/事实/证明/权威是**五类不可互换**的担保
  （`:67` 注释），一份低担保不能被别份的高值掩盖，所以汇合只能取最小。
- **⑤-B 权限秩版**（主干外）：`ReceiptAuthority.lean:23-27` 的 `authorityRank`（四级 → 0..3），
  `consensusRank`（`:102-103`）是**秩的 `foldr max`**。法律含义：共识取的是"在场最高档位"，
  多数重复不产生档位提升（`:101` 注释、`:106` 定理）。

两版共同满足的法律要求只有一条：**聚合结果不得越过各分量共同尊重的那个界**。
A 版更强（结果 ≤ 每一分量），B 版方向相反（结果 ≥ 每一分量，且 ≤ 任一公共上界）。
因此诚实的桥是**同一条律的两个模型**，不是两版之间的等价。

## §数学对象

- `BoundClosedAgg`：二元聚合 `op` + 序 `le` + **唯一**实质公理 `bound_closed`。
  这是两版都真成立的性质，也是本件的桥；刻意不要求自反、传递、结合、交换。
- `MeetAgg`：A 形加强载体（`le_left`、`le_right`、`le_trans`）。
  `bb5_meetAggToBoundClosed` 给出**唯一方向**的化归（加强 ⇒ 界封闭）；反向不成立，
  机器反例见 `bb5_consensusRank_not_meet_reading`。
- 抽象定理两条：`bb5_foldr_bound_closed`（列表归纳，只用那一条公理）、
  `bb5_meet_foldr_le_head`（A 形：非空折叠不高于首分量，无需界假设）。
- 两个既有结果的载体各成实例：`bb5_trustMeetAgg`（`TrustVector.meet` / `TrustLE`）、
  `bb5_natMaxBoundClosedAgg`（`Nat.max` / `Nat.le`），另加 `bb5_natMinMeetAgg`（`Nat.min`）。

## §证与不证

- 证（对抽象的**全体**输入成立，非逐例枚举）：`bb5_foldr_bound_closed`、
  `bb5_meet_foldr_le_head`（后者仅对 `MeetAgg` 输入成立）、`bb5_nat_max_bound_closed`、
  `bb5_nat_min_le_left`、`bb5_nat_min_le_right`、`bb5_consensusRank_eq_foldr_max`、
  `bb5_consensusRank_rank_mem_bound`、`bb5_consensusRank_ge_component`、
  `bb5_consensusRank_not_meet_reading`。
- 证（两版作为该抽象的模型 —— 桥的两侧）：`bb5_trust_aggregate_not_raised_above_bound`、
  `bb5_trust_aggregate_le_head`（仅 TrustVector）、
  `bb5_nat_min_aggregate_not_raised_above_bound`（仅 Nat）、
  `bb5_consensus_rank_not_raised_above_bound`（仅 AuthorityLevel 列表，经 `Nat.max` 模型）。
- **不证**：两版之间的等价或转换定理。§五禁止该主张，且上面两条反向陈述给出了方向相反的
  证明级理由，桥只能是共同抽象。
- **不证**：`Seams/BoundaryClosure.lean` 的 ⑤ 两条界定定理（现工作树 `:572`
  `closure_boundary5_trust_not_raised`、`:624` `closure_boundary5_consensus_not_escalating`）
  可由本抽象导出。那两条定理本件**不引用、不修改、不重述**（单写者避让：该文件正在被他方编辑，
  族层载体 `TrustAggregateOp` / `ConsensusOp` 在其 `:557` / `:593`）。
  注：该在编文件的行号会随对方提交漂移，**以定理名为准**。
- **不证**：全调用链意义上的"任何写法都不能靠聚合抬高保证"（§三第 2 档），本件仍是片段强度。

## §未覆盖片段

- 这座桥是**共同抽象**（一条律的两个模型），**不是**两版等价：本件未定义任何
  `TrustVector ↔ AuthorityLevel` 转换函数，也不主张两套 arity（3 与 4）或两套序方向相同。
- **族层未接**：⑤ 的两条界定定理是 `ConsensusOp` / `TrustAggregateOp` **归纳族**上的封闭性，
  族内另有 `compose` / `merge` 生成方式。把它们接到本抽象需要 import 那个在编文件，
  与单写者规则冲突，故本件未做，此债记在 `Seams/BoundaryClosure.lean` 一侧。
  特别注意：`merge`（列表拼接）**看上去**可在本抽象下闭合（拼接后仍逐元素受界），
  但本件未证该式，故不得读成"族层已被本件覆盖"，更不构成与本件陈述的等价主张。
- **B 版不是 `Nat.min` 读法**：任务书假设"`consensusRank` 可证 ≤ 每一所列秩"**为假**。
  定义是 `foldr max 0`，反例 `[.untrustedProposal, .admittedFormalInput]` 的共识秩为 3，
  而首分量秩为 0；该否定已由 `bb5_consensusRank_not_meet_reading` 钉成正定理。
  B 版的界封闭因此走 `Nat.max` 模型。
- **抽象层的自反性缺口**（UNPROVED，登记为 `bb5_meetFoldLeEachComponentObligation`）：
  `MeetAgg` 不假设 `le` 自反，故"折叠 ≤ 起点 `s`"在 `xs = []` 时不可导出（此时结论即 `le s s`）。
  该加强式对 `TrustVector` / `Nat.min` 这些具体实例另行闭合属于载体层工作，本件不做，
  也不得读成"抽象不足"之外的结论。
- 本件只使用主干已证的 `trust_meet_le_left` / `trust_meet_le_right`；
  未把 `TrustVector.meet` 与 `Fin 3` 的格结构定理（`Lattice` 层）挂钩。

## §档位

- 载体层：两版载体都在既有主干/主干外文件内；本件零新载体，只新增抽象层与实例化。
- 界定定理层：**片段强度**。`bb5_foldr_bound_closed` 对 `BoundClosedAgg` 全体输入成立，
  但"全体输入"限于本件定义的这一个类，不等于"全体聚合写法"。
- 审计面：本件 15 条定理名**尚未**进入 `AxiomAudit.lean` 具名面，也未进 `JurisLean.lean` 发布根
  与 `Seams/All.lean`（按派工要求刻意不入）。故本件的公理读数是 `CI_NOT_RUN`；
  GitHub Actions 才是 Lean 权威，本地 `lake build` 只是**临时预检**，不构成 Lean PASS。
- 禁止读法：不得读成"⑤两版已桥接等价"、"权限秩版是信任向量版的实例"、
  "聚合不抬高保证已对全体代码成立"、或"本件导出了 `closure_boundary5_*` 两条"。
-/

namespace JurisLean.Seams.BoundaryBridge5

open JurisLean.ULM

/-! ============================================================
    第一节 共同抽象：界封闭的聚合
    ============================================================ -/

/-- 中文说明：⑤的共同载体。只有一个实质公理 `bound_closed`：
两个都不越过 `K` 的分量，其聚合也不越过 `K`。
不要求自反、传递、结合、交换 —— 抽象层刻意取**两版都真成立的最弱形状**。 -/
structure BoundClosedAgg (α : Type) where
  op : α → α → α
  le : α → α → Prop
  bound_closed : ∀ a b K, le a K → le b K → le (op a b) K

/-- 中文说明：⑤-A 版（信任向量形）的加强载体：聚合值不高于**每个**分量，另需传递性。
加强形可化归到界封闭形（`bb5_meetAggToBoundClosed`），反向不成立
（机器反例见 `bb5_consensusRank_not_meet_reading`）。 -/
structure MeetAgg (α : Type) where
  op : α → α → α
  le : α → α → Prop
  le_left : ∀ a b, le (op a b) a
  le_right : ∀ a b, le (op a b) b
  le_trans : ∀ a b c, le a b → le b c → le a c

/-- 中文证明（抽象主定理）：任意有限个分量折成 `foldr op s`，只要起点 `s` 与每个分量
都不越过 `K`，结果就不越过 `K`。证明只用列表归纳与 `bound_closed` 这一条公理，
故对 `BoundClosedAgg` 的**全体**输入成立（不是逐例枚举）。 -/
theorem bb5_foldr_bound_closed {α : Type} (A : BoundClosedAgg α) (s K : α) :
    ∀ (xs : List α), A.le s K → (∀ x ∈ xs, A.le x K) → A.le (xs.foldr A.op s) K := by
  intro xs
  induction xs with
  | nil => intro hs _hxs; exact hs
  | cons y ys ih =>
      intro hs hxs
      refine A.bound_closed y (ys.foldr A.op s) K ?_ ?_
      · exact hxs y List.mem_cons_self
      · exact ih hs (fun x hx => hxs x (List.mem_cons_of_mem y hx))

/-- 中文证明（抽象·A 形加强陈述）：非空 meet 折叠不高于其**首分量**，无需任何界假设。
本条只对 `MeetAgg` 的输入成立；B 版（`max`）不满足它（见第五节）。 -/
theorem bb5_meet_foldr_le_head {α : Type} (M : MeetAgg α) (a : α) (xs : List α) (s : α) :
    M.le ((a :: xs).foldr M.op s) a :=
  M.le_left a (xs.foldr M.op s)

/-- 中文说明：加强形 ⇒ 界封闭形（唯一的化归方向）。只用 `le_left` 与传递性。 -/
def bb5_meetAggToBoundClosed {α : Type} (M : MeetAgg α) : BoundClosedAgg α where
  op := M.op
  le := M.le
  bound_closed := fun a b K ha _hb => M.le_trans (M.op a b) a K (M.le_left a b) ha

/-! ============================================================
    第二节 A 版实例：TrustVector.meet / TrustLE
    ============================================================ -/

/-- 中文证明：`TrustLE` 的传递性，本件自证。
主干 `Seams/BoundaryClosure.lean:548` 已有同性质的 `trustLE_trans`；本件不 import 该在编文件，
故在此重证一份并改名，避免与单写者冲突（内容未弱化：与主干那条同型）。 -/
theorem bb5_trustLE_trans {a b c : TrustVector}
    (hab : TrustLE a b) (hbc : TrustLE b c) : TrustLE a c :=
  ⟨le_trans hab.1 hbc.1, le_trans hab.2.1 hbc.2.1, le_trans hab.2.2.1 hbc.2.2.1,
    le_trans hab.2.2.2.1 hbc.2.2.2.1, le_trans hab.2.2.2.2 hbc.2.2.2.2⟩

/-- 中文说明：A 版是 `MeetAgg` 的实例。`op` 取 `TrustVector.meet`（`ULM14CoverageTrust.lean:78`），
`le` 取 `TrustLE`（`:85`），两侧不等式直接用主干已证的 `trust_meet_le_left`（`:92`）与
`trust_meet_le_right`（`:97`）。 -/
def bb5_trustMeetAgg : MeetAgg TrustVector where
  op := TrustVector.meet
  le := TrustLE
  le_left := trust_meet_le_left
  le_right := trust_meet_le_right
  le_trans := fun _ _ _ hab hbc => bb5_trustLE_trans hab hbc

/-- 中文证明（A 版·桥接陈述）：任意有限份信任向量的逐坐标 meet 折叠不越过共同界。
本条是抽象主定理在 `bb5_trustMeetAgg` 上的**实例**，只对 `TrustVector` 成立，
不得读成对 `TrustAggregateOp` 族的封闭性。 -/
theorem bb5_trust_aggregate_not_raised_above_bound (xs : List TrustVector) (s K : TrustVector)
    (hs : TrustLE s K) (hxs : ∀ x ∈ xs, TrustLE x K) :
    TrustLE (xs.foldr TrustVector.meet s) K :=
  bb5_foldr_bound_closed (bb5_meetAggToBoundClosed bb5_trustMeetAgg) s K xs hs hxs

/-- 中文证明（A 版·更强的一面）：非空 meet 折叠不高于首分量，无需界假设。 -/
theorem bb5_trust_aggregate_le_head (a : TrustVector) (xs : List TrustVector) (s : TrustVector) :
    TrustLE ((a :: xs).foldr TrustVector.meet s) a :=
  bb5_meet_foldr_le_head bb5_trustMeetAgg a xs s

/-! ============================================================
    第三节 Nat 上的两个模型：min 与 max
    ============================================================ -/

/-- 中文证明：`Nat.min` 的左界性质。用 `Mathlib/Order/Defs/LinearOrder.lean:155` 的
`min_le_left`（`Nat` 有 `LinearOrder`）。 -/
theorem bb5_nat_min_le_left (a b : Nat) : min a b ≤ a := min_le_left a b

/-- 中文证明：`Nat.min` 的右界性质。 -/
theorem bb5_nat_min_le_right (a b : Nat) : min a b ≤ b := min_le_right a b

/-- 中文证明：`max` 的界封闭性。用核心的 `Nat.max_le_of_le_of_le`
（`Init/Data/Nat/MinMax.lean:125`）。 -/
theorem bb5_nat_max_bound_closed (a b K : Nat) (ha : a ≤ K) (hb : b ≤ K) : max a b ≤ K :=
  Nat.max_le_of_le_of_le ha hb

/-- 中文说明：`Nat.min` 与 `≤` 构成 `MeetAgg Nat`（A 形载体在自然数上的模型）。 -/
def bb5_natMinMeetAgg : MeetAgg Nat where
  op := min
  le := Nat.le
  le_left := bb5_nat_min_le_left
  le_right := bb5_nat_min_le_right
  le_trans := fun _ _ _ => Nat.le_trans

/-- 中文说明：`Nat.max` 与 `≤` 只满足界封闭形，**不**满足 `MeetAgg`
（`max a b ≤ a` 一般为假，见第五节）。 -/
def bb5_natMaxBoundClosedAgg : BoundClosedAgg Nat where
  op := max
  le := Nat.le
  bound_closed := bb5_nat_max_bound_closed

/-- 中文证明（Nat.min 读法·桥接陈述）：有限个自然数取 min 折叠不越过共同界。
只对 `Nat` 与 `min` 这一具体模型成立。 -/
theorem bb5_nat_min_aggregate_not_raised_above_bound (xs : List Nat) (s K : Nat)
    (hs : s ≤ K) (hxs : ∀ x ∈ xs, x ≤ K) : xs.foldr min s ≤ K :=
  bb5_foldr_bound_closed (bb5_meetAggToBoundClosed bb5_natMinMeetAgg) s K xs hs hxs

/-! ============================================================
    第四节 B 版实例：authorityRank / consensusRank
    ============================================================ -/

/-- 中文证明：`consensusRank`（`ReceiptAuthority.lean:102-103` 的
`foldr (fun l acc => max (authorityRank l) acc) 0`）就是把秩列成 `Nat` 表后对 `max` 作右折叠。
本件据此把 B 版接进抽象。 -/
theorem bb5_consensusRank_eq_foldr_max (levels : List AuthorityLevel) :
    consensusRank levels = (levels.map authorityRank).foldr max 0 := by
  induction levels with
  | nil => rfl
  | cons y ys ih =>
      show max (authorityRank y) (consensusRank ys) =
        max (authorityRank y) ((ys.map authorityRank).foldr max 0)
      rw [ih]

/-- 中文证明：把法律式假设（每个投票的秩受界）迁成抽象式假设（秩像的每个元素受界）。 -/
theorem bb5_consensusRank_rank_mem_bound {levels : List AuthorityLevel} {K : Nat}
    (h : ∀ l ∈ levels, authorityRank l ≤ K) :
    ∀ n ∈ levels.map authorityRank, n ≤ K := by
  intro n hn
  cases List.mem_map.1 hn with
  | intro l hl =>
      rw [← hl.2]
      exact h l hl.1

/-- 中文证明（B 版·桥接陈述）：共识秩不越过任何"每个投票秩都不越过"的界。
本条是抽象主定理在 `bb5_natMaxBoundClosedAgg` 上的**实例**（`Nat.max` 模型，非 `Nat.min`），
与 A 版满足**同一条律**；这不构成两版等价（§五）。 -/
theorem bb5_consensus_rank_not_raised_above_bound (levels : List AuthorityLevel) (K : Nat)
    (h : ∀ l ∈ levels, authorityRank l ≤ K) : consensusRank levels ≤ K := by
  rw [bb5_consensusRank_eq_foldr_max]
  refine bb5_foldr_bound_closed bb5_natMaxBoundClosedAgg 0 K (levels.map authorityRank)
    (Nat.zero_le K) ?_
  exact bb5_consensusRank_rank_mem_bound h

/-! ============================================================
    第五节 为什么等价式不可陈述（方向相反 + 机器反例）
    ============================================================ -/

/-- 中文证明：B 版聚合值**不低于**每一分量的秩，即它是并（join）形而非 meet 形。
与 A 版的 `bb5_trust_aggregate_le_head` 方向相反，这就是两版之间不存在保序等价的技术理由。 -/
theorem bb5_consensusRank_ge_component :
    ∀ (levels : List AuthorityLevel) (l : AuthorityLevel),
      l ∈ levels → authorityRank l ≤ consensusRank levels := by
  intro levels
  induction levels with
  | nil => intro l hl; exact absurd hl List.not_mem_nil
  | cons y ys ih =>
      intro l hl
      show authorityRank l ≤ max (authorityRank y) (consensusRank ys)
      cases List.mem_cons.mp hl with
      | inl hy => rw [hy]; exact Nat.le_max_left _ _
      | inr hm => exact Nat.le_trans (ih l hm) (Nat.le_max_right _ _)

/-- 中文证明（机器反例）："consensusRank ≤ 每一所列秩"**为假**。
反例 `[.untrustedProposal, .admittedFormalInput]`：共识秩 `= max 0 (max 3 0) = 3`，
而首分量秩 `authorityRank .untrustedProposal = 0`，`3 ≤ 0` 不成立。
本条把任务书对 B 版的错前提固化为定理，防止后来者把 B 版当作 `Nat.min` 读法。 -/
theorem bb5_consensusRank_not_meet_reading :
    ¬ ∀ (levels : List AuthorityLevel), ∀ l ∈ levels, consensusRank levels ≤ authorityRank l := by
  intro h
  have hbad := h [.untrustedProposal, .admittedFormalInput] .untrustedProposal
    List.mem_cons_self
  have hval : consensusRank [.untrustedProposal, .admittedFormalInput] = 3 := by decide
  have hrank : authorityRank .untrustedProposal = 0 := rfl
  rw [hval, hrank] at hbad
  exact absurd hbad (by decide)

/-! ============================================================
    第六节 UNPROVED 义务登记（按 AGENTS.md：以 Prop 目标声明，不用公理或弱化命题冒充证明）
    ============================================================ -/

/-- 中文说明（状态 UNPROVED）：抽象层的**自反性缺口**义务。
`MeetAgg` 不假设 `le` 自反，故"折叠值 ≤ 起点 `s`"在 `xs = []` 时不可从公理导出
（此时结论正是 `le s s`）。该加强式对本件命名的两个模型（`TrustVector`、`Nat.min`）事实上成立，
但闭合它需要给载体补自反性，属载体层工作，本件**未证**，也不因此削弱第一节抽象定理。 -/
def bb5_meetFoldLeEachComponentObligation (α : Type) (M : MeetAgg α) : Prop :=
  ∀ (xs : List α) (s : α),
    (∀ y ∈ xs, M.le (xs.foldr M.op s) y) ∧ M.le (xs.foldr M.op s) s

/-- 中文说明：义务状态登记（UNPROVED）。 -/
def bb5_meetFoldObligationStatus : Bool := false

/-- 中文证明：登记一致性 —— UNPROVED 义务的状态不得被写成 closed。 -/
theorem bb5_registered_obligation_is_open : bb5_meetFoldObligationStatus = false := rfl

end JurisLean.Seams.BoundaryBridge5
