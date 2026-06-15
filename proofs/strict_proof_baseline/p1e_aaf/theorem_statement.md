# Theorem Statements: E1, E2, E3

## 文件信息

- **路径**: `p1e_aaf/theorem_statement.md`
- **项目**: juris-calculus 严格数学证明返工
- **日期**: 2026-06-11
- **作者**: AAF/Fixed-Point Proof Engineer

---

## Theorem E1: 有限 Dung AAF 的 Grounded Extension 存在唯一性

### 形式化 Statement

设 AF = ⟨Args, Att⟩ 是一个有限 Dung 抽象论证框架，其中：
- Args 是有限非空的 arguments 集合
- Att ⊆ Args × Args 是有向攻击关系

定义 characteristic function F: 2^Args → 2^Args 为：

```
F(S) = { a ∈ Args | ∀b ∈ Args: (b, a) ∈ Att → ∃c ∈ S: (c, b) ∈ Att }
```

即：F(S) 是所有被 S " defended " 的 arguments 的集合。

**Theorem E1.1 (存在性)**: 对任意有限 AF，grounded extension GE(AF) 存在。

**Theorem E1.2 (唯一性)**: 对任意有限 AF，grounded extension GE(AF) 唯一。

**Theorem E1.3 (收敛性)**: 对任意有限 AF，Kleene 迭代序列 ∅, F(∅), F²(∅), … 在有限步内收敛到 GE(AF)。

**Theorem E1.4 (收敛深度上界)**: 对 |Args| = n 的有限 AF，Kleene 迭代在 ≤ n 步内收敛。

### 证明方法

- **E1.1-E1.3**: 基于 Tarski 不动点定理（F 在完备格 (2^Args, ⊆) 上是单调算子）。
- **E1.4**: 穷举验证（n ≤ 4，2^(n²) 个攻击图）。

### Epistemic Status

- **n ≤ 4**: PROVED_BY_EXHAUSTIVE_ENUMERATION
- **一般有限情形**: OPEN_CONJECTURE（依赖 Tarski 定理的标准证明，但收敛深度上界 n 需要归纳证明）

---

## Theorem E2: 分层评估器的正确性条件

### 形式化 Statement

设：
- H 是有限 Horn 规则集
- R 是有限 rebuttal/exception 规则集
- Props 是有限命题符号集

定义分层评估器为四阶段管道：

**Stage 1**: closure_H: 2^Props → 2^Props
```
closure_H(S) = S ∪ { q | ∃(p₁ ∧ … ∧ pₙ → q) ∈ H: {p₁, …, pₙ} ⊆ S }
```

**Stage 2**: attack_graph: 2^Props → AttackGraph
```
attack_graph(C) = ⟨C, { (p, q) ∈ R | p ∈ C ∧ q ∈ C }⟩
```

**Stage 3**: grounded_extension: AttackGraph → 2^Props
```
grounded_extension(G) = lfp(F_G)  （F_G 是 G 的 characteristic function）
```

**Stage 4**: output: 2^Props → Result

**Theorem E2.1 (Stage 1 单调性)**: closure_H 是单调算子，即 S ⊆ T → closure_H(S) ⊆ closure_H(T)。

**Theorem E2.2 (Stage 2 确定性)**: attack_graph 是确定性函数，即给定 C 和 R，attack_graph(C) 唯一。

**Theorem E2.3 (Stage 3 收敛性)**: 对 Stage 2 输出的有限攻击图 G，grounded_extension(G) 存在、唯一，且 Kleene 迭代有限步收敛。

**Conjecture E2.4a (等价条件)**: 若攻击图是 DAG 且 confidence-zeroing 语义等价于 defeat，则分层评估器的输出等于原 evaluator 的输出。

**Theorem E2.4b (不等价条件)**: 若攻击图中存在有向循环，则分层评估器与原 evaluator 不等价。

### Epistemic Status

| 子定理 | 状态 |
|--------|------|
| E2.1 | PROVED_FORMAL |
| E2.2 | PROVED_FORMAL |
| E2.3 | PROVED_BY_EXHAUSTIVE_ENUMERATION (n ≤ 4) |
| E2.4a | OPEN_CONJECTURE |
| E2.4b | REFUTED_BY_COUNTEREXAMPLE |

---

## Theorem E3: 原始 Evaluator 不满足 Tarski 单调性

### 形式化 Statement

设原 evaluator 的 operator 为 F_orig: 2^Args → 2^Args：

```
F_orig(S) = { a ∈ S | ¬∃b ∈ S: (b, a) ∈ Att }
```

即：F_orig(S) 是 S 中未被 S 内任何 argument 攻击的 arguments。

**Theorem E3.1 (非单调性)**: F_orig 不是单调算子。

即：存在 A, B ⊆ Args，使得 A ⊆ B 但 F_orig(A) ⊈ F_orig(B)。

### 反例

设 Args = {a, b}，Att = {(b, a)}。

- A = {a}，F_orig(A) = {a}（a 在 A 中无攻击者）
- B = {a, b}，F_orig(B) = ∅（b 攻击 a，a 被移除）

验证：A ⊆ B，但 F_orig(A) = {a} ⊈ ∅ = F_orig(B)。

### Epistemic Status

- **E3.1**: REFUTED_BY_COUNTEREXAMPLE

### 推论

由于 F_orig 不满足单调性：
1. 不能保证 least fixpoint 存在（Tarski 定理的前提不满足）。
2. 即使 fixpoint 存在，也不能保证唯一。
3. Kleene 迭代可能不收敛或收敛到非预期结果。

---

## 依赖关系图

```
E2.1 (Horn closure 单调性) ──┐
                              ├──→ E2.3 (Stage 3 收敛性) ──→ E2 (整体正确性)
E1 (Grounded extension) ───────┘
                              
E3 (Evaluator 非单调性) ──────→ E2.4b (不等价条件)
                              
E2.4a (等价条件) ─────────────→ OPEN_CONJECTURE
```

---

## 文件清单

| 文件 | 内容 | 对应定理 |
|------|------|----------|
| `aaf_grounded_extension_proof.py` | 穷举验证 n ≤ 4 | E1 |
| `evaluator_nonmonotone_counterexample.py` | 非单调性反例 | E3 |
| `stratified_evaluator_correctness_conditions.md` | 分层评估器条件 | E2 |
| `p1e_aaf/theorem_statement.md` | 定理形式化陈述 | E1, E2, E3 |
