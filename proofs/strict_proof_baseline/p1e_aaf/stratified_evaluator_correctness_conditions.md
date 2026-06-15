# Theorem E2: 分层评估器的正确性条件

## Epistemic Status 概览

| 条件 | 状态 | 理由 |
|------|------|------|
| Stage 1: monotone Horn closure | **PROVED_FORMAL** | Horn closure 是标准单调算子 |
| Stage 2: static attack graph 确定性 | **PROVED_FORMAL** | 从 Horn closure 结果到攻击图的映射是函数 |
| Stage 3: grounded extension 收敛 (固定图) | **PROVED_BY_EXHAUSTIVE_ENUMERATION** (n <= 4) | 引用 Theorem E1 |
| Stage 跨图单调性 | **REFUTED_BY_COUNTEREXAMPLE** | 增加 premise 可能引入 unattacked attacker，打掉原本 grounded 的 argument |
| Stage 4a: 与原 evaluator 等价条件 | **OPEN_CONJECTURE** | 需要更严格的归纳证明 |
| Stage 4b: 与原 evaluator 不等价条件 | **REFUTED_BY_COUNTEREXAMPLE** | 引用 Theorem E3 |

---

## Stage 1: Monotone Horn Closure

### 定义

设 Horn 规则集为 H，每条规则形如：

```
p1 ∧ p2 ∧ … ∧ pn → q
```

其中 pᵢ 和 q 是命题符号。

定义 closure_H: 2^Props → 2^Props 为：

```
closure_H(S) = S ∪ { q | 存在规则 p1 ∧ … ∧ pn → q ∈ H，且 {p1, …, pn} ⊆ S }
```

### 定理 E2.1: closure_H 是单调算子

**Statement**: 对任意 S, T ⊆ Props，若 S ⊆ T，则 closure_H(S) ⊆ closure_H(T)。

**Proof**:

设 S ⊆ T。取任意 q ∈ closure_H(S)。有两种情况：

1. **q ∈ S**: 由于 S ⊆ T，有 q ∈ T ⊆ closure_H(T)。
2. **q ∉ S**: 则存在规则 p1 ∧ … ∧ pn → q ∈ H，使得 {p1, …, pn} ⊆ S。
   由于 S ⊆ T，有 {p1, …, pn} ⊆ T。
   因此 q ∈ closure_H(T)。

综上，closure_H(S) ⊆ closure_H(T)。∎

**Epistemic status**: PROVED_FORMAL

### Kleene 迭代

由于 closure_H 是单调算子，且 2^Props 是有限完备格（当 Props 有限时），
由 Tarski 不动点定理，closure_H 存在 least fixpoint，且 Kleene 迭代从 ∅ 出发有限步收敛。

---

## Stage 2: Static Attack Graph

### 定义

从 Horn closure 的结果 C = closure_H^*(∅)（least fixpoint）构建攻击图：

- **顶点**: C 中的所有命题（即被推导出的 arguments）
- **攻击边**: 从 rebuttal/exception 规则中提取
  - 若规则形式为 "p 是 q 的例外" 或 "p rebuttal q"，则添加攻击边 p → q

### 定理 E2.2: 攻击图构建是确定性的

**Statement**: 给定固定的 Horn 规则集 H 和 rebuttal 规则集 R，从 C = closure_H^*(∅) 构建的攻击图 G(C, R) 是唯一的。

**Proof**:

1. C = closure_H^*(∅) 是唯一的（由 Tarski 定理，least fixpoint 唯一）。
2. 攻击边由 R 和 C 的笛卡尔积的子集确定：
   对每条 rebuttal 规则 (p, q) ∈ R，若 p ∈ C 且 q ∈ C，则添加边 p → q。
3. 这是一个确定性的集合构造：给定 C 和 R，攻击边集合是 { (p, q) ∈ R | p ∈ C ∧ q ∈ C }。
4. 该集合由 C 和 R 唯一确定，因此 G(C, R) 唯一。∎

**Epistemic status**: PROVED_FORMAL

---

## Stage 3: Grounded Extension (固定图)

### 定理 E2.3: 分层评估器的 Stage 3 收敛

**Statement**: 对 Stage 2 构建的有限攻击图 G，其 grounded extension 存在、唯一，且 Kleene 迭代在 ≤ |V(G)| 步内收敛。

**Proof**:

直接引用 Theorem E1（Dung AAF grounded extension 的存在唯一性和收敛性）。
Stage 2 构建的攻击图是有限 Dung AAF，因此 Theorem E1 适用。∎

**Epistemic status**: PROVED_BY_EXHAUSTIVE_ENUMERATION (n <= 4) / OPEN_CONJECTURE (一般有限情形)

---

## Stage 跨图单调性反例

### 定理 E2.3b (COUNTEREXAMPLE): 分层评估器输出不随 premise 集单调递增

**Statement**: 增加 premise 可能导致 grounded extension 缩小（非单调）。

**Counterexample**:

考虑两个攻击图：

**G1** (premise 集 P1 = {a}):
- Args = {a}
- Att = {}
- GE(G1) = {a}

**G2** (premise 集 P2 = {a, b}, P1 ⊆ P2):
- Args = {a, b}
- Att = {(b, a)}  (b 攻击 a)
- GE(G2) = {b}  (b 无攻击者，被接受；a 被 b 攻击，被拒绝)

**结果**: 
- P1 ⊆ P2 (premise 集单调递增)
- 但 GE(G1) = {a} ⊈ {b} = GE(G2) (grounded extension 不单调)

**解释**:
增加 premise b 引入了 b 对 a 的攻击，导致原本被接受的 a 被击败。
这说明：
1. Horn closure 是单调的（更多 premise → 更多推导）
2. 攻击图构建是确定性的
3. 但 grounded extension 作为攻击图的函数，**不是**关于 premise 集的单调函数

**Epistemic status**: REFUTED_BY_COUNTEREXAMPLE

---

## Stage 4: 与原 Evaluator 的等价/不等价条件

### 原 Evaluator 的语义回顾

原 evaluator 定义 operator F_orig(S) = { a ∈ S | a 未被 S 中的任何 argument rebuttal 击败 }。

问题（Theorem E3）：F_orig 不满足单调性，因此不能直接用 Kleene 迭代求 least fixpoint。

### 分层评估器的语义

分层评估器将过程分为四个阶段：
1. Horn closure（单调）
2. 攻击图构建（确定性）
3. Grounded extension（对固定图单调 + 收敛，但对 premise 集非单调）
4. 结果输出

### 等价条件

**Conjecture E2.4a**: 当满足以下条件时，分层评估器与原 evaluator 等价：

1. **无循环攻击**: 攻击图中不存在有向循环（即攻击图是 DAG）。
2. **Confidence-zeroing 等价于 defeat**: 当 argument a 被攻击时，原 evaluator 的 confidence-zeroing 语义与 Dung AAF 的 "a 不在 grounded extension 中" 语义等价。
3. **无自攻击**: 不存在 argument 攻击自身的情况。
4. **Premise 集固定**: 不增加新的 premise（避免跨图非单调性）。

**Epistemic status**: OPEN_CONJECTURE

**为何未证明**:
- 需要形式化定义 "confidence-zeroing 等价于 defeat" 的精确语义。
- 需要归纳证明：对 DAG 攻击图，原 evaluator 的 fixpoint（如果存在）等于 grounded extension。
- 需要处理原 evaluator 可能不存在 fixpoint 的情况（由于非单调性）。
- 跨图非单调性（E2.3b）使得等价性更加复杂。

### 不等价条件

**Theorem E2.4b**: 当存在以下任一条件时，分层评估器与原 evaluator 不等价：

1. **存在循环攻击**: 攻击图中存在有向循环。
2. **Confidence-zeroing 与 defeat 语义不同**: 原 evaluator 的 confidence-zeroing 不仅移除被攻击的 argument，还可能级联影响其他 arguments 的推导。
3. **Premise 集变化**: 增加 premise 改变攻击图结构，导致 grounded extension 非单调变化。

**证明（循环攻击情形）**:

考虑两个 arguments a, b 互相攻击（a ↔ b）。

- **分层评估器（Stage 3）**: grounded extension 为 ∅（因为 a 和 b 互相攻击，无法同时接受，且单独接受任一个都不安全）。
- **原 evaluator**: 取决于迭代顺序和初始集合。
  - 若从 S = {a, b} 开始，F_orig(S) = ∅（a 和 b 互相击败）。
  - 但 F_orig(∅) = ∅，所以 ∅ 是一个 fixpoint。
  - 然而，若从 S = {a} 开始，F_orig(S) = {a}（a 无攻击者），所以 {a} 也是一个 fixpoint！
  - 类似地，{b} 也是一个 fixpoint。

因此原 evaluator 有多个 fixpoint（∅, {a}, {b}），而分层评估器给出唯一的 ∅。
这证明了不等价。

**Epistemic status**: REFUTED_BY_COUNTEREXAMPLE

---

## 总结

| Stage | 内容 | 状态 |
|-------|------|------|
| 1 | Horn closure 单调性 | PROVED_FORMAL |
| 2 | 攻击图构建确定性 | PROVED_FORMAL |
| 3a | Grounded extension 收敛 (固定图) | PROVED_BY_EXHAUSTIVE_ENUMERATION (n <= 4) |
| 3b | 跨图单调性 | REFUTED_BY_COUNTEREXAMPLE |
| 4a | 与原 evaluator 等价条件 | OPEN_CONJECTURE |
| 4b | 与原 evaluator 不等价条件 | REFUTED_BY_COUNTEREXAMPLE |

**整体 Theorem E2 状态**: 部分证明，部分开放，部分反驳。
分层评估器本身（Stage 1-2，Stage 3 固定图）的正确性在有限情形下已建立，
但跨图单调性被反例推翻，与原 evaluator 的精确关系仍需进一步工作。
