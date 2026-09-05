#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
evaluator_nonmonotone_counterexample.py
Theorem E3: 原始 evaluator 在同一 fixpoint loop 中执行 rebuttal/confidence-zeroing
不满足 Tarski 单调性。

Epistemic status: REFUTED_BY_COUNTEREXAMPLE

要求：
- 构造一个具体的最小反例
- 定义 evaluator operator F(S) = S 中未被 rebuttal 击败的 arguments
- 展示：A ⊆ B 但 F(A) ⊈ F(B)
- 输出 JSON 格式的反例
"""

import json
import sys
from typing import Set, Dict, Any


# ---------------------------------------------------------------------------
# 1. 定义 Argument 和 EvaluatorOperator
# ---------------------------------------------------------------------------
class Argument:
    """A single argument with a name."""

    __slots__ = ("name", "_hash")

    def __init__(self, name: str) -> None:
        self.name = name
        self._hash = hash(name)

    def __repr__(self) -> str:
        return f"Argument({self.name!r})"

    def __hash__(self) -> int:
        return self._hash

    def __eq__(self, other: object) -> bool:
        return isinstance(other, Argument) and self.name == other.name


class EvaluatorOperator:
    """
    原始 evaluator 的算子 F(S)。

    定义：
    F(S) = { a ∈ S | a 未被 S 中的任何 argument rebuttal 击败 }

    关键问题：confidence-zeroing 语义。
    当 S 中包含一个 argument b，且 b rebuttal 攻击 a 时，
    evaluator 会将 a 的 confidence 置零（即移除 a）。

    这与 Dung AAF 的 characteristic function 不同：
    - Dung 的 F(S) 可以接受原本不在 S 中的 argument（如果它的所有攻击者都被 S 攻击）
    - 原始 evaluator 的 F(S) 只能从 S 中筛选，且 rebuttal 关系在 S 内部生效
    """

    def __init__(self, arguments: Set[Argument], rebuttal_pairs: Set[tuple]) -> None:
        """
        arguments: 所有可能的 argument
        rebuttal_pairs: (attacker, target) 的有向边集合
        """
        self.arguments = arguments
        self.rebuttal_pairs = rebuttal_pairs

    def F(self, S: Set[Argument]) -> Set[Argument]:
        """
        原始 evaluator 的 operator：
        F(S) = { a ∈ S | 不存在 b ∈ S 使得 (b, a) ∈ rebuttal_pairs }

        即：S 中所有未被 S 内其他 argument rebuttal 击败的 arguments。
        """
        result = set()
        for a in S:
            # 检查 a 是否被 S 中的某个 b rebuttal
            defeated = False
            for b in S:
                if (b, a) in self.rebuttal_pairs:
                    defeated = True
                    break
            if not defeated:
                result.add(a)
        return result


# ---------------------------------------------------------------------------
# 2. 构造最小反例
# ---------------------------------------------------------------------------

def construct_counterexample() -> Dict[str, Any]:
    """
    构造 Theorem E3 的最小反例。

    场景：
    - A = {a}，a 无攻击者 → F(A) = {a}
    - B = {a, b}，b 攻击 a，evaluator 对 a 做 confidence-zeroing → F(B) = ∅
    - 结果：{a} = F(A) ⊈ ∅ = F(B)，但 A ⊆ B

    这违反了 Tarski 单调性：A ⊆ B 应该推出 F(A) ⊆ F(B)。
    """
    a = Argument("a")
    b = Argument("b")

    A = {a}
    B = {a, b}

    # b rebuttal attacks a, and b also attacks itself (self-attack)
    # The self-attack ensures F(B) = empty set, matching the required scenario.
    rebuttal_pairs = {(b, a), (b, b)}

    evaluator = EvaluatorOperator(arguments={a, b}, rebuttal_pairs=rebuttal_pairs)

    F_A = evaluator.F(A)
    F_B = evaluator.F(B)

    # 验证反例条件
    assert A.issubset(B), "A ⊆ B 必须成立"
    assert not F_A.issubset(F_B), "F(A) ⊈ F(B) 必须成立（这是反例的核心）"

    counterexample = {
        "theorem": "E3",
        "claim": "原始 evaluator 在同一 fixpoint loop 中执行 rebuttal/confidence-zeroing 满足 Tarski 单调性",
        "epistemic_status": "REFUTED_BY_COUNTEREXAMPLE",
        "arguments": [arg.name for arg in [a, b]],
        "rebuttal_pairs": [(attacker.name, target.name) for attacker, target in rebuttal_pairs],
        "note": "Self-attack (b,b) is added to ensure F(B) = empty set as required by the scenario.",
        "sets": {
            "A": [arg.name for arg in A],
            "B": [arg.name for arg in B],
        },
        "evaluator_operator": "F(S) = { a ∈ S | a 未被 S 中的任何 argument rebuttal 击败 }",
        "results": {
            "F(A)": [arg.name for arg in F_A],
            "F(B)": [arg.name for arg in F_B],
        },
        "monotonicity_check": {
            "A_subseteq_B": A.issubset(B),
            "F_A_subseteq_F_B": F_A.issubset(F_B),
            "counterexample_holds": not F_A.issubset(F_B),
        },
        "explanation": (
            "A = {a} ⊆ B = {a, b}，但 F(A) = {a} ⊈ ∅ = F(B)。\n"
            "原因：原始 evaluator 的 confidence-zeroing 语义使得当 b 加入 S 后，\n"
            "b 对 a 的 rebuttal 导致 a 被移除。这违反了单调性——增加元素反而减少了输出。\n"
            "在 Tarski 单调算子理论中，F(A) ⊆ F(B) 必须对 A ⊆ B 成立，此处不成立。"
        ),
        "why_this_matters": (
            "单调性是 Kleene 迭代收敛到 least fixpoint 的前提。\n"
            "原始 evaluator 不满足单调性，因此：\n"
            "  1. 不能保证 fixpoint 存在\n"
            "  2. 即使存在，也不能保证唯一\n"
            "  3. Kleene 迭代可能不收敛或收敛到非预期结果\n"
            "这正是引入分层评估器（Theorem E2）的动机。"
        ),
    }

    return counterexample


# ---------------------------------------------------------------------------
# 3. 主函数
# ---------------------------------------------------------------------------

def main() -> int:
    print("=" * 70)
    print("Theorem E3: Original Evaluator Monotonicity Counterexample")
    print("=" * 70)
    print("Epistemic status target: REFUTED_BY_COUNTEREXAMPLE")
    print("=" * 70)

    counterexample = construct_counterexample()

    print("\nCounterexample constructed successfully.")
    print("\nCounterexample details:")
    print(f"  Arguments: {counterexample['arguments']}")
    print(f"  Rebuttal pairs: {counterexample['rebuttal_pairs']}")
    print(f"\n  A = {counterexample['sets']['A']}")
    print(f"  B = {counterexample['sets']['B']}")
    print(f"  A subseteq B: {counterexample['monotonicity_check']['A_subseteq_B']}")
    print(f"\n  F(A) = {counterexample['results']['F(A)']}")
    print(f"  F(B) = {counterexample['results']['F(B)']}")
    print(f"\n  F(A) subseteq F(B): {counterexample['monotonicity_check']['F_A_subseteq_F_B']}")
    print(f"  Counterexample holds: {counterexample['monotonicity_check']['counterexample_holds']}")

    print("\n" + "=" * 70)
    print("Conclusion")
    print("=" * 70)
    print("Original evaluator's rebuttal/confidence-zeroing semantics violate Tarski monotonicity.")
    print("Therefore, the original evaluator cannot directly use Kleene iteration for least fixpoint.")
    print(f"Epistemic status: {counterexample['epistemic_status']}")

    # Output JSON
    json_path = "evaluator_nonmonotone_counterexample.json"
    with open(json_path, "w", encoding="utf-8") as f:
        json.dump(counterexample, f, indent=2, ensure_ascii=False)
    print(f"\nJSON counterexample written to: {json_path}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
