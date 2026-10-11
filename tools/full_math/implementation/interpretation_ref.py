"""T122/T123 interpretation layer reference (plan §3.1, §4.3, §11.2 P066).

K rows 2551-2552 (docs/spec/20261007-统一法律数学模型_附录K_全量目标落实表.md):
T122 五方法解释 — §3.1,11.2：五解释构造有原文理由，分支先隔离；
T123 解释分支 — §3.1,4.3：解释相容/攻击/优先，不能引用另支前提。

Five interpretation constructors (literal/systematic/teleological/historical/
constitutional) each output a concrete typed rule AST plus a NAMED textual
reason; construction is never adoption (§3.1: 不以"使用了某方法"自动证明解释
正确) — adopting or excluding a candidate requires statutory authority and a
named reason, and non-adopted candidates never enter the unconditional rule
base.  Interpretation branches are preserved per sourced reading (never
merged), carry compatibility/attack/priority relations built from adopted
candidates (never from labels, §4.3), and the branch-isolation gate rejects
any derivation citing another branch's premises.

Lean contract: proofs/lean/juris_lean/JurisLean/Seams/UnifiedW4Interp.lean
(namespace JurisLean.Seams.UnifiedW4Interp).  Independent checker:
tools/full_math/implementation/interp_ref_check.py (shares only these frozen
carriers, re-implements every predicate inline).
"""
from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import FrozenSet, Iterable, Optional, Tuple


class InterpMethod(Enum):
    """§3.1 五解释构造子（P066 修正注记：类推是漏洞续造构造子，不在五解释内）."""

    LITERAL = "literal"              # 文义
    SYSTEMATIC = "systematic"        # 体系
    TELEOLOGICAL = "teleological"    # 目的
    HISTORICAL = "historical"        # 历史
    CONSTITUTIONAL = "constitutional"  # 合宪


class InterpEffect(Enum):
    """P066：构造子保存的新增/选择/保持效应."""

    ADD_RULE = "add_rule"
    SELECT_READING = "select_reading"
    KEEP_READING = "keep_reading"


@dataclass(frozen=True)
class RuleAst:
    """具体有类型规则 AST（§3.1 解释构造子的输出）."""

    rule_id: str
    premises: Tuple[str, ...]
    conclusion: str


@dataclass(frozen=True)
class InterpInput:
    """解释输入面：原文与上下文/理由材料（P066：构造子保存输入文本）."""

    text_id: str
    context_ids: Tuple[str, ...]


@dataclass(frozen=True)
class InterpCandidate:
    """§3.1 解释候选：方法＋保存的输入面＋目标/范围/效应＋规则 AST＋具名理由＋
    法定权限（None＝未获采用权限：构造不等于采用）."""

    candidate_id: str
    method: InterpMethod
    input: InterpInput
    target: str
    scope: str
    effect: InterpEffect
    rule: RuleAst
    reason_id: Optional[str]
    authority_id: Optional[str]


def mk_candidate(
    method: InterpMethod,
    candidate_id: str,
    inp: InterpInput,
    target: str,
    scope: str,
    effect: InterpEffect,
    rule: RuleAst,
    reason_id: Optional[str],
    authority_id: Optional[str] = None,
) -> InterpCandidate:
    """统一构造门：输出必带具名理由；构造不内置采用权限。P066：合宪解释受
    相应制度权限约束——合宪候选缺权限直接拒绝（fail-fast），普通法院/模型不因
    合宪路径取得宣告法源失效的权限."""

    if not reason_id:
        raise ValueError(
            "interpretation candidate requires a NAMED reason (§3.1 具名理由)")
    if method is InterpMethod.CONSTITUTIONAL and not authority_id:
        raise ValueError(
            "constitutional interpretation requires statutory authority (P066)")
    return InterpCandidate(
        candidate_id=candidate_id, method=method, input=inp, target=target,
        scope=scope, effect=effect, rule=rule, reason_id=reason_id,
        authority_id=authority_id)


# One constructor per method（构造子＋理由字段；合法性见 tests 与 Lean *_legal）.

def mk_literal(candidate_id, inp, target, scope, effect, rule, reason_id):
    return mk_candidate(InterpMethod.LITERAL, candidate_id, inp, target,
                        scope, effect, rule, reason_id)


def mk_systematic(candidate_id, inp, target, scope, effect, rule, reason_id):
    return mk_candidate(InterpMethod.SYSTEMATIC, candidate_id, inp, target,
                        scope, effect, rule, reason_id)


def mk_teleological(candidate_id, inp, target, scope, effect, rule, reason_id):
    return mk_candidate(InterpMethod.TELEOLOGICAL, candidate_id, inp, target,
                        scope, effect, rule, reason_id)


def mk_historical(candidate_id, inp, target, scope, effect, rule, reason_id):
    return mk_candidate(InterpMethod.HISTORICAL, candidate_id, inp, target,
                        scope, effect, rule, reason_id)


def mk_constitutional(candidate_id, inp, target, scope, effect, rule, reason_id,
                      authority_id):
    return mk_candidate(InterpMethod.CONSTITUTIONAL, candidate_id, inp, target,
                        scope, effect, rule, reason_id, authority_id)


def adoptable(c: InterpCandidate) -> bool:
    """采用门（§3.1：采用/排除解释仍须法定权限与具名理由）."""

    return bool(c.reason_id) and c.authority_id is not None


def rule_base(cands: Iterable[InterpCandidate]) -> FrozenSet[RuleAst]:
    """无条件规则库：只收可合法采用候选的规则 AST（未采用候选不进入）."""

    return frozenset(c.rule for c in cands if adoptable(c))


# ---------------------------------------------------------------------------
# T123 解释分支：相容/攻击/优先 ＋ 分支隔离
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class InterpBranch:
    """具来源解释支路：本支已采用候选＋本支私有前提（§3.1：保留每个具来源的
    解释支路；支路不合并、不唯一化）."""

    branch_id: str
    adopted: FrozenSet[str]          # candidate ids
    private_premises: FrozenSet[str]


@dataclass(frozen=True)
class BranchDerivation:
    """分支内推导：结论＋所引用前提表."""

    derivation_id: str
    conclusion: str
    cited_premises: FrozenSet[str]


def conflict_on(x: InterpCandidate, y: InterpCandidate) -> bool:
    """攻击靶点冲突：同一解释目标上输出不相容的两条规则 AST."""

    return x.target == y.target and x.rule != y.rule


def interp_attack(a: InterpBranch, b: InterpBranch,
                  cands: Iterable[InterpCandidate]) -> bool:
    """支路攻击：由双方已采用候选的实际靶点冲突给出（§4.3：不从标签倒填边）."""

    by_id = {c.candidate_id: c for c in cands}
    return any(
        conflict_on(by_id[x], by_id[y])
        for x in a.adopted for y in b.adopted)


def branch_compatible(a: InterpBranch, b: InterpBranch,
                      cands: Iterable[InterpCandidate]) -> bool:
    """支路相容：互不攻击（§3.1 相互攻击的否定面）."""

    return not interp_attack(a, b, cands)


@dataclass(frozen=True)
class PriorityPair:
    """具名优先对：法源规定的排除效力（superior 压 inferior 的 candidate id）."""

    superior: str
    inferior: str


def has_priority(pairs: Iterable[PriorityPair], s: str, n: str) -> bool:
    return any(p.superior == s and p.inferior == n for p in pairs)


def priority_wf(pairs: Iterable[PriorityPair],
                pool: Iterable[InterpCandidate]) -> bool:
    """优先良构：每条具名边都落在池中一对真冲突上（§3.1：相冲突的候选才进入
    冲突实例；无冲突不造边）."""

    by_id = {c.candidate_id: c for c in pool}
    return all(
        p.superior in by_id and p.inferior in by_id
        and conflict_on(by_id[p.superior], by_id[p.inferior])
        for p in pairs)


def resolved_by_priority(pairs: Tuple[PriorityPair, ...],
                         pool: Tuple[InterpCandidate, ...]
                         ) -> Tuple[InterpCandidate, ...]:
    """优先解决后的采用集：池中未被任何在池候选（按具名边）压掉的候选
    （§3.1 profile：被采纳候选排除其靶点）."""

    return tuple(
        c for c in pool
        if not any(s.candidate_id != c.candidate_id
                   and has_priority(pairs, s.candidate_id, c.candidate_id)
                   for s in pool))


def branch_premises_of(c: InterpCandidate) -> FrozenSet[str]:
    """支路私有前提默认取该候选的上下文理由材料（输入面保存的下游读法）."""

    return frozenset(c.input.context_ids)


def branch_each(cands: Iterable[InterpCandidate]) -> Tuple[InterpBranch, ...]:
    """支路枚举：每个候选各成一支——枚举不合并不丢弃（§3.1：保留每个具来源的
    解释支路；采用层才按具名优先收敛）."""

    return tuple(
        InterpBranch(branch_id=c.candidate_id, adopted=frozenset({c.candidate_id}),
                     private_premises=branch_premises_of(c))
        for c in cands)


def derivation_ok(branch: InterpBranch, d: BranchDerivation) -> bool:
    """分支隔离门（T123）：推导引用的前提全在本支私有前提内——引用另支前提
    的推导在此被拒."""

    return d.cited_premises <= branch.private_premises


def premises_disjoint(a: InterpBranch, b: InterpBranch) -> bool:
    """前提不相交：两支私有前提无公共材料."""

    return not (a.private_premises & b.private_premises)


# ---------------------------------------------------------------------------
# 分支层总装（下游 run_case 消费的单一入口）
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class InterpLayer:
    """解释分支层快照：可合法采用池、具名优先解决后的采用集、全支路、攻击对、
    已应用的优先边、无法定胜负的报请冲突、无条件规则库."""

    pool: Tuple[str, ...]
    resolved: Tuple[str, ...]
    branches: Tuple[InterpBranch, ...]
    attacks: Tuple[Tuple[str, str], ...]
    priorities_applied: Tuple[Tuple[str, str], ...]
    referral: Tuple[Tuple[str, str], ...]
    rule_base: FrozenSet[RuleAst]


def build_interp_layer(
    cands: Iterable[InterpCandidate],
    priority_pairs: Iterable[PriorityPair] = (),
) -> InterpLayer:
    """总装解释分支层（§3.1）：候选 id 唯一 fail-fast；采用门过滤；支路全保留；
    同位冲突无具名边时记报请路径而不作选择."""

    cands = tuple(cands)
    pairs = tuple(priority_pairs)
    ids = [c.candidate_id for c in cands]
    if len(set(ids)) != len(ids):
        raise ValueError("duplicate interpretation candidate id")

    pool = tuple(c for c in cands if adoptable(c))
    resolved = resolved_by_priority(pairs, pool)
    branches = branch_each(pool)
    attacks = tuple(
        (a.branch_id, b.branch_id)
        for a in branches for b in branches if a.branch_id < b.branch_id
        and interp_attack(a, b, cands))
    referral = tuple(
        (x.candidate_id, y.candidate_id)
        for x in pool for y in pool
        if x.candidate_id < y.candidate_id
        and conflict_on(x, y)
        and not has_priority(pairs, x.candidate_id, y.candidate_id)
        and not has_priority(pairs, y.candidate_id, x.candidate_id))
    priorities_applied = tuple(
        (p.superior, p.inferior) for p in pairs
        if p.superior in {c.candidate_id for c in resolved})
    # The unconditional rule base is built from the ADOPTED readings only:
    # a candidate excluded by a named priority edge is 排除, not adopted
    # (§3.1), so its rule stays out just like a non-adopted candidate's.
    return InterpLayer(
        pool=tuple(c.candidate_id for c in pool),
        resolved=tuple(c.candidate_id for c in resolved),
        branches=branches,
        attacks=attacks,
        priorities_applied=priorities_applied,
        referral=referral,
        rule_base=rule_base(resolved))
