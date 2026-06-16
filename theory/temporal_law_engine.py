#!/usr/bin/env python3
"""
Temporal Law Engine (方向 6)

Formalizes the dual-timestamp model for legal temporal reasoning:
- fact_occurrence_date → substantive law snapshot
- procedural_current_date → procedural law snapshot

Implements:
1. "法不溯及既往" (non-retroactivity of substantive law)
2. "程序从新实体从旧" (new procedure, old substance)
3. governing_law_snapshot(date) → applicable rule set
4. Intertemporal conflict resolution

Based on the 2026-06-01 design session:
"Substantive law rules loaded via governing_law_snapshot(fact_occurrence_date),
procedural rules loaded via governing_law_snapshot(procedural_current_date).
Two rule sets operate in parallel in the same IRState."
"""
from __future__ import annotations
from dataclasses import dataclass, field
from enum import Enum
from typing import Dict, List, Optional, Set, Tuple
from datetime import date


class LawType(Enum):
    SUBSTANTIVE = "substantive"  # 实体法
    PROCEDURAL = "procedural"    # 程序法


class RetroactivityRule(Enum):
    NON_RETROACTIVE = "non_retroactive"    # 法不溯及既往
    RETROACTIVE_BENEFIT = "benefit"        # 从旧兼从轻（刑法）
    NEW_PROCEDURE = "new_procedure"        # 程序从新


@dataclass(frozen=True)
class LegalRule:
    """A legal rule with temporal validity."""
    id: str
    statute: str              # 法律名称
    article: str              # 条款号
    content: str              # 规则内容
    law_type: LawType
    effective_date: date      # 生效日期
    expiry_date: Optional[date] = None  # 失效日期（None = 现行有效）
    retroactivity: RetroactivityRule = RetroactivityRule.NON_RETROACTIVE


@dataclass
class TemporalLawEngine:
    """
    Manages legal rules with temporal validity.

    Core principle: A legal system at any point in time is a SNAPSHOT
    of all rules effective at that date. The engine maintains a timeline
    of rule changes and provides snapshot queries.
    """
    rules: List[LegalRule] = field(default_factory=list)

    def add_rule(self, rule: LegalRule) -> None:
        """Add a rule to the timeline."""
        self.rules.append(rule)

    def snapshot(self, query_date: date,
                 law_type: Optional[LawType] = None) -> List[LegalRule]:
        """
        Get all rules effective at query_date.

        A rule is effective if:
        - effective_date <= query_date
        - expiry_date is None OR expiry_date > query_date
        """
        result = []
        for rule in self.rules:
            if rule.effective_date > query_date:
                continue
            if rule.expiry_date and rule.expiry_date <= query_date:
                continue
            if law_type and rule.law_type != law_type:
                continue
            result.append(rule)
        return result

    def resolve_applicable_law(self, fact_date: date,
                                proc_date: date) -> Dict:
        """
        Resolve the applicable law for a case with dual timestamps.

        fact_date: when the legal fact occurred (实体法时间点)
        proc_date: current procedural stage date (程序法时间点)

        Returns:
        - substantive_rules: rules effective at fact_date
        - procedural_rules: rules effective at proc_date
        - conflicts: any intertemporal conflicts detected
        """
        substantive = self.snapshot(fact_date, LawType.SUBSTANTIVE)
        procedural = self.snapshot(proc_date, LawType.PROCEDURAL)

        # Detect intertemporal conflicts
        conflicts = []
        sub_ids = {r.id for r in substantive}
        proc_ids = {r.id for r in procedural}

        # Check: are there rules that changed between fact_date and proc_date?
        all_at_fact = {r.id for r in self.snapshot(fact_date)}
        all_at_proc = {r.id for r in self.snapshot(proc_date)}

        new_rules = all_at_proc - all_at_fact
        expired_rules = all_at_fact - all_at_proc

        if new_rules:
            conflicts.append({
                "type": "new_rule_between_dates",
                "rule_ids": sorted(new_rules),
                "impact": "New rules may apply to procedure but not substance"
            })
        if expired_rules:
            conflicts.append({
                "type": "expired_rule_between_dates",
                "rule_ids": sorted(expired_rules),
                "impact": "Expired rules may still apply to substance"
            })

        return {
            "fact_date": str(fact_date),
            "proc_date": str(proc_date),
            "substantive_rules": [
                {"id": r.id, "statute": r.statute, "article": r.article}
                for r in substantive
            ],
            "procedural_rules": [
                {"id": r.id, "statute": r.statute, "article": r.article}
                for r in procedural
            ],
            "conflicts": conflicts,
            "applicable_substantive_count": len(substantive),
            "applicable_procedural_count": len(procedural),
        }


def build_prc_law_timeline() -> TemporalLawEngine:
    """Build a realistic PRC legal timeline with major law changes."""
    engine = TemporalLawEngine()

    # 合同法 (Contract Law) — replaced by 民法典
    engine.add_rule(LegalRule(
        id="contract_law",
        statute="中华人民共和国合同法",
        article="全文",
        content="合同法总则 + 分则",
        law_type=LawType.SUBSTANTIVE,
        effective_date=date(1999, 10, 1),
        expiry_date=date(2021, 1, 1),  # Replaced by 民法典
        retroactivity=RetroactivityRule.NON_RETROACTIVE,
    ))

    # 民法典 (Civil Code)
    engine.add_rule(LegalRule(
        id="civil_code",
        statute="中华人民共和国民法典",
        article="全文",
        content="民法典合同编 + 总则编",
        law_type=LawType.SUBSTANTIVE,
        effective_date=date(2021, 1, 1),
        retroactivity=RetroactivityRule.NON_RETROACTIVE,
    ))

    # 民法典第584条（损害赔偿）
    engine.add_rule(LegalRule(
        id="civil_code_art584",
        statute="中华人民共和国民法典",
        article="第584条",
        content="违约赔偿 = 实际损失 + 可得利益，"
                "不得超过预见范围，故意/重大过失除外",
        law_type=LawType.SUBSTANTIVE,
        effective_date=date(2021, 1, 1),
        retroactivity=RetroactivityRule.NON_RETROACTIVE,
    ))

    # 民事诉讼法 (2017 amendment)
    engine.add_rule(LegalRule(
        id="cpl_2017",
        statute="中华人民共和国民事诉讼法",
        article="全文",
        content="2017年修正版民事诉讼法",
        law_type=LawType.PROCEDURAL,
        effective_date=date(2017, 7, 1),
        expiry_date=date(2024, 1, 1),
        retroactivity=RetroactivityRule.NEW_PROCEDURE,
    ))

    # 民事诉讼法 (2024 amendment)
    engine.add_rule(LegalRule(
        id="cpl_2024",
        statute="中华人民共和国民事诉讼法",
        article="全文",
        content="2024年修正版民事诉讼法",
        law_type=LawType.PROCEDURAL,
        effective_date=date(2024, 1, 1),
        retroactivity=RetroactivityRule.NEW_PROCEDURE,
    ))

    # 民事诉讼法第65条（举证期限）
    engine.add_rule(LegalRule(
        id="cpl_art65",
        statute="中华人民共和国民事诉讼法",
        article="第65条",
        content="举证期限制度：逾期举证不予采纳，"
                "但与基本事实有关的应采纳并训诫罚款",
        law_type=LawType.PROCEDURAL,
        effective_date=date(2024, 1, 1),
        retroactivity=RetroactivityRule.NEW_PROCEDURE,
    ))

    # 产品质量法第41条（举证责任倒置）
    engine.add_rule(LegalRule(
        id="product_liability_art41",
        statute="中华人民共和国产品质量法",
        article="第41条",
        content="因产品存在缺陷造成损害，生产者承担赔偿责任。"
                "生产者免责事由由生产者举证。",
        law_type=LawType.SUBSTANTIVE,
        effective_date=date(2000, 9, 1),
        retroactivity=RetroactivityRule.NON_RETROACTIVE,
    ))

    return engine


def run_example():
    """Run example: contract dispute spanning law change."""
    print("=" * 72)
    print("TEMPORAL LAW ENGINE — Intertemporal Law Resolution")
    print("=" * 72)

    engine = build_prc_law_timeline()
    print(f"\nLoaded {len(engine.rules)} rules")

    # Scenario 1: Contract formed in 2020, dispute in 2025
    print(f"\n{'─' * 72}")
    print("Scenario 1: Contract formed 2020, litigation in 2025")
    print(f"{'─' * 72}")
    result = engine.resolve_applicable_law(
        fact_date=date(2020, 6, 15),   # 合同签订日
        proc_date=date(2025, 3, 1),    # 诉讼日
    )
    print(f"  Substantive law at fact date: {result['applicable_substantive_count']} rules")
    for r in result['substantive_rules']:
        print(f"    - {r['statute']} {r['article']}")
    print(f"  Procedural law at proc date: {result['applicable_procedural_count']} rules")
    for r in result['procedural_rules']:
        print(f"    - {r['statute']} {r['article']}")
    if result['conflicts']:
        print(f"  ⚠ Conflicts:")
        for c in result['conflicts']:
            print(f"    {c['type']}: {c['impact']}")

    # Scenario 2: Contract formed in 2022, dispute in 2025
    print(f"\n{'─' * 72}")
    print("Scenario 2: Contract formed 2022, litigation in 2025")
    print(f"{'─' * 72}")
    result2 = engine.resolve_applicable_law(
        fact_date=date(2022, 3, 1),
        proc_date=date(2025, 3, 1),
    )
    print(f"  Substantive law: {result2['applicable_substantive_count']} rules")
    for r in result2['substantive_rules']:
        print(f"    - {r['statute']} {r['article']}")
    print(f"  Procedural law: {result2['applicable_procedural_count']} rules")
    for r in result2['procedural_rules']:
        print(f"    - {r['statute']} {r['article']}")

    # Scenario 3: Product liability spanning law change
    print(f"\n{'─' * 72}")
    print("Scenario 3: Product defect 2019, litigation 2025")
    print(f"{'─' * 72}")
    result3 = engine.resolve_applicable_law(
        fact_date=date(2019, 8, 1),
        proc_date=date(2025, 3, 1),
    )
    print(f"  Substantive law: {result3['applicable_substantive_count']} rules")
    for r in result3['substantive_rules']:
        print(f"    - {r['statute']} {r['article']}")
    if result3['conflicts']:
        print(f"  ⚠ Conflicts:")
        for c in result3['conflicts']:
            print(f"    {c['type']}: rule_ids={c['rule_ids']}, {c['impact']}")

    print(f"\n{'=' * 72}")
    print("PRINCIPLE: Substantive law at fact date, procedural law at current date.")
    print("When laws change between the two dates, intertemporal conflicts arise.")
    print(f"{'=' * 72}")

    return engine


if __name__ == "__main__":
    run_example()
