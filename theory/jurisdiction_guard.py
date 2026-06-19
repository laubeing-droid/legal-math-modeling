#!/usr/bin/env python3
"""
Jurisdiction Routing Guard
==========================

Real-time guard that checks cross-jurisdiction claim mappings before
allowing automatic merge. Integrates with the reasoning pipeline.

Usage:
    guard = JurisdictionGuard()
    result = guard.check("CN", "US", claim_text="违约方应承担赔偿责任")
    if result.blocked:
        print(result.reason)  # "该规则无境外对应，不可自动合并"
"""

from __future__ import annotations

import csv
import json
import os
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional, Set

_PROJECT_ROOT = Path(__file__).resolve().parent.parent
if str(_PROJECT_ROOT) not in sys.path:
    sys.path.insert(0, str(_PROJECT_ROOT))


@dataclass
class GuardResult:
    """Result of a jurisdiction routing check."""
    allowed: bool
    blocked: bool
    warning: bool
    mapping_status: str
    reason: str
    pattern_id: Optional[str] = None
    obstruction_type: Optional[str] = None


@dataclass
class JurisdictionGuard:
    """Real-time cross-jurisdiction routing guard.

    Loads claim_mapping.csv and obstruction_analysis.json at init,
    then provides O(1) lookup for each claim check.
    """

    _mappings: Dict[str, dict] = field(default_factory=dict, repr=False)
    _obstructions: Dict[str, dict] = field(default_factory=dict, repr=False)
    _cn_claims: Dict[str, str] = field(default_factory=dict, repr=False)
    _loaded: bool = False

    def _ensure_loaded(self):
        if self._loaded:
            return
        self._load_mappings()
        self._load_obstructions()
        self._loaded = True

    def _load_mappings(self):
        path = _PROJECT_ROOT / "data" / "category_rosetta" / "claim_mapping.csv"
        if not path.exists():
            return
        with open(path, encoding="utf-8") as f:
            for row in csv.DictReader(f):
                pid = row.get("pattern_id", "")
                self._mappings[pid] = row
                cn = row.get("cn_claim", "")
                if cn:
                    self._cn_claims[cn] = pid

    def _load_obstructions(self):
        path = _PROJECT_ROOT / "data" / "category_rosetta" / "obstruction_analysis.json"
        if not path.exists():
            return
        with open(path, encoding="utf-8") as f:
            data = json.load(f)
        for obs in data.get("obstructions", []):
            for hc in obs.get("hard_cases", []):
                self._obstructions[hc] = obs

    def check(self, source_jurisdiction: str, target_jurisdiction: str,
              claim_text: Optional[str] = None,
              pattern_id: Optional[str] = None) -> GuardResult:
        """Check if a claim can be merged across jurisdictions.

        Args:
            source_jurisdiction: Source jurisdiction (e.g., "CN")
            target_jurisdiction: Target jurisdiction (e.g., "US", "HK")
            claim_text: The claim text to look up (fuzzy match against cn_claim)
            pattern_id: Direct pattern_id lookup (e.g., "FP-CN-001")

        Returns:
            GuardResult with allowed/blocked/warning status.
        """
        self._ensure_loaded()

        # Same jurisdiction: always allowed
        if source_jurisdiction == target_jurisdiction:
            return GuardResult(
                allowed=True, blocked=False, warning=False,
                mapping_status="SAME_JURISDICTION",
                reason="同一法域内合并，无需跨域检查",
            )

        # Find the mapping
        mapping = None
        if pattern_id:
            mapping = self._mappings.get(pattern_id)
        elif claim_text:
            # Fuzzy match: check if claim_text is a substring of any cn_claim
            for cn, pid in self._cn_claims.items():
                if claim_text in cn or cn in claim_text:
                    mapping = self._mappings.get(pid)
                    break

        if mapping is None:
            return GuardResult(
                allowed=False, blocked=True, warning=False,
                mapping_status="NOT_FOUND",
                reason="未找到该规则的跨域映射记录，不可自动合并",
            )

        status = mapping.get("mapping_status", "")
        pid = mapping.get("pattern_id", "")
        obs = self._obstructions.get(pid, {})
        obs_type = obs.get("type", "") if obs else ""

        # CN_ONLY: no foreign mapping exists
        if status == "CN_ONLY":
            return GuardResult(
                allowed=False, blocked=True, warning=False,
                mapping_status=status, pattern_id=pid,
                reason=f"该规则（{pid}）无境外对应物，不可自动合并。仅适用于中国大陆法域。",
            )

        # COLLISION: mapping causes cross-jurisdiction conflict
        if status == "COLLISION":
            return GuardResult(
                allowed=False, blocked=True, warning=False,
                mapping_status=status, pattern_id=pid,
                obstruction_type=obs_type,
                reason=f"该规则（{pid}）在目标法域存在冲突"
                       + (f"（obstruction: {obs_type}）" if obs_type else "")
                       + "，需人工审核后方可合并。",
            )

        # ASYMMETRY: mapping is asymmetric
        if status == "ASYMMETRY":
            return GuardResult(
                allowed=True, blocked=False, warning=True,
                mapping_status=status, pattern_id=pid,
                obstruction_type=obs_type,
                reason=f"该规则（{pid}）在法域间存在不对称映射"
                       + (f"（obstruction: {obs_type}）" if obs_type else "")
                       + "，结果仅供参考，需人工确认。",
            )

        # PARTIAL: incomplete mapping
        if "PARTIAL" in status:
            return GuardResult(
                allowed=True, blocked=False, warning=True,
                mapping_status=status, pattern_id=pid,
                reason=f"该规则（{pid}）仅有部分跨域映射（{status}），结果可能不完整。",
            )

        # TRI_JURISDICTION_MAPPED: full mapping exists
        if status == "TRI_JURISDICTION_MAPPED":
            return GuardResult(
                allowed=True, blocked=False, warning=False,
                mapping_status=status, pattern_id=pid,
                reason=f"该规则（{pid}）有完整的三法域映射，允许合并。",
            )

        # Unknown status
        return GuardResult(
            allowed=False, blocked=True, warning=False,
            mapping_status=status, pattern_id=pid,
            reason=f"未知的映射状态（{status}），拒绝合并。",
        )

    def check_batch(self, claims: List[dict]) -> List[GuardResult]:
        """Check a batch of claims.

        Each claim dict should have at least 'source_jurisdiction',
        'target_jurisdiction', and optionally 'claim_text' or 'pattern_id'.
        """
        results = []
        for claim in claims:
            result = self.check(
                source_jurisdiction=claim.get("source_jurisdiction", "CN"),
                target_jurisdiction=claim.get("target_jurisdiction", "US"),
                claim_text=claim.get("claim_text"),
                pattern_id=claim.get("pattern_id"),
            )
            results.append(result)
        return results

    def summary(self) -> dict:
        """Return summary statistics of loaded data."""
        self._ensure_loaded()
        status_counts = {}
        for m in self._mappings.values():
            s = m.get("mapping_status", "UNKNOWN")
            status_counts[s] = status_counts.get(s, 0) + 1
        return {
            "total_mappings": len(self._mappings),
            "total_obstructions": len(self._obstructions),
            "status_distribution": status_counts,
        }


def demo():
    """Demo: check various cross-jurisdiction scenarios."""
    print("=" * 60)
    print("Jurisdiction Routing Guard — Demo")
    print("=" * 60)

    guard = JurisdictionGuard()
    summary = guard.summary()
    print(f"\nLoaded: {summary['total_mappings']} mappings, "
          f"{summary['total_obstructions']} obstructions")
    print(f"Status distribution: {summary['status_distribution']}")

    # Test cases
    test_cases = [
        {"source": "CN", "target": "CN", "text": "任何规则", "expect": "ALLOWED"},
        {"source": "CN", "target": "US", "text": "违约方应承担赔偿责任", "expect": "CHECK"},
        {"source": "CN", "target": "US", "text": "consideration", "expect": "CHECK"},
        {"source": "CN", "target": "HK", "text": "正当防卫", "expect": "CHECK"},
        {"source": "CN", "target": "US", "text": "不存在的规则XYZ", "expect": "BLOCKED"},
    ]

    print("\nTest cases:")
    for tc in test_cases:
        result = guard.check(tc["source"], tc["target"], claim_text=tc["text"])
        status = "BLOCKED" if result.blocked else "WARNING" if result.warning else "ALLOWED"
        print(f"\n  [{status}] {tc['source']}→{tc['target']}: \"{tc['text']}\"")
        print(f"    mapping_status: {result.mapping_status}")
        print(f"    reason: {result.reason}")

    print(f"\n{'=' * 60}")
    print("Demo complete")
    print("=" * 60)


if __name__ == "__main__":
    demo()
