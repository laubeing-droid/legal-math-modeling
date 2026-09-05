#!/usr/bin/env python3
"""
T8.5 + T9.4 Data Extractor
============================

Extracts structured data from Supreme Court full-text case files
for T8.5 (cross-jurisdiction claim mapping) and T9.4 (damages/pricing).

Source: external full-text JSON directory supplied by LEGAL_MATH_T85_T94_SOURCE_ROOT.
"""

import json
import os
import re
import csv
import sys
from pathlib import Path
from typing import List, Dict, Tuple, Optional

SOURCE_ROOT_ENV = "LEGAL_MATH_T85_T94_SOURCE_ROOT"

# File-to-domain mapping
FILE_DOMAIN = {
    "刑事": "criminal",
    "赔偿": "state_compensation",
    "审判监督": "supervision",
    "审判管理": "management",
    "执行": "enforcement",
    "未成年人": "juvenile",
    "民商事": "civil_commercial",
    "涉外": "foreign_commercial",
    "涉港澳": "hk_macau",
    "环境": "environment",
    "知识产权": "ip",
    "立案": "filing",
    "行政": "administrative",
}


def classify_file(filename: str) -> str:
    """Map filename to domain."""
    for keyword, domain in FILE_DOMAIN.items():
        if keyword in filename:
            return domain
    return "unknown"


def load_full_text(filepath: str) -> str:
    """Load all pages' text from a JSON file."""
    with open(filepath, encoding="utf-8") as f:
        data = json.load(f)
    return "\n".join(p.get("text", "") for p in data.get("pages", []))


def resolve_source_root() -> Path:
    """解析外部全文数据根目录；未显式配置时失败关闭，避免公开仓库绑定私有路径。"""
    configured = os.environ.get(SOURCE_ROOT_ENV)
    if not configured:
        raise RuntimeError(f"{SOURCE_ROOT_ENV} is required for full-text extraction")
    root = Path(configured).expanduser().resolve()
    if not root.is_dir():
        raise RuntimeError(f"{SOURCE_ROOT_ENV} does not point to a directory: {root}")
    return root


def extract_case_segments(text: str) -> List[Dict]:
    """Split text into case-level segments.

    Each segment starts with a case number pattern like (20XX)最高法xxx号
    or similar judicial document identifiers.
    """
    # Pattern: case numbers like （2021）最高法民终351号
    case_pattern = re.compile(
        r'[（(](\d{4})[）)][^\n]{0,30}号',
        re.MULTILINE
    )

    segments = []
    matches = list(case_pattern.finditer(text))

    for i, m in enumerate(matches):
        start = m.start()
        end = matches[i + 1].start() if i + 1 < len(matches) else len(text)
        segment_text = text[start:end]

        # Only keep segments with substantial content (>200 chars)
        if len(segment_text) < 200:
            continue

        segments.append({
            "case_number": m.group(0).strip(),
            "year": int(m.group(1)),
            "text": segment_text[:5000],  # cap at 5000 chars
            "full_length": len(segment_text),
        })

    return segments


def extract_money_amounts(text: str) -> List[float]:
    """Extract monetary amounts from text (in yuan)."""
    amounts = []
    # Pattern: 数字+元, 数字万元, 数字亿元
    for m in re.finditer(r'(\d+(?:\.\d+)?)\s*(万|亿)?\s*元', text):
        val = float(m.group(1))
        unit = m.group(2)
        if unit == "万":
            val *= 10000
        elif unit == "亿":
            val *= 100000000
        if 100 <= val <= 1e12:  # reasonable range
            amounts.append(val)
    return amounts


def extract_cross_jurisdiction_refs(text: str) -> Dict[str, bool]:
    """Detect cross-jurisdiction references."""
    return {
        "has_hk_ref": bool(re.search(r'香港|港澳|涉港|区际', text)),
        "has_us_ref": bool(re.search(r'美国|美利坚|涉外|域外', text)),
        "has_foreign_ref": bool(re.search(r'外国|境外|跨境|国际', text)),
        "has_treaty_ref": bool(re.search(r'公约|条约|双边|互惠', text)),
    }


def extract_damages_info(text: str) -> Dict:
    """Extract damages/pricing information from case text."""
    info = {
        "has_damages_claim": bool(re.search(r'赔偿|违约金|损失|损害', text)),
        "has_appeal": bool(re.search(r'上诉|二审|再审|发回重审', text)),
        "initial_claim": None,
        "final_award": None,
        "damage_type": None,
    }

    # Detect damage type
    if re.search(r'违约金', text):
        info["damage_type"] = "liquidated_damages"
    elif re.search(r'惩罚性赔偿', text):
        info["damage_type"] = "punitive"
    elif re.search(r'精神损害', text):
        info["damage_type"] = "emotional_distress"
    elif re.search(r'侵权.*赔偿|损害赔偿', text):
        info["damage_type"] = "compensatory"
    elif re.search(r'律师费', text):
        info["damage_type"] = "attorney_fees"

    # Extract amounts
    amounts = extract_money_amounts(text)
    if len(amounts) >= 2:
        # Heuristic: first mention = claim, last mention = award
        info["initial_claim"] = amounts[0]
        info["final_award"] = amounts[-1]
    elif len(amounts) == 1:
        info["final_award"] = amounts[0]

    return info


def extract_t85_mapping(segments: List[Dict], domain: str) -> List[Dict]:
    """Extract T8.5 cross-jurisdiction claim mapping data."""
    results = []
    for seg in segments:
        xj = extract_cross_jurisdiction_refs(seg["text"])
        if not any(xj.values()):
            continue  # skip non-cross-jurisdiction cases

        # Classify mapping status
        if xj["has_hk_ref"] and xj["has_us_ref"]:
            status = "TRI_JURISDICTION_PARTIAL"
        elif xj["has_hk_ref"]:
            status = "CN_HK_PARTIAL"
        elif xj["has_us_ref"] or xj["has_foreign_ref"]:
            status = "CN_US_PARTIAL"
        else:
            status = "CN_ONLY"

        # Extract key claim from text (first 200 chars of substantive content)
        claim_text = seg["text"][len(seg["case_number"]):].strip()[:200]

        results.append({
            "pattern_id": f"FP-EXT-{domain[:3].upper()}-{len(results)+1:04d}",
            "domain": domain,
            "case_number": seg["case_number"],
            "year": seg["year"],
            "fact_summary": claim_text,
            "mapping_status": status,
            "has_hk_ref": xj["has_hk_ref"],
            "has_us_ref": xj["has_us_ref"],
            "has_foreign_ref": xj["has_foreign_ref"],
            "has_treaty_ref": xj["has_treaty_ref"],
        })

    return results


def extract_t94_damages(segments: List[Dict], domain: str) -> List[Dict]:
    """Extract T9.4 damages/pricing data."""
    results = []
    for seg in segments:
        dmg = extract_damages_info(seg["text"])
        if not dmg["has_damages_claim"]:
            continue

        # Determine jurisdiction (default CN, check for HK/foreign)
        xj = extract_cross_jurisdiction_refs(seg["text"])
        jurisdiction = "CN"
        if xj["has_hk_ref"]:
            jurisdiction = "HK"
        elif xj["has_us_ref"]:
            jurisdiction = "US"

        results.append({
            "case_id": f"BD-{domain[:3].upper()}-{len(results)+1:04d}",
            "jurisdiction": jurisdiction,
            "domain": domain,
            "damage_type": dmg["damage_type"] or "compensatory",
            "initial_claim": dmg["initial_claim"],
            "final_award": dmg["final_award"],
            "has_appeal": dmg["has_appeal"],
            "year": seg["year"],
            "case_number": seg["case_number"],
        })

    return results


def main():
    print("=" * 60)
    print("T8.5 + T9.4 Data Extractor")
    print("=" * 60)

    all_t85 = []
    all_t94 = []
    try:
        base_dir = resolve_source_root()
    except RuntimeError as exc:
        print(f"ERROR: {exc}")
        return 1

    for filepath in sorted(base_dir.glob("*.json")):
        filename = filepath.name
        if not filename.endswith(".json"):
            continue

        domain = classify_file(filename)
        print(f"\n  Processing: {filename[:40]}... ({domain})")

        text = load_full_text(str(filepath))
        segments = extract_case_segments(text)
        print(f"    Case segments: {len(segments)}")

        t85 = extract_t85_mapping(segments, domain)
        t94 = extract_t94_damages(segments, domain)
        print(f"    T8.5 cross-jurisdiction: {len(t85)}")
        print(f"    T9.4 damages: {len(t94)}")

        all_t85.extend(t85)
        all_t94.extend(t94)

    # Summary
    print(f"\n{'=' * 60}")
    print(f"T8.5 total: {len(all_t85)} cross-jurisdiction cases")
    print(f"T9.4 total: {len(all_t94)} damages cases")

    # T8.5 status breakdown
    from collections import Counter
    t85_status = Counter(r["mapping_status"] for r in all_t85)
    print(f"\nT8.5 mapping_status:")
    for s, c in t85_status.most_common():
        print(f"  {s}: {c}")

    # T9.4 type breakdown
    t94_type = Counter(r["damage_type"] for r in all_t94)
    print(f"\nT9.4 damage_type:")
    for s, c in t94_type.most_common():
        print(f"  {s}: {c}")

    # T9.4 with amounts
    t94_with_amounts = [r for r in all_t94 if r["final_award"] is not None]
    print(f"\nT9.4 with amounts: {len(t94_with_amounts)}")
    if t94_with_amounts:
        awards = [r["final_award"] for r in t94_with_amounts]
        print(f"  Range: {min(awards):,.0f} - {max(awards):,.0f} yuan")
        print(f"  Median: {sorted(awards)[len(awards)//2]:,.0f} yuan")

    # Save outputs
    out_dir = Path(__file__).resolve().parent.parent.parent.parent / "data" / "category_rosetta"
    out_dir.mkdir(parents=True, exist_ok=True)

    # T8.5 CSV
    t85_path = out_dir / "t85_extracted_mappings.csv"
    if all_t85:
        with open(t85_path, "w", encoding="utf-8", newline="") as f:
            writer = csv.DictWriter(f, fieldnames=all_t85[0].keys())
            writer.writeheader()
            writer.writerows(all_t85)
        print(f"\nT8.5 saved: {t85_path} ({len(all_t85)} rows)")

    # T9.4 CSV
    t94_path = out_dir / "t94_extracted_damages.csv"
    if all_t94:
        with open(t94_path, "w", encoding="utf-8", newline="") as f:
            writer = csv.DictWriter(f, fieldnames=all_t94[0].keys())
            writer.writeheader()
            writer.writerows(all_t94)
        print(f"T9.4 saved: {t94_path} ({len(all_t94)} rows)")

    print(f"\n{'=' * 60}")
    return all_t85, all_t94


if __name__ == "__main__":
    result = main()
    sys.exit(result if isinstance(result, int) else 0)
