#!/usr/bin/env python3
"""Build a normalized T8.5 batch from local US/HK fact-pattern libraries.

This script converts the remaining source-grounded local cards in:
  - data/us_legal/us_fact_patterns.jsonl
  - data/hk_legal/hk_fact_patterns.jsonl

into the target rosetta CSV shape requested by
data/category_rosetta/T8.5_T9.4_data_collection_prompt.md.

It intentionally excludes source cards already represented in
data/category_rosetta/t85_us_hk_batch_001.csv.
"""

from __future__ import annotations

import csv
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
OUT_PATH = ROOT / "data" / "category_rosetta" / "t85_us_hk_batch_002.csv"
US_PATH = ROOT / "data" / "us_legal" / "us_fact_patterns.jsonl"
HK_PATH = ROOT / "data" / "hk_legal" / "hk_fact_patterns.jsonl"


USED_US = {
    "US-CONTRACT-001",
    "US-CONTRACT-002",
    "US-TORT-002",
    "US-CORPORATE-001",
    "US-CRIMINAL-001",
    "US-ADMINISTRATIVE-001",
    "US-IP-001",
    "US-EMPLOYMENT-001",
}

USED_HK = {
    "FP-HK-002",
    "FP-HK-003",
    "FP-HK-006",
    "FP-HK-007",
    "FP-HK-009",
    "FP-HK-013",
    "FP-HK-015",
    "FP-HK-020",
}


def normalize_domain(domain: str) -> str:
    mapping = {
        "administrative": "admin",
        "administrative/regulatory": "admin",
        "civil_procedure": "procedure",
        "employment": "labor",
        "intellectual_property": "ip",
        "constitutional/basic_law": "constitutional",
    }
    return mapping.get(domain, domain)


def load_jsonl(path: Path) -> list[dict]:
    rows = []
    with path.open("r", encoding="utf-8") as f:
        for line in f:
            rows.append(json.loads(line))
    return rows


def summarize_sources(value) -> str:
    if isinstance(value, list):
        parts = []
        for item in value:
            if isinstance(item, dict):
                citation = item.get("citation") or item.get("url_or_id") or ""
                if citation:
                    parts.append(citation)
            elif item:
                parts.append(str(item))
        return "; ".join(parts[:3])
    return str(value)


def build_us_rows() -> list[dict]:
    out = []
    counter = 9
    for row in load_jsonl(US_PATH):
        if row["pattern_id"] in USED_US:
            continue
        out.append(
            {
                "pattern_id": f"FP-US-{counter:04d}",
                "domain": normalize_domain(row["domain"]),
                "fact_summary": f'{row["fact_summary"]} / 本地US法源卡片转写',
                "cn_claim": "DATA_UNAVAILABLE",
                "us_claim": f'{row["us_claim"]} Sources: {summarize_sources(row.get("us_sources", []))}',
                "hk_claim": "DATA_UNAVAILABLE",
                "mapping_status": "ASYMMETRY",
                "hard_case": "True" if row.get("hard_case") else "False",
                "positive_control": "True" if row.get("positive_control") else "False",
                "notes": (
                    f'Source card {row["pattern_id"]}. '
                    f'Legal question: {row.get("legal_question", "")} '
                    f'Legal basis: {row.get("us_legal_basis", "")}'
                ).strip(),
            }
        )
        counter += 1
    return out


def build_hk_rows() -> list[dict]:
    out = []
    counter = 9
    for row in load_jsonl(HK_PATH):
        if row["pattern_id"] in USED_HK:
            continue
        out.append(
            {
                "pattern_id": f"FP-HK-{counter:04d}",
                "domain": normalize_domain(row["domain"]),
                "fact_summary": f'{row["fact_summary"]} / 本地HK法源卡片转写',
                "cn_claim": "DATA_UNAVAILABLE",
                "us_claim": "DATA_UNAVAILABLE",
                "hk_claim": f'{row["hk_claim"]} Sources: {summarize_sources(row.get("hk_sources", []))}',
                "mapping_status": "ASYMMETRY",
                "hard_case": "True" if row.get("hard_case") else "False",
                "positive_control": "True" if row.get("positive_control") else "False",
                "notes": (
                    f'Source card {row["pattern_id"]}. '
                    f'Legal question: {row.get("legal_question", "")} '
                    f'Legal basis: {summarize_sources(row.get("hk_legal_basis", []))}'
                ).strip(),
            }
        )
        counter += 1
    return out


def main() -> None:
    rows = build_us_rows() + build_hk_rows()
    OUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    with OUT_PATH.open("w", encoding="utf-8-sig", newline="") as f:
        writer = csv.DictWriter(
            f,
            fieldnames=[
                "pattern_id",
                "domain",
                "fact_summary",
                "cn_claim",
                "us_claim",
                "hk_claim",
                "mapping_status",
                "hard_case",
                "positive_control",
                "notes",
            ],
        )
        writer.writeheader()
        writer.writerows(rows)

    print(f"Wrote {len(rows)} rows to {OUT_PATH}")


if __name__ == "__main__":
    main()
