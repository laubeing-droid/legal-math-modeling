#!/usr/bin/env python3
"""Audit local T9.4 US/HK evidence quality.

The current extracted damages file contains many US/HK rows inferred from
cross-jurisdiction mentions inside Chinese judgments. This script produces a
small markdown audit to separate:
  1. noisy extracted rows that are likely false US/HK positives
  2. genuine local US/HK source cards that mention money but do not yet satisfy
     the full T9.4 case-award schema
"""

from __future__ import annotations

import csv
import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
T94_PATH = ROOT / "data" / "category_rosetta" / "t94_extracted_damages.csv"
US_PATH = ROOT / "data" / "us_legal" / "us_fact_patterns.jsonl"
HK_PATH = ROOT / "data" / "hk_legal" / "hk_fact_patterns.jsonl"
OUT_PATH = ROOT / "data" / "category_rosetta" / "t94_us_hk_local_audit.md"

MONEY_RE = re.compile(
    r"(?:US\$|HK\$|\$)\s?[\d,]+(?:\.\d+)?|\b\d[\d,]*(?:\.\d+)?\s?(?:million|billion|thousand)\b",
    re.I,
)


def load_jsonl(path: Path) -> list[dict]:
    with path.open("r", encoding="utf-8") as f:
        return [json.loads(line) for line in f]


def looks_like_cn_case(case_number: str) -> bool:
    return any(token in case_number for token in ("最高法", "民终", "民申", "行", "知民", "沪", "京", "粤", "苏", "浙"))


def audit_extracted_rows() -> tuple[list[dict], list[dict]]:
    suspect = []
    stronger = []
    with T94_PATH.open("r", encoding="utf-8-sig", newline="") as f:
        rows = list(csv.DictReader(f))
    for row in rows:
        if row["jurisdiction"] not in {"US", "HK"}:
            continue
        target = suspect if looks_like_cn_case(row["case_number"]) else stronger
        target.append(row)
    return suspect, stronger


def local_money_cards() -> list[dict]:
    out = []
    for path, label in ((US_PATH, "US"), (HK_PATH, "HK")):
        for row in load_jsonl(path):
            text = " ".join(
                str(row.get(k, ""))
                for k in ("fact_summary", "legal_question", "us_claim", "hk_claim", "notes")
            )
            hits = MONEY_RE.findall(text)
            if hits:
                out.append(
                    {
                        "jurisdiction": label,
                        "pattern_id": row["pattern_id"],
                        "domain": row["domain"],
                        "money_mentions": ", ".join(hits),
                        "fact_summary": row["fact_summary"],
                    }
                )
    return out


def main() -> None:
    suspect, stronger = audit_extracted_rows()
    money_cards = local_money_cards()

    lines = [
        "# T9.4 US/HK Local Evidence Audit",
        "",
        "## Extracted `t94_extracted_damages.csv` review",
        "",
        f"- US/HK rows in extracted file: {len(suspect) + len(stronger)}",
        f"- Rows that still look like Chinese case numbers and are therefore likely false US/HK positives: {len(suspect)}",
        f"- Rows that do not obviously look like Chinese case numbers: {len(stronger)}",
        "",
        "### Sample suspect rows",
        "",
    ]

    for row in suspect[:10]:
        lines.append(
            f"- {row['case_id']} | {row['jurisdiction']} | {row['domain']} | "
            f"claim={row['initial_claim'] or 'NA'} | award={row['final_award'] or 'NA'} | "
            f"case_number={row['case_number']}"
        )

    lines.extend(
        [
            "",
            "## Local US/HK source cards with money mentions",
            "",
            f"- Count: {len(money_cards)}",
            "- These cards mention money, but most are rule cards, statutory caps, or jury-award snapshots rather than full case-award records satisfying the T9.4 schema.",
            "",
        ]
    )

    for row in money_cards:
        lines.append(
            f"- {row['jurisdiction']} {row['pattern_id']} | {row['domain']} | "
            f"money={row['money_mentions']} | {row['fact_summary']}"
        )

    lines.extend(
        [
            "",
            "## Conclusion",
            "",
            "- Local T9.4 US/HK evidence is currently insufficient for a trustworthy large-batch export in the prompt schema.",
            "- The next valid path is targeted first-hand case research for US/HK damages judgments with explicit claim/award/appeal data, then manual normalization into the T9.4 columns.",
        ]
    )

    OUT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote audit report to {OUT_PATH}")


if __name__ == "__main__":
    main()
