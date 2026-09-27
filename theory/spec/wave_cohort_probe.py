#!/usr/bin/env python3
"""Measure a dated cohort of real Chinese court documents through the win-rate pipeline.

Why (R-08): the interval path needed per-case judgment dates, and the published
corpora we could reach either were gated behind terms of use or carried no dates at
all, so `real_cohort_probe.py` could only ever report a realized frequency and left
every cohort interval `BACKEND_UNAVAILABLE`. This tool reads the local WAVE-ALL-001
delivery -- 159,507,974 rows over 491 monthly shards, each row carrying `judge_date`,
`case_class`, `trial_prog` and `case_result` -- and feeds a dated cohort through
`theory/spec/probability_pipeline.py` unchanged, which is the first time the Beta
interval is computed on real judgments rather than on fixtures.

What it deliberately does not do:

* It never stores case text, party names, or document identifiers in this repository.
  The report holds counts, one rational frequency, and one interval.
* It does not measure a legal "win rate". The event is spelled out verbatim in the
  report as a text-matching rule over `case_result`; anything stronger (party
  satisfaction, counsel performance, reversibility on retrial) is not observed here.
* It does not impute the outcome. A row whose `case_result` is empty is `observed
  = False`, so the observed denominator is whatever the corpus actually answers, and
  the unknown share is published next to the interval.
* It does not claim the corpus is licensed for redistribution. The delivery documents
  per-field provenance but states no terms of use; that is recorded as a limitation,
  which is what caps the grade.

    python theory/spec/wave_cohort_probe.py --output docs/formal-release/wave_cohort_probe.json
"""

from __future__ import annotations

import argparse
import csv
import datetime as dt
import gzip
import hashlib
import json
import re
import sys
from fractions import Fraction
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Tuple

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from theory.spec.probability_pipeline import (  # noqa: E402
    RetrievedOutcome,
    TemporalProtocol,
    WinEventDefinition,
    estimate_retrieved_cohort,
)

DEFAULT_DATASET = Path("D:/Codex/1.法律工作区/legal-cn-cases工作区/legal-cn-cases")
SHARD_DIR = "WAVE-ALL-001"

# The event, stated as the text rule it actually is rather than as a legal concept.
WIN_MATCHER = re.compile("驳回上诉")
COHORT_CLASS = "民事案件"
COHORT_PROG = "民事二审"


def month_shards(shard_dir: Path, months: List[str]) -> List[Path]:
    paths = [shard_dir / f"{m}.csv.gz" for m in months]
    missing = [str(p.name) for p in paths if not p.exists()]
    if missing:
        raise SystemExit(f"missing monthly shards: {missing}")
    return paths


def parse_date(value: str) -> Optional[dt.date]:
    value = (value or "").strip()
    for fmt in ("%Y-%m-%d", "%Y/%m/%d", "%Y年%m月%d日"):
        try:
            return dt.datetime.strptime(value, fmt).date()
        except ValueError:
            continue
    return None


def read_cohort(
    paths: Iterable[Path], cap_per_month: int
) -> Tuple[List[Tuple[str, bool, bool, str]], dict]:
    """Stream the shards and return (case_id, observed, success, judge_date) records."""
    rows: List[Tuple[str, bool, bool, str]] = []
    stats = {
        "rows_seen": 0,
        "cohort_matched": 0,
        "undated_dropped": 0,
        "outcome_known": 0,
        "outcome_empty": 0,
        "duplicate_doc_ids_dropped": 0,
        "synthetic_doc_ids": 0,
        "judged_outside_shard_month": 0,
        "months_truncated_by_cap": [],
        "per_month": {},
        "judge_date_min": None,
        "judge_date_max": None,
    }
    for path in paths:
        month = path.name[:7]
        seen_in_month = 0
        with gzip.open(path, "rt", encoding="utf-8", errors="replace", newline="") as handle:
            csv.field_size_limit(2**31 - 1)
            reader = csv.DictReader(handle)
            for row in reader:
                seen_in_month += 1
                if seen_in_month > cap_per_month:
                    break
                stats["rows_seen"] += 1
                if (row.get("case_class") or "") != COHORT_CLASS:
                    continue
                if (row.get("trial_prog") or "") != COHORT_PROG:
                    continue
                judged = parse_date(row.get("judge_date") or "")
                if judged is None:
                    # A row with no readable judgment date cannot sit in a dated
                    # cohort; counted separately so the cohort denominators agree.
                    stats["undated_dropped"] += 1
                    continue
                stats["cohort_matched"] += 1
                if judged.strftime("%Y-%m") != month:
                    # Shards are not ordered by judgment date, so a month's file can
                    # carry rulings dated into the next month. Recorded, not filtered.
                    stats["judged_outside_shard_month"] += 1
                result = (row.get("case_result") or "").strip()
                observed = bool(result)
                if observed:
                    stats["outcome_known"] += 1
                else:
                    stats["outcome_empty"] += 1
                success = bool(WIN_MATCHER.search(result)) if observed else False
                doc_id = (row.get("canonical_doc_id") or "").strip()
                if doc_id:
                    identity = doc_id
                else:
                    # No document identifier: a positional label keeps the row
                    # countable but is recorded so the report can say how many.
                    identity = f"no-doc-id::{month}::{seen_in_month}"
                    stats["synthetic_doc_ids"] += 1
                rows.append((identity, observed, success, judged.isoformat()))
                lo, hi = stats["judge_date_min"], stats["judge_date_max"]
                iso = judged.isoformat()
                if lo is None or iso < lo:
                    stats["judge_date_min"] = iso
                if hi is None or iso > hi:
                    stats["judge_date_max"] = iso
        per_month = stats["per_month"]
        per_month[month] = per_month.get(month, 0) + min(seen_in_month, cap_per_month)
        if seen_in_month > cap_per_month:
            stats["months_truncated_by_cap"].append(month)
    return rows, stats


def verify_manifest_rowcount(shard_dir: Path, month: str) -> dict:
    """Compare one shard's row count against the delivery's own MANIFEST ledger."""
    manifest = shard_dir / "MANIFEST.csv"
    target = shard_dir / f"{month}.csv.gz"
    if not manifest.exists() or not target.exists():
        return {"status": "MANIFEST_OR_SHARD_ABSENT"}
    declared = None
    with manifest.open("r", encoding="utf-8", errors="replace", newline="") as handle:
        for row in csv.DictReader(handle):
            if (row.get("month") or "").strip() == month:
                declared = int((row.get("rows") or "0").strip() or 0)
                break
    if declared is None:
        return {"status": "MONTH_NOT_IN_MANIFEST", "month": month}
    counted = 0
    digest = hashlib.sha256()
    with gzip.open(target, "rt", encoding="utf-8", errors="replace", newline="") as handle:
        csv.field_size_limit(2**31 - 1)
        reader = csv.reader(handle)
        next(reader, None)
        for record in reader:
            counted += 1
            digest.update("\x01".join(record).encode("utf-8"))
    return {
        "status": "OK",
        "month": month,
        "manifest_rows": declared,
        "counted_rows": counted,
        "rows_match": declared == counted,
        "row_payload_sha256": digest.hexdigest(),
        "checksum_method": "README.md: fields joined with \\x01, header and newlines excluded",
    }


def build_event(cutoff: str) -> WinEventDefinition:
    # The backend registers time at cohort level, not per row: `win_model.Row` rejects
    # a row whose outcome is not strictly after its cutoff. Every judgment in the slice
    # was rendered on or before `cutoff`, so outcomes are all known one day later.
    outcome_time = (
        dt.date.fromisoformat(cutoff) + dt.timedelta(days=1)
    ).isoformat()
    return WinEventDefinition(
        identity="wave-001-civil-second-instance-affirmance",
        cluster=f"wave001::{COHORT_CLASS}::{COHORT_PROG}",
        objective=f"case_result matches /{WIN_MATCHER.pattern}/ on 民事二审 民事案件文书",
        group="wave001_civil2d",
        temporal=TemporalProtocol(
            split="train",
            cutoff=cutoff,
            feature_latest=cutoff,
            outcome_time=outcome_time,
        ),
        target_population=f"WAVE-ALL-001 {COHORT_CLASS}/{COHORT_PROG} 文书，"
                          f"裁判日期 {cutoff} 及以前",
        outcome_variable="case_result 文本匹配（'驳回上诉'）",
        observation_mechanism="逐月成品文件按 judge_date 直接可读，无抽样",
    )


def main(argv: Optional[List[str]] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--dataset", type=Path, default=DEFAULT_DATASET)
    ap.add_argument("--months", default="2019-01,2019-06,2019-12")
    ap.add_argument("--cap-per-month", type=int, default=120000)
    ap.add_argument("--manifest-check-month", default="1985-01",
                    help="small month used for the independent row-count recheck")
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args(argv)

    shard_dir = args.dataset / SHARD_DIR
    if not shard_dir.exists():
        print(f"dataset not present: {shard_dir}", file=sys.stderr)
        return 2
    months = [m.strip() for m in args.months.split(",") if m.strip()]
    rows, stats = read_cohort(month_shards(shard_dir, months), args.cap_per_month)
    observed_rows = [r for r in rows if r[1]]
    if not observed_rows:
        print("no observed outcomes in cohort; refusing to publish an estimate",
              file=sys.stderr)
        return 1

    cutoff = stats["judge_date_max"]
    # The Beta backend rejects repeated identities, so a doc id appearing in more
    # than one shard row is counted once and the surplus is reported, not hidden.
    seen: Dict[str, Tuple[str, bool, bool]] = {}
    dropped = 0
    for case_id, observed, success, _day in rows:
        if case_id in seen:
            dropped += 1
            continue
        seen[case_id] = (case_id, observed, success)
    stats["duplicate_doc_ids_dropped"] = dropped
    outcomes = [
        RetrievedOutcome(case_id=case_id, observed=observed, success=success,
                         synthetic=False)
        for case_id, observed, success in seen.values()
    ]
    estimate = estimate_retrieved_cohort(
        event=build_event(cutoff), rows=outcomes, repo_root=ROOT
    )
    freq = estimate.frequency
    successes = sum(1 for _id, observed, success in seen.values() if observed and success)
    report = {
        "schema_version": "wave-cohort-probe-v1",
        "generated_by": "python theory/spec/wave_cohort_probe.py --output <path>",
        "authority_note": (
            "Counts computed by streaming the delivery's own monthly shards on this "
            "machine. Aggregate only: no case text, party name, or document identifier "
            "is stored. The realized frequency is rational; the interval comes from the "
            "repository's existing win_model Beta backend, not from this file."
        ),
        "source": {
            "dataset_root": str(args.dataset),
            "shard_dir": SHARD_DIR,
            "months_read": months,
            "rows_capped_per_month": args.cap_per_month,
            "delivery_row_count_claimed": 159507974,
            "manifest_recheck": verify_manifest_rowcount(shard_dir, args.manifest_check_month),
        },
        "event": {
            "case_class": COHORT_CLASS,
            "trial_prog": COHORT_PROG,
            "outcome_matcher": f"case_result 含 '{WIN_MATCHER.pattern}'",
            "cutoff": cutoff,
            "identification_status": estimate.status.value,
            "identity": estimate.identity,
        },
        "cohort": {
            **stats,
            "unknown_share": str(Fraction(stats["outcome_empty"], max(1, stats["cohort_matched"]))),
        },
        "estimate": {
            "successes": successes,
            "observed_total": estimate.observed_total,
            "frequency_fraction": str(freq) if freq is not None else None,
            "frequency_decimal": (round(float(freq), 6) if freq is not None else None),
            "interval_low": estimate.interval_low,
            "interval_high": estimate.interval_high,
            "interval_backend": "unified.win_model.latent_rate_interval",
        },
        "grade_ceiling": "EVIDENCE_WITH_PROVENANCE_CAVEAT",
        "limitations": [
            "Each month was read as a file-order prefix under a row cap"
            + (f"; the cap bound {len(stats['months_truncated_by_cap'])} of "
               f"{len(months)} months ({stats['months_truncated_by_cap']})"
               if stats["months_truncated_by_cap"] else "; no month hit the cap")
            + ". A prefix is not a random sample and no sampling claim is made: this "
            "is a declared slice, not the delivery's population.",
            "`case_result` is free text; the event is a string match on '驳回上诉', so "
            "the rate is an affirmation rate under that matcher and not a measurement "
            "of party success, counsel performance, or legal error.",
            f"{stats['outcome_empty']} of {stats['cohort_matched']} cohort rows carry an "
            "empty `case_result`; those rows are `observed = False` and never imputed, "
            "so the interval covers only the self-reported outcome subset.",
            "Shards are not ordered by `judge_date`: "
            f"{stats['judged_outside_shard_month']} cohort rows carry a judgment date "
            "outside their shard's month. They are kept and the cutoff is the observed "
            "maximum, so the cohort window is set by the data rather than by the "
            "filename.",
            "The delivery records per-field provenance but states no terms of use for "
            "the underlying documents; redistribution is therefore not claimed and the "
            "numbers here stay aggregate.",
            "The interval is model-relative posterior mass from the repository's "
            "hyperprior mixture over one exchangeable group, not frequentist coverage "
            "and not a prediction interval for the next judgment.",
        ],
        "forbidden_readings": [
            "胜诉率的经验校准已完成",
            "二审维持率等于原审正确率",
            "该区间的口径适用于全部案件类型",
        ],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(report, ensure_ascii=False, indent=2, default=str) + "\n", encoding="utf-8"
    )
    print(f"wrote {args.output.relative_to(ROOT) if args.output.is_relative_to(ROOT) else args.output}"
          f": observed={estimate.observed_total} successes={successes} "
          f"freq={freq} interval=[{estimate.interval_low}, {estimate.interval_high}]")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
