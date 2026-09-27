#!/usr/bin/env python3
"""Run the retrieved-cohort pipeline against a real, external legal corpus.

Why (R-08): the win-rate pipeline could only ever be exercised on fixtures, so every
number it produced carried cross-cut A's `synthetic_data` ceiling, which is
NOT_CLAIMABLE. This tool fetches rows from a published corpus over HTTP Range -- no
bulk download, no vendoring of case text -- feeds them through
`theory/spec/probability_pipeline.py` unchanged, and writes an aggregate-only report.

What it does not do: it does not establish a causal win rate, it does not upgrade any
claim above `REFERENCE` (cross-cut A `empirical_output`), and it does not keep a single
character of case text in this repository. The corpus it reads carries
`license: unknown` on its host, which the report records as a limitation rather than
silently treating as permission.

    python theory/spec/real_cohort_probe.py --output docs/formal-release/real_cohort_probe.json
"""

from __future__ import annotations

import argparse
import datetime as dt
import json
import sys
import urllib.request
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from theory.spec.probability_pipeline import (  # noqa: E402
    RetrievedOutcome,
    WinEventDefinition,
    TemporalProtocol,
    estimate_retrieved_cohort,
    observed_frequency,
)

DATASET = "china-ai-law-challenge/cail2018"
FILE = "data/exercise_contest_train-00000-of-00001.parquet"
URL = f"https://huggingface.co/datasets/{DATASET}/resolve/main/{FILE}"
HOST_LICENSE = "unknown (challenge terms: research use; no permissive SPDX on the host card)"
OUTCOME_RULE = "imprisonment <= 36 months (轻刑档)"
SCHEMA = "real-cohort-probe-v1"
STATUS = "reference_grade_real_corpus_probe_not_causal_claim"
AUTHORITY = (
    "Aggregates computed from an external corpus at run time. Grade ceiling is "
    "REFERENCE per cross-cut A empirical_output; nothing here licenses a claim about "
    "win probability in a named jurisdiction, and no case text is stored. The source "
    "record's own license field is 'unknown', so a release may cite these numbers only "
    "as an instrument check, never as legal evidence."
)


class HttpRange:
    """Minimal seekable HTTP reader so only the needed row groups are transferred."""

    def __init__(self, url: str, timeout: int = 180) -> None:
        self.url, self.timeout = url, timeout
        req = urllib.request.Request(url, method="HEAD")
        with urllib.request.urlopen(req, timeout=timeout) as r:
            headers = r.headers
        if not headers.get("Accept-Ranges", "").lower().startswith("byte"):
            raise RuntimeError("host does not advertise byte ranges; refusing to bulk download")
        self.length = int(headers["Content-Length"])
        self.etag = (headers.get("ETag") or "").strip('"')
        self.linked_size = headers.get("X-Linked-Size")
        self.pos = 0
        self.bytes_read = 0
        self.closed = False

    def seek(self, offset: int, whence: int = 0) -> None:
        base = self.pos if whence == 1 else (self.length if whence == 2 else 0)
        self.pos = max(0, min(base + offset, self.length))

    def tell(self) -> int:
        return self.pos

    def read(self, size: int = -1) -> bytes:
        stop = self.length - 1 if size is None or size < 0 else min(self.length - 1, self.pos + size - 1)
        if self.pos > stop:
            return b""
        req = urllib.request.Request(self.url, headers={"Range": f"bytes={self.pos}-{stop}"})
        with urllib.request.urlopen(req, timeout=self.timeout) as r:
            data = r.read()
        self.pos += len(data)
        self.bytes_read += len(data)
        return data

    def close(self) -> None:
        self.closed = True


def event_for(charge: str, split: str) -> WinEventDefinition:
    """One fully specified event contract per cohort; any blank field and the
    pipeline itself returns UNKNOWN, which is the point of routing through it."""

    return WinEventDefinition(
        identity=f"cail2018::{charge}::{OUTCOME_RULE}",
        cluster=f"charge::{charge}",
        objective="刑事实证分布的仪表化核验（instrument check），非胜诉率主张",
        group=f"charge::{charge}",
        temporal=TemporalProtocol(
            split=split,
            cutoff="publication-of-the-exercise-contest-release",
            feature_latest="fact-段文本中的既认定情节",
            outcome_time="判决时点（同一次判决内）",
        ),
        target_population=f"CAIL2018 exercise_contest_train 中主罪名为「{charge}」的全部记录",
        outcome_variable=OUTCOME_RULE,
        observation_mechanism="数据集自带 imprisonment 月数字段；缺失或不可解析的记录记为未观测，不入分母",
    )


def outcome_of(row: Dict[str, Any]) -> Tuple[bool, Optional[bool]]:
    """(observed, success). Missing or negative sentences are unobserved."""

    months = row.get("imprisonment")
    if months is None:
        return False, None
    try:
        value = float(months)
    except (TypeError, ValueError):
        return False, None
    if value < 0 or value > 1200:
        return False, None
    return True, value <= 36


def probe(row_groups: int, max_cohorts: int) -> Dict[str, Any]:
    import pyarrow as pa
    import pyarrow.parquet as pq

    src = HttpRange(URL)
    pf = pq.ParquetFile(pa.PythonFile(src, mode="r"))
    meta = pf.metadata
    groups = min(row_groups, meta.num_row_groups)
    records: List[Dict[str, Any]] = []
    for g in range(groups):
        records.extend(pf.read_row_group(g, columns=["accusation", "imprisonment"]).to_pylist())

    per_charge: Dict[str, List[Tuple[bool, Optional[bool]]]] = {}
    for rec in records:
        charges = rec.get("accusation") or []
        if not charges:
            continue
        per_charge.setdefault(str(charges[0]), []).append(outcome_of(rec))

    charges = sorted(per_charge, key=lambda c: -len(per_charge[c]))[:max_cohorts]
    cohorts = []
    for charge in charges:
        obs = per_charge[charge]
        rows = tuple(
            RetrievedOutcome(case_id=f"cail2018-rg{g}-i{i}", observed=o, success=bool(s))
            for i, (o, s) in enumerate(obs)
        )
        freq = observed_frequency(rows)
        entry: Dict[str, Any] = {
            "charge": charge,
            "rows_retrieved": len(rows),
            "rows_observed": freq.observed_total,
            "successes": freq.successes,
            "frequency": str(freq.frequency) if freq.frequency is not None else None,
        }
        try:
            est = estimate_retrieved_cohort(event=event_for(charge, "train"), rows=rows, repo_root=ROOT)
            entry.update(
                {
                    "identity": est.identity,
                    "status": est.status.value if hasattr(est.status, "value") else str(est.status),
                    "interval_low": str(est.interval_low) if est.interval_low is not None else None,
                    "interval_high": str(est.interval_high) if est.interval_high is not None else None,
                }
            )
        except Exception as exc:  # fail closed: record why, never invent an interval
            entry.update({"identity": "RETRIEVED_COHORT", "status": "BACKEND_UNAVAILABLE",
                          "interval_low": None, "interval_high": None,
                          "backend_note": f"{type(exc).__name__}: {str(exc)[:120]}"})
        cohorts.append(entry)

    every = observed_frequency(
        tuple(
            RetrievedOutcome(case_id=f"all-{i}", observed=o, success=bool(s))
            for obs in per_charge.values() for i, (o, s) in enumerate(obs)
        )
    )
    return {
        "schema_version": SCHEMA,
        "status": STATUS,
        "authority_note": AUTHORITY,
        "generated_by": "python theory/spec/real_cohort_probe.py",
        "source": {
            "dataset": DATASET,
            "file": FILE,
            "url": URL,
            "http_etag": src.etag,
            "remote_bytes": src.length,
            "bytes_transferred": src.bytes_read,
            "row_groups_read": groups,
            "records_read": len(records),
            "license_on_record": HOST_LICENSE,
            "retrieved_at": dt.datetime.now(dt.timezone.utc).isoformat(timespec="seconds"),
            "outcome_rule": OUTCOME_RULE,
        },
        "whole_sample": {
            "rows_observed": every.observed_total,
            "successes": every.successes,
            "frequency": str(every.frequency) if every.frequency is not None else None,
            "charges_seen": len(per_charge),
        },
        "cohorts": cohorts,
        "limitations": [
            "CAIL2018 carries no per-case date, so win_model's anti-leakage ordering "
            "(cutoff / feature_latest / outcome_time) cannot be honestly filled; the "
            "interval path therefore stays BACKEND_UNAVAILABLE by design and only the "
            "realized frequency is reported.",
            "source record license is 'unknown', so these aggregates are an instrument "
            "check, not publishable legal evidence",
            "one row group sample of the exercise-contest split, not the full corpus",
        ],
        "grade_ceiling": "REFERENCE",
        "crosscut_grade": "crosscutA/empirical_output=REFERENCE",
        "privacy": "no case text, party names, or court identifiers are written; only charge labels, counts and rates",
        "forbidden_readings": [
            "胜诉率", "因果效应", "可发布为法律证据", "跨法域外推", "把 synthetic 通道升格",
        ],
    }


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--output", type=Path, default=ROOT / "docs/formal-release/real_cohort_probe.json")
    ap.add_argument("--row-groups", type=int, default=4)
    ap.add_argument("--max-cohorts", type=int, default=12)
    args = ap.parse_args()

    try:
        doc = probe(args.row_groups, args.max_cohorts)
    except ImportError as exc:
        print(f"BACKEND_UNAVAILABLE: {exc} (pyarrow is required for this probe)", file=sys.stderr)
        return 2
    args.output.write_text(
        json.dumps(doc, ensure_ascii=False, indent=1, sort_keys=True) + "\n",
        encoding="utf-8", newline="\n",
    )
    src = doc["source"]
    print(
        f"rows {src['records_read']} from {src['row_groups_read']} row groups "
        f"({src['bytes_transferred']} bytes of {src['remote_bytes']}); "
        f"cohorts {len(doc['cohorts'])}; whole-sample frequency {doc['whole_sample']['frequency']}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
