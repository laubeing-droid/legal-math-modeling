"""Contract tests for the WAVE-ALL-001 cohort probe (R-08).

The corpus is a local delivery, not a repository asset, so the tests that need it
skip when it is absent. What never skips is the temporal registration: the Beta
backend rejects a row whose outcome is not strictly after its cutoff, which is the
exact way this probe was first broken.
"""

from __future__ import annotations

import datetime as dt
import gzip
import json
from pathlib import Path

import pytest

from theory.spec import wave_cohort_probe as probe
from theory.spec.probability_pipeline import TemporalProtocol

ROOT = Path(probe.__file__).resolve().parents[2]

COLUMNS = ["canonical_doc_id", "case_class", "trial_prog", "judge_date", "case_result"]


def write_shard(path: Path, rows) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with gzip.open(path, "wt", encoding="utf-8", newline="") as handle:
        handle.write(",".join(COLUMNS) + "\n")
        for row in rows:
            handle.write(",".join(row) + "\n")


def test_parse_date_accepts_the_delivery_formats() -> None:
    assert probe.parse_date("2019-12-03") == dt.date(2019, 12, 3)
    assert probe.parse_date("2019/12/03") == dt.date(2019, 12, 3)
    assert probe.parse_date("2019年12月03日") == dt.date(2019, 12, 3)
    assert probe.parse_date("") is None
    assert probe.parse_date("不详") is None


def test_event_temporal_is_accepted_by_the_beta_backend() -> None:
    """`win_model.Row` raises unless feature_latest <= cutoff < outcome_time."""
    from theory.spec.probability_pipeline import load_win_model_module

    event = probe.build_event("2020-02-24")
    temporal: TemporalProtocol = event.temporal
    assert temporal.feature_latest <= temporal.cutoff < temporal.outcome_time
    win = load_win_model_module(Path(probe.__file__).resolve().parents[2])
    row = win.Row(
        identity="x", cluster="c", objective=event.objective, group=event.group,
        split="train", cutoff=temporal.cutoff, feature_latest=temporal.feature_latest,
        outcome_time=temporal.outcome_time, label=1, source="retrieved_cohort",
        synthetic=False,
    )
    assert row.outcome_time > row.cutoff
    assert dt.date.fromisoformat(temporal.outcome_time) - dt.date.fromisoformat(
        temporal.cutoff) == dt.timedelta(days=1)


def test_read_cohort_keeps_only_the_declared_cohort_and_never_imputes(tmp_path) -> None:
    shard = tmp_path / "2019-12.csv.gz"
    write_shard(shard, [
        ["d1", "民事案件", "民事二审", "2019-12-02", "驳回上诉，维持原判"],
        ["d2", "民事案件", "民事二审", "2019-12-03", "改判"],
        ["d3", "民事案件", "民事二审", "2019-12-04", ""],           # outcome unknown
        ["d4", "民事案件", "民事一审", "2019-12-05", "驳回上诉"],   # wrong stage
        ["d5", "刑事案件", "民事二审", "2019-12-06", "驳回上诉"],   # wrong class
        ["d6", "民事案件", "民事二审", "", "驳回上诉"],             # undated
        ["d7", "民事案件", "民事二审", "2020-01-11", "驳回上诉"],   # outside shard month
        ["d1", "民事案件", "民事二审", "2019-12-02", "驳回上诉"],   # duplicate doc id
    ])
    rows, stats = probe.read_cohort([shard], cap_per_month=1000)
    assert stats["rows_seen"] == 8
    # `cohort_matched` counts only rows that actually entered the dated cohort, so
    # `outcome_empty / cohort_matched` below is a share of the cohort, not of the file.
    assert stats["cohort_matched"] == 5
    assert stats["undated_dropped"] == 1
    assert stats["outcome_known"] == 4
    assert stats["outcome_empty"] == 1
    assert stats["judged_outside_shard_month"] == 1
    assert stats["months_truncated_by_cap"] == []
    assert [r[2] for r in rows] == [True, False, False, True, True]
    # The unknown row stays in the cohort as observed=False; nothing was imputed.
    assert sum(1 for _id, observed, _s, _d in rows if not observed) == 1


def test_row_cap_truncation_is_reported(tmp_path) -> None:
    shard = tmp_path / "2019-12.csv.gz"
    write_shard(shard, [["d%d" % i, "民事案件", "民事二审", "2019-12-02", "驳回上诉"]
                        for i in range(6)])
    rows, stats = probe.read_cohort([shard], cap_per_month=3)
    assert stats["rows_seen"] == 3
    assert len(rows) == 3
    assert stats["months_truncated_by_cap"] == ["2019-12"]


def test_manifest_recheck_compares_against_the_delivery_ledger(tmp_path) -> None:
    write_shard(tmp_path / "1985-01.csv.gz", [["d1", "民事案件", "民事一审", "1985-01-02", ""]])
    (tmp_path / "MANIFEST.csv").write_text(
        "month,rows\n1985-01,1\n", encoding="utf-8", newline=""
    )
    out = probe.verify_manifest_rowcount(tmp_path, "1985-01")
    assert out["status"] == "OK"
    assert out["rows_match"] is True
    assert out["counted_rows"] == 1
    assert len(out["row_payload_sha256"]) == 64


def test_absent_dataset_exits_nonzero(tmp_path) -> None:
    rc = probe.main(["--dataset", str(tmp_path), "--output", str(tmp_path / "out.json")])
    assert rc == 2


SHARDS = Path(probe.DEFAULT_DATASET) / probe.SHARD_DIR
REPORT = ROOT / "docs" / "formal-release" / "wave_cohort_probe.json"


def _report() -> dict:
    import json

    return json.loads(REPORT.read_text(encoding="utf-8"))


@pytest.mark.skipif(not REPORT.exists(), reason="probe report not generated yet")
def test_committed_report_is_internally_consistent() -> None:
    """Gate the published artifact itself, not just the code that writes it.

    This checks arithmetic and disclosure, not reproducibility: re-deriving the
    counts means re-streaming the delivery, which CI cannot do.
    """
    from fractions import Fraction

    report = _report()
    est = report["estimate"]
    freq = Fraction(est["frequency_fraction"])
    assert freq == Fraction(est["successes"], est["observed_total"])
    assert round(float(freq), 6) == est["frequency_decimal"]
    assert 0 <= est["successes"] <= est["observed_total"]
    assert report["event"]["identification_status"] == "IDENTIFIED"
    assert report["event"]["identity"] == "RETRIEVED_COHORT"
    low, high = Fraction(est["interval_low"]), Fraction(est["interval_high"])
    assert low <= freq <= high and 0 < float(low) and float(high) < 1
    assert est["interval_backend"] == "unified.win_model.latent_rate_interval"


@pytest.mark.skipif(not REPORT.exists(), reason="probe report not generated yet")
def test_committed_report_states_its_ceiling_and_every_caveat() -> None:
    report = _report()
    assert report["grade_ceiling"] == "EVIDENCE_WITH_PROVENANCE_CAVEAT"
    text = json.dumps(report, ensure_ascii=False)
    assert "驳回上诉，维持" not in text and "no-doc-id::" not in text
    # Every slice fact that could be read as a population claim must be caveated.
    cohort = report["cohort"]
    assert cohort["outcome_known"] + cohort["outcome_empty"] == cohort["cohort_matched"]
    assert len(report["limitations"]) >= 5
    assert report["forbidden_readings"]
    assert report["source"]["manifest_recheck"]["rows_match"] is True


@pytest.mark.skipif(not SHARDS.exists(), reason="local WAVE-ALL-001 delivery absent")
def test_probe_on_real_shards_publishes_a_bracketed_interval(tmp_path) -> None:
    from fractions import Fraction

    out = tmp_path / "probe.json"
    rc = probe.main([
        "--months", "2019-12", "--cap-per-month", "4000",
        "--output", str(out),
    ])
    assert rc == 0
    report = json.loads(out.read_text(encoding="utf-8"))
    est = report["estimate"]
    assert report["event"]["identification_status"] == "IDENTIFIED"
    assert report["event"]["identity"] == "RETRIEVED_COHORT"
    assert est["observed_total"] > 0
    low = Fraction(est["interval_low"])
    high = Fraction(est["interval_high"])
    freq = Fraction(est["frequency_fraction"])
    assert low <= freq <= high
    assert 0.0 < float(low) and float(high) < 1.0
    # Aggregate only: the report must not carry document identifiers or case text.
    text = json.dumps(report, ensure_ascii=False)
    assert "驳回上诉，维持" not in text
    assert "no-doc-id::" not in text
    assert report["source"]["manifest_recheck"]["status"] == "OK"
    assert report["grade_ceiling"] == "EVIDENCE_WITH_PROVENANCE_CAVEAT"
