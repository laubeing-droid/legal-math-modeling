import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from asset_coverage import (  # noqa: E402
    AssetCoverageError,
    build_disposition,
    check_consumption_claims,
    check_no_double_counted_targets,
    digest_id,
    disposition_for,
    load_candidates,
    no_orphan_assets_without_source_bound_disposition,
    summarise,
)


def _cand(job: str, reasons: list[str], proof: str = "NOT_PROVED") -> dict:
    return {"job_id": job, "hold_reasons": reasons, "formal_proof": proof,
            "producer": "test"}


def test_retired_wins_over_other_reasons():
    entry = disposition_for(_cand("j1", ["RESERVE_BY_DESIGN", "RETIRED"]))
    assert entry["disposition"] == "DISPOSED_RETIRED"


def test_source_review_beats_jurisdiction():
    entry = disposition_for(
        _cand("j2", ["JURISDICTION_ADAPTATION_REQUIRED",
                     "SOURCE_SUPPORT_REVIEW_PENDING_OR_REVISION"])
    )
    assert entry["disposition"] == "HELD_PENDING_SOURCE_REVIEW"


def test_unknown_reasons_fail_closed():
    with pytest.raises(AssetCoverageError, match="no source-bound state"):
        disposition_for(_cand("j3", ["SOMETHING_NEW"]))


def test_source_bound_unreasoned_candidate_held_as_obligation():
    cand = _cand("j3b", [])
    cand.update(
        state="SOURCE_BOUND_CANDIDATE",
        proof_status="OBLIGATIONS_ONLY_NOT_PROVED",
        source_support_review="SUPPORTED",
    )
    entry = disposition_for(cand)
    assert entry["disposition"] == "HELD_AS_UNCONSUMED_OBLIGATION"
    assert entry["rationale"] == ["source_bound_unconsumed_obligation"]


def test_proved_candidate_rejected():
    with pytest.raises(AssetCoverageError, match="CANDIDATE_ONLY"):
        disposition_for(_cand("j4", ["RETIRED"], proof="PROVED"))


def test_orphan_detection():
    disposition = {digest_id("j5"): disposition_for(_cand("j5", ["RETIRED"]))}
    with pytest.raises(AssetCoverageError, match="without disposition"):
        no_orphan_assets_without_source_bound_disposition(
            [digest_id("j5"), digest_id("ghost")], disposition
        )


def test_tombstone_detection():
    disposition = {digest_id("j6"): disposition_for(_cand("j6", ["RETIRED"])),
                   digest_id("j7"): disposition_for(_cand("j7", ["RETIRED"]))}
    with pytest.raises(AssetCoverageError, match="tombstone"):
        no_orphan_assets_without_source_bound_disposition([digest_id("j6")], disposition)


def test_claimed_wired_but_zero_consumption_rejected():
    d = digest_id("j8")
    disposition = {d: disposition_for(_cand("j8", ["RETIRED"]))}
    with pytest.raises(AssetCoverageError, match="consumption is 0"):
        check_consumption_claims([d], {}, disposition)


def test_double_counted_target_rejected():
    with pytest.raises(AssetCoverageError, match="double-counted"):
        check_no_double_counted_targets({"T9": ["a", "a"]})


def test_load_and_end_to_end(tmp_path: Path):
    path = tmp_path / "candidates.jsonl"
    rows = [
        _cand("k1", ["RETIRED"]),
        _cand("k2", ["JURISDICTION_ADAPTATION_REQUIRED"]),
        _cand("k3", ["RESERVE_BY_DESIGN"]),
    ]
    path.write_text("\n".join(json.dumps(r) for r in rows), encoding="utf-8")
    candidates = load_candidates(path)
    disposition = build_disposition(candidates)
    no_orphan_assets_without_source_bound_disposition(
        [e["digest"] for e in disposition.values()], disposition
    )
    assert summarise(disposition, total_rows=3)["unique_assets"] == 3
    assert summarise(disposition)["by_disposition"]["DISPOSED_RETIRED"] == 1


def test_duplicate_rows_deduped_with_occurrences():
    cand = _cand("dup", ["RETIRED"])
    disposition = build_disposition([cand, dict(cand), dict(cand)])
    entry = next(iter(disposition.values()))
    assert entry["occurrences"] == 3
    assert summarise(disposition, total_rows=3)["unique_assets"] == 1
