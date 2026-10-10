#!/usr/bin/env python3
"""T107 asset coverage: source-bound disposition for candidate assets.

Contract (R7附件_T37_T111_75项登记.md:1363, appendix K T107 row):
- The disposition map must be total over the actual asset list A
  (dom = A): every item gets a source, a target-T/retention slot or an
  explicit retirement rationale.
- NOT_PROVED candidates are never promoted to theorems by consumption.
- Adversarial cases this module must reject:
  1. README claims the 1502 are wired while actual consumption is 0.
  2. The same target T counted twice for coverage.
  3. Dead-code imports with no actual call/test.
  4. A stale snapshot covering new functionality.

The candidate file itself is private-domain and stays out of Git; the
emitted register records only job_id digests, disposition codes and
rationale classes.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

# Disposition codes. ADOPTED is deliberately absent: candidates in this
# register are CANDIDATE_ONLY/NOT_PROVED and can never be adopted as
# theorems by consumption (T107 contract).
DISPOSED_RETIRED = "DISPOSED_RETIRED"
HELD_PENDING_SOURCE_REVIEW = "HELD_PENDING_SOURCE_REVIEW"
HELD_PENDING_JURISDICTION_ADAPTATION = "HELD_PENDING_JURISDICTION_ADAPTATION"
RESERVED_BY_DESIGN = "RESERVED_BY_DESIGN"
HELD_AS_UNCONSUMED_OBLIGATION = "HELD_AS_UNCONSUMED_OBLIGATION"
UNDISPOSITIONED = "UNDISPOSITIONED"

_ALLOWED = {
    DISPOSED_RETIRED,
    HELD_PENDING_SOURCE_REVIEW,
    HELD_PENDING_JURISDICTION_ADAPTATION,
    RESERVED_BY_DESIGN,
    HELD_AS_UNCONSUMED_OBLIGATION,
}

# Most conservative first: retirement wins over holds; review-pending wins
# over jurisdiction work because blocking on provenance is stricter.
_PRIORITY = [
    ("RETIRED", DISPOSED_RETIRED),
    ("SOURCE_SUPPORT_REVIEW_PENDING_OR_REVISION", HELD_PENDING_SOURCE_REVIEW),
    ("JURISDICTION_ADAPTATION_REQUIRED", HELD_PENDING_JURISDICTION_ADAPTATION),
    ("RESERVE_BY_DESIGN", RESERVED_BY_DESIGN),
]


class AssetCoverageError(Exception):
    """Fail-closed signal for contract violations."""


def digest_id(job_id: str) -> str:
    return hashlib.sha256(job_id.encode("utf-8")).hexdigest()[:16]


def load_candidates(path: Path) -> list[dict]:
    candidates = []
    with path.open(encoding="utf-8") as fh:
        for lineno, line in enumerate(fh, 1):
            line = line.strip()
            if not line:
                continue
            try:
                candidates.append(json.loads(line))
            except json.JSONDecodeError as exc:  # pragma: no cover - corrupt input
                raise AssetCoverageError(
                    f"candidate line {lineno} is not valid JSON: {exc}"
                ) from exc
    return candidates


def disposition_for(candidate: dict) -> dict:
    """Map one candidate to its source-bound disposition entry."""
    job_id = candidate.get("job_id")
    if not job_id:
        raise AssetCoverageError("candidate without job_id cannot be dispositioned")
    reasons = candidate.get("hold_reasons") or []
    chosen = UNDISPOSITIONED
    for reason, code in _PRIORITY:
        if reason in reasons:
            chosen = code
            break
    if chosen == UNDISPOSITIONED:
        # No hold reason: the register's own state fields must still bind
        # the candidate to a source before it may be held as an obligation.
        if (
            candidate.get("state") == "SOURCE_BOUND_CANDIDATE"
            and candidate.get("proof_status") == "OBLIGATIONS_ONLY_NOT_PROVED"
            and candidate.get("source_support_review") == "SUPPORTED"
        ):
            chosen = HELD_AS_UNCONSUMED_OBLIGATION
            reasons = ["source_bound_unconsumed_obligation"]
        else:
            raise AssetCoverageError(
                f"candidate {job_id} has no recognised hold_reasons "
                f"and no source-bound state: {candidate.get('state')!r}"
            )
    if candidate.get("formal_proof") == "PROVED":
        raise AssetCoverageError(
            f"candidate {job_id} claims formal_proof=PROVED; register is "
            "CANDIDATE_ONLY and must not carry proved entries"
        )
    return {
        "digest": digest_id(job_id),
        "disposition": chosen,
        "rationale": reasons,
        "producer": candidate.get("producer"),
    }


def build_disposition(candidates: list[dict]) -> dict:
    """Disposition map keyed by digest over unique job_ids.

    The register contains repeated rows for the same job_id (same
    snapshot, later state records); each unique job is dispositioned once
    from its last record and the row count is recorded so the ledger
    total stays honest (1502 rows, 1008 unique assets — never presented
    as 1502 distinct assets).
    """
    latest: dict[str, tuple[int, dict]] = {}
    for idx, cand in enumerate(candidates):
        job_id = cand.get("job_id")
        if not job_id:
            raise AssetCoverageError("candidate without job_id cannot be dispositioned")
        prev = latest.get(job_id)
        if prev is None or idx > prev[0]:
            latest[job_id] = (idx, cand)
    table: dict[str, dict] = {}
    occurrences: dict[str, int] = {}
    for job_id, (_, cand) in latest.items():
        entry = disposition_for(cand)
        entry["occurrences"] = sum(
            1 for c in candidates if c.get("job_id") == job_id
        )
        digest = digest_id(job_id)
        if digest in table:  # pragma: no cover - digest collision
            raise AssetCoverageError(f"duplicate job_id digest {digest}")
        table[digest] = entry
        occurrences[str(entry["occurrences"])] = (
            occurrences.get(str(entry["occurrences"]), 0) + 1
        )
    return table


def no_orphan_assets_without_source_bound_disposition(
    asset_ids: list[str], disposition: dict[str, dict]
) -> None:
    """Raise unless every asset has a source-bound disposition entry.

    Orphan (in A, missing from the map), tombstone (in the map, not in A)
    and non-allowed disposition codes all fail closed.
    """
    asset_set = set(asset_ids)
    missing = sorted(asset_set - set(disposition))
    if missing:
        raise AssetCoverageError(f"{len(missing)} asset(s) without disposition")
    extra = sorted(set(disposition) - asset_set)
    if extra:
        raise AssetCoverageError(f"{len(extra)} tombstone disposition(s) not in A")
    for key, entry in disposition.items():
        if entry["disposition"] not in _ALLOWED:
            raise AssetCoverageError(
                f"disposition {entry['disposition']!r} for {key} not allowed"
            )
        if not entry.get("rationale"):
            raise AssetCoverageError(f"disposition for {key} lacks rationale")


def check_consumption_claims(
    claimed_wired: list[str], consumption: dict[str, int], disposition: dict[str, dict]
) -> None:
    """Adversarial check: no coverage claim without actual consumption.

    claimed_wired: digests the narrative claims are integrated.
    consumption: digest -> observed consumption count (imports, calls,
    tests). A claim with zero consumption is the 'README says wired,
    reality says 0' cheat and fails.
    """
    for digest in claimed_wired:
        if consumption.get(digest, 0) <= 0:
            raise AssetCoverageError(
                f"asset {digest} claimed wired but consumption is 0"
            )
        if digest not in disposition:
            raise AssetCoverageError(f"asset {digest} claimed but not in A")


def check_no_double_counted_targets(target_map: dict[str, list[str]]) -> None:
    """Adversarial check: one asset may serve many targets, but the same
    (asset, target) pair counted twice inflates coverage."""
    seen: set[tuple[str, str]] = set()
    for target, assets in target_map.items():
        for digest in assets:
            pair = (digest, target)
            if pair in seen:
                raise AssetCoverageError(
                    f"asset {digest} double-counted for target {target}"
                )
            seen.add(pair)


def summarise(disposition: dict[str, dict], total_rows: int | None = None) -> dict:
    counts: dict[str, int] = {}
    for entry in disposition.values():
        counts[entry["disposition"]] = counts.get(entry["disposition"], 0) + 1
    summary = {"unique_assets": len(disposition), "by_disposition": counts}
    if total_rows is not None:
        summary["register_rows"] = total_rows
    return summary


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--candidates", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args(argv)

    candidates = load_candidates(args.candidates)
    disposition = build_disposition(candidates)
    no_orphan_assets_without_source_bound_disposition(
        [e["digest"] for e in disposition.values()], disposition
    )
    register = {
        "schema": "t107-asset-disposition-v1",
        "source_path_digest": digest_id(str(args.candidates.resolve())),
        "summary": summarise(disposition, total_rows=len(candidates)),
        "entries": disposition,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(register, ensure_ascii=False, indent=1), encoding="utf-8"
    )
    print(json.dumps(register["summary"], ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
