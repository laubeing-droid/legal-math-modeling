#!/usr/bin/env python3
"""Materialize the tracked LMM refinement template for one repository commit."""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import subprocess
import tempfile
from typing import Any, Mapping, Sequence

from theory.spec.runtime_differential import build_expected_fixture


TEMPLATE_SCHEMA = "runtime-refinement-expected-template-v2"
TEMPLATE_STATUS = "expected_only_not_runtime_receipt"


def materialize_expected_fixture(
    template: Mapping[str, Any],
    *,
    lmm_commit: str,
    source_snapshot_digests: Sequence[str],
    rule_pack_digest: str,
) -> dict[str, Any]:
    """Validate the expected-only template and bind its cases to immutable inputs."""

    if template.get("schema_version") != TEMPLATE_SCHEMA:
        raise ValueError("unsupported expected-template schema")
    if template.get("status") != TEMPLATE_STATUS:
        raise ValueError("template must remain expected-only")
    if set(template) != {
        "schema_version",
        "status",
        "semantics",
        "cases",
        "limitations",
    }:
        raise ValueError("template fields do not match the v2 contract")

    semantics = template.get("semantics")
    cases = template.get("cases")
    limitations = template.get("limitations")
    if not isinstance(semantics, Mapping) or set(semantics) != {"id", "version"}:
        raise ValueError("template semantics are malformed")
    if not isinstance(cases, list) or not cases:
        raise ValueError("template requires at least one expected case")
    if (
        not isinstance(limitations, list)
        or not limitations
        or any(not isinstance(item, str) or not item for item in limitations)
    ):
        raise ValueError("template limitations are malformed")

    return build_expected_fixture(
        lmm_commit=lmm_commit,
        fixture_cases=cases,
        source_snapshot_digests=source_snapshot_digests,
        rule_pack_digest=rule_pack_digest,
        semantics_id=str(semantics.get("id", "")),
        semantics_version=str(semantics.get("version", "")),
    )


def _git(repo_root: Path, *args: str) -> str:
    completed = subprocess.run(
        ["git", "-C", str(repo_root), *args],
        check=True,
        capture_output=True,
        text=True,
        encoding="utf-8",
    )
    return completed.stdout.strip()


def _current_clean_commit(repo_root: Path) -> str:
    tracked_status = _git(repo_root, "status", "--porcelain", "--untracked-files=no")
    if tracked_status:
        raise RuntimeError("tracked LMM files are dirty")
    return _git(repo_root, "rev-parse", "HEAD")


def _write_json_atomic(path: Path, value: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary_name: str | None = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="w",
            encoding="utf-8",
            newline="\n",
            dir=path.parent,
            prefix=f".{path.name}.",
            suffix=".tmp",
            delete=False,
        ) as temporary:
            json.dump(value, temporary, ensure_ascii=False, indent=2)
            temporary.write("\n")
            temporary_name = temporary.name
        os.replace(temporary_name, path)
    finally:
        if temporary_name is not None:
            Path(temporary_name).unlink(missing_ok=True)


def _parser() -> argparse.ArgumentParser:
    root = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--template",
        default=root / "runtime" / "refinement_cases" / "four_slice_expected.template.json",
    )
    parser.add_argument("--source-digest", action="append", required=True)
    parser.add_argument("--rule-pack-digest", required=True)
    parser.add_argument("--output", required=True)
    parser.add_argument("--repo-root", default=root)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    repo_root = Path(args.repo_root).resolve()
    template = json.loads(Path(args.template).read_text(encoding="utf-8"))
    expected = materialize_expected_fixture(
        template,
        lmm_commit=_current_clean_commit(repo_root),
        source_snapshot_digests=tuple(args.source_digest),
        rule_pack_digest=args.rule_pack_digest,
    )
    output = Path(args.output).resolve()
    _write_json_atomic(output, expected)
    print(
        json.dumps(
            {
                "status": "PASS",
                "output": str(output),
                "lmm_commit": expected["lmm_commit"],
                "fixture_digest": expected["fixture_digest"],
                "case_count": len(expected["cases"]),
            },
            ensure_ascii=False,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
