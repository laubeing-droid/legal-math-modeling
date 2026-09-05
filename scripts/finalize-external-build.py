#!/usr/bin/env python3
"""Compatibility entrypoint for independent formal release verification."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Sequence

from verify_formal_release_certificate import verify_certificate


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate")
    parser.add_argument("--repo-root", default=None)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    certificate_path = Path(args.certificate).resolve()
    repo_root = (
        Path(args.repo_root).resolve()
        if args.repo_root
        else Path(__file__).resolve().parents[1]
    )
    document = json.loads(certificate_path.read_text(encoding="utf-8"))
    report = verify_certificate(
        document,
        repo_root,
        certificate_path.parent,
        require_current_head=True,
    )
    print(json.dumps(report, ensure_ascii=False, indent=2))
    return 0 if report["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
