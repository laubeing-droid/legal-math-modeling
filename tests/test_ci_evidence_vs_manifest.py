"""Reconcile the CI-issued release certificate with the repository's own account.

A landed certificate (docs/formal-release/ci-evidence/<run>/) is GitHub Actions
speaking: it enumerates the Lean sources the release job took inventory of, their
SHA-256 as CI computed them, and the theorem declarations it saw in each. The
repository separately claims scope counts from `theorem_inventory_v3.json`. Those two
accounts had never been put in the same room, which is how "the package lake build
compiles" came to be written about a 217-file scope while the certificate for the same
commit named 96 files and 506 declarations.

These tests check CI's own numbers against git, without compiling anything:
the certificate's hashes must equal the committed bytes at the certificate's subject,
and every declaration it lists must really be in that blob.
"""

from __future__ import annotations

import glob
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
EVIDENCE = ROOT / "docs" / "formal-release" / "ci-evidence"


def certificates() -> list[dict]:
    out = []
    for path in sorted(glob.glob(str(EVIDENCE / "*" / "*" / "formal-release-certificate.json"))):
        doc = json.loads(Path(path).read_text(encoding="utf-8"))
        doc["_rel"] = str(Path(path).relative_to(ROOT)).replace("\\", "/")
        out.append(doc)
    assert out, "no release certificate has been landed yet"
    return out


def _git_show(subject: str, rel: str) -> bytes | None:
    """Raw committed bytes -- the certificate's hash contract is over those, not over
    a decoded-and-re-encoded copy."""

    proc = subprocess.run(
        ["git", "show", f"{subject}:{rel}"],
        cwd=ROOT, capture_output=True,
    )
    return None if proc.returncode else proc.stdout


def test_certificate_internal_arithmetic_adds_up() -> None:
    for cert in certificates():
        src = cert["source_inventory"]["sources"]
        assert cert["source_inventory"]["lean_source_file_count"] == len(src), cert["_rel"]
        assert cert["source_inventory"]["theorem_declaration_count"] == sum(
            len(f["theorems"]) for f in src
        ), cert["_rel"]


def test_certificate_hashes_match_the_committed_bytes() -> None:
    """CI's SHA-256 must equal the hash of the bytes at CI's own subject commit."""

    bad = []
    for cert in certificates():
        subject = cert["subject"]["sha"]
        for f in cert["source_inventory"]["sources"]:
            blob = _git_show(subject, f["path"])
            if blob is None:
                bad.append(f"{f['path']}: not in {subject[:7]}")
                continue
            local = hashlib.sha256(blob).hexdigest()
            if local != f["sha256"]:
                bad.append(f"{f['path']}: cert {f['sha256'][:12]} vs git {local[:12]}")
        assert not bad, f"certificate disagrees with git: {bad[:4]}"
        bad = []


def test_certificate_declarations_are_really_in_those_blobs() -> None:
    bad = []
    for cert in certificates():
        subject = cert["subject"]["sha"]
        for f in cert["source_inventory"]["sources"]:
            blob = _git_show(subject, f["path"])
            if blob is None:
                continue
            for thm in f["theorems"]:
                if b"theorem " + thm["name"].encode("utf-8") not in blob:
                    bad.append(f"{f['path']}:{thm['name']}")
        assert not bad, f"certificate lists declarations git cannot find: {bad[:4]}"
        bad = []


def test_certificate_states_its_own_limits() -> None:
    for cert in certificates():
        joined = " ".join(cert["limitations"]).lower()
        assert "not a lean build" in joined or "github actions" in joined, cert["_rel"]
        assert cert["status"].startswith("RELEASE_"), cert["status"]


def test_the_ci_certified_scope_is_smaller_than_the_declared_package_scope() -> None:
    """The point of landing the certificate: scope honesty, in digits.

    The certificate at the audited subject names 96 files / 506 declarations, while
    the manifest's `juris_lean_package` scope counts hundreds more. If the two ever
    converge, this assertion is the place that has to be re-read, not a footnote.
    """

    inv = json.loads(
        (ROOT / "docs/formal-release/theorem_inventory_v3.json").read_text(encoding="utf-8")
    )
    by_path = {f["path"]: f for f in inv["files"]}
    package_theorems = sum(
        by_path[p]["theorem_count"] for p in inv["scopes"]["juris_lean_package"]
    )
    for cert in certificates():
        certified = cert["source_inventory"]["theorem_declaration_count"]
        assert certified < package_theorems, (
            f"{cert['_rel']} certifies {certified} of {package_theorems}: "
            "the scopes now coincide, re-check what each one means before citing either"
        )
