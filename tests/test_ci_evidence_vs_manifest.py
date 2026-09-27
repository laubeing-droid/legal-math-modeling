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
        rel = str(Path(path).relative_to(ROOT)).replace("\\", "/")
        doc["_rel"] = rel
        doc["_run_id"] = re.search(r"ci-evidence/(\d+)/", rel).group(1)
        out.append(doc)
    assert out, "no release certificate has been landed yet"
    return out


def run_id_of(cert: dict) -> str:
    return cert["_run_id"]


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


def test_landed_bytes_are_still_landed_bytes_in_git() -> None:
    """Check what the commit stores, not what this working tree happens to show.

    The repository's `* text=auto` rule rewrote every landed file on a fresh
    checkout, which silently invalidated all 34 digests: the evidence was only
    byte-exact on the machine that downloaded it. `ci-evidence/** -text` in
    .gitattributes is what keeps it true, and this is the gate that notices if that
    line is ever dropped.
    """

    problems = []
    for sidecar in sorted((EVIDENCE / "digests.json").parent.glob("*/digests.json")):
        doc = json.loads(sidecar.read_text(encoding="utf-8"))
        for f in doc["files"]:
            rel = f"{EVIDENCE.relative_to(ROOT).as_posix()}/{doc['run_id']}/{f['path']}"
            proc = subprocess.run(
                ["git", "show", f"HEAD:{rel}"], cwd=ROOT, capture_output=True
            )
            if proc.returncode:
                problems.append(f"{rel}: not committed at HEAD")
            elif hashlib.sha256(proc.stdout).hexdigest() != f["sha256"]:
                problems.append(f"{rel}: committed bytes differ from the digest")
    assert not problems, f"landed CI evidence is not byte-exact in git: {problems[:3]}"


def test_certificate_states_its_own_limits() -> None:
    for cert in certificates():
        joined = " ".join(cert["limitations"]).lower()
        assert "not a lean build" in joined or "github actions" in joined, cert["_rel"]
        assert cert["status"].startswith("RELEASE_"), cert["status"]


def _package_paths_at(subject: str) -> set[str]:
    """Every `JurisLean/**/*.lean` path in a commit -- one `ls-tree`, no compiling."""

    proc = subprocess.run(
        ["git", "ls-tree", "-r", "--name-only", subject, "--",
         "proofs/lean/juris_lean/JurisLean"],
        cwd=ROOT, capture_output=True, text=True, encoding="utf-8",
    )
    assert proc.returncode == 0, proc.stderr[:200]
    return {line for line in proc.stdout.splitlines() if line.endswith(".lean")}


def test_the_ci_certified_scope_covers_the_recursive_package_scope() -> None:
    """The certificate must name the tree it claims to inventory.

    The two certificates from the audited commits list 96 files where their own
    subjects contained 202 -- the generator walked `JurisLean/*.lean`
    non-recursively, and the papers drew scope conclusions from a count that
    silently meant something narrower. That omission is pinned by run id rather than
    inferred from "older", because once the fix landed later certificates
    legitimately list all 217 files. Each certificate is checked against *its own*
    subject, so the gate does not go red merely because HEAD moved past it.
    """

    audited_era = {"36258179200", "36259479766"}
    newest_run = run_id_of(max(certificates(), key=lambda c: int(run_id_of(c))))
    for cert in certificates():
        sources = cert["source_inventory"]["sources"]
        listed = {e["path"] for e in sources}
        assert len(listed) == len(sources), f"{cert['_rel']} lists a path twice"
        assert cert["source_inventory"]["lean_source_file_count"] == len(listed), (
            f"{cert['_rel']} counts {cert['source_inventory']['lean_source_file_count']} "
            f"files while enumerating {len(listed)}"
        )
        counted = sum(len(e["theorems"]) for e in sources)
        declared = cert["source_inventory"]["theorem_declaration_count"]
        assert declared == counted, f"{cert['_rel']} totals {declared} but lists {counted}"

        actual = _package_paths_at(cert["subject"]["sha"])
        assert not (listed - actual), (
            f"{cert['_rel']} names files its own subject does not contain"
        )
        missing = sorted(actual - listed)
        if run_id_of(cert) == newest_run:
            assert not missing, (
                f"the newest certificate still omits {len(missing)} package files, "
                f"starting {missing[:3]}"
            )
        elif run_id_of(cert) in audited_era:
            assert missing, (
                f"{cert['_rel']} is the evidence for the non-recursive walk; if it now "
                "lists everything, the audited-era record has been rewritten"
            )
            assert len(listed) < len(actual)
