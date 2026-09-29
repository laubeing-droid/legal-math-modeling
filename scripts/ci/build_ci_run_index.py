#!/usr/bin/env python3
"""Build the in-repo index of GitHub Actions runs that the repository quotes.

Why this exists (Qoder audit P2-26): repo markdown names a batch of run ids as
evidence for build, axiom-audit and certificate claims, but nothing in the repo
recorded what those runs actually were. Verifying a quoted "CI 全绿" therefore
required an outside `gh` session, which is exactly the "third parties cannot
re-check the claim" failure the audit named. This script snapshots, per run, the
fields that make the quote checkable -- subject commit, branch, trigger event,
conclusion, every job's conclusion, artifact count -- next to the file and line
that quote it, and emits the same account as JSON and as a markdown table.

This is a metadata snapshot read from GitHub Actions. It is not a release
certificate and does not make any Lean claim: the conclusion recorded here is
what Actions reported for that run, and `--check` re-reads it to catch drift.

    python scripts/ci/build_ci_run_index.py            # write both files
    python scripts/ci/build_ci_run_index.py --check     # fail if stale/incomplete
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
JSON_OUT = ROOT / "docs" / "formal-release" / "ci_run_index.json"
MD_OUT = ROOT / "docs" / "formal-release" / "ci_run_index.md"
REPO = "laubeing-droid/legal-math-modeling"
RUN_ID_RE = re.compile(r"\b\d{11}\b")
SCHEMA = "ci-run-index-v1"
STATUS = "external_actions_metadata_snapshot_not_release_certificate"
AUTHORITY = (
    "Read from the GitHub Actions API by scripts/ci/build_ci_run_index.py. Records "
    "what Actions reported for each run the repository quotes; it does not re-run "
    "Lean, does not certify any theorem, and does not survive a force-push or a "
    "deleted run -- re-derive it rather than trusting a stale copy."
)


def run_ids_in_markdown() -> dict[str, list[str]]:
    """Every 11-digit run id quoted in tracked markdown, with its locations.

    The generated index and evidence accounts are excluded: they name the ids they
    are cataloguing, so scanning them would let the index vouch for itself and every
    non-success run would look "named as red" by its own table row.
    """

    listing = subprocess.run(
        ["git", "ls-files", "-z", "*.md"],
        cwd=ROOT, capture_output=True, text=True, encoding="utf-8", check=True,
    )
    generated = {MD_OUT.relative_to(ROOT).as_posix()}
    if EVIDENCE_ROOT.exists():
        generated |= {p.relative_to(ROOT).as_posix() for p in EVIDENCE_ROOT.rglob("*.md")}
    found: dict[str, list[str]] = {}
    for rel in filter(None, listing.stdout.split("\0")):
        if rel in generated:
            continue
        path = ROOT / rel
        try:
            text = path.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            continue
        for n, line in enumerate(text.splitlines(), 1):
            for rid in set(RUN_ID_RE.findall(line)):
                found.setdefault(rid, []).append(f"{rel}:{n}")
    return found


def gh_api(path: str) -> dict:
    proc = subprocess.run(
        ["gh", "api", path], cwd=ROOT, capture_output=True, text=True, encoding="utf-8"
    )
    if proc.returncode != 0:
        raise RuntimeError(f"gh api {path} failed: {proc.stderr.strip()[:200]}")
    return json.loads(proc.stdout)


def describe(rid: str, quoted: list[str]) -> dict:
    run = gh_api(f"repos/{REPO}/actions/runs/{rid}")
    jobs = gh_api(f"repos/{REPO}/actions/runs/{rid}/jobs?per_page=100").get("jobs", [])
    artifacts = gh_api(f"repos/{REPO}/actions/runs/{rid}/artifacts?per_page=100")
    return {
        "run_id": int(rid),
        "quoted_by": sorted(quoted),
        "workflow": run.get("name"),
        "name": run.get("display_title"),
        "head_sha": run.get("head_sha"),
        "head_branch": run.get("head_branch"),
        "event": run.get("event"),
        "status": run.get("status"),
        "conclusion": run.get("conclusion"),
        "created_at": run.get("created_at"),
        "updated_at": run.get("updated_at"),
        "html_url": run.get("html_url"),
        "jobs_total": len(jobs),
        # `jobs == []` means two different things: never scheduled (the workflow file
        # itself failed) versus scheduled and still running. Say which, from the API.
        "started": bool(jobs) or run.get("status") != "completed",
        "jobs": [
            {"name": j.get("name"), "status": j.get("status"),
             "conclusion": j.get("conclusion")}
            for j in jobs
        ],
        "artifacts_total": artifacts.get("total_count"),
        "evidence": evidence_index(rid),
    }


EVIDENCE_ROOT = ROOT / "docs" / "formal-release" / "ci-evidence"
EVIDENCE_MAX_BYTES = 100_000
EVIDENCE_ARTIFACTS = (
    "release-certificate-", "seven-axis-gate-", "full-math-completion-", "runtime-refinement-",
)
EVIDENCE_SKIP_SUFFIX = (".log",)
EVIDENCE_SCHEMA = "ci-run-evidence-v1"
EVIDENCE_NOTE = (
    "Bytes downloaded from the GitHub Actions artifact store for this run, digested on "
    "arrival. Only the report artifacts a claim is actually cited from land here "
    "(certificate, gate, completion, refinement); build and test logs stay outside. A "
    "digest proves this repository's copy has not been edited since download -- it does "
    "not re-derive the result, which would mean re-running Lean."
)


AUDIT_LOG_ARTIFACT_PREFIX = "lean-full-build-run"
AUDIT_LOG_NAME = "axiom-audit.raw.txt"


def land_audit_log(rid: str, artifacts: list[dict], dest: Path) -> None:
    """Land the kernel's axiom-audit output, which is otherwise too big to fetch.

    The build artifact holding `axiom-audit.raw.txt` also holds a multi-megabyte
    compile log, so it fails the size filter that keeps the evidence directory small.
    This takes just the audit file: it is the only artefact that says what the theorems
    rest on, and without it "no sorryAx" is a claim about a log nobody can re-read.
    """
    hit = next(
        (a for a in artifacts
         if not a.get("expired") and str(a.get("name", "")).startswith(AUDIT_LOG_ARTIFACT_PREFIX)),
        None,
    )
    if hit is None:
        return
    staging = dest / "_build-artifact"
    proc = subprocess.run(
        ["gh", "run", "download", rid, "-n", hit["name"], "-D", str(staging)],
        cwd=ROOT, capture_output=True, text=True, encoding="utf-8",
    )
    if proc.returncode != 0:
        raise RuntimeError(f"gh run download {rid} {hit['name']}: {proc.stderr.strip()[:200]}")
    found = next((f for f in staging.rglob(AUDIT_LOG_NAME)), None)
    if found is None:
        shutil.rmtree(staging, ignore_errors=True)
        return
    out = dest / "axiom-audit"
    out.mkdir(exist_ok=True)
    shutil.copyfile(found, out / AUDIT_LOG_NAME)
    shutil.rmtree(staging, ignore_errors=True)


def evidence_dir(rid: str) -> Path:
    return EVIDENCE_ROOT / rid


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def fetch_evidence(rid: str) -> dict:
    """Download the small decisive artifacts of one run and digest what landed."""

    artifacts = gh_api(f"repos/{REPO}/actions/runs/{rid}/artifacts?per_page=100")["artifacts"]
    picked = [
        a for a in artifacts
        if not a.get("expired")
        and str(a.get("name", "")).startswith(EVIDENCE_ARTIFACTS)
        and a.get("size_in_bytes", 1 << 30) <= EVIDENCE_MAX_BYTES
    ]
    if not picked:
        raise RuntimeError(
            f"run {rid}: no report artifact matched {EVIDENCE_ARTIFACTS} "
            f"under {EVIDENCE_MAX_BYTES} bytes"
        )
    skipped = sorted(
        str(a.get("name")) for a in artifacts if a not in picked
    )
    dest = evidence_dir(rid)
    if dest.exists():
        shutil.rmtree(dest)
    dest.mkdir(parents=True)
    for a in picked:
        proc = subprocess.run(
            ["gh", "run", "download", rid, "-n", a["name"], "-D", str(dest / a["name"])],
            cwd=ROOT, capture_output=True, text=True, encoding="utf-8",
        )
        if proc.returncode != 0:
            raise RuntimeError(f"gh run download {rid} {a['name']}: {proc.stderr.strip()[:200]}")
    land_audit_log(rid, artifacts, dest)

    for p in sorted(dest.rglob("*")):
        if p.is_file() and p.name.endswith(EVIDENCE_SKIP_SUFFIX):
            p.unlink()
    files = [
        {
            "path": p.relative_to(dest).as_posix(),
            "artifact": p.relative_to(dest).parts[0],
            "sha256": _sha256(p),
            "bytes": p.stat().st_size,
        }
        for p in sorted(dest.rglob("*"))
        if p.is_file()
        and p.name != "digests.json"
        and not p.name.endswith(EVIDENCE_SKIP_SUFFIX)
    ]
    doc = {
        "schema_version": EVIDENCE_SCHEMA,
        "run_id": int(rid),
        "authority_note": EVIDENCE_NOTE,
        "source": f"https://github.com/{REPO}/actions/runs/{rid}",
        "artifacts_landed": sorted(str(a["name"]) for a in picked),
        "artifacts_not_landed": skipped,
        "files": files,
    }
    (dest / "digests.json").write_text(
        json.dumps(doc, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8", newline="\n",
    )
    return doc


def verify_evidence(doc: dict) -> list[str]:
    """Recompute the digests of a landed evidence record; return mismatches."""

    dest = evidence_dir(str(doc["run_id"]))
    problems = []
    for f in doc["files"]:
        path = dest / f["path"]
        if not path.exists():
            problems.append(f"missing {f['path']}")
        elif _sha256(path) != f["sha256"]:
            problems.append(f"digest mismatch {f['path']}")
    return problems


def evidence_index(rid: str) -> str | None:
    sidecar = evidence_dir(rid) / "digests.json"
    return f"docs/formal-release/ci-evidence/{rid}/digests.json" if sidecar.exists() else None


def build(ids: dict[str, list[str]]) -> dict:
    return {
        "schema_version": SCHEMA,
        "status": STATUS,
        "authority_note": AUTHORITY,
        "repository": REPO,
        "verify_command": "python scripts/ci/build_ci_run_index.py --check",
        "quote_scan": "git ls-files -z '*.md' | xargs -0 grep -ohE '\\b[0-9]{11}\\b' | sort -u",
        "runs": [describe(rid, quoted) for rid, quoted in sorted(ids.items())],
    }


def render_markdown(doc: dict) -> str:
    lines = [
        "# CI run index (generated)",
        "",
        f"`{doc['schema_version']}` — generated by `{Path(__file__).name}`; "
        f"status `{doc['status']}`.",
        "",
        doc["authority_note"],
        "",
        "Run ids below are the ones this repository's markdown quotes. `quoted_by`",
        "gives file:line, so a claim of the form \"CI run N is green\" can be opened",
        "without guessing where it came from.",
        "",
        "| run | conclusion | head sha | branch | event | jobs ok/total | artifacts | quoted in |",
        "|---|---|---|---|---|---|---|---|",
    ]
    for r in doc["runs"]:
        sha = (r["head_sha"] or "")[:7]
        files = ", ".join(sorted({q.split(":")[0].split("/")[-1] for q in r["quoted_by"]}))
        ok = sum(1 for j in r["jobs"] if j["conclusion"] == "success")
        lines.append(
            f"| {r['run_id']} | {r['conclusion']} | `{sha}` | {r['head_branch']} "
            f"| {r['event']} | {ok}/{len(r['jobs'])} | {r['artifacts_total']} | {files} |"
        )
    failed = [r["run_id"] for r in doc["runs"] if r["conclusion"] not in ("success",)]
    lines += [
        "",
        f"Runs not concluding `success`: {len(failed)}"
        + (f" — {', '.join(str(f) for f in failed)}." if failed else "."),
        "",
        "`jobs ok/total` is there because a run-level conclusion and a job-level one",
        "differ: a run can end `cancelled` while every job a document names succeeded,",
        "and a document may legitimately quote the jobs. Read the per-job list in the",
        "JSON before repeating any \"that run was green\" claim.",
        "",
    ]
    landed = [r for r in doc["runs"] if r.get("evidence")]
    if landed:
        lines += ["", "## Artifact bytes landed in this repository", ""]
        for r in landed:
            side = ROOT / r["evidence"]
            rec = json.loads(side.read_text(encoding="utf-8")) if side.exists() else {"files": []}
            lines.append(
                f"- run {r['run_id']}: {len(rec['files'])} files, "
                f"{sum(f['bytes'] for f in rec['files'])} bytes, digests in "
                f"`{r['evidence']}`"
            )
        lines += [
            "",
            "Land another run's bytes with `--fetch-evidence <run>`; `--check` "
            "recomputes every digest in every `digests.json` and fails if a landed "
            "set no longer matches, or belongs to a run nothing quotes.",
            "",
        ]
    lines += [
        "Regenerate: `python scripts/ci/build_ci_run_index.py`. "
        "Check without writing: `--check`.",
        "",
    ]
    return "\n".join(lines)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--check", action="store_true", help="fail if quoted ids are missing from the committed index")
    ap.add_argument("--index", default=str(JSON_OUT), help="index file to check (default: the committed one)")
    ap.add_argument(
        "--quotes-only",
        action="store_true",
        help="refresh only the quoted_by locations from the markdown, reusing the "
             "cached Actions metadata (docs move; runs do not)",
    )
    ap.add_argument(
        "--fetch-evidence",
        metavar="RUN_ID",
        help="download this run's small artifacts under docs/formal-release/ci-evidence/ and digest them",
    )
    args = ap.parse_args()

    if args.fetch_evidence:
        doc = fetch_evidence(args.fetch_evidence)
        print(f"run {doc['run_id']}: landed {len(doc['files'])} files, "
              f"{sum(f['bytes'] for f in doc['files'])} bytes under "
              f"{evidence_dir(args.fetch_evidence).relative_to(ROOT)}")
        return 0

    ids = run_ids_in_markdown()
    index_path = Path(args.index)
    if args.check:
        if not index_path.exists():
            print(f"MISSING {index_path.relative_to(ROOT) if index_path.is_relative_to(ROOT) else index_path}", file=sys.stderr)
            return 1
        committed = json.loads(index_path.read_text(encoding="utf-8"))
        recorded = {str(r["run_id"]) for r in committed["runs"]}
        orphans = sorted(set(ids) - recorded)
        if orphans:
            print(f"stale index: quoted run ids not in the index: {orphans}", file=sys.stderr)
            return 1
        extra = sorted(recorded - set(ids))
        if extra:
            print(f"index lists runs no markdown quotes any more: {extra}", file=sys.stderr)
            return 1
        for r in committed["runs"]:
            # A run whose workflow file failed to parse has no jobs at all; that is a
            # complete record, not a missing one, provided `started` says so and the
            # job list is empty rather than uncollected.
            if r.get("started") is False:
                if r.get("jobs"):
                    print(f"run {r['run_id']} marked not started but lists jobs",
                          file=sys.stderr)
                    return 1
                continue
            if not (r.get("head_sha") and r.get("jobs") and r.get("conclusion")):
                print(f"incomplete record for run {r['run_id']}", file=sys.stderr)
                return 1
        for sidecar in sorted(EVIDENCE_ROOT.glob("*/digests.json")) if EVIDENCE_ROOT.exists() else []:
            landed = json.loads(sidecar.read_text(encoding="utf-8"))
            problems = verify_evidence(landed)
            if problems:
                print(f"evidence for run {landed['run_id']} does not match its digests: {problems}",
                      file=sys.stderr)
                return 1
            if str(landed["run_id"]) not in recorded:
                print(f"evidence landed for run {landed['run_id']}, which markdown no longer quotes",
                      file=sys.stderr)
                return 1
        # The markdown table is generated from this JSON, and nothing above reads
        # it: a tampered or stale table passed every check while telling a reader
        # something else. Rendering the committed JSON is byte-stable, so the
        # committed pair must match -- but only when checking the committed index,
        # since --index may point at a scratch copy on purpose.
        if index_path.resolve() == JSON_OUT.resolve():
            if not MD_OUT.exists() or MD_OUT.read_text(encoding="utf-8") != render_markdown(committed):
                print(f"stale markdown index: {MD_OUT.name} does not match the JSON; "
                      "regenerate with build_ci_run_index.py", file=sys.stderr)
                return 1
        print(f"ci run index ok: {len(recorded)} runs, {sum(len(v) for v in ids.values())} quotes")
        return 0

    if args.quotes_only:
        cached = json.loads(JSON_OUT.read_text(encoding="utf-8"))
        known = {str(r["run_id"]): r for r in cached["runs"]}
        missing = sorted(set(ids) - set(known))
        if missing:
            print(
                f"--quotes-only cannot invent metadata for newly quoted runs: {missing}; "
                "run without the flag to fetch them",
                file=sys.stderr,
            )
            return 2
        doc = dict(cached)
        doc["runs"] = [
            {
                **known[rid],
                "quoted_by": sorted(q),
                "evidence": evidence_index(rid),
            }
            for rid, q in sorted(ids.items())
        ]
    else:
        doc = build(ids)
    JSON_OUT.parent.mkdir(parents=True, exist_ok=True)
    JSON_OUT.write_text(
        json.dumps(doc, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8", newline="\n",
    )
    MD_OUT.write_text(render_markdown(doc), encoding="utf-8", newline="\n")
    print(f"wrote {JSON_OUT.relative_to(ROOT)} and {MD_OUT.relative_to(ROOT)} "
          f"({len(doc['runs'])} runs, {sum(len(r['quoted_by']) for r in doc['runs'])} quotes)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
