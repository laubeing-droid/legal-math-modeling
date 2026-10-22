"""Bind the 50 frozen clause rows to declarations the tip Lean build actually compiled.

A numeric ``formal_ci`` is the run id stored in the tip receipt. It means the
module that contains the listed declaration was built by that run's
``lean-full-clean-build``. It is not an acceptance discharge, and this checker
rejects the token PASS on the clause label, the candidate label, and the
remaining-obligations text.

The checker does not re-download the job log and does not re-run Lean. It
checks the receipt against ``git show <subject>:<path>`` and against the
working tree, then checks that each listed name is a real declaration in that
source with no forbidden shell proof.
"""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path
from urllib.parse import urlparse

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "scripts"))

from lean_grammar import strip_comments  # noqa: E402

CANDIDATE = Path(
    "proofs/lean/juris_lean/JurisLean/Candidates/Final20261021"
)
STATUS_REL = CANDIDATE / "50_clause_status.json"
RECEIPT_REL = CANDIDATE / "evidence" / "ci-tip-304d428c" / "verification.json"
PRIOR_REL = CANDIDATE / "evidence" / "ci-stage1-d59a487" / "verification.json"
LEGAL_REL = CANDIDATE / "evidence" / "seven_clause_legal_sources.txt"

RECEIPT_STATUS = (
    "TIP_LEAN_BUILD_LOCATED_DECLARATIONS_ACCEPTANCE_NOT_DISCHARGED"
)
CANDIDATE_LABEL = "LISTED_DECLARATIONS_IN_TIP_BUILD"
MODULE_PREFIX = "JurisLean.Candidates.Final20261021"
SEVEN = ("U01.4", "U02.4", "U04.1", "U04.3", "U04.4", "U05.1", "U06.5")
OFFICIAL_HOSTS = {"flk.npc.gov.cn", "www.flk.npc.gov.cn", "npc.gov.cn", "www.npc.gov.cn"}

BOUNDARY = re.compile(
    r"^(?:@\[[^\]]*\][ \t]*)*"
    r"(axiom|theorem|lemma|def|abbrev|structure|inductive|class|opaque|macro)"
    r"\s+([^\s(:{=\[]+)"
)
BANNED = (
    ("sorry tactic", re.compile(r"\bsorry\b")),
    ("admit tactic", re.compile(r"\badmit\b")),
    ("native_decide tactic", re.compile(r"\bnative_decide\b")),
    ("axiom declaration", re.compile(r"^axiom\b")),
    ("theorem-of-True evasion", re.compile(r":\s*True\s*:=")),
)
PASS_TOKEN = re.compile(r"\bPASS\b")


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_show_bytes(subject: str, rel: str) -> bytes:
    proc = subprocess.run(
        ["git", "show", f"{subject}:{rel}"],
        cwd=ROOT,
        capture_output=True,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"git show {subject}:{rel} failed: {proc.stderr.decode()[:200]}"
        )
    return proc.stdout


def declaration_index(text: str) -> list[tuple[int, str, str]]:
    """Return (1-based line, kind, name) for each top-level declaration."""

    starts: list[tuple[int, str, str]] = []
    depth = 0
    for lineno, raw in enumerate(text.splitlines(), start=1):
        code, depth = strip_comments(raw, depth)
        match = BOUNDARY.match(code.strip())
        if match:
            starts.append((lineno, match.group(1), match.group(2)))
    return starts


def body_violations(text: str, short: str) -> list[str]:
    starts = declaration_index(text)
    hits = [item for item in starts if item[2] == short]
    if not hits:
        return [f"missing declaration {short}"]
    if len(hits) != 1:
        return [f"declaration {short} occurs {len(hits)} times"]
    start_line = hits[0][0]
    later = [item[0] for item in starts if item[0] > start_line]
    end = (later[0] - 1) if later else len(text.splitlines())
    violations: list[str] = []
    depth = 0
    for lineno, raw in enumerate(text.splitlines(), start=1):
        code, depth = strip_comments(raw, depth)
        if not (start_line <= lineno <= end) or not code.strip():
            continue
        for label, pattern in BANNED:
            if pattern.search(code.strip()):
                violations.append(f"{short}:{lineno}: {label}")
    return violations


def iter_named(node: object, acc: list[tuple[str, str]]) -> None:
    if isinstance(node, dict):
        if "name" in node and "file" in node:
            acc.append((str(node["name"]), str(node["file"])))
        for value in node.values():
            iter_named(value, acc)
    elif isinstance(node, list):
        for value in node:
            iter_named(value, acc)


def legal_line_errors(line: str, expected_id: str | None = None) -> list[str]:
    """One archivist row. A missing column forces the row to be marked 待核."""

    errors: list[str] = []
    cells = [cell.strip() for cell in line.split("｜")]
    if expected_id is not None and (not cells or cells[0] != expected_id):
        errors.append(f"legal row does not start with {expected_id}: {line}")
        return errors
    clause_id = cells[0] if cells else ""
    rest = cells[1:]
    marked = "待核" in line
    complete = len(cells) == 6 and all(cells) and not marked
    if not complete and not marked:
        errors.append(f"{clause_id}: missing column without 待核")
        return errors
    if marked:
        if len(cells) != 6 or any(cell != "待核" for cell in rest):
            errors.append(f"{clause_id}: 待核 row also fills another column")
        if "://" in line or "http" in line.lower():
            errors.append(f"{clause_id}: 待核 row also contains a URL")
        return errors
    url = cells[4]
    host = (urlparse(url).hostname or "").lower()
    if host not in OFFICIAL_HOSTS:
        errors.append(f"{clause_id}: unofficial URL host {host or url}")
    return errors


def check_legal_text(text: str) -> list[str]:
    rows = []
    for raw in text.splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        rows.append(line)
    errors: list[str] = []
    ids = [line.split("｜", 1)[0].strip() for line in rows]
    if ids != list(SEVEN):
        errors.append(f"legal rows {ids} != {list(SEVEN)}")
    for line, clause_id in zip(rows, ids):
        errors.extend(legal_line_errors(line, clause_id))
    return errors


def check() -> tuple[list[str], dict[str, int]]:
    errors: list[str] = []
    counts = {
        "clauses": 0,
        "formal_ci_run_id": 0,
        "formal_ci_CI_NOT_RUN": 0,
        "declarations_located": 0,
        "remaining_obligations_nonempty": 0,
        "legal_rows_daihe": 0,
    }
    status_path = ROOT / STATUS_REL
    receipt_path = ROOT / RECEIPT_REL
    prior_path = ROOT / PRIOR_REL
    legal_path = ROOT / LEGAL_REL
    status = json.loads(status_path.read_text(encoding="utf-8"))
    receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
    prior = json.loads(prior_path.read_text(encoding="utf-8"))

    if receipt.get("status") != RECEIPT_STATUS:
        errors.append(f"receipt status {receipt.get('status')!r}")
    if receipt.get("does_not_discharge_exact_scope") is not True:
        errors.append("receipt does not keep does_not_discharge_exact_scope")
    if receipt.get("artifact_zip_sha256") != "NOT_RECOMPUTED_ARTIFACT_NOT_DOWNLOADED":
        errors.append("receipt claims an artifact zip sha256")
    if receipt.get("axiom_audit") != "NOT_REEXTRACTED_FROM_ARTIFACT":
        errors.append("receipt claims a re-extracted axiom audit")
    subject = str(receipt.get("subject_commit") or "")
    if not re.fullmatch(r"[0-9a-f]{40}", subject):
        errors.append(f"receipt subject is not a commit: {subject}")
    run_id = receipt.get("run_id")
    if not isinstance(run_id, int):
        errors.append("receipt run_id is not an int")
        return errors, counts
    scope = str(status.get("formal_ci_field_scope") or "")
    if "does not discharge" not in scope or "CI_NOT_RUN" not in scope:
        errors.append("formal_ci_field_scope does not keep the non-discharge sentence")

    lean_files = sorted((ROOT / CANDIDATE).glob("*.lean"))
    expected_paths = [p.relative_to(ROOT).as_posix() for p in lean_files]
    hashed = {item["path"]: item["sha256"] for item in receipt.get("source_hashes", [])}
    if sorted(hashed) != expected_paths:
        errors.append("receipt source_hashes do not match the candidate lean files")
    modules_built = set(receipt.get("modules_built") or [])
    expected_modules = {f"{MODULE_PREFIX}.{path.stem}" for path in lean_files}
    if modules_built != expected_modules:
        errors.append("receipt modules_built does not match the candidate lean files")

    prior_hashed = {item["path"]: item["sha256"] for item in prior.get("source_hashes", [])}
    changed = set(receipt.get("files_changed_since_d59a487") or [])
    for path, old_hash in prior_hashed.items():
        new_hash = hashed.get(path)
        if new_hash is None:
            errors.append(f"tip receipt dropped {path}")
            continue
        if old_hash == new_hash and path in changed:
            errors.append(f"{path} is listed as changed but the hash matches d59a487")
        if old_hash != new_hash and path not in changed:
            errors.append(f"{path} differs from d59a487 but is not listed as changed")

    for path, digest in hashed.items():
        try:
            committed = git_show_bytes(subject, path)
        except RuntimeError as exc:
            errors.append(str(exc))
            continue
        if sha256_bytes(committed) != digest:
            errors.append(f"{path} hash != git show {subject}")
        working = (ROOT / path).read_bytes()
        if sha256_bytes(working) != digest:
            errors.append(f"{path} working tree != receipt hash")

    rows = status.get("rows")
    if not isinstance(rows, list) or len(rows) != 50:
        errors.append(f"expected 50 rows, got {len(rows) if isinstance(rows, list) else type(rows)}")
        rows = []
    counts["clauses"] = len(rows)
    file_cache: dict[str, str] = {}

    for row in rows:
        clause = str(row.get("clause"))
        obligations = row.get("remaining_obligations")
        if not isinstance(obligations, str) or not obligations.strip():
            errors.append(f"{clause}: remaining_obligations empty")
        else:
            counts["remaining_obligations_nonempty"] += 1
            if PASS_TOKEN.search(obligations):
                errors.append(f"{clause}: remaining_obligations contains PASS")
        label = str(row.get("candidate_formal_ci") or "")
        if PASS_TOKEN.search(label):
            errors.append(f"{clause}: candidate_formal_ci contains PASS")
        formal = row.get("formal_ci")
        if formal == "PASS" or (isinstance(formal, str) and PASS_TOKEN.search(formal)):
            errors.append(f"{clause}: formal_ci contains PASS")
        named: list[tuple[str, str]] = []
        iter_named(row.get("declarations"), named)
        if not named:
            errors.append(f"{clause}: no declarations")
            continue
        located = True
        modules: list[str] = []
        for full, filename in named:
            short = full.split(".")[-1]
            rel = (CANDIDATE / filename).as_posix()
            module = f"{MODULE_PREFIX}.{Path(filename).stem}"
            modules.append(module)
            if module not in modules_built or rel not in hashed:
                located = False
                errors.append(f"{clause}: {module} is not in the tip build")
                continue
            if rel not in file_cache:
                file_cache[rel] = (ROOT / rel).read_text(encoding="utf-8")
            problems = body_violations(file_cache[rel], short)
            if problems:
                located = False
                errors.extend(f"{clause}: {problem}" for problem in problems)
            else:
                counts["declarations_located"] += 1
        if located:
            if formal != str(run_id):
                errors.append(f"{clause}: located declarations still have formal_ci {formal!r}")
            else:
                counts["formal_ci_run_id"] += 1
            if label != CANDIDATE_LABEL:
                errors.append(f"{clause}: candidate label {label!r}")
            evidence = row.get("candidate_ci_evidence") or {}
            if evidence.get("run_id") != run_id:
                errors.append(f"{clause}: evidence run_id {evidence.get('run_id')!r}")
            if evidence.get("acceptance_discharged") is not False:
                errors.append(f"{clause}: acceptance_discharged is not false")
            if evidence.get("subject") != subject:
                errors.append(f"{clause}: evidence subject differs from the receipt")
            missing_modules = [module for module in modules if module not in set(evidence.get("module_built") or [])]
            if missing_modules:
                errors.append(f"{clause}: evidence omits {missing_modules}")
        else:
            if formal != "CI_NOT_RUN":
                errors.append(f"{clause}: unlocated row has formal_ci {formal!r}")
            else:
                counts["formal_ci_CI_NOT_RUN"] += 1

    if not legal_path.is_file():
        errors.append(f"missing {LEGAL_REL.as_posix()}")
    else:
        legal_errors = check_legal_text(legal_path.read_text(encoding="utf-8"))
        errors.extend(legal_errors)
        if not legal_errors:
            counts["legal_rows_daihe"] = len(SEVEN)
    return errors, counts


def main() -> int:
    errors, counts = check()
    print(
        "clauses {clauses}; formal_ci_run_id {formal_ci_run_id}; "
        "formal_ci_CI_NOT_RUN {formal_ci_CI_NOT_RUN}; "
        "declarations_located {declarations_located}; "
        "remaining_obligations_nonempty {remaining_obligations_nonempty}; "
        "legal_rows_daihe {legal_rows_daihe}".format(**counts)
    )
    if errors:
        print(f"FAIL {len(errors)}", file=sys.stderr)
        for error in errors:
            print(error, file=sys.stderr)
        return 1
    print("clause declaration binding: located, not acceptance discharge")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
