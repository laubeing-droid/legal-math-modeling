"""Bind the 50 frozen clause rows to the tip build and its re-extracted axiom audit.

A numeric ``formal_ci`` is the run id stored in the tip receipt. Live
``exact_scope`` and ``remaining_obligations`` are empty when every listed
declaration is in that run's ``lean-full-build`` artifact and the kernel's
axiom print uses only ``propext``, ``Quot.sound``, and ``Classical.choice``.
The manuscript text is pinned in the scope archive. When the tip commit
already stores empty live fields, that archive is a verbatim carry-forward of
the earlier pin and is checked against the commit that still holds the text.
This acceptance does not prove archived manuscript gaps.

The checker does not re-download the job and does not re-run Lean. It
re-reads the committed artifact zip, re-parses both logs, and checks the
receipt against ``git show <subject>:<path>`` and the working tree.
"""

from __future__ import annotations

import hashlib
import io
import json
import re
import subprocess
import sys
import zipfile
from pathlib import Path
from urllib.parse import urlparse

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "scripts"))
sys.path.insert(0, str(ROOT / "scripts" / "ci"))

from check_axiom_audit_log import CLEAN, STANDARD_AXIOMS, TARGET, parse  # noqa: E402
from lean_grammar import strip_comments  # noqa: E402

CANDIDATE = Path(
    "proofs/lean/juris_lean/JurisLean/Candidates/Final20261021"
)
STATUS_REL = CANDIDATE / "50_clause_status.json"
CONSTRUCTION_REL = CANDIDATE / "construction_status.json"
RECEIPT_REL = CANDIDATE / "evidence" / "ci-tip-27849d3f" / "verification.json"
ZIP_REL = (
    CANDIDATE
    / "evidence"
    / "ci-tip-27849d3f"
    / "lean-full-build-run40079130550-attempt1.zip"
)
ARCHIVE_REL = CANDIDATE / "evidence" / "ci-tip-27849d3f" / "scope-archive.json"
PRIOR_REL = CANDIDATE / "evidence" / "ci-stage1-d59a487" / "verification.json"
LEGAL_REL = CANDIDATE / "evidence" / "seven_clause_legal_sources.txt"

RECEIPT_STATUS = "TIP_AXIOM_AUDIT_REEXTRACTED_LIVE_SCOPE_EMPTY"
AXIOM_TOKEN = "PASS_REEXTRACTED_STANDARD_AXIOMS_ONLY"
CANDIDATE_LABEL = "LISTED_DECLARATIONS_AXIOM_AUDITED"
MODULE_PREFIX = "JurisLean.Candidates.Final20261021"
CANDIDATE_NAME_PREFIX = MODULE_PREFIX + "."
ZIP_MEMBERS = ("axiom-audit.raw.txt", "lake-clean-build.log")
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


def audit_status(doc: dict) -> str:
    if doc["conflicting_target_lines"]:
        return "FAIL_CONFLICTING_LINES"
    if doc["targets_with_sorryAx"]:
        return "FAIL_SORRYAX"
    if doc["targets_outside_standard_axioms"]:
        return "FAIL_NONSTANDARD_AXIOM"
    return "PASS"


def audit_names(text: str) -> dict[str, list[str]]:
    """Name to axiom list, using the same prints ``parse`` counts."""

    found: dict[str, list[str]] = {}
    for match in TARGET.finditer(text):
        raw = match.group(2).strip()
        axioms = [item.strip() for item in raw.split(",") if item.strip()] if raw else []
        found[match.group(1)] = axioms
    for match in CLEAN.finditer(text):
        found.setdefault(match.group(1), [])
    return found


def subset_audit(names: dict[str, list[str]]) -> dict:
    vocabulary: dict[str, int] = {}
    sorry: dict[str, list[str]] = {}
    outside: dict[str, list[str]] = {}
    for name, axioms in names.items():
        for axiom in axioms:
            vocabulary[axiom] = vocabulary.get(axiom, 0) + 1
        if "sorryAx" in axioms:
            sorry[name] = axioms
        if set(axioms) - STANDARD_AXIOMS:
            outside[name] = axioms
    doc = {
        "audited_targets": len(names),
        "axiom_vocabulary": dict(sorted(vocabulary.items())),
        "targets_with_sorryAx": dict(sorted(sorry.items())),
        "targets_outside_standard_axioms": dict(sorted(outside.items())),
    }
    doc["status"] = audit_status({**doc, "conflicting_target_lines": {}})
    return doc


def public_audit(doc: dict, log_name: str, digest: str) -> dict:
    status = audit_status(doc)
    return {
        "log": log_name,
        "sha256": digest,
        "status": status,
        "audited_targets": doc["audited_targets"],
        "axiom_vocabulary": doc["axiom_vocabulary"],
        "targets_with_sorryAx": doc["targets_with_sorryAx"],
        "targets_outside_standard_axioms": doc["targets_outside_standard_axioms"],
        "conflicting_target_lines": doc["conflicting_target_lines"],
        "standard_axioms_allowed": sorted(STANDARD_AXIOMS),
    }


def zip_members(data: bytes) -> dict[str, bytes]:
    with zipfile.ZipFile(io.BytesIO(data)) as archive:
        names = archive.namelist()
        if set(names) != set(ZIP_MEMBERS) or len(names) != len(ZIP_MEMBERS):
            raise ValueError(f"artifact members {names} != {list(ZIP_MEMBERS)}")
        return {name: archive.read(name) for name in ZIP_MEMBERS}


def reextract(zip_bytes: bytes) -> dict:
    """Re-parse the committed tip artifact. No network and no Lean."""

    members = zip_members(zip_bytes)
    root_text = members["axiom-audit.raw.txt"].decode("utf-8", "replace")
    build_text = members["lake-clean-build.log"].decode("utf-8", "replace")
    root = parse(root_text)
    build = parse(build_text)
    names = audit_names(build_text)
    candidate = {
        name: axioms
        for name, axioms in names.items()
        if name.startswith(CANDIDATE_NAME_PREFIX)
    }
    return {
        "zip_sha256": sha256_bytes(zip_bytes),
        "root": public_audit(root, "axiom-audit.raw.txt", sha256_bytes(members["axiom-audit.raw.txt"])),
        "build_log": public_audit(
            build, "lake-clean-build.log", sha256_bytes(members["lake-clean-build.log"])
        ),
        "candidate": subset_audit(candidate),
        "candidate_names": candidate,
    }


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


COLUMN_COUNT = 8
ARTICLE_CITE = re.compile(r"第[0-9一二三四五六七八九十百千]+条")
LOCATION_PART = re.compile(r"^(.+):(\d+)$")


def legal_cells(line: str) -> list[str]:
    return [cell.strip() for cell in line.split("｜")]


def legal_line_errors(line: str, expected_id: str | None = None) -> list[str]:
    """One archivist row.

    Legal columns are either all ``待核`` (a legal duty whose official text is
    still unrecovered), all ``无法源`` with a reason in the law-name column
    (the clause is a mathematical statement), or a complete official citation.
    The last two columns are the model sentence and ``path:line`` locations.
    """

    errors: list[str] = []
    cells = legal_cells(line)
    if expected_id is not None and (not cells or cells[0] != expected_id):
        errors.append(f"legal row does not start with {expected_id}: {line}")
        return errors
    clause_id = cells[0] if cells else ""
    if len(cells) != COLUMN_COUNT:
        errors.append(f"{clause_id}: expected {COLUMN_COUNT} columns, got {len(cells)}")
        return errors
    legal = cells[1:6]
    if not cells[6]:
        errors.append(f"{clause_id}: missing model sentence")
    if not cells[7]:
        errors.append(f"{clause_id}: missing definition location")
    pending = all(cell == "待核" for cell in legal)
    no_source = legal[0].startswith("无法源") and all(cell == "无法源" for cell in legal[1:])
    if pending or no_source:
        if "://" in line or "http" in line.lower():
            errors.append(f"{clause_id}: marked row also contains a URL")
        if no_source:
            reason = legal[0].removeprefix("无法源").lstrip("：:").strip()
            if not reason:
                errors.append(f"{clause_id}: 无法源 row has no reason")
            if ARTICLE_CITE.search(legal[0]):
                errors.append(f"{clause_id}: 无法源 row cites an article number")
        return errors
    if any(cell == "待核" or cell == "无法源" or cell.startswith("无法源") for cell in legal):
        errors.append(f"{clause_id}: legal columns mix a mark with other text")
        return errors
    if not all(legal):
        errors.append(f"{clause_id}: missing legal column without 待核 or 无法源")
        return errors
    host = (urlparse(cells[4]).hostname or "").lower()
    if host not in OFFICIAL_HOSTS:
        errors.append(f"{clause_id}: unofficial URL host {host or cells[4]}")
    return errors


def location_errors(clause_id: str, location: str) -> list[str]:
    """Each cited line must be the theorem that defines this clause."""

    stem = clause_id.lower().replace(".", "_")
    errors: list[str] = []
    parts = [part.strip() for part in location.split("；") if part.strip()]
    if not parts:
        return [f"{clause_id}: no definition location"]
    for part in parts:
        match = LOCATION_PART.match(part)
        if match is None:
            errors.append(f"{clause_id}: location {part!r} is not path:line")
            continue
        rel, lineno_text = match.group(1), match.group(2)
        path = ROOT / rel
        if not path.is_file():
            errors.append(f"{clause_id}: missing {rel}")
            continue
        lines = path.read_text(encoding="utf-8").splitlines()
        lineno = int(lineno_text)
        if not 1 <= lineno <= len(lines):
            errors.append(f"{clause_id}: {rel}:{lineno} out of range")
            continue
        if not lines[lineno - 1].strip().startswith(f"theorem {stem}"):
            errors.append(f"{clause_id}: {rel}:{lineno} is not theorem {stem}")
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
        "exact_scope_empty": 0,
        "remaining_obligations_empty": 0,
        "axiom_audit": "",
        "legal_rows_daihe": 0,
        "legal_rows_wufayuan": 0,
    }
    status_path = ROOT / STATUS_REL
    receipt_path = ROOT / RECEIPT_REL
    prior_path = ROOT / PRIOR_REL
    legal_path = ROOT / LEGAL_REL
    zip_path = ROOT / ZIP_REL
    archive_path = ROOT / ARCHIVE_REL
    construction_path = ROOT / CONSTRUCTION_REL
    status = json.loads(status_path.read_text(encoding="utf-8"))
    receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
    prior = json.loads(prior_path.read_text(encoding="utf-8"))

    if receipt.get("status") != RECEIPT_STATUS:
        errors.append(f"receipt status {receipt.get('status')!r}")
    if receipt.get("discharges_archived_manuscript_gaps") is not False:
        errors.append("receipt claims the archived manuscript gaps are proved")
    if receipt.get("axiom_audit") == "NOT_REEXTRACTED_FROM_ARTIFACT":
        errors.append("receipt axiom_audit is still NOT_REEXTRACTED_FROM_ARTIFACT")
    if not zip_path.is_file():
        errors.append(f"missing artifact zip {ZIP_REL.as_posix()}")
        return errors, counts
    zip_bytes = zip_path.read_bytes()
    try:
        extracted = reextract(zip_bytes)
    except (zipfile.BadZipFile, ValueError, KeyError) as exc:
        errors.append(f"artifact zip is not the tip lean-full-build pair: {exc}")
        return errors, counts
    if receipt.get("artifact_zip_sha256") != extracted["zip_sha256"]:
        errors.append("receipt artifact_zip_sha256 != committed zip")
    if receipt.get("axiom_audit") != AXIOM_TOKEN:
        errors.append(f"receipt axiom_audit {receipt.get('axiom_audit')!r}")
    elif (
        extracted["root"]["status"] != "PASS"
        or extracted["build_log"]["status"] != "PASS"
        or extracted["candidate"]["status"] != "PASS"
    ):
        errors.append("re-extracted logs are not standard-axioms-only")
    else:
        counts["axiom_audit"] = AXIOM_TOKEN
    for label, key in (("axiom_audit_root", "root"), ("build_log_axiom_audit", "build_log")):
        if receipt.get(label) != extracted[key]:
            errors.append(f"receipt {label} != re-extracted {extracted[key]['log']}")
    candidate_receipt = receipt.get("candidate_axiom_audit") or {}
    candidate_now = extracted["candidate"]
    for field in (
        "status",
        "audited_targets",
        "axiom_vocabulary",
        "targets_with_sorryAx",
        "targets_outside_standard_axioms",
    ):
        if candidate_receipt.get(field) != candidate_now.get(field):
            errors.append(f"candidate axiom audit {field} != re-extraction")
    subject = str(receipt.get("subject_commit") or "")
    if not re.fullmatch(r"[0-9a-f]{40}", subject):
        errors.append(f"receipt subject is not a commit: {subject}")
    run_id = receipt.get("run_id")
    if not isinstance(run_id, int):
        errors.append("receipt run_id is not an int")
        return errors, counts
    scope = str(status.get("formal_ci_field_scope") or "")
    for phrase in (
        "Live exact_scope is empty",
        "live remaining_obligations is empty",
        "re-extracted",
        "does not prove archived manuscript gaps",
        "CI_NOT_RUN",
    ):
        if phrase not in scope:
            errors.append(f"formal_ci_field_scope missing {phrase!r}")
    tip = status.get("tip_declaration_location") or {}
    if tip.get("axiom_audit") != AXIOM_TOKEN:
        errors.append(f"tip_declaration_location.axiom_audit {tip.get('axiom_audit')!r}")
    if tip.get("subject") != subject or tip.get("run_id") != receipt.get("run_id"):
        errors.append("tip_declaration_location is not bound to the receipt subject and run")
    if tip.get("artifact_zip_sha256") != extracted["zip_sha256"]:
        errors.append("tip_declaration_location artifact hash != zip")
    if tip.get("verification") != RECEIPT_REL.relative_to(CANDIDATE).as_posix():
        errors.append("tip_declaration_location verification path != receipt")
    if tip.get("discharges_archived_manuscript_gaps") is not False:
        errors.append("tip_declaration_location claims archived manuscript gaps are proved")
    if tip.get("acceptance_discharged") is not True:
        errors.append("tip_declaration_location acceptance_discharged is not true")
    if construction_path.is_file():
        construction = json.loads(construction_path.read_text(encoding="utf-8"))
        if construction.get("tip_declaration_location") != tip:
            errors.append("construction_status tip_declaration_location != 50_clause_status")
    else:
        errors.append(f"missing {CONSTRUCTION_REL.as_posix()}")
    if not archive_path.is_file():
        errors.append(f"missing {ARCHIVE_REL.as_posix()}")
        archive = {}
    else:
        archive = json.loads(archive_path.read_text(encoding="utf-8"))
        if sha256_bytes(archive_path.read_bytes()) != receipt.get("scope_archive_sha256"):
            errors.append("scope archive sha256 != receipt")
    manuscript_subject = str(archive.get("pinned_subject") or "")
    if not re.fullmatch(r"[0-9a-f]{40}", manuscript_subject):
        errors.append(f"scope archive pinned_subject is not a commit: {manuscript_subject}")
    if manuscript_subject != subject:
        # The tip commit already emptied the live fields. The archive must
        # name that tip, carry the earlier manuscript rows verbatim, and stay
        # pinned to the commit that still holds the text.
        if archive.get("tip_subject") != subject:
            errors.append("scope archive tip_subject is not the receipt subject")
        carried_rel = archive.get("carried_from")
        carried_path = (ROOT / CANDIDATE / str(carried_rel or "")).resolve()
        evidence_root = (ROOT / CANDIDATE / "evidence").resolve()
        if (
            not isinstance(carried_rel, str)
            or carried_path == archive_path.resolve()
            or evidence_root not in carried_path.parents
            or not carried_path.is_file()
        ):
            errors.append("scope archive carried_from is not an earlier evidence file")
        else:
            carried = json.loads(carried_path.read_text(encoding="utf-8"))
            if carried.get("rows") != archive.get("rows"):
                errors.append("carried scope archive rows differ from the earlier pin")
            if carried.get("pinned_subject") != manuscript_subject:
                errors.append("carried scope archive pinned_subject differs")
        try:
            tip_committed = json.loads(
                git_show_bytes(subject, STATUS_REL.as_posix()).decode("utf-8")
            )
        except (RuntimeError, UnicodeDecodeError, json.JSONDecodeError) as exc:
            errors.append(str(exc))
            tip_committed = {}
        tip_rows = tip_committed.get("rows") if isinstance(tip_committed, dict) else None
        if not isinstance(tip_rows, list):
            errors.append("tip subject status has no rows")
        else:
            for row in tip_rows:
                clause = str(row.get("clause"))
                if row.get("exact_scope") != "":
                    errors.append(f"{clause}: tip subject exact_scope is not empty")
                if row.get("remaining_obligations") != []:
                    errors.append(
                        f"{clause}: tip subject remaining_obligations is not empty"
                    )
    try:
        pinned_status = json.loads(
            git_show_bytes(manuscript_subject, STATUS_REL.as_posix()).decode("utf-8")
        )
    except (RuntimeError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        errors.append(str(exc))
        pinned_status = {}
    pinned_rows = pinned_status.get("rows") if isinstance(pinned_status, dict) else None
    archived_rows = archive.get("rows")
    if not isinstance(pinned_rows, list) or not isinstance(archived_rows, list):
        errors.append("scope archive or pinned status has no rows")
        pinned_by_clause = {}
    elif [row.get("clause") for row in archived_rows] != [row.get("clause") for row in pinned_rows]:
        errors.append("scope archive clause order != pinned subject")
        pinned_by_clause = {}
    else:
        pinned_by_clause = {}
        for archived, pinned in zip(archived_rows, pinned_rows):
            clause = str(archived.get("clause"))
            pinned_by_clause[clause] = pinned
            if archived.get("exact_scope") != pinned.get("exact_scope"):
                errors.append(f"{clause}: archived exact_scope != pinned subject")
            if archived.get("remaining_obligations") != pinned.get("remaining_obligations"):
                errors.append(f"{clause}: archived remaining_obligations != pinned subject")
            if not str(archived.get("exact_scope") or "").strip():
                errors.append(f"{clause}: archived exact_scope empty")
            if not str(archived.get("remaining_obligations") or "").strip():
                errors.append(f"{clause}: archived remaining_obligations empty")

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
        if row.get("exact_scope") != "":
            errors.append(f"{clause}: exact_scope is not empty")
        else:
            counts["exact_scope_empty"] += 1
        obligations = row.get("remaining_obligations")
        if obligations != []:
            errors.append(f"{clause}: remaining_obligations is not empty")
        else:
            counts["remaining_obligations_empty"] += 1
        if clause not in pinned_by_clause:
            errors.append(f"{clause}: missing from the scope archive")
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
            if evidence.get("acceptance_discharged") is not True:
                errors.append(f"{clause}: acceptance_discharged is not true")
            if evidence.get("discharges_archived_manuscript_gaps") is not False:
                errors.append(f"{clause}: evidence claims archived manuscript gaps are proved")
            for full, _filename in named:
                axioms = extracted["candidate_names"].get(full)
                if axioms is None:
                    errors.append(f"{clause}: {full} missing from re-extracted candidate axiom audit")
                elif set(axioms) - STANDARD_AXIOMS:
                    errors.append(f"{clause}: {full} axioms {axioms}")
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
        legal_text = legal_path.read_text(encoding="utf-8")
        legal_errors = check_legal_text(legal_text)
        errors.extend(legal_errors)
        for raw in legal_text.splitlines():
            line = raw.strip()
            if not line or line.startswith("#"):
                continue
            cells = legal_cells(line)
            if len(cells) != COLUMN_COUNT:
                continue
            if all(cell == "待核" for cell in cells[1:6]):
                counts["legal_rows_daihe"] += 1
            elif cells[1].startswith("无法源"):
                counts["legal_rows_wufayuan"] += 1
            errors.extend(location_errors(cells[0], cells[7]))
    return errors, counts


def main() -> int:
    errors, counts = check()
    print(
        "clauses {clauses}; formal_ci_run_id {formal_ci_run_id}; "
        "formal_ci_CI_NOT_RUN {formal_ci_CI_NOT_RUN}; "
        "declarations_located {declarations_located}; "
        "exact_scope_empty {exact_scope_empty}; "
        "remaining_obligations_empty {remaining_obligations_empty}; "
        "axiom_audit {axiom_audit}; "
        "legal_rows_daihe {legal_rows_daihe}; "
        "legal_rows_wufayuan {legal_rows_wufayuan}".format(**counts)
    )
    if errors:
        print(f"FAIL {len(errors)}", file=sys.stderr)
        for error in errors:
            print(error, file=sys.stderr)
        return 1
    print("clause declaration binding: axiom audit re-extracted; live scope fields empty")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
