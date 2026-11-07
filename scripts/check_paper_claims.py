#!/usr/bin/env python3
"""Inventory epistemic claims across the paper corpus.

Exit codes: 0 clean, 1 regression against a baseline, 2 usage error.
"""

from __future__ import annotations

import argparse
import html
import json
import re
import sys
from pathlib import Path
from urllib.error import HTTPError, URLError
from urllib.parse import quote
from urllib.request import Request, urlopen

LABEL_WORDS = {"FORMALIZED", "DERIVED", "CONJECTURE"}
TEX_LABEL_RE = re.compile(r"\\(formalized|derived|conjectured)\{\}")
MD_LABEL_RE = re.compile(r"(?:\*\*|`)\s*(FORMALIZED|DERIVED|CONJECTURE)\b", re.IGNORECASE)
CITE_TEX_RE = re.compile(r"\\cite[tp]?\{([^}]*)\}")
CITE_MD_RE = re.compile(r"\[@([A-Za-z0-9_;\-]+)\]")
BIBKEY_RE = re.compile(r"^\s*@\w+\{\s*([^,]+),", re.MULTILINE)
EQLABEL_RE = re.compile(r"\\label\{([^}]*)\}")
EQREF_RE = re.compile(r"\\eqref\{([^}]*)\}")
LEAN_NAME_RE = re.compile(r"\b(?:ULM\d{2}\w*|[A-Z]\w+)\.lean\b")
BACKTICK_ID_RE = re.compile(r"`([A-Za-z_][A-Za-z0-9_.\-]*)`")
TAG_RE = re.compile(r"\\tag\{(\d+)\}")
HEX40_RE = re.compile(r"\b[0-9a-f]{40}\b")
RUN_ID_RE = re.compile(r"\brun\s*[`'\"]?\d{6,}")
MONITORED_INTS = {"145", "27", "46", "91", "94", "97", "206", "452", "476", "2993"}
BARE_NUM_RE = re.compile(r"\b(?:" + "|".join(sorted(MONITORED_INTS, key=len, reverse=True)) + r")\b")
MATH_SPAN_RE = re.compile(
    r"\\begin\{(?:equation|align|gather)\}.*?\\end\{(?:equation|align|gather)\}"
    r"|\$\$.*?\$\$"
    r"\\\{.*?\\\}"
    r"|\\tag\{\d+\}|\\label\{[^}]*\}|\\eqref\{[^}]*\}"
    r"|(?:Equations?|式)\s*\(?[\d(),\-–\s]+\)?"
    r"|\(\d{1,3}\)(?![\w])",
    re.DOTALL,
)


def prose_only(text: str) -> str:
    return MATH_SPAN_RE.sub(" ", text)


def cite_keys(group: str) -> list[str]:
    return [k.strip() for k in re.split(r"[;,]", group) if k.strip()]


SUBJECT_BOUND_FILES = {"paper/main.md", "paper/main_cn.md"}


def read(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def collect(paper_dir: Path) -> dict:
    tex_files = sorted(paper_dir.glob("sections/*.tex")) + [paper_dir / "main.tex"]
    md_files = sorted(p for p in paper_dir.glob("*.md") if p.name != "README.md")

    inv: dict = {
        "labels": {},
        "eq_labels": set(),
        "eq_refs": set(),
        "tex_eq_labels": set(),
        "tex_eq_refs": set(),
        "tags": set(),
        "cite_keys": set(),
        "lean_files": set(),
        "identifiers": set(),
        "unbound_number_lines": [],
        "files": {},
    }

    for path in tex_files + md_files:
        rel = path.relative_to(paper_dir.parent).as_posix()
        text = read(path)
        tl = len(TEX_LABEL_RE.findall(text))
        ml = len(MD_LABEL_RE.findall(text))
        inv["labels"][rel] = tl + ml
        inv["files"][rel] = {
            "labels": tl + ml,
            "words": len(re.findall(r"\S+", text)),
            "equations": len(re.findall(r"\\begin\{(?:equation|align)\}", text))
            + len(TAG_RE.findall(text)),
        }
        inv["eq_labels"].update(EQLABEL_RE.findall(text))
        inv["eq_refs"].update(EQREF_RE.findall(text))
        inv["tags"].update(TAG_RE.findall(text))
        for group in CITE_TEX_RE.findall(text) + CITE_MD_RE.findall(text):
            inv["cite_keys"].update(cite_keys(group))
        inv["lean_files"].update(LEAN_NAME_RE.findall(text))
        inv["identifiers"].update(
            i for i in BACKTICK_ID_RE.findall(text) if i.upper() not in LABEL_WORDS
        )
        if path.suffix == ".tex":
            inv["tex_eq_labels"].update(EQLABEL_RE.findall(text))
            inv["tex_eq_refs"].update(EQREF_RE.findall(text))

        if rel not in SUBJECT_BOUND_FILES:
            for i, line in enumerate(text.splitlines(), 1):
                plain = prose_only(line)
                if BARE_NUM_RE.search(plain) and not (HEX40_RE.search(line) or RUN_ID_RE.search(line)):
                    inv["unbound_number_lines"].append(
                        {"file": rel, "line": i, "text": line.strip()[:140]}
                    )
    return inv


def bib_keys(paper_dir: Path) -> set[str]:
    path = paper_dir / "references.bib"
    return set(BIBKEY_RE.findall(read(path))) if path.exists() else set()


def bib_entries(text: str) -> dict[str, dict[str, str]]:
    """Read literal BibTeX fields, including nested braces and the first entry.

    String macros/concatenation and malformed entries are explicit errors;
    they cannot silently disappear from the DOI check denominator.
    """
    entries = {}
    pos = 0
    while pos < len(text):
        space = re.match(r"(?:\s|%[^\n]*)*", text[pos:])
        pos += space.end()
        if pos == len(text):
            break
        header = re.match(r"@(\w+)\s*([({])\s*([^,\s{}()]+)\s*,", text[pos:])
        if not header or header[1].lower() in {"string", "preamble", "comment"}:
            raise ValueError(f"unsupported BibTeX entry at offset {pos}")
        key, end = header[3], "}" if header[2] == "{" else ")"
        if key in entries:
            raise ValueError(f"duplicate BibTeX key: {key}")
        pos += header.end()
        fields = {}
        while True:
            space = re.match(r"(?:\s|%[^\n]*)*", text[pos:])
            pos += space.end()
            if pos < len(text) and text[pos] == end:
                pos += 1
                break
            field = re.match(r"(\w+)\s*=\s*", text[pos:])
            if not field:
                raise ValueError(f"malformed BibTeX field in {key} at offset {pos}")
            name = field[1].lower()
            if name in fields:
                raise ValueError(f"duplicate BibTeX field: {key}.{name}")
            pos += field.end()
            start = pos
            if pos < len(text) and text[pos] in '{"':
                opener = text[pos]
                pos += 1
                start = pos
                depth = 1 if opener == "{" else 0
                while pos < len(text):
                    char = text[pos]
                    if char == "\\":
                        pos += 2
                        continue
                    if char == "{":
                        depth += 1
                    elif char == "}":
                        depth -= 1
                    if (opener == "{" and depth == 0) or (opener == '"' and char == '"' and depth == 0):
                        break
                    pos += 1
                if pos >= len(text) or depth < 0:
                    raise ValueError(f"unterminated BibTeX value: {key}.{name}")
                value = text[start:pos]
                pos += 1
            else:
                number = re.match(r"\d+", text[pos:])
                if not number:
                    raise ValueError(f"unsupported BibTeX macro: {key}.{name}")
                value = number[0]
                pos += number.end()
            fields[name] = value
            space = re.match(r"(?:\s|%[^\n]*)*", text[pos:])
            pos += space.end()
            if pos < len(text) and text[pos] == ",":
                pos += 1
            elif pos >= len(text) or text[pos] != end:
                raise ValueError(f"unsupported BibTeX value suffix: {key}.{name}")
        entries[key] = fields
    return entries


def doi_identity(value: str) -> str:
    # DOI equality folds ASCII A-Z only, not Unicode case or normalization.
    return value.strip().translate(str.maketrans("ABCDEFGHIJKLMNOPQRSTUVWXYZ", "abcdefghijklmnopqrstuvwxyz"))


def bibliographic_text(value: str) -> tuple[str, ...]:
    return tuple(re.findall(r"[^\W_]+", html.unescape(value).replace("{", "").replace("}", "").casefold()))


def compare_doi_metadata(fields: dict, metadata: dict) -> list[str]:
    """Exact normalized field comparisons; differing fields require review.

    Initials, abbreviations and partial token overlap never produce a match.
    Online/print/issued years are alternatives explicitly supplied by Crossref.
    """
    issues = []
    if doi_identity(metadata.get("DOI", "")) != doi_identity(fields["doi"]):
        issues.append("DOI_IDENTITY_MISMATCH")
    for field, remote in (("title", "title"), ("journal" if "journal" in fields else "booktitle", "container-title")):
        if field != "title" and field not in fields:
            continue
        values = metadata.get(remote, [])
        if not fields.get(field) or not values:
            issues.append(f"{field.upper()}_MISSING")
        elif bibliographic_text(fields[field]) not in [bibliographic_text(v) for v in values]:
            issues.append(f"{field.upper()}_DIFFERS")
    years = {str(parts[0]) for date in ("issued", "published-print", "published-online")
             for parts in metadata.get(date, {}).get("date-parts", []) if parts}
    if not years or not fields.get("year"):
        issues.append("YEAR_MISSING")
    elif fields["year"].strip() not in years:
        issues.append("YEAR_DIFFERS")
    local_authors = []
    for author in fields.get("author", "").split(" and "):
        parts = [p.strip() for p in author.split(",")]
        local_authors.append(bibliographic_text(" ".join(reversed(parts))))
    remote_authors = [bibliographic_text(a.get("name") or " ".join((a.get("given", ""), a.get("family", ""))))
                      for a in metadata.get("author", [])]
    if not fields.get("author") or not remote_authors or not all(remote_authors):
        issues.append("AUTHOR_MISSING")
    elif local_authors != remote_authors:
        issues.append("AUTHOR_DIFFERS")
    return issues


def fetch_doi_metadata(doi: str) -> dict:
    request = Request(
        "https://api.crossref.org/works/" + quote(doi, safe=""),
        headers={"Accept": "application/json", "User-Agent": "legal-math-modeling/doi-check"},
    )
    with urlopen(request, timeout=20) as response:
        return json.load(response)["message"]


def check_dois(paper_dir: Path, supplied: dict | None = None) -> dict:
    entries = bib_entries(read(paper_dir / "references.bib"))
    results = []
    for key, fields in entries.items():
        if not fields.get("doi"):
            continue
        doi = fields["doi"].strip()
        try:
            metadata = fetch_doi_metadata(doi) if supplied is None else supplied[doi_identity(doi)]
            issues = compare_doi_metadata(fields, metadata)
            status = "REVIEW_REQUIRED" if issues else "MATCH"
        except (HTTPError, URLError, TimeoutError, OSError, ValueError, KeyError, TypeError) as exc:
            # Crossref absence/failure is unresolved, not proof of an invalid DOI.
            issues, status = [f"{type(exc).__name__}: {exc}"], "UNVERIFIED"
        results.append({"key": key, "doi": doi, "status": status, "issues": issues})
    return {"entries": len(entries), "doi_entries": len(results),
            "without_doi": len(entries) - len(results), "results": results}


def compare(baseline: dict, current: dict) -> list[str]:
    problems: list[str] = []
    for key, value in sorted(baseline["labels"].items()):
        gained = current["labels"].get(key, 0)
        if gained < value:
            problems.append(f"label count dropped: {key} {value} -> {gained}")
    for field in ("eq_labels", "cite_keys", "lean_files", "identifiers"):
        missing = set(baseline[field]) - set(current[field])
        if missing:
            problems.append(f"{field} lost: {', '.join(sorted(missing)[:8])}")
    return problems


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    ap = argparse.ArgumentParser()
    ap.add_argument("--paper-dir", default=str(root / "paper"))
    ap.add_argument("--json-out")
    ap.add_argument("--baseline")
    ap.add_argument("--allow-missing-anchors", default="")
    doi_mode = ap.add_mutually_exclusive_group()
    doi_mode.add_argument("--check-dois", action="store_true", help="DOI-only mode: fetch Crossref metadata")
    doi_mode.add_argument("--doi-metadata", help="DOI-only mode: JSON mapping canonical DOI to Crossref work metadata")
    args = ap.parse_args()

    paper_dir = Path(args.paper_dir)
    if not paper_dir.is_dir():
        print(f"FAIL no paper dir: {paper_dir}", file=sys.stderr)
        return 2

    if args.check_dois or args.doi_metadata:
        try:
            supplied = json.loads(read(Path(args.doi_metadata))) if args.doi_metadata else None
            report = check_dois(paper_dir, supplied)
        except (OSError, ValueError) as exc:
            print(f"FAIL DOI input error: {exc}", file=sys.stderr)
            return 1
        if args.json_out:
            out = Path(args.json_out)
            out.parent.mkdir(parents=True, exist_ok=True)
            out.write_text(json.dumps(report, ensure_ascii=False, indent=1), encoding="utf-8")
        failures = [r for r in report["results"] if r["status"] != "MATCH"]
        print(f"DOI entries={report['entries']} checked={report['doi_entries']} "
              f"without_doi={report['without_doi']} unresolved={len(failures)}")
        for result in failures:
            print(f"DOI {result['key']}: {result['status']} {', '.join(result['issues'])}")
        return 1 if failures else 0

    current = collect(paper_dir)
    waiver = {w for w in args.allow_missing_anchors.split(",") if w}
    uncited = sorted(set(current["tex_eq_labels"]) - set(current["tex_eq_refs"]) - waiver)
    dangling = sorted(set(current["tex_eq_refs"]) - set(current["tex_eq_labels"]))
    undefined_cites = sorted(set(current["cite_keys"]) - bib_keys(paper_dir))

    report = {k: (sorted(v) if isinstance(v, set) else v) for k, v in current.items()}
    problems = []
    if undefined_cites:
        problems.append(f"cite keys absent from references.bib: {undefined_cites[:10]}")
    if dangling:
        problems.append(f"\\eqref without matching \\label: {dangling[:10]}")
    if uncited:
        problems.append(
            f"{len(uncited)} \\label never \\eqref'd (dead equations): "
            + ", ".join(uncited[:12])
        )
    if current["unbound_number_lines"]:
        problems.append(
            f"{len(current['unbound_number_lines'])} numeric claims lack a subject SHA or run id"
        )

    if args.baseline:
        problems.extend(compare(json.loads(Path(args.baseline).read_text(encoding="utf-8")), report))

    if args.json_out:
        out = Path(args.json_out)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(report, ensure_ascii=False, indent=1), encoding="utf-8")

    total_labels = sum(current["labels"].values())
    print(f"files={len(current['files'])} labels={total_labels} "
          f"eq_labels={len(current['eq_labels'])} tags={len(current['tags'])} "
          f"cite_keys={len(current['cite_keys'])} lean_files={len(current['lean_files'])} "
          f"identifiers={len(current['identifiers'])}")
    for rel, meta in sorted(current["files"].items()):
        print(f"  {rel:44s} labels={meta['labels']:3d} eq={meta['equations']:3d} words={meta['words']:6d}")
    for item in current["unbound_number_lines"][:12]:
        print(f"  UNBOUND {item['file']}:{item['line']} {item['text']}")

    if problems:
        print("\nFAIL")
        for p in problems:
            print(f"  - {p}")
        return 1
    print("\nOK")
    return 0


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    raise SystemExit(main())
