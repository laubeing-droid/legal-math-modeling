"""Every backticked citation in the construction docs must resolve to a real source line.

Docs that quote theorem locations by hand go stale the moment a proof file grows in the
middle: on 2026-10-01 a single 14-theorem insertion into `Seams/BoundaryClosure.lean`
shifted 36 anchors in the delivery notes, each of which had been verified when written.
The carrier-surface gate checked that names are *audited*; nothing checked that they are
*still where the doc says*. And because the only shape the gate recognised was
`` `name:LINE` ``, an unrecognised name was skipped in silence -- so a drifted table
anchor and a theorem name that exists nowhere in the tree could both go green. Silence on
an unknown name is the defect this rewrite removes: every decision to excuse a token is
listed in VOCAB or EXEMPT with a reason, and every coordinate the doc leaves unbound is
printed, not dropped.

Four citation shapes are checked:

1. `` `name:LINE` `` -- the name is a Lean declaration and LINE must be one of its
   declaration lines in the Lean tree.
2. table shape `` `name` | `:LINE` `` and `` `:LINE name` `` -- number and name sit in
   separate code spans, so shape 1 never paired them. An orphan `` `:LINE` `` adopts the
   subject of the code span immediately before it, but only when nothing but a separator
   stands between the two; in `` `:LINE name` `` the trailing name is what lives there, so
   it heads the anchor when nothing precedes it.
3. file shape `` `file.lean:LINE` `` / `` `file:LINE resident` `` -- the subject is a file.
   The file must exist and LINE must land on a non-blank line; when a resident is named,
   the stated line (or somewhere in the stated range) must actually name it.
4. bare `` `name` `` with no coordinate -- treated as a declaration citation only where the
   doc is plainly citing declarations: the same table cell or sentence already resolves at
   least one other backticked name to a real declaration. There the name must parse as a
   declaration, as a file, as the unique expansion of a declared-name prefix, or be excused
   with a reason; otherwise it is red. Requiring *every* backticked token to be a
   declaration would instead flag JSON keys, CI status enums, Lean tactics and short shas
   by the hundred and bury the real finding, so the confirmation is the trigger.

A coordinate with no citable subject anywhere near it is reported as `unbound`, in its own
block, and does not fail the gate: the doc there points at a line without saying which file
is in scope, which is a doc-completeness gap, not a drift, and guessing a binding would
invent findings. Historical readings quoted in prose (`225->294` and friends,
`audited_targets=1949`) carry no subject and no coordinate grammar, so they are neither
checked nor rewritten.

Two limits are recorded rather than hidden. Mathlib is pinned by commit and not indexed
here, so a Mathlib declaration name (`PMF.cond`, `Finset.exists_maximalFor`) is checked only
for the file it is cited in, never for the name; and a bare name in a cell that cites no
declaration at all is left alone, which is what the shape-4 confirmation buys. Run with
--explain to see both lists.

`--fix` rewrites an anchor only when the repair cannot invent a location: a declaration
anchor with no file token of its own whose short name is declared once in the whole tree, or
a file-scoped anchor whose resident is declared once inside that same file. The file token is
never rewritten; a range, an unbound coordinate, a doc reference, a prefix-expanded shorthand
and a file-only pointer are never rewritten at all.
"""

from __future__ import annotations

import argparse
import os
import re
from collections import defaultdict
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SOURCE_ROOT = ROOT / "proofs" / "lean" / "juris_lean" / "JurisLean"
DOCS = sorted((ROOT / "docs" / "master-plan").glob("0[6-9]_*.md")) + sorted(
    (ROOT / "docs" / "master-plan").glob("1[01]_*.md")
)

# Subscript digits appear inside real declaration names (joint_obs₁_agrees).
SUB = "\u2080-\u2089\u00b9\u00b2\u00b3"
NAME = rf"[A-Za-z_][A-Za-z0-9_{SUB}]*(?:\.[A-Za-z_][A-Za-z0-9_{SUB}]*)*"
DECL = re.compile(
    r"^(?:@\[[^\]]*\][ \t]*)*"
    r"(?:theorem|lemma|def|abbrev|structure|inductive|class)\s+"
    rf"([A-Za-z_][A-Za-z0-9_.{SUB}]*[A-Za-z0-9_{SUB}])"
)

# Paths in this corpus carry CJK segments, so the file token gets a wider alphabet than NAME.
PATHSEG = rf"[A-Za-z0-9_.{SUB}\u4e00-\u9fff-]+"
FILE_EXT = ("lean", "py", "md", "json", "yaml", "yml", "toml", "sh", "txt")
TOKEN = re.compile(
    rf"(?P<file>(?:{PATHSEG}/)*{PATHSEG}\.(?:{'|'.join(FILE_EXT)}))"
    rf"|(?P<docid>\d{{2}}):(?P<doclo>\d+)(?:-(?P<doclo_end>\d+))?"
    rf"|(?P<name>{NAME})"
    rf"|:\s*(?P<lo>\d+)(?:\s*[-\u2013]\s*(?P<hi>\d+))?"
)

# A code span holding any of these is prose, a shell command or a data literal, never a
# citation: `{"msg":"...","code":500}` and `audited_targets=1949` must not parse as anchors.
DISQUALIFIERS = set("{}[]=<>%&*\"'!?+~`；：，。、")

# Sentence ends. A coordinate never adopts a subject across one of these, which is what
# keeps `... 首处 `:292`` in a later table cell from binding to a file named two cells back.
BOUNDARIES = re.compile(r"[。；;]|\n")

# The only text allowed between a citation and the orphan `:LINE` that follows it. A gap
# carrying a word -- ` 与 `、`表头`、`首处` -- means the doc is not pointing back at that
# subject, so the coordinate stays unbound instead of borrowing a wrong owner.
SEPARATORS = set(" \t、,/|（）()-–—…")

SKIP_DIRS = {".git", ".lake", "__pycache__", "node_modules", ".venv", "build", "dist"}
EXTERNAL_ROOTS = ("Mathlib/", "Std/", "Batteries/")

#: Vocabulary that is a real identifier of Lean, Mathlib, a shell or a tactic -- never a
#: citation into this repository's tree, so never something the gate should demand of a doc.
VOCAB = frozenset(
    """theorem lemma def abbrev structure inductive class instance example where by show have
    from if then else protected private noncomputable partial mutual unfolding set_option open
    namespace end deriving variable include axiom sorry admit native_decide decide rfl omega
    dsimp simp simp_all rw intro exact apply refine norm_num ring linarith tauto aesop rcases
    obtain induction wlog push_neg ext constructor congr cases rename_i trivial familiar
    guard fun_induction positivity de构
    Prop True False Set Class Subtype Sigma PSigma ULift Eq Iff And Or Option Bool Unit Nat Int
    String List Fin Float NNReal Real Rat Order Measure PMF Finset Multiset AddLeftMono
    Nonempty EmptyType ElimMismatch Decidable Quot Classical
    GaloisConnection IsSatisfiable mem_cons_self Int.toNat toMeasure stdSimplex
    grep sed awk curl wget python pytest lake git rg jq make cmake shell bash
    M a b c f g n p q r s t x y z xs ys vs vs2 h hsep hclosed q_ e_
    UNKNOWN CI_NOT_RUN PASS FAIL SKIP ERROR TIMEOUT""".split()
)
VOCAB -= {"de构"}
VOCAB |= {"some", "none", "in", "do", "let", "return", "match", "with", "fun", "suffices"}

#: Backticked names that are genuine identifiers of some *other* part of this repository --
#: JSON keys, artifact fields, CI status words, record fields, doc-side shorthands. Every
#: entry is a decision, not an oversight: no reason, no exemption.
EXEMPT: dict[str, str] = {
    "propext": "Lean core axiom, not a JurisLean declaration",
    "Quot.sound": "Lean core axiom, not a JurisLean declaration",
    "Classical.choice": "Lean core axiom, not a JurisLean declaration",
    "sorryAx": "Lean kernel constant named in axiom audits",
    "mem_cons_self": "Mathlib lemma, outside the JurisLean tree",
    "deriving": "keyword; also the source of auto-generated .mk false positives",
    "X.mk": "generic constructor shape named by card W1c",
    "Lean": "the prover, named as a system rather than as an identifier",
    "rest": "Python slice variable quoted inside the card W1b defect note",
    "header": "Python variable quoted inside the card W1b defect note",
    "name": "placeholder inside a shape description",
    "CarriesBasis": "record field named while describing the record",
    "OutcomeExpr": "proposed type named in a method note",
    "SolverState": "proposed type named in a method note",
    "Institution": "category-theory concept named in prose",
    "Comorphism": "category-theory concept named in prose",
    "Fibring": "category-theory concept named in prose",
    "Derive": "Lean elaborator hook named in prose",
    "Derive_i": "auto-generated elaborator hook name",
    "TwoSidedBurden": "record sketch named in the four-question volume",
    "Outcome.failure": "constructor path named as data",
    "EvalResult.noExtension": "constructor path named as data",
    "Step.defenseDefused": "constructor path named as data",
    "Step.enforceabilityRestored": "constructor path named as data",
    "BurdenState.shiftedTo": "field path named as a transition",
    "ApplicableNormQuery.normEnv": "nested field path named in prose",
    "EventHistory.eventTimes": "field path named in prose",
    "LegalModelV2.atDay": "field path named in prose",
    "KernelV3.factTime": "field path named in prose",
    "history.factTime": "field path named in prose",
    "P015.enactedDay": "field path of a frozen artifact",
    "P049.deadlineDay": "field path of a frozen artifact",
    "normId": "JSON key of a canonical legal-fact record",
    "factTime": "field name named in prose",
    "eventTimes": "field name named in prose",
    "adjudicatedStatus": "field named in a four-way split",
    "proceduralDisposition": "field named in a four-way split",
    "pendingLegalJudgment": "field named in a four-way split",
    "adverse": "constructor named as data",
    "unenforceable": "status label named in a walk",
    "compliantProved": "field named inside a record sketch",
    "undecidedPerformance": "constructor named as a terminal state",
    "backflow": "family shorthand for the backflow* declarations, not one name",
    "toGaloisInsertion": "Mathlib name cited from a Mathlib path this gate does not index",
    "introN": "binder name quoted out of a compiler error",
    "remainder": "field explicitly flagged as 溢缴 rather than 未偿",
    "compose": "Mathlib function named inside a fragment quote",
    "enc": "string fragment quoted from a codec",
    "penalt": "string fragment quoted from a grep",
    "liquidated": "legal term in backticks, not an identifier",
    "nonempty_iff": "name fragment quoted while discussing a suffix collision",
    "general_form_closed": "key of 卷覆盖账.jsonl, a Python artifact field",
    "general_form_carriers": "key of 卷覆盖账.jsonl, a Python artifact field",
    "subject_binding": "field of the CI run index artifact",
    "juris_lean_package": "lakefile package identifier",
    "all_tracked_lean": "argument word of scripts/ci/changed_lean_modules.py",
    "all_tracked": "argument word of scripts/ci/changed_lean_modules.py",
    "theorem_inventory_v3": "artifact stem under docs/formal-release",
    "targets_with_sorryAx": "key of the axiom-audit JSON artifact",
    "targets_outside_standard_axioms": "key of the axiom-audit JSON artifact",
    "audited_targets": "key of the axiom-audit JSON artifact",
    "SURFACE_HOLDOUTS": "constant of the carrier-surface gate",
    "PENDING_CI_MODULES": "constant of the root-module holdout",
    "SURFACES": "constant of the surface generator",
    "UNINHABITED": "status word introduced by card W1c",
    "DEF_PROJECTION": "ledger column name",
    "EVIDENCE_ARTIFACTS": "constant of scripts/ci/build_ci_run_index.py",
    "EVIDENCE_MAX_BYTES": "constant of scripts/ci/build_ci_run_index.py",
    "EVIDENCE_SKIP_SUFFIX": "constant of scripts/ci/build_ci_run_index.py",
    "NO_REPORT_ARTIFACT_BY_JOB_SHAPE": "status word introduced by card W1d",
    "ARTIFACT_UNAVAILABLE_NOT_LANDED": "status word introduced by card W1d",
    "FETCH_BLOCKED_OFFLINE": "status word introduced by card W1d",
    "metadata_only_verdict_unreadable_in_repo": "status word introduced by card W1d",
    "head_sha": "GitHub Actions payload field",
    "success": "GitHub Actions conclusion",
    "BOUNDARY_MARKER": "sentinel of a generated audit surface",
    "lean_grammar.declarations": "function of scripts/ci/lean_grammar.py",
    "gapPresent": "field of the signal-detection contract sketch",
    "statistic": "field of the signal-detection contract sketch",
    "detected": "field of the signal-detection contract sketch",
    "SignalDetectionContract": "contract sketch named in a status cell",
    "query.bibliographic": "API field path quoted from a request sample",
    "test_generator_can_refuse_a_stale_label": "pytest function under tests/",
    "test_the_surface_names_no_comment_text": "pytest function under tests/",
    "step_monotone": (
        "structure field proved at DungDefinitions.lean:42, not a top-level declaration"
    ),
}


def is_commit_sha(token: str) -> bool:
    """A short git sha is a reading of a commit, not an identifier to resolve."""

    return (
        7 <= len(token) <= 40
        and token.isascii()
        and token == token.lower()
        and all(c in "0123456789abcdef" for c in token)
    )


def is_vocab(token: str) -> bool:
    return short(token) in VOCAB or token in VOCAB


@dataclass
class Index:
    decl: dict[str, list[tuple[str, int]]]
    decl_full: set[str]
    decls_of: dict[str, dict[str, list[int]]]
    lean_by_stem: dict[str, list[str]]
    lean_by_path: dict[str, str]
    repo_by_basename: dict[str, list[str]]
    doc_stems: dict[str, list[str]]
    lines: dict[str, list[str]] = field(default_factory=dict)
    blocks: dict[tuple[str, int], int] = field(default_factory=dict)


def strip_comments(text: str) -> str:
    """Blank out doc-comments and line-comments so prose never parses as a declaration.

    Without this, a doc-comment body line such as `structure itself.` is indexed as a
    declaration named `itself.`, and every short-name lookup downstream inherits the noise.
    """

    out: list[str] = []
    depth = 0
    for line in text.split("\n"):
        buf: list[str] = []
        i = 0
        while i < len(line):
            if depth:
                if line.startswith("/-", i):
                    depth += 1
                    buf.append("  ")
                    i += 2
                elif line.startswith("-/", i):
                    depth -= 1
                    buf.append("  ")
                    i += 2
                else:
                    buf.append(" ")
                    i += 1
                continue
            if line.startswith("/-", i):
                depth += 1
                buf.append("  ")
                i += 2
            elif line.startswith("--", i):
                buf.append(" " * (len(line) - i))
                i = len(line)
            else:
                buf.append(line[i])
                i += 1
        out.append("".join(buf))
    return "\n".join(out)


def walk_repo() -> list[str]:
    """Repo-relative paths of every possible anchor target, pruning build noise.

    A file anchor may name a doc, a Python helper or a CI artifact rather than a Lean
    source, so the lookup spans the tree; .lake/.git are pruned instead of walked, which
    is tens of thousands of Mathlib build files.
    """

    found: list[str] = []
    for dirpath, dirnames, filenames in os.walk(ROOT):
        # .github is not build noise: the docs cite workflow files by name and line.
        dirnames[:] = [d for d in dirnames if d not in SKIP_DIRS and d != ".git"]
        for name in filenames:
            found.append((Path(dirpath) / name).relative_to(ROOT).as_posix())
    return sorted(found)


def read_lines(rel: str) -> list[str]:
    try:
        return (ROOT / rel).read_text(encoding="utf-8", errors="replace").splitlines()
    except OSError:
        return []


def file_lines(rel: str, index: Index) -> list[str]:
    if rel not in index.lines:
        index.lines[rel] = read_lines(rel)
    return index.lines[rel]


def build_index() -> Index:
    """Declarations plus the file tables the wider shapes need.

    Each declaration is keyed by its full dotted name and by its last component, so a doc
    that writes `_hasSum` where the source says `foo._hasSum` still resolves.
    """

    decl: dict[str, list[tuple[str, int]]] = defaultdict(list)
    decl_full: set[str] = set()
    decls_of: dict[str, dict[str, list[int]]] = defaultdict(lambda: defaultdict(list))
    lean_by_stem: dict[str, list[str]] = defaultdict(list)
    lean_by_path: dict[str, str] = {}
    for lean in sorted(SOURCE_ROOT.rglob("*.lean")):
        rel = lean.relative_to(ROOT).as_posix()
        lean_by_path[rel] = rel
        aliases = {lean.stem, lean.name, rel}
        if rel.startswith("proofs/lean/juris_lean/"):
            tail = rel[len("proofs/lean/juris_lean/") : -5].replace("/", ".")
            aliases.add(tail)
            aliases.add(f"JurisLean.{tail}")
        if rel.startswith("proofs/lean/juris_lean/JurisLean/"):
            tail = rel[len("proofs/lean/juris_lean/JurisLean/") : -5].replace("/", ".")
            aliases.add(tail)
        for alias in aliases:
            lean_by_stem[alias].append(rel)
        for lineno, line in enumerate(strip_comments("\n".join(read_lines(rel))).split("\n"), 1):
            match = DECL.match(line)
            if not match:
                continue
            full = match.group(1)
            decl_full.add(full)
            for key in {full, short(full)}:
                decl[key].append((rel, lineno))
                decls_of[rel][key].append(lineno)

    repo_by_basename: dict[str, list[str]] = defaultdict(list)
    doc_stems: dict[str, list[str]] = defaultdict(list)
    for rel in walk_repo():
        repo_by_basename[Path(rel).name].append(rel)
        stem = Path(rel).stem
        if stem[:2].isdigit():
            doc_stems[stem[:2]].append(rel)
    return Index(dict(decl), decl_full, dict(decls_of), lean_by_stem, lean_by_path,
                 dict(repo_by_basename), dict(doc_stems))


def resolve_file(token: str, index: Index) -> tuple[list[str], bool]:
    """Candidate repo paths for a file-shaped subject, plus whether it is external."""

    token = token.strip()
    root = token.split("/", 1)[0]
    if root in {r.rstrip("/") for r in EXTERNAL_ROOTS}:
        return [], True
    if token in index.lean_by_path:
        return [index.lean_by_path[token]], False
    if token in index.lean_by_stem:
        return sorted(set(index.lean_by_stem[token])), False
    name = token.rsplit("/", 1)[-1]
    hits = sorted(set(index.repo_by_basename.get(name, [])))
    if "/" not in token:
        return hits, False
    # A path is only this repository's file when the repo path really ends with it:
    # `Genealogy/Part1.lean` is, `ModelTheory/Semantics.lean` is not (that is Mathlib).
    exact = [h for h in hits if h.endswith(token)]
    if exact:
        return exact, False
    for depth in range(2, len(token.split("/"))):
        tail = "/".join(token.split("/")[-depth:])
        narrowed = [h for h in hits if h.endswith(tail)]
        if narrowed:
            return narrowed, False
    return [], False


@dataclass
class Ref:
    """One parsed coordinate citation: a subject, a line window, named residents."""

    doc: Path
    line: int
    subject: str | None
    lo: int
    hi: int | None
    residents: list[str]
    start: int  # column of the digits within the doc line, for --fix
    stop: int
    shape: str  # coord | docref
    raw: str = ""


def short(token: str) -> str:
    return token.rsplit(".", 1)[-1]


def scan_doc(doc: Path, index: Index) -> tuple[list[Ref], list[tuple[int, str]]]:
    """Walk one doc line by line, pairing each coordinate with the subject the doc means.

    A code span heads the line only when it *is* a citation: a lone name, or a file with a
    coordinate on it. A span such as `Nat → TimePoint` is prose about two names and must not
    become the owner of the `:378` that follows it.
    """

    coords: list[Ref] = []
    bares: list[tuple[int, str]] = []
    text = doc.read_text(encoding="utf-8")
    for lineno, raw_line in enumerate(text.split("\n"), 1):
        line = raw_line.rstrip("\r")
        spans = [m for m in re.finditer(r"`([^`\n]+)`", line) if m.group(1).strip()]
        subject: str | None = None
        subject_stop = 0
        for span in spans:
            raw = span.group(1)
            base = span.start(1) + (len(raw) - len(raw.lstrip()))
            body = raw.strip()
            if any(c in DISQUALIFIERS for c in body):
                continue
            atoms = list(TOKEN.finditer(body))
            if not atoms:
                continue
            between = line[subject_stop : span.start()] if subject is not None else ""
            adoptable = (
                subject is not None
                and not BOUNDARIES.search(between)
                and set(between) <= SEPARATORS
            )
            if re.fullmatch(NAME, body):
                bares.append((lineno, body))
                if is_citable(body, index):
                    subject, subject_stop = body, span.end()
                continue
            inherited = subject if adoptable else None
            head: str | None = None
            pending: Ref | None = None
            for atom in atoms:
                col = base + atom.start()
                if atom.group("doclo"):
                    # `09:209` is a volume-and-line reference and only counts when a volume
                    # with that number exists; otherwise a timestamp like `18:41` would be
                    # read as a citation to a volume 18.
                    docid = atom.group("docid")
                    if docid in index.doc_stems:
                        coords.append(
                            Ref(doc, lineno, docid, int(atom.group("doclo")),
                                _int(atom.group("doclo_end")), [],
                                base + atom.start("doclo"), base + atom.end("doclo"),
                                "docref", atom.group(0))
                        )
                    pending = None
                    continue
                if atom.group("file") or atom.group("name"):
                    word = atom.group(0)
                    if pending is not None:
                        pending.residents.append(word)
                        if pending.subject is None and is_citable(word, index):
                            pending.subject = word
                    elif head is None and is_citable(word, index):
                        head = word
                    continue
                if atom.group("lo"):
                    # Match.end() on a group that did not participate is -1, which is truthy:
                    # asking for it directly silently turned a rewrite into an insertion.
                    digits_stop = atom.end("hi") if atom.group("hi") else atom.end("lo")
                    ref = Ref(doc, lineno, head or inherited, int(atom.group("lo")),
                              _int(atom.group("hi")), [],
                              base + atom.start("lo"),
                              base + digits_stop, "coord", body)
                    coords.append(ref)
                    pending = ref
            if head is not None and (re.fullmatch(NAME, body) or atoms[0].group("file")):
                subject, subject_stop = head, span.end()
            elif pending is not None:
                subject_stop = span.end()
    return coords, bares


@dataclass
class Resolved:
    kind: str  # decl | file | doc | external | unknown
    subject: str
    files: list[str]
    sites: list[tuple[str, int]]
    expanded: list[str] = field(default_factory=list)


def resolve_token(token: str, index: Index) -> Resolved:
    """Decide what a subject token points at, in the order the doc means it.

    A token with a path separator or a file extension is read as a file and nothing else;
    a bare token is read as a declaration first, then as an unambiguous module stem. Making
    the file reading win for a bare token would let a misspelt theorem name pass as long as
    some file shared its stem, which is a fresh variety of the same silence.

    Two readings keep honest doc shorthand out of the red: a token that is the unique
    head of exactly one declaration (`solverIncomplete` for `solverIncomplete_ne_adjudicated`)
    expands to it, and a leading-underscore token (`_hasSum`) is read as the tail of the one
    declaration that ends with it. Both are still reported as shorthands by `--fix` refusing
    to move them.
    """

    token = token.strip()
    if not token:
        return Resolved("unknown", token, [], [])
    files, external = resolve_file(token, index)
    explicit = "/" in token or token.rsplit(".", 1)[-1] in FILE_EXT
    if explicit:
        if external:
            return Resolved("external", token, [], [])
        # An unresolvable path is reported, not excused: `docs/history/gone.md:326` is a
        # citation to a file that is not in the repo, and an upstream path written without
        # its `Mathlib/` root cannot be checked as written.
        return Resolved("file", token, files, [])
    key = short(token)
    sites = index.decl.get(key, [])
    if sites:
        return Resolved("decl", token, sorted({f for f, _ in sites}), sites)
    if files:
        return Resolved("file", token, files, [])
    heads = sorted({n for n in index.decl_full if key and n.startswith(key)})
    if len(heads) == 1:
        only = heads[0]
        return Resolved("decl", token, sorted({f for f, _ in index.decl[only]}),
                        index.decl[only], heads)
    if key.startswith("_"):
        tails = sorted({n for n in index.decl_full if n.endswith(key)})
        if len(tails) == 1:
            only = tails[0]
            return Resolved("decl", token, sorted({f for f, _ in index.decl[only]}),
                            index.decl[only], tails)
        return Resolved("unknown", token, [], [], tails)
    return Resolved("unknown", token, [], [], heads)


def is_citable(token: str, index: Index) -> bool:
    """Only a token that points at something real may head a coordinate.

    Vocabulary loses even when it resolves: `theorem` and `def` do occur as declaration
    names in this tree, but a doc writing `` `:164 protected theorem compose` `` is naming a
    keyword, not citing the theorem called `theorem`.
    """

    if is_vocab(token):
        return False
    return resolve_token(token, index).kind != "unknown"


def _int(token: str | None) -> int | None:
    return int(token) if token else None


def classify(ref: Ref, index: Index) -> Resolved:
    if ref.shape == "docref":
        return Resolved("doc", ref.subject or "", sorted(set(index.doc_stems.get(
            ref.subject or "", []))), [])
    return resolve_token(ref.subject or "", index)


def describe(res: Resolved) -> str:
    if res.kind in ("file", "doc"):
        return ", ".join(res.files[:3]) or "no such file"
    return ", ".join(f"{f}:{ln}" for f, ln in res.sites[:3])


def names_word(text: str, want: str) -> bool:
    return bool(re.search(rf"(?<![\w.{SUB}]){re.escape(want)}\b", text))


def resident_forms(resident: str) -> list[str]:
    """`TimePoint.epochDay` cites a field through its enclosing type, so both ends count.

    A doc that writes `LegalIds.lean:72 TimePoint.epochDay` points at the structure line,
    and demanding the field name there would flag a citation that is true as written.
    """

    parts = [p for p in resident.split(".") if p]
    if len(parts) <= 1:
        return [resident]
    return [parts[0], parts[-1]]


def _covers(rel: str, ref: Ref, index: Index, want: str | None) -> bool:
    """Does this file back the stated coordinate?

    A single line must be non-blank, and must name a resident when one is given. A range
    only has to sit inside the file and hold the resident somewhere in it: a range points
    at a block, and demanding the name on every line of the block would flag honest
    citations such as `KernelV3.lean:286-298 Exhaustion/FullyExhausted`.
    """

    lines = file_lines(rel, index)
    last = ref.hi or ref.lo
    if ref.lo < 1 or last > len(lines):
        return False
    window = lines[ref.lo - 1 : last]
    wants: list[str] = [want] if want else []
    for resident in ref.residents:
        wants.extend(form for form in resident_forms(resident) if form != want)
    if wants:
        return any(names_word(text, w) for text in window for w in wants)
    if ref.hi is not None:
        return any(text.strip() for text in window)
    return bool(window and window[0].strip())


def _declared_at(res: Resolved, ref: Ref, index: Index) -> str:
    """Where the named resident actually sits, so the report can say where to look."""

    wants = [form for r in ref.residents for form in resident_forms(r)]
    spots = sorted(
        {
            f"{rel}:{ln}"
            for rel in (res.files or [])
            for key, lns in index.decls_of.get(rel, {}).items()
            if key in wants
            for ln in lns
        },
        key=lambda s: (s.split(":")[0], int(s.split(":")[1])),
    )
    return f" ; {', '.join(wants[:2])} is declared at {', '.join(spots[:3])}" if spots else ""


def excused(token: str) -> bool:
    """Listed in EXEMPT (by full dotted name or by last component), or a sha, or vocabulary."""

    return (
        token in EXEMPT
        or short(token) in EXEMPT
        or is_vocab(token)
        or is_commit_sha(token)
    )


def decl_block(rel: str, decl_line: int, index: Index) -> int:
    """Last line of a declaration's signature, so a pointer into it still counts as citing it.

    A doc that writes `_hasSum:182` next to `...apply:181` is quoting the statement, not a
    different theorem. The block runs from the `theorem` line to the line that opens the
    body, capped at twelve, so a real drift of tens or hundreds of lines stays red.
    """

    cached = index.blocks.get((rel, decl_line))
    if cached is not None:
        return cached
    lines = file_lines(rel, index)
    end = min(decl_line + 12, len(lines))
    for ln in range(decl_line, end + 1):
        text = lines[ln - 1] if ln <= len(lines) else ""
        if re.search(r"(:=|:=\s*by|\bwhere\b|\bby\b)", text):
            end = ln
            break
    index.blocks[(rel, decl_line)] = end
    return end


def _decl_cites(res: Resolved, ref: Ref, index: Index) -> bool:
    """Does this declaration back the cited line?

    An exact name accepts its own line, a line inside its signature block, or -- for a range,
    which points at a block rather than at a declaration -- any non-blank window in the file
    that holds it. A *expanded* shorthand (`solverIncomplete` for
    `solverIncomplete_ne_adjudicated`, `_hasSum` for `..._hasSum`) gets no such grace: the doc
    named something the source does not spell that way at that line, so the token itself has
    to appear there.
    """

    if res.expanded:
        want = short(res.expanded[0]) if len(res.expanded) == 1 else short(ref.subject)
        return any(_covers(rel, ref, index, want) for rel in res.files)
    for rel, ln in res.sites:
        if ref.lo == ln:
            return True
        if ref.hi is not None:
            if ref.lo <= ln <= ref.hi:
                return True
            lines = file_lines(rel, index)
            if 1 <= ref.lo <= min(ref.hi or ref.lo, len(lines)):
                window = lines[ref.lo - 1 : ref.hi]
                if any(text.strip() for text in window):
                    return True
        elif ln <= ref.lo <= decl_block(rel, ln, index):
            return True
    return False


def check_ref(ref: Ref, res: Resolved, index: Index) -> tuple[str, str] | None:
    """(category, message) for a broken coordinate; None when the citation holds."""

    label = f"{ref.subject or '(no subject)'}:{ref.lo}" + (f"-{ref.hi}" if ref.hi else "")
    if ref.subject is None:
        return "unbound", f"{label} -- no file or declaration in scope on this line"
    if res.kind == "external":
        return None
    if res.kind == "unknown":
        if excused(ref.subject):
            return None
        hint = f" (nearest declared name: {res.expanded[0]})" if res.expanded else ""
        return "missing", f"{label} no such declaration or file{hint}"
    if res.kind in ("file", "doc"):
        if not res.files:
            return "missing", f"{label} no such {'document' if res.kind == 'doc' else 'file'}"
        if any(_covers(rel, ref, index, None) for rel in res.files):
            return None
        bound = max((len(file_lines(rel, index)) for rel in res.files), default=0)
        named = "/".join(resident_forms(r)[0] for r in ref.residents[:2]) or "a line"
        return "drift", (f"{label} file anchor misses: nothing naming {named} at {ref.subject}"
                         f":{ref.lo}{('-' + str(ref.hi)) if ref.hi else ''}"
                         f" [{describe(res)}, {bound} lines]{_declared_at(res, ref, index)}")
    if _decl_cites(res, ref, index) and (not ref.residents or _holds(res, ref, index)):
        return None
    return "drift", f"{label} (source: {describe(res)})"


def _holds(res: Resolved, ref: Ref, index: Index) -> bool:
    """A resident named beside a declaration anchor must sit in the same line window."""

    probe = Ref(ref.doc, ref.line, ref.subject, ref.lo, ref.hi, list(ref.residents),
                ref.start, ref.stop, "coord")
    return any(_covers(rel, probe, index, None) for rel in res.files)


def segments_of(text: str) -> dict[int, list[str]]:
    """Table cells and sentences, the scope in which a bare name is a citation."""

    return {
        lineno: BOUNDARIES.split(raw.rstrip("\r"))
        for lineno, raw in enumerate(text.split("\n"), 1)
    }


def check_bare(name: str, line_segments: list[str], index: Index) -> tuple[str, str] | None:
    """Red only where the doc is already citing declarations in the same cell or sentence."""

    key = short(name)
    if excused(name) or len(key) <= 3:
        return None
    if is_citable(name, index):
        return None
    confirming = [
        other
        for seg in line_segments
        for other in re.findall(rf"`({NAME})`", seg)
        if other != name and index.decl.get(short(other)) and not is_vocab(other)
    ]
    if not confirming:
        return None
    return "missing", f"{name} no such declaration or file (cited beside {confirming[0]})"


def unpoliced(doc: Path, index: Index) -> list[str]:
    """Bare names excused only because their cell cites no declaration.

    `--explain` prints these. They are the price of the shape-4 confirmation rule, and they
    belong in the open: a name that neither resolves nor has a sibling is invisible to the
    gate, and a list is the only honest way to say so.
    """

    text = doc.read_text(encoding="utf-8")
    segs = segments_of(text)
    _coords, bares = scan_doc(doc, index)
    out: list[str] = []
    seen: set[tuple[int, str]] = set()
    for lineno, name in bares:
        if (lineno, name) in seen or check_bare(name, segs.get(lineno, []), index) is not None:
            continue
        if resolve_token(name, index).kind == "unknown" and not excused(name):
            seen.add((lineno, name))
            out.append(f"L{lineno}: {name}")
    return out


def check(doc: Path, index: Index) -> dict[str, list[str]]:
    text = doc.read_text(encoding="utf-8")
    segs = segments_of(text)
    coords, bares = scan_doc(doc, index)
    buckets: dict[str, list[str]] = {"drift": [], "missing": [], "unbound": []}
    for ref in coords:
        found = check_ref(ref, classify(ref, index), index)
        if found:
            buckets[found[0]].append(f"L{ref.line}: {found[1]}")
    for lineno, name in bares:
        found = check_bare(name, segs.get(lineno, []), index)
        if found:
            buckets[found[0]].append(f"L{lineno}: {found[1]}")
    return buckets


def fixable_anchor(ref: Ref, res: Resolved, index: Index) -> int | None:
    """The one line this anchor may be moved to, or None when a repair would guess.

    Two rewrites are safe because exactly one line can be meant: a declaration anchor with
    no file token of its own whose short name is declared once in the whole tree, and a
    file-scoped anchor whose resident is declared once inside that same file. The file
    token is never rewritten, so a repair can move a number onto a declaration line but can
    never point a wrong file at a plausible line.
    """

    if ref.subject is None or ref.hi is not None:
        return None
    if res.kind == "decl" and not res.expanded and not ref.residents:
        sites = set(res.sites)
        if len({f for f, _ in sites}) == 1 and len(sites) == 1:
            line = res.sites[0][1]
            return None if line == ref.lo else line
        return None
    if res.kind == "file" and ref.residents and ref.hi is None:
        want = short(ref.residents[0])
        for rel in res.files:
            if _covers(rel, ref, index, None):
                return None
            spots = sorted({ln for key, lns in index.decls_of.get(rel, {}).items()
                            if key == want for ln in lns})
            if len(spots) == 1:
                return None if spots[0] == ref.lo else spots[0]
        return None
    return None


def fix(doc: Path, index: Index) -> int:
    text = doc.read_text(encoding="utf-8")
    lines = text.split("\n")
    coords, _bares = scan_doc(doc, index)
    edits: defaultdict[int, list[tuple[int, int, str]]] = defaultdict(list)
    count = 0
    for ref in coords:
        new = fixable_anchor(ref, classify(ref, index), index)
        if new is None or new == ref.lo:
            continue
        edits[ref.line].append((ref.start, ref.stop, str(new)))
        count += 1
    for lineno, patches in edits.items():
        buf = list(lines[lineno - 1])
        for start, stop, value in sorted(patches, key=lambda p: p[0], reverse=True):
            buf[start:stop] = list(value)
        lines[lineno - 1] = "".join(buf)
    if count:
        doc.write_text("\n".join(lines), encoding="utf-8", newline="\n")
    return count


def show(path: Path) -> str:
    try:
        return path.relative_to(ROOT).as_posix()
    except ValueError:  # a doc outside the repository (a test fixture)
        return path.name


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--fix", action="store_true", help="rewrite unambiguous stale anchors")
    ap.add_argument("--explain", action="store_true",
                    help="also list coordinates and names the gate deliberately does not police")
    ap.add_argument("--doc", action="append", help="restrict to these docs (repo-relative)")
    args = ap.parse_args()

    docs = [ROOT / d for d in args.doc] if args.doc else DOCS
    index = build_index()
    if args.fix:
        for doc in docs:
            print(f"{show(doc)}: {fix(doc, index)} anchors rewritten")
        return 0
    totals: dict[str, int] = defaultdict(int)
    for doc in docs:
        buckets = check(doc, index)
        hard = buckets["drift"] + buckets["missing"]
        totals["drift"] += len(buckets["drift"])
        totals["missing"] += len(buckets["missing"])
        totals["unbound"] += len(buckets["unbound"])
        if not hard and not buckets["unbound"]:
            print(f"{show(doc)}: anchors current")
        else:
            print(f"{show(doc)}: {len(hard)} stale anchors, {len(buckets['unbound'])} unbound")
        for heading, key in (("drift", "drift"), ("no such name or file", "missing"),
                             ("unbound, no subject in scope (advisory)", "unbound")):
            if buckets[key]:
                print(f"  [{heading}]")
                for item in buckets[key]:
                    print(f"    {item}")
        if args.explain:
            quiet = unpoliced(doc, index)
            print(f"  [not policed: bare name with no declared sibling in its cell] "
                  f"({len(quiet)})")
            for item in quiet:
                print(f"    {item}")
    total = totals["drift"] + totals["missing"]
    if total:
        print(f"doc anchor drift: {total} stale "
              f"({totals['drift']} line drift, {totals['missing']} name or file absent); "
              f"{totals['unbound']} unbound are advisory. Run --fix where unambiguous.")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
