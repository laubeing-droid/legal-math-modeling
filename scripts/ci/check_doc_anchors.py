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
   the stated line (or somewhere in the stated range) must actually name it. A file that is
   not in the repository is not thereby excused: it is looked for in the pinned packages, in
   the four orders named in RESOLUTION_ORDER below, and is red when all four miss.
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

Mathlib and the other pinned packages are part of what the docs cite, so they are part of
what the gate checks: `` `ModelTheory/Semantics.lean:1067` `` used to be reported as "no such
file" because only the repository tree was indexed, and the gate then read as correct a
citation that was merely outside its reach. External files and external declaration names are
resolved against `.lake/packages` through a lazily built index (one pass over ~9 200 files
and ~100 MB, cached for the process, never per anchor) and the cited line is verified exactly
as a repository line is. A name is put to that index only when the doc spells it qualified
(`Finset.filter_congr`), because Mathlib's 168 000 identifiers end in ordinary words and a bare
`name` would resolve to something and mean nothing; bare words stay the business of VOCAB and
EXEMPT, where a reason is written. A bare name in a cell that cites no declaration at all is
left alone, which is what the shape-4 confirmation rule buys. Run with --explain to see both
lists.

Four consequences are recorded rather than hidden. An external declaration is matched on the
declaration-shaped line, so doc-comment prose that opens with `theorem ` can make a name look
present -- it can excuse a name, never redden one. Ambiguous external file names are red:
`Types.lean:159` matches eleven files under the pinned packages, and a gate that accepted any
of them would stop checking the line the doc means. Lean's own core is not under
`.lake/packages` at all, because it ships with the toolchain, so `Nat.le_of_lt` and
`Quot.sound` resolve nowhere for this gate and stay in EXEMPT with that reason written. And
where `.lake/packages` is not on disk -- the `python-gates` CI job checks out the repository
without the pinned sources -- an external citation cannot be verified, so it is red with the
missing root named in the message: "unverifiable here" is not "verified".

`--fix` rewrites an anchor only when the repair cannot invent a location: a declaration
anchor with no file token of its own whose short name is declared once in the whole tree, or
a file-scoped anchor whose resident is declared once inside that same file. The file token is
never rewritten; a range, an unbound coordinate, a doc reference, a prefix-expanded shorthand
and a file-only pointer are never rewritten at all.
"""

from __future__ import annotations

import argparse
import json
import os
import re
from collections import defaultdict
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SOURCE_ROOT = ROOT / "proofs" / "lean" / "juris_lean" / "JurisLean"
PLAN_ROOT = ROOT / "docs" / "master-plan"
#: Volumes the construction record numbers from 06 upward. The corpus is a rule over the
#: directory, not a list of globs: the coverage once widened by pattern (`0[6-9]` plus `1*`),
#: and a volume 20 would then have joined no gate while every earlier volume kept being read.
#: FIRST_POLICED_VOLUME is the one decision the rule carries, and the test for coverage restates
#: it, so a new volume cannot be added without the gate either reading it or being told to.
FIRST_POLICED_VOLUME = 6


def doc_corpus() -> list[Path]:
    """Every numbered volume from FIRST_POLICED_VOLUME on, in filename order."""

    out = []
    for path in sorted(PLAN_ROOT.glob("*.md")):
        head = path.stem[:2]
        if head.isdigit() and int(head) >= FIRST_POLICED_VOLUME:
            out.append(path)
    return out


DOCS = doc_corpus()


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
#: Roots that mark a citation as upstream rather than ours. They used to mean "skip"; they now
#: mean "this token is a file, not a declaration name" -- the file is then looked for in the
#: pinned packages and its line verified like any other.
EXTERNAL_ROOTS = ("Mathlib/", "Std/", "Batteries/")

#: The lake build directory of the pinned dependencies. It is 101 MB of Lean across ~9 200
#: files, so it is never walked by `walk_repo`; the external index below reads it once, lazily.
LAKE_PACKAGES = ROOT / "proofs" / "lean" / "juris_lean" / ".lake" / "packages"
MATHLIB_PACKAGE = "mathlib"
#: The ports the repository carries in-tree (elazarg/GameTheory, davorje/neural-network-proofs).
VENDORED_EXTERNAL = SOURCE_ROOT / "External"

#: The orders a file anchor is resolved in, and the words the failure message quotes back.
#: Order 1 is the repository source tree, which already contains the vendored ports; order 4 is
#: kept explicitly so that a future change pruning `External/` from the repo walk still resolves
#: a port rather than reporting it as a file that does not exist.
RESOLUTION_ORDER = (
    "JurisLean/**",
    ".lake/packages/mathlib/**",
    ".lake/packages/*/**",
    "JurisLean/External/**",
)
ORDER_FOUR = ", ".join(RESOLUTION_ORDER)
#: Namespace scopes of the pinned sources: Mathlib declares `filter_congr` under
#: `namespace Finset`, and the doc cites `Finset.filter_congr`. The two are the same theorem
#: only once the scope is read, so the scope is what the name check compares against.
EXT_SCOPE = re.compile(rb"^(?:(namespace)|(end))[ \t]+([A-Za-z_][A-Za-z0-9_.]*)", re.M)

#: How many files a cited declaration name is followed into for its line number. Real names sit
#: in one to three files; the cap only bites on a short name no doc should cite by line.
EXTERNAL_SITE_FILES = 40

# An external declaration is matched on a declaration-shaped line. `protected`, `private`,
# `noncomputable`, `partial`, `mutual` and attributes precede the keyword in Mathlib sources,
# so a prefix-blind pattern loses real names (`protected theorem compose` is cited in 卷12).
# External identifiers are ASCII: subscripted names are a feature of the vendored ports, and
# order 1 indexes those with the repo pattern that carries SUB.
EXT_DECL = re.compile(
    rb"^(?:@\[[^\]]*\][ \t]*|(?:protected|private|noncomputable|partial|mutual)[ \t]+)*"
    rb"(?:theorem|lemma|def|abbrev|structure|inductive|class)\s+"
    rb"([A-Za-z_][A-Za-z0-9_.]*)",
    re.M,
)

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
    "mem_cons_self": "Lean core lemma: the pinned Mathlib declares only the Finset, Multiset, "
                     "Sym and Vector versions of this name",
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
    is tens of thousands of Mathlib build files. The pinned sources the docs genuinely cite
    are indexed separately, once, by `build_external`.
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


@dataclass
class Tier:
    """One resolution order over the pinned sources, with its own basename table."""

    label: str
    paths: list[str]
    by_basename: dict[str, list[str]] = field(default_factory=dict)


@dataclass
class External:
    """The pinned packages, indexed once for the process, in two separately lazy halves.

    `.lake/packages` is 101 MB of Lean across ~9 300 files, so it is never re-walked per anchor.
    Path names come off a directory walk in under a second and answer file anchors; declaration
    names need every file *read* (about five seconds), which only a qualified citation can ask
    for, so that half is paid on the first dotted name and never for a doc that cites no
    upstream identifier. Doing neither is what let a guessed Mathlib name --
    `Finset.not_mem_empty`, `Finset.mem_prod`, `PMF.cond`, nine compile cycles burned this
    session -- read as a broken doc instead of a broken guess.
    """

    present: bool
    tiers: list[Tier]
    decl_paths: dict[str, set[str]] = field(default_factory=dict)
    sites: dict[str, list[tuple[str, int]]] = field(default_factory=dict)
    scopes: dict[str, list[tuple[int, str, str]]] = field(default_factory=dict)
    scanned: bool = False
    files: int = 0
    names: int = 0


_EXTERNAL: External | None = None


def external_index() -> External:
    """The one cached external index; every lookup goes through here."""

    global _EXTERNAL
    if _EXTERNAL is None:
        _EXTERNAL = build_external()
    return _EXTERNAL


def _tier(label: str, paths: list[str]) -> Tier:
    by_name: dict[str, list[str]] = defaultdict(list)
    for rel in sorted(paths):
        by_name[Path(rel).name].append(rel)
    return Tier(label, sorted(paths), dict(by_name))


def build_external() -> External:
    """Walk the pinned sources for their paths, grouped in the order a file anchor reads them.

    Declaration names are the expensive half -- every file has to be read for them -- so they
    are not collected here; `ensure_decl_names` does that once, on the first qualified citation
    that can ask. A doc that cites no upstream identifier never pays for the corpus.
    """

    paths: dict[str, list[str]] = {MATHLIB_PACKAGE: [], "package": [], "vendored": []}
    present = LAKE_PACKAGES.is_dir()
    if present:
        for dirpath, dirnames, filenames in os.walk(LAKE_PACKAGES):
            dirnames[:] = [d for d in dirnames if d not in SKIP_DIRS]
            here = Path(dirpath).relative_to(LAKE_PACKAGES).parts
            package = (here[0] if here else "").lower()
            bucket = MATHLIB_PACKAGE if package == MATHLIB_PACKAGE else "package"
            for name in filenames:
                if name.endswith(".lean"):
                    paths[bucket].append((Path(dirpath) / name).relative_to(ROOT).as_posix())
    if VENDORED_EXTERNAL.is_dir():
        paths["vendored"] = [p.relative_to(ROOT).as_posix()
                             for p in VENDORED_EXTERNAL.rglob("*.lean")]
    tiers = [
        _tier(RESOLUTION_ORDER[1], paths[MATHLIB_PACKAGE]),
        _tier(RESOLUTION_ORDER[2], paths["package"]),
        _tier(RESOLUTION_ORDER[3], paths["vendored"]),
    ]
    return External(present, tiers, files=sum(len(t.paths) for t in tiers))


def ensure_decl_names(ext: External) -> External:
    """Read the pinned sources once and key every declaration name by what the file typed.

    Names are keyed both by the identifier as written and by its last component, because a
    Mathlib file declares `filter_congr` inside `namespace Finset` while a doc cites
    `Finset.filter_congr`; the namespace is confirmed later, against the file itself, in
    `file_decl_names`. Lines are not recorded here: 240k line records for names no doc ever
    cites is memory nobody needs, so a cited name's line is recovered from the few files the
    name index points at. The `scanned` flag is set before the read, so a half-failed pass makes
    the gate report what it has rather than re-reading 100 MB once per anchor.
    """

    if ext.scanned or not ext.present:
        return ext
    ext.scanned = True
    for tier in ext.tiers[:2]:  # the vendored ports are declaration-indexed by order 1 already
        for rel in tier.paths:
            try:
                data = (ROOT / rel).read_bytes()
            except OSError:
                continue
            for match in EXT_DECL.finditer(data):
                full = match.group(1).decode("utf-8", "replace")
                for key in {full, short(full)}:
                    ext.decl_paths.setdefault(key, set()).add(rel)
    ext.names = len(ext.decl_paths)
    return ext


def may_be_external(token: str, explicit: bool) -> bool:
    """Is it worth reading 100 MB to answer this token?

    Two refusals keep the corpus off the common path. The external tiers hold `.lean`
    sources only, so a doc or Python anchor the repository does not carry cannot be hiding in
    them -- and a file anchor only needs the path walk, never the read. And a *bare* name is
    never put to the declaration index: across 168 000 Mathlib identifiers, the tails
    of `name`, `compose`, `rest` and `sound` all answer, so a qualified `Foo.bar` is what makes
    an external citation identifiable as one -- a bare word stays the business of VOCAB and
    EXEMPT, where a human wrote a reason.
    """

    if explicit:
        return token.endswith(".lean") or any(token.startswith(root) for root in EXTERNAL_ROOTS)
    return "." in token


def resolve_external_file(token: str, ext: External) -> tuple[list[str], str]:
    """Resolution orders 2 to 4: the pinned Mathlib, the other packages, then the ports.

    Order 1 is the repository tree and has already been tried by `resolve_file`. The first order
    that answers wins, and its whole hit set is handed back: the caller reports more than one
    file as ambiguous, because accepting any one of the eleven `Types.lean` files in the pin
    would check the line the doc means in none of them.
    """

    for tier in ext.tiers:
        if "/" in token:
            hits = [p for p in tier.paths if p.endswith("/" + token)]
        else:
            hits = list(tier.by_basename.get(token.strip("/"), []))
        if hits:
            return sorted(set(hits)), tier.label
    return [], ""


def external_decl_paths(token: str, ext: External) -> list[str]:
    """Files in the pinned sources that declare this name, as written and by last component."""

    ensure_decl_names(ext)
    key = short(token)
    return sorted(ext.decl_paths.get(token, set()) | ext.decl_paths.get(key, set()))


def file_decl_names(rel: str, ext: External) -> list[tuple[int, str, str]]:
    """(line, name as typed, name with its namespaces in front) for one pinned source file.

    The corpus pass records the name as typed, which is not the name the checker sees: inside
    `namespace Finset`, `theorem filter_congr` *is* `Finset.filter_congr`. Reading the scopes
    back from the handful of files a cited name lives in costs almost nothing and is what makes
    a qualified citation checkable rather than plausible. Memoised per file.
    """

    cached = ext.scopes.get(rel)
    if cached is not None:
        return cached
    out: list[tuple[int, str, str]] = []
    try:
        data = (ROOT / rel).read_bytes()
    except OSError:
        ext.scopes[rel] = out
        return out
    events: list[tuple[int, int, str]] = []
    for match in EXT_SCOPE.finditer(data):
        events.append((match.start(), 0 if match.group(1) else 1,
                       match.group(3).decode("utf-8", "replace")))
    for match in EXT_DECL.finditer(data):
        events.append((match.start(), 2, match.group(1).decode("utf-8", "replace")))
    events.sort()
    stack: list[str] = []
    line = 1
    last = 0
    for pos, kind, name in events:
        line += data.count(b"\n", last, pos)
        last = pos
        if kind == 0:
            stack.append(name)
        elif kind == 1:
            # `end X` closes the innermost scope called X; a stray `end` must not pop a scope
            # it never opened, which would qualify every later name wrongly.
            for depth in range(len(stack) - 1, -1, -1):
                if stack[depth] == name.rsplit(".", 1)[-1] or ".".join(stack[: depth + 1]) == name:
                    del stack[depth:]
                    break
        else:
            qualified = ".".join(stack + [name]) if stack else name
            out.append((line, name, qualified))
    ext.scopes[rel] = out
    return out


def external_decl_sites(token: str, ext: External) -> list[tuple[str, int]]:
    """The declaration lines of a qualified pinned-package name, in the files that hold it.

    Only a dotted token is put to the corpus: a bare `name` or `sound` matches thousands of
    declaration tails in Mathlib and would let an English word in a doc head a line number. The
    token has to be the name the source elaborates to -- typed that way, or typed under the
    namespaces it spells -- so `Finset.filter_congr` checks and `Quot.sound` does not resolve to
    some tactic test's `Proof.sound`. A name declared in more than EXTERNAL_SITE_FILES files
    keeps its existence but may lose its line, which is the honest failure: the gate says the
    line was not found rather than inventing one.
    """

    cached = ext.sites.get(token)
    if cached is not None:
        return cached
    out: list[tuple[str, int]] = []
    if "." in token:
        for rel in external_decl_paths(token, ext)[:EXTERNAL_SITE_FILES]:
            for lineno, typed, qualified in file_decl_names(rel, ext):
                if token in (typed, qualified) or typed.endswith("." + token) \
                        or qualified.endswith("." + token):
                    out.append((rel, lineno))
    ext.sites[token] = out
    return out


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
    """Resolution order 1: candidate repo paths for a file-shaped subject, plus externality.

    The bool says the token is rooted upstream (`Mathlib/...`), which makes it a file and never
    a declaration name. Upstream is no longer the same word as unverified: a miss here falls
    through to `resolve_external_file`, which reads the pinned packages.
    """

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
    # `Genealogy/Part1.lean` is, `ModelTheory/Semantics.lean` is not -- that one is Mathlib,
    # and the caller sends it on to the orders that read the pinned packages.
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
    kind: str  # decl | file | doc | ambiguous | unknown
    subject: str
    files: list[str]
    sites: list[tuple[str, int]]
    expanded: list[str] = field(default_factory=list)
    order: str = ""  # which of RESOLUTION_ORDER answered, empty for the repository's own tree


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

    Anything the repository's own tree cannot answer is then put to the pinned packages, in the
    orders of RESOLUTION_ORDER, and is red when they all miss. This is the whole point of the
    fallback: `ModelTheory/Semantics.lean:1067` is a true citation into Mathlib that the
    repo-only index called a nonexistent file, while `Finset.not_mem_empty` -- a name invented
    this session, at the cost of nine compile cycles -- was invisible in either direction. The
    fallback makes the gate read both, and read them the same way it reads our own sources.
    """

    token = token.strip()
    if not token:
        return Resolved("unknown", token, [], [])
    files, external = resolve_file(token, index)
    explicit = "/" in token or token.rsplit(".", 1)[-1] in FILE_EXT
    ext = external_index() if may_be_external(token, explicit) else External(False, [])
    if explicit:
        # An unresolvable path is reported, not excused: `docs/history/gone.md:326` is a
        # citation to a file that is not in the repo, and an upstream path written without
        # its `Mathlib/` root cannot be checked as written.
        if not files:
            hits, order = resolve_external_file(token, ext)
            if len(hits) > 1:
                return Resolved("ambiguous", token, hits, [], [], order)
            if hits:
                return Resolved("file", token, hits, [], [], order)
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
    tails: list[str] = []
    if key.startswith("_"):
        tails = sorted({n for n in index.decl_full if n.endswith(key)})
        if len(tails) == 1:
            only = tails[0]
            return Resolved("decl", token, sorted({f for f, _ in index.decl[only]}),
                            index.decl[only], tails)
    # Neither the repository nor a shorthand: the pinned packages get their turn at being asked
    # whether this declaration exists, and only then is the name declared absent. The qualified
    # site list is the arbiter, not the candidate list -- `Quot.sound` has candidates (tens of
    # files declare some `sound`) and no qualified site, and reading that as a resolution is
    # exactly the invented-Mathlib-name the gate exists to catch.
    ext_sites = external_decl_sites(token, ext)
    if ext_sites:
        return Resolved("decl", token, sorted({f for f, _ in ext_sites}), ext_sites, [],
                        ext_order([f for f, _ in ext_sites], ext))
    return Resolved("unknown", token, [], [], tails or heads)


def ext_order(paths: list[str], ext: External) -> str:
    """Which resolution order a name or path came from, so the report can say so."""

    for tier in ext.tiers:
        root = tier_label_root(tier.label)
        if any(rel.startswith(root) for rel in paths):
            return tier.label
    return ""


def tier_label_root(label: str) -> str:
    """The path prefix a tier owns: `.lake/packages/mathlib/`, or the vendored port root."""

    if label == RESOLUTION_ORDER[3]:
        return SOURCE_ROOT.relative_to(ROOT).as_posix() + "/External/"
    return LAKE_PACKAGES.relative_to(ROOT).as_posix() + "/" + (
        "mathlib/" if label == RESOLUTION_ORDER[1] else ""
    )


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


#: Citations into the pinned sources, recorded because `python-gates` checks out the repository
#: without `.lake/packages` and cannot re-read them there. Each entry was resolved where the
#: root IS present, at the rev named below. A pinned citation NOT in this record stays red in
#: that checkout, so growing the docs means adding a verified line here or going red -- the
#: record is a whitelist the docs have to grow into, never a blanket excuse.
#: The cited line is part of the answer, not decoration: a record keyed on the file alone would
#: excuse `Semantics.lean:1` as readily as the line the doc means. `0` is the one entry that
#: carries no line, because a declaration name is cited without one.
PIN_RECORD: dict[str, int] = {
    "ModelTheory/Semantics.lean": 1067,   # theorem nonempty_iff
    "Satisfiability.lean": 65,            # def IsSatisfiable
    "Mathlib/ModelTheory/Satisfiability.lean": 65,
    "Mathlib/Order/GaloisConnection/Defs.lean": 41,   # def GaloisConnection
    "Finset.filter_congr": 0,             # Mathlib/Data/Finset/Filter.lean:176 theorem filter_congr
}

#: The rev `proofs/lean/juris_lean/lake-manifest.json` pins mathlib to, which every entry above
#: was read from. A copy of a pinned tree is only true while the pin holds, so the record is
#: consulted only while this string still matches the manifest: after a pin bump the citations
#: go back to red until someone re-reads them where the sources are on disk. That re-binding is
#: what makes the comment above a mechanism rather than a hope.
PIN_RECORD_REV = "c5ea00351c28e24afc9f0f84379aa41082b1188f"
LAKE_MANIFEST = ROOT / "proofs" / "lean" / "juris_lean" / "lake-manifest.json"


def pinned_mathlib_rev() -> str:
    """The rev the manifest names for mathlib, or "" when it cannot be read."""

    try:
        manifest = json.loads(LAKE_MANIFEST.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return ""
    for package in manifest.get("packages", []):
        if package.get("name") == MATHLIB_PACKAGE:
            return str(package.get("rev", ""))
    return ""


def pin_record_authoritative() -> bool:
    """Whether the recorded citations still speak for this checkout.

    An unreadable manifest withdraws the record: `unverifiable` is not `verified`, and a gate
    that excuses citations because it could not read its own evidence is the silence this file
    was rewritten to remove.
    """

    rev = pinned_mathlib_rev()
    return bool(rev) and rev == PIN_RECORD_REV


def answered_by_pin_record(ref, label: str) -> bool:
    """True when the pinned sources are absent and this citation is one the record covers.

    Deliberately silent while `.lake/packages` is on disk: there the walk is the authority,
    and a stale record must never be able to excuse a citation the live sources contradict.
    Silent too once the manifest names a different rev, or cannot be read at all.
    A declaration name carries no line of its own, so only the file anchors are line-bound.
    """

    want = PIN_RECORD.get(ref.subject)
    if want is None or LAKE_PACKAGES.is_dir() or not pin_record_authoritative():
        return False
    return want == 0 or f":{want}" in label


def describe(res: Resolved) -> str:
    if res.kind in ("file", "doc", "ambiguous"):
        return ", ".join(res.files[:3]) or "no such file"
    return ", ".join(f"{f}:{ln}" for f, ln in res.sites[:3])


def lake_rel() -> str:
    """The pinned-sources root as the report prints it, however it was configured.

    A message builder must not be the thing that crashes the gate: a root outside the repository
    (a shared build directory, a test that points the fallback somewhere else) would otherwise
    raise out of `relative_to` while the report was being written.
    """

    try:
        return LAKE_PACKAGES.relative_to(ROOT).as_posix()
    except ValueError:
        return LAKE_PACKAGES.as_posix()


def orders_exhausted(token: str) -> str:
    """Why a miss is a miss, naming the four orders that were asked and the root that may be
    missing from this machine -- a citation into a pinned package that the checkout does not
    carry is a different finding from a citation into a file that never existed, and the report
    must not let the two look alike."""

    note = f"no path or name answers {token} in the four resolution orders ({ORDER_FOUR})"
    if not LAKE_PACKAGES.is_dir():
        note += (f"; orders 2 and 3 could not run because the pinned sources are not on disk "
                 f"here ({lake_rel()} is absent)")
    return note


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
    if res.kind == "ambiguous":
        return "ambiguous", (
            f"{label} is ambiguous: {len(res.files)} files answer it in the pinned sources "
            f"[{describe(res)} ...] -- cite which one, the gate will not pick a line number "
            f"out of an arbitrary file of the same name")
    if res.kind == "unknown":
        if excused(ref.subject):
            return None
        hint = f" (nearest declared name: {res.expanded[0]})" if res.expanded else ""
        # A dotted name is the shape a Mathlib citation takes, and this gate is where a
        # guessed one has to die: `Finset.not_mem_empty`, `decide_pos` and `Finset.mem_prod`
        # were each written as fact and each cost a compile cycle before the checker said no.
        said = f" no such declaration or file{hint}"
        if "." in ref.subject:
            if answered_by_pin_record(ref, label):
                return None
            said = f" -- {orders_exhausted(ref.subject)}{hint}"
        return "missing", f"{label}{said}"
    if res.kind in ("file", "doc"):
        if not res.files:
            if res.kind == "doc":
                return "missing", f"{label} no such document"
            if answered_by_pin_record(ref, label):
                return None
            return "missing", f"{label} -- {orders_exhausted(ref.subject)}"
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
    """A resident named beside a declaration anchor must sit in the same line window.

    A resident that *is* the cited name is not demanded a second time. The declaration check
    has already landed this line on that name's declaration site, and an upstream source
    declares it qualified -- `def GaloisConnection.toGaloisInsertion` at
    Mathlib/Order/GaloisConnection/Defs.lean:243 -- where the word-boundary probe reads the
    true line as a miss because the name sits behind a dot. That is a shape of the source, not
    a drift in the doc, and calling it drift would teach the owner to distrust the gate.
    """

    subject = ref.subject or ""
    keep = [r for r in ref.residents
            if r != subject and not r.endswith("." + subject) and not subject.endswith("." + r)]
    if not keep:
        return True
    probe = Ref(ref.doc, ref.line, ref.subject, ref.lo, ref.hi, keep,
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
    if "." in name:
        if (PIN_RECORD.get(name) == 0 and not LAKE_PACKAGES.is_dir()
                and pin_record_authoritative()):
            return None
        return "missing", (f"{name} -- {orders_exhausted(name)} (cited beside {confirming[0]})")
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
    buckets: dict[str, list[str]] = {"drift": [], "missing": [], "ambiguous": [], "unbound": []}
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
    never point a wrong file at a plausible line, and nothing resolved in the pinned packages
    is rewritten at all -- see the order check below.
    """

    if ref.subject is None or ref.hi is not None:
        return None
    if res.order:
        # An upstream line number is not ours to move: the pin can shift under the doc, and a
        # repair that rewrites a citation to wherever Mathlib happens to sit today turns a doc
        # claim into a snapshot of this checkout. Red is the honest answer for the owner to fix.
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
        hard = buckets["drift"] + buckets["missing"] + buckets["ambiguous"]
        totals["drift"] += len(buckets["drift"])
        totals["missing"] += len(buckets["missing"])
        totals["ambiguous"] += len(buckets["ambiguous"])
        totals["unbound"] += len(buckets["unbound"])
        if not hard and not buckets["unbound"]:
            print(f"{show(doc)}: anchors current")
        else:
            print(f"{show(doc)}: {len(hard)} stale anchors, {len(buckets['unbound'])} unbound")
        for heading, key in (("drift", "drift"), ("no such name or file", "missing"),
                             ("ambiguous external file", "ambiguous"),
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
    if args.explain:
        print(f"  [{external_summary()}]")
        print(f"  [resolution orders: {ORDER_FOUR}]")
    total = totals["drift"] + totals["missing"] + totals["ambiguous"]
    if total:
        print(f"doc anchor drift: {total} stale "
              f"({totals['drift']} line drift, {totals['missing']} name or file absent, "
              f"{totals['ambiguous']} ambiguous external file); "
              f"{totals['unbound']} unbound are advisory. Run --fix where unambiguous.")
        return 1
    return 0


def external_summary() -> str:
    """What the pinned-source index cost this run, or the fact that nothing needed it.

    A gate that silently reads 100 MB and a gate that does not are different tools; the second
    one is also what a fresh CI checkout gets, so the run says which it was.
    """

    ext = _EXTERNAL
    if ext is None:
        return "external index: never needed, no citation left the repository tree"
    if not ext.present:
        return (f"external index: roots ABSENT, {len(ext.tiers[-1].paths)} vendored port files "
                f"only -- {lake_rel()} is not on disk")
    names = (f"{ext.names} declaration names read, {len(ext.sites)} names followed to a line"
             if ext.scanned else "declaration names not needed")
    return f"external index: {ext.files} pinned .lean files walked, {names}"


if __name__ == "__main__":
    raise SystemExit(main())
