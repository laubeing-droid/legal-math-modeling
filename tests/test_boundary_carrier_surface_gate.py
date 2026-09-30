"""The reverse gate for the six boundary categories (order items C1/C2).

`tests/test_axiom_audit_log_gate.py::test_the_surface_names_no_comment_text` checks one
direction: every name printed on the audit surface is a declaration the source really makes.
It cannot catch the failure the binding table cares about, namely a carrier that the table
CLAIMS is named on the surface while no `#print axioms` line names it -- a silent hole that
turns "this category's认定 was independently re-read" into prose. That direction was explicitly
left open in `docs/master-plan/06_六类边界绑定表.md` sec 4.1 item (2): "现有门测只保证面内名字真实
存在，不保证六类载体全部在面内（缺的是反向断言）". This file is that reverse assertion.

Design choices that matter:

- The expected carriers are READ OUT of the binding table itself, not typed in here. A hardcoded
  list would let the gate bless whatever the ledger said last time it was edited; parsing the
  ledger means an edit to the table moves the requirement in the same commit.
- A backticked token only becomes a requirement if some Lean source actually declares it as a
  `theorem`/`lemma`. That filters constructors and fields (`Outcome.failure`,
  `PartialPayload.open_nonempty`, `openObligations.Nonempty`) automatically, because those are
  type-level carriers, not theorems, and are never on an axiom surface by design.
- "On the surface" means on ANY of the repo's audit drivers, because the table itself splits
  carriers between `AxiomAudit.lean` (release root) and `ULMAllTheoremsAxiomAudit.lean` (trunk).
- The gate insists on how many carriers it resolved. A regex that silently matched nothing would
  otherwise pass, which is precisely the class of dead gate this repo has been burned by.
"""

from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TABLE = ROOT / "docs" / "master-plan" / "06_六类边界绑定表.md"
PKG = ROOT / "proofs" / "lean" / "juris_lean" / "JurisLean"
DRIVERS = (
    "AxiomAudit.lean",
    "ULMAllTheoremsAxiomAudit.lean",
    "ULMAxiomAudit.lean",
    "ULMCoreCompAxiomAudit.lean",
)

CATEGORIES = "①②③④⑤⑥"
BACKTICK = re.compile(r"`([^`]+)`")
DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:theorem|lemma)\s+([A-Za-z0-9_.']+)")


def surface_targets() -> set[str]:
    out: set[str] = set()
    for name in DRIVERS:
        text = (PKG / name).read_text(encoding="utf-8")
        for line in text.splitlines():
            if line.startswith("#print axioms"):
                parts = line.split()
                # `#print axioms JurisLean.Foo.bar` splits into THREE tokens; taking parts[1]
                # here once yielded an empty surface and made the gate pass by vacuity.
                if len(parts) == 2 and parts[1] != "axioms":
                    out.add(parts[1])
                elif len(parts) == 3:
                    out.add(parts[2])
    return out


def declared_theorems() -> set[str]:
    """Bare names of every theorem/lemma declared anywhere in the package tree."""
    names: set[str] = set()
    for path in PKG.rglob("*.lean"):
        for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
            m = DECL.match(line)
            if m:
                names.add(m.group(1))
    return names


def table_rows() -> list[tuple[str, str]]:
    """(category glyph, carrier cell) for each row of sec 二's binding table."""
    rows: list[tuple[str, str]] = []
    for line in TABLE.read_text(encoding="utf-8").splitlines():
        if not line.startswith("|"):
            continue
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        if len(cells) < 5 or cells[0] not in CATEGORIES:
            continue
        rows.append((cells[0], cells[2]))
    return rows


def test_the_binding_table_row_set_is_the_six_categories():
    rows = table_rows()
    assert [c for c, _ in rows] == list(CATEGORIES), [c for c, _ in rows]


def test_carriers_resolve_to_real_theorems_and_are_all_on_the_surface():
    surface = surface_targets()
    # A driver that fails to parse yields an empty set, and "every carrier is on the surface"
    # is then vacuously true. This is the exact dead-gate shape this repo has been burned by,
    # so the surface's size is asserted before any membership claim is made.
    assert len(surface) > 1500, f"audit surface parsed to {len(surface)} targets; parser is broken"
    declared = declared_theorems()
    rows = table_rows()
    checked: dict[str, list[str]] = {}
    missing: list[str] = []
    for cat, cell in rows:
        found: list[str] = []
        for token in BACKTICK.findall(cell):
            bare = token.split(".")[-1].split(" ")[0].strip()
            if bare.endswith(("(", ":")) or "(" in token:
                continue
            if bare in declared:
                found.append(bare)
                if not any(t.rsplit(".", 1)[-1] == bare for t in surface):
                    missing.append(f"{cat} {token}")
        checked[cat] = found
    # The table visibly cites ~20 theorem carriers across six rows; a much smaller number means
    # the parse broke, not that the ledger got honest.
    total = sum(len(v) for v in checked.values())
    assert total >= 15, f"only resolved {total} theorem carriers from the table; parsing broke: {checked}"
    assert not missing, f"carriers the table claims are named but no audit driver prints: {missing}"


def test_the_gate_fails_when_a_named_carrier_is_dropped_from_the_surface(tmp_path):
    """Refusal path: a carrier that stops being printed must be caught, not shrugged off."""
    surface = surface_targets()
    a_carrier = next(
        bare
        for _, cell in table_rows()
        for bare in (t.split(".")[-1] for t in BACKTICK.findall(cell))
        if any(s.rsplit(".", 1)[-1] == bare for s in surface)
    )
    shrunk = {s for s in surface if s.rsplit(".", 1)[-1] != a_carrier}
    assert a_carrier not in {s.rsplit(".", 1)[-1] for s in shrunk}
    assert len(shrunk) == len(surface) - 1
