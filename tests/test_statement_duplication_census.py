"""The verbatim-duplication census is the measurement behind R-04.

R-04 was booked as "migrate Genealogy's three hundred declarations onto the shared
kernel", premised on restatement. This census is what tests that premise: it counts
statements written identically in two places, and it publishes its own blind spot (the
headers it cannot read) rather than reporting a clean zero.

The counts here are deliberately not written as literals. W1b found that a literal
(`duplicated_statement_types == 8`) had baked in a scanner defect -- the comparison key
carried the declaration name, so a statement restated under a *different* name was
structurally invisible -- and the pinned figure kept the gate green while the claim it
was supposed to test was false. Each figure below is recomputed from source in the same
run, and the name-independence of the key is asserted directly, so a revert of the fix
fails instead of regenerating a new literal.
"""

from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TOOL = ROOT / "scripts" / "ci" / "build_statement_duplication_census.py"
CENSUS = ROOT / "docs" / "formal-release" / "statement_duplication_census.json"
PKG = ROOT / "proofs" / "lean" / "juris_lean" / "JurisLean"

sys.path.insert(0, str(ROOT / "scripts" / "ci"))


def _census() -> dict:
    return json.loads(CENSUS.read_text(encoding="utf-8"))


def _names(hits: list[dict]) -> set[str]:
    """The declaration names a census group is carried by.

    A carrier is `family/name`, and one family label ("root/other") contains a slash,
    so the name is whatever follows the **last** slash. Splitting on the first one
    returns `other/<name>` for every root-level module, which would make the
    name-independence guard below compare against a string no key can ever hold.
    """
    return {hit["carrier"].rsplit("/", 1)[-1] for hit in hits}


def _families(hits: list[dict]) -> set[str]:
    return {hit["carrier"].rsplit("/", 1)[0] for hit in hits}


def test_check_mode_passes_offline() -> None:
    proc = subprocess.run([sys.executable, str(TOOL), "--check"], cwd=ROOT,
                          capture_output=True, text=True, encoding="utf-8",
                          errors="replace")
    assert proc.returncode == 0, proc.stdout + proc.stderr


def test_census_records_its_own_coverage_gap() -> None:
    doc = _census()
    assert doc["inventory_package_theorems"] > 0
    # A scanner that silently reads less than the account it is checking is the failure
    # mode this whole repository was audited for, so the gap is a published number.
    # Private/protected headers are read for duplication analysis but are outside the
    # inventory's counting convention (as with `rg "^theorem "`), so the identity
    # compares public headers only.
    public = doc["statements_read"] - doc["private_protected_headers_read"]
    assert doc["headers_missed_by_scanner"] >= 0
    assert public + doc["headers_missed_by_scanner"] == \
        doc["inventory_package_theorems"]


def test_census_counts_and_key_sets_are_recomputed_not_copied() -> None:
    """Every published figure and every published key must equal an on-the-spot recount.

    This replaces `duplicated_statement_types == 8` and `cross_family_statement_types
    == 0`, which pinned a number rather than the property: the number was right about a
    wrong measurement.
    """
    from build_statement_duplication_census import scan

    doc = _census()
    live = scan()
    for field in ("files_scanned", "statements_read", "distinct_statement_types",
                  "duplicated_statement_types", "cross_family_statement_types",
                  "inventory_package_theorems", "headers_missed_by_scanner",
                  "private_protected_headers_read"):
        assert doc[field] == live[field], (
            f"{field}: the account says {doc[field]}, the source says {live[field]}; "
            "regenerate rather than editing the account"
        )
    assert set(doc["duplicates"]) == set(live["duplicates"]), (
        "the duplicated statement types in the account are not the ones in the tree"
    )
    assert set(doc["cross_family"]) == set(live["cross_family"]), (
        "the cross-family duplicates in the account are not the ones in the tree"
    )
    # cross_family is a subset of duplicates by construction; if it stopped being, the
    # two columns in the account would be counting different things.
    assert set(doc["cross_family"]) <= set(doc["duplicates"])


def test_the_comparison_key_never_carries_the_declaration_name() -> None:
    """Renamed restatements must be visible: that is the whole point of the census.

    Two guards, because a recount alone would not catch this: regenerating the account
    after a revert makes the numbers agree again while the measurement stays wrong.
    """
    doc = _census()
    # (1) no published key may start with the name of a declaration it files under it;
    # a name-inclusive key breaks this for every group, since the key would then begin
    # with the very name the group records.
    for stmt, hits in doc["duplicates"].items():
        for name in _names(hits):
            # `name` at the very start of the key, not followed by more identifier
            # characters -- that is what a name-inclusive key looks like.
            assert not re.match(re.escape(name) + r"(?![A-Za-z0-9_'])", stmt), (
                f"the statement key still carries the declaration name {name!r}: "
                f"{stmt[:120]!r} -- restatements under a new name are invisible"
            )
    # (2) the census must actually register pairs whose names differ; before the W1b fix
    # it registered eight groups and every one of them was the *same* name in two files,
    # i.e. zero evidence about renaming.
    renamed = [hits for hits in doc["duplicates"].values() if len(_names(hits)) > 1]
    assert renamed, (
        "no duplicated statement is registered under two different names, which is the "
        "signature of a key that still includes the name"
    )


def test_headers_differing_only_by_name_share_a_key() -> None:
    """Negative case for the W1b defect, fed straight to `split_header`.

    Binders stay in the key on purpose: comparing only the conclusion would let
    `theorem a (h : P) : Q` and `theorem b (h : R) : Q` read as one statement.
    """
    from build_statement_duplication_census import split_header

    first_name, first = split_header(
        "theorem bb5_trustLE_trans {a b c : TrustVector} (hab : TrustLE a b) "
        "(hbc : TrustLE b c) : TrustLE a c")
    second_name, second = split_header(
        "theorem trustLE_trans {a b c : TrustVector} (hab : TrustLE a b) "
        "(hbc : TrustLE b c) : TrustLE a c")
    assert first_name != second_name
    assert first == second, (
        "two headers identical apart from their names produced different keys, so "
        "renaming a restatement hides it from the census again"
    )
    # the counter-example to "strip everything but the conclusion"
    _n1, with_p = split_header("theorem a (h : P) : Q := hp")
    _n2, with_r = split_header("theorem b (h : R) : Q := hr")
    assert with_p != with_r, "binders left the key; a shared shape is not a duplicate"

    # and the real pair is registered in the account, not just reproducible in isolation
    doc = _census()
    registered = {
        (tuple(sorted(_names(hits))), tuple(sorted(h["path"] for h in hits)))
        for hits in doc["duplicates"].values()
    }
    assert (("bb5_trustLE_trans", "trustLE_trans"),
            tuple(sorted(["Seams/BoundaryBridge5.lean", "Seams/BoundaryClosure.lean"]))) \
        in registered, (
        "the bb5_trustLE_trans / trustLE_trans restatement left the account; either the "
        "declarations moved (regenerate and re-point this pin) or the key changed again")


def test_verbatim_duplication_is_named_and_local() -> None:
    doc = _census()
    # The gate that used to read "cross_family_statement_types == 0" now states the
    # property it was protecting: a duplicate spanning module families is new evidence,
    # and it belongs in the ledger rather than being absorbed by a merge. How many such
    # groups exist today is pinned by the recount above, so this pins only where they
    # may live.
    for stmt, hits in doc["duplicates"].items():
        assert len(hits) >= 2
        for hit in hits:
            assert (PKG / hit["path"]).exists()
    for stmt, hits in doc["cross_family"].items():
        assert len(_families(hits)) > 1, stmt[:120]
