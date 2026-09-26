"""Gates for the four mandate modules written after the Qoder audit.

The audit's judgement 4 said the five mandate items had no Lean carrier: the
win-rate pipeline, structural case comparison, the certified approximator and
game theory existed as Python contracts, registry rows, or `rfl` identities over
record fields. These four modules answer that with real, quantified theorems.

The gate exists to stop the opposite failure — a new file becoming a new
over-claim. So it checks both directions: the mathematics is there, and the
bookkeeping still says it is unverified.
"""

from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PKG = ROOT / "proofs" / "lean" / "juris_lean" / "JurisLean"
ROOT_MODULE = PKG.parent / "JurisLean.lean"
AUDIT = PKG / "AxiomAudit.lean"
REGISTRY = ROOT / "theory" / "spec" / "p_registry.json"
LEDGER = ROOT / "docs" / "master-plan" / "03_证明战役台账.md"

# mandate item -> (module, theorems that must exist, concept it serves)
# mandate item -> (module, theorems that must exist, concept it serves)
MODULES: dict[str, tuple[str, tuple[str, ...], str]] = {
    "shared_kernel": (
        "Mandate/Kernel.lean",
        ("successes_le_length", "rate_le_self", "le_max_l", "le_max_r", "max_zero",
         "best_le_best_append", "sig3_relabel_fst", "sig3_relabel_edges", "sig3_sum",
         "sig3_fst_le_sum"),
        "P-112",
    ),
    "win_rate_step_two": (
        "Mandate/CohortRate.lean",
        ("rateOfCohort_defined", "rateOfCohort_none_iff", "rateOfCohort_num_le_den",
         "rate_le_addedSuccess", "addedFailure_le_rate"),
        "P-112",
    ),
    "structural_comparison": (
        "Mandate/StructureInvariants.lean",
        ("same_labels", "signatures_differ", "sum_signature_third",
         "discrimination_survives_sum", "relabel_cannot_bridge", "sig3_double",
         "sig3_le_sum_any"),
        "P-109",
    ),
    "computed_certificate": (
        "Mandate/DerivedCertificate.lean",
        ("approx_closed", "pow_damped", "approx_error_eq_computedBound",
         "approx_damped", "certificate_bound_is_computed", "admits_iff",
         "not_admits_negative", "approx_zero"),
        "P-118",
    ),
    "game_tree": (
        "Mandate/GameTree.lean",
        ("value_leaf", "value_nil", "value_cons", "value_ge_head",
         "value_ge_of_mem", "value_node_append_le", "value_of_leaves"),
        "P-090",
    ),
}

# Modules that must *consume* the kernel instead of restating its carriers.
KERNEL_CONSUMERS = (
    "Mandate/CohortRate.lean",
    "Mandate/StructureInvariants.lean",
    "Mandate/GameTree.lean",
)

# Declared exactly once, in the kernel, and nowhere else in Mandate/.
SINGLE_DECLARATIONS = (
    "structure Rate where",
    "structure CaseStructure where",
    "infix:50",
    "theorem le_max_l",
    "theorem successes_le_length",
    "def sig3 ",
    "def successes ",
)

DECL = re.compile(r"^(?:@\[[^\]]*\][ \t]*)*theorem\s+([^\s(:{]+)", re.M)
FORBIDDEN = re.compile(r"\bsorry\b|\badmit\b|\bnative_decide\b|^\s*axiom\b")


def _strip_comments(text: str) -> str:
    out_lines = []
    depth = 0
    for line in text.splitlines():
        res = []
        i = 0
        in_string = False
        while i < len(line):
            ch = line[i]
            nxt = line[i + 1] if i + 1 < len(line) else ""
            if depth > 0:
                if ch == "/" and nxt == "-":
                    depth += 1
                    i += 2
                    continue
                if ch == "-" and nxt == "/":
                    depth -= 1
                    i += 2
                    continue
                i += 1
                continue
            if not in_string and ch == "-" and nxt == "-":
                break
            if not in_string and ch == "/" and nxt == "-":
                depth += 1
                i += 2
                continue
            if ch == '"':
                in_string = not in_string
            res.append(ch)
            i += 1
        depth_now = depth
        out_lines.append("".join(res) if depth_now == 0 else "")
    return "\n".join(out_lines)


def _text(rel: str) -> str:
    return (PKG / rel).read_text(encoding="utf-8")


def test_every_mandate_module_exists_with_real_theorems() -> None:
    for item, (rel, required, _concept) in MODULES.items():
        path = PKG / rel
        assert path.exists(), f"{item}: missing module {rel}"
        names = set(DECL.findall(_strip_comments(path.read_text(encoding="utf-8"))))
        missing = [n for n in required if n not in names]
        assert not missing, f"{item}: required theorems absent: {missing}"
        assert len(names) >= 5, f"{item}: only {len(names)} theorems"


def test_mandate_modules_use_no_forbidden_constructs() -> None:
    for item, (rel, _req, _concept) in MODULES.items():
        code = _strip_comments(_text(rel))
        hits = [l for l in code.splitlines() if FORBIDDEN.search(l)]
        assert not hits, f"{item}: {rel} has {hits[:3]}"


GENERAL_NOT_WITNESS: dict[str, tuple[str, ...]] = {
    "shared_kernel": ("successes_le_length", "rate_le_self", "le_max_l", "le_max_r",
                      "max_zero", "best_le_best_append", "sig3_relabel_fst", "sig3_sum"),
    "win_rate_step_two": ("rateOfCohort_defined", "rateOfCohort_none_iff",
                          "rateOfCohort_num_le_den", "rate_le_addedSuccess",
                          "addedFailure_le_rate"),
    "structural_comparison": ("sum_signature_third", "discrimination_survives_sum",
                              "relabel_cannot_bridge", "sig3_double",
                              "sig3_le_sum_any"),
    "computed_certificate": ("approx_closed", "pow_damped",
                             "approx_error_eq_computedBound", "approx_damped",
                             "certificate_bound_is_computed", "admits_iff",
                             "not_admits_negative"),
    "game_tree": ("value_cons", "value_ge_head", "value_ge_of_mem",
                  "value_node_append_le", "value_of_leaves",
                  "value_ignores_payoff_renaming_when_dominated"),
}


def test_mandate_modules_prove_general_statements_not_witnesses() -> None:
    """The disease being replaced was `rfl` over a record field: demand binders.

    Only the listed theorems are held to this, and each module lists at least
    five, so a module cannot pass by carrying one quantified lemma plus witnesses.
    """
    for item, (rel, _req, _concept) in MODULES.items():
        names = GENERAL_NOT_WITNESS[item]
        assert len(names) >= 5, item
        text = _strip_comments(_text(rel))
        for name in names:
            m = re.search(r"^theorem\s+" + re.escape(name), text, re.M)
            assert m, f"{item}: general theorem {name} absent"
            rest = text[m.start():].split(":=", 1)[0]
            assert re.search(r"[({]|∀", rest), f"{item}::{name} binds no variable"


def test_mandate_modules_are_not_claimed_as_verified() -> None:
    """They may not enter the root or the audit surface before a CI module build."""
    root_text = ROOT_MODULE.read_text(encoding="utf-8")
    audit_text = AUDIT.read_text(encoding="utf-8")
    for item, (rel, _req, _concept) in MODULES.items():
        mod = "JurisLean." + rel[:-5].replace("/", ".")
        assert f"import {mod}" not in root_text, f"{item} reached the release root"
        assert mod not in audit_text, f"{item} reached the axiom-audit surface"


def test_ledger_records_the_mandate_wave_as_pending_ci() -> None:
    text = LEDGER.read_text(encoding="utf-8")
    m = re.search(r"军令件补写", text)
    assert m, "the campaign ledger must record the mandate wave"
    tail = text[m.start():m.start() + 2500]
    assert "CI_NOT_RUN" in tail, "the mandate wave must be labelled unverified"


def test_registry_not_yet_upgraded_with_unverified_anchors() -> None:
    """A CI_NOT_RUN module may not silently become a concept's Lean anchor."""
    import json

    entries = {e["id"]: e for e in json.loads(REGISTRY.read_text(encoding="utf-8"))["entries"]}
    for item, (rel, _req, concept) in MODULES.items():
        files = {a["file"] for a in entries[concept]["anchors"]}
        assert not any(rel.split("/")[-1] in f for f in files), (
            f"{concept} is anchored to {rel} before CI has built it"
        )


def test_mandate_modules_reuse_the_kernel_instead_of_restating_it() -> None:
    """Audit judgement 1: the old line declared a fresh model per theorem.

    Each consumer must import and open the kernel, and the shared carriers may be
    declared in exactly one file, so a later module cannot quietly fork its own
    `Rate` or `CaseStructure` again.
    """
    for rel in KERNEL_CONSUMERS:
        text = _text(rel)
        assert "import JurisLean.Mandate.Kernel" in text, f"{rel} does not import the kernel"
        assert re.search(r"^open JurisLean\.Mandate\.Kernel", text, re.M), f"{rel} does not open it"

    files = sorted((PKG / "Mandate").glob("*.lean"))
    for decl in SINGLE_DECLARATIONS:
        owners = [f.name for f in files if decl in _strip_comments(f.read_text(encoding="utf-8"))]
        assert owners == ["Kernel.lean"], f"{decl!r} declared in {owners}, not only in the kernel"


def test_kernel_is_still_quarantined() -> None:
    text = ROOT_MODULE.read_text(encoding="utf-8")
    assert "JurisLean.Mandate" not in text, "the kernel reached the release root before CI"
