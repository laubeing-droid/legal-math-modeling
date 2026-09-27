"""Read the kernel's answer: fail if an audited declaration depends on `sorryAx`.

`lean-full-clean-build` runs `lake env lean JurisLean/AxiomAudit.lean` into
`axiom-audit.raw.txt` and uploads the log. Until now nothing read it. The step
still fails when the file does not elaborate, so an unknown name is caught, but a
theorem closed by `sorry` elaborates fine and prints `depends on axioms: [sorryAx]`
-- exactly the thing this repository's first rule forbids. The textual guard scan
catches the *word* `sorry` in source; only this log shows what the kernel was
actually told a proof rests on, including proofs that never wrote the word.

Standard axioms are reported, not rejected: Mathlib results legitimately depend on
`propext`, `Quot.sound` and `Classical.choice`. Anything outside that vocabulary,
`sorryAx` above all, is a failure.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

TARGET = re.compile(r"'(.+)' depends on axioms: \[([^\]]*)\]")
CLEAN = re.compile(r"'(.+)' does not depend on any axioms")
STANDARD_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}


def parse(text: str) -> dict:
    targets: dict[str, list[str]] = {}
    for m in TARGET.finditer(text):
        name, axioms = m.group(1), m.group(2).strip()
        targets[name] = [a.strip() for a in axioms.split(",") if a.strip()] if axioms else []
    for m in CLEAN.finditer(text):
        targets.setdefault(m.group(1), [])
    vocabulary: dict[str, int] = {}
    for axioms in targets.values():
        for axiom in axioms:
            vocabulary[axiom] = vocabulary.get(axiom, 0) + 1
    offenders = {n: a for n, a in targets.items() if set(a) - STANDARD_AXIOMS}
    sorry = {n: a for n, a in targets.items() if "sorryAx" in a}
    return {
        "audited_targets": len(targets),
        "axiom_vocabulary": dict(sorted(vocabulary.items())),
        "targets_with_sorryAx": dict(sorted(sorry.items())),
        "targets_outside_standard_axioms": dict(sorted(offenders.items())),
    }


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--log", required=True, type=Path)
    ap.add_argument("--json", type=Path, default=None)
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--min-targets", type=int, default=1)
    args = ap.parse_args(argv)

    text = args.log.read_text(encoding="utf-8", errors="replace")
    doc = parse(text)
    doc["schema_version"] = "axiom-audit-log-v1"
    doc["log"] = str(args.log)
    doc["standard_axioms_allowed"] = sorted(STANDARD_AXIOMS)
    doc["status"] = (
        "FAIL_SORRYAX" if doc["targets_with_sorryAx"]
        else "FAIL_NONSTANDARD_AXIOM" if doc["targets_outside_standard_axioms"]
        else "PASS"
    )
    if args.json:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(json.dumps(doc, ensure_ascii=False, indent=2) + "\n",
                             encoding="utf-8")
    if not args.check:
        print(json.dumps(doc, ensure_ascii=False, indent=2))
        return 0

    problems = []
    if doc["targets_with_sorryAx"]:
        problems.append(f"{len(doc['targets_with_sorryAx'])} audited target(s) close on sorryAx: "
                        + ", ".join(sorted(doc["targets_with_sorryAx"])[:5]))
    if doc["targets_outside_standard_axioms"]:
        problems.append("axioms outside the standard vocabulary: "
                        + ", ".join(sorted(set(
                            a for v in doc["targets_outside_standard_axioms"].values()
                            for a in v))))
    if doc["audited_targets"] < args.min_targets:
        problems.append(f"log names {doc['audited_targets']} targets, expected at least "
                        f"{args.min_targets}: the audit printed nothing, which is not a pass")
    if problems:
        for p in problems:
            print(f"AXIOM AUDIT FAIL: {p}", file=sys.stderr)
        return 1
    print(f"axiom audit ok: {doc['audited_targets']} targets, vocabulary "
          f"{sorted(doc['axiom_vocabulary']) or ['(none)']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
