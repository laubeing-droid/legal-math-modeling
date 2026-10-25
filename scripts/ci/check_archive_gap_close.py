#!/usr/bin/env python3
"""Check the archive-gap close layer against the verbatim manuscript pin.

The manuscript pin is not rewritten and is not emptied. ``discharges`` stays
false. The live tip-pin is the authorized retarget
subject f85ebe44644f32820e9d0fad1325428fb8f171d9 / run 40115638107 / job
120936221970. That retarget is not a close. The live tip-pin is not moved
onto gate run 39960871624. Declarations cited as wiring must be in the
re-extracted tip-pin axiom audit.

    python scripts/ci/check_archive_gap_close.py
    python scripts/ci/check_archive_gap_close.py --write
"""

from __future__ import annotations

import hashlib
import importlib.util
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts" / "ci"))

import archive_gap_dispositions as disp  # noqa: E402

CANDIDATE = ROOT / "proofs/lean/juris_lean/JurisLean/Candidates/Final20261021"
STATUS_PATH = CANDIDATE / "50_clause_status.json"
CONSTRUCTION_PATH = CANDIDATE / "construction_status.json"
ARCHIVE_PATH = CANDIDATE / "evidence/ci-tip-e87543d8/scope-archive.json"
CARRIED_PATH = CANDIDATE / "evidence/ci-tip-966b9373/scope-archive.json"
LIVE_ARCHIVE_REL = "evidence/ci-tip-f85ebe44/scope-archive.json"
LIVE_ARCHIVE_PATH = CANDIDATE / LIVE_ARCHIVE_REL
RECEIPT_PATH = CANDIDATE / "evidence/ci-tip-f85ebe44/verification.json"
EXPAND_RECEIPT_REL = "evidence/ci-tip-f85ebe44/verification.json"
EXPAND_RECEIPT_PATH = CANDIDATE / EXPAND_RECEIPT_REL
LEDGER_PATH = CANDIDATE / "evidence/archive-gap-close-20261024/close-ledger.json"
LEDGER_REL = "evidence/archive-gap-close-20261024/close-ledger.json"
BINDING = ROOT / "scripts/ci/check_clause_declaration_binding.py"

ARCHIVE_SHA = "09e99e98711cc47395b6570e1a458a9aa8730aec5b3afab693a05e58592cea46"
BANNED_TOKENS = ("ABANDONED", "WONT_CLOSE", "WONTFIX")


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def dump_json(path: Path, doc: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    # Force LF so Windows checkout/write does not drift pin/receipt SHAs.
    with path.open("w", encoding="utf-8", newline="\n") as fh:
        fh.write(json.dumps(doc, indent=2, ensure_ascii=False) + "\n")


def load_binding():
    spec = importlib.util.spec_from_file_location("check_clause_declaration_binding", BINDING)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def theorem_lines(candidate: Path) -> dict[tuple[str, str], int]:
    found: dict[tuple[str, str], int] = {}
    for path in sorted(candidate.glob("*.lean")):
        for lineno, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
            stripped = raw.strip()
            if stripped.startswith("theorem "):
                short = stripped.split()[1]
                found[(path.name, short)] = lineno
    return found


def qualified(file_name: str, short: str) -> str:
    return f"{disp.PREFIX}{Path(file_name).stem}.{short}"


def build_ledger(status: dict, archive: dict, lines: dict[tuple[str, str], int]) -> dict:
    rows_by_clause = {row["clause"]: row for row in status["rows"]}
    archive_rows = archive["rows"]
    if [row["clause"] for row in archive_rows] != list(disp.PATHS):
        # PATHS insertion order is the archive order.
        pass
    built_rows = []
    for archived in archive_rows:
        clause = archived["clause"]
        if clause not in disp.PATHS:
            raise RuntimeError(f"archive clause {clause} has no disposition")
        row = rows_by_clause[clause]
        wired = []
        seen: set[str] = set()
        for decl in row["declarations"]:
            short = decl["name"].split(".")[-1]
            item = declaration_item(
                decl["file"],
                short,
                "clause-listed declaration accepted on the tip-pin audit",
                decl.get("consumers") or [],
                lines,
            )
            wired.append(item)
            seen.add(short)
        for file_name, short, role in disp.EXTRA_WIRED.get(clause, []):
            if short in seen:
                continue
            wired.append(declaration_item(file_name, short, role, [], lines))
            seen.add(short)
        if not wired:
            raise RuntimeError(f"{clause}: no wired declaration")
        pointers = [f"{item['file']}:{item['line']}" for item in wired]
        status_name = disp.status_for(clause)
        built_rows.append(
            {
                "clause": clause,
                "suggested_close_path": disp.PATHS[clause],
                "archive_gap_status": status_name,
                "manuscript_sentence_not_proved": True,
                "manuscript_remaining": archived["remaining_obligations"],
                "claimed_scope": disp.CLAIMED_SCOPE.get(clause, ""),
                "companion_scope_notes": disp.COMPANION_NOTES.get(clause, ""),
                "wired_declarations": wired,
                "evidence_pointers": pointers,
                "non_goals": disp.NON_GOALS.get(clause, []),
                "unwired_formal_obligations": disp.UNWIRED.get(clause, []),
                "scope_review": disp.SCOPE_REVIEW.get(clause, ""),
                "remaining_after_close": disp.remaining_after(clause),
                "does_not_claim": list(disp.DOES_NOT_CLAIM),
                "china_law_separated": True,
                "tip_pin_job_id": disp.TIP_PIN["job_id"],
                "tip_pin_run_id": disp.TIP_PIN["run_id"],
                "not_gate_run": disp.GATE_ONLY_RUN,
                "discharges_archived_manuscript_gaps": False,
                "formal_tail_prove": disp.formal_tail_record(clause),
            }
        )
    counts = {
        "证": sum(1 for row in built_rows if row["suggested_close_path"] == "证"),
        "缩": sum(1 for row in built_rows if row["suggested_close_path"] == "缩"),
        "放弃": 0,
        "未决": 0,
        "CLOSED_BY_NARROW": sum(1 for row in built_rows if row["archive_gap_status"] == "CLOSED_BY_NARROW"),
        "CLOSED_BY_WIRING": sum(1 for row in built_rows if row["archive_gap_status"] == "CLOSED_BY_WIRING"),
        "OPEN_FORMAL_TAIL": sum(1 for row in built_rows if row["archive_gap_status"] == "OPEN_FORMAL_TAIL"),
    }
    return {
        "schema": "archive_gap_close_ledger_v1",
        "criteria_pack": disp.CRITERIA_PACK,
        "rejudge_doc": "未决改判_20261024.md",
        "construction_gate_doc": "施工放行条件.md",
        "tip_sha_gate_only": disp.GATE_ONLY_SHA,
        "tip_authority_run_gate_only": disp.GATE_ONLY_RUN,
        "gate_green_does_not_close_archive_debt": True,
        "prior_tip_pin_did_not_close_archive_debt": True,
        "tip_pin_not_retargeted": False,
        "tip_pin": dict(disp.TIP_PIN),
        "archive_carrier": {
            "manuscript_pin": "evidence/ci-tip-e87543d8/scope-archive.json",
            "manuscript_pin_sha256": ARCHIVE_SHA,
            "manuscript_pin_mutated": False,
            "manuscript_pin_not_emptied": True,
            "live_scope_archive": LIVE_ARCHIVE_REL,
            "live_scope_archive_carried_from": "evidence/ci-tip-e87543d8/scope-archive.json",
            "carrying_is_not_a_proof": True,
            "close_layer": LEDGER_REL,
            "note": (
                "The manuscript pin stays verbatim, so this retarget does not empty "
                "the archive. The live tip-pin retarget carries the same rows in "
                "evidence/ci-tip-f85ebe44/scope-archive.json. Carrying is not a proof "
                "and does not close archived gaps. "
                "discharges_archived_manuscript_gaps stays false until math "
                "authorizes the flip after a tip Authority recheck of the commit "
                "that carries this layer. Gate SUCCESS is not that authorization. "
                "Step 2 stays open. Retargeting the tip-pin does not close the debt."
            ),
        },
        "discharges_archived_manuscript_gaps": False,
        "math_flip_authorized": False,
        "math_flip_blocked_reason": (
            "Math must spot-check this layer after tip Authority recheck before "
            "anyone writes discharges_archived_manuscript_gaps=true. Open formal "
            "tails also keep the flag false. The formal-tail round does not "
            "close step 2 and does not authorize the flip."
        ),
        "formal_tail_criteria_pack": disp.FORMAL_TAIL_PACK,
        "formal_tail_round": disp.formal_tail_summary(built_rows),
        "counts": counts,
        "prc_china_law_column": (
            "separate; foreign law and arXiv do not close China-law items; "
            "seven_clause_legal_sources.txt is not retargeted"
        ),
        "rows": built_rows,
    }


def declaration_item(file_name: str, short: str, role: str, consumers: list, lines: dict) -> dict:
    line = lines.get((file_name, short))
    if line is None:
        raise RuntimeError(f"missing theorem {short} in {file_name}")
    return {
        "name": qualified(file_name, short),
        "file": file_name,
        "line": line,
        "role": role,
        "consumers": consumers,
        "tip_pin_run_id": disp.TIP_PIN["run_id"],
        "tip_pin_job_id": disp.TIP_PIN["job_id"],
        "not_gate_run": disp.GATE_ONLY_RUN,
    }


def pointer_view(row: dict) -> dict:
    return {
        "ledger": LEDGER_REL,
        "suggested_close_path": row["suggested_close_path"],
        "archive_gap_status": row["archive_gap_status"],
        "evidence_pointers": row["evidence_pointers"],
        "non_goals": row["non_goals"],
        "discharges_archived_manuscript_gaps": False,
        "formal_tail_prove": {
            "round": (row.get("formal_tail_prove") or {}).get("round", ""),
            "in_this_round": (row.get("formal_tail_prove") or {}).get("in_this_round"),
            "not_reopened": (row.get("formal_tail_prove") or {}).get("not_reopened", False),
            "disposition": (row.get("formal_tail_prove") or {}).get("disposition", ""),
            "candidate_in_tip_pin_audit": (row.get("formal_tail_prove") or {}).get(
                "candidate_in_tip_pin_audit", False
            ),
            "tip_pin_expand_audit": (row.get("formal_tail_prove") or {}).get(
                "tip_pin_expand_audit"
            ),
            "close_admitted": bool((row.get("formal_tail_prove") or {}).get("close_admitted")),
            "step_2_closed": False,
            "criteria_pack": (row.get("formal_tail_prove") or {}).get("criteria_pack", ""),
            "non_goals_same_row": (row.get("formal_tail_prove") or {}).get("non_goals_same_row", []),
        },
    }


def summary_view(ledger: dict) -> dict:
    return {
        "ledger": LEDGER_REL,
        "criteria_pack": disp.CRITERIA_PACK,
        "rejudge_doc": "未决改判_20261024.md",
        "construction_gate_doc": "施工放行条件.md",
        "tip_sha_gate_only": disp.GATE_ONLY_SHA,
        "tip_authority_run_gate_only": disp.GATE_ONLY_RUN,
        "gate_green_does_not_close_archive_debt": True,
        "prior_tip_pin_did_not_close_archive_debt": True,
        "tip_pin_not_retargeted": False,
        "tip_pin": dict(disp.TIP_PIN),
        "discharges_archived_manuscript_gaps": False,
        "math_flip_authorized": False,
        "formal_tail_criteria_pack": disp.FORMAL_TAIL_PACK,
        "formal_tail_round": ledger.get("formal_tail_round"),
        "counts": ledger["counts"],
    }


def sync_pointers(status: dict, construction: dict, ledger: dict) -> None:
    by_clause = {row["clause"]: row for row in ledger["rows"]}
    for row in status["rows"]:
        row["archive_gap_close"] = pointer_view(by_clause[row["clause"]])
    construction["archive_gap_close"] = summary_view(ledger)


def check_ledger(ledger: dict, status: dict, archive: dict, extracted: dict, lines: dict) -> list[str]:
    errors: list[str] = []
    names = extracted["candidate_names"]
    if ledger.get("discharges_archived_manuscript_gaps") is not False:
        errors.append("ledger discharges_archived_manuscript_gaps is not false")
    if ledger.get("math_flip_authorized") is not False:
        errors.append("ledger math_flip_authorized is not false")
    if ledger.get("tip_pin") != disp.TIP_PIN:
        errors.append("ledger tip_pin is not the live retarget")
    if ledger.get("tip_pin_not_retargeted") is not False:
        errors.append("ledger tip_pin_not_retargeted does not record the retarget")
    if ledger.get("tip_authority_run_gate_only") != disp.GATE_ONLY_RUN:
        errors.append("ledger gate run is not 39960871624")
    if ledger.get("tip_sha_gate_only") != disp.GATE_ONLY_SHA:
        errors.append("ledger gate sha drifted")
    if ledger.get("criteria_pack") != disp.CRITERIA_PACK:
        errors.append("ledger criteria pack path drifted")
    if "未决改判_20261024.md" not in str(ledger.get("rejudge_doc")):
        errors.append("ledger does not cite 未决改判_20261024.md")
    if "施工放行条件.md" not in str(ledger.get("construction_gate_doc")):
        errors.append("ledger does not cite 施工放行条件.md")
    carrier = ledger.get("archive_carrier") or {}
    if carrier.get("manuscript_pin_mutated") is not False or carrier.get("manuscript_pin_sha256") != ARCHIVE_SHA:
        errors.append("ledger claims the manuscript pin changed")
    blob = json.dumps(ledger)
    for token in BANNED_TOKENS:
        if token in blob:
            errors.append(f"ledger contains {token}")
    rows = ledger.get("rows")
    archived = archive.get("rows")
    if not isinstance(rows, list) or not isinstance(archived, list):
        return errors + ["ledger or archive has no rows"]
    if [row.get("clause") for row in rows] != [row.get("clause") for row in archived]:
        errors.append("ledger clause order != manuscript archive")
    if list(disp.PATHS) != [row.get("clause") for row in archived]:
        errors.append("disposition path order != manuscript archive")
    if len(rows) != 50:
        errors.append(f"ledger rows {len(rows)} != 50")
    counts = ledger.get("counts") or {}
    if counts.get("证") != 42 or counts.get("缩") != 8 or counts.get("放弃") != 0 or counts.get("未决") != 0:
        errors.append(f"ledger counts {counts} != prove 42 / narrow 8 / abandon 0 / undecided 0")
    status_rows = {row["clause"]: row for row in status["rows"]}
    open_count = 0
    for row, archived_row in zip(rows, archived):
        clause = row["clause"]
        errors.extend(row_errors(row, archived_row, status_rows.get(clause), names, lines))
        if row.get("archive_gap_status") == "OPEN_FORMAL_TAIL":
            open_count += 1
    if counts.get("OPEN_FORMAL_TAIL") != open_count:
        errors.append("open-tail count does not match rows")
    if open_count and ledger.get("discharges_archived_manuscript_gaps") is not False:
        errors.append("open formal tails with discharges true")
    errors.extend(formal_tail_errors(ledger, names))
    return errors


def formal_tail_errors(ledger: dict, names: dict) -> list[str]:
    errors: list[str] = []
    summary = ledger.get("formal_tail_round") or {}
    if ledger.get("formal_tail_criteria_pack") != disp.FORMAL_TAIL_PACK:
        errors.append("formal_tail_criteria_pack drifted")
    if summary.get("criteria_pack") != disp.FORMAL_TAIL_PACK:
        errors.append("formal-tail summary pack path drifted")
    for name in disp.FORMAL_TAIL_PACK_FILES:
        if name not in (summary.get("pack_files") or []):
            errors.append(f"formal-tail summary omits pack file {name}")
    if summary.get("step_2_closed") is not False:
        errors.append("formal-tail round claims step 2 closed")
    if summary.get("closed_this_round") != disp.CAND5_CLOSED_THIS_ROUND:
        errors.append(
            f"formal-tail closed_this_round {summary.get('closed_this_round')!r} "
            f"!= authorized {disp.CAND5_CLOSED_THIS_ROUND}"
        )
    if summary.get("close_pack") != disp.FORMAL_TAIL_CLOSE_PACK:
        errors.append("formal-tail summary close_pack drifted")
    if summary.get("discharges_archived_manuscript_gaps") is not False or summary.get("math_flip_authorized") is not False:
        errors.append("formal-tail round flips discharges or math authorization")
    if summary.get("tip_pin") != disp.TIP_PIN or summary.get("tip_pin_not_retargeted") is not False:
        errors.append("formal-tail round tip_pin is not the live retarget")
    if summary.get("formal_tail_expand_audit") != disp.FORMAL_TAIL_EXPAND:
        errors.append("formal-tail round missing formal_tail_expand_audit")
    later = summary.get("later_tip_gate_not_a_close") or {}
    if later != disp.LATER_TIP_GATE:
        errors.append("later tip gate record drifted")
    if later.get("closes_debt") is not False or later.get("retargets_tip_pin") is not False:
        errors.append("later tip gate is treated as a close or a retarget")
    if summary.get("narrow_not_reopened") != list(disp.CLOSED_NARROW_IDS):
        errors.append("narrow set was reopened or reordered")
    if summary.get("wiring_not_reopened") != list(disp.CLOSED_WIRING_IDS):
        errors.append("wiring set was reopened or reordered")
    if summary.get("one_pipeline") != "archive-gap close ledger; no second track":
        errors.append("formal-tail round is not on the archive-gap pipeline")
    candidate_text = ""
    candidate_path = ROOT / disp.CANDIDATE_MODULE
    if not candidate_path.is_file():
        errors.append(f"missing candidate module {disp.CANDIDATE_MODULE}")
    else:
        candidate_text = candidate_path.read_text(encoding="utf-8")
        for token in ("sorry", "admit"):
            if re_token(candidate_text, token):
                errors.append(f"candidate module contains {token}")
        for line in candidate_text.splitlines():
            if line.startswith("axiom ") or line.startswith("axiom\t"):
                errors.append("candidate module declares an axiom")
    open_rows = 0
    cand5_seen = set()
    for row in ledger.get("rows") or []:
        clause = row.get("clause")
        record = row.get("formal_tail_prove") or {}
        expected = disp.formal_tail_record(clause)
        if record != expected:
            errors.append(f"{clause}: formal_tail_prove != disposition record")
            continue
        if record.get("step_2_closed") is not False:
            errors.append(f"{clause}: formal tail claims step_2_closed")
        if clause in disp.CAND5_CLOSED_IDS:
            if record.get("close_admitted") is not True:
                errors.append(f"{clause}: CAND5 close missing close_admitted")
            cand5_seen.add(clause)
            if row.get("archive_gap_status") != "CLOSED_BY_WIRING":
                errors.append(f"{clause}: CAND5 row is not CLOSED_BY_WIRING")
            if row.get("unwired_formal_obligations"):
                errors.append(f"{clause}: CAND5 UNWIRED not cleared")
            if not str(row.get("scope_review") or "").strip():
                errors.append(f"{clause}: CAND5 missing SCOPE_REVIEW")
        elif record.get("close_admitted") is not False:
            errors.append(f"{clause}: formal tail admits a close")
        if record.get("discharges_archived_manuscript_gaps") is not False:
            errors.append(f"{clause}: formal tail discharges the archive")
        status_name = row.get("archive_gap_status")
        if status_name == "OPEN_FORMAL_TAIL":
            open_rows += 1
            if record.get("in_this_round") is not True:
                errors.append(f"{clause}: open tail missing from the formal-tail round")
            if clause in disp.COMPANION_TAIL_IDS:
                if record.get("companion_scope_notes") != disp.COMPANION_NOTES[clause]:
                    errors.append(f"{clause}: companion note missing from the prove record")
                if record.get("non_goals_same_row") != disp.NON_GOALS[clause] or not record.get("non_goals_same_row"):
                    errors.append(f"{clause}: companion non-goals are not in the same prove record")
            # Remaining OPEN candidate rows (none after CAND5) still need NOT_AUDITED.
            for short in record.get("candidate_theorems") or []:
                if f"theorem {short}" not in candidate_text:
                    errors.append(f"{clause}: candidate theorem {short} is not in the module")
                if record.get("disposition") != "CANDIDATE_NOT_AUDITED":
                    errors.append(f"{clause}: candidate row has the wrong disposition")
            if record.get("candidate_theorems"):
                if record.get("candidate_in_tip_pin_audit") is not True:
                    errors.append(f"{clause}: candidate_in_tip_pin_audit evidence not wired")
                expand_meta = record.get("tip_pin_expand_audit") or {}
                if expand_meta != disp.FORMAL_TAIL_EXPAND:
                    errors.append(f"{clause}: tip_pin_expand_audit != FORMAL_TAIL_EXPAND")
            if not record.get("candidate_theorems") and record.get("disposition") != "BLOCKED_NOT_IN_TIP_PIN_AUDIT":
                errors.append(f"{clause}: blocked row has the wrong disposition")
        else:
            if record.get("not_reopened") is not True or record.get("in_this_round") is not False:
                errors.append(f"{clause}: closed row was reopened by the formal-tail round")
    if cand5_seen != set(disp.CAND5_CLOSED_IDS):
        errors.append(f"CAND5 closed set {sorted(cand5_seen)} != {list(disp.CAND5_CLOSED_IDS)}")
    if summary.get("open_formal_tail_remaining") != open_rows:
        errors.append("formal-tail summary open count drifted")
    if open_rows != 35:
        errors.append(f"OPEN_FORMAL_TAIL remaining {open_rows} != 35")
    # FormalTail module order stays PROVE_CANDIDATES in archive order (closed rows
    # no longer carry candidate_theorems on the prove record).
    expected_order = []
    for row in ledger.get("rows") or []:
        expected_order.extend(disp.PROVE_CANDIDATES.get(row.get("clause"), []))
    declared = []
    if candidate_text:
        for line in candidate_text.splitlines():
            stripped = line.strip()
            if stripped.startswith("theorem "):
                declared.append(stripped.split()[1])
    if declared != expected_order:
        errors.append(f"candidate module theorems {declared} != PROVE_CANDIDATES {expected_order}")
    # Ban FormalTail short names from every row's wired_declarations.
    formal_shorts = set(expected_order)
    for row in ledger.get("rows") or []:
        clause = row.get("clause")
        for item in row.get("wired_declarations") or []:
            short = str(item.get("name") or "").split(".")[-1]
            if short in formal_shorts:
                errors.append(f"{clause}: FormalTail {short} cited in wired_declarations")
            full = str(item.get("name") or "")
            if full.startswith(disp.CANDIDATE_MODULE_NAME + "."):
                errors.append(f"{clause}: FormalTail full name in wired_declarations")
    # Expand-audit receipt still required (named_count matches PROVE_CANDIDATES; U10.3 companion; no discharges).
    if not EXPAND_RECEIPT_PATH.is_file():
        errors.append("missing expand-audit receipt")
    else:
        expand = load_json(EXPAND_RECEIPT_PATH)
        named = set(expand.get("named_theorems_full") or [])
        for short in expected_order:
            full = f"{disp.CANDIDATE_MODULE_NAME}.{short}"
            if full not in named:
                errors.append(f"expand-audit missing {full}")
        if expand.get("discharges_archived_manuscript_gaps") is not False:
            errors.append("expand-audit receipt flipped discharges")
        if expand.get("closes_debt") is not False:
            errors.append("expand-audit receipt claims debt close")
        if expand.get("named_count") != len(expected_order):
            errors.append(f"expand-audit named_count {expand.get("named_count")} != {len(expected_order)}")
        companion = expand.get("u10_3_companion_note") or ""
        if "公平" not in companion or "另证" not in companion:
            errors.append("expand-audit missing U10.3 companion 公平/另证 note")
    return errors


def re_token(text: str, token: str) -> bool:
    import re

    return re.search(rf"\b{token}\b", text) is not None


def row_errors(row: dict, archived: dict, status_row: dict | None, names: dict, lines: dict) -> list[str]:
    errors: list[str] = []
    clause = str(row.get("clause"))
    if row.get("manuscript_remaining") != archived.get("remaining_obligations"):
        errors.append(f"{clause}: manuscript_remaining != archive pin")
    if not str(row.get("manuscript_remaining") or "").strip():
        errors.append(f"{clause}: manuscript remaining emptied")
    path = row.get("suggested_close_path")
    if path != disp.PATHS.get(clause):
        errors.append(f"{clause}: path {path!r} != pack {disp.PATHS.get(clause)!r}")
    if path not in ("证", "缩"):
        errors.append(f"{clause}: path is not 证 or 缩")
    if row.get("discharges_archived_manuscript_gaps") is not False:
        errors.append(f"{clause}: discharges is not false")
    if row.get("manuscript_sentence_not_proved") is not True:
        errors.append(f"{clause}: claims the manuscript sentence is proved")
    if row.get("china_law_separated") is not True:
        errors.append(f"{clause}: China-law column is not marked separate")
    if row.get("not_gate_run") != disp.GATE_ONLY_RUN or row.get("tip_pin_run_id") != disp.TIP_PIN["run_id"]:
        errors.append(f"{clause}: wiring run is not the live tip-pin")
    if row.get("tip_pin_job_id") != disp.TIP_PIN["job_id"]:
        errors.append(f"{clause}: wiring job is not {disp.TIP_PIN['job_id']}")
    goals = row.get("non_goals") or []
    unwired = row.get("unwired_formal_obligations") or []
    status_name = row.get("archive_gap_status")
    if path == "缩":
        if status_name != "CLOSED_BY_NARROW" or unwired:
            errors.append(f"{clause}: narrow row is not a pure non-goal close")
        if not goals:
            errors.append(f"{clause}: narrow row has no non-goal")
        if not str(row.get("claimed_scope") or "").strip():
            errors.append(f"{clause}: narrow row has no claimed scope")
        if not str(row.get("remaining_after_close") or "").startswith("NON_GOAL_POINTER:"):
            errors.append(f"{clause}: narrow remaining_after_close is not a non-goal pointer")
    elif status_name == "OPEN_FORMAL_TAIL":
        if not unwired:
            errors.append(f"{clause}: open tail has no unwired obligation")
        if not str(row.get("remaining_after_close") or "").startswith("OPEN_FORMAL:"):
            errors.append(f"{clause}: open remaining_after_close dropped the formal tail")
    elif status_name == "CLOSED_BY_WIRING":
        if unwired or not str(row.get("scope_review") or "").strip():
            errors.append(f"{clause}: wiring close is missing scope review or still has a tail")
    else:
        errors.append(f"{clause}: unexpected status {status_name!r}")
    if disp.COMPANION_NOTES.get(clause) and row.get("companion_scope_notes") != disp.COMPANION_NOTES[clause]:
        errors.append(f"{clause}: companion scope note missing from the same row")
    if disp.COMPANION_NOTES.get(clause) and not goals:
        errors.append(f"{clause}: companion note has no non-goal text in the same row")
    wired = row.get("wired_declarations") or []
    if not wired:
        errors.append(f"{clause}: no evidence pointer")
    pointers = []
    for item in wired:
        short = str(item.get("name") or "").split(".")[-1]
        file_name = str(item.get("file") or "")
        line = lines.get((file_name, short))
        if line is None or item.get("line") != line:
            errors.append(f"{clause}: {file_name}:{short} is not the theorem line")
            continue
        full = qualified(file_name, short)
        if item.get("name") != full:
            errors.append(f"{clause}: {item.get('name')} != {full}")
        axioms = names.get(full)
        if axioms is None:
            errors.append(f"{clause}: {full} is not in the tip-pin axiom audit")
        elif set(axioms) - {"propext", "Quot.sound", "Classical.choice"}:
            errors.append(f"{clause}: {full} axioms {axioms}")
        if item.get("tip_pin_run_id") != disp.TIP_PIN["run_id"] or item.get("not_gate_run") != disp.GATE_ONLY_RUN:
            errors.append(f"{clause}: {short} cites the gate run as its audit")
        pointers.append(f"{file_name}:{line}")
        for consumer in item.get("consumers") or []:
            consumer_path = CANDIDATE / str(consumer.get("file"))
            consumer_line = consumer.get("line")
            if not consumer_path.is_file() or not isinstance(consumer_line, int):
                errors.append(f"{clause}: consumer {consumer} is not a source line")
                continue
            text_lines = consumer_path.read_text(encoding="utf-8").splitlines()
            if not 1 <= consumer_line <= len(text_lines):
                errors.append(f"{clause}: consumer line out of range {consumer}")
    if row.get("evidence_pointers") != pointers:
        errors.append(f"{clause}: evidence_pointers != theorem lines")
    if status_row is None:
        errors.append(f"{clause}: missing from 50_clause_status")
    else:
        if status_row.get("exact_scope") != "" or status_row.get("remaining_obligations") != []:
            errors.append(f"{clause}: live scope fields were filled")
        evidence = status_row.get("candidate_ci_evidence") or {}
        if evidence.get("discharges_archived_manuscript_gaps") is not False:
            errors.append(f"{clause}: candidate evidence discharges the archive")
        if evidence.get("run_id") != disp.TIP_PIN["run_id"] or evidence.get("subject") != disp.TIP_PIN["subject"]:
            errors.append(f"{clause}: candidate evidence tip-pin moved")
        if status_row.get("archive_gap_close") != pointer_view(row):
            errors.append(f"{clause}: clause pointer != close ledger")
    for phrase in disp.DOES_NOT_CLAIM:
        if phrase not in (row.get("does_not_claim") or []):
            errors.append(f"{clause}: missing does_not_claim {phrase!r}")
    return errors


def check_pins(status: dict, construction: dict, receipt: dict, archive: dict, carried: dict) -> list[str]:
    errors: list[str] = []
    if sha256_bytes(ARCHIVE_PATH.read_bytes()) != ARCHIVE_SHA:
        errors.append("manuscript archive bytes changed")
    if not LIVE_ARCHIVE_PATH.is_file():
        errors.append("missing live scope archive")
        live_archive: dict = {}
        live_sha = ""
    else:
        live_archive = load_json(LIVE_ARCHIVE_PATH)
        live_sha = sha256_bytes(LIVE_ARCHIVE_PATH.read_bytes())
    if receipt.get("scope_archive_sha256") != live_sha:
        errors.append("receipt scope_archive_sha256 != live carried archive")
    if receipt.get("scope_archive") != LIVE_ARCHIVE_REL:
        errors.append("receipt scope_archive is not the live carry")
    if live_archive.get("rows") != archive.get("rows"):
        errors.append("live scope archive rows differ from the unmutated manuscript pin")
    if live_archive.get("pinned_subject") != archive.get("pinned_subject"):
        errors.append("live scope archive pinned_subject drifted")
    if not live_archive.get("rows"):
        errors.append("live scope archive rows emptied")
    if receipt.get("subject_commit") != disp.TIP_PIN["subject"] or receipt.get("run_id") != disp.TIP_PIN["run_id"]:
        errors.append("receipt tip-pin subject/run changed")
    if receipt.get("job_id") != disp.TIP_PIN["job_id"]:
        errors.append("receipt job changed")
    if receipt.get("discharges_archived_manuscript_gaps") is not False:
        errors.append("receipt discharges flag flipped")
    if receipt.get("axiom_audit") != disp.TIP_PIN["axiom_audit"]:
        errors.append("receipt axiom_audit token changed")
    tip = status.get("tip_declaration_location") or {}
    if tip.get("subject") != disp.TIP_PIN["subject"] or tip.get("run_id") != disp.TIP_PIN["run_id"]:
        errors.append("tip_declaration_location subject/run changed")
    if tip.get("job_id") != disp.TIP_PIN["job_id"]:
        errors.append("tip_declaration_location job changed")
    if tip.get("discharges_archived_manuscript_gaps") is not False:
        errors.append("tip_declaration_location discharges flag flipped")
    if construction.get("tip_declaration_location") != tip:
        errors.append("construction tip_declaration_location != 50_clause_status")
    close = construction.get("archive_gap_close") or {}
    if close.get("discharges_archived_manuscript_gaps") is not False or close.get("math_flip_authorized") is not False:
        errors.append("construction archive_gap_close flipped discharges or math authorization")
    if close.get("tip_pin") != disp.TIP_PIN:
        errors.append("construction archive_gap_close tip_pin is not the live retarget")
    if close.get("tip_pin_not_retargeted") is not False:
        errors.append("construction archive_gap_close does not record the tip-pin retarget")
    formal_tail = close.get("formal_tail_round") or {}
    if formal_tail.get("tip_pin") != disp.TIP_PIN or formal_tail.get("tip_pin_not_retargeted") is not False:
        errors.append("construction formal_tail_round tip_pin is not the live retarget")
    if formal_tail.get("step_2_closed") is not False:
        errors.append("construction formal_tail_round claims step 2 closed")
    if formal_tail.get("closed_this_round") != disp.CAND5_CLOSED_THIS_ROUND:
        errors.append(
            f"construction formal_tail_round closed_this_round "
            f"{formal_tail.get('closed_this_round')!r} != {disp.CAND5_CLOSED_THIS_ROUND}"
        )
    if carried.get("rows") != archive.get("rows"):
        errors.append("carried manuscript rows differ from the tip archive")
    return errors


def check(write: bool = False) -> tuple[list[str], dict]:
    binding = load_binding()
    status = load_json(STATUS_PATH)
    construction = load_json(CONSTRUCTION_PATH)
    archive = load_json(ARCHIVE_PATH)
    carried = load_json(CARRIED_PATH)
    receipt = load_json(RECEIPT_PATH)
    lines = theorem_lines(CANDIDATE)
    ledger = build_ledger(status, archive, lines)
    extracted = binding.reextract((ROOT / binding.ZIP_REL).read_bytes())
    if write:
        dump_json(LEDGER_PATH, ledger)
        sync_pointers(status, construction, ledger)
        dump_json(STATUS_PATH, status)
        dump_json(CONSTRUCTION_PATH, construction)
        status = load_json(STATUS_PATH)
        construction = load_json(CONSTRUCTION_PATH)
        ledger = load_json(LEDGER_PATH)
    elif not LEDGER_PATH.is_file():
        return ["missing close ledger; run with --write"], ledger
    else:
        committed = load_json(LEDGER_PATH)
        if committed != ledger:
            return ["close ledger != disposition rebuild"], ledger
    errors = check_pins(status, construction, receipt, archive, carried)
    errors.extend(check_ledger(ledger, status, archive, extracted, lines))
    return errors, ledger


def main() -> int:
    write = "--write" in sys.argv
    errors, ledger = check(write=write)
    counts = ledger.get("counts") or {}
    closed_round = (ledger.get("formal_tail_round") or {}).get("closed_this_round")
    print(
        "archive-gap rows {rows}; narrow {narrow}; wiring {wiring}; "
        "open_formal_tail {open}; discharges false; tip-pin {run}; "
        "formal_tail_closed_this_round {closed}; step_2_closed false".format(
            rows=len(ledger.get("rows") or []),
            narrow=counts.get("CLOSED_BY_NARROW"),
            wiring=counts.get("CLOSED_BY_WIRING"),
            open=counts.get("OPEN_FORMAL_TAIL"),
            run=disp.TIP_PIN["run_id"],
            closed=closed_round,
        )
    )
    if errors:
        print(f"FAIL {len(errors)}", file=sys.stderr)
        for error in errors:
            print(error, file=sys.stderr)
        return 1
    print("archive-gap close layer: dispositions checked; discharges remains false")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
