#!/usr/bin/env python3
"""Check the archive-gap close layer against the verbatim manuscript pin.

The manuscript pin is not rewritten and is not emptied. ``discharges`` stays
false. The live tip-pin is the authorized retarget
subject 21862d9bdd94bfa15e5da39079538b5eb30ff235 / run 40274167574 / job
121413235107. That retarget is not a close. The live tip-pin is not moved
onto gate run 39960871624. Declarations cited as wiring must be in the
re-extracted tip-pin axiom audit.

    python scripts/ci/check_archive_gap_close.py
    python scripts/ci/check_archive_gap_close.py --write
"""

from __future__ import annotations

import hashlib
import importlib.util
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts" / "ci"))

import archive_gap_dispositions as disp  # noqa: E402
import check_axiom_audit_log as axiom_audit  # noqa: E402

CANDIDATE = ROOT / "proofs/lean/juris_lean/JurisLean/Candidates/Final20261021"
STATUS_PATH = CANDIDATE / "50_clause_status.json"
CONSTRUCTION_PATH = CANDIDATE / "construction_status.json"
ARCHIVE_PATH = CANDIDATE / "evidence/ci-tip-e87543d8/scope-archive.json"
CARRIED_PATH = CANDIDATE / "evidence/ci-tip-966b9373/scope-archive.json"
LIVE_ARCHIVE_REL = "evidence/ci-tip-21862d9b/scope-archive.json"
LIVE_ARCHIVE_PATH = CANDIDATE / LIVE_ARCHIVE_REL
RECEIPT_PATH = CANDIDATE / "evidence/ci-tip-21862d9b/verification.json"
EXPAND_RECEIPT_REL = "evidence/ci-tip-21862d9b/verification.json"
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
                **({"independent_closure": {"receipt": disp.INDEPENDENT_RECEIPTS[clause],
                    "named_theorems_full": disp.INDEPENDENT_NAMES[clause]}}
                    if clause in disp.INDEPENDENT_CLOSED_IDS else {}),
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
                "evidence/ci-tip-21862d9b/scope-archive.json. Carrying is not a proof "
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
        **({"independent_closure": row["independent_closure"]} if "independent_closure" in row else {}),
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
        evidence = dict(row.get("candidate_ci_evidence") or {})
        evidence["subject"] = disp.TIP_PIN["subject"]
        evidence["run_id"] = disp.TIP_PIN["run_id"]
        evidence["job"] = "lean-full-clean-build"
        evidence["job_id"] = disp.TIP_PIN["job_id"]
        evidence["verification"] = disp.TIP_PIN["verification"]
        evidence["acceptance_discharged"] = True
        evidence["discharges_archived_manuscript_gaps"] = False
        row["candidate_ci_evidence"] = evidence
    construction["archive_gap_close"] = summary_view(ledger)
    construction["tip_declaration_location"] = status.get("tip_declaration_location")


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
    if counts.get("证") != 44 or counts.get("缩") != 6 or counts.get("放弃") != 0 or counts.get("未决") != 0:
        errors.append(f"ledger counts {counts} != prove 44 / narrow 6 / abandon 0 / undecided 0")
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
    if summary.get("closed_this_round") != len(disp.CURRENT_CLOSE_IDS):
        errors.append(
            f"formal-tail closed_this_round {summary.get('closed_this_round')!r} "
            f"!= authorized {len(disp.CURRENT_CLOSE_IDS)}"
        )
    if disp.CAND7_CLOSED_THIS_ROUND != 5 or len(disp.CAND7_CLOSED_IDS) != 5:
        errors.append("CAND7 close authorization is not the five releasable ids")
    if summary.get("close_pack") != disp.CURRENT_CLOSE_PACK:
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
    if summary.get("wiring_not_reopened") != [c for c in disp.CLOSED_WIRING_IDS if c not in disp.CURRENT_CLOSE_IDS]:
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
    cand5bis_seen = set()
    cand6_seen = set()
    cand7_seen = set()
    authorized_closed = (
        set(disp.CAND5_CLOSED_IDS)
        | set(disp.CAND5BIS_CLOSED_IDS)
        | set(disp.CAND6_CLOSED_IDS)
        | set(disp.CAND7_CLOSED_IDS)
        | set(disp.INDEPENDENT_CLOSED_IDS)
    )
    for row in ledger.get("rows") or []:
        clause = row.get("clause")
        record = row.get("formal_tail_prove") or {}
        expected = disp.formal_tail_record(clause)
        if record != expected:
            errors.append(f"{clause}: formal_tail_prove != disposition record")
            continue
        if record.get("step_2_closed") is not False:
            errors.append(f"{clause}: formal tail claims step_2_closed")
        if clause in authorized_closed:
            if record.get("close_admitted") is not True:
                errors.append(f"{clause}: close missing close_admitted")
            if clause in disp.CAND5_CLOSED_IDS:
                cand5_seen.add(clause)
            if clause in disp.CAND5BIS_CLOSED_IDS:
                cand5bis_seen.add(clause)
            if clause in disp.CAND6_CLOSED_IDS:
                cand6_seen.add(clause)
            if clause in disp.CAND7_CLOSED_IDS:
                cand7_seen.add(clause)
            if row.get("archive_gap_status") != "CLOSED_BY_WIRING":
                errors.append(f"{clause}: authorized close is not CLOSED_BY_WIRING")
            if row.get("unwired_formal_obligations"):
                errors.append(f"{clause}: authorized close UNWIRED not cleared")
            if not str(row.get("scope_review") or "").strip():
                errors.append(f"{clause}: authorized close missing SCOPE_REVIEW")
            if clause in disp.CAND6_CLOSED_IDS or clause in disp.CAND7_CLOSED_IDS:
                review = str(row.get("scope_review") or "")
                if "本条关项范围＝FormalTail 覆盖的形式义务" not in review:
                    errors.append(f"{clause}: SCOPE_REVIEW missing the authorized close sentence")
                if "FormalTail20261024" not in review:
                    errors.append(f"{clause}: SCOPE_REVIEW does not name FormalTail20261024")
            if clause == "U08.3":
                goals = row.get("non_goals") or []
                companion = str(row.get("companion_scope_notes") or "")
                if not any("现实真值" in item for item in goals):
                    errors.append("U08.3: 现实真值定理 NON_GOAL missing from the same row")
                if "现实真值" not in companion:
                    errors.append("U08.3: COMPANION_NOTES missing 现实真值定理")
                if "现实真值" not in str(row.get("scope_review") or ""):
                    errors.append("U08.3: SCOPE_REVIEW missing 现实真值 NON_GOAL")
            if clause == "U15.3":
                goals = row.get("non_goals") or []
                companion = str(row.get("companion_scope_notes") or "")
                if not any("readback" in item for item in goals):
                    errors.append("U15.3: external load readback NON_GOAL missing from the same row")
                if "readback" not in companion:
                    errors.append("U15.3: COMPANION_NOTES missing external load readback")
                if "readback" not in str(row.get("scope_review") or ""):
                    errors.append("U15.3: SCOPE_REVIEW missing external load readback NON_GOAL")
            if clause == "U09.1":
                goals = row.get("non_goals") or []
                companion = str(row.get("companion_scope_notes") or "")
                goal_text = " ".join(goals)
                if "legal allocation" not in goal_text and "法律分配" not in goal_text:
                    errors.append("U09.1: 法律分配效果 NON_GOAL missing from the same row")
                if "法律关系" not in goal_text and "法律关系" not in companion:
                    errors.append("U09.1: 法律关系消灭 NON_GOAL missing from the same row")
                if "法律关系" not in companion:
                    errors.append("U09.1: COMPANION_NOTES missing 法律关系消灭")
                review = str(row.get("scope_review") or "")
                if "法律分配" not in review or "法律关系" not in review:
                    errors.append("U09.1: SCOPE_REVIEW missing 法律分配效果／法律关系消灭 NON_GOAL")
            if clause == "U04.3":
                goals = row.get("non_goals") or []
                companion = str(row.get("companion_scope_notes") or "")
                if not any("校准" in item for item in goals):
                    errors.append("U04.3: 校准 NON_GOAL missing from the same row")
                if "校准" not in companion or "另证" not in companion:
                    errors.append("U04.3: COMPANION_NOTES missing 校准＝另证")
                if "校准" not in str(row.get("scope_review") or ""):
                    errors.append("U04.3: SCOPE_REVIEW missing 校准 NON_GOAL")
            if clause == "U13.1":
                goals = row.get("non_goals") or []
                companion = str(row.get("companion_scope_notes") or "")
                if not any("Authority integration" in item and "另证" in item for item in goals):
                    errors.append("U13.1: authority integration NON_GOAL missing from the same row")
                if "集成" not in companion or "另证" not in companion:
                    errors.append("U13.1: COMPANION_NOTES missing authority 集成＝另证")
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
            # OPEN rows that still carry candidate theorems must stay NOT_AUDITED.
            # The CAND5 / CAND5bis / CAND6 / CAND7 closes are not in this branch.
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
    if cand5bis_seen != set(disp.CAND5BIS_CLOSED_IDS):
        errors.append(f"CAND5bis closed set {sorted(cand5bis_seen)} != {list(disp.CAND5BIS_CLOSED_IDS)}")
    if cand6_seen != set(disp.CAND6_CLOSED_IDS):
        errors.append(f"CAND6 closed set {sorted(cand6_seen)} != {list(disp.CAND6_CLOSED_IDS)}")
    if cand7_seen != set(disp.CAND7_CLOSED_IDS):
        errors.append(f"CAND7 closed set {sorted(cand7_seen)} != {list(disp.CAND7_CLOSED_IDS)}")
    if summary.get("open_formal_tail_remaining") != open_rows:
        errors.append("formal-tail summary open count drifted")
    current_open = disp.INDEPENDENT_CLOSE_PACKS[-1]["open_after"]
    if open_rows != current_open:
        errors.append(f"OPEN_FORMAL_TAIL remaining {open_rows} != {current_open}")
    if summary.get("blocked_rows") != current_open:
        errors.append(f"blocked_rows {summary.get('blocked_rows')!r} != {current_open}")
    if summary.get("candidate_rows") != 0:
        errors.append(
            f"candidate_rows {summary.get('candidate_rows')!r} != 0 after CAND7 close"
        )
    wiring_ids = [
        row.get("clause")
        for row in ledger.get("rows") or []
        if row.get("archive_gap_status") == "CLOSED_BY_WIRING"
    ]
    if len(disp.CLOSED_WIRING_IDS) != 44 or set(wiring_ids) != set(disp.CLOSED_WIRING_IDS):
        errors.append(
            f"CLOSED_BY_WIRING {sorted(wiring_ids)} != authorized {list(disp.CLOSED_WIRING_IDS)}"
        )
    if summary.get("discharges_archived_manuscript_gaps") is not False:
        errors.append("formal-tail round discharges flipped")
    if summary.get("math_flip_authorized") is not False or summary.get("step_2_closed") is not False:
        errors.append("formal-tail round flipped math_flip or step_2_closed")
    # FormalTail module order stays PROVE_CANDIDATES in archive order (closed rows
    # no longer carry candidate_theorems on the prove record).
    expected_order = []
    cand6_ids = set(disp.CAND6_IDS)
    cand7_ids = set(disp.CAND7_IDS)
    cand8_ids = set(disp.CAND8_IDS)
    for row in ledger.get("rows") or []:
        if row.get("clause") in cand6_ids or row.get("clause") in cand7_ids:
            continue
        expected_order.extend(disp.PROVE_CANDIDATES.get(row.get("clause"), []))
    # CAND6 and CAND7 short names stay in PROVE_CANDIDATES and in
    # FormalTail20261024.lean. The ten rows are CLOSED_BY_WIRING and no longer carry
    # candidate_theorems on the prove record. Source order appends twenty-four names
    # after the earlier 37. That is not archive order, so the module-order check keeps
    # them as suffixes. The expand receipt stays closes_debt=false /
    # closed_this_round=0 / named_count=61. That receipt is not this close.
    cand6_suffix: list[str] = []
    for clause in disp.CAND6_IDS:
        cand6_suffix.extend(disp.PROVE_CANDIDATES.get(clause, []))
    cand7_suffix: list[str] = []
    for clause in disp.CAND7_IDS:
        cand7_suffix.extend(disp.PROVE_CANDIDATES.get(clause, []))
    if len(cand6_suffix) != 12:
        errors.append(f"CAND6 theorem count {len(cand6_suffix)} != 12")
    if len(cand7_suffix) != 12:
        errors.append(f"CAND7 theorem count {len(cand7_suffix)} != 12")
    prove_names = {name for names in disp.PROVE_CANDIDATES.values() for name in names}
    missing_from_prove = [name for name in cand6_suffix + cand7_suffix if name not in prove_names]
    if missing_from_prove:
        errors.append(f"CAND6/CAND7 suffix missing from PROVE_CANDIDATES: {missing_from_prove}")
    # CAND8 v1.1 (pack formal_tail_真证CAND8_20261026): eight negative theorems only.
    # They remain absent from PROVE_CANDIDATES. U07.2 is separately closed by its
    # independent positive source-model package; this does not promote CAND8 or
    # treat its negative declarations as close evidence. The historical expand
    # receipt stays closes_debt=false / closed_this_round=0 / named_count=61.
    cand8_suffix = [
        "u03_1_relative_soundness_not_provenance_dag_to_finite_closure",
        "u03_1_computed_sound_not_dag_connected_to_executable_closure",
        "u03_1_robust_countermodel_not_connected_to_finite_closure",
        "u03_2_relative_completeness_not_verified_fuel_bound",
        "u03_2_checked_closure_complete_not_list_carrier_bound",
        "u03_2_incomplete_fuel_not_carrier_fuel_bound",
        "u07_2_common_fiber_not_semantic_compatibility",
        "u07_2_incompatible_fiber_not_layer_compatibility",
    ]
    if len(cand8_suffix) != 8:
        errors.append(f"CAND8 theorem count {len(cand8_suffix)} != 8")
    overlap8 = [name for name in cand8_suffix if name in prove_names]
    if overlap8:
        errors.append(f"CAND8 suffix overlaps PROVE_CANDIDATES: {overlap8}")
    for row in ledger.get("rows") or []:
        if row.get("clause") not in cand8_ids or row.get("clause") in disp.INDEPENDENT_CLOSED_IDS:
            continue
        record = row.get("formal_tail_prove") or {}
        if row.get("archive_gap_status") != "OPEN_FORMAL_TAIL":
            errors.append(f"{row.get('clause')}: CAND8 true-proof flipped archive_gap_status")
        if record.get("disposition") != "BLOCKED_NOT_IN_TIP_PIN_AUDIT":
            errors.append(f"{row.get('clause')}: CAND8 true-proof flipped disposition")
        if record.get("candidate_theorems"):
            errors.append(f"{row.get('clause')}: CAND8 true-proof wrote candidate_theorems")
        if record.get("discharges_archived_manuscript_gaps") is not False:
            errors.append(f"{row.get('clause')}: CAND8 true-proof flipped discharges")
        if record.get("step_2_closed") is not False:
            errors.append(f"{row.get('clause')}: CAND8 true-proof flipped step_2_closed")
    declared = []
    if candidate_text:
        for line in candidate_text.splitlines():
            stripped = line.strip()
            if stripped.startswith("theorem "):
                declared.append(stripped.split()[1])
    if declared != expected_order + cand6_suffix + cand7_suffix + cand8_suffix:
        errors.append(
            f"candidate module theorems {declared} != "
            f"PROVE_CANDIDATES+CAND6+CAND7+CAND8 "
            f"{expected_order + cand6_suffix + cand7_suffix + cand8_suffix}"
        )
    # Ban FormalTail short names from every row's wired_declarations.
    formal_shorts = (
        set(expected_order) | set(cand6_suffix) | set(cand7_suffix) | set(cand8_suffix)
    )
    for row in ledger.get("rows") or []:
        clause = row.get("clause")
        for item in row.get("wired_declarations") or []:
            short = str(item.get("name") or "").split(".")[-1]
            if short in formal_shorts:
                errors.append(f"{clause}: FormalTail {short} cited in wired_declarations")
            full = str(item.get("name") or "")
            if full.startswith(disp.CANDIDATE_MODULE_NAME + "."):
                errors.append(f"{clause}: FormalTail full name in wired_declarations")
    # Live expand receipt names CAND5 (25) + CAND5bis (12) + CAND6 (12) + CAND7 (12)
    # = 61 on tip 21862d9b. Historical 1c72e444 (49), dc7b7430 (37), f85ebe44 (25).
    if not EXPAND_RECEIPT_PATH.is_file():
        errors.append("missing expand-audit receipt")
    else:
        expand = load_json(EXPAND_RECEIPT_PATH)
        named = set(expand.get("named_theorems_full") or [])
        expected = []
        for row in ledger.get("rows") or []:
            expected.extend(disp.PROVE_CANDIDATES.get(row.get("clause"), []))
        for short in expected:
            full = f"{disp.CANDIDATE_MODULE_NAME}.{short}"
            if full not in named:
                errors.append(f"expand-audit missing {full}")
        for clause in disp.CAND5BIS_IDS:
            for short in disp.PROVE_CANDIDATES.get(clause, []):
                full = f"{disp.CANDIDATE_MODULE_NAME}.{short}"
                if full not in named:
                    errors.append(f"expand-audit missing CAND5bis {full}")
        if expand.get("discharges_archived_manuscript_gaps") is not False:
            errors.append("expand-audit receipt flipped discharges")
        if expand.get("closes_debt") is not False:
            errors.append("expand-audit receipt claims debt close")
        for short in cand6_suffix:
            full = f"{disp.CANDIDATE_MODULE_NAME}.{short}"
            if full not in named:
                errors.append(f"expand-audit missing CAND6 {full}")
        for short in cand7_suffix:
            full = f"{disp.CANDIDATE_MODULE_NAME}.{short}"
            if full not in named:
                errors.append(f"expand-audit missing CAND7 {full}")
        for short in cand8_suffix:
            full = f"{disp.CANDIDATE_MODULE_NAME}.{short}"
            if full in named:
                errors.append(f"expand-audit must not name CAND8 {full}")
        if expand.get("named_count") != 61:
            errors.append(
                f"expand-audit named_count {expand.get('named_count')} != 61 "
                "(CAND5+CAND5bis+CAND6+CAND7)"
            )
        if len(expand.get("named_theorems_full") or []) != 61:
            errors.append("expand-audit named_theorems_full length != 61")
        if expand.get("subject_commit") != disp.TIP_PIN["subject"]:
            errors.append("expand-audit subject_commit != live tip_pin subject")
        if expand.get("run_id") != disp.TIP_PIN["run_id"]:
            errors.append("expand-audit run_id != live tip_pin run_id")
        if expand.get("job_id") != disp.TIP_PIN["job_id"]:
            errors.append("expand-audit job_id != live tip_pin job_id")
        if expand.get("open_formal_tail_remaining") != 25:
            errors.append("expand-audit open_formal_tail_remaining != 25")
        if expand.get("closed_this_round") != 0:
            errors.append("expand-audit closed_this_round != 0 (this expand increments 0)")
        companion = expand.get("u10_3_companion_note") or ""
        if "公平" not in companion or "另证" not in companion:
            errors.append("expand-audit missing U10.3 companion 公平/另证 note")
        u13 = expand.get("u13_1_companion_note") or ""
        if "另证" not in u13 and "NON_GOAL" not in u13:
            errors.append("expand-audit missing U13.1 companion 另证/NON_GOAL note")
        u08_3 = expand.get("u08_3_companion_note") or ""
        if "现实真值" not in u08_3 or ("另证" not in u08_3 and "NON_GOAL" not in u08_3):
            errors.append("expand-audit missing U08.3 companion 现实真值/NON_GOAL note")
        u15_3 = expand.get("u15_3_companion_note") or ""
        if "readback" not in u15_3 or ("另证" not in u15_3 and "NON_GOAL" not in u15_3):
            errors.append("expand-audit missing U15.3 companion readback/NON_GOAL note")
        u09_1 = expand.get("u09_1_companion_note") or ""
        if "法律关系" not in u09_1 or ("另证" not in u09_1 and "NON_GOAL" not in u09_1):
            errors.append("expand-audit missing U09.1 companion 法律关系/NON_GOAL note")
        u04_3 = expand.get("u04_3_companion_note") or ""
        if "校准" not in u04_3 or ("另证" not in u04_3 and "NON_GOAL" not in u04_3):
            errors.append("expand-audit missing U04.3 companion 校准/NON_GOAL note")
        # Historical CAND5+CAND5bis+CAND6 receipt must remain named_count=49 and
        # must not gain the CAND7 names.
        prior_path = CANDIDATE / "evidence/ci-tip-1c72e444/verification.json"
        if prior_path.is_file():
            prior = load_json(prior_path)
            if prior.get("named_count") != 49:
                errors.append("historical 1c72e444 named_count drifted from 49")
            if prior.get("closes_debt") is not False:
                errors.append("historical 1c72e444 closes_debt flipped")
            prior_named = set(prior.get("named_theorems_full") or [])
            for short in cand7_suffix:
                full = f"{disp.CANDIDATE_MODULE_NAME}.{short}"
                if full in prior_named:
                    errors.append(f"historical 1c72e444 must not name CAND7 {full}")
        else:
            errors.append("missing historical 1c72e444 receipt")
        # Historical CAND5+CAND5bis receipt must remain named_count=37 and must
        # not gain the CAND6 names.
        prior_path = CANDIDATE / "evidence/ci-tip-dc7b7430/verification.json"
        if prior_path.is_file():
            prior = load_json(prior_path)
            if prior.get("named_count") != 37:
                errors.append("historical dc7b7430 named_count drifted from 37")
            if prior.get("closes_debt") is not False:
                errors.append("historical dc7b7430 closes_debt flipped")
            prior_named = set(prior.get("named_theorems_full") or [])
            for short in cand6_suffix:
                full = f"{disp.CANDIDATE_MODULE_NAME}.{short}"
                if full in prior_named:
                    errors.append(f"historical dc7b7430 must not name CAND6 {full}")
        else:
            errors.append("missing historical dc7b7430 receipt")
        # Historical receipt must remain CAND5-only (named_count=25).
        hist_path = CANDIDATE / "evidence/ci-tip-f85ebe44/verification.json"
        if hist_path.is_file():
            hist = load_json(hist_path)
            if hist.get("named_count") != 25:
                errors.append("historical f85ebe44 named_count drifted from 25")
            hist_named = set(hist.get("named_theorems_full") or [])
            for clause in disp.CAND5BIS_IDS:
                for short in disp.PROVE_CANDIDATES.get(clause, []):
                    full = f"{disp.CANDIDATE_MODULE_NAME}.{short}"
                    if full in hist_named:
                        errors.append(f"historical f85ebe44 must not name CAND5bis {full}")
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
    if formal_tail.get("closed_this_round") != len(disp.CURRENT_CLOSE_IDS):
        errors.append(
            f"construction formal_tail_round closed_this_round "
            f"{formal_tail.get('closed_this_round')!r} != {len(disp.CURRENT_CLOSE_IDS)}"
        )
    if carried.get("rows") != archive.get("rows"):
        errors.append("carried manuscript rows differ from the tip archive")
    return errors


def independent_close_errors(receipt: dict, raw: str,
                             pack: dict = disp.INDEPENDENT_CLOSE_PACKS[0]) -> list[str]:
    """Accept the exact original residuals and evidence of one independent close."""
    errors = []
    expected = {name for names in pack["names"].values() for name in names}
    if receipt.get("closed_ids") != list(pack["closed_ids"]):
        errors.append("independent close: unauthorized clause set")
    if receipt.get("names_by_clause") != pack["names"]:
        errors.append("independent close: residual theorem mapping changed")
    if receipt.get("closes_debt") is not True or receipt.get("closed_this_round") != len(pack["closed_ids"]):
        errors.append("independent close: missing explicit clause admission")
    if receipt.get("discharges_archived_manuscript_gaps") is not False:
        errors.append("independent close: global discharges changed")
    if receipt.get("tip_pin") != disp.TIP_PIN:
        errors.append("independent close: frozen pin changed")
    if receipt.get("job_conclusion") != "success" or not receipt.get("run_id") or not receipt.get("job_id"):
        errors.append("independent close: no successful named audit")
    if (receipt.get("named_count"), receipt.get("open_before"), receipt.get("open_after")) != (len(expected), pack["open_before"], pack["open_after"]):
        errors.append("independent close: target or debt count drifted")
    subject = receipt.get("subject", "")
    if not re.fullmatch(r"[0-9a-f]{40}", subject):
        return errors + ["independent close: invalid exact subject"]
    archive = {row["clause"]: row for row in load_json(ARCHIVE_PATH)["rows"]}
    residuals = {clause: archive[clause]["remaining_obligations"] for clause in pack["closed_ids"]}
    if receipt.get("original_residuals") != residuals:
        errors.append("independent close: original residual was replaced or omitted")
    for receipt_key, pack_key in (
        ("subject", "expected_subject"),
        ("run_id", "expected_run_id"),
        ("job_id", "expected_job_id"),
        ("attempt", "expected_attempt"),
        ("artifact_id", "expected_artifact_id"),
        ("artifact_sha256", "expected_artifact_sha256"),
    ):
        if pack.get(pack_key) is not None and receipt.get(receipt_key) != pack[pack_key]:
            errors.append(f"independent close: {receipt_key} differs from the pinned receipt")
    if receipt.get("driver_path") != pack["driver"]:
        errors.append("independent close: wrong audit driver")
    driver = (ROOT / pack["driver"]).read_text(encoding="utf-8")
    expected_checks = expected | set(pack.get("object_checks", ()))
    for command in ("#check", "#print axioms"):
        names = re.findall(rf"^{command} (\S+)$", driver, re.MULTILINE)
        wanted = expected_checks if command == "#check" else expected
        if len(names) != len(wanted) or set(names) != wanted:
            errors.append(f"independent close: {command} target set changed")
    actual = [m.group(1) for pattern in (axiom_audit.TARGET, axiom_audit.CLEAN) for m in pattern.finditer(raw)]
    report = axiom_audit.parse(raw)
    if len(actual) != len(expected) or set(actual) != expected or report != receipt.get("axiom_audit"):
        errors.append("independent close: raw axiom evidence differs from named targets")
    if any(report[k] for k in ("targets_with_sorryAx", "targets_outside_standard_axioms", "conflicting_target_lines")):
        errors.append("independent close: unsupported kernel dependencies")
    for name in expected:
        if not re.search(r"(?m)^" + re.escape(name) + r"(?:\.\{|\s|$)", raw):
            errors.append(f"independent close: full type absent for {name}")
    sources = receipt.get("sources", [])
    if len(sources) != len(pack["sources"]) or {s.get("path") for s in sources} != set(pack["sources"]):
        errors.append("independent close: source/consumer inventory incomplete")
    for source in sources:
        rel = source.get("path")
        if rel not in pack["sources"]:
            continue
        current = (ROOT / rel).read_bytes().replace(b"\r\n", b"\n")
        built = subprocess.run(["git", "show", f"{subject}:{rel}"], cwd=ROOT, capture_output=True)
        if built.returncode or current != built.stdout or sha256_bytes(current) != source.get("sha256"):
            errors.append(f"independent close: source differs from successful audit: {rel}")
    root = (ROOT / "proofs/lean/juris_lean/JurisLean.lean").read_text(encoding="utf-8")
    module = Path(pack["driver"]).relative_to("proofs/lean/juris_lean").with_suffix("").as_posix().replace("/", ".")
    if f"import {module}" not in root.splitlines():
        errors.append("independent close: proof/consumer audit is outside the full build root")
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
    errors = []
    for pack in disp.INDEPENDENT_CLOSE_PACKS:
        independent = load_json(ROOT / pack["receipt"])
        raw = (ROOT / pack["pack"] / "axiom-audit.raw.txt").read_text(encoding="utf-8")
        errors.extend(independent_close_errors(independent, raw, pack))
    if errors:
        return errors, ledger
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
