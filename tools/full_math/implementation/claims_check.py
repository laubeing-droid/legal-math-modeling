"""Independent contract checker for group-04 claims/issues (D029-D036).

This module deliberately re-derives every expected value from the demand
contract with its own inline logic (while-scans, negated-condition forms);
it shares no code with ``claims_ref`` (it never imports that module),
takes no witness callbacks, and never uses the main implementation to
generate expectations.  Each ``check_D0XX`` returns ``(ok, reasons)``:
``ok`` is True exactly when the observed intermediate result satisfies the
demand's contract on the given structured input.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Sequence


def _fail(reasons, msg):
    return tuple(reasons) + (msg,)


# ---------------------------------------------------------------------------
# D029
# ---------------------------------------------------------------------------


def check_D029(rule_table: Sequence[tuple], primary: str, alternative: str,
               primary_holds: bool, alt_holds: bool, principal_amount,
               incidental_amount, out: dict):
    reasons = ()
    # independent while-scan: candidates are exactly the premise-true rows
    expected = []
    i = 0
    while i < len(rule_table):
        if rule_table[i][1] is True:
            expected.append(rule_table[i][0])
        i += 1
    if tuple(out["candidates"]) != tuple(expected):
        reasons = _fail(reasons, "candidates are not the premise-true rows")
    # every candidate is a table row with a true premise (and vice versa)
    for c in out["candidates"]:
        hit = False
        i = 0
        while i < len(rule_table):
            if rule_table[i][0] == c and rule_table[i][1] is True:
                hit = True
            i += 1
        if not hit:
            reasons = _fail(reasons,
                            f"candidate {c!r} has no premise-true table row")
    for row in rule_table:
        if row[1] is True and row[0] not in out["candidates"]:
            reasons = _fail(reasons,
                            f"premise-true row {row[0]!r} is not a candidate")
    # the award carrier: primary only when it holds, the alternative only
    # when the primary does not — mutually exclusive alternatives are
    # never both fully awarded by default
    expected_awards = []
    if primary_holds:
        expected_awards.append(primary)
    elif alt_holds:
        expected_awards.append(alternative)
    if tuple(out["awards"]) != tuple(expected_awards):
        reasons = _fail(reasons,
                        "award carrier diverges from the exclusivity rule")
    if primary_holds and alternative in out["awards"]:
        reasons = _fail(reasons,
                        "a mutually exclusive alternative was co-awarded "
                        "with the primary by default")
    if primary_holds and primary not in out["awards"]:
        reasons = _fail(reasons, "the holding primary claim lost its award")
    # principal and incidental are independent debt items: separate
    # carriers with their own kind tags and verbatim amounts
    if out["debts"]["principal"]["kind"] == \
            out["debts"]["incidental"]["kind"]:
        reasons = _fail(reasons, "principal and incidental lost their own "
                                 "kind tags")
    if out["debts"]["principal"]["amount"] != principal_amount or \
            out["debts"]["incidental"]["amount"] != incidental_amount:
        reasons = _fail(reasons, "debt amounts were altered or merged")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D030
# ---------------------------------------------------------------------------

_STAGE_TAGS = ("filed", "allowed", "supported", "awarded")


def check_D030(filed_rows: Sequence[tuple], allowed_table: Sequence[tuple],
               out: dict):
    reasons = ()
    # independent while-scans for the four carriers
    filed, supported, awarded = [], [], []
    i = 0
    while i < len(filed_rows):
        claim_id, sup, awd = filed_rows[i]
        filed.append(claim_id)
        if sup is True:
            supported.append(claim_id)
        if sup is True and awd is True:
            awarded.append(claim_id)
        i += 1
    allowed = []
    i = 0
    while i < len(allowed_table):
        if allowed_table[i][1] is True:
            allowed.append(allowed_table[i][0])
        i += 1
    if tuple(out["filed"]) != tuple(filed):
        reasons = _fail(reasons, "filed carrier diverges")
    if tuple(out["supported"]) != tuple(supported):
        reasons = _fail(reasons, "supported carrier diverges")
    if tuple(out["awarded"]) != tuple(awarded):
        reasons = _fail(reasons, "awarded carrier diverges")
    if tuple(out["allowed"]) != tuple(allowed):
        reasons = _fail(reasons, "allowed carrier diverges")
    # explicit chain: awarded ⊆ supported ⊆ filed
    for c in awarded:
        if c not in supported or c not in filed:
            reasons = _fail(reasons,
                            f"awarded claim {c!r} broke the stage chain")
    for c in supported:
        if c not in filed:
            reasons = _fail(reasons,
                            f"supported claim {c!r} is not filed")
    # the four stage names are pairwise distinct carriers
    tags = out.get("stages") or ()
    i = 0
    while i < len(tags):
        j = 0
        while j < len(tags):
            if i != j and tags[i] == tags[j]:
                reasons = _fail(reasons, "stage carriers are not distinct")
            j += 1
        i += 1
    # echoing the filed list never earns the all-allowed certificate when
    # the allowed table has rows beyond the filed claims
    beyond = []
    i = 0
    while i < len(allowed):
        if allowed[i] not in filed:
            beyond.append(allowed[i])
        i += 1
    if beyond and out["echo_is_all_allowed"]:
        reasons = _fail(reasons, "the echo of the filed list was certified "
                                 "as covering all allowed claims")
    if not beyond and not out["echo_is_all_allowed"]:
        reasons = _fail(reasons, "a complete allowed coverage was denied "
                                 "without cause")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D031
# ---------------------------------------------------------------------------


def check_D031(rows: Sequence[tuple], defense_rows: Sequence[tuple],
               out: dict):
    reasons = ()
    # each relation exports its own premise/conclusion, all sharing the
    # delivered sum; distinct relations are distinct scenario entries
    scenarios = out["scenarios"]
    if len(scenarios) != len(rows):
        reasons = _fail(reasons, "scenario rows were merged or dropped")
    i = 0
    while i < len(rows):
        rel, prem, concl = rows[i]
        found = None
        j = 0
        while j < len(scenarios):
            if scenarios[j]["relation"] == rel:
                found = scenarios[j]
            j += 1
        if found is None:
            reasons = _fail(reasons,
                            f"scenario {rel!r} vanished from the export")
        else:
            if found["premise"] != prem or found["conclusion"] != concl:
                reasons = _fail(reasons,
                                f"scenario {rel!r} lost its own premise/"
                                "conclusion")
            if found["shared_delivery"] != out["scenarios"][0][
                    "shared_delivery"]:
                reasons = _fail(reasons,
                                f"scenario {rel!r} does not share the "
                                "delivered sum")
        i += 1
    # independent while-scan of the exclusive routing
    admissions, contras, rejected = [], [], []
    i = 0
    while i < len(defense_rows):
        prop, adm, con = defense_rows[i]
        if adm and con:
            rejected.append(prop)
        elif adm:
            admissions.append(prop)
        elif con:
            contras.append(prop)
        i += 1
    if sorted(out["admissions"]) != sorted(admissions):
        reasons = _fail(reasons, "admission carrier diverges from the "
                                 "exclusive routing")
    if sorted(out["contras"]) != sorted(contras):
        reasons = _fail(reasons, "contrary-fact carrier diverges from the "
                                 "exclusive routing")
    if sorted(out["rejected_dual"]) != sorted(rejected):
        reasons = _fail(reasons, "dual-flagged rows were not flagged for "
                                 "review")
    # no proposition sits in both carriers (never admission AND contrary)
    for p in out["admissions"]:
        if p in out["contras"]:
            reasons = _fail(reasons,
                            f"proposition {p!r} is both an admission and "
                            "the contrary fact")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D032
# ---------------------------------------------------------------------------

_DECLARED_PAIRS = (("valid", "principal"), ("invalid", "yield"))


def check_D032(claim_id: str, input_version: str, out: dict):
    reasons = ()
    # both branches share the claim identity and the input version
    branches = out["branches"]
    if len(branches) != 2 or branches[0][0] == branches[1][0]:
        reasons = _fail(reasons, "the two branches are not distinct rows")
    for b in branches:
        if b[1] != claim_id or b[2] != input_version:
            reasons = _fail(reasons,
                            f"branch {b[0]!r} broke the shared identity/"
                            "version")
    # the applicable-rule table is the declared closed one
    got_pairs = tuple(out["allowed_rule_pairs"])
    if got_pairs != _DECLARED_PAIRS:
        reasons = _fail(reasons, "the rule table is not the declared "
                                 "closed set")
    # a stitched pair is allowed iff it is declared: the cross-branch
    # (valid, yield) and (invalid, principal) are rejected
    for regime, kind in (("valid", "principal"), ("invalid", "yield"),
                         ("valid", "yield"), ("invalid", "principal")):
        expected = (regime, kind) in _DECLARED_PAIRS
        hit = None
        i = 0
        while i < len(out["stitched"]):
            if out["stitched"][i]["pair"] == (regime, kind):
                hit = out["stitched"][i]
            i += 1
        if hit is None or hit["allowed"] != expected:
            reasons = _fail(reasons,
                            f"stitched pair {(regime, kind)!r} diverges "
                            "from the declared table")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D033
# ---------------------------------------------------------------------------


def check_D033(due_met: bool, defense_raised: bool, acknowledged: bool,
               ack_day: int, restart_days: int, out: dict):
    reasons = ()
    # independent derivation: dismissal needs BOTH switches
    dismissed = bool(due_met and defense_raised)
    if out["dismissed"] != dismissed:
        reasons = _fail(reasons, "dismissal diverges from the two-switch "
                                 "rule")
    if out["claim_alive"] != (not dismissed):
        reasons = _fail(reasons, "claim-alive diverges from the dismissal "
                                 "verdict")
    # expiry alone never deletes the claim
    if due_met and not defense_raised:
        if out["dismissed"] or not out["claim_alive"]:
            reasons = _fail(reasons, "an expired period alone dismissed "
                                     "the claim (no defense was raised)")
    # the restart is its own ledger, never merged into the expiry decision
    if out["restart_from_ack"] != ack_day + restart_days:
        reasons = _fail(reasons, "the interruption restart diverges from "
                                 "its own ledger")
    # the acknowledgment switch is not read by the dismissal computation:
    # flipping it leaves dismissal untouched
    if out["acknowledged"] != bool(acknowledged):
        reasons = _fail(reasons, "the acknowledgment switch was altered")
    if out["acknowledged"] and out["dismissed"] != \
            bool(due_met and defense_raised):
        reasons = _fail(reasons, "the acknowledgment switch leaked into "
                                 "the expiry decision")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D034
# ---------------------------------------------------------------------------


def check_D034(rows: Sequence[tuple], support_established: bool, out: dict):
    reasons = ()
    nodes = out["nodes"]
    # every row's five links are exported separately and verbatim
    if len(nodes) != len(rows):
        reasons = _fail(reasons, "issue nodes were merged or dropped")
    i = 0
    while i < len(rows):
        issue, claim, rebuttal, party, target = rows[i]
        found = None
        j = 0
        while j < len(nodes):
            if nodes[j]["issue"] == issue:
                found = nodes[j]
            j += 1
        if found is None:
            reasons = _fail(reasons, f"issue {issue!r} vanished from the "
                                     "graph")
        else:
            if (found["claim"], found["rebuttal"], found["responsible_party"],
                    found["attack_target"]) != (claim, rebuttal, party,
                                                target):
                reasons = _fail(reasons,
                                f"issue {issue!r} lost one of its five "
                                "links")
        i += 1
    # a claim is proved only through its own support set — the proof
    # status never reads the rebuttal side
    expected = bool(support_established)
    if out["proved"]["proved"] != expected:
        reasons = _fail(reasons, "the proof status diverges from the "
                                 "claim's own support set")
    if not support_established and out["proved"]["proved"]:
        reasons = _fail(reasons, "a claim was proved without its own "
                                 "support (the rebuttal jump was taken)")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D035
# ---------------------------------------------------------------------------


def check_D035(defense_rows: Sequence[tuple], out: dict):
    reasons = ()
    # every defense links the claim and evidence it responds to, verbatim
    links = out["links"]
    i = 0
    while i < len(defense_rows):
        prop, claim, evidence = defense_rows[i][0], defense_rows[i][1], \
            defense_rows[i][2]
        found = None
        j = 0
        while j < len(links):
            if links[j]["prop"] == prop:
                found = links[j]
            j += 1
        if found is None:
            reasons = _fail(reasons, f"defense {prop!r} lost its target "
                                     "links")
        elif (found["responds_claim"], found["responds_evidence"]) != \
                (claim, evidence):
            reasons = _fail(reasons,
                            f"defense {prop!r} points at the wrong target")
        i += 1
    # independent while-scans for the two carriers
    admissions, review = [], []
    i = 0
    while i < len(defense_rows):
        prop, _claim, _ev, admit, sourced = defense_rows[i]
        if admit and sourced:
            admissions.append(prop)
        elif admit:
            review.append(prop)
        i += 1
    if sorted(out["admissions"]) != sorted(admissions):
        reasons = _fail(reasons, "the record carrier is not the sourced "
                                 "admissions")
    if sorted(out["review_required"]) != sorted(review):
        reasons = _fail(reasons, "the review carrier is not the unsourced "
                                 "admissions")
    # every written admission is backed by a sourced row
    for p in out["admissions"]:
        backed = False
        i = 0
        while i < len(defense_rows):
            if defense_rows[i][0] == p and defense_rows[i][4] is True:
                backed = True
            i += 1
        if not backed:
            reasons = _fail(reasons,
                            f"admission {p!r} was written without an "
                            "authorization source")
    # an unsourced admission is flagged for review, never silently written
    for p in review:
        if p in out["admissions"]:
            reasons = _fail(reasons,
                            f"unsourced admission {p!r} was silently "
                            "written into the record")
    return not reasons, reasons


# ---------------------------------------------------------------------------
# D036
# ---------------------------------------------------------------------------


def check_D036(parties_shares: Sequence[tuple], total: Fraction,
               external_paid: Sequence[tuple], out: dict):
    reasons = ()
    # internal rows: the joint model output (party, method, share,
    # share × total), each row its own party
    internal = out["internal"]
    if len(internal) != len(parties_shares):
        reasons = _fail(reasons, "internal rows were merged or dropped")
    i = 0
    while i < len(parties_shares):
        party, share = parties_shares[i]
        found = None
        j = 0
        while j < len(internal):
            if internal[j]["party"] == party:
                found = internal[j]
            j += 1
        if found is None:
            reasons = _fail(reasons, f"liable party {party!r} vanished "
                                     "from the joint model")
        else:
            if found["share"] != share or \
                    found["amount"] != share * total or \
                    found["method"] != "proportional":
                reasons = _fail(reasons,
                                f"party {party!r}'s joint (method, share, "
                                "amount) row was altered")
        i += 1
    # distinct parties stay distinct rows
    i = 0
    while i < len(parties_shares):
        j = 0
        while j < len(parties_shares):
            if i != j and parties_shares[i][0] == parties_shares[j][0]:
                reasons = _fail(reasons, "one party carries two internal "
                                         "rows")
            j += 1
        i += 1
    # the joint model conserves the total
    zero = Fraction(0)
    internal_total = zero
    i = 0
    while i < len(internal):
        internal_total += internal[i]["amount"]
        i += 1
    if internal_total != total:
        reasons = _fail(reasons, "the internal share ledger does not "
                                 "conserve the total")
    # external is its own per-obligor ledger, verbatim and conserving
    external = out["external"]
    if len(external) != len(external_paid):
        reasons = _fail(reasons, "external rows were merged or dropped")
    i = 0
    while i < len(external_paid):
        party, paid = external_paid[i]
        found = None
        j = 0
        while j < len(external):
            if external[j]["party"] == party:
                found = external[j]
            j += 1
        if found is None or found["paid"] != paid:
            reasons = _fail(reasons,
                            f"external payment of {party!r} was altered")
        i += 1
    external_total = zero
    i = 0
    while i < len(external):
        external_total += external[i]["paid"]
        i += 1
    if external_total != total:
        reasons = _fail(reasons, "the external payment ledger does not "
                                 "conserve the total")
    # the external ledger is never read as a per-capita proportional
    # award: when the declared payments are not uniform, the carrier must
    # not be replaced by (or reported as) the uniform per-capita split
    per_capita = total / len(external_paid) if external_paid else None
    uniform = per_capita is None or \
        all(paid == per_capita for _p, paid in external_paid)
    if not uniform:
        per_capita_rows = tuple({"party": p, "paid": per_capita}
                                for p, _paid in external_paid)
        if tuple(out["external"]) == per_capita_rows:
            reasons = _fail(reasons, "the external ledger was replaced by "
                                     "the per-capita proportional split")
        if "external_is_per_capita" in out and \
                out["external_is_per_capita"]:
            reasons = _fail(reasons, "an unequal external ledger was "
                                     "reported as a per-capita "
                                     "proportional award")
    return not reasons, reasons
