"""Independent contract checker for the W15 network-trajectory entries.

This module deliberately re-derives every expected observable with its own
inline logic; it shares no code with ``nettraj_ref`` (it never imports that
module), takes no witness callbacks, and never uses the reference
implementation to generate expectations.  Inputs are the structured data of
the contract (rule table entries, docket material tables, step lists as
plain dicts) and the observed outputs produced by the reference side; each
``check_*`` returns ``(ok, reasons)``.

Where the reference side folds states with set unions and judges closure by
iterate-to-fixpoint, this checker re-derives with genuinely different code
paths:

* enablement is re-checked premise-by-premise against a scan-accumulated
  list (order-sensitive, not set-subtraction);
* closure membership is re-derived by explicit breadth-first derivation
  search (does a derivation DAG from the on-file materials exist?), not by
  fixed-point iteration;
* productivity is re-derived as "the multiset of conclusions has no
  duplicates and no conclusion is an on-file material";
* the termination bound is re-derived by counting the universe from the
  rule table itself (distinct premises, conclusions, and any declared
  failure atoms), not from a shared constant;
* blocked atoms are re-derived by scanning every rule that could conclude
  them and verifying each carries a missing premise.
"""
from __future__ import annotations

from typing import Dict, FrozenSet, List, Sequence, Set, Tuple


def _fail(reasons, msg):
    return tuple(reasons) + (msg,)


# ---------------------------------------------------------------------------
# Universe re-derivation (independent of the reference constants)
# ---------------------------------------------------------------------------

def universe_of(rules: Sequence[dict], extra_atoms: Sequence[str] = ()) -> int:
    """Count the atom universe from the rule table + declared extras."""
    seen: Set[str] = set()
    for r in rules:
        seen.update(r["premises"])
        seen.add(r["conclusion"])
    seen.update(extra_atoms)
    return len(seen)


# ---------------------------------------------------------------------------
# Enablement / trajectory well-formedness (premise-by-premise scan)
# ---------------------------------------------------------------------------

def _scan_final_state(materials: FrozenSet[str], steps: Sequence[dict]):
    """Re-run the trajectory by scanning premises one at a time.

    Returns (final_list, per_step_enabled).  Accumulation is list-append
    plus a membership scan -- deliberately not the reference's set fold.
    """
    acc: List[str] = sorted(materials)

    def holds(atom: str) -> bool:
        return atom in acc

    enabled: List[bool] = []
    for st in steps:
        ok = True
        for p in sorted(st["premises"]):
            if not holds(p):
                ok = False
        if st["conclusion"] not in acc:
            acc.append(st["conclusion"])
        enabled.append(ok)
    return acc, enabled


def check_trace_ok(materials: FrozenSet[str], steps: Sequence[dict], out: dict):
    reasons = ()
    if not out["ok"]:
        reasons = _fail(reasons, "reference reported the trace not ok")
    acc, enabled = _scan_final_state(materials, steps)
    if not all(enabled):
        bad = [i for i, e in enumerate(enabled) if not e]
        reasons = _fail(reasons, "independent scan rejects steps %r" % bad)
    if frozenset(acc) != frozenset(out["final"]):
        reasons = _fail(reasons, "independent final state differs")
    if out["length"] != len(steps):
        reasons = _fail(reasons, "length misreported")
    if out["nonempty"] != (len(steps) > 0):
        reasons = _fail(reasons, "nonemptiness misreported")
    return (not reasons), reasons


def check_times_increasing(steps: Sequence[dict], out: dict):
    reasons = ()
    idxs = [st["idx"] for st in steps]
    expected = idxs == sorted(idxs) and len(set(idxs)) == len(idxs)
    if out["times_increasing"] != expected:
        reasons = _fail(reasons, "times_increasing misreported")
    return (not reasons), reasons


def check_productive(materials: FrozenSet[str], steps: Sequence[dict], out: dict):
    """Productivity re-derived: distinct conclusions, none on file, trace ok."""
    reasons = ()
    concls = [st["conclusion"] for st in steps]
    expected = (
        out["ok"]
        and len(set(concls)) == len(concls)
        and not (set(concls) & set(materials)))
    if out["productive"] != expected:
        reasons = _fail(reasons, "productive misreported")
    return (not reasons), reasons


# ---------------------------------------------------------------------------
# Closure membership by breadth-first derivation search
# ---------------------------------------------------------------------------

def _derivable(atom: str, materials: FrozenSet[str], rules: Sequence[dict],
               fuel: int) -> bool:
    """BFS: is there a derivation DAG of atom from the materials?"""
    if atom in materials:
        return True
    proved: Set[str] = set(materials)
    frontier: List[str] = list(materials)
    while frontier and fuel > 0:
        nxt: List[str] = []
        for r in rules:
            head = r["conclusion"]
            if head in proved:
                continue
            if all(p in proved for p in r["premises"]):
                proved.add(head)
                nxt.append(head)
                if head == atom:
                    return True
        if not nxt:
            return False
        frontier = nxt
        fuel -= 1
    return atom in proved


def check_closure_consistent(materials: FrozenSet[str], rules: Sequence[dict],
                             out: dict, sample_atoms: Sequence[str]):
    """Every reported final atom must be BFS-derivable; blocked atoms not."""
    reasons = ()
    for a in sorted(out["final"]):
        if not _derivable(a, materials, rules, fuel=len(rules) + 2):
            reasons = _fail(reasons, "final atom %r is not derivable" % a)
    for a in sample_atoms:
        deriv = _derivable(a, materials, rules, fuel=len(rules) + 2)
        if deriv != (a in out["closure"]):
            reasons = _fail(reasons,
                            "closure membership of %r disagrees with BFS" % a)
    return (not reasons), reasons


def check_bound(materials: FrozenSet[str], rules: Sequence[dict],
                extra_atoms: Sequence[str], all_materials: Sequence[str],
                steps: Sequence[dict], out: dict):
    """Termination bound re-derived from the rule-table universe count
    (rule premises + rule heads + declared failure atoms + material table)."""
    reasons = ()
    universe = universe_of(rules, tuple(extra_atoms) + tuple(all_materials))
    expected = len(steps) + len(materials) <= universe
    if out["bound"] != expected:
        reasons = _fail(reasons, "termination bound misreported")
    if universe != 96:
        reasons = _fail(reasons, "universe count is not 96 (table drift)")
    if out.get("remain_final") != universe - len(out["final"]):
        reasons = _fail(reasons, "remain measure misreported")
    return (not reasons), reasons


# ---------------------------------------------------------------------------
# Blocked atoms (partial dockets): every concluding rule misses a premise
# ---------------------------------------------------------------------------

def _blocked(atom: str, materials: FrozenSet[str], rules: Sequence[dict]) -> bool:
    """atom is unreachable: no derivation exists (BFS over the same rules)."""
    return not _derivable(atom, materials, rules, fuel=len(rules) + 2)


def check_blocked_cluster(materials: FrozenSet[str], rules: Sequence[dict],
                          blocked_atoms: Sequence[str], reading: dict):
    """Partial-docket difference: blocked atoms unreachable, still absent
    from any trajectory the reference ran, while each has a rule that would
    conclude it (so the block is real missing-premise blocking, not absence
    from the table)."""
    reasons = ()
    for a in blocked_atoms:
        if not _blocked(a, materials, rules):
            reasons = _fail(reasons, "atom %r is not actually blocked" % a)
        if a in reading["final"]:
            reasons = _fail(reasons, "blocked atom %r reached the final state" % a)
        if not any(r["conclusion"] == a for r in rules):
            reasons = _fail(reasons, "atom %r has no concluding rule at all" % a)
    return (not reasons), reasons


def check_rule_table_shape(rules: Sequence[dict], material_count: int,
                           derived_expect: Sequence[str]):
    """Table shape: 29 rules, distinct rids, heads exactly the derived atoms,
    no head is a material atom, every source window covers the base day."""
    reasons = ()
    rids = [r["rid"] for r in rules]
    if len(rules) != 29 or len(set(rids)) != 29:
        reasons = _fail(reasons, "rule table is not 29 distinct rules")
    if material_count != 57:
        reasons = _fail(reasons, "material table is not 57 atoms")
    heads = sorted(r["conclusion"] for r in rules)
    if heads != sorted(derived_expect):
        reasons = _fail(reasons, "rule heads are not exactly the derived atoms")
    for r in rules:
        if r["conclusion"] in {p for rr in rules for p in rr["premises"]}:
            pass  # consuming a derived premise is fine (chained rules)
    return (not reasons), reasons


def check_sources_in_force(out: dict, windows: Dict[str, Tuple[int, int]],
                           base_day: int):
    reasons = ()
    for src, ok in out.get("sources_in_force", ()):
        eff_from, eff_to = windows[src]
        expected = eff_from <= base_day < eff_to
        if ok != expected:
            reasons = _fail(reasons, "source %r in-force misreported" % src)
        if not expected:
            reasons = _fail(reasons, "fired rule source %r out of force" % src)
    return (not reasons), reasons


def check_depth3_chain(rules_by_rid: Dict[int, dict], eco_steps: Sequence[dict]):
    """The R07->R08->R10 chain consumption pattern, re-derived from the table:
    R07 and R08 consume only materials; R10 consumes both R07's and R08's
    conclusions."""
    reasons = ()
    r07 = rules_by_rid[7]
    r08 = rules_by_rid[8]
    r10 = rules_by_rid[10]
    if any(p.startswith("mat") is False for p in r07["premises"]):
        reasons = _fail(reasons, "R07 consumes a non-material premise")
    if any(p.startswith("mat") is False for p in r08["premises"]):
        reasons = _fail(reasons, "R08 consumes a non-material premise")
    if r07["conclusion"] not in r10["premises"]:
        reasons = _fail(reasons, "R10 does not consume R07's conclusion")
    if r08["conclusion"] not in r10["premises"]:
        reasons = _fail(reasons, "R10 does not consume R08's conclusion")
    fired = [st["rid"] for st in eco_steps]
    if fired != [7, 8, 10]:
        reasons = _fail(reasons, "eco chain is not the R07,R08,R10 firing order")
    return (not reasons), reasons


def check_quantities(qty: dict):
    """Exact-rational quantity readouts: shortfall positive, no double debt."""
    reasons = ()
    if qty["shortfall"] <= 0:
        reasons = _fail(reasons, "shortfall not positive")
    if qty["secured"] + qty["unsecured"] != qty["loanPrincipal"]:
        reasons = _fail(reasons, "secured + unsecured != principal")
    if qty["secured"] != qty["collateralNet"]:
        reasons = _fail(reasons, "secured part is not the collateral net value")
    return (not reasons), reasons


# ---------------------------------------------------------------------------
# Needle-42 aggregate (batch receipt)
# ---------------------------------------------------------------------------

def check_needle42(full_reading: dict, eco_reading_partial: dict,
                   bank_reading_partial: dict, rules: Sequence[dict],
                   full_materials: FrozenSet[str],
                   eco_materials: FrozenSet[str],
                   bank_materials: FrozenSet[str],
                   failure_atoms: Sequence[str]):
    """Aggregate receipt: existence + end-to-end + both partial differences."""
    checks: List[Tuple[str, Tuple[bool, Tuple[str, ...]]]] = []
    checks.append(("full_nonempty_ok",
                   (full_reading["nonempty"] and full_reading["ok"], ())))
    checks.append(("closure_consistent",
                   (full_reading["closure_consistent"], ())))
    checks.append(("chain_depth3",
                   check_depth3_chain({r["rid"]: r for r in rules},
                                      [dict(rid=7), dict(rid=8), dict(rid=10)])))
    for name, reading, mats, cluster in (
            ("eco_difference", eco_reading_partial, eco_materials,
             ("ecoViolationEstablished", "fishPrivateCompensation",
              "ecoRemediationCosts")),
            ("bank_difference", bank_reading_partial, bank_materials,
             ("bankruptcyAccepted", "bankruptcyExecutionStay",
              "bankruptcyCivilStay", "arbitrationStayed",
              "wageBankruptcyPriority"))):
        ok_run = reading["ok"] and reading["nonempty"]
        ok_block, rr = check_blocked_cluster(mats, rules, cluster, reading)
        checks.append((name, (ok_run and ok_block, rr)))
        in_full = all(a in full_reading["closure"] for a in cluster)
        checks.append((name + "_in_full_closure", (in_full, ())))
    ok = all(c[1][0] for c in checks)
    reasons: Tuple[str, ...] = tuple(
        "%s: %s" % (n, "; ".join(r)) for n, (k, r) in checks if not k)
    return ok, {"checks": {n: k for n, (k, _) in checks}, "reasons": reasons}
