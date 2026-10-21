"""Source inventory only. Never executes Lean or marks a clause formally proved."""
import hashlib
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[5]
sys.path.insert(0, str(ROOT))
from scripts.ci.changed_lean_modules import strip_comments_strings

PREFIX = "JurisLean.Candidates.Final20261021"
ORDER = "Interfaces Representation Compiler Harness Transactions Temporal EvidenceProcedure Authorization Progress Ledger Trace Learning Probability Calibration Decision Behavior Policy RSI Feedback Iteration Pipeline Acceptance".split()

# Reviewed boundary mappings, not a claim that the proposed spelling existed.
BOUNDARIES = {
    "proposed_payment_binding": ["Pipeline.interpretPayment", "Ledger.validationError"],
    "proposed_legal_allocation": ["Ledger.performance"],
    "proposed_quantity_cash_receipt": ["Ledger.commitPayment"],
    "proposed_probability_and_amount": ["Decision.evaluate"],
    "proposed_bounded_prediction": ["Calibration.proposed_calibration_support_gate"],
    "proposed_prediction_or_harness": ["Pipeline.runBound"],
}

# A source body can implement a proper subset of a frozen clause. Preserve the
# missing subclaims explicitly; a successful build cannot close these rows.
GAPS = {
    "U07.1": "Reverse separation and non-surjective-encode examples and full observation decoding still need acceptance.",
    "U07.2": "Fresh CI and actual semantic compatibility of supplied layers remain separate.",
    "U07.3": "Fresh CI; source truth and arbitrary extractor fidelity are not proved by the fixed-history construction.",
    "U03.1": "Provenance DAG validation and robust-intersection countermodel not yet connected to the executable finite closure.",
    "U03.2": "Connect executable stable finite closure to semantic derivability; incomplete fuel is not completeness.",
    "U02.1": "Actual-world and actual-successor refinement of the concrete pipeline table remains unproved.",
    "U02.2": "Abstract transaction safety bodies are present; refine Ledger receipts/U and actual pipeline steps to that protocol, and close the complete-read CAS snapshot lemma.",
    "U02.3": "Generator support coverage and common-idle/empty-successor counterexamples not fully discharged.",
    "U02.4": "Conditional-law tower/filtration theorem, random budgets, and H=B countermodel remain unformalized; union and partition sublemmas do not close them.",
    "U08.1": "Late retroactive-transition and mutable-current-status countermodels still require complete Lean acceptance.",
    "U10.1": "Tie named authorization and append/refresh to the same actual protected transaction; content alone is not external authority.",
    "U10.2": "Numeric/cash/freshness invariant is implemented; full identity/receipt correspondence, authorized Gamma field frame, and concrete pipeline-to-Step refinement remain open.",
    "U08.2": "Current versus reachable exhaustion and nonempty-state preservation of every observation remain partially formalized.",
    "U08.3": "Four-state/product and countermodels are present; full finite dependency-policy reflection and compatibility-world classification still need audit.",
    "U10.3": "Connect per-operation abstract simulation length and business-observation faithfulness, including zero-step prohibitions.",
    "U09.1": "General scalar/list conservation and actual same-case calls are present; full receipt/U invariant and quantitative projection to the reused vector afterStream remain to prove.",
    "U09.2": "Finite closed-account and per-account sums present. Actual occurrence and completeness of boundary accounts remain external premises.",
    "U09.3": "Weak allocation, metadata, accrual, None, restitution interfaces are present; full greedy prefix/ordering and same-institution legal-effect countermodels remain.",
    "U01.0": "MGF/upper/two-tail ingredients present; assemble exact bounded-sum two-tail statement and D=0 branch without losing the strict-positive threshold.",
    "U01.1": "Sub-Gaussian fixed-class union and ERM algebra present; finish iid sample-mean/sqrt radius specialization and representation-risk decomposition.",
    "U01.2": "Finite rational 0-1 bridge present; general measurable bounded-loss integration and jointly estimated bridge budget remain.",
    "U01.3": "Finite rational TV bound only; the manuscript general measurable-distribution TV theorem is UNPROVED, not reduced to this finite support.",
    "U01.4": "Full training/target/deployment and independent-versus-copied variance witness family still unformalized.",
    "U04.1": "Finite posterior normalization is not Beta conjugacy or its predictive bridge; both and 5/6 countermodel remain UNPROVED.",
    "U04.2": "Real ratio enclosure present; width, beta integrals, three-event sharp identified set and contamination subclaims remain.",
    "U04.3": "UNFORMALIZED: full-coordinate ridge logistic minimizer existence/uniqueness and unpenalized-intercept counterexample.",
    "U04.4": "Effective-count result type and zero denominator branch present; full covariance expansion and PSD/degenerate witness remain.",
    "U04.5": "Identity types and LR16/LR4 arithmetic present; general joint likelihood/copy and sigma-field information argument remain.",
    "U05.1": "UNFORMALIZED: exchangeable-rank split conformal theorem, ties, infinite threshold and conditional group scope.",
    "U05.2": "Bernoulli algebra and ratio gate present; conditional-expectation Brier decomposition, simultaneous threshold coverage and rare-group examples remain.",
    "U06.1": "Finite free-information comparison present; full Bellman optimum, blocked terminal convention and nonrectangular counterexample remain.",
    "U06.2": "Universal allowed-deviation real payoff transfer present; mixed expectations and explicit strategy/tree bridge remain.",
    "U06.3": "Rational AST, typed gate and executable IR present; arbitrary interval multiplication enclosure and general uncertainty comparison remain.",
    "U06.4": "Three real slope-direction theorems present; q-in-[0,1] out-of-range corollaries still need acceptance.",
    "U06.5": "UNFORMALIZED: noisy-information/bargaining tree and finite mixed-equilibrium existence with verified background. T113 stays excluded OPEN.",
    "U11.1": "Observational-equivalence/ATE countermodel and transport arithmetic present; g formula, K1/K2 selection, sharp support gaps and measurement bridges remain.",
    "U12.1": "Finite IPW cancellation only; complete causal/measurement interpretation and support-gap identified range remain.",
    "U12.2": "Complete metric contraction theorem present; damping, oscillation and noncontraction sufficiency counterexamples remain.",
    "U12.3": "Clipping identity only; weighted uniform selection, MAR and full sequential-kernel likelihood-ratio theorem remain UNPROVED.",
    "U12.4": "Two incentive inequalities and distinguishability counterexample present; verify full frozen model acceptance in CI.",
    "U13.1": "Read-set noninterference present; lawful statistical-evidence input-change counterexample and authority integration remain.",
    "U13.2": "Five preparations and personal/data/condition frames present; complete authorized rule/mechanism load and persistent storage refinement remain.",
    "U13.3": "Bijective prediction transfer present; same-loss risk transfer and unsupported-domain witnesses remain.",
    "U13.4": "Absent personal/population/prior/retrieval branching present; validate distinct provenance/scope policies for the fallback sources and nonidentification witnesses.",
    "U14.1": "Acceptance algebra, identity/readback gate and label conflicts present; independent statistical validation, adaptive conditional budgets and service-load integration remain.",
    "U15.1": "Finite real telescoping bound present; finite-state strict-improvement length and no-parameter-convergence counterexample remain.",
    "U14.2": "Independent cluster upper tail present; full two-tail normalized N^2/sum(nj^2) specialization, degenerate sizes, and n_eff witness remain.",
    "U15.2": "Preserved-prediction finite risk identity present; key-point regression and finite-observation indistinguishability examples remain.",
    "U15.3": "Exact two-point risks and actual second-round-state consumer present; complete five evidence levels and external load readback path remain.",
    "U00": "Actual finite source-to-decision-to-two-payment-to-feedback paths present. All 50 subclaims, common statistical law, full operation refinement and authorized Loaded consumption are NOT closed.",
}

def write(name, data):
    (HERE/name).write_text(json.dumps(data, ensure_ascii=False, indent=2)+"\n", encoding="utf-8")


def main():
    texts = {name: (HERE/(name+".lean")).read_text(encoding="utf-8") for name in ORDER}
    clean = {name: strip_comments_strings(text) for name, text in texts.items()}
    declarations = []
    for module, code in clean.items():
        namespace = re.search(r"^namespace (\S+)", code, re.M)[1]
        for m in re.finditer(r"^(theorem|def|structure|inductive)\s+([\w.]+)", code, re.M):
            declarations.append({"name": namespace+"."+m[2], "short": m[2], "kind": m[1],
                                 "module": module, "file": module+".lean",
                                 "line": code[:m.start()].count("\n")+1})
    audit = [f"import {PREFIX}.Acceptance", "", "-- Fresh CI types/axioms, not baseline evidence."]
    for d in declarations:
        if d["kind"] == "theorem":
            audit += ["#check "+d["name"], "#print axioms "+d["name"]]
        d["consumers"] = []
        pattern = re.compile(r"(?<![\w.])(?:"+re.escape(d["module"])+r"\.)?"+re.escape(d["short"])+r"(?![\w])")
        for mod, code in clean.items():
            for i, line in enumerate(code.splitlines(), 1):
                if mod == d["module"] and i == d["line"]:
                    continue
                if (mod == d["module"] or d["module"]+"."+d["short"] in line) and pattern.search(line):
                    d["consumers"].append({"file": mod+".lean", "line": i})
    (HERE/"AxiomAudit.lean").write_text("\n".join(audit)+"\n", encoding="utf-8")
    (HERE/"CIAll.lean").write_text("\n".join(f"import {PREFIX}.{m}" for m in ORDER+["AxiomAudit"])+"\n", encoding="utf-8")
    write("declarations.json", {"status": "STATIC_SOURCE_INVENTORY_NOT_LEAN_EVIDENCE", "declarations": [
        d for d in declarations if d["kind"] == "theorem" or d["short"].startswith("proposed_")]})

    old = json.loads((HERE/"50_clause_status.json").read_text(encoding="utf-8"))
    rows = []
    for row in old["rows"]:
        r = {k: v for k, v in row.items() if k not in {"candidate_reference", "candidate_evidence_status"}}
        r["original_mapping"] = "50条施工映射.json::"+r["clause"]
        module = Path(r["planned_file"]).stem
        matches = [d for d in declarations if d["kind"] == "theorem" and d["short"].startswith(r["planned_declaration_stem"])]
        if r["clause"] == "U02.2":
            matches = [d for d in declarations if d["module"] == "Transactions" and d["kind"] == "theorem"]
        r.update(formal_ci="CI_NOT_RUN", runtime_status="NOT_RUN", closure="OPEN_FULL_SCOPE_AND_CI",
                 implementation="PARTIAL_CANDIDATE_SOURCE" if matches else "UNFORMALIZED_FULL_TARGET",
                 declarations=[{k: d[k] for k in ["name", "file", "line", "consumers"]} for d in matches],
                 remaining_obligations=GAPS[r["clause"]])
        rows.append(r)
    write("50_clause_status.json", {"baseline": old["baseline"], "scope": old["scope"], "rows": rows})

    proposed = json.loads((HERE/"proposed_825792b.json").read_text(encoding="utf-8"))
    for r in proposed["rows"]:
        found = [d for d in declarations if d["short"] == r["symbol"]]
        if not found and r["symbol"] in BOUNDARIES:
            found = [d for d in declarations if d["module"]+"."+d["short"] in BOUNDARIES[r["symbol"]]]
            r["mapping_scope"] = "Reviewed new mathematical candidate boundary; no baseline symbol or product integration is asserted."
        r["lean_target"] = [d["name"] for d in found] or None
        r["consumer"] = [x for d in found for x in d["consumers"]] or None
        r["status"] = "SOURCE_PRESENT_AWAITING_CI_AND_SCOPE_AUDIT" if found else "UNLOCATED_IMPLEMENTATION"
        r["baseline_825792b"] = "NEW" if found else "UNLOCATED"
        r["formal_ci"] = "CI_NOT_RUN"
    write("proposed_825792b.json", proposed)
    write("module_inventory.json", {"status": "UNCOMPILED_CANDIDATES", "modules": [
        {"file": m+".lean", "sha256": hashlib.sha256((HERE/(m+".lean")).read_bytes()).hexdigest(),
         "theory": [r["clause"] for r in rows if Path(r["planned_file"]).stem == m],
         "theorems": [d["name"] for d in declarations if d["module"] == m and d["kind"] == "theorem"],
         "consumer_evidence": "declarations.json (actual lexical references, not a refinement proof)",
         "formal_ci": "CI_NOT_RUN"} for m in ORDER]})
    print("Source inventories and CIAll refreshed; no formal CI status promoted.")


if __name__ == "__main__":
    main()
