"""Source inventory only. Never executes Lean or marks a clause formally proved."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
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

# Selected synthetic witnesses. Indirect Pipeline fixtures exercise a chain of
# definitions; they never certify every theorem in an imported module.
EXAMPLES = {
    "Interfaces": (["a_u09_three_observations"], ["n_exact_half_and_currency", "n_poststate_name_not_binding"]),
    "Representation": (["a07_1_identity_observation_separates"], ["n07_1_constant_family_not_separating", "n07_1_retraction_need_not_encode_surjectively", "n07_observation_wrong_relation"]),
    "Compiler": (["u00_pipeline_success"], ["n03_incomplete_fuel_is_not_closure", "n03_must_facts_closure_is_not_robust_closure", "n03_missing_exception_is_not_positive_witness"]),
    "Harness": (["a02_common_idle_remains_allowed"], ["n05_raising_score_threshold_increases_risk"]),
    "Transactions": (["a02_transaction_actual_commit", "a02_transaction_actual_replay"], ["n02_cancelled_attempt_no_commit"]),
    "Temporal": (["a08_event_specific_versions"], ["n08_latest_case_time_wrong_for_first_event"]),
    "EvidenceProcedure": (["a08_insufficient_but_lawfully_closed"], ["n08_2_missing_opportunity", "n08_4_timeout_not_lawful_closure"]),
    "Authorization": (["u00_pipeline_success"], ["n10_authorization_binds_full_payload", "n_pipeline_score_does_not_authorize"]),
    "Progress": ([], []),
    "Ledger": (["a_u09_continuous_10_7_7", "a_zero_yes_writes_U", "a_rest_claim_then_eligibility", "a_restpay_only_n3"], ["n_a1_layer_collapse", "n_non_continuous_consume", "n_unknown_does_not_burn_U", "n_burned_by_unknown", "n1_premature_cash", "n_rest_not_eligible", "n2_auto_full_refund", "n3_accrual_cash_collapse"]),
    "Trace": (["a_opening_invariant", "a_two_actual_commits_preserve_receipts"], ["n_non_continuous_consume", "n_poststate_name_not_binding"]),
    "Learning": ([], []),
    "Probability": ([], ["n04_zero_variance_not_finite_count"]),
    "Calibration": (["u00_pipeline_success"], ["n_pipeline_target_mismatch"]),
    "Decision": (["a06_risk_gate_precedes_expected_value"], ["n_exact_half_and_currency", "n06_probability_has_no_money_dimension", "n06_duplicate_cash_identity"]),
    "Behavior": (["u00_pipeline_success"], ["n11_window_not_mature_negative_unknown", "n_pipeline_zero_balance_no_external_label"]),
    "Policy": (["u00_pipeline_success"], ["n12_support_gap_not_smoothed"]),
    "RSI": (["u00_pipeline_success"], ["n13_absent_is_not_half_probability"]),
    "Feedback": (["u00_pipeline_success"], ["n14_evaluated_is_not_loaded", "n14_wrong_bytes_do_not_load", "n14_self_suggestion_is_not_external_label"]),
    "Iteration": (["u00_pipeline_success"], []),
    "Pipeline": (["u00_pipeline_success"], ["u00_pipeline_reject", "u00_pipeline_unknown", "n_pipeline_unresolved_identity", "n_pipeline_target_mismatch", "n_pipeline_decision_payload_mismatch", "n_pipeline_zero_balance_no_external_label"]),
    "Acceptance": (["u00_pipeline_success"], ["u00_pipeline_reject", "u00_pipeline_unknown"]),
}

# Historical gap prose. Live formal_ci rows do not copy it: exact_scope and
# remaining_obligations stay empty after the tip artifact's axiom audit is
# re-extracted. The verbatim manuscript text is pinned in
# evidence/ci-tip-e87543d8/scope-archive.json, carried forward from
# evidence/ci-tip-966b9373/scope-archive.json. This dict is not a proof.
GAPS = {
    "U07.1": "Retraction, observation monotonicity, reverse-separation and non-surjective-encode witnesses have candidate bodies. Full observation/history decoding acceptance and fresh CI remain.",
    "U07.2": "Fresh CI and actual semantic compatibility of supplied layers remain separate.",
    "U07.3": "Fresh CI; source truth and arbitrary extractor fidelity are not proved by the fixed-history construction.",
    "U03.1": "Provenance DAG validation and robust-intersection countermodel not yet connected to the executable finite closure.",
    "U03.2": "Accepted checked closures are connected to semantic derivability; insufficient fuel returns checkIncomplete. A verified finite carrier/fuel bound for this list implementation is still missing.",
    "U02.1": "Actual-world and actual-successor refinement of the concrete pipeline table remains unproved.",
    "U02.2": "Abstract transaction safety, actual commit/replay/cancel examples and complete-read CAS snapshot lemma have candidate bodies. Full refinement of concrete Ledger/Pipeline into Store/Trace, including cancellation and external occurrences, remains open.",
    "U02.3": "Generator support coverage and common-idle/empty-successor counterexamples not fully discharged.",
    "U02.4": "Conditional-law tower/filtration theorem, random budgets, and H=B countermodel remain unformalized; union and partition sublemmas do not close them.",
    "U08.1": "Late retroactive-transition and mutable-current-status countermodels still require complete Lean acceptance.",
    "U10.1": "The actual full-context authorized Pipeline refresh is linked to Trace.Step. Complete protocol refinement and external legal authority evidence remain open; a reference alone does not prove authority.",
    "U10.2": "Numeric/cash/freshness plus key/receipt/cash-backing invariant, actual consume-to-Step, and two-payment known-post refinement have candidate bodies. Full mixed-operation coverage, Gamma frame/read-domain correspondence and service refinement remain open.",
    "U08.2": "Current versus reachable exhaustion and nonempty-state preservation of every observation remain partially formalized.",
    "U08.3": "Four-state/product and countermodels are present; full finite dependency-policy reflection and compatibility-world classification still need audit.",
    "U10.3": "Connect per-operation abstract simulation length and business-observation faithfulness, including zero-step prohibitions.",
    "U09.1": "General list conservation, receipt/U/cash-backing coherence, actual mixed-trace at-most-once safety, and scalar/vector stream balance refinement have candidate bodies. Full legal allocation effects, receipt revision ordering/cash uniqueness and product-protocol refinement remain open.",
    "U09.2": "Finite closed-account and per-account sums present. Actual occurrence and completeness of boundary accounts remain external premises.",
    "U09.3": "Weak allocation, metadata, accrual, None, restitution interfaces are present; full greedy prefix/ordering and same-institution legal-effect countermodels remain.",
    "U01.0": "Exact independent bounded-sum two-tail statement and D=0 null-tail branch, both at strictly positive thresholds, have candidate proof bodies. Fresh Lean CI, axiom audit and assumption/scope review remain required.",
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
    "U14.2": "Normalized independent-cluster two-tail bound with N=sum sizes>0, derived positive sum of squares, and 99/1 effective-size witness have candidate bodies. Zero-N rejection, endogenous-size/common-cause counterexamples and fresh CI remain.",
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
    audit = [f"import {PREFIX}.{module}" for module in ORDER]
    audit += ["", "-- Fresh CI types/axioms, not baseline evidence."]
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
    (HERE/"AxiomAudit.lean").write_text("\n".join(audit)+"\n", encoding="utf-8", newline="\n")
    (HERE/"CIAll.lean").write_text("\n".join(f"import {PREFIX}.{m}" for m in ORDER+["AxiomAudit"])+"\n", encoding="utf-8", newline="\n")
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
                 consumers=[x for d in matches for x in d["consumers"]],
                 remaining_obligations=[])
        rows.append(r)
    missing = [r["clause"] for r in rows if r["clause"] not in GAPS]
    if missing:
        raise RuntimeError(f"historical gap keys missing {missing}")
    write("50_clause_status.json", {"baseline": old["baseline"],
        "scope": "CANDIDATE_SOURCE_WITH_FROZEN_FULL_SCOPES_NOT_CLOSURE",
        "ci_attempts": old.get("ci_attempts", []), "rows": rows})

    proposed = json.loads((HERE/"proposed_825792b.json").read_text(encoding="utf-8"))
    registered = {r["symbol"] for r in proposed["rows"]}
    for d in declarations:
        if d["short"].startswith("proposed_") and d["short"] not in registered:
            result = subprocess.run(["git", "grep", "-n", "-E",
                r"^(noncomputable )?(def|theorem|structure|inductive) " + d["short"] + r"([^A-Za-z0-9_]|$)",
                old["baseline"], "--", "*.lean"], cwd=ROOT, capture_output=True, text=True, encoding="utf-8")
            if result.returncode not in (0, 1):
                raise RuntimeError(result.stderr)
            hits = result.stdout.splitlines()
            proposed["rows"].append({"symbol": d["short"],
                "theory": [r["clause"] for r in rows if Path(r["planned_file"]).stem == d["module"]],
                "baseline_825792b": "UNLOCATED" if hits else "NEW", "baseline_hits": hits,
                "basis": "Exact declaration name searched at the fixed baseline; semantic reuse is reported separately in baseline_reuse.json.",
                "accept": []})
            registered.add(d["short"])
    fixture = {d["short"]: d for d in declarations if d["module"] == "Acceptance" and d["kind"] == "theorem"}
    def examples(module):
        positive, negative = EXAMPLES[module]
        def refs(names):
            return [{"name": fixture[n]["name"], "file": fixture[n]["file"], "line": fixture[n]["line"]} for n in names]
        return {"positive": refs(positive), "negative": refs(negative),
                "scope": "Selected synthetic source witnesses, some via Pipeline.run; NOT complete frozen-scope coverage and NOT executed before Lean CI.",
                "missing_selected_positive": not bool(positive), "missing_selected_negative": not bool(negative)}
    for r in proposed["rows"]:
        found = [d for d in declarations if d["short"] == r["symbol"]]
        if not found and r["symbol"] in BOUNDARIES:
            found = [d for d in declarations if d["module"]+"."+d["short"] in BOUNDARIES[r["symbol"]]]
            r["mapping_scope"] = "Reviewed new mathematical candidate boundary; no baseline symbol or product integration is asserted."
        r["lean_target"] = [d["name"] for d in found] or None
        r["candidate_source_evidence"] = [{"file": d["file"], "line": d["line"],
            "worktree_sha256": hashlib.sha256((HERE/d["file"]).read_bytes()).hexdigest(),
            "imports": re.findall(r"^import (\S+)", texts[d["module"]], re.M),
            "hash_scope": "WORKTREE_BYTES; canonical source/dependency blobs in evidence/local-checks.json"}
            for d in found]
        r["consumer"] = [x for d in found for x in d["consumers"]] or None
        r["accept"] = [{"module": m, "examples": examples(m)} for m in dict.fromkeys(d["module"] for d in found)]
        r["status"] = "SOURCE_PRESENT_AWAITING_CI_AND_SCOPE_AUDIT" if found else "UNLOCATED_IMPLEMENTATION"
        r["baseline_825792b"] = "NEW" if found else "UNLOCATED"
        r["formal_ci"] = "CI_NOT_RUN"
    write("proposed_825792b.json", proposed)
    write("module_inventory.json", {"status": "UNCOMPILED_CANDIDATES", "modules": [
        {"file": m+".lean", "sha256": hashlib.sha256((HERE/(m+".lean")).read_bytes()).hexdigest(),
         "theory": [r["clause"] for r in rows if Path(r["planned_file"]).stem == m],
         "hash_scope": "WORKTREE_BYTES; canonical Git blob hashes are recorded in evidence/local-checks.json",
         "theorems": [d["name"] for d in declarations if d["module"] == m and d["kind"] == "theorem"],
         "consumer_evidence": "declarations.json (actual lexical references, not a refinement proof)",
         "operational_calls": [{"name": d["name"], "kind": d["kind"], "line": d["line"],
                                "consumers": d["consumers"]} for d in declarations
                               if d["module"] == m and d["kind"] == "def" and d["consumers"]],
         "examples": examples(m),
         "remaining_obligations": [],
         "formal_ci": "CI_NOT_RUN"} for m in ORDER]})
    print("Source inventories and CIAll refreshed; no formal CI status promoted.")


if __name__ == "__main__":
    main()
