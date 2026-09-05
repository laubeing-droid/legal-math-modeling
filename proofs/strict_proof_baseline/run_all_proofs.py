#!/usr/bin/env python3
"""
run_all_proofs.py — One-click runner for all juris-calculus proof artifacts.
Usage:
    cd proofs/strict_proof_baseline
    python run_all_proofs.py
"""
import subprocess, sys, os, json
from pathlib import Path

PROOF_DIR = Path(__file__).parent
RESULTS = {}

def run(cmd: list, cwd=None, timeout=60):
    try:
        r = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout,
                           encoding="utf-8", errors="replace")
        return {"returncode": r.returncode, "stdout": (r.stdout or "")[:500], "stderr": (r.stderr or "")[:500]}
    except FileNotFoundError as e:
        return {"returncode": -1, "error": f"Command not found: {e}"}
    except subprocess.TimeoutExpired:
        return {"returncode": -1, "error": "Timeout"}

def main():
    # --- P0-A: Category Rosetta (toy no-total-mapping checker) ---
    print("[P0-A] Running finite_no_total_mapping_checker.py...")
    RESULTS["P0-A"] = run([sys.executable, "p0a_category/finite_no_total_mapping_checker.py"], cwd=PROOF_DIR)

    # --- P0-B: DP Privilege Lattice (Z3) ---
    print("[P0-B] Checking Z3 SMT proof...")
    z3_smt = run(["z3", "smt/cn_privilege_lattice.smt2"], cwd=PROOF_DIR)
    z3_py = run([sys.executable, "smt/cn_privilege_lattice_z3.py"], cwd=PROOF_DIR)
    RESULTS["P0-B"] = {"smt2": z3_smt, "python": z3_py}

    # --- P0-C: Banach Contraction (Lean) ---
    # Lean proofs require Mathlib compilation; use extended timeout
    print("[P0-C] Checking Lean 4 proof (timeout=300s, TOOLCHAIN_PENDING expected)...")
    lean = run(["lake", "env", "lean", "lean/BanachEffectiveNodes.lean"], cwd=PROOF_DIR, timeout=300)
    if lean.get("returncode") == -1 and "Timeout" in lean.get("error", ""):
        lean["status"] = "TOOLCHAIN_PENDING"
        lean["note"] = "Lean build requires Mathlib; timeout is expected. See proofs/lean/ for source."
    RESULTS["P0-C"] = lean

    # --- P0-D: Galois Adjunction (Lean) ---
    print("[P0-D] Checking Lean 4 Galois proof (timeout=300s, TOOLCHAIN_PENDING expected)...")
    lean_g = run(["lake", "env", "lean", "lean/FiniteGaloisAdjunction.lean"], cwd=PROOF_DIR, timeout=300)
    if lean_g.get("returncode") == -1 and "Timeout" in lean_g.get("error", ""):
        lean_g["status"] = "TOOLCHAIN_PENDING"
        lean_g["note"] = "Lean build requires Mathlib; timeout is expected. See proofs/lean/ for source."
    RESULTS["P0-D"] = lean_g

    # --- P0-D2: Privilege Epsilon Refutation ---
    print("[P0-D2] Running privilege epsilon refutation...")
    RESULTS["P0-D2"] = run([sys.executable, "p0d_privilege_epsilon/privilege_epsilon_refutation.py"], cwd=PROOF_DIR)

    # --- P1-E: Dung AAF ---
    print("[P1-E] Running Dung grounded extension verification...")
    RESULTS["P1-E"] = run([sys.executable, "p1e_aaf/aaf_grounded_extension_proof.py"], cwd=PROOF_DIR, timeout=300)

    # --- Evaluator Non-Monotone Counterexample ---
    print("[E3] Running evaluator non-monotone counterexample...")
    RESULTS["E3"] = run([sys.executable, "p1e_aaf/evaluator_nonmonotone_counterexample.py"], cwd=PROOF_DIR)

    # --- Summary ---
    print("\n" + "="*60)
    print("PROOF RUN SUMMARY")
    print("="*60)
    for theorem, result in RESULTS.items():
        if "returncode" in result:
            status = "PASS" if result["returncode"] == 0 else "FAIL"
        elif "smt2" in result:
            s1 = "PASS" if result["smt2"].get("returncode") == 0 else "FAIL/PENDING"
            s2 = "PASS" if result["python"].get("returncode") == 0 else "FAIL/PENDING"
            status = f"SMT={s1}, PY={s2}"
        else:
            status = f"ERROR: {result.get('error', 'unknown')}"
        print(f"  {theorem}: {status}")

    # Save results
    out_path = PROOF_DIR / "proof_run_results.json"
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(RESULTS, f, ensure_ascii=False, indent=2)
    print(f"\nResults saved to: {out_path}")

    # Overall status
    all_pass = all(
        r.get("returncode") == 0 if isinstance(r, dict) and "returncode" in r else
        (r.get("smt2", {}).get("returncode") == 0 and r.get("python", {}).get("returncode") == 0) if isinstance(r, dict) and "smt2" in r else False
        for r in RESULTS.values()
    )
    return 0 if all_pass else 1

if __name__ == "__main__":
    sys.exit(main())
