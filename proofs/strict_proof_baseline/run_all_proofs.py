#!/usr/bin/env python3
"""
run_all_proofs.py — One-click runner for all juris-calculus proof artifacts.
Usage:
    cd "D:\\Codex\\juris-calculus\\20260611 kimi proof\\proof"
    python run_all_proofs.py
"""
import subprocess, sys, os, json
from pathlib import Path

PROOF_DIR = Path(__file__).parent
RESULTS = {}

def run(cmd: list, cwd=None, timeout=60):
    try:
        r = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout)
        return {"returncode": r.returncode, "stdout": r.stdout[:500], "stderr": r.stderr[:500]}
    except FileNotFoundError as e:
        return {"returncode": -1, "error": f"Command not found: {e}"}
    except subprocess.TimeoutExpired:
        return {"returncode": -1, "error": "Timeout"}

def main():
    # --- P0-A: Category Rosetta ---
    print("[P0-A] Running category_rosetta_obstruction_verifier.py...")
    RESULTS["P0-A"] = run([sys.executable, "category_rosetta_obstruction_verifier.py"], cwd=PROOF_DIR)

    # --- P0-B: DP Privilege Lattice (Z3) ---
    print("[P0-B] Checking Z3 SMT proof...")
    z3_smt = run(["z3", "smt/cn_privilege_lattice.smt2"], cwd=PROOF_DIR)
    z3_py = run([sys.executable, "smt/cn_privilege_lattice_z3.py"], cwd=PROOF_DIR)
    RESULTS["P0-B"] = {"smt2": z3_smt, "python": z3_py}

    # --- P0-C: Banach Contraction (Lean) ---
    print("[P0-C] Checking Lean 4 proof...")
    lean = run(["lake", "env", "lean", "lean/BanachEffectiveNodes.lean"], cwd=PROOF_DIR)
    RESULTS["P0-C"] = lean

    # --- P0-D: Galois Adjunction (Lean) ---
    print("[P0-D] Checking Lean 4 Galois proof...")
    lean_g = run(["lake", "env", "lean", "lean/FiniteGaloisAdjunction.lean"], cwd=PROOF_DIR)
    RESULTS["P0-D"] = lean_g

    # --- P1-E: Dung AAF ---
    print("[P1-E] Running Dung grounded extension verification...")
    RESULTS["P1-E"] = run([sys.executable, "aaf/dung_grounded_extension.py"], cwd=PROOF_DIR, timeout=300)

    # --- Shadow Pipeline ---
    print("[Shadow] Running Dung AAF shadow evaluator...")
    RESULTS["Shadow"] = run([sys.executable, "../compiler_core/argumentation.py", "--run-diff"], cwd=PROOF_DIR, timeout=120)

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
