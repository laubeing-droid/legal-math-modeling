"""finalize-external-build.py -- Verify external lake build and finalize release."""

import json, sys, hashlib, subprocess
from pathlib import Path
from datetime import datetime

REPO = Path(r"D:\Claude\数学证明\legal-math-modeling")

def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def verify(result_path: str) -> dict:
    rp = Path(result_path)
    if not rp.exists():
        return {"status": "FAIL", "reason": f"result file not found: {result_path}"}

    result = json.loads(rp.read_text(encoding="utf-8-sig"))
    checks = []

    # 1. exit_code == 0
    if result["exit_code"] != 0:
        checks.append(f"FAIL: exit_code={result['exit_code']}")
    else:
        checks.append("PASS: exit_code == 0")

    # 2. git_commit matches HEAD
    head = subprocess.run(
        ["git", "-C", str(REPO), "rev-parse", "HEAD"],
        capture_output=True, text=True
    ).stdout.strip()
    if result["git_commit"] != head:
        checks.append(f"FAIL: commit mismatch (build:{result['git_commit'][:8]} HEAD:{head[:8]})")
    else:
        checks.append(f"PASS: commit {head[:8]}")

    # 3. log file exists and SHA matches
    log_dir = rp.parent
    log_file = log_dir / "lake-build.log"
    if not log_file.exists():
        checks.append("FAIL: lake-build.log not found")
    else:
        actual_sha = sha256_file(log_file)
        if actual_sha != result["log_sha256"]:
            checks.append("FAIL: log SHA256 mismatch")
        else:
            checks.append("PASS: log SHA256 verified")

    # 4. Lean source tree remains clean after the recorded build
    diff = subprocess.run(
        [
            "git",
            "-C",
            str(REPO),
            "status",
            "--porcelain",
            "--untracked-files=no",
            "--",
            "proofs/lean/juris_lean/JurisLean/",
        ],
        capture_output=True,
        text=True,
    ).stdout.strip()
    if diff:
        checks.append(f"FAIL: Lean source tree dirty after build: {diff}")
    else:
        checks.append("PASS: Lean source tree clean after build")

    all_pass = all(c.startswith("PASS") for c in checks)
    return {
        "status": "PASS" if all_pass else "FAIL",
        "checks": checks,
        "verified_at": datetime.now().isoformat(),
        "result_file": str(rp),
    }

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python finalize-external-build.py <path/to/build-result.json>")
        sys.exit(1)
    report = verify(sys.argv[1])
    print(json.dumps(report, indent=2, ensure_ascii=False))
    sys.exit(0 if report["status"] == "PASS" else 1)
