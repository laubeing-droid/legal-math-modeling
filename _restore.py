import os, subprocess, pathlib

repo = os.environ.get("LEGAL_MATH_MODELING_ROOT", r'D:\Codex\数学证明\legal-math-modeling')
result = subprocess.run(
    ['git', 'cat-file', '-p', '78f9d48:proofs/lean/juris_lean/JurisLean/FiniteMonotoneIteration.lean'],
    capture_output=True, cwd=repo)
p = pathlib.Path(repo) / r'proofs\lean\juris_lean\JurisLean\FiniteMonotoneIteration.lean'
p.write_bytes(result.stdout)
data2 = p.read_bytes()
print(f'Wrote {len(data2)} bytes')
print(f'Valid: {data2[:6] == b"import"}')
