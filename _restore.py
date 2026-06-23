import subprocess, pathlib
result = subprocess.run(
    ['git', 'cat-file', '-p', '78f9d48:proofs/lean/juris_lean/JurisLean/FiniteMonotoneIteration.lean'],
    capture_output=True, cwd=r'D:\Claude\数学证明\legal-math-modeling')
p = pathlib.Path(r'D:\Claude\数学证明\legal-math-modeling\proofs\lean\juris_lean\JurisLean\FiniteMonotoneIteration.lean')
p.write_bytes(result.stdout)
data2 = p.read_bytes()
print(f'Wrote {len(data2)} bytes')
print(f'Valid: {data2[:6] == b"import"}')