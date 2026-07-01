# Documentation Rewrite Evidence

Status: rewritten on 2026-07-01.

## Scope

The rewrite covered every tracked file under `docs/` and every tracked file under `paper/`. It also covered public-facing root files and human-readable report summaries where a rewrite was warranted.

## Rewritten Areas

- `docs/`: full rewrite, including Markdown, text, JSON, and YAML documentation artifacts.
- `paper/`: full rewrite, including Markdown papers, LaTeX entrypoint, LaTeX sections, and BibTeX references.
- Root public entrypoints: `README.md`, `README_CN.md`, `CLAUDE.md`, and `CITATION.cff`.
- Human-readable generated report summaries in `reports/`.
- Report-style theory READMEs: `theory/conjecture/README.md` and `theory/spec/README.md`.

## Deliberately Not Rewritten As Prose

- `AGENTS.md`: retained as the project rule source.
- `SORRY_LEDGER.md`: retained as the proof-status ledger.
- `requirements.txt`: dependency contract, not prose documentation.
- `runtime/*.json`: runtime fixture data.
- `scripts/`, `tests/`, `verification/`, and Python modules under `theory/`: executable code or tests.
- Raw LLM export text files in `reports/`: retained as provenance rather than rewritten in place.
- Machine result JSON/JSONL/CSV/PNG artifacts in `reports/`: retained as generated data.

## Rewrite Rule

All rewritten prose is source-bounded. It must not claim full runtime verification, must not convert generated reports into formal proof, and must keep LLM output as candidate-only until source-bound verification succeeds.

## Release Boundary

The public repository contains an auditable specification boundary. Customer data, commercial rule libraries, lawyer workflows, litigation strategy, and private benchmarks remain out of public scope by default.
