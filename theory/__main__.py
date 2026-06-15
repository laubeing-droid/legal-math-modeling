#!/usr/bin/env python3
"""Command-line entry for the evidence-calibrated theory package."""

from . import run_all


if __name__ == "__main__":
    raise SystemExit(0 if run_all() else 1)
