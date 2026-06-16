"""Data quality labels for legal-math-modeling datasets.

Each data directory in the project carries a quality label indicating
the provenance and reliability of the underlying data:

    REAL      — Court records, case law, statutory text
    SYNTHETIC — AI-generated or toy data
    PROXY     — Proxy data (fee schedules, not real timesheets)
    ANNOTATED — Expert-annotated data
    UNKNOWN   — Unassessed

This module provides a central registry of quality labels so downstream
consumers can filter or gate claims by data provenance.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import List


# ---------------------------------------------------------------------------
# Shared enum (canonical location; model_status.py imports separately)
# ---------------------------------------------------------------------------

# Import from canonical location
try:
    from .model_status import DataQuality
except ImportError:
    from model_status import DataQuality


# ---------------------------------------------------------------------------
# Label dataclass
# ---------------------------------------------------------------------------

@dataclass
class DataQualityLabel:
    """Provenance and quality metadata for one dataset directory."""
    dataset_name: str
    quality: DataQuality
    source_description: str
    sample_size: int
    limitations: str


# ---------------------------------------------------------------------------
# Registry of labels for each data directory
# ---------------------------------------------------------------------------

DATA_QUALITY_LABELS: List[DataQualityLabel] = [
    DataQualityLabel(
        dataset_name="cn_legal",
        quality=DataQuality.ANNOTATED,
        source_description="Expert-annotated Chinese legal claims and judgments",
        sample_size=56,
        limitations="Annotations are subjective; inter-annotator agreement not formally measured.",
    ),
    DataQualityLabel(
        dataset_name="us_legal",
        quality=DataQuality.SYNTHETIC,
        source_description="Generated scripts simulating US legal argument patterns",
        sample_size=100,
        limitations="Scripts are synthetic and do not reflect real case law outcomes.",
    ),
    DataQualityLabel(
        dataset_name="hk_legal",
        quality=DataQuality.ANNOTATED,
        source_description="Hong Kong e-Legislation statutory text, manually curated",
        sample_size=30,
        limitations="Coverage limited to selected ordinance chapters; not exhaustive.",
    ),
    DataQualityLabel(
        dataset_name="aaf_legal",
        quality=DataQuality.SYNTHETIC,
        source_description="Synthetic AAF (Abstract Argumentation Framework) graphs with annotated legal patterns",
        sample_size=50,
        limitations="Mix of synthetic attack graphs and hand-written legal patterns; not a coherent real dataset.",
    ),
    DataQualityLabel(
        dataset_name="banach_pricing",
        quality=DataQuality.PROXY,
        source_description="Fee-schedule proxies used for Banach contraction modelling",
        sample_size=200,
        limitations="Fee schedules are proxies, not real timesheets or billing records. Contraction parameters are not calibrated on production data.",
    ),
    DataQualityLabel(
        dataset_name="category_rosetta",
        quality=DataQuality.ANNOTATED,
        source_description="Cross-jurisdiction concept mapping (CN/US/HK legal ontology alignment)",
        sample_size=44,
        limitations="Expert-annotated 44-row Rosetta table; limited to mapped concepts only.",
    ),
    DataQualityLabel(
        dataset_name="dp_privilege",
        quality=DataQuality.ANNOTATED,
        source_description="Jurisdiction privilege lattices for differential privacy policy modelling",
        sample_size=15,
        limitations="Lattice structure is expert-annotated; small sample; privacy semantics vary across jurisdictions.",
    ),
    DataQualityLabel(
        dataset_name="galois_semantics",
        quality=DataQuality.SYNTHETIC,
        source_description="Mathematical verification data for Galois connection and reverse-index proofs",
        sample_size=40,
        limitations="Entirely synthetic; used for formal verification, not empirical legal analysis.",
    ),
]


# ---------------------------------------------------------------------------
# Reporting
# ---------------------------------------------------------------------------

def print_data_quality_report() -> None:
    """Print a formatted data quality report for all registered datasets."""
    print("=" * 72)
    print("Data Quality Report — legal-math-modeling")
    print("=" * 72)
    for label in DATA_QUALITY_LABELS:
        print(f"\n  Dataset:  {label.dataset_name}")
        print(f"  Quality:  {label.quality.value}")
        print(f"  Source:   {label.source_description}")
        print(f"  Samples:  {label.sample_size}")
        print(f"  Limits:   {label.limitations}")
    print("\n" + "=" * 72)
    print("Report complete.")


# ---------------------------------------------------------------------------
# Demo
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    print_data_quality_report()
