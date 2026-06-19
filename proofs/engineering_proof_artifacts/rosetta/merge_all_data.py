#!/usr/bin/env python3
"""
Merge + Deduplicate T8.5 + T9.4 data from both directories.
"""

import csv
import os
import hashlib
from pathlib import Path
from collections import Counter

VALID_STATUSES = {
    'CN_ONLY', 'CN_US_PARTIAL', 'CN_HK_PARTIAL', 'COLLISION',
    'ASYMMETRY', 'TRI_JURISDICTION_PARTIAL', 'TRI_JURISDICTION_MAPPED',
    'US_HK_PARTIAL'
}

T85_FIELDS = ['pattern_id', 'domain', 'fact_summary', 'cn_claim', 'us_claim',
              'hk_claim', 'mapping_status', 'hard_case', 'positive_control', 'notes']

T94_FIELDS = ['case_id', 'jurisdiction', 'domain', 'damage_type',
              'initial_claim', 'final_award', 'iterations', 'court_level',
              'year', 'converged', 'convergence_gap', 'notes']


def read_csv(path):
    rows = []
    try:
        with open(path, encoding='utf-8-sig') as f:
            for r in csv.DictReader(f):
                rows.append(r)
    except Exception:
        try:
            with open(path, encoding='utf-8') as f:
                for r in csv.DictReader(f):
                    rows.append(r)
        except Exception:
            pass
    return rows


def t85_content_hash(row):
    key = (row.get('fact_summary', '').strip()[:100],
           row.get('cn_claim', '').strip()[:80],
           row.get('us_claim', '').strip()[:80])
    return hashlib.md5('|'.join(key).encode()).hexdigest()


def t94_content_hash(row):
    key = (row.get('case_id', '').strip(),
           row.get('jurisdiction', '').strip(),
           str(row.get('final_award', '')).strip()[:20])
    return hashlib.md5('|'.join(key).encode()).hexdigest()


def collect_t85_files():
    files = []
    # category_rosetta
    base1 = 'data/category_rosetta'
    for f in sorted(os.listdir(base1)):
        if f.endswith('.csv') and ('t85' in f.lower() or 'T8.5' in f or f == 'claim_mapping.csv'):
            files.append(os.path.join(base1, f))
    # category_rosetta_kimi
    base2 = 'data/category_rosetta_kimi'
    for f in sorted(os.listdir(base2)):
        if f.endswith('.csv') and ('T8.5' in f or 't85' in f.lower()):
            files.append(os.path.join(base2, f))
    return files


def collect_t94_files():
    files = []
    base1 = 'data/category_rosetta'
    for f in sorted(os.listdir(base1)):
        if f.endswith('.csv') and ('t94' in f.lower() or 'T9.4' in f):
            files.append(os.path.join(base1, f))
    base2 = 'data/category_rosetta_kimi'
    for f in sorted(os.listdir(base2)):
        if f.endswith('.csv') and ('T9.4' in f or 't94' in f.lower()):
            files.append(os.path.join(base2, f))
    return files


def normalize_status(val):
    v = val.strip().upper().replace(' ', '_')
    if v in VALID_STATUSES:
        return v
    # Try partial matches
    for s in VALID_STATUSES:
        if s in v:
            return s
    return ''


def normalize_domain(val):
    v = val.strip().lower()
    domain_map = {
        'contract': 'contract', 'tort': 'tort', 'criminal': 'criminal',
        'admin': 'admin', 'administrative': 'admin', 'ip': 'ip',
        'labor': 'labor', 'labour': 'labor', 'employment': 'labor',
        'corporate': 'corporate', 'family': 'family', 'tax': 'tax',
        'procedure': 'procedure', 'civil_commercial': 'contract',
        'foreign_commercial': 'contract', 'hk_macau': 'contract',
        'state_compensation': 'admin', 'supervision': 'procedure',
        'enforcement': 'procedure', 'juvenile': 'criminal',
        'environment': 'tort', 'management': 'admin', 'filing': 'procedure',
        'constitutional': 'admin', 'data_privacy': 'ip',
        'data_crossborder': 'admin', 'intellectual_property': 'ip',
    }
    for k, mapped in domain_map.items():
        if k == v:
            return mapped
    if '+' in v:
        return v.split('+')[0].strip()
    # Garbled/unknown: return 'unknown' to be filtered
    if len(v) > 20 or any(ord(c) > 127 for c in v):
        return 'unknown'
    return v if v else 'unknown'


def merge_t85():
    files = collect_t85_files()
    print(f"T8.5 files found: {len(files)}")

    seen = set()
    all_rows = []
    stats = {'total_read': 0, 'duplicate': 0, 'invalid_status': 0, 'kept': 0}

    for fp in files:
        rows = read_csv(fp)
        stats['total_read'] += len(rows)
        for r in rows:
            h = t85_content_hash(r)
            if h in seen:
                stats['duplicate'] += 1
                continue
            seen.add(h)

            status = normalize_status(r.get('mapping_status', ''))
            if not status:
                stats['invalid_status'] += 1
                continue

            domain = normalize_domain(r.get('domain', ''))
            clean = {
                'pattern_id': r.get('pattern_id', '').strip(),
                'domain': domain,
                'fact_summary': r.get('fact_summary', '').strip(),
                'cn_claim': r.get('cn_claim', '').strip(),
                'us_claim': r.get('us_claim', '').strip(),
                'hk_claim': r.get('hk_claim', '').strip(),
                'mapping_status': status,
                'hard_case': r.get('hard_case', '').strip(),
                'positive_control': r.get('positive_control', '').strip(),
                'notes': r.get('notes', '').strip(),
            }
            if clean['fact_summary'] and clean['mapping_status'] and clean['domain'] != 'unknown':
                all_rows.append(clean)
                stats['kept'] += 1

    # Also add extracted Supreme Court data (different schema)
    extracted_path = 'data/category_rosetta/t85_extracted_mappings.csv'
    if os.path.exists(extracted_path):
        for r in read_csv(extracted_path):
            h = t85_content_hash(r)
            if h in seen:
                stats['duplicate'] += 1
                continue
            seen.add(h)
            clean = {
                'pattern_id': r.get('pattern_id', '').strip(),
                'domain': normalize_domain(r.get('domain', '')),
                'fact_summary': r.get('fact_summary', '').strip(),
                'cn_claim': r.get('fact_summary', '').strip()[:200],
                'us_claim': 'DATA_UNAVAILABLE',
                'hk_claim': 'DATA_UNAVAILABLE',
                'mapping_status': normalize_status(r.get('mapping_status', 'CN_ONLY')),
                'hard_case': 'False',
                'positive_control': 'False',
                'notes': f"Extracted from Supreme Court case: {r.get('case_number', '')}",
            }
            if clean['fact_summary']:
                all_rows.append(clean)
                stats['kept'] += 1

    return all_rows, stats


def merge_t94():
    files = collect_t94_files()
    print(f"T9.4 files found: {len(files)}")

    seen = set()
    all_rows = []
    stats = {'total_read': 0, 'duplicate': 0, 'no_amount': 0, 'kept': 0}

    for fp in files:
        rows = read_csv(fp)
        stats['total_read'] += len(rows)
        for r in rows:
            h = t94_content_hash(r)
            if h in seen:
                stats['duplicate'] += 1
                continue
            seen.add(h)

            award = r.get('final_award', '').strip()
            if not award or award in ('None', '', '0'):
                stats['no_amount'] += 1
                continue

            try:
                float(award)
            except ValueError:
                stats['no_amount'] += 1
                continue

            juris = r.get('jurisdiction', 'CN').strip().upper()
            if juris not in ('CN', 'US', 'HK'):
                juris = 'CN'

            clean = {
                'case_id': r.get('case_id', '').strip(),
                'jurisdiction': juris,
                'domain': normalize_domain(r.get('domain', '')),
                'damage_type': r.get('damage_type', 'compensatory').strip(),
                'initial_claim': r.get('initial_claim', '').strip(),
                'final_award': award,
                'iterations': r.get('iterations', '1').strip(),
                'court_level': r.get('court_level', 'trial').strip(),
                'year': r.get('year', '').strip(),
                'converged': r.get('converged', '').strip(),
                'convergence_gap': r.get('convergence_gap', '').strip(),
                'notes': r.get('notes', '').strip(),
            }
            all_rows.append(clean)
            stats['kept'] += 1

    return all_rows, stats


def main():
    # Auto-detect project root from script location
    project_root = Path(__file__).resolve().parent.parent.parent.parent
    os.chdir(project_root)

    print("=" * 60)
    print("T8.5 + T9.4 Data Merge & Dedup")
    print("=" * 60)

    # T8.5
    t85_rows, t85_stats = merge_t85()
    print(f"\nT8.5 merge results:")
    for k, v in t85_stats.items():
        print(f"  {k}: {v}")

    t85_status = Counter(r['mapping_status'] for r in t85_rows)
    print(f"\nT8.5 by mapping_status:")
    for s, c in t85_status.most_common():
        print(f"  {s}: {c}")

    t85_domain = Counter(r['domain'] for r in t85_rows)
    print(f"\nT8.5 by domain:")
    for d, c in t85_domain.most_common():
        print(f"  {d}: {c}")

    # T9.4
    t94_rows, t94_stats = merge_t94()
    print(f"\nT9.4 merge results:")
    for k, v in t94_stats.items():
        print(f"  {k}: {v}")

    t94_juris = Counter(r['jurisdiction'] for r in t94_rows)
    print(f"\nT9.4 by jurisdiction:")
    for j, c in t94_juris.most_common():
        print(f"  {j}: {c}")

    t94_type = Counter(r['damage_type'] for r in t94_rows)
    print(f"\nT9.4 by damage_type:")
    for t, c in t94_type.most_common():
        print(f"  {t}: {c}")

    # Save
    out_dir = Path('data/category_rosetta')

    t85_out = out_dir / 'T8.5_merged_clean.csv'
    with open(t85_out, 'w', encoding='utf-8-sig', newline='') as f:
        w = csv.DictWriter(f, fieldnames=T85_FIELDS)
        w.writeheader()
        w.writerows(t85_rows)
    print(f"\nT8.5 saved: {t85_out} ({len(t85_rows)} rows)")

    t94_out = out_dir / 'T9.4_merged_clean.csv'
    with open(t94_out, 'w', encoding='utf-8-sig', newline='') as f:
        w = csv.DictWriter(f, fieldnames=T94_FIELDS)
        w.writeheader()
        w.writerows(t94_rows)
    print(f"T9.4 saved: {t94_out} ({len(t94_rows)} rows)")

    print(f"\n{'=' * 60}")
    print(f"FINAL: T8.5={len(t85_rows)} rows, T9.4={len(t94_rows)} rows")
    print(f"{'=' * 60}")


if __name__ == '__main__':
    main()
