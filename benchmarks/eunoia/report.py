#!/usr/bin/env python3
"""Produce a reviewable table from one checked-tactic benchmark run."""

import argparse
import itertools
import json
import math
from pathlib import Path


def tables(rows):
    """Keep coverage denominators separate from paired successful timings."""
    attempts = {}
    for row in rows:
        key = row['backend'], row['case_id'], row['repeat']
        if key in attempts:
            raise ValueError(f'Duplicate attempt: {key}')
        if row['solved']:
            if row['expected'] != 'proved' or row['status'] != 'solved':
                raise ValueError(f'Invalid solved attempt: {key}')
            for field in ['tactic_wall_s', 'qed_wall_s']:
                value = row[field]
                if not isinstance(value, (int, float)) or not math.isfinite(value) or value < 0:
                    raise ValueError(f'Invalid checked timing: {key}, {field}')
        attempts[key] = row
    backends = sorted({r['backend'] for r in rows})
    coverage = []
    for backend in backends:
        selected = [r for r in rows if r['backend'] == backend]
        positive = [r for r in selected if r['expected'] == 'proved']
        checked = [r for r in positive if r['solved']]
        negative = [r for r in selected if r['expected'] == 'rejected']
        coverage.append((backend, len(checked), len(positive),
            sum(r['status'] == 'negative_rejected' for r in negative), len(negative),
            sum(r['tactic_wall_s'] for r in checked),
            sum(r['qed_wall_s'] for r in checked)))
    paired = []
    for left, right in itertools.combinations(backends, 2):
        shared = []
        for (backend, case, repeat), a in attempts.items():
            b = attempts.get((right, case, repeat))
            if backend == left and a['solved'] and b and b['solved']:
                if a['theory'] != b['theory']:
                    raise ValueError(f'Mismatched theory for shared case: {case}')
                shared.append((a, b))
        paired.append((left, right, len(shared),
            sum(a['tactic_wall_s'] for a, _ in shared),
            sum(b['tactic_wall_s'] for _, b in shared),
            sum(a['qed_wall_s'] for a, _ in shared),
            sum(b['qed_wall_s'] for _, b in shared)))
    return coverage, paired


def markdown(rows):
    coverage, paired = tables(rows)
    lines = [
        '| Backend | Checked positives / scheduled | Rejected controls / scheduled | Checked tactic total (s) | Checked Qed total (s) |',
        '| --- | ---: | ---: | ---: | ---: |']
    for backend, checked, total, rejected, controls, tactic, qed in coverage:
        times = (f'{tactic:.3f}', f'{qed:.3f}') if checked else ('unmeasured', 'unmeasured')
        lines.append(f'| {backend} | {checked}/{total} | {rejected}/{controls} | {times[0]} | {times[1]} |')
    lines += ['', 'Timing totals include only checked positive proofs; their solved sets can differ.',
        'Each latency comparison below uses the same case and repeat checked by both backends.', '',
        '| Backend pair | Shared checked attempts | Tactic totals (s), left / right | Qed totals (s), left / right |',
        '| --- | ---: | ---: | ---: |']
    for left, right, count, lt, rt, lq, rq in paired:
        tactic = f'{lt:.3f} / {rt:.3f}' if count else 'unmeasured'
        qed = f'{lq:.3f} / {rq:.3f}' if count else 'unmeasured'
        lines.append(f'| {left} / {right} | {count} | {tactic} | {qed} |')
    lines += ['', 'Timing excludes failed, unavailable and negative attempts. Whole compiler timeouts',
        'and tactic errors remain unsolved in the coverage denominator. Tactic and Qed',
        'times are separate; solver-only time is unavailable.', '']
    return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('results', type=Path, help='one results.json from run.py')
    args = parser.parse_args()
    data = json.loads(args.results.read_text())
    if data.get('schema_version') != 1:
        parser.error('Unsupported results schema')
    print(markdown(data['rows']), end='')


if __name__ == '__main__':
    main()
