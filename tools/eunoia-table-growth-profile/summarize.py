#!/usr/bin/env python3
"""Classify search-created entries at the last completed witness boundary.

A search-created entry later used by source reification is required. Initial
prefix entries and between-call growth are conservatively source-required.
Retained certificate dependencies include all action and expected literals,
ordered roots, recursive formula children, and recursive atom children.
No claim is made about an unfinished final call or unobserved later work.
"""
import argparse
import json
from pathlib import Path


def summarize(text):
    calls = {}
    previous = None
    source = {'atoms': set(), 'forms': set()}
    retained = {'atoms': set(), 'forms': set()}
    created = {'atoms': set(), 'forms': set()}
    rows = []
    for line in text.splitlines():
        if not line.startswith('EUNOIA_TABLE '):
            continue
        event = json.loads(line[len('EUNOIA_TABLE '):])
        if event['event'] == 'begin':
            if previous is not None and any(event[k] < previous[k] for k in source):
                raise ValueError('table reset: use one tactic per compiler')
            calls[event['id']] = event
            for kind in source:
                source[kind].update(range(0 if previous is None else previous[kind], event[kind]))
                source[kind].update(event['source_' + kind])
        elif event['event'] == 'end':
            start = calls.pop(event['id'])
            row = {'id': event['id'], 'status': event['status']}
            for kind in source:
                if event[kind] < start[kind]:
                    raise ValueError('tables shrank inside search')
                created[kind].update(range(start[kind], event[kind]))
                retained[kind].update(event['retained_' + kind])
                row[kind + '_between_calls'] = None if previous is None else start[kind] - previous[kind]
                row[kind + '_before'] = start[kind]
                row[kind + '_after'] = event[kind]
                row[kind + '_added'] = event[kind] - start[kind]
            rows.append(row)
            previous = event
    result = {'completed_calls': len(rows), 'open_calls': sorted(calls), 'calls': rows}
    for kind in source:
        needed = source[kind] | retained[kind]
        result[kind] = {'final_observed': None if previous is None else previous[kind],
                        'search_created': len(created[kind]),
                        'search_created_source_required': len(created[kind] & source[kind]),
                        'search_created_certificate_only': len((created[kind] & retained[kind]) - source[kind]),
                        'search_created_unused': len(created[kind] - needed),
                        'unused_indices': sorted(created[kind] - needed)}
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('logs', type=Path, nargs='+')
    args = parser.parse_args()
    for log in args.logs:
        value = summarize(log.read_text())
        log.with_name('tables-summary.json').write_text(json.dumps(value, indent=2) + '\n')
        print(json.dumps({'log': str(log), **{k: v for k, v in value.items() if k != 'calls'}}))


if __name__ == '__main__':
    main()
