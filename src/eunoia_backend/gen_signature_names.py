#!/usr/bin/env python3
"""Generate untrusted compiler metadata from the signature-generated module.

Strict CPC conformance still reads its loaded Rocq metadata. These names only
help the untrusted proof translator; semantic certificates are checked in Rocq.
"""
import json
from pathlib import Path
import re
import sys

source, target = map(Path, sys.argv[1:])
match = re.search(r'^Definition cpc_signature_names : list string := \[(.*?)\]\.',
                  source.read_text(), re.M)
if match is None:
    raise SystemExit('missing generated CPC symbol inventory')
parts = [p.strip() for p in match[1].split(';') if p.strip()]
names = []
for part in parts:
    if not re.fullmatch(r'"(?:[^"\n]|"")*"', part):
        raise SystemExit('unsupported generated symbol spelling')
    name = part[1:-1].replace('""', '"')
    if not name.isascii():
        raise SystemExit('non-ASCII signature symbol')
    names.append(name)
if not names or len(names) != len(set(names)):
    raise SystemExit('empty or duplicate signature inventory')
target.write_text('(* Generated untrusted CPC translation metadata. *)\nlet names = [\n' +
                  ''.join('  ' + json.dumps(n) + ';\n' for n in names) + ']\n')
