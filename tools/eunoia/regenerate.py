#!/usr/bin/env python3
"""Deterministically regenerate the selected real cvc5 CPC signature data."""
import argparse
import json
from pathlib import Path
from compile import Compiler

ROOT = Path(__file__).resolve().parents[2]

if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, default=ROOT / 'theories/checker/eunoia/CpcGenerated.v')
    ap.add_argument('--manifest', type=Path, default=ROOT / 'tools/eunoia/cpc-manifest.json')
    args = ap.parse_args()
    code, manifest = Compiler(ROOT / 'tools/eunoia/signatures/cpc/Cpc.eo').compile(
        (ROOT / 'tools/eunoia/rules.txt').read_text().split())
    args.output.write_text(code)
    args.manifest.write_text(json.dumps(manifest, indent=2, sort_keys=True) + '\n')
    print(f"compiled {len(manifest['selected_rules'])} rules, {len(manifest['programs'])} helpers, "
          f"{len(manifest['sources'])} source includes; {len(manifest['excluded_rules'])} rules excluded")
