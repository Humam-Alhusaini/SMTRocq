#!/usr/bin/env python3
"""Replay actual CPC fixtures through the untrusted combined helper producer.

This checks producer compatibility only. Acceptance still uses the proved
reference-refining cache checker and SMTCoq's separate semantic gate.
"""
import argparse
from pathlib import Path
from replay_fixtures import generate

ROOT = Path(__file__).resolve().parents[2]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    code = '''From Stdlib Require Import String List.
From SMTCoq.checker.eunoia Require Import EoSyntax EoRuntime CpcGenerated
 TraceReplay LiaTraceReplay CpcMemoCollector.
Definition helper_derive fuel query name args premises :=
 fst (derive_context_logged default_primitive fuel query name None args premises).
Definition helper_assuming fuel query name assumption args premises :=
 fst (derive_context_logged default_primitive fuel query name (Some assumption) args premises).
Definition helper_final query roots steps goal :=
 match replay_with helper_derive query roots steps with
 | Some env=>lookup goal env|None=>None end.
Definition helper_trace_final := trace_final_with helper_derive helper_assuming.
'''
    base = ROOT / "tools/eunoia/tests"
    groups = [(sorted((base / "fixtures").glob("uf*.cpc")), False),
              (sorted((base / "fixtures").glob("lia*.cpc")), True),
              (sorted((base / "reduced-fixtures").glob("*.cpc")), True),
              (sorted((base / "integer-fixtures").glob("*.cpc")), True)]
    for paths, scoped in groups:
        if not paths:
            raise ValueError("missing fixture group")
        text = generate(paths, scoped=scoped)
        text = text.replace(" : trace_final ", " : helper_trace_final ")
        text = text.replace(" : final_term ", " : helper_final ")
        code += text
    args.output.write_text(code)


if __name__ == "__main__":
    main()
